// Copyright 2019-2021 PureStake Inc.
// This file is part of Moonbeam.

// Moonbeam is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Moonbeam is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Moonbeam.  If not, see <http://www.gnu.org/licenses/>.

//! # Parachain Staking
//! Minimal staking pallet that implements collator selection by total backed stake.
//! The main difference between this pallet and `frame/pallet-staking` is that this pallet
//! uses direct delegation. Delegators choose exactly who they delegate and with what stake.
//! This is different from `frame/pallet-staking` where delegators approval vote and run Phragmen.
//!
//! ### Rules
//! There is a new round every `<Round<T>>::get().length` blocks.
//!
//! At the start of every round,
//! * issuance is distributed to collators (and their delegators) for block authoring
//! `T::RewardPaymentDelay` rounds ago
//! * queued collator and delegator exits are executed
//! * a new set of collators is chosen from the candidates
//!
//! To join the set of candidates, call `join_candidates` with `bond >= MinCandidateStk`.
//! To leave the set of candidates, call `schedule_leave_candidates`. If the call succeeds,
//! the collator is removed from the pool of candidates so they cannot be selected for future
//! collator sets, but they are not unbonded until their exit request is executed. Any signed
//! account may trigger the exit `T::LeaveCandidatesDelay` rounds after the round in which the
//! original request was made.
//!
//! To join the set of delegators, call `delegate` and pass in an account that is
//! already a collator candidate and `bond >= MinDelegatorStk`. Each delegator can delegate up to
//! `T::MaxDelegationsPerDelegator` collator candidates by calling `delegate`.
//!
//! To revoke a delegation, call `revoke_delegation` with the collator candidate's account.
//! To leave the set of delegators and revoke all delegations, call `leave_delegators`.

#![cfg_attr(not(feature = "std"), no_std)]

// #[cfg(any(test, feature = "runtime-benchmarks"))]
// mod benchmarks;
mod inflation;
#[cfg(test)]
mod mock;
mod set;
#[cfg(test)]
mod tests;
pub mod weights;

use frame_support::pallet;
pub use inflation::{InflationInfo, Range};
use weights::WeightInfo;
pub use mangata_primitives::{Balance, TokenId};
use orml_tokens::{MultiTokenCurrency, MultiTokenReservableCurrency};
use pallet_xyk::Valuate;

use crate::{set::OrderedSet};
use frame_support::pallet_prelude::*;
use frame_support::traits::{Get, Imbalance, EstimateNextSessionRotation};
use frame_system::pallet_prelude::*;
use frame_system::RawOrigin;
use parity_scale_codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Saturating, Zero, One},
	Perbill, Permill, Percent, RuntimeDebug,
	helpers_128bit::multiply_by_rational,
};
use sp_std::{cmp::Ordering, collections::btree_map::BTreeMap, prelude::*};
use sp_staking::SessionIndex;

pub use pallet::*;

#[pallet]
pub mod pallet {
	pub use super::*;
	

	/// Pallet for parachain staking
	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[derive(Eq, PartialEq, Clone, Encode, Decode, RuntimeDebug, TypeInfo,)]
	pub enum PairedOrLiquidityToken{
		Paired(TokenId),
		Liquidity(TokenId),
	}

	#[derive(Default, Clone, Encode, Decode, RuntimeDebug, TypeInfo,)]
	pub struct Bond<AccountId> {
		pub owner: AccountId,
		pub amount: Balance,
		pub liquidity_token: TokenId
	}

	impl<A> Bond<A> {
		fn from_owner(owner: A) -> Self {
			Bond {
				owner,
				amount: Balance::default(),
				liquidity_token: TokenId::default(),
			}
		}
	}

	impl<AccountId: Ord> Eq for Bond<AccountId> {}

	impl<AccountId: Ord> Ord for Bond<AccountId> {
		fn cmp(&self, other: &Self) -> Ordering {
			self.owner.cmp(&other.owner)
		}
	}

	impl<AccountId: Ord> PartialOrd for Bond<AccountId> {
		fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
			Some(self.cmp(other))
		}
	}

	impl<AccountId: Ord> PartialEq for Bond<AccountId> {
		fn eq(&self, other: &Self) -> bool {
			self.owner == other.owner
		}
	}

	#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// The activity status of the collator
	pub enum CollatorStatus {
		/// Committed to be online and producing valid blocks (not equivocating)
		Active,
		/// Temporarily inactive and excused for inactivity
		Idle,
		/// Bonded until the inner round
		Leaving(RoundIndex),
	}

	impl Default for CollatorStatus {
		fn default() -> CollatorStatus {
			CollatorStatus::Active
		}
	}

	#[derive(Default, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Snapshot of collator state at the start of the round for which they are selected
	pub struct CollatorSnapshot<AccountId> {
		pub bond: Balance,
		pub delegations: Vec<Bond<AccountId>>,
		pub total: Balance,
		pub liquidity_token: TokenId,
	}

	#[derive(PartialEq, Clone, Copy, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Changes allowed by an active collator candidate to their self bond
	pub enum CandidateBondChange {
		Increase,
		Decrease,
	}

	#[derive(PartialEq, Clone, Copy, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Request scheduled to change the collator candidate self-bond
	pub struct CandidateBondRequest {
		pub amount: Balance,
		pub change: CandidateBondChange,
		pub when_executable: RoundIndex,
	}
	
	#[derive(Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Collator candidate state with self bond + delegations
	pub struct CollatorCandidate<AccountId> {
		/// The account of this collator
		pub id: AccountId,
		/// This collator's self stake.
		pub bond: Balance,
		/// This is the liquidity_token the collator uses
		pub liquidity_token: TokenId,
		/// Set of all delegator AccountIds (to prevent >1 delegation per AccountId)
		pub delegators: OrderedSet<AccountId>,
		/// Top T::MaxDelegatorsPerCollator::get() delegations, ordered greatest to least
		pub top_delegations: Vec<Bond<AccountId>>,
		/// Bottom delegations (unbounded), ordered least to greatest
		pub bottom_delegations: Vec<Bond<AccountId>>,
		/// Sum of top delegations + self.bond
		pub total_counted: Balance,
		/// Sum of all delegations + self.bond = (total_counted + uncounted)
		pub total_backing: Balance,
		/// Maximum 1 pending request to adjust candidate self bond at any given time
		pub request: Option<CandidateBondRequest>,
		/// Current status of the collator
		pub state: CollatorStatus,
	}

	/// Convey relevant information describing if a delegator was added to the top or bottom
	/// Delegations added to the top yield a new total
	#[derive(Clone, Copy, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
	pub enum DelegatorAdded {
		AddedToTop { new_total: Balance },
		AddedToBottom,
	}

	impl<
			A: Ord + Clone + sp_std::fmt::Debug,
		> CollatorCandidate<A>
	{
		pub fn new(id: A, bond: Balance, liquidity_token: TokenId) -> Self {
			CollatorCandidate {
				id,
				bond,
				liquidity_token,
				delegators: OrderedSet::new(),
				top_delegations: Vec::new(),
				bottom_delegations: Vec::new(),
				total_counted: bond,
				total_backing: bond,
				request: None,
				state: CollatorStatus::default(), // default active
			}
		}
		pub fn is_active(&self) -> bool {
			self.state == CollatorStatus::Active
		}
		pub fn is_leaving(&self) -> bool {
			matches!(self.state, CollatorStatus::Leaving(_))
		}
		pub fn can_leave<T: Config>(&self) -> DispatchResult {
			if let CollatorStatus::Leaving(when) = self.state {
				ensure!(
					<Round<T>>::get().current >= when,
					Error::<T>::CandidateCannotLeaveYet
				);
				Ok(())
			} else {
				Err(Error::<T>::CandidateNotLeaving.into())
			}
		}
		/// Schedule executable increase of collator candidate self bond
		/// Returns the round at which the collator can execute the pending request
		pub fn schedule_bond_more<T: Config>(
			&mut self,
			more: Balance,
		) -> Result<RoundIndex, DispatchError>
		where
			T::AccountId: From<A>,
		{
			// ensure no pending request
			ensure!(
				self.request.is_none(),
				Error::<T>::PendingCandidateRequestAlreadyExists
			);
			let candidate_id: T::AccountId = self.id.clone().into();
			ensure!(
				<T::Currency as MultiTokenReservableCurrency<T::AccountId>>::can_reserve(self.liquidity_token.into(), &candidate_id, more.into()),
				Error::<T>::InsufficientBalance
			);
			let when_executable = <Round<T>>::get().current + T::CandidateBondDelay::get();
			self.request = Some(CandidateBondRequest {
				change: CandidateBondChange::Increase,
				amount: more,
				when_executable,
			});
			Ok(when_executable)
		}
		/// Schedule executable decrease of collator candidate self bond
		/// Returns the round at which the collator can execute the pending request
		pub fn schedule_bond_less<T: Config>(
			&mut self,
			less: Balance,
		) -> Result<RoundIndex, DispatchError>
		{
			// ensure no pending request
			ensure!(
				self.request.is_none(),
				Error::<T>::PendingCandidateRequestAlreadyExists
			);
			// ensure bond above min after decrease
			ensure!(self.bond > less, Error::<T>::CandidateBondBelowMin);
			ensure!(
				self.bond >= T::MinCandidateStk::get().saturating_add(less),
				Error::<T>::CandidateBondBelowMin
			);
			let when_executable = <Round<T>>::get().current + T::CandidateBondDelay::get();
			self.request = Some(CandidateBondRequest {
				change: CandidateBondChange::Decrease,
				amount: less,
				when_executable,
			});
			Ok(when_executable)
		}
		/// Execute pending request to change the collator self bond
		/// Returns the event to be emitted
		pub fn execute_pending_request<T: Config>(&mut self) -> Result<Event<T>, DispatchError>
		where
			T::AccountId: From<A>,
		{
			let request = self
				.request
				.ok_or(Error::<T>::PendingCandidateRequestsDNE)?;
			ensure!(
				request.when_executable <= <Round<T>>::get().current,
				Error::<T>::PendingCandidateRequestNotDueYet
			);
			let caller: T::AccountId = self.id.clone().into();
			let event = match request.change {
				CandidateBondChange::Increase => {
					T::Currency::reserve(self.liquidity_token.into(), &caller, request.amount.into())?;
					let new_total = <Total<T>>::get(self.liquidity_token).saturating_add(request.amount);
					<Total<T>>::insert(self.liquidity_token, new_total);
					self.bond += request.amount;
					
					self.total_counted += request.amount;
					self.total_backing += request.amount;
					Event::CandidateBondedMore(
						self.id.clone().into(),
						request.amount,
						self.bond,
					)
				}
				CandidateBondChange::Decrease => {
					T::Currency::unreserve(self.liquidity_token.into(), &caller, request.amount.into());
					let new_total_staked = <Total<T>>::get(self.liquidity_token).saturating_sub(request.amount);
					<Total<T>>::insert(self.liquidity_token, new_total_staked);
					// Arithmetic assumptions are self.bond > less && self.bond - less > CollatorMinBond
					// (assumptions enforced by `schedule_bond_less`; if storage corrupts, must re-verify)
					self.bond -= request.amount;
					
					self.total_counted -= request.amount;
					self.total_backing -= request.amount;
					Event::CandidateBondedLess(
						self.id.clone().into(),
						request.amount.into(),
						self.bond.into(),
					)
				}
			};
			// reset s.t. no pending request
			self.request = None;
			// update candidate pool value because it must change if self bond changes
			if self.is_active() {
				Pallet::<T>::update_active(self.id.clone().into(), self.total_counted, self.liquidity_token);
			}
			Ok(event)
		}
		/// Cancel pending request to change the collator self bond
		pub fn cancel_pending_request<T: Config>(&mut self) -> Result<Event<T>, DispatchError>
		where
			T::AccountId: From<A>,
		{
			let request = self
				.request
				.ok_or(Error::<T>::PendingCandidateRequestsDNE)?;
			let event = Event::CancelledCandidateBondChange(self.id.clone().into(), request.into());
			self.request = None;
			Ok(event)
		}
		/// Infallible sorted insertion
		/// caller must verify !self.delegators.contains(delegation.owner) before call
		pub fn add_top_delegation(&mut self, delegation: Bond<A>) {
			match self
				.top_delegations
				.binary_search_by(|x| delegation.amount.cmp(&x.amount))
			{
				Ok(i) => self.top_delegations.insert(i, delegation),
				Err(i) => self.top_delegations.insert(i, delegation),
			}
		}
		/// Infallible sorted insertion
		/// caller must verify !self.delegators.contains(delegation.owner) before call
		pub fn add_bottom_delegation(&mut self, delegation: Bond<A>) {
			match self
				.bottom_delegations
				.binary_search_by(|x| x.amount.cmp(&delegation.amount))
			{
				Ok(i) => self.bottom_delegations.insert(i, delegation),
				Err(i) => self.bottom_delegations.insert(i, delegation),
			}
		}
		/// Sort top delegations from greatest to least
		pub fn sort_top_delegations(&mut self) {
			self.top_delegations
				.sort_unstable_by(|a, b| b.amount.cmp(&a.amount));
		}
		/// Sort bottom delegations from least to greatest
		pub fn sort_bottom_delegations(&mut self) {
			self.bottom_delegations
				.sort_unstable_by(|a, b| a.amount.cmp(&b.amount));
		}
		/// Bond account and add delegation. If successful, the return value indicates whether the
		/// delegation is top for the candidate.
		pub fn add_delegation<T: Config>(
			&mut self,
			acc: A,
			amount: Balance,
		) -> Result<DelegatorAdded, DispatchError> {
			ensure!(
				self.delegators.insert(acc.clone()),
				Error::<T>::DelegatorExists
			);
			self.total_backing += amount;
			if (self.top_delegations.len() as u32) < T::MaxDelegatorsPerCandidate::get() {
				self.add_top_delegation(Bond { owner: acc, amount, liquidity_token: self.liquidity_token });
				self.total_counted += amount;
				Ok(DelegatorAdded::AddedToTop {
					new_total: self.total_counted,
				})
			} else {
				// >pop requires push to reset in case isn't pushed to bottom
				let last_delegation_in_top = self
					.top_delegations
					.pop()
					.expect("self.top_delegations.len() >= T::Max exists >= 1 element in top");
				if amount > last_delegation_in_top.amount {
					// update total_counted with positive difference
					self.total_counted += amount - last_delegation_in_top.amount;
					// last delegation already popped from top_delegations
					// insert new delegation into top_delegations
					self.add_top_delegation(Bond { owner: acc, amount, liquidity_token: self.liquidity_token });
					self.add_bottom_delegation(last_delegation_in_top);
					Ok(DelegatorAdded::AddedToTop {
						new_total: self.total_counted,
					})
				} else {
					// >required push to previously popped last delegation into top_delegations
					self.top_delegations.push(last_delegation_in_top);
					self.add_bottom_delegation(Bond { owner: acc, amount, liquidity_token: self.liquidity_token });
					Ok(DelegatorAdded::AddedToBottom)
				}
			}
		}
		/// Return Ok((if_total_counted_changed, delegation_amount))
		pub fn rm_delegator<T: Config>(
			&mut self,
			delegator: A,
		) -> Result<(bool, Balance), DispatchError> {
			ensure!(
				self.delegators.remove(&delegator),
				Error::<T>::DelegatorDNEInDelegatorSet
			);
			let mut delegation_amt: Option<Balance> = None;
			self.top_delegations = self
				.top_delegations
				.clone()
				.into_iter()
				.filter_map(|d| {
					if d.owner != delegator {
						Some(d)
					} else {
						delegation_amt = Some(d.amount);
						None
					}
				})
				.collect();
			// item removed from the top => highest bottom is popped from bottom and pushed to top
			if let Some(amount) = delegation_amt {
				// last element has largest amount as per ordering
				if let Some(last) = self.bottom_delegations.pop() {
					self.total_counted -= amount - last.amount;
					self.add_top_delegation(last);
				} else {
					// no item in bottom delegations so no item from bottom to pop and push up
					self.total_counted -= amount;
				}
				self.total_backing -= amount;
				return Ok((true, amount));
			}
			// else (no item removed from the top)
			self.bottom_delegations = self
				.bottom_delegations
				.clone()
				.into_iter()
				.filter_map(|d| {
					if d.owner != delegator {
						Some(d)
					} else {
						delegation_amt = Some(d.amount);
						None
					}
				})
				.collect();
			// if err, no item with account exists in top || bottom
			let amount = delegation_amt.ok_or(Error::<T>::DelegatorDNEinTopNorBottom)?;
			self.total_backing -= amount;
			Ok((false, amount))
		}
		/// Return true if in_top after call
		/// Caller must verify before call that account is a delegator
		fn increase_delegation(&mut self, delegator: A, more: Balance) -> bool {
			let mut in_top = false;
			for x in &mut self.top_delegations {
				if x.owner == delegator {
					x.amount += more;
					self.total_counted += more;
					self.total_backing += more;
					in_top = true;
					break;
				}
			}
			// if delegator was increased in top delegations
			if in_top {
				self.sort_top_delegations();
				return true;
			}
			// else delegator to increase must exist in bottom
			// >pop requires push later on to reset in case it isn't used
			let lowest_top = self
				.top_delegations
				.pop()
				.expect("any bottom delegations => must exist max top delegations");
			let mut move_2_top = false;
			for x in &mut self.bottom_delegations {
				if x.owner == delegator {
					x.amount += more;
					self.total_backing += more;
					move_2_top = x.amount > lowest_top.amount;
					break;
				}
			}
			if move_2_top {
				self.sort_bottom_delegations();
				let highest_bottom = self.bottom_delegations.pop().expect("updated => exists");
				self.total_counted += highest_bottom.amount - lowest_top.amount;
				self.add_top_delegation(highest_bottom);
				self.add_bottom_delegation(lowest_top);
				true
			} else {
				// >required push to reset top_delegations from earlier pop
				self.top_delegations.push(lowest_top);
				self.sort_bottom_delegations();
				false
			}
		}
		/// Return true if in_top after call
		pub fn decrease_delegation(&mut self, delegator: A, less: Balance) -> bool {
			let mut in_top = false;
			let mut new_lowest_top: Option<Bond<A>> = None;
			for x in &mut self.top_delegations {
				if x.owner == delegator {
					x.amount -= less;
					// if there is at least 1 delegator in bottom delegators, compare it to check
					// if it should be swapped with lowest top delegation and put in top
					// >pop requires push later on to reset in case it isn't used
					if let Some(highest_bottom) = self.bottom_delegations.pop() {
						if highest_bottom.amount > x.amount {
							new_lowest_top = Some(highest_bottom);
						} else {
							// >required push to reset self.bottom_delegations
							self.bottom_delegations.push(highest_bottom);
						}
					}
					in_top = true;
					break;
				}
			}
			if in_top {
				self.sort_top_delegations();
				if let Some(highest_bottom) = new_lowest_top {
					// pop last in top to swap it with top bottom
					let lowest_top = self
						.top_delegations
						.pop()
						.expect("must have >1 item to update, assign in_top = true");
					self.total_counted -= lowest_top.amount + less;
					self.total_counted += highest_bottom.amount;
					self.total_backing -= less;
					self.add_top_delegation(highest_bottom);
					self.add_bottom_delegation(lowest_top);
					return false;
				} else {
					// no existing bottom delegators so update both counters the same magnitude
					self.total_counted -= less;
					self.total_backing -= less;
					return true;
				}
			}
			for x in &mut self.bottom_delegations {
				if x.owner == delegator {
					x.amount -= less;
					self.total_backing -= less;
					break;
				}
			}
			self.sort_bottom_delegations();
			false
		}
		pub fn go_offline(&mut self) {
			self.state = CollatorStatus::Idle;
		}
		pub fn go_online(&mut self) {
			self.state = CollatorStatus::Active;
		}
		pub fn leave<T: Config>(&mut self) -> Result<(RoundIndex, RoundIndex), DispatchError> {
			ensure!(!self.is_leaving(), Error::<T>::CandidateAlreadyLeaving);
			let now = <Round<T>>::get().current;
			let when = now + T::LeaveCandidatesDelay::get();
			self.state = CollatorStatus::Leaving(when);
			Ok((now, when))
		}
	}

	impl<A: Clone> From<CollatorCandidate<A>> for CollatorSnapshot<A> {
		fn from(other: CollatorCandidate<A>) -> CollatorSnapshot<A> {
			CollatorSnapshot {
				bond: other.bond,
				delegations: other.top_delegations,
				total: other.total_counted,
				liquidity_token: other.liquidity_token,
			}
		}
	}

	#[derive(Clone, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
	pub enum DelegatorStatus {
		/// Active with no scheduled exit
		Active,
		/// Schedule exit to revoke all ongoing delegations
		Leaving(RoundIndex),
	}

	#[derive(Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Delegator state
	pub struct Delegator<AccountId> {
		/// Delegator account
		pub id: AccountId,
		/// All current delegations
		pub delegations: OrderedSet<Bond<AccountId>>,
		/// Requests to change delegations, relevant iff active
		pub requests: PendingDelegationRequests<AccountId>,
		/// Status for this delegator
		pub status: DelegatorStatus,
	}

	impl<
			A: Ord + Clone + Default,
		> Delegator<A>
	{
		pub fn new(id: A, collator: A, amount: Balance, liquidity_token: TokenId) -> Self {
			Delegator {
				id,
				delegations: OrderedSet::from(vec![Bond {
					owner: collator,
					amount,
					liquidity_token: liquidity_token
				}]),
				requests: PendingDelegationRequests::new(),
				status: DelegatorStatus::Active,
			}
		}
		pub fn requests(&self) -> BTreeMap<A, DelegationRequest<A>> {
			self.requests.requests.clone()
		}
		pub fn is_active(&self) -> bool {
			matches!(self.status, DelegatorStatus::Active)
		}
		pub fn is_leaving(&self) -> bool {
			matches!(self.status, DelegatorStatus::Leaving(_))
		}
		/// Can only leave if the current round is less than or equal to scheduled execution round
		/// - returns None if not in leaving state
		pub fn can_execute_leave<T: Config>(&self, delegation_weight_hint: u32) -> DispatchResult {
			ensure!(
				delegation_weight_hint >= (self.delegations.0.len() as u32),
				Error::<T>::TooLowDelegationCountToLeaveDelegators
			);
			if let DelegatorStatus::Leaving(when) = self.status {
				ensure!(
					<Round<T>>::get().current >= when,
					Error::<T>::DelegatorCannotLeaveYet
				);
				Ok(())
			} else {
				Err(Error::<T>::DelegatorNotLeaving.into())
			}
		}
		/// Set status to leaving
		pub(crate) fn set_leaving(&mut self, when: RoundIndex) {
			self.status = DelegatorStatus::Leaving(when);
		}
		/// Schedule status to exit
		pub fn schedule_leave<T: Config>(&mut self) -> (RoundIndex, RoundIndex) {
			let now = <Round<T>>::get().current;
			let when = now + T::LeaveDelegatorsDelay::get();
			self.set_leaving(when);
			(now, when)
		}
		/// Set delegator status to active
		pub fn cancel_leave(&mut self) {
			self.status = DelegatorStatus::Active
		}
		pub fn add_delegation(&mut self, bond: Bond<A>) -> bool {
			if self.delegations.insert(bond) {
				true
			} else {
				false
			}
		}
		// Return Some(remaining balance), must be more than MinDelegatorStk
		// Return None if delegation not found
		pub fn rm_delegation(&mut self, collator: A) -> Option<usize> {
			let mut amt: Option<Balance> = None;
			let delegations = self
				.delegations
				.0
				.iter()
				.filter_map(|x| {
					if x.owner == collator {
						amt = Some(x.amount);
						None
					} else {
						Some(x.clone())
					}
				})
				.collect();
			if let Some(_) = amt {
				self.delegations = OrderedSet::from(delegations);
				Some(self.delegations.0.len())
			} else {
				None
			}
		}
		/// Schedule increase delegation
		pub fn schedule_increase_delegation<T: Config>(
			&mut self,
			collator: A,
			more: Balance,
		) -> Result<RoundIndex, DispatchError>
		where
			T::AccountId: From<A>,
		{
			let Bond { liquidity_token, .. } = self
				.delegations
				.0
				.iter()
				.find(|b| b.owner == collator)
				.ok_or(Error::<T>::DelegationDNE)?;
			let delegator_id: T::AccountId = self.id.clone().into();
			ensure!(
				T::Currency::can_reserve((*liquidity_token).into(), &delegator_id, more.into()),
				Error::<T>::InsufficientBalance
			);
			let when = <Round<T>>::get().current + T::DelegationBondDelay::get();
			self.requests.bond_more::<T>(collator, more, when)?;
			Ok(when)
		}
		/// Schedule decrease delegation
		pub fn schedule_decrease_delegation<T: Config>(
			&mut self,
			collator: A,
			less: Balance,
		) -> Result<RoundIndex, DispatchError>
		where
			Balance: Into<Balance> + From<Balance>,
		{
			// get delegation amount
			let Bond { amount, .. } = self
				.delegations
				.0
				.iter()
				.find(|b| b.owner == collator)
				.ok_or(Error::<T>::DelegationDNE)?;
			ensure!(
				*amount >= T::MinDelegation::get().saturating_add(less),
				Error::<T>::DelegationBelowMin
			);
			let when = <Round<T>>::get().current + T::DelegationBondDelay::get();
			self.requests.bond_less::<T>(collator, less, when)?;
			Ok(when)
		}
		/// Schedule revocation for the given collator
		pub fn schedule_revoke<T: Config>(
			&mut self,
			collator: A,
		) -> Result<(RoundIndex, RoundIndex), DispatchError>
		where
			Balance: Into<Balance>,
		{
			// get delegation amount
			let Bond { amount, .. } = self
				.delegations
				.0
				.iter()
				.find(|b| b.owner == collator)
				.ok_or(Error::<T>::DelegationDNE)?;
			let now = <Round<T>>::get().current;
			let when = now + T::RevokeDelegationDelay::get();
			// add revocation to pending requests
			self.requests.revoke::<T>(collator, *amount, when)?;
			Ok((now, when))
		}
		/// Execute pending delegation change request
		pub fn execute_pending_request<T: Config>(&mut self, candidate: A) -> DispatchResult
		where
			Balance: From<Balance> + Into<Balance>,
			T::AccountId: From<A>,
			Delegator<T::AccountId>: From<Delegator<A>>,
		{
			let now = <Round<T>>::get().current;
			let DelegationRequest {
				amount,
				action,
				when_executable,
				..
			} = self
				.requests
				.requests
				.remove(&candidate)
				.ok_or(Error::<T>::PendingDelegationRequestDNE)?;
			ensure!(
				when_executable <= now,
				Error::<T>::PendingDelegationRequestNotDueYet
			);
			let (balance_amt, candidate_id, delegator_id): (
				Balance,
				T::AccountId,
				T::AccountId,
			) = (
				amount.into(),
				candidate.clone().into(),
				self.id.clone().into(),
			);
			match action {
				DelegationChange::Revoke => {
					// revoking last delegation => leaving set of delegators
					let leaving = if self.delegations.0.len() == 1usize {
						true
					} else {
						false
					};
					// remove delegation from delegator state
					self.rm_delegation(candidate.clone());
					// remove delegation from collator state delegations
					Pallet::<T>::delegator_leaves_collator(
						delegator_id.clone(),
						candidate_id.clone(),
					)?;
					Pallet::<T>::deposit_event(Event::DelegationRevoked(
						delegator_id.clone(),
						candidate_id,
						balance_amt,
					));
					if leaving {
						<DelegatorState<T>>::remove(&delegator_id);
						Pallet::<T>::deposit_event(Event::DelegatorLeft(delegator_id, balance_amt));
					} else {
						let nom_st: Delegator<T::AccountId> = self.clone().into();
						<DelegatorState<T>>::insert(&delegator_id, nom_st);
					}
					Ok(())
				}
				DelegationChange::Increase => {
					// increase delegation
					for x in &mut self.delegations.0 {
						if x.owner == candidate {
							x.amount += amount;
							// update collator state delegation
							let mut collator_state = <CandidateState<T>>::get(&candidate_id)
								.ok_or(Error::<T>::CandidateDNE)?;
							T::Currency::reserve(x.liquidity_token.into(), &self.id.clone().into(), balance_amt.into())?;
							let before = collator_state.total_counted;
							let in_top = collator_state
								.increase_delegation(self.id.clone().into(), balance_amt);
							let after = collator_state.total_counted;
							if collator_state.is_active() && (before != after) {
								Pallet::<T>::update_active(candidate_id.clone(), after, collator_state.liquidity_token);
							}
							let new_total_staked = <Total<T>>::get(collator_state.liquidity_token).saturating_add(balance_amt);
							<Total<T>>::insert(collator_state.liquidity_token, new_total_staked);
							<CandidateState<T>>::insert(&candidate_id, collator_state);
							let nom_st: Delegator<T::AccountId> = self.clone().into();
							<DelegatorState<T>>::insert(&delegator_id, nom_st);
							Pallet::<T>::deposit_event(Event::DelegationIncreased(
								delegator_id,
								candidate_id,
								balance_amt,
								in_top,
							));
							return Ok(());
						}
					}
					Err(Error::<T>::DelegationDNE.into())
				}
				DelegationChange::Decrease => {
					// decrease delegation
					for x in &mut self.delegations.0 {
						if x.owner == candidate {
							if x.amount > amount.saturating_add(T::MinDelegation::get()) {
								x.amount -= amount;
								let mut collator = <CandidateState<T>>::get(&candidate_id)
									.ok_or(Error::<T>::CandidateDNE)?;
								T::Currency::unreserve(x.liquidity_token.into(), &delegator_id, balance_amt.into());
								let before = collator.total_counted;
								// need to go into decrease_delegation
								let in_top =
									collator.decrease_delegation(delegator_id.clone(), balance_amt);
								let after = collator.total_counted;
								if collator.is_active() && (before != after) {
									Pallet::<T>::update_active(candidate_id.clone(), after, collator.liquidity_token);
								}
								let new_total_staked =
									<Total<T>>::get(collator.liquidity_token).saturating_sub(balance_amt);
								<Total<T>>::insert(collator.liquidity_token, new_total_staked);
								<CandidateState<T>>::insert(&candidate_id, collator);
								let nom_st: Delegator<T::AccountId> =
									self.clone().into();
								<DelegatorState<T>>::insert(&delegator_id, nom_st);
								Pallet::<T>::deposit_event(Event::DelegationDecreased(
									delegator_id,
									candidate_id,
									balance_amt,
									in_top,
								));
								return Ok(());
							} else {
								// must rm entire delegation if x.amount <= less or cancel request
								return Err(Error::<T>::DelegationBelowMin.into());
							}
						}
					}
					Err(Error::<T>::DelegationDNE.into())
				}
			}
		}
		/// Cancel pending delegation change request
		pub fn cancel_pending_request<T: Config>(
			&mut self,
			candidate: A,
		) -> Result<DelegationRequest<A>, DispatchError> {
			let order = self
				.requests
				.requests
				.remove(&candidate)
				.ok_or(Error::<T>::PendingDelegationRequestDNE)?;
			Ok(order)
		}
	}

	#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Changes requested by the delegator
	/// - limit of 1 ongoing change per delegation
	/// - no changes allowed if delegator is leaving
	pub enum DelegationChange {
		Revoke,
		Increase,
		Decrease,
	}

	#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
	pub struct DelegationRequest<AccountId> {
		pub collator: AccountId,
		pub amount: Balance,
		pub when_executable: RoundIndex,
		pub action: DelegationChange,
	}

	#[derive(Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Pending requests to mutate delegations for each delegator
	pub struct PendingDelegationRequests<AccountId> {
		/// Map from collator -> Request (enforces at most 1 pending request per delegation)
		pub requests: BTreeMap<AccountId, DelegationRequest<AccountId>>,
	}

	impl<A: Ord> Default for PendingDelegationRequests<A> {
		fn default() -> PendingDelegationRequests<A> {
			PendingDelegationRequests {
				requests: BTreeMap::new(),
			}
		}
	}

	impl<
			A: Ord + Clone,
		> PendingDelegationRequests<A>
	{
		/// New default (empty) pending requests
		pub fn new() -> PendingDelegationRequests<A> {
			PendingDelegationRequests::default()
		}
		/// Add bond more order to pending requests
		pub fn bond_more<T: Config>(
			&mut self,
			collator: A,
			amount: Balance,
			when_executable: RoundIndex
		) -> DispatchResult {
			ensure!(
				self.requests.get(&collator).is_none(),
				Error::<T>::PendingDelegationRequestAlreadyExists
			);
			self.requests.insert(
				collator.clone(),
				DelegationRequest {
					collator,
					amount,
					when_executable,
					action: DelegationChange::Increase,
				},
			);
			Ok(())
		}
		/// Add bond less order to pending requests, only succeeds if returns true
		/// - limit is the maximum amount allowed that can be subtracted from the delegation
		/// before it would be below the minimum delegation amount
		pub fn bond_less<T: Config>(
			&mut self,
			collator: A,
			amount: Balance,
			when_executable: RoundIndex
		) -> DispatchResult {
			ensure!(
				self.requests.get(&collator).is_none(),
				Error::<T>::PendingDelegationRequestAlreadyExists
			);
			self.requests.insert(
				collator.clone(),
				DelegationRequest {
					collator,
					amount,
					when_executable,
					action: DelegationChange::Decrease,
				},
			);
			Ok(())
		}
		/// Add revoke order to pending requests
		/// - limit is the maximum amount allowed that can be subtracted from the delegation
		/// before it would be below the minimum delegation amount
		pub fn revoke<T: Config>(
			&mut self,
			collator: A,
			amount: Balance,
			when_executable: RoundIndex
		) -> DispatchResult {
			ensure!(
				self.requests.get(&collator).is_none(),
				Error::<T>::PendingDelegationRequestAlreadyExists
			);
			self.requests.insert(
				collator.clone(),
				DelegationRequest {
					collator,
					amount,
					when_executable,
					action: DelegationChange::Revoke,
				},
			);
			Ok(())
		}
	}

	#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// The current round index and transition information
	pub struct RoundInfo<BlockNumber> {
		/// Current round index
		pub current: RoundIndex,
		/// The first block of the current round
		pub first: BlockNumber,
		/// The length of the current round in number of blocks
		pub length: u32,
	}
	impl<
			B: Copy
				+ sp_std::ops::Add<Output = B>
				+ sp_std::ops::Sub<Output = B>
				+ From<u32>
				+ PartialOrd
				+ One
				+ Zero,
		> RoundInfo<B>
	{
		pub fn new(current: RoundIndex, first: B, length: u32) -> RoundInfo<B> {
			RoundInfo {
				current,
				first,
				length,
			}
		}
		/// Check if the round should be updated
		pub fn should_update(&self, now: B) -> bool {
			now + One::one()  >= self.first + self.length.into()
		}
		/// New round
		pub fn update(&mut self, now: B) {
			self.current += 1u32;
			self.first = now;
		}
	}
	impl<
			B: Copy
				+ sp_std::ops::Add<Output = B>
				+ sp_std::ops::Sub<Output = B>
				+ From<u32>
				+ PartialOrd
				+ One
				+ Zero,
		> Default for RoundInfo<B>
	{
		fn default() -> RoundInfo<B> {
			RoundInfo::new(0u32, Zero::zero(), 20u32)
		}
	}

	#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
	/// Reserve information { account, percent_of_inflation }
	pub struct ParachainBondConfig<AccountId> {
		/// Account which receives funds intended for parachain bond
		pub account: AccountId,
		/// Percent of inflation set aside for parachain bond account
		pub percent: Percent,
	}
	impl<A: Default> Default for ParachainBondConfig<A> {
		fn default() -> ParachainBondConfig<A> {
			ParachainBondConfig {
				account: A::default(),
				percent: Percent::zero(),
			}
		}
	}

	pub(crate) type RoundIndex = u32;
	type RewardPoint = u32;

	/// Configuration trait of this pallet.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Overarching event type
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// The currency type
		type Currency: MultiTokenCurrency<Self::AccountId> + MultiTokenReservableCurrency<Self::AccountId>;
		/// The origin for monetary governance
		type MonetaryGovernanceOrigin: EnsureOrigin<Self::Origin>;
		/// Minimum number of blocks per round
		#[pallet::constant]
		type MinBlocksPerRound: Get<u32>;
		/// Default number of blocks per round at genesis
		#[pallet::constant]
		type DefaultBlocksPerRound: Get<u32>;
		/// Number of rounds that candidates remain bonded before exit request is executable
		#[pallet::constant]
		type LeaveCandidatesDelay: Get<RoundIndex>;
		/// Number of rounds that candidate requests to adjust self-bond must wait to be executable
		#[pallet::constant]
		type CandidateBondDelay: Get<RoundIndex>;
		/// Number of rounds that delegators remain bonded before exit request is executable
		#[pallet::constant]
		type LeaveDelegatorsDelay: Get<RoundIndex>;
		/// Number of rounds that delegations remain bonded before revocation request is executable
		#[pallet::constant]
		type RevokeDelegationDelay: Get<RoundIndex>;
		/// Number of rounds that delegation {more, less} requests must wait before executable
		#[pallet::constant]
		type DelegationBondDelay: Get<RoundIndex>;
		/// Number of rounds after which block authors are rewarded
		#[pallet::constant]
		type RewardPaymentDelay: Get<RoundIndex>;
		/// Minimum number of selected candidates every round
		#[pallet::constant]
		type MinSelectedCandidates: Get<u32>;
		/// Maximum delegators counted per candidate
		#[pallet::constant]
		type MaxDelegatorsPerCandidate: Get<u32>;
		/// Maximum delegations per delegator
		#[pallet::constant]
		type MaxDelegationsPerDelegator: Get<u32>;
		/// Default commission due to collators, is `CollatorCommission` storage value in genesis
		#[pallet::constant]
		type DefaultCollatorCommission: Get<Perbill>;
		/// Default parachain bond account 
		#[pallet::constant]
		type DefaultParachainBondReserveAccount: Get<Self::AccountId>;
		/// Default percent of inflation set aside for parachain bond account
		#[pallet::constant]
		type DefaultParachainBondReservePercent: Get<Percent>;
		/// Minimum stake required for any candidate to be in `SelectedCandidates` for the round
		#[pallet::constant]
		type MinCollatorStk: Get<Balance>;
		/// Minimum stake required for any account to be a collator candidate
		#[pallet::constant]
		type MinCandidateStk: Get<Balance>;
		/// Minimum stake for any registered on-chain account to delegate
		#[pallet::constant]
		type MinDelegation: Get<Balance>;
		/// The native token used for payouts
		#[pallet::constant]
		type NativeTokenId: Get<TokenId>;
		/// The valuator for our staking liquidity tokens, i.e., XYK
		/// This should never return (_, Zero::zero())
		type StakingLiquidityTokenValuator: Valuate;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		DelegatorDNE,
		DelegatorDNEinTopNorBottom,
		DelegatorDNEInDelegatorSet,
		CandidateDNE,
		DelegationDNE,
		DelegatorExists,
		CandidateExists,
		CandidateBondBelowMin,
		InsufficientBalance,
		DelegationBelowMin,
		AlreadyOffline,
		AlreadyActive,
		DelegatorAlreadyLeaving,
		DelegatorNotLeaving,
		DelegatorCannotLeaveYet,
		CannotDelegateIfLeaving,
		CandidateAlreadyLeaving,
		CandidateNotLeaving,
		CandidateCannotLeaveYet,
		CannotGoOnlineIfLeaving,
		ExceedMaxDelegationsPerDelegator,
		AlreadyDelegatedCandidate,
		InvalidSchedule,
		CannotSetBelowMin,
		NoWritingSameValue,
		TooLowCandidateCountWeightHintJoinCandidates,
		TooLowCandidateCountWeightHintCancelLeaveCandidates,
		TooLowCandidateCountToLeaveCandidates,
		TooLowDelegationCountToDelegate,
		TooLowCandidateDelegationCountToDelegate,
		TooLowDelegationCountToLeaveDelegators,
		PendingCandidateRequestsDNE,
		PendingCandidateRequestAlreadyExists,
		PendingCandidateRequestNotDueYet,
		PendingDelegationRequestDNE,
		PendingDelegationRequestAlreadyExists,
		PendingDelegationRequestNotDueYet,
		StakingLiquidityTokenNotListed,
		TooLowCurrentStakingLiquidityTokensCount,
		StakingLiquidityTokenAlreadyListed,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(crate) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Starting Block, Round, Number of Collators Selected, Total Balance
		NewRound(T::BlockNumber, RoundIndex, u32, Balance),
		/// Account, Amount Locked, New Total Amt Locked
		JoinedCollatorCandidates(T::AccountId, Balance, Balance),
		/// Round, Collator Account, Total Exposed Amount (includes all delegations)
		CollatorChosen(RoundIndex, T::AccountId, Balance),
		/// Candidate, Amount To Increase, Round at which request can be executed by caller
		CandidateBondMoreRequested(T::AccountId, Balance, RoundIndex),
		/// Candidate, Amount To Decrease, Round at which request can be executed by caller
		CandidateBondLessRequested(T::AccountId, Balance, RoundIndex),
		/// Candidate, Amount, New Bond Total
		CandidateBondedMore(T::AccountId, Balance, Balance),
		/// Candidate, Amount, New Bond
		CandidateBondedLess(T::AccountId, Balance, Balance),
		/// Round Offline, Candidate
		CandidateWentOffline(RoundIndex, T::AccountId),
		/// Round Online, Candidate
		CandidateBackOnline(RoundIndex, T::AccountId),
		/// Round At Which Exit Is Allowed, Candidate, Scheduled Exit
		CandidateScheduledExit(RoundIndex, T::AccountId, RoundIndex),
		/// Candidate
		CancelledCandidateExit(T::AccountId),
		/// Candidate, Cancelled Request
		CancelledCandidateBondChange(T::AccountId, CandidateBondRequest),
		/// Ex-Candidate, Amount Unlocked, New Total Amt Locked
		CandidateLeft(T::AccountId, Balance, Balance),
		/// Delegator, Candidate, Amount to be increased, Round at which can be executed
		DelegationIncreaseScheduled(T::AccountId, T::AccountId, Balance, RoundIndex),
		/// Delegator, Candidate, Amount to be decreased, Round at which can be executed
		DelegationDecreaseScheduled(T::AccountId, T::AccountId, Balance, RoundIndex),
		// Delegator, Candidate, Amount, If in top delegations for candidate after increase
		DelegationIncreased(T::AccountId, T::AccountId, Balance, bool),
		// Delegator, Candidate, Amount, If in top delegations for candidate after decrease
		DelegationDecreased(T::AccountId, T::AccountId, Balance, bool),
		/// Round, Delegator, Scheduled Exit
		DelegatorExitScheduled(RoundIndex, T::AccountId, RoundIndex),
		/// Round, Delegator, Candidate, Scheduled Exit
		DelegationRevocationScheduled(RoundIndex, T::AccountId, T::AccountId, RoundIndex),
		/// Delegator, Amount Unstaked
		DelegatorLeft(T::AccountId, Balance),
		/// Delegator, Candidate, Amount Unstaked
		DelegationRevoked(T::AccountId, T::AccountId, Balance),
		/// Delegator
		DelegatorExitCancelled(T::AccountId),
		/// Delegator, Cancelled Request
		CancelledDelegationRequest(T::AccountId, DelegationRequest<T::AccountId>),
		/// Delegator, Amount Locked, Candidate, Delegator Position with New Total Counted if in Top
		Delegation(
			T::AccountId,
			Balance,
			T::AccountId,
			DelegatorAdded,
		),
		/// Delegator, Candidate, Amount Unstaked, New Total Amt Staked for Candidate
		DelegatorLeftCandidate(T::AccountId, T::AccountId, Balance, Balance),
		/// Delegator, Collator, Due reward (as per counted delegation for collator)
		DelegatorDueReward(T::AccountId, T::AccountId, Balance),
		/// Paid the account (delegator or collator) the balance as liquid rewards
		Rewarded(T::AccountId, Balance),
		/// Transferred to account which holds funds reserved for parachain bond
		ReservedForParachainBond(T::AccountId, Balance),
		/// Account (re)set for parachain bond treasury [old, new]
		ParachainBondAccountSet(T::AccountId, T::AccountId),
		/// Percent of inflation reserved for parachain bond (re)set [old, new]
		ParachainBondReservePercentSet(Percent, Percent),
		/// Annual inflation input (first 3) was used to derive new per-round inflation (last 3)
		InflationSet(Perbill, Perbill, Perbill, Perbill, Perbill, Perbill),
		/// Staking expectations set
		StakeExpectationsSet(Balance, Balance, Balance),
		/// Set total selected candidates to this value [old, new]
		TotalSelectedSet(u32, u32),
		/// Set collator commission to this value [old, new]
		CollatorCommissionSet(Perbill, Perbill),
		/// Set blocks per round [current_round, first_block, old, new, new_per_round_inflation]
		BlocksPerRoundSet(
			RoundIndex,
			T::BlockNumber,
			u32,
			u32,
			Perbill,
			Perbill,
			Perbill,
		),
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		
	}

	#[pallet::storage]
	#[pallet::getter(fn collator_commission)]
	/// Commission percent taken off of rewards for all collators
	type CollatorCommission<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn total_selected)]
	/// The total candidates selected every round
	type TotalSelected<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn parachain_bond_info)]
	/// Parachain bond config info { account, percent_of_inflation }
	type ParachainBondInfo<T: Config> =
		StorageValue<_, ParachainBondConfig<T::AccountId>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn round)]
	/// Current round index and next round scheduled transition
	pub(crate) type Round<T: Config> = StorageValue<_, RoundInfo<T::BlockNumber>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn delegator_state)]
	/// Get delegator state associated with an account if account is delegating else None
	pub(crate) type DelegatorState<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		Delegator<T::AccountId>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn candidate_state)]
	/// Get collator candidate state associated with an account if account is a candidate else None
	pub(crate) type CandidateState<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		CollatorCandidate<T::AccountId>,
		OptionQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn selected_candidates)]
	/// The collator candidates selected for the current round
	type SelectedCandidates<T: Config> = StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn total)]
	/// Total capital locked by this staking pallet
	type Total<T: Config> = StorageMap<_, Twox64Concat, TokenId, Balance, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn candidate_pool)]
	/// The pool of collator candidates, each with their total backing stake
	type CandidatePool<T: Config> =
		StorageValue<_, OrderedSet<Bond<T::AccountId>>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn at_stake)]
	/// Snapshot of collator delegation stake at the start of the round
	pub type AtStake<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		RoundIndex,
		Twox64Concat,
		T::AccountId,
		CollatorSnapshot<T::AccountId>,
		ValueQuery,
	>;
	
	#[pallet::storage]
	#[pallet::getter(fn staked)]
	/// Total counted stake for selected candidates in the round
	pub type Staked<T: Config> = StorageMap<_, Twox64Concat, RoundIndex, Balance, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn relevant_staked)]
	/// Total counted stake for selected candidates in the round
	pub type RelevantStaked<T: Config> = StorageMap<_, Twox64Concat, RoundIndex, Balance, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn inflation_config)]
	/// Inflation configuration
	pub type InflationConfig<T: Config> = StorageValue<_, InflationInfo<Balance>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn points)]
	/// Total points awarded to collators for block production in the round
	pub type Points<T: Config> = StorageMap<_, Twox64Concat, RoundIndex, RewardPoint, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn awarded_pts)]
	/// Points for each collator per round
	pub type AwardedPts<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		RoundIndex,
		Twox64Concat,
		T::AccountId,
		RewardPoint,
		ValueQuery,
	>;

	#[pallet::storage]
	#[pallet::getter(fn staking_liquidity_tokens)]
	/// Points for each collator per round
	pub type StakingLiquidityTokens<T: Config> = StorageValue<
		_,
		BTreeMap<TokenId, Option<(Balance, Balance)>>,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub candidates: Vec<(T::AccountId, Balance, TokenId)>,
		pub delegations: Vec<(T::AccountId, T::AccountId, Balance)>,
		pub inflation_config: InflationInfo<Balance>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				candidates: vec![],
				delegations: vec![],
				..Default::default()
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			<InflationConfig<T>>::put(self.inflation_config.clone());
			let mut liquidity_token_list: Vec<TokenId> = self.candidates.iter().cloned().map(|(_,_,l)| l).collect::<Vec<TokenId>>();
			liquidity_token_list.dedup();
			for (i, liquidity_token) in liquidity_token_list.iter().enumerate(){
				if let Err(error) = <Pallet<T>>::add_staking_liquidity_token(
					RawOrigin::Root.into(),
					PairedOrLiquidityToken::Liquidity(*liquidity_token),
					i as u32,	
				) {
					log::warn!("Adding staking liquidity token failed in genesis with error {:?}", error);
				}
			}
			let mut candidate_count = 0u32;
			// Initialize the candidates
			for &(ref candidate, balance, liquidity_token) in &self.candidates {
				assert!(
					T::Currency::free_balance(liquidity_token.into(), candidate).into() >= balance,
					"Account does not have enough balance to bond as a candidate."
				);
				candidate_count += 1u32;
				if let Err(error) = <Pallet<T>>::join_candidates(
					T::Origin::from(Some(candidate.clone()).into()),
					balance,
					liquidity_token,
					candidate_count,
				) {
					log::warn!("Join candidates failed in genesis with error {:?}", error);
				} else {
					candidate_count += 1u32;
				}
			}
			let mut col_delegator_count: BTreeMap<T::AccountId, u32> = BTreeMap::new();
			let mut del_delegation_count: BTreeMap<T::AccountId, u32> = BTreeMap::new();
			// Initialize the delegations
			for &(ref delegator, ref target, balance) in &self.delegations {
				let associated_collator = self.candidates.iter().find(|b| b.0 == *target);
				let collator_liquidity_token = associated_collator.expect("Delegation to non-existant collator").2;
				assert!(
					T::Currency::free_balance(collator_liquidity_token.into(), delegator).into() >= balance,
					"Account does not have enough balance to place delegation."
				);
				let cd_count = if let Some(x) = col_delegator_count.get(target) {
					*x
				} else {
					0u32
				};
				let dd_count = if let Some(x) = del_delegation_count.get(delegator) {
					*x
				} else {
					0u32
				};
				if let Err(error) = <Pallet<T>>::delegate(
					T::Origin::from(Some(delegator.clone()).into()),
					target.clone(),
					balance,
					cd_count,
					dd_count,
				) {
					log::warn!("Delegate failed in genesis with error {:?}", error);
				} else {
					if let Some(x) = col_delegator_count.get_mut(target) {
						*x += 1u32;
					} else {
						col_delegator_count.insert(target.clone(), 1u32);
					};
					if let Some(x) = del_delegation_count.get_mut(delegator) {
						*x += 1u32;
					} else {
						del_delegation_count.insert(delegator.clone(), 1u32);
					};
				}
			}
			// Set collator commission to default config
			<CollatorCommission<T>>::put(T::DefaultCollatorCommission::get());
			// Set parachain bond config to default config
			<ParachainBondInfo<T>>::put(ParachainBondConfig {
				// must be set soon; if not => due inflation will be sent to collators/delegators
				account: T::DefaultParachainBondReserveAccount::get(),
				percent: T::DefaultParachainBondReservePercent::get(),
			});
			// Set total selected candidates to minimum config
			<TotalSelected<T>>::put(T::MinSelectedCandidates::get());
			// Choose top TotalSelected collator candidates
			let (v_count, _, total_relevant_exposure, total_round_exposure) = <Pallet<T>>::select_top_candidates(1u32);
			// Start Round 1 at Block 0
			let round: RoundInfo<T::BlockNumber> =
				RoundInfo::new(0u32, 0u32.into(), T::DefaultBlocksPerRound::get());
			<Round<T>>::put(round);
			// Snapshot total stake
			<Staked<T>>::insert(1u32, total_round_exposure);
			// So that round 0 can be rewarded
			for atstake in <AtStake<T>>::iter_prefix(1u32){
				<AtStake<T>>::insert(0u32, atstake.0, atstake.1);
			}
			<Staked<T>>::insert(0u32, total_round_exposure);
			<Pallet<T>>::deposit_event(Event::NewRound(
				T::BlockNumber::zero(),
				0u32,
				v_count,
				total_relevant_exposure,
			));
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(<T as Config>::WeightInfo::set_staking_expectations())]
		/// Set the expectations for total staked. These expectations determine the issuance for
		/// the round according to logic in `fn compute_issuance`
		pub fn set_staking_expectations(
			origin: OriginFor<T>,
			expectations: Range<Balance>,
		) -> DispatchResultWithPostInfo {
			T::MonetaryGovernanceOrigin::ensure_origin(origin)?;
			ensure!(expectations.is_valid(), Error::<T>::InvalidSchedule);
			let mut config = <InflationConfig<T>>::get();
			ensure!(
				config.expect != expectations,
				Error::<T>::NoWritingSameValue
			);
			config.set_expectations(expectations);
			Self::deposit_event(Event::StakeExpectationsSet(
				config.expect.min,
				config.expect.ideal,
				config.expect.max,
			));
			<InflationConfig<T>>::put(config);
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_inflation())]
		/// Set the annual inflation rate to derive per-round inflation
		pub fn set_inflation(
			origin: OriginFor<T>,
			schedule: Range<Perbill>,
		) -> DispatchResultWithPostInfo {
			T::MonetaryGovernanceOrigin::ensure_origin(origin)?;
			ensure!(schedule.is_valid(), Error::<T>::InvalidSchedule);
			let mut config = <InflationConfig<T>>::get();
			ensure!(config.annual != schedule, Error::<T>::NoWritingSameValue);
			config.annual = schedule;
			config.set_round_from_annual::<T>(schedule);
			Self::deposit_event(Event::InflationSet(
				config.annual.min,
				config.annual.ideal,
				config.annual.max,
				config.round.min,
				config.round.ideal,
				config.round.max,
			));
			<InflationConfig<T>>::put(config);
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_parachain_bond_account())]
		/// Set the account that will hold funds set aside for parachain bond
		pub fn set_parachain_bond_account(
			origin: OriginFor<T>,
			new: T::AccountId,
		) -> DispatchResultWithPostInfo {
			T::MonetaryGovernanceOrigin::ensure_origin(origin)?;
			let ParachainBondConfig {
				account: old,
				percent,
			} = <ParachainBondInfo<T>>::get();
			ensure!(old != new, Error::<T>::NoWritingSameValue);
			<ParachainBondInfo<T>>::put(ParachainBondConfig {
				account: new.clone(),
				percent,
			});
			Self::deposit_event(Event::ParachainBondAccountSet(old, new));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_parachain_bond_reserve_percent())]
		/// Set the percent of inflation set aside for parachain bond
		pub fn set_parachain_bond_reserve_percent(
			origin: OriginFor<T>,
			new: Percent,
		) -> DispatchResultWithPostInfo {
			T::MonetaryGovernanceOrigin::ensure_origin(origin)?;
			let ParachainBondConfig {
				account,
				percent: old,
			} = <ParachainBondInfo<T>>::get();
			ensure!(old != new, Error::<T>::NoWritingSameValue);
			<ParachainBondInfo<T>>::put(ParachainBondConfig {
				account,
				percent: new,
			});
			Self::deposit_event(Event::ParachainBondReservePercentSet(old, new));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_total_selected())]
		/// Set the total number of collator candidates selected per round
		/// - changes are not applied until the start of the next round
		pub fn set_total_selected(origin: OriginFor<T>, new: u32) -> DispatchResultWithPostInfo {
			frame_system::ensure_root(origin)?;
			ensure!(
				new >= T::MinSelectedCandidates::get(),
				Error::<T>::CannotSetBelowMin
			);
			let old = <TotalSelected<T>>::get();
			ensure!(old != new, Error::<T>::NoWritingSameValue);
			<TotalSelected<T>>::put(new);
			Self::deposit_event(Event::TotalSelectedSet(old, new));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_collator_commission())]
		/// Set the commission for all collators
		pub fn set_collator_commission(
			origin: OriginFor<T>,
			new: Perbill,
		) -> DispatchResultWithPostInfo {
			frame_system::ensure_root(origin)?;
			let old = <CollatorCommission<T>>::get();
			ensure!(old != new, Error::<T>::NoWritingSameValue);
			<CollatorCommission<T>>::put(new);
			Self::deposit_event(Event::CollatorCommissionSet(old, new));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::set_blocks_per_round())]
		/// Set blocks per round
		/// - if called with `new` less than length of current round, will transition immediately
		/// in the next block
		/// - also updates per-round inflation config
		pub fn set_blocks_per_round(origin: OriginFor<T>, new: u32) -> DispatchResultWithPostInfo {
			frame_system::ensure_root(origin)?;
			ensure!(
				new >= T::MinBlocksPerRound::get(),
				Error::<T>::CannotSetBelowMin
			);
			let mut round = <Round<T>>::get();
			let (now, first, old) = (round.current, round.first, round.length);
			ensure!(old != new, Error::<T>::NoWritingSameValue);
			round.length = new;
			// update per-round inflation given new rounds per year
			let mut inflation_config = <InflationConfig<T>>::get();
			inflation_config.reset_round(new);
			<Round<T>>::put(round);
			Self::deposit_event(Event::BlocksPerRoundSet(
				now,
				first,
				old,
				new,
				inflation_config.round.min,
				inflation_config.round.ideal,
				inflation_config.round.max,
			));
			<InflationConfig<T>>::put(inflation_config);
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::join_candidates(*candidate_count))]
		/// Join the set of collator candidates
		pub fn join_candidates(
			origin: OriginFor<T>,
			bond: Balance,
			liquidity_token: TokenId,
			candidate_count: u32,
		) -> DispatchResultWithPostInfo {
			let acc = ensure_signed(origin)?;
			ensure!(!Self::is_candidate(&acc), Error::<T>::CandidateExists);
			ensure!(!Self::is_delegator(&acc), Error::<T>::DelegatorExists);
			ensure!(
				<StakingLiquidityTokens<T>>::get().contains_key(&liquidity_token),
				Error::<T>::StakingLiquidityTokenNotListed
			);
			ensure!(
				bond >= T::MinCandidateStk::get(),
				Error::<T>::CandidateBondBelowMin
			);
			let mut candidates = <CandidatePool<T>>::get();
			let old_count = candidates.0.len() as u32;
			ensure!(
				candidate_count >= old_count,
				Error::<T>::TooLowCandidateCountWeightHintJoinCandidates
			);
			ensure!(
				candidates.insert(Bond {
					owner: acc.clone(),
					amount: bond,
					liquidity_token: liquidity_token,
				}),
				Error::<T>::CandidateExists
			);
			T::Currency::reserve(liquidity_token.into(), &acc, bond.into())?;
			let candidate = CollatorCandidate::new(acc.clone(), bond, liquidity_token);
			<CandidateState<T>>::insert(&acc, candidate);
			<CandidatePool<T>>::put(candidates);
			let new_total = <Total<T>>::get(liquidity_token).saturating_add(bond);
			<Total<T>>::insert(liquidity_token, new_total);
			Self::deposit_event(Event::JoinedCollatorCandidates(acc, bond, new_total));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_leave_candidates(*candidate_count))]
		/// Request to leave the set of candidates. If successful, the account is immediately
		/// removed from the candidate pool to prevent selection as a collator.
		pub fn schedule_leave_candidates(
			origin: OriginFor<T>,
			candidate_count: u32,
		) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let (now, when) = state.leave::<T>()?;
			let mut candidates = <CandidatePool<T>>::get();
			ensure!(
				candidate_count >= candidates.0.len() as u32,
				Error::<T>::TooLowCandidateCountToLeaveCandidates
			);
			if candidates.remove(&Bond::from_owner(collator.clone())) {
				<CandidatePool<T>>::put(candidates);
			}
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CandidateScheduledExit(now, collator, when));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::execute_leave_candidates())]
		/// Execute leave candidates request
		pub fn execute_leave_candidates(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			let state = <CandidateState<T>>::get(&candidate).ok_or(Error::<T>::CandidateDNE)?;
			state.can_leave::<T>()?;
			
			let return_stake = |bond: Bond<T::AccountId>| {
				T::Currency::unreserve(bond.liquidity_token.into(), &bond.owner, bond.amount.into());
				// remove delegation from delegator state
				let mut delegator = DelegatorState::<T>::get(&bond.owner).expect(
					"Collator state and delegator state are consistent. 
						Collator state has a record of this delegation. Therefore, 
						Delegator state also has a record. qed.",
				);
				if let Some(remaining_delegations) = delegator.rm_delegation(candidate.clone()) {
					if remaining_delegations.is_zero() {
						<DelegatorState<T>>::remove(&bond.owner);
					} else {
						<DelegatorState<T>>::insert(&bond.owner, delegator);
					}
				}
			};
			// return all top delegations
			for bond in state.top_delegations {
				return_stake(bond);
			}
			// return all bottom delegations
			for bond in state.bottom_delegations {
				return_stake(bond);
			}
			// return stake to collator
			T::Currency::unreserve(state.liquidity_token.into(), &state.id, state.bond.into());
			<CandidateState<T>>::remove(&candidate);
			let new_total_staked = <Total<T>>::get(state.liquidity_token).saturating_sub(state.total_backing);
			<Total<T>>::insert(state.liquidity_token, new_total_staked);
			Self::deposit_event(Event::CandidateLeft(
				candidate,
				state.total_backing,
				new_total_staked,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::cancel_leave_candidates(*candidate_count))]
		/// Cancel open request to leave candidates
		/// - only callable by collator account
		/// - result upon successful call is the candidate is active in the candidate pool
		pub fn cancel_leave_candidates(
			origin: OriginFor<T>,
			candidate_count: u32,
		) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			ensure!(state.is_leaving(), Error::<T>::CandidateNotLeaving);
			state.go_online();
			let mut candidates = <CandidatePool<T>>::get();
			ensure!(
				candidates.0.len() as u32 <= candidate_count,
				Error::<T>::TooLowCandidateCountWeightHintCancelLeaveCandidates
			);
			ensure!(
				candidates.insert(Bond {
					owner: collator.clone(),
					amount: state.total_counted,
					liquidity_token: state.liquidity_token
				}),
				Error::<T>::AlreadyActive
			);
			<CandidatePool<T>>::put(candidates);
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CancelledCandidateExit(collator));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::go_offline())]
		/// Temporarily leave the set of collator candidates without unbonding
		pub fn go_offline(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			ensure!(state.is_active(), Error::<T>::AlreadyOffline);
			state.go_offline();
			let mut candidates = <CandidatePool<T>>::get();
			if candidates.remove(&Bond::from_owner(collator.clone())) {
				<CandidatePool<T>>::put(candidates);
			}
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CandidateWentOffline(
				<Round<T>>::get().current,
				collator,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::go_online())]
		/// Rejoin the set of collator candidates if previously had called `go_offline`
		pub fn go_online(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			ensure!(!state.is_active(), Error::<T>::AlreadyActive);
			ensure!(!state.is_leaving(), Error::<T>::CannotGoOnlineIfLeaving);
			state.go_online();
			let mut candidates = <CandidatePool<T>>::get();
			ensure!(
				candidates.insert(Bond {
					owner: collator.clone(),
					amount: state.total_counted,
					liquidity_token: state.liquidity_token
				}),
				Error::<T>::AlreadyActive
			);
			<CandidatePool<T>>::put(candidates);
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CandidateBackOnline(
				<Round<T>>::get().current,
				collator,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_candidate_bond_more())]
		/// Request by collator candidate to increase self bond by `more`
		pub fn schedule_candidate_bond_more(
			origin: OriginFor<T>,
			more: Balance,
		) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let when = state.schedule_bond_more::<T>(more)?;
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CandidateBondMoreRequested(collator, more, when));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_candidate_bond_less())]
		/// Request by collator candidate to decrease self bond by `less`
		pub fn schedule_candidate_bond_less(
			origin: OriginFor<T>,
			less: Balance,
		) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let when = state.schedule_bond_less::<T>(less)?;
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::CandidateBondLessRequested(collator, less, when));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::execute_candidate_bond_more())]
		/// Execute pending request to adjust the collator candidate self bond
		pub fn execute_candidate_bond_request(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?; // we may want to reward this if caller != candidate
			let mut state = <CandidateState<T>>::get(&candidate).ok_or(Error::<T>::CandidateDNE)?;
			let event = state.execute_pending_request::<T>()?;
			<CandidateState<T>>::insert(&candidate, state);
			Self::deposit_event(event);
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::cancel_candidate_bond_more())]
		/// Cancel pending request to adjust the collator candidate self bond
		pub fn cancel_candidate_bond_request(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let collator = ensure_signed(origin)?;
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let event = state.cancel_pending_request::<T>()?;
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(event);
			Ok(().into())
		}
		#[pallet::weight(
			<T as Config>::WeightInfo::delegate(
				*candidate_delegation_count,
				*delegation_count
			)
		)]
		/// If caller is not a delegator and not a collator, then join the set of delegators
		/// If caller is a delegator, then makes delegation to change their delegation state
		pub fn delegate(
			origin: OriginFor<T>,
			collator: T::AccountId,
			amount: Balance,
			candidate_delegation_count: u32,
			delegation_count: u32,
		) -> DispatchResultWithPostInfo {
			let acc = ensure_signed(origin)?;
			let mut collator_state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let delegator_state = if let Some(mut state) = <DelegatorState<T>>::get(&acc) {
				ensure!(state.is_active(), Error::<T>::CannotDelegateIfLeaving);
				// delegation after first
				ensure!(
					amount >= T::MinDelegation::get(),
					Error::<T>::DelegationBelowMin
				);
				ensure!(
					delegation_count >= state.delegations.0.len() as u32,
					Error::<T>::TooLowDelegationCountToDelegate
				);
				ensure!(
					(state.delegations.0.len() as u32) < T::MaxDelegationsPerDelegator::get(),
					Error::<T>::ExceedMaxDelegationsPerDelegator
				);
				ensure!(
					state.add_delegation(Bond {
						owner: collator.clone(),
						amount: amount,
						liquidity_token: collator_state.liquidity_token,
					}),
					Error::<T>::AlreadyDelegatedCandidate
				);
				state
			} else {
				ensure!(
				amount >= T::MinDelegation::get(),
				Error::<T>::DelegationBelowMin
			);
				ensure!(!Self::is_candidate(&acc), Error::<T>::CandidateExists);
				Delegator::new(acc.clone(), collator.clone(), amount, collator_state.liquidity_token)
			};
			ensure!(
				candidate_delegation_count >= collator_state.delegators.0.len() as u32,
				Error::<T>::TooLowCandidateDelegationCountToDelegate
			);
			let delegator_position = collator_state.add_delegation::<T>(acc.clone(), amount)?;
			T::Currency::reserve(collator_state.liquidity_token.into(), &acc, amount.into())?;
			if let DelegatorAdded::AddedToTop { new_total } = delegator_position {
				if collator_state.is_active() {
					// collator in candidate pool
					Self::update_active(collator.clone(), new_total, collator_state.liquidity_token);
				}
			}
			let new_total_locked = <Total<T>>::get(collator_state.liquidity_token).saturating_add(amount);
			<Total<T>>::insert(collator_state.liquidity_token, new_total_locked);
			<CandidateState<T>>::insert(&collator, collator_state);
			<DelegatorState<T>>::insert(&acc, delegator_state);
			Self::deposit_event(Event::Delegation(acc, amount, collator, delegator_position));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_leave_delegators())]
		/// Request to leave the set of delegators. If successful, the caller is scheduled
		/// to be allowed to exit. Success forbids future delegator actions until the request is
		/// invoked or cancelled.
		pub fn schedule_leave_delegators(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let acc = ensure_signed(origin)?;
			let mut state = <DelegatorState<T>>::get(&acc).ok_or(Error::<T>::DelegatorDNE)?;
			ensure!(!state.is_leaving(), Error::<T>::DelegatorAlreadyLeaving);
			let (now, when) = state.schedule_leave::<T>();
			<DelegatorState<T>>::insert(&acc, state);
			Self::deposit_event(Event::DelegatorExitScheduled(now, acc, when));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::execute_leave_delegators(*delegation_count))]
		/// Execute the right to exit the set of delegators and revoke all ongoing delegations.
		pub fn execute_leave_delegators(
			origin: OriginFor<T>,
			delegator: T::AccountId,
			delegation_count: u32,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			let state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			state.can_execute_leave::<T>(delegation_count)?;
			let mut amount_unstaked: Balance = Zero::zero();
			for bond in state.delegations.0 {
				amount_unstaked = amount_unstaked.saturating_add(bond.amount);
				if let Err(error) =
					Self::delegator_leaves_collator(delegator.clone(), bond.owner.clone())
				{
					log::warn!(
						"STORAGE CORRUPTED \nDelegator leaving collator failed with error: {:?}",
						error
					);
				}
			}
			<DelegatorState<T>>::remove(&delegator);
			Self::deposit_event(Event::DelegatorLeft(delegator, amount_unstaked));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::cancel_leave_delegators())]
		/// Cancel a pending request to exit the set of delegators. Success clears the pending exit
		/// request (thereby resetting the delay upon another `leave_delegators` call).
		pub fn cancel_leave_delegators(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let delegator = ensure_signed(origin)?;
			// ensure delegator state exists
			let mut state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			// ensure state is leaving
			ensure!(state.is_leaving(), Error::<T>::DelegatorDNE);
			// cancel exit request
			state.cancel_leave();
			<DelegatorState<T>>::insert(&delegator, state);
			Self::deposit_event(Event::DelegatorExitCancelled(delegator));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_revoke_delegation())]
		/// Request to revoke an existing delegation. If successful, the delegation is scheduled
		/// to be allowed to be revoked via the `execute_delegation_request` extrinsic.
		pub fn schedule_revoke_delegation(
			origin: OriginFor<T>,
			collator: T::AccountId,
		) -> DispatchResultWithPostInfo {
			let delegator = ensure_signed(origin)?;
			let mut state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			let (now, when) = state.schedule_revoke::<T>(collator.clone())?;
			<DelegatorState<T>>::insert(&delegator, state);
			Self::deposit_event(Event::DelegationRevocationScheduled(
				now, delegator, collator, when,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_delegator_bond_more())]
		/// Request to bond more for delegators wrt a specific collator candidate.
		pub fn schedule_delegator_bond_more(
			origin: OriginFor<T>,
			candidate: T::AccountId,
			more: Balance,
		) -> DispatchResultWithPostInfo {
			let delegator = ensure_signed(origin)?;
			let mut state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			let when = state.schedule_increase_delegation::<T>(candidate.clone(), more)?;
			<DelegatorState<T>>::insert(&delegator, state);
			Self::deposit_event(Event::DelegationIncreaseScheduled(
				delegator, candidate, more, when,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::schedule_delegator_bond_less())]
		/// Request bond less for delegators wrt a specific collator candidate.
		pub fn schedule_delegator_bond_less(
			origin: OriginFor<T>,
			candidate: T::AccountId,
			less: Balance,
		) -> DispatchResultWithPostInfo {
			let caller = ensure_signed(origin)?;
			let mut state = <DelegatorState<T>>::get(&caller).ok_or(Error::<T>::DelegatorDNE)?;
			let when = state.schedule_decrease_delegation::<T>(candidate.clone(), less)?;
			<DelegatorState<T>>::insert(&caller, state);
			Self::deposit_event(Event::DelegationDecreaseScheduled(
				caller, candidate, less, when,
			));
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::execute_delegator_bond_more())]
		/// Execute pending request to change an existing delegation
		pub fn execute_delegation_request(
			origin: OriginFor<T>,
			delegator: T::AccountId,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?; // we may want to reward caller if caller != delegator
			let mut state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			state.execute_pending_request::<T>(candidate)?;
			Ok(().into())
		}
		#[pallet::weight(<T as Config>::WeightInfo::cancel_delegator_bond_more())]
		/// Cancel request to change an existing delegation.
		pub fn cancel_delegation_request(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			let delegator = ensure_signed(origin)?;
			let mut state = <DelegatorState<T>>::get(&delegator).ok_or(Error::<T>::DelegatorDNE)?;
			let request = state.cancel_pending_request::<T>(candidate)?;
			<DelegatorState<T>>::insert(&delegator, state);
			Self::deposit_event(Event::CancelledDelegationRequest(delegator, request));
			Ok(().into())
		}

		#[pallet::weight(100_000)]
		pub fn add_staking_liquidity_token(
			origin: OriginFor<T>,
			paired_or_liquidity_token: PairedOrLiquidityToken,
			current_liquidity_tokens: u32,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			let added_liquidity_token:TokenId = match paired_or_liquidity_token {
				PairedOrLiquidityToken::Paired(x) => T::StakingLiquidityTokenValuator::get_liquidity_asset(x.into(), T::NativeTokenId::get().into())?,
				PairedOrLiquidityToken::Liquidity(x) => x,
			};

			StakingLiquidityTokens::<T>::try_mutate(|staking_liquidity_tokens| -> DispatchResult {
				ensure!(
					current_liquidity_tokens as usize >= staking_liquidity_tokens.len(),
					Error::<T>::TooLowCurrentStakingLiquidityTokensCount
				);
				ensure!(
					staking_liquidity_tokens.insert(added_liquidity_token, None).is_none(),
					Error::<T>::StakingLiquidityTokenAlreadyListed
				);
				
				Ok(())
			})?;
			Ok(().into())
		}

		#[pallet::weight(100_000)]
		pub fn remove_staking_liquidity_token(
			origin: OriginFor<T>,
			paired_or_liquidity_token: PairedOrLiquidityToken,
			current_liquidity_tokens: u32,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;

			let removed_liquidity_token: TokenId = match paired_or_liquidity_token {
				PairedOrLiquidityToken::Paired(x) => T::StakingLiquidityTokenValuator::get_liquidity_asset(x.into(), T::NativeTokenId::get().into())?,
				PairedOrLiquidityToken::Liquidity(x) => x,
			};

			StakingLiquidityTokens::<T>::try_mutate(|staking_liquidity_tokens| -> DispatchResult {
				ensure!(
					current_liquidity_tokens as usize >= staking_liquidity_tokens.len(),
					Error::<T>::TooLowCurrentStakingLiquidityTokensCount
				);
				ensure!(
					staking_liquidity_tokens.remove(&removed_liquidity_token).is_some(),
					Error::<T>::StakingLiquidityTokenNotListed
				);
				
				Ok(())
			})?;
			Ok(().into())
		}

	}

	impl<T: Config> Pallet<T> {
		pub fn is_delegator(acc: &T::AccountId) -> bool {
			<DelegatorState<T>>::get(acc).is_some()
		}
		pub fn is_candidate(acc: &T::AccountId) -> bool {
			<CandidateState<T>>::get(acc).is_some()
		}
		pub fn is_selected_candidate(acc: &T::AccountId) -> bool {
			<SelectedCandidates<T>>::get().binary_search(acc).is_ok()
		}
		/// Caller must ensure candidate is active before calling
		fn update_active(candidate: T::AccountId, total: Balance, candidate_liquidity_token: TokenId) {
			let mut candidates = <CandidatePool<T>>::get();
			candidates.remove(&Bond::from_owner(candidate.clone()));
			candidates.insert(Bond {
				owner: candidate,
				amount: total,
				liquidity_token: candidate_liquidity_token,
			});
			<CandidatePool<T>>::put(candidates);
		}
		/// Compute round issuance based on total staked for the given round
		fn compute_issuance(staked: Balance) -> Balance {
			let config = <InflationConfig<T>>::get();
			let round_issuance = crate::inflation::round_issuance_range::<T>(config.round);
			// TODO: consider interpolation instead of bounded range
			if staked < config.expect.min {
				round_issuance.min
			} else if staked > config.expect.max {
				round_issuance.max
			} else {
				round_issuance.ideal
			}
		}
		fn delegator_leaves_collator(
			delegator: T::AccountId,
			collator: T::AccountId,
		) -> DispatchResult {
			let mut state = <CandidateState<T>>::get(&collator).ok_or(Error::<T>::CandidateDNE)?;
			let (total_changed, delegator_stake) = state.rm_delegator::<T>(delegator.clone())?;
			T::Currency::unreserve(state.liquidity_token.into(), &delegator, delegator_stake.into());
			if state.is_active() && total_changed {
				Self::update_active(collator.clone(), state.total_counted, state.liquidity_token);
			}
			let new_total_locked = <Total<T>>::get(state.liquidity_token).saturating_sub(delegator_stake);
			<Total<T>>::insert(state.liquidity_token, new_total_locked);
			let new_total = state.total_counted;
			<CandidateState<T>>::insert(&collator, state);
			Self::deposit_event(Event::DelegatorLeftCandidate(
				delegator,
				collator,
				delegator_stake,
				new_total,
			));
			Ok(())
		}

		fn pay_stakers(now: RoundIndex) {
			// payout is now - duration rounds ago => now - duration > 0 else return early
			let duration = T::RewardPaymentDelay::get();
			if now <= duration {
				return;
			}
			let round_to_payout = now - duration;
			let total = <Points<T>>::take(round_to_payout);
			if total.is_zero() {
				return;
			}
			let total_staked = <Staked<T>>::take(round_to_payout);
			let total_issuance = Self::compute_issuance(total_staked);
			let mut left_issuance = total_issuance;
			// reserve portion of issuance for parachain bond account
			let bond_config = <ParachainBondInfo<T>>::get();
			let parachain_bond_reserve = bond_config.percent * total_issuance;
			let imb =
				T::Currency::deposit_creating(T::NativeTokenId::get().into(), &bond_config.account, parachain_bond_reserve.into());
				
			// update round issuance iff transfer succeeds
			left_issuance -= imb.peek().into();
			Self::deposit_event(Event::ReservedForParachainBond(
				bond_config.account,
				imb.peek().into(),
			));
				
			let mint = |amt: Balance, to: T::AccountId| {
				let amount_transferred = T::Currency::deposit_creating(T::NativeTokenId::get().into(), &to, amt.into());
				Self::deposit_event(Event::Rewarded(to.clone(), amount_transferred.peek().into()));
			};
			// only pay out rewards at the end to transfer only total amount due
			let mut due_rewards: BTreeMap<T::AccountId, Balance> = BTreeMap::new();
			let mut increase_due_rewards = |amt: Balance, to: T::AccountId| {
				if let Some(already_due) = due_rewards.get(&to) {
					let amount = amt.saturating_add(*already_due);
					due_rewards.insert(to, amount);
				} else {
					due_rewards.insert(to, amt);
				}
			};
			let collator_fee = <CollatorCommission<T>>::get();
			let collator_issuance = collator_fee * left_issuance;
			for (collator, pts) in <AwardedPts<T>>::drain_prefix(round_to_payout) {
				let pct_due = Perbill::from_rational(pts, total);
				let mut amt_due = pct_due * left_issuance;
				// Take the snapshot of block author and delegations
				let state = <AtStake<T>>::take(round_to_payout, &collator);
				if state.delegations.is_empty() {
					// solo collator with no delegators
					mint(amt_due, collator.clone());
				} else {
					// pay collator first; commission + due_portion
					let collator_pct = Perbill::from_rational(state.bond, state.total);
					let commission = pct_due * collator_issuance;
					amt_due -= commission;
					let collator_reward = (collator_pct * amt_due) + commission;
					mint(collator_reward, collator.clone());
					// pay delegators due portion
					for Bond { owner, amount, .. } in state.delegations {
						let percent = Perbill::from_rational(amount, state.total);
						let due = percent * amt_due;
						increase_due_rewards(due, owner.clone());
						Self::deposit_event(Event::DelegatorDueReward(
							owner.clone(),
							collator.clone(),
							due,
						));
					}
				}
			}

			for (delegator, total_due) in due_rewards {
				mint(total_due, delegator);
			}
		}

		/// Compute the top `TotalSelected` candidates in the CandidatePool and return
		/// a vec of their AccountIds (in the order of selection)
		pub fn compute_top_candidates() -> (Vec<(T::AccountId, Balance)>, Balance) {
			let candidates = <CandidatePool<T>>::get().0;
			let staking_liquidity_tokens = <StakingLiquidityTokens<T>>::get();

			// morph amount in candidates to exposure in mga
			let mut valuated_candidates: Vec<(T::AccountId, Balance)> = candidates.iter().filter_map(|x| 
				if let Some(pool_ratio_option) = staking_liquidity_tokens.get(&x.liquidity_token) {
					if let Some(pool_ratio) = pool_ratio_option{
						if !pool_ratio.1.is_zero(){
							Some((x.owner.clone(), multiply_by_rational(x.amount, pool_ratio.0, pool_ratio.1).unwrap_or_else(|_| Balance::max_value())))
						} else {
							None
						}
					}else{
						None
					}
				} else {
					None
				}
			).collect();
			// order candidates by stake (least to greatest so requires `rev()`)
			valuated_candidates.sort_unstable_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
			// Add all staked valuated mga for Staked storage item
			let total_staked: Balance = valuated_candidates.iter().cloned().fold(Zero::zero(), |acc, x| acc.saturating_add(x.1));
			let top_n = <TotalSelected<T>>::get() as usize;
			// choose the top TotalSelected qualified candidates, ordered by stake
			let mut valuated_collators: Vec<(T::AccountId, Balance)> = valuated_candidates
				.into_iter()
				.rev()
				.take(top_n)
				.filter(|x| x.1 >= T::MinCollatorStk::get())
				.collect::<_>();
			valuated_collators.sort_unstable_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
			(valuated_collators, total_staked)
		}

		pub fn staking_liquidity_tokens_snapshot() {
			let mut staking_liquidity_tokens = <StakingLiquidityTokens<T>>::get();

			for (token, valuation) in staking_liquidity_tokens.iter_mut(){
				*valuation = T::StakingLiquidityTokenValuator::get_pool_state((*token).into());
			}

			<StakingLiquidityTokens<T>>::put(staking_liquidity_tokens);
		}

		/// Best as in most cumulatively supported in terms of stake
		/// Returns [collator_count, delegation_count, total staked]
		fn select_top_candidates(now: RoundIndex) -> (u32, u32, Balance, Balance) {
			let (mut collator_count, mut delegation_count, mut total_relevant_exposure) =
				(0u32, 0u32, Balance::zero());
			Self::staking_liquidity_tokens_snapshot();
			// choose the top TotalSelected qualified candidates, ordered by stake
			let (collators, total_round_exposure) = Self::compute_top_candidates();
			// snapshot exposure for round for weighting reward distribution
			for collator in collators.iter() {
				let state = <CandidateState<T>>::get(&collator.0)
					.expect("all members of CandidateQ must be candidates");
				collator_count += 1u32;
				delegation_count += state.delegators.0.len() as u32;
				let amount = collator.1;
				total_relevant_exposure = total_relevant_exposure.saturating_add(amount);
				let collator_snaphot: CollatorSnapshot<T::AccountId> = state.into();
				<AtStake<T>>::insert(now, collator.0.clone(), collator_snaphot);
				Self::deposit_event(Event::CollatorChosen(now, collator.0.clone(), amount));
			}

			// insert canonical collator set
			<SelectedCandidates<T>>::put(collators.iter().cloned().map(|x| x.0).collect::<Vec<T::AccountId>>());
			(collator_count, delegation_count, total_relevant_exposure, total_round_exposure)
		}
	}

	/// Add reward points to block authors:
	/// * 20 points to the block producer for producing a block in the chain
	impl<T: Config> pallet_authorship::EventHandler<T::AccountId, T::BlockNumber> for Pallet<T> {
		fn note_author(author: T::AccountId) {
			let now = <Round<T>>::get().current;
			let score_plus_20 = <AwardedPts<T>>::get(now, &author).saturating_add(20);
			<AwardedPts<T>>::insert(now, author, score_plus_20);
			<Points<T>>::mutate(now, |x| *x = x.saturating_add(20));
		}

		fn note_uncle(_: T::AccountId, _: T::BlockNumber) {
			// ignore
		}
	}

	impl<T: Config> pallet_session::SessionManager<T::AccountId> for Pallet<T> {
		fn new_session(_: SessionIndex) -> Option<Vec<T::AccountId>> {
			Some(Self::selected_candidates())
		}
		fn start_session(_: SessionIndex) {
			let n = <frame_system::Pallet<T>>::block_number().saturating_add(One::one());
			let mut round = <Round<T>>::get();
			// mutate round
			round.update(n);
			// pay all stakers for T::RewardPaymentDelay rounds ago
			Self::pay_stakers(round.current);
			// select top collator candidates for next round
			let (collator_count, _delegation_count, total_relevant_exposure, total_round_exposure) =
				Self::select_top_candidates(round.current.saturating_add(One::one()));
			// start next round
			<Round<T>>::put(round);
			// snapshot total stake
			<Staked<T>>::insert(round.current.saturating_add(One::one()), total_round_exposure);
			// <RelevantStaked<T>>::insert(round.current + One::one(), total_relevant_exposure);
			Self::deposit_event(Event::NewRound(
				round.first,
				round.current,
				collator_count,
				total_relevant_exposure,
			));
		}
		fn end_session(_: SessionIndex) {
			// ignore
		}
	}

	impl<T: Config> pallet_session::ShouldEndSession<T::BlockNumber> for Pallet<T> {
		fn should_end_session(now: T::BlockNumber) -> bool {
			let round = <Round<T>>::get();
			round.should_update(now)
		}
	}

	impl<T: Config> EstimateNextSessionRotation<T::BlockNumber> for Pallet<T> {
		fn average_session_length() -> T::BlockNumber {
			<Round<T>>::get().length.into()
		}

		fn estimate_current_session_progress(now: T::BlockNumber) -> (Option<Permill>, Weight) {
			let round = <Round<T>>::get();
			let passed_blocks = now.saturating_sub(round.first).saturating_add(One::one());

			(
				Some(Permill::from_rational(passed_blocks, round.length.into())),
				// One read for the round info, blocknumber is read free
				T::DbWeight::get().reads(1),
			)
		}

		fn estimate_next_session_rotation(_now: T::BlockNumber) -> (Option<T::BlockNumber>, Weight) {
			let round = <Round<T>>::get();

			(
				Some(round.first + round.length.saturating_sub(One::one()).into()),
				// One read for the round info, blocknumber is read free
				T::DbWeight::get().reads(1),
			)
		}
	}

}
