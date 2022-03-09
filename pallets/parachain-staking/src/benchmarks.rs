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

// set_staking_expectations
// will be removed
// simple, no scaling

// set_inflation
// will be removed
// simple, no scaling

// set_parachain_bond_account
// will be removed
// simple, no scaling

// set_parachain_bond_reserve_percent
// will be removed
// simple, no scaling


// set_total_selected
// simple, no scaling

// set_collator_commission
// simple, no scaling

// set_blocks_per_round
// will be removed
// simple, no scaling

// join_candidates
// scales with candidate count due to ordered set insertion
// scales with liquidity_token due to contain_key check

// schedule_leave_candidates
// scales with candidate count due to ordered set removal
// liquidity_token does not affect scaling

// execute_leave_candidates
// scales with candidate delegator count due to delegator unbonds
// scales with the number of delegations of the delegators that have delegated to the collator
// ^ But this a parameter can be avoided (not that we can even effectively provide this as a parameter) by considering the MaxDelegationsPerDelegator bound, and filling all delegators to the collator (in question) to MaxDelegationsPerDelegator number of delegations
// liquidity_token does not affect scaling

// cancel_leave_candidates
// scales with candidate count due to ordered set insertion
// liquidity_token does not affect scaling

// go_offline
// scales with candidate count due to ordered set removal
// liquidity_token does not affect scaling

// go_online
// scales with candidate count due to ordered set insertion
// liquidity_token does not affect scaling

// schedule_candidate_bond_more
// does not scale

// schedule_candidate_bond_less
// does not scale

// execute_candidate_bond_request
// scales with candidate count due to ordered set change upon update_active
// liquidity_token does not affect scaling

// cancel_candidate_bond_request
// does not scale

// add_staking_liquidity_token
// potentially scales with liquidity_token_count

// remove_staking_liquidity_token
// potentially scales with liquidity_token_count

// delegate
// To keep it simple just use candidate_delegation_count = max delegation bound + i
// Will have to adjust the weighing function appropriately
// Worst Case Complexity is insertion into a full collator causing removal from top and add to bottom of existing delegation in collator
// ^ Can we use max delegation bounds for these? No max delegation bounds applies only to top_delegations
// candidate_delegation_count due to insert into candidate ordered bond list
// delegator delegation_count due to insert into delegator ordered bond list
// also depends on candidate_count due to update_active

// schedule_leave_delegators
// does not scale

// execute_leave_delegators
// To keep it simple just use candidate_delegation_count = max delegation bound + i
// Will have to adjust the weighing function appropriately
// Worst case when all collators have full top_delegations and a delegation from top_delegation has been removed
// ^ Can we use max delegation bounds for these? No max delegation bounds applies only to top_delegations
// scales with delegator delegations count
// scales with candidate count due to update_active
// scales with collator delegation count due to remove in rm_delegator and delegator suffle

// cancel_leave_delegators
// does not scale

// schedule_revoke_delegation
// Since the requests are a btreemap keyed with candidate_id, this extrinsic scales with number of candidates, as the worst case for request btree
// However this can also be parameterized better by using the delegators current pending request count. 

// schedule_delegator_bond_more
// Since the requests are a btreemap keyed with candidate_id, this extrinsic scales with number of candidates, as the worst case for request btree
// However this can also be parameterized better by using the delegators current pending request count. 

// schedule_delegator_bond_less
// Since the requests are a btreemap keyed with candidate_id, this extrinsic scales with number of candidates, as the worst case for request btree
// However this can also be parameterized better by using the delegators current pending request count. 

// cancel_delegation_request
// Since the requests are a btreemap keyed with candidate_id, this extrinsic scales with number of candidates, as the worst case for request btree
// However this can also be parameterized better by using the delegators current pending request count. 

// execute_delegation_request
// To keep it simple just use candidate_delegation_count = max delegation bound + i
// Will have to adjust the weighing function appropriately
// ALL SCALE WITH the delegators current pending request count.
// revoke :=
// scales with delegator delegation count to remove from delegations
// scales with candidates_delegation_count due to removal from delegators and shuffling delegators
// scales with candidate count due to update_active
// increase:=
// scales with delegator delegation count to iterate through them
// scales with candidates_delegation_count due to removal from delegators and shuffling delegators
// scales with candidate count due to update_active
// decrease:=
// scales with delegator delegation count to iterate through them
// scales with candidates_delegation_count due to removal from delegators and shuffling delegators
// scales with candidate count due to update_active

// new_session
// is just one db read

// start_session
// TotalSelected - loops through each collator for pay_stakers 
// MaxDelegatorsPerCandidate - loops through each delegator of the candidate to increase reward.
// Worst case when each delegator involved in pay_Stakers is separate.
// Liquidity_tokens_count - for valuating each token
// candidate_count - compute_candidates processes the entire set of candidates


#![cfg(feature = "runtime-benchmarks")]

//! Benchmarking
// use crate::{
// 	BalanceOf, Call, CandidateBondChange, CandidateBondRequest, Config, DelegationChange,
// 	DelegationRequest, Pallet, Range,
// };
use crate::{*};
use frame_benchmarking::{account, benchmarks, impl_benchmark_test_suite};
use frame_support::assert_ok;
use frame_support::traits::{Currency, Get, OnFinalize, OnInitialize, ReservableCurrency, ExistenceRequirement};
use frame_system::RawOrigin;
use sp_runtime::{Perbill, Percent};
use sp_std::{collections::btree_map::BTreeMap, vec::Vec};
use orml_tokens::MultiTokenCurrencyExtended;
use orml_tokens::Pallet as Tokens;
use pallet_authorship::EventHandler;

/// Minimum collator candidate stake
fn min_candidate_stk<T: Config>() -> Balance {
	<<T as Config>::MinCollatorStk as Get<Balance>>::get()
}

/// Minimum delegator stake
fn min_delegator_stk<T: Config>() -> Balance {
	<<T as Config>::MinDelegation as Get<Balance>>::get()
}


const DOLLAR: Balance = 1__000_000_000_000_000_000u128;
const MGA_TOKEN_ID: TokenId = 0u32;

/// We assume
/// Mga token is token id 0
/// Not more than 100 curated tokens
/// Not more than 1000 candidates

/// To maintain simplicity, creating a pool and using resulting liqudity tokens to stake have been separated
/// To do this we mint tokens and create pools using one user, the funding account
/// And then distribute the liquidity tokens to various users
/// For each liquidity token, two additional tokens must be created
/// (Token n, Token n+1) <=> Token n+2
/// Starting from n0=5 as the first 4 are taken by the genesis config, but the starting n0 will be determined at the start of each bench by checking tokens
/// Any set of tokens x, x0=0, will have token_id, (3x+5, 3x+6) <=> 3x+7 
/// Since we are creating new tokens every time we can simply just use (v, v+1) as the pooled token amounts, to mint v liquidity tokens


/// Mint v liquidity tokens of token set x to funding account
fn create_non_staking_liquidity_for_funding<T: Config + orml_tokens::Config + pallet_xyk::Config>(
	v: Option<Balance>,
) -> Result<TokenId, DispatchError> {
	let funding_account: T::AccountId = account("funding", 0u32, 0u32);
	let x: TokenId = 
		<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::get_next_currency_id().into();
	let v = v.unwrap_or(1_000_000 * DOLLAR);
	<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::create(&funding_account, v.into())?;
	<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::create(&funding_account, (v + 1u128).into())?;

	assert_ok!(<pallet_xyk::Pallet<T>>::create_pool(RawOrigin::Signed(funding_account.clone()).into(), x.into(), v.into(), (x + 1u32).into(), (v + 1).into()));

	assert_eq!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::total_balance((x + 2u32).into(), &funding_account), v.into());
	Ok(x+2u32)
}

/// Mint v liquidity tokens of token set x to funding account
fn create_staking_liquidity_for_funding<T: Config + orml_tokens::Config + pallet_xyk::Config>(
	v: Option<Balance>,
) -> Result<TokenId, DispatchError> {
	let funding_account: T::AccountId = account("funding", 0u32, 0u32);
	let x: TokenId = 
		<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::get_next_currency_id().into();
	let v = v.unwrap_or(1_000_000 * DOLLAR);
	<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::mint(MGA_TOKEN_ID.into(), &funding_account, v.into())?;
	<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::create(&funding_account, (v + 1u128).into())?;

	assert_ok!(<pallet_xyk::Pallet<T>>::create_pool(RawOrigin::Signed(funding_account.clone()).into(), MGA_TOKEN_ID.into(), v.into(), (x).into(), (v + 1).into()));

	assert_eq!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::total_balance((x + 1u32).into(), &funding_account), v.into());
	Ok(x+1u32)
}

/// Create a funded user.
/// Extra + min_candidate_stk is total minted funds
/// Returns tuple (id, balance)
fn create_funded_user<T: Config + orml_tokens::Config>(
	string: &'static str,
	n: u32,
	token_id: TokenId,
	v: Option<Balance>,
) -> (T::AccountId, TokenId, Balance) {
	let funding_account: T::AccountId = account("funding", 0u32, 0u32);
	const SEED: u32 = 0;
	let user = account(string, n, SEED);
	let v = v.unwrap_or(100 * DOLLAR);
	assert_ok!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::transfer((token_id).into(), &funding_account, &user, v.into(), ExistenceRequirement::AllowDeath));
	(user, token_id, v)
}

/// Create a funded delegator.
fn create_funded_delegator<T: Config>(
	string: &'static str,
	n: u32,
	collator: T::AccountId,
	collator_token_id: TokenId,
	v: Option<Balance>,
	collator_delegator_count: u32,
) -> Result<T::AccountId, &'static str> {
	let (user, token_id, v) = create_funded_user::<T>(string, n, collator_token_id, v);
	Pallet::<T>::delegate(
		RawOrigin::Signed(user.clone()).into(),
		collator,
		v,
		collator_delegator_count,
		0u32, // first delegation for all calls
	)?;
	Ok(user)
}

/// Create a funded collator.
fn create_funded_collator<T: Config + orml_tokens::Config>(
	string: &'static str,
	n: u32,
	token_id: TokenId,
	v: Option<Balance>,
	candidate_count: u32,
	liquidity_token_count: u32,
) -> Result<T::AccountId, &'static str> {
	let (user, token_id, v) = create_funded_user::<T>(string, n, token_id, v);
	Pallet::<T>::join_candidates(
		RawOrigin::Signed(user.clone()).into(),
		v,
		token_id,
		candidate_count,
		liquidity_token_count,
	)?;
	Ok(user)
}

pub(crate) fn roll_to_round_and_author<T: Config + pallet_session::Config>(n: u32, author: T::AccountId) {
	let current_round: u32 = Pallet::<T>::round().current;
	// log::info!("n: {:?}", n);
	// log::info!("current_round: {:?}", current_round);
	// log::info!("<frame_system::Pallet<T>>::block_number(): {:?}", <frame_system::Pallet<T>>::block_number());

	while !(Pallet::<T>::round().current >= n + current_round as u32 + 1u32) {
		// log::info!("Pallet::<T>::round().current: {:?}", Pallet::<T>::round().current);
		// log::info!("At A");
		<pallet::Pallet<T> as frame_support::traits::Hooks<_>>::on_finalize(<frame_system::Pallet<T>>::block_number());
		// log::info!("At B");
		<frame_system::Pallet<T> as frame_support::traits::Hooks<_>>::on_finalize(<frame_system::Pallet<T>>::block_number());
		// log::info!("At C");
		<frame_system::Pallet<T>>::set_block_number(<frame_system::Pallet<T>>::block_number() + 1u32.into());
		// log::info!("At D");
		<frame_system::Pallet<T> as frame_support::traits::Hooks<_>>::on_initialize(<frame_system::Pallet<T>>::block_number());
		// log::info!("At E");
		Pallet::<T>::note_author(author.clone());
		// log::info!("At F");
		<pallet::Pallet<T> as frame_support::traits::Hooks<_>>::on_initialize(<frame_system::Pallet<T>>::block_number());
		// log::info!("At G");
		// log::info!("<frame_system::Pallet<T>>::block_number(): {:?}", <frame_system::Pallet<T>>::block_number());
		if <Pallet::<T> as pallet_session::ShouldEndSession<_>>::should_end_session(<frame_system::Pallet<T>>::block_number()){
			// log::info!("Starting session");
			// log::info!("pallet_session::Pallet::<T>::current_index(): {:?}", pallet_session::Pallet::<T>::current_index());
			<Pallet::<T> as pallet_session::SessionManager<_>>::start_session(pallet_session::Pallet::<T>::current_index() as u32 + 1u32);
		}
	}

	// Assumes round is atleast 3 blocks
	// Roll to 2 blocks into the given round
	for i in 0..2{
		<pallet::Pallet<T> as frame_support::traits::Hooks<_>>::on_finalize(<frame_system::Pallet<T>>::block_number());
		<frame_system::Pallet<T> as frame_support::traits::Hooks<_>>::on_finalize(<frame_system::Pallet<T>>::block_number());
		<frame_system::Pallet<T>>::set_block_number(<frame_system::Pallet<T>>::block_number() + 1u32.into());
		<frame_system::Pallet<T> as frame_support::traits::Hooks<_>>::on_initialize(<frame_system::Pallet<T>>::block_number());
		Pallet::<T>::note_author(author.clone());
		<pallet::Pallet<T> as frame_support::traits::Hooks<_>>::on_initialize(<frame_system::Pallet<T>>::block_number());
	}

}

const USER_SEED: u32 = 999666;
const DUMMY_COUNT: u32 = 999666;

benchmarks! {
	// MONETARY ORIGIN DISPATCHABLES

	set_staking_expectations {
		let stake_range: Range<Balance> = Range {
			min: 100u32.into(),
			ideal: 200u32.into(),
			max: 300u32.into(),
		};
	}: _(RawOrigin::Root, stake_range)
	verify {
		assert_eq!(Pallet::<T>::inflation_config().expect, stake_range);
	}

	set_inflation {
		let inflation_range: Range<Perbill> = Range {
			min: Perbill::from_perthousand(1),
			ideal: Perbill::from_perthousand(2),
			max: Perbill::from_perthousand(3),
		};

	}: _(RawOrigin::Root, inflation_range)
	verify {
		assert_eq!(Pallet::<T>::inflation_config().annual, inflation_range);
	}

	set_parachain_bond_account {
		let parachain_bond_account: T::AccountId = account("TEST", 0u32, USER_SEED);
	}: _(RawOrigin::Root, parachain_bond_account.clone())
	verify {
		assert_eq!(Pallet::<T>::parachain_bond_info().account, parachain_bond_account);
	}

	set_parachain_bond_reserve_percent {
	}: _(RawOrigin::Root, Percent::from_percent(33))
	verify {
		assert_eq!(Pallet::<T>::parachain_bond_info().percent, Percent::from_percent(33));
	}

	// ROOT DISPATCHABLES

	set_total_selected {}: _(RawOrigin::Root, 100u32)
	verify {
		assert_eq!(Pallet::<T>::total_selected(), 100u32);
	}

	set_collator_commission {}: _(RawOrigin::Root, Perbill::from_percent(33))
	verify {
		assert_eq!(Pallet::<T>::collator_commission(), Perbill::from_percent(33));
	}

	set_blocks_per_round {}: _(RawOrigin::Root, 1800u32)
	verify {
		assert_eq!(Pallet::<T>::round().length, 1800u32);
	}

	// USER DISPATCHABLES

	join_candidates {
		let x in 3..1_000;
		let y in 3..100;
		

		let token_0: TokenId = Tokens::<T>::next_asset_id().into();

		// let token_0: TokenId = <orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrencyExtended<T::AccountId>>::get_next_currency_id().into();

		// Worst Case Complexity is search into a list so \exists full list before call
		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();
		assert!(y > liquidity_token_count);
		for i in liquidity_token_count..(y - 1u32){
			assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(DUMMY_COUNT - i), i));
		}

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), y - 1));


		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();
		assert!(x >= candidate_count);

		// Worst Case Complexity is insertion into an ordered list so \exists full list before call

		for i in candidate_count..x {
			let seed = USER_SEED - i;
			let collator = create_funded_collator::<T>(
				"collator",
				seed,
				created_liquidity_token,
				None,
				i,
				y
			)?;
		}
		let (caller, _, _) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
	}: _(RawOrigin::Signed(caller.clone()), 100*DOLLAR, created_liquidity_token , x, y)
	verify {
		assert!(Pallet::<T>::is_candidate(&caller));
	}

	// This call schedules the collator's exit and removes them from the candidate pool
	// -> it retains the self-bond and delegator bonds
	schedule_leave_candidates {
		let x in 3..1_000;

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();
		assert!(x >= candidate_count);

		// Worst Case Complexity is insertion into an ordered list so \exists full list before call

		for i in candidate_count..(x - 1u32) {
			let seed = USER_SEED - i;
			let collator = create_funded_collator::<T>(
				"collator",
				seed,
				created_liquidity_token,
				None,
				i,
				liquidity_token_count
			)?;
		}
		let caller = create_funded_collator::<T>("caller", USER_SEED, created_liquidity_token, None, x - 1u32, liquidity_token_count)?;

	}: _(RawOrigin::Signed(caller.clone()), x)
	verify {
		assert!(Pallet::<T>::candidate_state(&caller).unwrap().is_leaving());
	}

	execute_leave_candidates {
		// x is total number of delegations for the candidate
		let x in 2..(<<T as Config>::MaxDelegatorsPerCandidate as Get<u32>>::get()
		* 2);

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let candidate: T::AccountId = create_funded_collator::<T>(
			"unique_caller",
			USER_SEED - 100,
			created_liquidity_token,
			None,
			candidate_count + 1u32,
			liquidity_token_count,
		)?;
		// 2nd delegation required for all delegators to ensure DelegatorState updated not removed
		let second_candidate: T::AccountId = create_funded_collator::<T>(
			"unique__caller",
			USER_SEED - 99,
			created_liquidity_token,
			None,
			candidate_count + 2u32,
			liquidity_token_count,
		)?;

		let mut delegators: Vec<T::AccountId> = Vec::new();
		let mut col_del_count = 0u32;
		for i in 1..x {
			let seed = USER_SEED + i;
			let delegator = create_funded_delegator::<T>(
				"delegator",
				seed,
				candidate.clone(),
				created_liquidity_token,
				None,
				col_del_count,
			)?;
			assert_ok!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::transfer((created_liquidity_token).into(), &account("funding", 0u32, 0u32), &delegator, min_delegator_stk::<T>().into(), ExistenceRequirement::AllowDeath));
			Pallet::<T>::delegate(
				RawOrigin::Signed(delegator.clone()).into(),
				second_candidate.clone(),
				min_delegator_stk::<T>(),
				col_del_count,
				1u32,
			)?;
			Pallet::<T>::schedule_revoke_delegation(
				RawOrigin::Signed(delegator.clone()).into(),
				candidate.clone()
			)?;
			delegators.push(delegator);
			col_del_count += 1u32;
		}
		Pallet::<T>::schedule_leave_candidates(
			RawOrigin::Signed(candidate.clone()).into(),
			candidate_count + 3u32
		)?;
		roll_to_round_and_author::<T>(2, candidate.clone());
	}: _(RawOrigin::Signed(candidate.clone()), candidate.clone(), col_del_count)
	verify {
		assert!(Pallet::<T>::candidate_state(&candidate).is_none());
		assert!(Pallet::<T>::candidate_state(&second_candidate).is_some());
		for delegator in delegators {
			assert!(Pallet::<T>::is_delegator(&delegator));
		}
	}

	cancel_leave_candidates {
		let x in 3..1_000;
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		// Worst Case Complexity is removal from an ordered list so \exists full list before call
		let mut candidate_count = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();
		for i in 2..x {
			let seed = USER_SEED - i;
			let collator = create_funded_collator::<T>(
				"collator",
				seed,
				created_liquidity_token,
				None,
				candidate_count,
				liquidity_token_count,
			)?;
			candidate_count += 1u32;
		}
		let caller: T::AccountId = create_funded_collator::<T>(
			"caller",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		candidate_count += 1u32;
		Pallet::<T>::schedule_leave_candidates(
			RawOrigin::Signed(caller.clone()).into(),
			candidate_count
		)?;
		candidate_count -= 1u32;
	}: _(RawOrigin::Signed(caller.clone()), candidate_count)
	verify {
		assert!(Pallet::<T>::candidate_state(&caller).unwrap().is_active());
	}

	go_offline {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;
		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert!(!Pallet::<T>::candidate_state(&caller).unwrap().is_active());
	}

	go_online {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		Pallet::<T>::go_offline(RawOrigin::Signed(caller.clone()).into())?;
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert!(Pallet::<T>::candidate_state(&caller).unwrap().is_active());
	}

	schedule_candidate_bond_more {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();
	
		let more = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		assert_ok!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::transfer((created_liquidity_token).into(), &account("funding", 0u32, 0u32), &caller, more.into(), ExistenceRequirement::AllowDeath));
		
	}: _(RawOrigin::Signed(caller.clone()), more)
	verify {
		let state = Pallet::<T>::candidate_state(&caller).expect("request bonded more so exists");
		assert_eq!(
			state.request,
			Some(CandidateBondRequest {
				amount: more,
				change: CandidateBondChange::Increase,
				when_executable: 2,
			})
		);
	}

	schedule_candidate_bond_less {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let less = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
	}: _(RawOrigin::Signed(caller.clone()), less)
	verify {
		let state = Pallet::<T>::candidate_state(&caller).expect("request bonded less so exists");
		assert_eq!(
			state.request,
			Some(CandidateBondRequest {
				amount: less,
				change: CandidateBondChange::Decrease,
				when_executable: 2,
			})
		);
	}

	execute_candidate_bond_more {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let more = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		assert_ok!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::transfer((created_liquidity_token).into(), &account("funding", 0u32, 0u32), &caller, more.into(), ExistenceRequirement::AllowDeath));
		
		Pallet::<T>::schedule_candidate_bond_more(
			RawOrigin::Signed(caller.clone()).into(),
			more
		)?;
		roll_to_round_and_author::<T>(2, caller.clone());
	}: {
		Pallet::<T>::execute_candidate_bond_request(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone()
		)?;
	} verify {
		let expected_bond = 110*DOLLAR;
		assert_eq!(<T as pallet::Config>::Currency::reserved_balance(created_liquidity_token.into(), &caller).into(), expected_bond);
	}

	execute_candidate_bond_less {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;
		
		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let less = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		Pallet::<T>::schedule_candidate_bond_less(
			RawOrigin::Signed(caller.clone()).into(),
			less
		)?;
		roll_to_round_and_author::<T>(2, caller.clone());
	}: {
		Pallet::<T>::execute_candidate_bond_request(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone()
		)?;
	} verify {
		assert_eq!(<T as pallet::Config>::Currency::reserved_balance(created_liquidity_token.into(), &caller).into(), 90*DOLLAR);
	}

	cancel_candidate_bond_more {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;
		
		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let more = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		assert_ok!(<orml_tokens::MultiTokenCurrencyAdapter<T> as MultiTokenCurrency<T::AccountId>>::transfer((created_liquidity_token).into(), &account("funding", 0u32, 0u32), &caller, more.into(), ExistenceRequirement::AllowDeath));
		
		Pallet::<T>::schedule_candidate_bond_more(
			RawOrigin::Signed(caller.clone()).into(),
			more
		)?;
	}: {
		Pallet::<T>::cancel_candidate_bond_request(
			RawOrigin::Signed(caller.clone()).into(),
		)?;
	} verify {
		assert!(
			Pallet::<T>::candidate_state(&caller).unwrap().request.is_none()
		);
	}

	cancel_candidate_bond_less {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;
		
		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let less = 10*DOLLAR;
		let caller: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		Pallet::<T>::schedule_candidate_bond_less(
			RawOrigin::Signed(caller.clone()).into(),
			less
		)?;
	}: {
		Pallet::<T>::cancel_candidate_bond_request(
			RawOrigin::Signed(caller.clone()).into(),
		)?;
	} verify {
		assert!(
			Pallet::<T>::candidate_state(&caller).unwrap().request.is_none()
		);
	}

	delegate {
		let x in 3..<<T as Config>::MaxDelegationsPerDelegator as Get<u32>>::get();
		let y in 2..<<T as Config>::MaxDelegatorsPerCandidate as Get<u32>>::get();

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		// Worst Case is full of delegations before calling `delegate`
		let mut collators: Vec<T::AccountId> = Vec::new();
		// Initialize MaxDelegationsPerDelegator collator candidates
		for i in 2..x {
			let seed = USER_SEED - i;
			let collator = create_funded_collator::<T>(
				"collator",
				seed,
				created_liquidity_token,
				None,
				collators.len() as u32 + candidate_count,
				liquidity_token_count,
			)?;
			collators.push(collator.clone());
		}

		let (caller, _, _) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, Some(100 * DOLLAR * (collators.len() as u128 + 1u128) + 1u128));
		// Delegation count
		let mut del_del_count = 0u32;
		// Nominate MaxDelegationsPerDelegators collator candidates
		for col in collators.clone() {
			Pallet::<T>::delegate(
				RawOrigin::Signed(caller.clone()).into(), col, 100 * DOLLAR, 0u32, del_del_count
			)?;
			del_del_count += 1u32;
		}
		// Last collator to be delegated
		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			collators.len() as u32 + candidate_count,
			liquidity_token_count,
		)?;
		// Worst Case Complexity is insertion into an almost full collator
		let mut col_del_count = 0u32;
		for i in 1..y {
			let seed = USER_SEED + i;
			let _ = create_funded_delegator::<T>(
				"delegator",
				seed,
				collator.clone(),
				created_liquidity_token,
				None,
				col_del_count,
			)?;
			col_del_count += 1u32;
		}
	}: _(RawOrigin::Signed(caller.clone()), collator, 100*DOLLAR + 1u128, col_del_count, del_del_count)
	verify {
		assert!(Pallet::<T>::is_delegator(&caller));
	}

	schedule_leave_delegators {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, _) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			100*DOLLAR,
			0u32,
			0u32
		)?;
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert!(Pallet::<T>::delegator_state(&caller).unwrap().is_leaving());
	}

	execute_leave_delegators {
		let x in 2..<<T as Config>::MaxDelegationsPerDelegator as Get<u32>>::get();
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		// Worst Case is full of delegations before execute exit
		let mut collators: Vec<T::AccountId> = Vec::new();
		// Initialize MaxDelegationsPerDelegator collator candidates
		for i in 1..x {
			let seed = USER_SEED - i;
			let collator = create_funded_collator::<T>(
				"collator",
				seed,
				created_liquidity_token,
				None,
				collators.len() as u32 + candidate_count,
				liquidity_token_count
			)?;
			collators.push(collator.clone());
		}
		// Fund the delegator
		let (caller, _, _) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, Some(100 * DOLLAR * (collators.len() as u128)));
		// Delegation count
		let mut delegation_count = 0u32;
		let author = collators[0].clone();
		// Nominate MaxDelegationsPerDelegators collator candidates
		for col in collators {
			Pallet::<T>::delegate(
				RawOrigin::Signed(caller.clone()).into(),
				col,
				100*DOLLAR,
				0u32,
				delegation_count
			)?;
			delegation_count += 1u32;
		}
		Pallet::<T>::schedule_leave_delegators(RawOrigin::Signed(caller.clone()).into())?;
		roll_to_round_and_author::<T>(2, author);
	}: _(RawOrigin::Signed(caller.clone()), caller.clone(), delegation_count)
	verify {
		assert!(Pallet::<T>::delegator_state(&caller).is_none());
	}

	cancel_leave_delegators {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
		Pallet::<T>::schedule_leave_delegators(RawOrigin::Signed(caller.clone()).into())?;
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert!(Pallet::<T>::delegator_state(&caller).unwrap().is_active());
	}

	schedule_revoke_delegation {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
	}: _(RawOrigin::Signed(caller.clone()), collator.clone())
	verify {
		assert_eq!(
			Pallet::<T>::delegator_state(&caller).unwrap().requests().get(&collator),
			Some(&DelegationRequest {
				collator,
				amount: v,
				when_executable: 2,
				action: DelegationChange::Revoke
			})
		);
	}

	schedule_delegator_bond_more {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			v - 10*DOLLAR,
			0u32,
			0u32
		)?;
	}: _(RawOrigin::Signed(caller.clone()), collator.clone(), 10*DOLLAR)
	verify {
		let state = Pallet::<T>::delegator_state(&caller)
			.expect("just request bonded less so exists");
		assert_eq!(
			state.requests().get(&collator),
			Some(&DelegationRequest {
				collator,
				amount: 10*DOLLAR,
				when_executable: 2,
				action: DelegationChange::Increase
			})
		);
	}

	schedule_delegator_bond_less {

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
	}: _(RawOrigin::Signed(caller.clone()), collator.clone(), 10*DOLLAR)
	verify {
		let state = Pallet::<T>::delegator_state(&caller)
			.expect("just request bonded less so exists");
		assert_eq!(
			state.requests().get(&collator),
			Some(&DelegationRequest {
				collator,
				amount: 10*DOLLAR,
				when_executable: 2,
				action: DelegationChange::Decrease
			})
		);
	}

	execute_revoke_delegation {

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
		Pallet::<T>::schedule_revoke_delegation(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone()
		)?;
		roll_to_round_and_author::<T>(2, collator.clone());
	}: {
		Pallet::<T>::execute_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone(),
			collator.clone()
		)?;
	} verify {
		assert!(
			!Pallet::<T>::is_delegator(&caller)
		);
	}

	execute_delegator_bond_more {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		
		Pallet::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			v - 10*DOLLAR,
			0u32,
			0u32
		)?;
		Pallet::<T>::schedule_delegator_bond_more(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			10*DOLLAR
		)?;
		roll_to_round_and_author::<T>(2, collator.clone());
	}: {
		Pallet::<T>::execute_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone(),
			collator.clone()
		)?;
	} verify {
		let expected_bond = 100*DOLLAR;
		assert_eq!(<T as pallet::Config>::Currency::reserved_balance(created_liquidity_token.into(), &caller).into(), expected_bond);
	}

	execute_delegator_bond_less {

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
		let bond_less = 10*DOLLAR;
		Pallet::<T>::schedule_delegator_bond_less(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			bond_less
		)?;
		roll_to_round_and_author::<T>(2, collator.clone());
	}: {
		Pallet::<T>::execute_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone(),
			collator.clone()
		)?;
	} verify {
		let expected = v - bond_less;
		assert_eq!(<T as pallet::Config>::Currency::reserved_balance(created_liquidity_token.into(), &caller).into(), expected);
	}

	cancel_revoke_delegation {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			v,
			0u32,
			0u32
		)?;
		Pallet::<T>::schedule_revoke_delegation(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone()
		)?;
	}: {
		Pallet::<T>::cancel_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone()
		)?;
	} verify {
		assert!(
			Pallet::<T>::delegator_state(&caller).unwrap().requests().get(&collator).is_none()
		);
	}

	cancel_delegator_bond_more {

		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, v) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		
		Pallet::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			v - 10*DOLLAR,
			0u32,
			0u32
		)?;
		Pallet::<T>::schedule_delegator_bond_more(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			10*DOLLAR
		)?;
		roll_to_round_and_author::<T>(2, collator.clone());
	}: {
		Pallet::<T>::cancel_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone()
		)?;
	} verify {
		assert!(
			Pallet::<T>::delegator_state(&caller)
				.unwrap()
				.requests()
				.get(&collator)
				.is_none()
		);
	}

	cancel_delegator_bond_less {
		let created_liquidity_token =
			create_non_staking_liquidity_for_funding::<T>(None);

		assert_ok!(created_liquidity_token);

		let created_liquidity_token =
			created_liquidity_token.unwrap();

		let mut liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(created_liquidity_token), liquidity_token_count));

		liquidity_token_count = liquidity_token_count + 1u32;

		let mut candidate_count: u32 = Pallet::<T>::candidate_pool().0.len().try_into().unwrap();

		let collator: T::AccountId = create_funded_collator::<T>(
			"collator",
			USER_SEED,
			created_liquidity_token,
			None,
			candidate_count,
			liquidity_token_count,
		)?;
		let (caller, _, total) = create_funded_user::<T>("caller", USER_SEED, created_liquidity_token, None);
		Pallet::<T>::delegate(RawOrigin::Signed(
			caller.clone()).into(),
			collator.clone(),
			total - 10*DOLLAR,
			0u32,
			0u32
		)?;
		let bond_less = 10*DOLLAR;
		Pallet::<T>::schedule_delegator_bond_less(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone(),
			bond_less
		)?;
		roll_to_round_and_author::<T>(2, collator.clone());
	}: {
		Pallet::<T>::cancel_delegation_request(
			RawOrigin::Signed(caller.clone()).into(),
			collator.clone()
		)?;
	} verify {
		assert!(
			Pallet::<T>::delegator_state(&caller)
				.unwrap()
				.requests()
				.get(&collator)
				.is_none()
		);
	}

	add_staking_liquidity_token {
		let x in 3..100;

		let liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();
		assert!(x > liquidity_token_count);
		for i in liquidity_token_count..(x){
			assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(DUMMY_COUNT - i), i));
		}
		
	}: _(RawOrigin::Root, PairedOrLiquidityToken::Liquidity(DUMMY_COUNT + 1u32), x)
	verify {
		assert!(
			Pallet::<T>::staking_liquidity_tokens()
				.contains_key(&(DUMMY_COUNT + 1u32))
		);
	}

	remove_staking_liquidity_token {
		let x in 3..100;

		let liquidity_token_count: u32 = Pallet::<T>::staking_liquidity_tokens().len().try_into().unwrap();
		assert!(x > liquidity_token_count);
		for i in liquidity_token_count..(x - 1u32){
			assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(DUMMY_COUNT - i), i));
		}

		assert_ok!(Pallet::<T>::add_staking_liquidity_token(RawOrigin::Root.into(), PairedOrLiquidityToken::Liquidity(DUMMY_COUNT + 1u32), x - 1u32));
		
	}: _(RawOrigin::Root, PairedOrLiquidityToken::Liquidity(DUMMY_COUNT + 1u32), x)
	verify {
		assert!(
			!Pallet::<T>::staking_liquidity_tokens()
				.contains_key(&(DUMMY_COUNT + 1u32))
		);
	}


	// // ON_INITIALIZE

	// active_on_initialize {
	// 	// TOTAL SELECTED COLLATORS PER ROUND
	// 	let x in 1..28;
	// 	// DELEGATIONS
	// 	let y in 0..(<<T as Config>::MaxDelegatorsPerCandidate as Get<u32>>::get() * 28);
	// 	let max_delegators_per_collator =
	// 		<<T as Config>::MaxDelegatorsPerCandidate as Get<u32>>::get();
	// 	let max_delegations = x * max_delegators_per_collator;
	// 	// y should depend on x but cannot directly, we overwrite y here if necessary to bound it
	// 	let total_delegations: u32 = if max_delegations < y { max_delegations } else { y };
	// 	// INITIALIZE RUNTIME STATE
	// 	let high_inflation: Range<Perbill> = Range {
	// 		min: Perbill::one(),
	// 		ideal: Perbill::one(),
	// 		max: Perbill::one(),
	// 	};
	// 	Pallet::<T>::set_inflation(RawOrigin::Root.into(), high_inflation.clone())?;
	// 	Pallet::<T>::set_total_selected(RawOrigin::Root.into(), 28u32)?;
	// 	// INITIALIZE COLLATOR STATE
	// 	let mut collators: Vec<T::AccountId> = Vec::new();
	// 	let mut collator_count = 1u32;
	// 	for i in 0..x {
	// 		let seed = USER_SEED - i;
	// 		let collator = create_funded_collator::<T>(
	// 			"collator",
	// 			seed,
	// 			min_candidate_stk::<T>() * 1_000_000u32.into(),
	// 			true,
	// 			collator_count
	// 		)?;
	// 		collators.push(collator);
	// 		collator_count += 1u32;
	// 	}
	// 	// STORE starting balances for all collators
	// 	let collator_starting_balances: Vec<(
	// 		T::AccountId,
	// 		<<T as Config>::Currency as Currency<T::AccountId>>::Balance
	// 	)> = collators.iter().map(|x| (x.clone(), <T as pallet::Config>::Currency::free_balance(&x))).collect();
	// 	// INITIALIZE DELEGATIONS
	// 	let mut col_del_count: BTreeMap<T::AccountId, u32> = BTreeMap::new();
	// 	collators.iter().for_each(|x| {
	// 		col_del_count.insert(x.clone(), 0u32);
	// 	});
	// 	let mut delegators: Vec<T::AccountId> = Vec::new();
	// 	let mut remaining_delegations = if total_delegations > max_delegators_per_collator {
	// 		for j in 1..(max_delegators_per_collator + 1) {
	// 			let seed = USER_SEED + j;
	// 			let delegator = create_funded_delegator::<T>(
	// 				"delegator",
	// 				seed,
	// 				min_candidate_stk::<T>() * 1_000_000u32.into(),
	// 				collators[0].clone(),
	// 				true,
	// 				delegators.len() as u32,
	// 			)?;
	// 			delegators.push(delegator);
	// 		}
	// 		total_delegations - max_delegators_per_collator
	// 	} else {
	// 		for j in 1..(total_delegations + 1) {
	// 			let seed = USER_SEED + j;
	// 			let delegator = create_funded_delegator::<T>(
	// 				"delegator",
	// 				seed,
	// 				min_candidate_stk::<T>() * 1_000_000u32.into(),
	// 				collators[0].clone(),
	// 				true,
	// 				delegators.len() as u32,
	// 			)?;
	// 			delegators.push(delegator);
	// 		}
	// 		0u32
	// 	};
	// 	col_del_count.insert(collators[0].clone(), delegators.len() as u32);
	// 	// FILL remaining delegations
	// 	if remaining_delegations > 0 {
	// 		for (col, n_count) in col_del_count.iter_mut() {
	// 			if n_count < &mut (delegators.len() as u32) {
	// 				// assumes delegators.len() <= MaxDelegatorsPerCandidate
	// 				let mut open_spots = delegators.len() as u32 - *n_count;
	// 				while open_spots > 0 && remaining_delegations > 0 {
	// 					let caller = delegators[open_spots as usize - 1usize].clone();
	// 					if let Ok(_) = Pallet::<T>::delegate(RawOrigin::Signed(
	// 						caller.clone()).into(),
	// 						col.clone(),
	// 						<<T as Config>::MinDelegatorStk as Get<Balance>>::get(),
	// 						*n_count,
	// 						collators.len() as u32, // overestimate
	// 					) {
	// 						*n_count += 1;
	// 						remaining_delegations -= 1;
	// 					}
	// 					open_spots -= 1;
	// 				}
	// 			}
	// 			if remaining_delegations == 0 {
	// 				break;
	// 			}
	// 		}
	// 	}
	// 	// STORE starting balances for all delegators
	// 	let delegator_starting_balances: Vec<(
	// 		T::AccountId,
	// 		<<T as Config>::Currency as Currency<T::AccountId>>::Balance
	// 	)> = delegators.iter().map(|x| (x.clone(), <T as pallet::Config>::Currency::free_balance(&x))).collect();
	// 	// PREPARE RUN_TO_BLOCK LOOP
	// 	let before_running_round_index = Pallet::<T>::round().current;
	// 	let round_length: T::BlockNumber = Pallet::<T>::round().length.into();
	// 	let reward_delay = <<T as Config>::RewardPaymentDelay as Get<u32>>::get() + 2u32;
	// 	let mut now = <frame_system::Pallet<T>>::block_number() + 1u32.into();
	// 	let mut counter = 0usize;
	// 	let end = Pallet::<T>::round().first + (round_length * reward_delay.into());
	// 	// SET collators as authors for blocks from now - end
	// 	while now < end {
	// 		let author = collators[counter % collators.len()].clone();
	// 		Pallet::<T>::note_author(author);
	// 		<frame_system::Pallet<T>>::on_finalize(<frame_system::Pallet<T>>::block_number());
	// 		<frame_system::Pallet<T>>::set_block_number(
	// 			<frame_system::Pallet<T>>::block_number() + 1u32.into()
	// 		);
	// 		<frame_system::Pallet<T>>::on_initialize(<frame_system::Pallet<T>>::block_number());
	// 		Pallet::<T>::on_initialize(<frame_system::Pallet<T>>::block_number());
	// 		now += 1u32.into();
	// 		counter += 1usize;
	// 	}
	// 	Pallet::<T>::note_author(collators[counter % collators.len()].clone());
	// 	<frame_system::Pallet<T>>::on_finalize(<frame_system::Pallet<T>>::block_number());
	// 	<frame_system::Pallet<T>>::set_block_number(
	// 		<frame_system::Pallet<T>>::block_number() + 1u32.into()
	// 	);
	// 	<frame_system::Pallet<T>>::on_initialize(<frame_system::Pallet<T>>::block_number());
	// }: { Pallet::<T>::on_initialize(<frame_system::Pallet<T>>::block_number()); }
	// verify {
	// 	// Collators have been paid
	// 	for (col, initial) in collator_starting_balances {
	// 		assert!(<T as pallet::Config>::Currency::free_balance(&col) > initial);
	// 	}
	// 	// Nominators have been paid
	// 	for (col, initial) in delegator_starting_balances {
	// 		assert!(<T as pallet::Config>::Currency::free_balance(&col) > initial);
	// 	}
	// 	// Round transitions
	// 	assert_eq!(Pallet::<T>::round().current, before_running_round_index + reward_delay);
	// }

	// passive_on_initialize {
	// 	let collator: T::AccountId = create_funded_collator::<T>(
	// 		"collator",
	// 		USER_SEED,
	// 		0u32.into(),
	// 		true,
	// 		1u32
	// 	)?;
	// 	let start = <frame_system::Pallet<T>>::block_number();
	// 	Pallet::<T>::note_author(collator.clone());
	// 	<frame_system::Pallet<T>>::on_finalize(start);
	// 	<frame_system::Pallet<T>>::set_block_number(
	// 		start + 1u32.into()
	// 	);
	// 	let end = <frame_system::Pallet<T>>::block_number();
	// 	<frame_system::Pallet<T>>::on_initialize(end);
	// }: { Pallet::<T>::on_initialize(end); }
	// verify {
	// 	// Round transitions
	// 	assert_eq!(start + 1u32.into(), end);
	// }
}