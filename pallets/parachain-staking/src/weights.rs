// This file is part of Mangata.

// Copyright (C) 2020-2022 Mangata Foundation.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Autogenerated weights for parachain_staking
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-03-24, STEPS: `20`, REPEAT: 10, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// /home/ubuntu/mangata-node/scripts/..//target/release/mangata-node
// benchmark
// --chain
// dev
// --execution
// wasm
// --wasm-execution
// compiled
// --pallet
// parachain_staking
// --extrinsic
// *
// --steps
// 20
// --repeat
// 10
// --output
// ./benchmarks/parachain_staking_weights.rs
// --template
// ./templates/module-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for parachain_staking.
pub trait WeightInfo {
	fn set_total_selected() -> Weight;
	fn set_collator_commission() -> Weight;
	fn join_candidates(x: u32, y: u32, ) -> Weight;
	fn schedule_leave_candidates(x: u32, ) -> Weight;
	fn execute_leave_candidates(x: u32, ) -> Weight;
	fn cancel_leave_candidates(x: u32, ) -> Weight;
	fn go_offline() -> Weight;
	fn go_online() -> Weight;
	fn schedule_candidate_bond_more() -> Weight;
	fn schedule_candidate_bond_less() -> Weight;
	fn execute_candidate_bond_more() -> Weight;
	fn execute_candidate_bond_less() -> Weight;
	fn cancel_candidate_bond_more() -> Weight;
	fn cancel_candidate_bond_less() -> Weight;
	fn delegate(x: u32, y: u32, ) -> Weight;
	fn schedule_leave_delegators() -> Weight;
	fn execute_leave_delegators(x: u32, ) -> Weight;
	fn cancel_leave_delegators() -> Weight;
	fn schedule_revoke_delegation() -> Weight;
	fn schedule_delegator_bond_more() -> Weight;
	fn schedule_delegator_bond_less() -> Weight;
	fn execute_revoke_delegation() -> Weight;
	fn execute_delegator_bond_more() -> Weight;
	fn execute_delegator_bond_less() -> Weight;
	fn cancel_revoke_delegation() -> Weight;
	fn cancel_delegator_bond_more() -> Weight;
	fn cancel_delegator_bond_less() -> Weight;
	fn add_staking_liquidity_token(x: u32, ) -> Weight;
	fn remove_staking_liquidity_token(x: u32, ) -> Weight;
	fn passive_session_change() -> Weight;
	fn active_session_change(x: u32, y: u32, z: u32, w: u32, ) -> Weight;
}

/// Weights for parachain_staking using the Mangata node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: ParachainStaking TotalSelected (r:1 w:1)
	fn set_total_selected() -> Weight {
		Weight::from_ref_time(14_867_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CollatorCommission (r:1 w:1)
	fn set_collator_commission() -> Weight {
		Weight::from_ref_time(14_948_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking DelegatorState (r:1 w:0)
	// Storage: ParachainStaking StakingLiquidityTokens (r:1 w:0)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn join_candidates(x: u32, y: u32, ) -> Weight {
		Weight::from_ref_time(57_975_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(452_000)).saturating_mul(x as u64))
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(95_000)).saturating_mul(y as u64))
			.saturating_add(T::DbWeight::get().reads(6 as u64))
			.saturating_add(T::DbWeight::get().writes(4 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	fn schedule_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(34_598_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(428_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: Tokens Accounts (r:2 w:2)
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn execute_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(19_556_000)
			// Standard Error: 19_000
			.saturating_add((Weight::from_ref_time(19_556_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().reads((2 as u64).saturating_mul(x as u64)))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
			.saturating_add(T::DbWeight::get().writes((2 as u64).saturating_mul(x as u64)))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	fn cancel_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(31_884_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(421_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn go_offline() -> Weight {
		Weight::from_ref_time(34_946_000)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn go_online() -> Weight {
		Weight::from_ref_time(33_628_000)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:0)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_candidate_bond_more() -> Weight {
		Weight::from_ref_time(36_194_000)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_candidate_bond_less() -> Weight {
		Weight::from_ref_time(29_009_000)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	fn execute_candidate_bond_more() -> Weight {
		Weight::from_ref_time(61_070_000)
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(4 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	fn execute_candidate_bond_less() -> Weight {
		Weight::from_ref_time(57_922_000)
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(4 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	fn cancel_candidate_bond_more() -> Weight {
		Weight::from_ref_time(26_206_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	fn cancel_candidate_bond_less() -> Weight {
		Weight::from_ref_time(25_974_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn delegate(x: u32, y: u32, ) -> Weight {
		Weight::from_ref_time(62_286_000)
			// Standard Error: 9_000
			.saturating_add((Weight::from_ref_time(689_000)).saturating_mul(x as u64))
			// Standard Error: 30_000
			.saturating_add((Weight::from_ref_time(639_000)).saturating_mul(y as u64))
			.saturating_add(T::DbWeight::get().reads(5 as u64))
			.saturating_add(T::DbWeight::get().writes(5 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_leave_delegators() -> Weight {
		Weight::from_ref_time(30_002_000)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn execute_leave_delegators(x: u32, ) -> Weight {
		Weight::from_ref_time(0)
			// Standard Error: 110_000
			.saturating_add((Weight::from_ref_time(29_927_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(4 as u64))
			.saturating_add(T::DbWeight::get().reads((1 as u64).saturating_mul(x as u64)))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
			.saturating_add(T::DbWeight::get().writes((1 as u64).saturating_mul(x as u64)))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	fn cancel_leave_delegators() -> Weight {
		Weight::from_ref_time(25_498_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_revoke_delegation() -> Weight {
		Weight::from_ref_time(30_598_000)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:0)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_delegator_bond_more() -> Weight {
		Weight::from_ref_time(38_554_000)
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	fn schedule_delegator_bond_less() -> Weight {
		Weight::from_ref_time(30_322_000)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn execute_revoke_delegation() -> Weight {
		Weight::from_ref_time(76_394_000)
			.saturating_add(T::DbWeight::get().reads(6 as u64))
			.saturating_add(T::DbWeight::get().writes(5 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn execute_delegator_bond_more() -> Weight {
		Weight::from_ref_time(70_382_000)
			.saturating_add(T::DbWeight::get().reads(6 as u64))
			.saturating_add(T::DbWeight::get().writes(5 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	// Storage: ParachainStaking Round (r:1 w:0)
	// Storage: ParachainStaking CandidateState (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: ParachainStaking CandidatePool (r:1 w:1)
	// Storage: ParachainStaking Total (r:1 w:1)
	fn execute_delegator_bond_less() -> Weight {
		Weight::from_ref_time(66_780_000)
			.saturating_add(T::DbWeight::get().reads(6 as u64))
			.saturating_add(T::DbWeight::get().writes(5 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	fn cancel_revoke_delegation() -> Weight {
		Weight::from_ref_time(27_076_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	fn cancel_delegator_bond_more() -> Weight {
		Weight::from_ref_time(32_355_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking DelegatorState (r:1 w:1)
	fn cancel_delegator_bond_less() -> Weight {
		Weight::from_ref_time(31_925_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking StakingLiquidityTokens (r:1 w:1)
	fn add_staking_liquidity_token(x: u32, ) -> Weight {
		Weight::from_ref_time(7_373_000)
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(92_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking StakingLiquidityTokens (r:1 w:1)
	fn remove_staking_liquidity_token(x: u32, ) -> Weight {
		Weight::from_ref_time(7_078_000)
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(95_000)).saturating_mul(x as u64))
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: ParachainStaking Round (r:1 w:0)
	fn passive_session_change() -> Weight {
		Weight::from_ref_time(5_166_000)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
	}
	// Storage: ParachainStaking Round (r:1 w:1)
	// Storage: Session CurrentIndex (r:1 w:1)
	// Storage: Session QueuedChanged (r:1 w:1)
	// Storage: Session QueuedKeys (r:1 w:1)
	// Storage: Session DisabledValidators (r:1 w:0)
	// Storage: ParachainStaking Points (r:1 w:1)
	// Storage: ParachainStaking Staked (r:1 w:2)
	// Storage: ParachainStaking InflationConfig (r:1 w:0)
	// Storage: Tokens TotalIssuance (r:4 w:1)
	// Storage: ParachainStaking ParachainBondInfo (r:1 w:0)
	// Storage: Tokens Accounts (r:289 w:289)
	// Storage: System Account (r:287 w:287)
	// Storage: ParachainStaking CollatorCommission (r:1 w:0)
	// Storage: ParachainStaking AwardedPts (r:25 w:24)
	// Storage: ParachainStaking AtStake (r:24 w:48)
	// Storage: ParachainStaking StakingLiquidityTokens (r:1 w:1)
	// Storage: Xyk LiquidityPools (r:3 w:0)
	// Storage: Xyk Pools (r:3 w:0)
	// Storage: ParachainStaking CandidatePool (r:1 w:0)
	// Storage: ParachainStaking TotalSelected (r:1 w:0)
	// Storage: ParachainStaking CandidateState (r:24 w:0)
	// Storage: Session NextKeys (r:24 w:0)
	// Storage: Aura Authorities (r:1 w:0)
	// Storage: ParachainStaking SelectedCandidates (r:0 w:1)
	// Storage: Session Validators (r:0 w:1)
	fn active_session_change(x: u32, y: u32, z: u32, w: u32, ) -> Weight {
		Weight::from_ref_time(470_042_000)
			// Standard Error: 1_684_000
			.saturating_add((Weight::from_ref_time(23_366_000)).saturating_mul(x as u64))
			// Standard Error: 4_024_000
			.saturating_add((Weight::from_ref_time(139_318_000)).saturating_mul(y as u64))
			// Standard Error: 23_684_000
			.saturating_add((Weight::from_ref_time(761_880_000)).saturating_mul(z as u64))
			// Standard Error: 12_287_000
			.saturating_add((Weight::from_ref_time(470_042_000)).saturating_mul(w as u64))
			.saturating_add(T::DbWeight::get().reads((4 as u64).saturating_mul(x as u64)))
			.saturating_add(T::DbWeight::get().reads((10 as u64).saturating_mul(y as u64)))
			.saturating_add(T::DbWeight::get().reads((51 as u64).saturating_mul(z as u64)))
			.saturating_add(T::DbWeight::get().reads((34 as u64).saturating_mul(w as u64)))
			.saturating_add(T::DbWeight::get().writes((1 as u64).saturating_mul(x as u64)))
			.saturating_add(T::DbWeight::get().writes((9 as u64).saturating_mul(y as u64)))
			.saturating_add(T::DbWeight::get().writes((50 as u64).saturating_mul(z as u64)))
			.saturating_add(T::DbWeight::get().writes((33 as u64).saturating_mul(w as u64)))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn set_total_selected() -> Weight {
		Weight::from_ref_time(14_867_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn set_collator_commission() -> Weight {
		Weight::from_ref_time(14_948_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn join_candidates(x: u32, y: u32, ) -> Weight {
		Weight::from_ref_time(57_975_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(452_000)).saturating_mul(x as u64))
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(95_000)).saturating_mul(y as u64))
			.saturating_add(RocksDbWeight::get().reads(6 as u64))
			.saturating_add(RocksDbWeight::get().writes(4 as u64))
	}
	fn schedule_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(34_598_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(428_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	fn execute_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(34_089_000)
			// Standard Error: 19_000
			.saturating_add((Weight::from_ref_time(19_556_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().reads((2 as u64).saturating_mul(x as u64)))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
			.saturating_add(RocksDbWeight::get().writes((2 as u64).saturating_mul(x as u64)))
	}
	fn cancel_leave_candidates(x: u32, ) -> Weight {
		Weight::from_ref_time(31_884_000)
			// Standard Error: 3_000
			.saturating_add((Weight::from_ref_time(421_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	fn go_offline() -> Weight {
		Weight::from_ref_time(34_946_000)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	fn go_online() -> Weight {
		Weight::from_ref_time(33_628_000)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	fn schedule_candidate_bond_more() -> Weight {
		Weight::from_ref_time(36_194_000)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn schedule_candidate_bond_less() -> Weight {
		Weight::from_ref_time(29_009_000)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn execute_candidate_bond_more() -> Weight {
		Weight::from_ref_time(61_070_000)
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(4 as u64))
	}
	fn execute_candidate_bond_less() -> Weight {
		Weight::from_ref_time(57_922_000)
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(4 as u64))
	}
	fn cancel_candidate_bond_more() -> Weight {
		Weight::from_ref_time(26_206_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn cancel_candidate_bond_less() -> Weight {
		Weight::from_ref_time(25_974_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn delegate(x: u32, y: u32, ) -> Weight {
		Weight::from_ref_time(62_286_000)
			// Standard Error: 9_000
			.saturating_add((Weight::from_ref_time(689_000)).saturating_mul(x as u64))
			// Standard Error: 30_000
			.saturating_add((Weight::from_ref_time(639_000)).saturating_mul(y as u64))
			.saturating_add(RocksDbWeight::get().reads(5 as u64))
			.saturating_add(RocksDbWeight::get().writes(5 as u64))
	}
	fn schedule_leave_delegators() -> Weight {
		Weight::from_ref_time(30_002_000)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn execute_leave_delegators(x: u32, ) -> Weight {
		Weight::from_ref_time(0)
			// Standard Error: 110_000
			.saturating_add((Weight::from_ref_time(29_927_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(4 as u64))
			.saturating_add(RocksDbWeight::get().reads((1 as u64).saturating_mul(x as u64)))
			.saturating_add(RocksDbWeight::get().writes(3 as u64))
			.saturating_add(RocksDbWeight::get().writes((1 as u64).saturating_mul(x as u64)))
	}
	fn cancel_leave_delegators() -> Weight {
		Weight::from_ref_time(25_498_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn schedule_revoke_delegation() -> Weight {
		Weight::from_ref_time(30_598_000)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn schedule_delegator_bond_more() -> Weight {
		Weight::from_ref_time(38_554_000)
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn schedule_delegator_bond_less() -> Weight {
		Weight::from_ref_time(30_322_000)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn execute_revoke_delegation() -> Weight {
		Weight::from_ref_time(76_394_000)
			.saturating_add(RocksDbWeight::get().reads(6 as u64))
			.saturating_add(RocksDbWeight::get().writes(5 as u64))
	}
	fn execute_delegator_bond_more() -> Weight {
		Weight::from_ref_time(70_382_000)
			.saturating_add(RocksDbWeight::get().reads(6 as u64))
			.saturating_add(RocksDbWeight::get().writes(5 as u64))
	}
	fn execute_delegator_bond_less() -> Weight {
		Weight::from_ref_time(66_780_000)
			.saturating_add(RocksDbWeight::get().reads(6 as u64))
			.saturating_add(RocksDbWeight::get().writes(5 as u64))
	}
	fn cancel_revoke_delegation() -> Weight {
		Weight::from_ref_time(27_076_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn cancel_delegator_bond_more() -> Weight {
		Weight::from_ref_time(32_355_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn cancel_delegator_bond_less() -> Weight {
		Weight::from_ref_time(31_925_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn add_staking_liquidity_token(x: u32, ) -> Weight {
		Weight::from_ref_time(7_373_000)
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(92_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn remove_staking_liquidity_token(x: u32, ) -> Weight {
		Weight::from_ref_time(7_078_000)
			// Standard Error: 1_000
			.saturating_add((Weight::from_ref_time(95_000)).saturating_mul(x as u64))
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn passive_session_change() -> Weight {
		Weight::from_ref_time(5_166_000)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
	}
	fn active_session_change(x: u32, y: u32, z: u32, w: u32, ) -> Weight {
		Weight::from_ref_time(470_042_000)
			// Standard Error: 1_684_000
			.saturating_add((Weight::from_ref_time(23_366_000)).saturating_mul(x as u64))
			// Standard Error: 4_024_000
			.saturating_add((Weight::from_ref_time(139_318_000)).saturating_mul(y as u64))
			// Standard Error: 23_684_000
			.saturating_add((Weight::from_ref_time(761_880_000)).saturating_mul(z as u64))
			// Standard Error: 12_287_000
			.saturating_add((Weight::from_ref_time(470_042_000)).saturating_mul(w as u64))
			.saturating_add(RocksDbWeight::get().reads((4 as u64).saturating_mul(x as u64)))
			.saturating_add(RocksDbWeight::get().reads((10 as u64).saturating_mul(y as u64)))
			.saturating_add(RocksDbWeight::get().reads((51 as u64).saturating_mul(z as u64)))
			.saturating_add(RocksDbWeight::get().reads((34 as u64).saturating_mul(w as u64)))
			.saturating_add(RocksDbWeight::get().writes((1 as u64).saturating_mul(x as u64)))
			.saturating_add(RocksDbWeight::get().writes((9 as u64).saturating_mul(y as u64)))
			.saturating_add(RocksDbWeight::get().writes((50 as u64).saturating_mul(z as u64)))
			.saturating_add(RocksDbWeight::get().writes((33 as u64).saturating_mul(w as u64)))
	}
}