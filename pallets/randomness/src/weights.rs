// Copyright 2019-2022 PureStake Inc.
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


//! Autogenerated weights for pallet_randomness
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-04-28, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `benchmarker`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: None, DB CACHE: 1024

// Executed Command:
// ./target/release/moonbeam
// benchmark
// pallet
// --execution=wasm
// --wasm-execution=compiled
// --pallet
// *
// --extrinsic
// *
// --steps
// 50
// --repeat
// 20
// --template=./benchmarking/frame-weight-template.hbs
// --json-file
// raw.json
// --output
// weights/

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_randomness.
pub trait WeightInfo {
	fn set_babe_randomness_results() -> Weight;
	fn on_initialize() -> Weight;
	fn request_randomness() -> Weight;
	fn prepare_fulfillment(x: u32, ) -> Weight;
	fn finish_fulfillment() -> Weight;
	fn increase_fee() -> Weight;
	fn execute_request_expiration() -> Weight;
}

/// Weights for pallet_randomness using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Randomness RelayEpoch (r:1 w:1)
	/// Proof Skipped: Randomness RelayEpoch (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ParachainSystem ValidationData (r:1 w:0)
	/// Proof Skipped: ParachainSystem ValidationData (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ParachainSystem RelayStateProof (r:1 w:0)
	/// Proof Skipped: ParachainSystem RelayStateProof (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness InherentIncluded (r:0 w:1)
	/// Proof Skipped: Randomness InherentIncluded (max_values: Some(1), max_size: None, mode: Measured)
	fn set_babe_randomness_results() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `297`
		//  Estimated: `9405`
		// Minimum execution time: 22_271_000 picoseconds.
		Weight::from_parts(22_704_000, 9405)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: Randomness NotFirstBlock (r:1 w:0)
	/// Proof Skipped: Randomness NotFirstBlock (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Digest (r:1 w:0)
	/// Proof Skipped: System Digest (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: AuthorMapping MappingWithDeposit (r:1 w:0)
	/// Proof Skipped: AuthorMapping MappingWithDeposit (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness LocalVrfOutput (r:1 w:1)
	/// Proof Skipped: Randomness LocalVrfOutput (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	fn on_initialize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `719`
		//  Estimated: `14980`
		// Minimum execution time: 1_190_265_000 picoseconds.
		Weight::from_parts(1_191_969_000, 14980)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Randomness RequestCount (r:1 w:1)
	/// Proof Skipped: Randomness RequestCount (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness Requests (r:0 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	fn request_randomness() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `442`
		//  Estimated: `12448`
		// Minimum execution time: 56_924_000 picoseconds.
		Weight::from_parts(57_236_000, 12448)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(5_u64))
	}
	/// Storage: Randomness Requests (r:1 w:0)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:0)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// The range of component `x` is `[1, 100]`.
	fn prepare_fulfillment(x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `412`
		//  Estimated: `7754`
		// Minimum execution time: 13_365_000 picoseconds.
		Weight::from_parts(13_619_602, 7754)
			// Standard Error: 1_129
			.saturating_add(Weight::from_parts(301_030, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
	}
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness Requests (r:0 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	fn finish_fulfillment() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `706`
		//  Estimated: `11049`
		// Minimum execution time: 42_894_000 picoseconds.
		Weight::from_parts(43_277_000, 11049)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: Randomness Requests (r:1 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	fn increase_fee() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `792`
		//  Estimated: `10429`
		// Minimum execution time: 40_040_000 picoseconds.
		Weight::from_parts(40_462_000, 10429)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: Randomness Requests (r:1 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	fn execute_request_expiration() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `801`
		//  Estimated: `14704`
		// Minimum execution time: 45_278_000 picoseconds.
		Weight::from_parts(45_761_000, 14704)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Randomness RelayEpoch (r:1 w:1)
	/// Proof Skipped: Randomness RelayEpoch (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ParachainSystem ValidationData (r:1 w:0)
	/// Proof Skipped: ParachainSystem ValidationData (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ParachainSystem RelayStateProof (r:1 w:0)
	/// Proof Skipped: ParachainSystem RelayStateProof (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness InherentIncluded (r:0 w:1)
	/// Proof Skipped: Randomness InherentIncluded (max_values: Some(1), max_size: None, mode: Measured)
	fn set_babe_randomness_results() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `297`
		//  Estimated: `9405`
		// Minimum execution time: 22_271_000 picoseconds.
		Weight::from_parts(22_704_000, 9405)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: Randomness NotFirstBlock (r:1 w:0)
	/// Proof Skipped: Randomness NotFirstBlock (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Digest (r:1 w:0)
	/// Proof Skipped: System Digest (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: AuthorMapping MappingWithDeposit (r:1 w:0)
	/// Proof Skipped: AuthorMapping MappingWithDeposit (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness LocalVrfOutput (r:1 w:1)
	/// Proof Skipped: Randomness LocalVrfOutput (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	fn on_initialize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `719`
		//  Estimated: `14980`
		// Minimum execution time: 1_190_265_000 picoseconds.
		Weight::from_parts(1_191_969_000, 14980)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Randomness RequestCount (r:1 w:1)
	/// Proof Skipped: Randomness RequestCount (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness Requests (r:0 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	fn request_randomness() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `442`
		//  Estimated: `12448`
		// Minimum execution time: 56_924_000 picoseconds.
		Weight::from_parts(57_236_000, 12448)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(5_u64))
	}
	/// Storage: Randomness Requests (r:1 w:0)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness RandomnessResults (r:1 w:0)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// The range of component `x` is `[1, 100]`.
	fn prepare_fulfillment(x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `412`
		//  Estimated: `7754`
		// Minimum execution time: 13_365_000 picoseconds.
		Weight::from_parts(13_619_602, 7754)
			// Standard Error: 1_129
			.saturating_add(Weight::from_parts(301_030, 0).saturating_mul(x.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
	}
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	/// Storage: Randomness Requests (r:0 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	fn finish_fulfillment() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `706`
		//  Estimated: `11049`
		// Minimum execution time: 42_894_000 picoseconds.
		Weight::from_parts(43_277_000, 11049)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: Randomness Requests (r:1 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	fn increase_fee() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `792`
		//  Estimated: `10429`
		// Minimum execution time: 40_040_000 picoseconds.
		Weight::from_parts(40_462_000, 10429)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: Randomness Requests (r:1 w:1)
	/// Proof Skipped: Randomness Requests (max_values: None, max_size: None, mode: Measured)
	/// Storage: System Account (r:2 w:2)
	/// Proof: System Account (max_values: None, max_size: Some(116), added: 2591, mode: MaxEncodedLen)
	/// Storage: Randomness RandomnessResults (r:1 w:1)
	/// Proof Skipped: Randomness RandomnessResults (max_values: None, max_size: None, mode: Measured)
	fn execute_request_expiration() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `801`
		//  Estimated: `14704`
		// Minimum execution time: 45_278_000 picoseconds.
		Weight::from_parts(45_761_000, 14704)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
}