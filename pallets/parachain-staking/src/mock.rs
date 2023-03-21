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

//! Test utilities
use crate as stake;
use crate::{pallet, AwardedPts, Balance, Config, DispatchError, Points, TokenId, Valuate, BondKind, StakingReservesProviderTrait};
use frame_support::{
	construct_runtime, parameter_types,
	traits::{Contains, Everything, GenesisBuild, OnFinalize, OnInitialize, tokens::currency::{MultiTokenCurrency}},
	PalletId, assert_ok
};
use mangata_types::Amount;
use orml_tokens::{MultiTokenReservableCurrency};
use orml_traits::parameter_type_with_key;
use parity_scale_codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_core::{H256};
use sp_io;
use sp_runtime::traits::Zero;
use sp_runtime::{DispatchResult,
	testing::Header,
	traits::{AccountIdConversion, BlakeTwo256, IdentityLookup},
	Perbill, Percent, RuntimeDebug,
};
use sp_std::marker::PhantomData;
use orml_tokens::MultiTokenCurrencyExtended;
use pallet_vesting_mangata::MultiTokenVestingSchedule;
use sp_std::convert::{TryFrom, TryInto};

pub type AccountId = u64;
pub type BlockNumber = u64;
pub const MGA_TOKEN_ID: TokenId = 0;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Tokens: orml_tokens::{Pallet, Storage, Call, Event<T>, Config<T>},
		Stake: stake::{Pallet, Call, Storage, Config<T>, Event<T>},
		Issuance: pallet_issuance::{Pallet, Storage, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	// pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
	pub const SS58Prefix: u8 = 42;
}
impl frame_system::Config for Test {
	type BaseCallFilter = Everything;
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = BlockNumber;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type BlockWeights = ();
	type BlockLength = ();
	type SS58Prefix = SS58Prefix;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub const HistoryLimit: u32 = 10u32;

	pub const LiquidityMiningIssuanceVaultId: PalletId = PalletId(*b"py/lqmiv");
	pub LiquidityMiningIssuanceVault: AccountId = LiquidityMiningIssuanceVaultId::get().into_account_truncating();
	pub const StakingIssuanceVaultId: PalletId = PalletId(*b"py/stkiv");
	pub StakingIssuanceVault: AccountId = StakingIssuanceVaultId::get().into_account_truncating();

	pub const TotalCrowdloanAllocation: Balance = 200_000_000;
	pub const IssuanceCap: Balance = 4_000_000_000;
	pub const LinearIssuanceBlocks: u32 = 13_140_000u32; // 5 years
	pub const LiquidityMiningSplit: Perbill = Perbill::from_parts(555555556);
	pub const StakingSplit: Perbill = Perbill::from_parts(444444444);
	pub const ImmediateTGEReleasePercent: Percent = Percent::from_percent(20);
	pub const TGEReleasePeriod: u32 = 5_256_000u32; // 2 years
	pub const TGEReleaseBegin: u32 = 100_800u32; // Two weeks into chain start
}

pub struct ActivedPoolQueryApiMock;


impl pallet_issuance::ActivedPoolQueryApi for ActivedPoolQueryApiMock {
    fn get_pool_activate_amount(_liquidity_token_id: TokenId) -> Option<Balance> {
        todo!()
    }
}

impl pallet_issuance::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type NativeCurrencyId = MgaTokenId;
	type Tokens = orml_tokens::MultiTokenCurrencyAdapter<Test>;
	type BlocksPerRound = BlocksPerRound;
	type HistoryLimit = HistoryLimit;
	type LiquidityMiningIssuanceVault = LiquidityMiningIssuanceVault;
	type StakingIssuanceVault = StakingIssuanceVault;
	type TotalCrowdloanAllocation = TotalCrowdloanAllocation;
	type IssuanceCap = IssuanceCap;
	type LinearIssuanceBlocks = LinearIssuanceBlocks;
	type LiquidityMiningSplit = LiquidityMiningSplit;
	type StakingSplit = StakingSplit;
	type ImmediateTGEReleasePercent = ImmediateTGEReleasePercent;
	type TGEReleasePeriod = TGEReleasePeriod;
	type TGEReleaseBegin = TGEReleaseBegin;
	type VestingProvider = TestVestingModule<AccountId, orml_tokens::MultiTokenCurrencyAdapter<Test>, BlockNumber>;
	type WeightInfo = ();
	type ActivedPoolQueryApiType = ActivedPoolQueryApiMock;
}

pub struct TestVestingModule<A, C: MultiTokenCurrency<A>, B>(PhantomData<A>,PhantomData<C>,PhantomData<B>);
impl<A, C: MultiTokenCurrency<A>, B> MultiTokenVestingSchedule<A> for TestVestingModule<A, C, B>
{
	type Currency = C;
	type Moment = B;

	fn vesting_balance(_who: &A, _token_id: <C as MultiTokenCurrency<A>>::CurrencyId) -> Option<<C as MultiTokenCurrency<A>>::Balance> {
		None
	}

	fn add_vesting_schedule(
		_who: &A,
		_locked: <C as MultiTokenCurrency<A>>::Balance,
		_per_block: <C as MultiTokenCurrency<A>>::Balance,
		_starting_block: B,
		_token_id: <C as MultiTokenCurrency<A>>::CurrencyId,
	) -> DispatchResult {
		
		Ok(())
	}

	// Ensure we can call `add_vesting_schedule` without error. This should always
	// be called prior to `add_vesting_schedule`.
	fn can_add_vesting_schedule(
		_who: &A,
		_locked: <C as MultiTokenCurrency<A>>::Balance,
		_per_block: <C as MultiTokenCurrency<A>>::Balance,
		_starting_block: B,
		_token_id: <C as MultiTokenCurrency<A>>::CurrencyId,
	) -> DispatchResult {
		Ok(())
	}

	/// Remove a vesting schedule for a given account.
	fn remove_vesting_schedule(_who: &A, _token_id: <C as MultiTokenCurrency<A>>::CurrencyId, _schedule_index: u32) -> DispatchResult {
		Ok(())
	}
}

parameter_type_with_key! {
	pub ExistentialDeposits: |currency_id: TokenId| -> Balance {
		match currency_id {
			&MGA_TOKEN_ID => 0,
			_ => 0,
		}
	};
}

parameter_types! {
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const BnbTreasurySubAccDerive: [u8; 4] = *b"bnbt";
	pub TreasuryAccount: AccountId = TreasuryPalletId::get().into_account_truncating();
	pub const MaxLocks: u32 = 50;
	pub const MgaTokenId: TokenId = MGA_TOKEN_ID;
}

pub struct DustRemovalWhitelist;
impl Contains<AccountId> for DustRemovalWhitelist {
	fn contains(a: &AccountId) -> bool {
		*a == TreasuryAccount::get()
	}
}

impl orml_tokens::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Balance = Balance;
	type Amount = Amount;
	type CurrencyId = TokenId;
	type WeightInfo = ();
	type ExistentialDeposits = ExistentialDeposits;
	type MaxLocks = MaxLocks;
	type DustRemovalWhitelist = DustRemovalWhitelist;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type CurrencyHooks = ();
}

pub struct TokensStakingPassthrough<T: stake::Config>(PhantomData<T>);
impl<T: stake::Config> StakingReservesProviderTrait for TokensStakingPassthrough<T>{
	type AccountId = T::AccountId;

	fn can_bond(token_id: TokenId, account_id: &T::AccountId, amount: Balance, _use_balance_from: Option<BondKind>)
	-> bool{
		T::Currency::can_reserve(token_id.into(), &account_id, amount.into())
	}

	fn bond(token_id: TokenId, account_id: &T::AccountId, amount: Balance, _use_balance_from: Option<BondKind>)
	-> DispatchResult{
		T::Currency::reserve(token_id.into(), account_id, amount.into())
	}

	fn unbond(token_id: TokenId, account_id: &T::AccountId, amount: Balance) -> Balance{
		T::Currency::unreserve(token_id.into(), account_id, amount.into()).into()
	}
}


impl crate::StakingBenchmarkConfig for Test {}

parameter_types! {
	pub const BlocksPerRound: u32 = 5;
	pub const LeaveCandidatesDelay: u32 = 2;
	pub const CandidateBondDelay: u32 = 2;
	pub const LeaveDelegatorsDelay: u32 = 2;
	pub const RevokeDelegationDelay: u32 = 2;
	pub const DelegationBondDelay: u32 = 2;
	pub const RewardPaymentDelay: u32 = 2;
	pub const MinSelectedCandidates: u32 = 5;
	pub const MaxCollatorCandidates: u32 = 10;
	pub const MaxDelegatorsPerCandidate: u32 = 4;
	pub const MaxTotalDelegatorsPerCandidate: u32 = 10;
	pub const MaxDelegationsPerDelegator: u32 = 4;
	pub const DefaultCollatorCommission: Perbill = Perbill::from_percent(20);
	pub const MinCollatorStk: u128 = 10;
	pub const MinDelegation: u128 = 3;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type StakingReservesProvider = TokensStakingPassthrough<Test>;
	type Currency = orml_tokens::MultiTokenCurrencyAdapter<Test>;
	type MonetaryGovernanceOrigin = frame_system::EnsureRoot<AccountId>;
	type BlocksPerRound = BlocksPerRound;
	type LeaveCandidatesDelay = LeaveCandidatesDelay;
	type CandidateBondDelay = CandidateBondDelay;
	type LeaveDelegatorsDelay = LeaveDelegatorsDelay;
	type RevokeDelegationDelay = RevokeDelegationDelay;
	type DelegationBondDelay = DelegationBondDelay;
	type RewardPaymentDelay = RewardPaymentDelay;
	type MinSelectedCandidates = MinSelectedCandidates;
	type MaxCollatorCandidates = MaxCollatorCandidates;
	type MaxTotalDelegatorsPerCandidate = MaxTotalDelegatorsPerCandidate;
	type MaxDelegatorsPerCandidate = MaxDelegatorsPerCandidate;
	type MaxDelegationsPerDelegator = MaxDelegationsPerDelegator;
	type DefaultCollatorCommission = DefaultCollatorCommission;
	type MinCollatorStk = MinCollatorStk;
	type MinCandidateStk = MinCollatorStk;
	type MinDelegation = MinDelegation;
	type NativeTokenId = MgaTokenId;
	type StakingLiquidityTokenValuator = TestTokenValuator;
	type Issuance = Issuance;
	type StakingIssuanceVault = StakingIssuanceVault;
	type FallbackProvider = ();
	type WeightInfo = ();
}

#[derive(Default, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct TestTokenValuator {}

impl Valuate for TestTokenValuator {
	type Balance = Balance;

	type CurrencyId = TokenId;

	fn get_liquidity_asset(
		first_asset_id: Self::CurrencyId,
		_second_asset_id: Self::CurrencyId,
	) -> Result<TokenId, DispatchError> {
		Ok(first_asset_id / 100)
	}

	fn get_liquidity_token_mga_pool(
		_liquidity_token_id: Self::CurrencyId,
	) -> Result<(Self::CurrencyId, Self::CurrencyId), DispatchError> {
		unimplemented!("Not required in tests!")
	}

	fn valuate_liquidity_token(
		_liquidity_token_id: Self::CurrencyId,
		liquidity_token_amount: Self::Balance,
	) -> Self::Balance {
		liquidity_token_amount
	}

	fn scale_liquidity_by_mga_valuation(
		_mga_valuation: Self::Balance,
		_liquidity_token_amount: Self::Balance,
		_mga_token_amount: Self::Balance,
	) -> Self::Balance {
		unimplemented!("Not required in tests!")
	}

	fn get_pool_state(
		liquidity_token_id: Self::CurrencyId,
	) -> Option<(Self::Balance, Self::Balance)> {
		match liquidity_token_id {
			1 => Some((1, 1)),
			2 => Some((2, 1)),
			3 => Some((5, 1)),
			4 => Some((1, 1)),
			5 => Some((1, 2)),
			6 => Some((1, 5)),
			_ => None,
		}
	}

	fn get_reserves(
			_first_asset_id: TokenId,
			_second_asset_id: TokenId,
		) -> Result<(Balance, Balance), DispatchError> {
			todo!()
		}
	}

pub(crate) struct ExtBuilder {
	// tokens used for staking, these aren't backed in the xyk pallet and are just simply nominal tokens
	staking_tokens: Vec<(AccountId, Balance, TokenId)>,
	// [collator, amount]
	collators: Vec<(AccountId, Balance, TokenId)>,
	// [delegator, collator, delegation_amount]
	delegations: Vec<(AccountId, AccountId, Balance)>,
}

impl Default for ExtBuilder {
	fn default() -> ExtBuilder {
		ExtBuilder {
			staking_tokens: vec![],
			delegations: vec![],
			collators: vec![],
		}
	}
}

impl ExtBuilder {
	pub(crate) fn with_staking_tokens(
		mut self,
		staking_tokens: Vec<(AccountId, Balance, TokenId)>,
	) -> Self {
		self.staking_tokens = staking_tokens;
		self
	}

	pub(crate) fn with_default_staking_token(
		mut self,
		staking_tokens: Vec<(AccountId, Balance)>,
	) -> Self {
		let mut init_staking_token = vec![(999u64, 10u128, 0u32), (999u64, 100u128, 1u32)];
		init_staking_token.append(
			&mut staking_tokens
				.iter()
				.cloned()
				.map(|(x, y)| (x, y, 1u32))
				.collect::<Vec<(u64, u128, u32)>>(),
		);
		self.staking_tokens = init_staking_token;
		self
	}

	pub(crate) fn with_candidates(mut self, collators: Vec<(AccountId, Balance, TokenId)>) -> Self {
		self.collators = collators;
		self
	}

	pub(crate) fn with_default_token_candidates(
		mut self,
		collators: Vec<(AccountId, Balance)>,
	) -> Self {
		self.collators = collators
			.iter()
			.cloned()
			.map(|(x, y)| (x, y, 1u32))
			.collect();
		self
	}

	pub(crate) fn with_delegations(
		mut self,
		delegations: Vec<(AccountId, AccountId, Balance)>,
	) -> Self {
		self.delegations = delegations;
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.expect("Frame system builds valid default genesis config");

		orml_tokens::GenesisConfig::<Test> {
			tokens_endowment: Default::default(),
			created_tokens_for_staking: self
				.staking_tokens
				.iter()
				.cloned()
				.map(|(who, amount, token)| (who, token, amount))
				.collect(),
		}
		.assimilate_storage(&mut t)
		.expect("Tokens storage can be assimilated");

		stake::GenesisConfig::<Test> {
			candidates: self.collators,
			delegations: self.delegations,
		}
		.assimilate_storage(&mut t)
		.expect("Parachain Staking's storage can be assimilated");

		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| {
			System::set_block_number(1);

			if !StakeCurrency::exists(MGA_TOKEN_ID){
				assert_ok!(StakeCurrency::create(&99999, 100));
			}

			let current_issuance = StakeCurrency::total_issuance(MGA_TOKEN_ID);
			let target_tge = 2_000_000_000u128;
			assert!(current_issuance <= target_tge);

			assert_ok!(StakeCurrency::mint(MGA_TOKEN_ID, &99999, target_tge - current_issuance));
			
			assert_ok!(Issuance::finalize_tge(RuntimeOrigin::root()));
			assert_ok!(Issuance::init_issuance_config(RuntimeOrigin::root()));
			assert_ok!(Issuance::calculate_and_store_round_issuance(0u32));
		});
		ext
	}
}

pub(crate) fn roll_to(n: u64) {
	while System::block_number() < n {
		Stake::on_finalize(System::block_number());
		Tokens::on_finalize(System::block_number());
		System::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		Tokens::on_initialize(System::block_number());
		Stake::on_initialize(System::block_number());
		if <Stake as pallet_session::ShouldEndSession<_>>::should_end_session(System::block_number())
		{
			if System::block_number().is_zero() {
				<Stake as pallet_session::SessionManager<_>>::start_session(Default::default());
			} else {
				<Stake as pallet_session::SessionManager<_>>::start_session(1);
			}
		}
	}
}

pub(crate) fn last_event() -> RuntimeEvent {
	System::events().pop().expect("Event expected").event
}

pub(crate) fn events() -> Vec<pallet::Event<Test>> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| {
			if let RuntimeEvent::Stake(inner) = e {
				Some(inner)
			} else {
				None
			}
		})
		.collect::<Vec<_>>()
}

/// Assert input equal to the last event emitted
#[macro_export]
macro_rules! assert_last_event {
	($event:expr) => {
		match &$event {
			e => assert_eq!(*e, crate::mock::last_event()),
		}
	};
}

/// Compares the system events with passed in events
/// Prints highlighted diff iff assert_eq fails
#[macro_export]
macro_rules! assert_eq_events {
	($events:expr) => {
		match &$events {
			e => similar_asserts::assert_eq!(*e, crate::mock::events()),
		}
	};
}

/// Panics if an event is not found in the system log of events
#[macro_export]
macro_rules! assert_event_emitted {
	($event:expr) => {
		match &$event {
			e => {
				assert!(
					crate::mock::events().iter().find(|x| *x == e).is_some(),
					"Event {:?} was not found in events: \n {:?}",
					e,
					crate::mock::events()
				);
			}
		}
	};
}

// Same storage changes as EventHandler::note_author impl
pub(crate) fn set_author(round: u32, acc: u64, pts: u32) {
	<Points<Test>>::mutate(round, |p| *p += pts);
	<AwardedPts<Test>>::mutate(round, acc, |p| *p += pts);
}

pub type StakeCurrency = <Test as pallet::Config>::Currency;

#[test]
fn geneses() {
	ExtBuilder::default()
		.with_staking_tokens(vec![
			(999, 100, 0),
			(1, 1000, 1),
			(2, 300, 2),
			(3, 100, 1),
			(4, 100, 1),
			(5, 100, 2),
			(6, 100, 2),
			(7, 100, 3),
			(8, 9, 3),
			(9, 4, 3),
		])
		.with_candidates(vec![(1, 500, 1), (2, 200, 2)])
		.with_delegations(vec![(3, 1, 100), (4, 1, 100), (5, 2, 100), (6, 2, 100)])
		.build()
		.execute_with(|| {
			// collators
			assert_eq!(StakeCurrency::reserved_balance(1, &1), 500);
			assert_eq!(StakeCurrency::free_balance(1, &1), 500);
			assert!(Stake::is_candidate(&1));
			assert_eq!(StakeCurrency::reserved_balance(2, &2), 200);
			assert_eq!(StakeCurrency::free_balance(2, &2), 100);
			assert!(Stake::is_candidate(&2));
			// delegators
			for x in 3..5 {
				assert!(Stake::is_delegator(&x));
				assert_eq!(StakeCurrency::free_balance(1, &x), 0);
				assert_eq!(StakeCurrency::reserved_balance(1, &x), 100);
			}
			for x in 5..7 {
				assert!(Stake::is_delegator(&x));
				assert_eq!(StakeCurrency::free_balance(2, &x), 0);
				assert_eq!(StakeCurrency::reserved_balance(2, &x), 100);
			}
			// uninvolved
			for x in 7..10 {
				assert!(!Stake::is_delegator(&x));
			}
			assert_eq!(StakeCurrency::free_balance(3, &7), 100);
			assert_eq!(StakeCurrency::reserved_balance(3, &7), 0);
			assert_eq!(StakeCurrency::free_balance(3, &8), 9);
			assert_eq!(StakeCurrency::reserved_balance(3, &8), 0);
			assert_eq!(StakeCurrency::free_balance(3, &9), 4);
			assert_eq!(StakeCurrency::reserved_balance(3, &9), 0);
		});
	ExtBuilder::default()
		.with_staking_tokens(vec![
			(999, 100, 0),
			(1, 100, 1),
			(2, 100, 2),
			(3, 100, 1),
			(4, 100, 3),
			(5, 100, 3),
			(6, 100, 1),
			(7, 100, 1),
			(8, 100, 1),
			(8, 100, 2),
			(9, 100, 2),
			(10, 100, 1),
		])
		.with_candidates(vec![
			(1, 20, 1),
			(2, 20, 2),
			(3, 20, 1),
			(4, 20, 3),
			(5, 10, 3),
		])
		.with_delegations(vec![
			(6, 1, 10),
			(7, 1, 10),
			(8, 1, 10),
			(8, 2, 10),
			(9, 2, 10),
			(10, 1, 10),
		])
		.build()
		.execute_with(|| {
			// collators
			for x in [1, 3] {
				assert!(Stake::is_candidate(&x));
				assert_eq!(StakeCurrency::free_balance(1, &x), 80);
				assert_eq!(StakeCurrency::reserved_balance(1, &x), 20);
			}
			assert!(Stake::is_candidate(&2));
			assert_eq!(StakeCurrency::free_balance(2, &2), 80);
			assert_eq!(StakeCurrency::reserved_balance(2, &2), 20);
			for x in 4..5 {
				assert!(Stake::is_candidate(&x));
				assert_eq!(StakeCurrency::free_balance(3, &x), 80);
				assert_eq!(StakeCurrency::reserved_balance(3, &x), 20);
			}
			assert!(Stake::is_candidate(&5));
			assert_eq!(StakeCurrency::free_balance(3, &5), 90);
			assert_eq!(StakeCurrency::reserved_balance(3, &5), 10);
			// delegators
			for x in [6, 7, 8, 10] {
				assert!(Stake::is_delegator(&x));
				assert_eq!(StakeCurrency::free_balance(1, &x), 90);
				assert_eq!(StakeCurrency::reserved_balance(1, &x), 10);
			}
			for x in [8, 9] {
				assert!(Stake::is_delegator(&x));
				assert_eq!(StakeCurrency::free_balance(2, &x), 90);
				assert_eq!(StakeCurrency::reserved_balance(2, &x), 10);
			}
		});
}
