#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};
use frame_support::{
    decl_error, decl_event, decl_module, decl_storage, dispatch, ensure, traits::Get, Parameter,
};
use frame_system::{self as system, ensure_signed};
use sp_runtime::traits::{AtLeast32BitUnsigned, MaybeSerializeDeserialize, Member, Zero};
use sp_std::{collections::btree_map::BTreeMap, fmt::Debug, prelude::*};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
pub use serde::{Deserialize, Serialize};

pub trait Trait: system::Trait + assets::Trait + balances::Trait {
    type Event: From<Event<Self>>
        + Into<<Self as system::Trait>::Event>
        + Into<<Self as assets::Trait>::Event>
        + Into<<Self as balances::Trait>::Event>;

    type DEXAccountId: Get<<Self as system::Trait>::AccountId>;

    type InitialShares: Get<Self::Shares>;

    type DexBalance: From<<Self as balances::Trait>::Balance>
        + From<<Self as assets::Trait>::Balance>
        + Into<<Self as balances::Trait>::Balance>
        + Into<<Self as assets::Trait>::Balance>
        + Parameter
        + Member
        + AtLeast32BitUnsigned
        + Codec
        + Default
        + Copy
        + MaybeSerializeDeserialize
        + Debug
        + Zero;

    type FeeRate: From<Self::DexBalance>
        + Into<Self::DexBalance>
        + Parameter
        + Member
        + AtLeast32BitUnsigned
        + Codec
        + Default
        + Copy
        + MaybeSerializeDeserialize
        + Debug
        + Zero;

    type Shares: From<Self::DexBalance>
        + Into<Self::DexBalance>
        + Parameter
        + Member
        + AtLeast32BitUnsigned
        + Codec
        + Default
        + Copy
        + MaybeSerializeDeserialize
        + Debug
        + Zero;
}

#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, Debug)]
pub struct TokensPair<T: Trait> {
    fee_rate: T::FeeRate,
    ksm_pool: T::DexBalance,
    token_pool: T::DexBalance,
    invariant: T::DexBalance,
    total_shares: T::Shares,
    shares: BTreeMap<T::AccountId, T::Shares>,
}

impl<T: Trait> Default for TokensPair<T> {
    fn default() -> Self {
        Self {
            fee_rate: T::FeeRate::default(),
            ksm_pool: T::DexBalance::default(),
            token_pool: T::DexBalance::default(),
            invariant: T::DexBalance::default(),
            total_shares: T::Shares::default(),
            shares: BTreeMap::new(),
        }
    }
}

impl<T: Trait> TokensPair<T> {
    pub fn initialize_new(
        ksm_amount: T::DexBalance,
        token_amount: T::DexBalance,
        sender: T::AccountId,
    ) -> Self {
        let mut shares_map = BTreeMap::new();
        shares_map.insert(sender, T::InitialShares::get());
        Self {
            fee_rate: T::FeeRate::default(),
            ksm_pool: ksm_amount,
            token_pool: token_amount,
            invariant: ksm_amount * token_amount,
            total_shares: T::InitialShares::get(),
            shares: shares_map,
        }
    }

    pub fn calculate_ksm_to_token_swap(
        &self,
        ksm_amount: T::DexBalance,
    ) -> (T::DexBalance, T::DexBalance, T::DexBalance) {
        let fee = ksm_amount / self.fee_rate.into();
        let new_ksm_pool = self.ksm_pool + ksm_amount;
        let temp_ksm_pool = new_ksm_pool - fee;
        let new_token_pool = self.invariant / temp_ksm_pool;
        let tokens_out = self.token_pool - new_token_pool;
        (new_ksm_pool, new_token_pool, tokens_out)
    }

    pub fn calculate_token_to_ksm_swap(
        &self,
        token_amount: T::DexBalance,
    ) -> (T::DexBalance, T::DexBalance, T::DexBalance) {
        let fee = token_amount / self.fee_rate.into();
        let new_token_pool = self.token_pool + token_amount;
        let temp_token_pool = new_token_pool - fee;
        let new_ksm_pool = self.invariant / temp_token_pool;
        let ksm_out = self.ksm_pool - new_ksm_pool;
        (new_ksm_pool, new_token_pool, ksm_out)
    }

    pub fn calculate_share_price(&self, shares: T::Shares) -> (T::DexBalance, T::DexBalance) {
        let ksm_per_share = self.ksm_pool / self.total_shares.into();
        let ksm_cost = ksm_per_share * shares.into();
        let tokens_per_share = self.token_pool / self.total_shares.into();
        let tokens_cost = tokens_per_share * shares.into();
        (ksm_cost, tokens_cost)
    }

    pub fn invest(
        &mut self,
        ksm_amount: T::DexBalance,
        token_amount: T::DexBalance,
        shares: T::Shares,
        sender: T::AccountId,
    ) {
        let updated_shares = if let Some(prev_shares) = self.shares.get(&sender) {
            *prev_shares + shares
        } else {
            shares
        };
        self.shares.insert(sender.clone(), updated_shares);
        self.total_shares += shares;
        self.ksm_pool += ksm_amount;
        self.token_pool += token_amount;
        self.invariant = self.ksm_pool * self.token_pool;
    }

    pub fn divest(
        &mut self,
        ksm_amount: T::DexBalance,
        token_amount: T::DexBalance,
        shares: T::Shares,
        sender: T::AccountId,
    ) {
        if let Some(share) = self.shares.get_mut(&sender) {
            *share -= shares;
        }

        self.total_shares -= shares;
        self.ksm_pool -= ksm_amount;
        self.token_pool -= token_amount;
        if self.total_shares == T::Shares::zero() {
            self.invariant = T::DexBalance::zero();
        } else {
            self.invariant = self.ksm_pool * self.token_pool;
        }
    }

    pub fn update_pools(&mut self, ksm_pool: T::DexBalance, token_pool: T::DexBalance) {
        self.ksm_pool = ksm_pool;
        self.token_pool = token_pool;
        self.invariant = self.ksm_pool * self.token_pool;
    }

    pub fn ensure_launch(
        &self,
        ksm_amount: T::DexBalance,
        token_amount: T::DexBalance,
    ) -> dispatch::DispatchResult {
        ensure!(
            self.invariant == T::DexBalance::zero(),
            Error::<T>::InvariantNotNull
        );
        ensure!(
            self.total_shares == T::Shares::zero(),
            Error::<T>::TotalSharesNotNull
        );
        ensure!(ksm_amount > T::DexBalance::zero(), Error::<T>::LowKsmAmount);
        ensure!(
            token_amount > T::DexBalance::zero(),
            Error::<T>::LowTokenAmount
        );
        Ok(())
    }

    pub fn ensure_tokens_out(
        &self,
        tokens_out: T::DexBalance,
        min_tokens_received: T::DexBalance,
    ) -> dispatch::DispatchResult {
        ensure!(tokens_out >= min_tokens_received, Error::<T>::LowAmountOut);
        ensure!(tokens_out <= self.token_pool, Error::<T>::InsufficientPool);
        Ok(())
    }

    pub fn ensure_burned_shares(
        &self,
        sender: T::AccountId,
        shares_burned: T::Shares,
    ) -> dispatch::DispatchResult {
        ensure!(shares_burned > T::Shares::zero(), Error::<T>::LowShares);
        if let Some(shares) = self.shares.get(&sender) {
            ensure!(*shares >= shares_burned, Error::<T>::InsufficientShares);
            Ok(())
        } else {
            Err(Error::<T>::DoesNotOwnShare.into())
        }
    }

    pub fn ensure_ksm_out(
        &self,
        ksm_out: T::DexBalance,
        min_ksm_received: T::DexBalance,
    ) -> dispatch::DispatchResult {
        ensure!(ksm_out >= min_ksm_received, Error::<T>::LowAmountOut);
        ensure!(ksm_out <= self.ksm_pool, Error::<T>::InsufficientPool);
        Ok(())
    }
}
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub PairStructs get(fn pair_structs): map hasher(blake2_128_concat) T::AssetId => TokensPair<T>;
    }
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as system::Trait>::AccountId,
        AssetId = <T as assets::Trait>::AssetId,
        Shares = <T as Trait>::Shares,
        Balance = <T as Trait>::DexBalance,
    {
        Exchanged(AssetId, AssetId, Balance, AccountId),
        Invested(AccountId, Shares),
        Divested(AccountId, Shares),
        Withdrawn(AssetId, Balance, AccountId),
    }
);

// The pallet's errors
decl_error! {
    pub enum Error for Module<T: Trait> {
        Initialized,
        PairNotExist,
        PairExist,
        InvariantNotNull,
        TotalSharesNotNull,
        LowKsmAmount,
        LowTokenAmount,
        LowAmountOut,
        InsufficientPool,
        ForbiddenPair,
        LowShares,
        InsufficientShares,
        DoesNotOwnShare
    }
}

impl<T: Trait> Module<T> {
    pub fn ensure_tokens_exchange(
        token_from: T::AssetId,
        token_to: T::AssetId,
    ) -> dispatch::DispatchResult {
        ensure!(token_from != token_to, Error::<T>::ForbiddenPair);
        Ok(())
    }
    pub fn ensure_divest_expectations(
        ksm_cost: T::DexBalance,
        tokens_cost: T::DexBalance,
        min_ksm_received: T::DexBalance,
        min_token_received: T::DexBalance,
    ) -> dispatch::DispatchResult {
        ensure!(ksm_cost >= min_ksm_received, Error::<T>::LowAmountOut);
        ensure!(tokens_cost >= min_token_received, Error::<T>::LowAmountOut);
        Ok(())
    }
    pub fn ensure_pair_exists(token: T::AssetId) -> Result<TokensPair<T>, Error<T>> {
        ensure!(
            PairStructs::<T>::contains_key(token),
            Error::<T>::PairNotExist
        );
        Ok(Self::pair_structs(token))
    }
}
// The pallet's dispatchable functions.
decl_module! {
    /// The module declaration.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {

        type Error = Error<T>;

        fn deposit_event() = default;

        #[weight = 10_000]
        pub fn initialize_exchange(origin, token: T::AssetId, ksm_amount: T::DexBalance,  token_amount: T::DexBalance) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin.clone())?;
            if PairStructs::<T>::contains_key(token) {
                let pair = Self::pair_structs(token);
                pair.ensure_launch(ksm_amount, token_amount)?;
            }

            let pair = TokensPair::<T>::initialize_new(ksm_amount, token_amount, sender.clone());
            PairStructs::<T>::insert(token, pair);

            // <balances::Module<T>>::transfer(origin, T::DEXAccountId::get().into(), ksm_amount.into());
            // <assets::Module<T>>::transfer(origin, token, T::DEXAccountId::get().into(), token_amount.into());

            // transfer `ksm_amount` to our address
            // transfer `token_amount` to our address

            Self::deposit_event(RawEvent::Invested(sender, T::InitialShares::get()));
            Ok(())
        }

        #[weight = 10_000]
        pub fn ksm_to_token_swap(origin, token: T::AssetId, ksm_amount: T::DexBalance,  min_tokens_received: T::DexBalance, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let pair = Self::ensure_pair_exists(token)?;


            let (new_ksm_pool, new_token_pool, tokens_out) = pair.calculate_ksm_to_token_swap(ksm_amount);
            pair.ensure_tokens_out(tokens_out, min_tokens_received)?;

            <PairStructs<T>>::mutate(token, |pair| {
                pair.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `ksm_amount` to our address
            // transfer `token_out` to receiver

            // Self::deposit_event(RawEvent::Exchanged(KSM_ACCOUNT_ID, token, ksm_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_ksm_swap(origin, token: T::AssetId, token_amount: T::DexBalance, min_ksm_received : T::DexBalance, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let pair = Self::ensure_pair_exists(token)?;

            let (new_ksm_pool, new_token_pool, ksm_out) = pair.calculate_token_to_ksm_swap(token_amount);
            pair.ensure_ksm_out(ksm_out, min_ksm_received)?;

            <PairStructs<T>>::mutate(token, |pair| {
                pair.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `token_amount` to our address
            // transfer `ksm_out` to receiver

            // Self::deposit_event(RawEvent::Exchanged(token, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_token_swap(origin, token_from: T::AssetId, token_to: T::AssetId, token_amount: T::DexBalance, min_tokens_received : T::DexBalance, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            Self::ensure_tokens_exchange(token_from,token_to)?;
            let pair_from = Self::ensure_pair_exists(token_from)?;
            let pair_to = Self::ensure_pair_exists(token_to)?;

            let (new_ksm_pool_from, new_token_pool_from, ksm_out) = pair_from.calculate_token_to_ksm_swap(token_amount);
            pair_from.ensure_ksm_out(ksm_out, T::DexBalance::zero())?;

            let (new_ksm_pool_to, new_token_pool_to, tokens_out) = pair_to.calculate_ksm_to_token_swap(ksm_out);
            pair_to.ensure_tokens_out(tokens_out, min_tokens_received)?;

            //
            // == MUTATION SAFE ==
            //

            <PairStructs<T>>::mutate(token_from, |pair| {
                pair.update_pools(new_ksm_pool_from, new_token_pool_from)
            });
            <PairStructs<T>>::mutate(token_to, |pair| {
                pair.update_pools(new_ksm_pool_to, new_token_pool_to)
            });

            // transfer `token_amount` to our address
            // transfer `tokens_out` to receiver

            // Self::deposit_event(RawEvent::Exchanged(token_from, token_to, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn invest_liquidity(origin, token: T::AssetId, shares: T::Shares) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            Self::ensure_pair_exists(token)?;

            //
            // == MUTATION SAFE ==
            //

            <PairStructs<T>>::mutate(token, |pair| {
                let (ksm_cost, tokens_cost) = pair.calculate_share_price(shares);
                pair.invest(ksm_cost, tokens_cost, shares, sender.clone())
            });

            // transfer `ksm_cost` to our address
            // transfer `tokens_cost` to our address

            Self::deposit_event(RawEvent::Invested(sender, shares));
            Ok(())
        }

        #[weight = 10_000]
        pub fn divest_liquidity(origin, token: T::AssetId, shares_burned:  T::Shares, min_ksm_received : T::DexBalance, min_token_received : T::DexBalance) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let pair = Self::ensure_pair_exists(token)?;

            pair.ensure_burned_shares(sender.clone(), shares_burned)?;

            let (ksm_cost, tokens_cost) = pair.calculate_share_price(shares_burned);

            Self::ensure_divest_expectations(ksm_cost, tokens_cost, min_ksm_received, min_token_received)?;

            //
            // == MUTATION SAFE ==
            //

            <PairStructs<T>>::mutate(token, |pair| {
                pair.divest(ksm_cost, tokens_cost, shares_burned, sender.clone())
            });

            // transfer `ksm_cost` to sender
            // transfer `tokens_cost` to sender

            Self::deposit_event(RawEvent::Divested(sender, shares_burned));
            Ok(())
        }
    }
}
