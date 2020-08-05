#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{
    decl_error, decl_event, decl_module, decl_storage, dispatch, ensure,
    traits::{Get, WithdrawReason},
};
use frame_system::{self as system, ensure_signed};
use sp_runtime::traits::{CheckedSub, Zero};
use sp_std::{collections::btree_map::BTreeMap, fmt::Debug, prelude::*};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
pub use serde::{Deserialize, Serialize};

pub type AssetIdOf<T> = <T as generic_asset::Trait>::AssetId;

type BalanceOf<T> = <T as generic_asset::Trait>::Balance;

pub const FEE_RATE_DENOMINATOR: u32 = 1000;

pub trait Trait: system::Trait + generic_asset::Trait {
    type Event: From<Event<Self>>
        + Into<<Self as system::Trait>::Event>
        + Into<<Self as generic_asset::Trait>::Event>;

    //type Currency: Currency<Self::AccountId>;

    type DEXAccountId: Get<<Self as system::Trait>::AccountId>;

    type KSMAssetId: Get<AssetIdOf<Self>>;

    type InitialShares: Get<BalanceOf<Self>>;

    type ExchangeFeeRate: Get<BalanceOf<Self>>;
}

#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, Debug)]
pub struct Exchange<T: Trait> {
    fee_rate: BalanceOf<T>,
    ksm_pool: BalanceOf<T>,
    token_pool: BalanceOf<T>,
    invariant: BalanceOf<T>,
    total_shares: BalanceOf<T>,
    shares: BTreeMap<T::AccountId, BalanceOf<T>>,
}

impl<T: Trait> Default for Exchange<T> {
    fn default() -> Self {
        Self {
            fee_rate: BalanceOf::<T>::default(),
            ksm_pool: BalanceOf::<T>::default(),
            token_pool: BalanceOf::<T>::default(),
            invariant: BalanceOf::<T>::default(),
            total_shares: BalanceOf::<T>::default(),
            shares: BTreeMap::new(),
        }
    }
}

impl<T: Trait> Exchange<T> {
    pub fn initialize_new(
        ksm_amount: BalanceOf<T>,
        token_amount: BalanceOf<T>,
        sender: T::AccountId,
    ) -> Self {
        let mut shares_map = BTreeMap::new();
        shares_map.insert(sender, T::InitialShares::get());
        Self {
            fee_rate: T::ExchangeFeeRate::get(),
            ksm_pool: ksm_amount,
            token_pool: token_amount,
            invariant: ksm_amount * token_amount,
            total_shares: T::InitialShares::get(),
            shares: shares_map,
        }
    }

    pub fn calculate_ksm_to_token_swap(
        &self,
        ksm_amount: BalanceOf<T>,
    ) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
        let fee = ksm_amount * self.fee_rate / FEE_RATE_DENOMINATOR.into();
        let new_ksm_pool = self.ksm_pool + ksm_amount;
        let temp_ksm_pool = new_ksm_pool - fee;
        let new_token_pool = self.invariant / temp_ksm_pool;
        let tokens_out = self.token_pool - new_token_pool;
        (new_ksm_pool, new_token_pool, tokens_out)
    }

    pub fn calculate_token_to_ksm_swap(
        &self,
        token_amount: BalanceOf<T>,
    ) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
        let fee = token_amount * self.fee_rate / FEE_RATE_DENOMINATOR.into();
        let new_token_pool = self.token_pool + token_amount;
        let temp_token_pool = new_token_pool - fee;
        let new_ksm_pool = self.invariant / temp_token_pool;
        let ksm_out = self.ksm_pool - new_ksm_pool;
        (new_ksm_pool, new_token_pool, ksm_out)
    }

    pub fn calculate_share_price(&self, shares: BalanceOf<T>) -> (BalanceOf<T>, BalanceOf<T>) {
        let ksm_per_share = self.ksm_pool / self.total_shares;
        let ksm_cost = ksm_per_share * shares;
        let tokens_per_share = self.token_pool / self.total_shares;
        let tokens_cost = tokens_per_share * shares;
        (ksm_cost, tokens_cost)
    }

    pub fn invest(
        &mut self,
        ksm_amount: BalanceOf<T>,
        token_amount: BalanceOf<T>,
        shares: BalanceOf<T>,
        sender: T::AccountId,
    ) {
        let updated_shares = if let Some(prev_shares) = self.shares.get(&sender) {
            *prev_shares + shares
        } else {
            shares
        };
        self.shares.insert(sender, updated_shares);
        self.total_shares += shares;
        self.ksm_pool += ksm_amount;
        self.token_pool += token_amount;
        self.invariant = self.ksm_pool * self.token_pool;
    }

    pub fn divest(
        &mut self,
        ksm_amount: BalanceOf<T>,
        token_amount: BalanceOf<T>,
        shares: BalanceOf<T>,
        sender: T::AccountId,
    ) {
        if let Some(share) = self.shares.get_mut(&sender) {
            *share -= shares;
        }

        self.total_shares -= shares;
        self.ksm_pool -= ksm_amount;
        self.token_pool -= token_amount;
        if self.total_shares == BalanceOf::<T>::zero() {
            self.invariant = BalanceOf::<T>::zero();
        } else {
            self.invariant = self.ksm_pool * self.token_pool;
        }
    }

    pub fn update_pools(&mut self, ksm_pool: BalanceOf<T>, token_pool: BalanceOf<T>) {
        self.ksm_pool = ksm_pool;
        self.token_pool = token_pool;
        self.invariant = self.ksm_pool * self.token_pool;
    }

    pub fn ensure_launch(
        &self,
        ksm_amount: BalanceOf<T>,
        token_amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            ksm_amount > BalanceOf::<T>::zero(),
            Error::<T>::LowKsmAmount
        );
        ensure!(
            token_amount > BalanceOf::<T>::zero(),
            Error::<T>::LowTokenAmount
        );
        ensure!(
            self.invariant == BalanceOf::<T>::zero(),
            Error::<T>::InvariantNotNull
        );
        ensure!(
            self.total_shares == BalanceOf::<T>::zero(),
            Error::<T>::TotalSharesNotNull
        );
        Ok(())
    }

    pub fn ensure_tokens_out(
        &self,
        tokens_out: BalanceOf<T>,
        min_tokens_received: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(tokens_out >= min_tokens_received, Error::<T>::LowAmountOut);
        ensure!(tokens_out <= self.token_pool, Error::<T>::InsufficientPool);
        Ok(())
    }

    pub fn ensure_burned_shares(
        &self,
        sender: T::AccountId,
        shares_burned: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            shares_burned > BalanceOf::<T>::zero(),
            Error::<T>::LowShares
        );
        if let Some(shares) = self.shares.get(&sender) {
            ensure!(*shares >= shares_burned, Error::<T>::InsufficientShares);
            Ok(())
        } else {
            Err(Error::<T>::DoesNotOwnShare.into())
        }
    }

    pub fn ensure_ksm_out(
        &self,
        ksm_out: BalanceOf<T>,
        min_ksm_received: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(ksm_out >= min_ksm_received, Error::<T>::LowAmountOut);
        ensure!(ksm_out <= self.ksm_pool, Error::<T>::InsufficientPool);
        Ok(())
    }
}
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub Exchanges get(fn exchanges): map hasher(blake2_128_concat) T::AssetId => Exchange<T>;
    }
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as system::Trait>::AccountId,
        AssetId = AssetIdOf<T>,
        Shares = BalanceOf<T>,
        Balance = BalanceOf<T>,
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
        ExchangeNotExists,
        ExchangeAlreadyExists,
        InvalidExchange,
        InvariantNotNull,
        TotalSharesNotNull,
        LowKsmAmount,
        LowTokenAmount,
        LowAmountOut,
        InsufficientPool,
        LowShares,
        InsufficientShares,
        DoesNotOwnShare,
        InsufficientKsmBalance,
        InsufficientOtherAssetBalance
    }
}

impl<T: Trait> Module<T> {
    pub fn ensure_valid_exchange(
        token_from: T::AssetId,
        token_to: T::AssetId,
    ) -> dispatch::DispatchResult {
        ensure!(
            token_from == T::KSMAssetId::get(),
            Error::<T>::InvalidExchange
        );
        ensure!(token_from != token_to, Error::<T>::InvalidExchange);
        Ok(())
    }

    pub fn ensure_exchange_exists(token: T::AssetId) -> Result<Exchange<T>, Error<T>> {
        ensure!(
            Exchanges::<T>::contains_key(token),
            Error::<T>::ExchangeNotExists
        );
        Ok(Self::exchanges(token))
    }

    pub fn ensure_exchange_not_exists(token: T::AssetId) -> dispatch::DispatchResult {
        ensure!(
            !Exchanges::<T>::contains_key(token),
            Error::<T>::ExchangeAlreadyExists
        );
        Ok(())
    }

    pub fn ensure_sufficient_balances(
        from: &T::AccountId,
        ksm_amount: BalanceOf<T>,
        token_asset_id: &T::AssetId,
        token_amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        let new_ksm_balance = <generic_asset::Module<T>>::free_balance(&T::KSMAssetId::get(), from)
            .checked_sub(&ksm_amount)
            .ok_or(Error::<T>::InsufficientKsmBalance)?;
        <generic_asset::Module<T>>::ensure_can_withdraw(
            &T::KSMAssetId::get(),
            from,
            ksm_amount,
            WithdrawReason::Transfer.into(),
            new_ksm_balance,
        )?;
        let new_token_balance = <generic_asset::Module<T>>::free_balance(token_asset_id, from)
            .checked_sub(&token_amount)
            .ok_or(Error::<T>::InsufficientOtherAssetBalance)?;
        <generic_asset::Module<T>>::ensure_can_withdraw(
            &T::KSMAssetId::get(),
            from,
            token_amount,
            WithdrawReason::Transfer.into(),
            new_token_balance,
        )?;
        Ok(())
    }

    pub fn ensure_divest_expectations(
        ksm_cost: BalanceOf<T>,
        tokens_cost: BalanceOf<T>,
        min_ksm_received: BalanceOf<T>,
        min_token_received: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(ksm_cost >= min_ksm_received, Error::<T>::LowAmountOut);
        ensure!(tokens_cost >= min_token_received, Error::<T>::LowAmountOut);
        Ok(())
    }
}
// The pallet's dispatchable functions.
decl_module! {
    /// The module declaration.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {

        type Error = Error<T>;

        fn deposit_event() = default;

        #[weight = 10_000]
        pub fn initialize_exchange(origin, ksm_amount: BalanceOf<T>, token: T::AssetId, token_amount: BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            Self::ensure_exchange_not_exists(token)?;
            Self::exchanges(token).ensure_launch(ksm_amount, token_amount)?;
            Self::ensure_sufficient_balances(&sender, ksm_amount, &token, token_amount)?;

            // transfer `ksm_amount` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &sender, &T::DEXAccountId::get(), ksm_amount)?;

            // transfer `token_amount` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &sender, &T::DEXAccountId::get(), token_amount)?;

            //
            // == MUTATION SAFE ==
            //
            let exchange = Exchange::<T>::initialize_new(ksm_amount, token_amount, sender.clone());

            Exchanges::<T>::insert(token, exchange);

            Self::deposit_event(RawEvent::Invested(sender, T::InitialShares::get()));
            Ok(())
        }

        #[weight = 10_000]
        pub fn ksm_to_token_swap(origin, token: T::AssetId, ksm_amount: BalanceOf<T>,  min_tokens_received: BalanceOf<T>, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let exchange = Self::ensure_exchange_exists(token)?;

            let (new_ksm_pool, new_token_pool, tokens_out) = exchange.calculate_ksm_to_token_swap(ksm_amount);
            exchange.ensure_tokens_out(tokens_out, min_tokens_received)?;

            //
            // == MUTATION SAFE ==
            //

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `ksm_amount` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &sender, &T::DEXAccountId::get(), tokens_out)?;

            // transfer `token_amount` to receiver
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &T::DEXAccountId::get(), &sender, tokens_out)?;

            // Self::deposit_event(RawEvent::Exchanged(KSM_ACCOUNT_ID, token, ksm_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_ksm_swap(origin, token: T::AssetId, token_amount: BalanceOf<T>, min_ksm_received : BalanceOf<T>, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let exchange = Self::ensure_exchange_exists(token)?;

            let (new_ksm_pool, new_token_pool, ksm_out) = exchange.calculate_token_to_ksm_swap(token_amount);
            exchange.ensure_ksm_out(ksm_out, min_ksm_received)?;

            //
            // == MUTATION SAFE ==
            //

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `token_amount` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &sender, &T::DEXAccountId::get(), token_amount)?;

            // transfer `ksm_out` to receiver
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &T::DEXAccountId::get(), &sender, token_amount)?;

            // Self::deposit_event(RawEvent::Exchanged(token, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_token_swap(origin, token_from: T::AssetId, token_to: T::AssetId, token_amount: BalanceOf<T>, min_tokens_received : BalanceOf<T>, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            Self::ensure_valid_exchange(token_from,token_to)?;
            let pair_from = Self::ensure_exchange_exists(token_from)?;
            let pair_to = Self::ensure_exchange_exists(token_to)?;

            let (new_ksm_pool_from, new_token_pool_from, ksm_out) = pair_from.calculate_token_to_ksm_swap(token_amount);
            pair_from.ensure_ksm_out(ksm_out, BalanceOf::<T>::zero())?;

            let (new_ksm_pool_to, new_token_pool_to, tokens_out) = pair_to.calculate_ksm_to_token_swap(ksm_out);
            pair_to.ensure_tokens_out(tokens_out, min_tokens_received)?;

            //
            // == MUTATION SAFE ==
            //

            <Exchanges<T>>::mutate(token_from, |exchange| {
                exchange.update_pools(new_ksm_pool_from, new_token_pool_from)
            });
            <Exchanges<T>>::mutate(token_to, |exchange| {
                exchange.update_pools(new_ksm_pool_to, new_token_pool_to)
            });

            // transfer `token_amount` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&token_from, &sender, &T::DEXAccountId::get(), token_amount)?;

            // transfer `tokens_out` to receiver
            <generic_asset::Module<T>>::make_transfer_with_event(&token_to, &T::DEXAccountId::get(), &sender, tokens_out)?;

            // Self::deposit_event(RawEvent::Exchanged(token_from, token_to, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn invest_liquidity(origin, token: T::AssetId, shares: BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            let (ksm_cost, tokens_cost) = Self::ensure_exchange_exists(token)?.calculate_share_price(shares);

            //
            // == MUTATION SAFE ==
            //

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.invest(ksm_cost, tokens_cost, shares, sender.clone())
            });

            // transfer `ksm_cost` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &sender, &T::DEXAccountId::get(), ksm_cost)?;

            // transfer `tokens_cost` to our address
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &sender, &T::DEXAccountId::get(), tokens_cost)?;

            Self::deposit_event(RawEvent::Invested(sender, shares));
            Ok(())
        }

        #[weight = 10_000]
        pub fn divest_liquidity(origin, token: T::AssetId, shares_burned:  BalanceOf<T>, min_ksm_received : BalanceOf<T>, min_token_received : BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            let exchange = Self::ensure_exchange_exists(token)?;

            exchange.ensure_burned_shares(sender.clone(), shares_burned)?;

            let (ksm_cost, tokens_cost) = exchange.calculate_share_price(shares_burned);

            Self::ensure_divest_expectations(ksm_cost, tokens_cost, min_ksm_received, min_token_received)?;

            //
            // == MUTATION SAFE ==
            //

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.divest(ksm_cost, tokens_cost, shares_burned, sender.clone())
            });

            // transfer `ksm_cost` to sender
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &T::DEXAccountId::get(), &sender, ksm_cost)?;

            // transfer `tokens_cost` to sender
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &T::DEXAccountId::get(), &sender, tokens_cost)?;


            Self::deposit_event(RawEvent::Divested(sender, shares_burned));
            Ok(())
        }
    }
}
