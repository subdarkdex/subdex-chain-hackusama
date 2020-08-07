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
        let token_amount = self.token_pool - new_token_pool;
        (new_ksm_pool, new_token_pool, token_amount)
    }

    pub fn calculate_to_token_ksm_swap(
        &self,
        token_amount: BalanceOf<T>,
    ) -> (BalanceOf<T>, BalanceOf<T>, BalanceOf<T>) {
        let fee = token_amount * self.fee_rate / FEE_RATE_DENOMINATOR.into();
        let new_token_pool = self.token_pool + token_amount;
        let temp_token_pool = new_token_pool - fee;
        let new_ksm_pool = self.invariant / temp_token_pool;
        let ksm_amount = self.ksm_pool - new_ksm_pool;
        (new_ksm_pool, new_token_pool, ksm_amount)
    }

    pub fn calculate_share_price(&self, shares: BalanceOf<T>) -> (BalanceOf<T>, BalanceOf<T>) {
        let ksm_per_share = self.ksm_pool / self.total_shares;
        let ksm_cost = ksm_per_share * shares;
        let token_per_share = self.token_pool / self.total_shares;
        let token_cost = token_per_share * shares;
        (ksm_cost, token_cost)
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

    pub fn ensure_token_amount(
        &self,
        token_out_amount: BalanceOf<T>,
        min_token_out_amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            token_out_amount >= min_token_out_amount,
            Error::<T>::TokenAmountBelowExpectation
        );
        ensure!(
            token_out_amount <= self.token_pool,
            Error::<T>::InsufficientPool
        );
        Ok(())
    }

    pub fn ensure_burned_shares(
        &self,
        sender: T::AccountId,
        shares_burned: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            shares_burned > BalanceOf::<T>::zero(),
            Error::<T>::InvalidShares
        );
        if let Some(shares) = self.shares.get(&sender) {
            ensure!(*shares >= shares_burned, Error::<T>::InsufficientShares);
            Ok(())
        } else {
            Err(Error::<T>::DoesNotOwnShare.into())
        }
    }

    pub fn ensure_ksm_amount(
        &self,
        ksm_out_amount: BalanceOf<T>,
        min_ksm_out_amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            ksm_out_amount >= min_ksm_out_amount,
            Error::<T>::KsmAmountBelowExpectation
        );
        ensure!(
            ksm_out_amount <= self.ksm_pool,
            Error::<T>::InsufficientPool
        );
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
        Exchanged(AssetId, Balance, AssetId, Balance, AccountId),
        Invested(AccountId, AssetId, Shares),
        Divested(AccountId, AssetId, Shares),
        Withdrawn(AssetId, Balance, AccountId),
    }
);

decl_error! {
    pub enum Error for Module<T: Trait> {
        ExchangeNotExists,
        ExchangeAlreadyExists,
        InvalidExchange,
        InvariantNotNull,
        TotalSharesNotNull,
        LowKsmAmount,
        LowTokenAmount,
        KsmAmountBelowExpectation,
        TokenAmountBelowExpectation,
        InsufficientPool,
        InvalidShares,
        InsufficientShares,
        DoesNotOwnShare,
        InsufficientKsmBalance,
        InsufficientOtherAssetBalance
    }
}

decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {

        type Error = Error<T>;

        fn deposit_event() = default;

        #[weight = 10_000]
        pub fn initialize_exchange(origin, ksm_amount: BalanceOf<T>, token: T::AssetId, token_amount: BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            Self::ensure_exchange_not_exists(token)?;
            Self::exchanges(token).ensure_launch(ksm_amount, token_amount)?;
            Self::ensure_sufficient_balances(&sender, &T::KSMAssetId::get(), ksm_amount, &token, token_amount)?;

            //
            // == MUTATION SAFE ==
            //

            // transfer KSM to the DEX account
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &sender, &T::DEXAccountId::get(), ksm_amount)?;
            // transfer token to the DEX account
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &sender, &T::DEXAccountId::get(), token_amount)?;

            let exchange = Exchange::<T>::initialize_new(ksm_amount, token_amount, sender.clone());

            Exchanges::<T>::insert(token, exchange);

            Self::deposit_event(RawEvent::Invested(sender, token, T::InitialShares::get()));
            Ok(())
        }

        #[weight = 10_000]
        pub fn swap(origin, token_in: T::AssetId, token_in_amount: BalanceOf<T>, token_out: T::AssetId,  min_token_out_amount : BalanceOf<T>, receiver : T::AccountId) {
            let sender = ensure_signed(origin)?;

            Self::ensure_valid_exchange(token_in, token_out)?;

            if token_in == T::KSMAssetId::get() {
                Self::ksm_to_token_swap(sender, token_in_amount, token_out, min_token_out_amount, receiver)?;
            } else if token_out == T::KSMAssetId::get() {
                Self::token_to_ksm_swap(sender, token_in, token_in_amount, min_token_out_amount, receiver)?;
            } else {
                Self::token_to_token_swap(sender, token_in, token_in_amount, token_out, min_token_out_amount, receiver)?;
            }
        }

        #[weight = 10_000]
        pub fn invest_liquidity(origin, token: T::AssetId, shares: BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            let (ksm_cost, token_cost) = Self::ensure_exchange_exists(token)?.calculate_share_price(shares);
            Self::ensure_sufficient_balances(&sender, &T::KSMAssetId::get(), ksm_cost, &token, token_cost)?;

            //
            // == MUTATION SAFE ==
            //

            // transfer KSM to the DEX account
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &sender, &T::DEXAccountId::get(), ksm_cost)?;
            // transfer token to the DEX account
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &sender, &T::DEXAccountId::get(), token_cost)?;

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.invest(ksm_cost, token_cost, shares, sender.clone())
            });

            Self::deposit_event(RawEvent::Invested(sender, token, shares));
            Ok(())
        }

        #[weight = 10_000]
        pub fn divest_liquidity(origin, token: T::AssetId, shares_burned:  BalanceOf<T>, min_ksm_received : BalanceOf<T>, min_token_received : BalanceOf<T>) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;

            let exchange = Self::ensure_exchange_exists(token)?;
            exchange.ensure_burned_shares(sender.clone(), shares_burned)?;
            let (ksm_cost, token_cost) = exchange.calculate_share_price(shares_burned);
            Self::ensure_divest_expectations(ksm_cost, token_cost, min_ksm_received, min_token_received)?;
            Self::ensure_sufficient_balances(&T::DEXAccountId::get(), &T::KSMAssetId::get(), ksm_cost, &token, token_cost)?;

            //
            // == MUTATION SAFE ==
            //

            // transfer KSM to sender
            <generic_asset::Module<T>>::make_transfer_with_event(&T::KSMAssetId::get(), &T::DEXAccountId::get(), &sender, ksm_cost)?;
            // transfer token to sender
            <generic_asset::Module<T>>::make_transfer_with_event(&token, &T::DEXAccountId::get(), &sender, token_cost)?;

            <Exchanges<T>>::mutate(token, |exchange| {
                exchange.divest(ksm_cost, token_cost, shares_burned, sender.clone())
            });

            Self::deposit_event(RawEvent::Divested(sender, token, shares_burned));
            Ok(())
        }
    }
}

impl<T: Trait> Module<T> {
    pub fn ensure_valid_exchange(
        token_in: T::AssetId,
        token_out: T::AssetId,
    ) -> dispatch::DispatchResult {
        ensure!(token_in != token_out, Error::<T>::InvalidExchange);
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
        sender: &T::AccountId,
        token_in: &T::AssetId,
        token_in_amount: BalanceOf<T>,
        token_out: &T::AssetId,
        token_out_amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        Self::ensure_sufficient_balance(sender, token_in, token_in_amount)?;
        Self::ensure_sufficient_balance(sender, token_out, token_out_amount)?;
        Ok(())
    }

    pub fn ensure_sufficient_balance(
        from: &T::AccountId,
        asset_id: &T::AssetId,
        amount: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        let mut error = Error::<T>::InsufficientOtherAssetBalance;
        if &T::KSMAssetId::get() == asset_id {
            error = Error::<T>::InsufficientKsmBalance;
        }
        let new_balance = <generic_asset::Module<T>>::free_balance(asset_id, from)
            .checked_sub(&amount)
            .ok_or(error)?;
        <generic_asset::Module<T>>::ensure_can_withdraw(
            asset_id,
            from,
            amount,
            WithdrawReason::Transfer.into(),
            new_balance,
        )?;
        Ok(())
    }

    pub fn ensure_divest_expectations(
        ksm_cost: BalanceOf<T>,
        tokens_cost: BalanceOf<T>,
        min_ksm_received: BalanceOf<T>,
        min_token_received: BalanceOf<T>,
    ) -> dispatch::DispatchResult {
        ensure!(
            ksm_cost >= min_ksm_received,
            Error::<T>::KsmAmountBelowExpectation
        );
        ensure!(
            tokens_cost >= min_token_received,
            Error::<T>::TokenAmountBelowExpectation
        );
        Ok(())
    }

    pub fn ksm_to_token_swap(
        sender: T::AccountId,
        ksm_in_amount: BalanceOf<T>,
        token_out: T::AssetId,
        min_token_out_amount: BalanceOf<T>,
        receiver: T::AccountId,
    ) -> dispatch::DispatchResult {
        let exchange = Self::ensure_exchange_exists(token_out)?;
        let (new_ksm_pool, new_token_pool, token_out_amount) =
            exchange.calculate_ksm_to_token_swap(ksm_in_amount);
        exchange.ensure_token_amount(token_out_amount, min_token_out_amount)?;
        Self::ensure_sufficient_balance(&sender, &T::KSMAssetId::get(), ksm_in_amount)?;
        Self::ensure_sufficient_balance(&T::DEXAccountId::get(), &token_out, token_out_amount)?;

        //
        // == MUTATION SAFE ==
        //

        // transfer KSM to the DEX account
        <generic_asset::Module<T>>::make_transfer_with_event(
            &T::KSMAssetId::get(),
            &sender,
            &T::DEXAccountId::get(),
            ksm_in_amount,
        )?;
        // transfer token to the receiver
        <generic_asset::Module<T>>::make_transfer_with_event(
            &token_out,
            &T::DEXAccountId::get(),
            &receiver,
            token_out_amount,
        )?;

        Exchanges::<T>::mutate(token_out, |exchange| {
            exchange.update_pools(new_ksm_pool, new_token_pool)
        });

        Self::deposit_event(RawEvent::Exchanged(
            T::KSMAssetId::get(),
            ksm_in_amount,
            token_out,
            token_out_amount,
            sender,
        ));
        Ok(())
    }

    pub fn token_to_ksm_swap(
        sender: T::AccountId,
        token_in: T::AssetId,
        token_in_amount: BalanceOf<T>,
        min_ksm_out_amount: BalanceOf<T>,
        receiver: T::AccountId,
    ) -> dispatch::DispatchResult {
        let exchange = Self::ensure_exchange_exists(token_in)?;
        let (new_ksm_pool, new_token_pool, ksm_out_amount) =
            exchange.calculate_to_token_ksm_swap(token_in_amount);
        exchange.ensure_ksm_amount(ksm_out_amount, min_ksm_out_amount)?;
        Self::ensure_sufficient_balance(&sender, &token_in, token_in_amount)?;
        Self::ensure_sufficient_balance(
            &T::DEXAccountId::get(),
            &T::KSMAssetId::get(),
            ksm_out_amount,
        )?;

        //
        // == MUTATION SAFE ==
        //

        // transfer token to the DEX account
        <generic_asset::Module<T>>::make_transfer_with_event(
            &token_in,
            &sender,
            &T::DEXAccountId::get(),
            token_in_amount,
        )?;
        // transfer KSM to the receiver
        <generic_asset::Module<T>>::make_transfer_with_event(
            &T::KSMAssetId::get(),
            &T::DEXAccountId::get(),
            &receiver,
            ksm_out_amount,
        )?;

        Exchanges::<T>::mutate(token_in, |exchange| {
            exchange.update_pools(new_ksm_pool, new_token_pool)
        });

        Self::deposit_event(RawEvent::Exchanged(
            token_in,
            token_in_amount,
            T::KSMAssetId::get(),
            ksm_out_amount,
            sender,
        ));
        Ok(())
    }

    pub fn token_to_token_swap(
        sender: T::AccountId,
        token_in: T::AssetId,
        token_in_amount: BalanceOf<T>,
        token_out: T::AssetId,
        min_token_out_amount: BalanceOf<T>,
        receiver: T::AccountId,
    ) -> dispatch::DispatchResult {
        let from_exchange = Self::ensure_exchange_exists(token_in)?;
        let to_exchange = Self::ensure_exchange_exists(token_out)?;

        let (new_ksm_pool_from, new_token_pool_from, ksm_amount) =
            from_exchange.calculate_to_token_ksm_swap(token_in_amount);
        from_exchange.ensure_ksm_amount(ksm_amount, BalanceOf::<T>::zero())?;

        let (new_ksm_pool_to, new_token_pool_to, token_out_amount) =
            to_exchange.calculate_ksm_to_token_swap(ksm_amount);
        to_exchange.ensure_token_amount(token_out_amount, min_token_out_amount)?;
        Self::ensure_sufficient_balance(&sender, &token_in, token_in_amount)?;
        Self::ensure_sufficient_balance(&T::DEXAccountId::get(), &token_out, token_out_amount)?;

        //
        // == MUTATION SAFE ==
        //

        // transfer `token_amount` to the DEX account
        <generic_asset::Module<T>>::make_transfer_with_event(
            &token_in,
            &sender,
            &T::DEXAccountId::get(),
            token_in_amount,
        )?;
        // transfer `tokens_out` to the receiver
        <generic_asset::Module<T>>::make_transfer_with_event(
            &token_out,
            &T::DEXAccountId::get(),
            &receiver,
            token_out_amount,
        )?;

        <Exchanges<T>>::mutate(token_in, |exchange| {
            exchange.update_pools(new_ksm_pool_from, new_token_pool_from)
        });
        <Exchanges<T>>::mutate(token_out, |exchange| {
            exchange.update_pools(new_ksm_pool_to, new_token_pool_to)
        });

        Self::deposit_event(RawEvent::Exchanged(
            token_in,
            token_in_amount,
            token_out,
            token_out_amount,
            sender,
        ));
        Ok(())
    }
}
