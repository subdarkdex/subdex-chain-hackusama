#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{decl_error, decl_event, decl_module, decl_storage, dispatch, ensure};
use frame_system::{self as system, ensure_signed};
use sp_std::vec::Vec;
use sp_std::{collections::btree_map::BTreeMap, prelude::*};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "std")]
pub use serde::{Deserialize, Serialize};

type TokenId = u128;
type TShares = u128;
type TAmount = u128;

const KSM_ACCOUNT_ID: TAmount = 0;
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, Debug)]
pub struct TokensPair<T: Trait> {
    fee_rate: u128,
    ksm_pool: TAmount,
    token_pool: TAmount,
    invariant: TAmount,
    total_shares: TShares,
    shares: BTreeMap<T::AccountId, TShares>,
}

pub trait Trait: system::Trait {
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}
impl<T: Trait> Default for TokensPair<T> {
    fn default() -> Self {
        Self {
            fee_rate: 0,
            ksm_pool: 0,
            token_pool: 0,
            invariant: 0,
            total_shares: 0,
            shares: BTreeMap::new(),
        }
    }
}

impl<T: Trait> TokensPair<T> {
    pub fn initialize_new(
        ksm_amount: TAmount,
        token_amount: TAmount,
        shares: TShares,
        sender: T::AccountId,
    ) -> Self {
        let mut shares_map = BTreeMap::new();
        shares_map.insert(sender.clone(), shares);
        Self {
            fee_rate: 333,
            ksm_pool: ksm_amount,
            token_pool: token_amount,
            invariant: ksm_amount * token_amount,
            total_shares: shares,
            shares: shares_map,
        }
    }

    pub fn calculate_ksm_to_token_swap(&self, ksm_amount: TAmount) -> (TAmount, TAmount, TAmount) {
        let fee = ksm_amount / self.fee_rate;
        let new_ksm_pool = self.ksm_pool + ksm_amount;
        let temp_ksm_pool = new_ksm_pool - fee;
        let new_token_pool = self.invariant / temp_ksm_pool;
        let tokens_out = self.token_pool - new_token_pool;
        (new_ksm_pool, new_token_pool, tokens_out)
    }

    pub fn calculate_token_to_ksm_swap(
        &self,
        token_amount: TAmount,
    ) -> (TAmount, TAmount, TAmount) {
        let fee = token_amount / self.fee_rate;
        let new_token_pool = self.token_pool + token_amount;
        let temp_token_pool = new_token_pool - fee;
        let new_ksm_pool = self.invariant / temp_token_pool;
        let ksm_out = self.ksm_pool - new_ksm_pool;
        (new_ksm_pool, new_token_pool, ksm_out)
    }

    pub fn calculate_share_price(&self, shares: TShares) -> (TAmount, TAmount) {
        let ksm_per_share = self.ksm_pool / self.total_shares;
        let ksm_cost = ksm_per_share * shares;
        let tokens_per_share = self.token_pool / self.total_shares;
        let tokens_cost = tokens_per_share * shares;
        (ksm_cost, tokens_cost)
    }

    pub fn invest(
        &mut self,
        ksm_amount: TAmount,
        token_amount: TAmount,
        shares: TShares,
        sender: T::AccountId,
    ) {
        let updated_shares = if let Some(prev_shares) = self.shares.get(&sender) {
            prev_shares + shares
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
        ksm_amount: TAmount,
        token_amount: TAmount,
        shares: TShares,
        sender: T::AccountId,
    ) {
        self.shares
            .insert(sender.clone(), self.shares.get(&sender).unwrap() - shares);
        self.total_shares -= shares;
        self.ksm_pool -= ksm_amount;
        self.token_pool -= token_amount;
        if self.total_shares == 0 {
            self.invariant = 0;
        } else {
            self.invariant = self.ksm_pool * self.token_pool;
        }
    }

    pub fn update_pools(&mut self, ksm_pool: TAmount, token_pool: TAmount) {
        self.ksm_pool = ksm_pool;
        self.token_pool = token_pool;
        self.invariant = self.ksm_pool * self.token_pool;
    }

    pub fn ensure_launch(
        &self,
        ksm_amount: TAmount,
        token_amount: TAmount,
    ) -> dispatch::DispatchResult {
        ensure!(self.invariant != 0, Error::<T>::InvariantNotNull);
        ensure!(self.total_shares != 0, Error::<T>::TotalSharesNotNull);
        ensure!(ksm_amount > 0, Error::<T>::LowKsmAmount);
        ensure!(token_amount > 0, Error::<T>::LowTokenAmount);
        Ok(())
    }

    pub fn ensure_tokens_out(
        &self,
        tokens_out: TAmount,
        min_tokens_received: TAmount,
    ) -> dispatch::DispatchResult {
        ensure!(tokens_out >= min_tokens_received, Error::<T>::LowAmountOut);
        ensure!(tokens_out <= self.token_pool, Error::<T>::InsufficientPool);
        Ok(())
    }

    pub fn ensure_ksm_out(
        &self,
        ksm_out: TAmount,
        min_ksm_received: TAmount,
    ) -> dispatch::DispatchResult {
        ensure!(ksm_out >= min_ksm_received, Error::<T>::LowAmountOut);
        ensure!(ksm_out <= self.ksm_pool, Error::<T>::InsufficientPool);
        Ok(())
    }

    pub fn ensure_pair_exists(token: TokenId) -> dispatch::DispatchResult {
        ensure!(
            PairStructs::<T>::contains_key(token),
            Error::<T>::PairNotExist
        );
        Ok(())
    }
}
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub PairStructs get(fn pair_structs): map hasher(blake2_128_concat) TokenId => TokensPair<T>;
    }
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as system::Trait>::AccountId,
    {
        Exchanged(TokenId, TokenId, TAmount, AccountId),
        Invested(AccountId, TShares),
        Divested(AccountId, TShares),
        Withdrawn(TokenId, TAmount, AccountId),
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
    }
}

// The pallet's dispatchable functions.
decl_module! {
    /// The module declaration.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        type Error = Error<T>;

        fn deposit_event() = default;

        #[weight = 10_000]
        pub fn initialize_exchange(origin, token: TokenId, ksm_amount : TAmount,  token_amount: TAmount) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            if PairStructs::<T>::contains_key(token) {
                let pair = Self::pair_structs(token);
                pair.ensure_launch(ksm_amount, token_amount)?;
            }

            let total_shares = 1000u128;
            let pair = TokensPair::<T>::initialize_new(ksm_amount, token_amount, total_shares, sender.clone());
            PairStructs::<T>::insert(token, pair);

            // transfer `ksm_amount` to our address
            // transfer `token_amount` to our address

            Self::deposit_event(RawEvent::Invested(sender, total_shares));
            Ok(())
        }

        #[weight = 10_000]
        pub fn ksm_to_token_swap(origin, token: TokenId, ksm_amount : TAmount,  min_tokens_received: TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            TokensPair::<T>::ensure_pair_exists(token)?;
            let pair = Self::pair_structs(token);

            let (new_ksm_pool, new_token_pool, tokens_out) = pair.calculate_ksm_to_token_swap(ksm_amount);
            pair.ensure_tokens_out(tokens_out, min_tokens_received)?;

            <PairStructs<T>>::mutate(token, |pair| {
                pair.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `ksm_amount` to our address
            // transfer `token_out` to receiver

            Self::deposit_event(RawEvent::Exchanged(KSM_ACCOUNT_ID, token, ksm_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_ksm_swap(origin, token: TokenId, token_amount: TAmount, min_ksm_received : TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            TokensPair::<T>::ensure_pair_exists(token)?;
            let pair = Self::pair_structs(token);

            let (new_ksm_pool, new_token_pool, ksm_out) = pair.calculate_token_to_ksm_swap(token_amount);
            pair.ensure_ksm_out(ksm_out, min_ksm_received)?;

            <PairStructs<T>>::mutate(token, |pair| {
                pair.update_pools(new_ksm_pool, new_token_pool)
            });

            // transfer `token_amount` to our address
            // transfer `ksm_out` to receiver

            Self::deposit_event(RawEvent::Exchanged(token, KSM_ACCOUNT_ID, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_token_swap(origin, token_from: TokenId, token_to: TokenId, token_amount: TAmount, min_tokens_received : TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            TokensPair::<T>::ensure_pair_exists(token_from)?;
            TokensPair::<T>::ensure_pair_exists(token_to)?;
            ensure!(token_from != token_to, Error::<T>::ForbiddenPair);
            let pair_from = Self::pair_structs(token_from);
            let pair_to = Self::pair_structs(token_to);

            let (new_ksm_pool_from, new_token_pool_from, ksm_out) = pair_from.calculate_token_to_ksm_swap(token_amount);
            pair_from.ensure_ksm_out(ksm_out, 0)?;

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

            Self::deposit_event(RawEvent::Exchanged(token_from, token_to, token_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn invest_liquidity(origin, token: TokenId, shares: TShares) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            TokensPair::<T>::ensure_pair_exists(token)?;

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
        pub fn divest_liquidity(origin, token: TokenId, shares_burned: TShares, min_ksm_received : TAmount, min_token_received : TAmount) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            ensure!(shares_burned > 0, Error::<T>::LowShares);
            TokensPair::<T>::ensure_pair_exists(token)?;
            let pair = Self::pair_structs(token);
            let (ksm_cost, tokens_cost) = pair.calculate_share_price(shares_burned);

            ensure!(ksm_cost >= min_ksm_received, Error::<T>::LowAmountOut);
            ensure!(tokens_cost >= min_token_received, Error::<T>::LowAmountOut);

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
