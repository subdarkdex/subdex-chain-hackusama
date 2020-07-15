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
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub SupportedTokens get(fn supported_tokens): Vec<TokenId>;
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
        InsufficientPool
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
            ensure!(!PairStructs::<T>::contains_key(token), Error::<T>::PairExist);

            let mut pair = TokensPair::<T>::default();
            ensure!(pair.invariant != 0 , Error::<T>::InvariantNotNull);
            ensure!(pair.total_shares != 0 , Error::<T>::TotalSharesNotNull);
            ensure!(ksm_amount > 0 , Error::<T>::LowKsmAmount);
            ensure!(token_amount > 0 , Error::<T>::LowTokenAmount);
            pair.ksm_pool = ksm_amount;
            pair.token_pool = token_amount;
            pair.invariant = token_amount * ksm_amount;
            let total_shares = 1000u128;
            pair.shares.insert(sender.clone(), total_shares);
            pair.invariant = total_shares;
            PairStructs::<T>::insert(token, pair);

            // transfer `ksm_amount` to our address
            // transfer `token_amount` to our address

            // event
            Self::deposit_event(RawEvent::Invested(sender, total_shares));
            Ok(())
        }

        #[weight = 10_000]
        pub fn ksm_to_token_swap(origin, token: TokenId, ksm_amount : TAmount,  min_tokens_received: TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let sender = ensure_signed(origin)?;
            ensure!(PairStructs::<T>::contains_key(token), Error::<T>::PairNotExist);
            let mut pair = PairStructs::<T>::get(token);

            let fee = ksm_amount / pair.fee_rate;
            pair.ksm_pool += ksm_amount;
            let temp_ksm_pool = pair.ksm_pool - fee;
            let new_token_pool = pair.invariant / temp_ksm_pool;
            let tokens_out = pair.token_pool - new_token_pool;

            ensure!(tokens_out >= min_tokens_received, Error::<T>::LowAmountOut);
            ensure!(tokens_out <= pair.token_pool, Error::<T>::InsufficientPool);
            pair.token_pool = new_token_pool;
            pair.invariant = pair.token_pool * pair.ksm_pool;

            // transfer `ksm_amount` to our address
            // transfer `token_amount` to receiver

            Self::deposit_event(RawEvent::Exchanged(KSM_ACCOUNT_ID, token, ksm_amount, sender));
            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_ksm_swap(origin, token: TokenId, token_amount: TAmount,min_ksm_received : TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let who = ensure_signed(origin)?;

            Ok(())
        }

        #[weight = 10_000]
        pub fn token_to_token_swap(origin, token_from: TokenId, token_to: TokenId, token_amount: TAmount, min_token_received : TAmount, receiver : T::AccountId) -> dispatch::DispatchResult {
            let who = ensure_signed(origin)?;

            Ok(())
        }

        #[weight = 10_000]
        pub fn invest_liquidity(origin, token: TokenId, min_shares: TShares) -> dispatch::DispatchResult {
            let who = ensure_signed(origin)?;

            Ok(())
        }

        #[weight = 10_000]
        pub fn divest_liquidity(origin, token: TokenId,shares_burned: TShares, min_ksm_received : TAmount, min_token_received : TAmount) -> dispatch::DispatchResult {
            let who = ensure_signed(origin)?;

            Ok(())
        }
    }
}
