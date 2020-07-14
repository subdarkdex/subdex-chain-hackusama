#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{decl_error, decl_event, decl_module, decl_storage, dispatch};
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
            fee_rate: 0u128,
            ksm_pool: 0u128,
            token_pool: 0u128,
            invariant: 0u128,
            total_shares: 0u128,
            shares: BTreeMap::new(),
        }
    }
}
decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        pub SupportedTokens: Vec<TokenId>;
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
        /// Value was None
        NoneValue,
        /// Value reached maximum and cannot be incremented further
        StorageOverflow,
    }
}

// The pallet's dispatchable functions.
decl_module! {
    /// The module declaration.
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        type Error = Error<T>;

        // Initializing events
        // this is needed only if you are using events in your pallet
        fn deposit_event() = default;

        /// Just a dummy entry point.
        /// function that can be called by the external world as an extrinsics call
        /// takes a parameter of the type `AccountId`, stores it, and emits an event
        #[weight = 10_000]
        pub fn do_something(origin, something: u32) -> dispatch::DispatchResult {
            let who = ensure_signed(origin)?;

            Ok(())
        }
    }
}
