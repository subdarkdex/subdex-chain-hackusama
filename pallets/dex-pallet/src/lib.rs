#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{decl_error, decl_event, decl_module, decl_storage, dispatch};
use frame_system::{self as system, ensure_signed};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;
type TokenId = u128;
type TShares = u128;
pub trait Trait: system::Trait {
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_storage! {
    trait Store for Module<T: Trait> as TemplateModule {
        Something get(fn something): Option<u32>;
    }
}

decl_event!(
    pub enum Event<T>
    where
        AccountId = <T as system::Trait>::AccountId,
    {
        Exchanged(TokenId, TokenId, u128, AccountId),
        Invested(AccountId, TShares),
        Divested(AccountId, TShares),
        Withdrawn(TokenId, u128, AccountId),
    }
);

// // The pallet's errors
// decl_error! {
//     pub enum Error for Module<T: Trait> {
//         /// Value was None
//         NoneValue,
//         /// Value reached maximum and cannot be incremented further
//         StorageOverflow,
//     }
// }

// // The pallet's dispatchable functions.
// decl_module! {
//     /// The module declaration.
//     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//         // Initializing errors
//         // this includes information about your errors in the node's metadata.
//         // it is needed only if you are using errors in your pallet
//         type Error = Error<T>;

//         // Initializing events
//         // this is needed only if you are using events in your pallet
//         fn deposit_event() = default;

//         /// Just a dummy entry point.
//         /// function that can be called by the external world as an extrinsics call
//         /// takes a parameter of the type `AccountId`, stores it, and emits an event
//         #[weight = 10_000]
//         pub fn do_something(origin, something: u32) -> dispatch::DispatchResult {
//             // Check it was signed and get the signer. See also: ensure_root and ensure_none
//             let who = ensure_signed(origin)?;

//             // Code to execute when something calls this.
//             // For example: the following line stores the passed in u32 in the storage
//             Something::put(something);

//             // Here we are raising the Something event
//             Self::deposit_event(RawEvent::SomethingStored(something, who));
//             Ok(())
//         }

//         /// Another dummy entry point.
//         /// takes no parameters, attempts to increment storage value, and possibly throws an error
//         #[weight = 10_000]
//         pub fn cause_error(origin) -> dispatch::DispatchResult {
//             // Check it was signed and get the signer. See also: ensure_root and ensure_none
//             let _who = ensure_signed(origin)?;

//             match Something::get() {
//                 None => Err(Error::<T>::NoneValue)?,
//                 Some(old) => {
//                     let new = old.checked_add(1).ok_or(Error::<T>::StorageOverflow)?;
//                     Something::put(new);
//                     Ok(())
//                 },
//             }
//         }
//     }
// }
