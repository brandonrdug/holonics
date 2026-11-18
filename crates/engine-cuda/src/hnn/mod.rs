//! **The card and the field's resident realization**: the card (`card`); the realization's state and schedule (`resident`) and its
//! phases by object (`clock`, `moment`, `contact`, `carry`, `level`, `adjoint`); the card's readings of itself (`profile`); and the
//! module that re-exports them with the card suite's tests (`field`).

#![deny(clippy::float_arithmetic)]

pub mod adjoint;
pub mod card;
pub mod carry;
pub mod clock;
pub mod contact;
pub mod field;
pub mod level;
pub mod moment;
pub mod profile;
pub mod resident;

pub use card::{Card, CardBuffer, CardError, DeviceCensus};
pub use field::{Resident, FieldTimes, Yardsticks};
