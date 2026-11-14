//! The card and the field's resident realization, moved from `holonics_cuda::hnn` by C3 of #603.

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

pub use card::{
    Card, CardBuffer, CardError, DeviceCensus, EntryCensus, Layout, Operand, Realization,
    certificate_layout, copy_layout, ingest_layout, read_layout, word_layout,
};
pub use field::{CardField, FieldTimes, Yardsticks};
