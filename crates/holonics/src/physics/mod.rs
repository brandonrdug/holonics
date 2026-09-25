//! **Physical instances** of the Holon law (ELEMENTARY_OBJECTS operator contract, "Physical
//! instances"; rebuild step 6, K3 #74): fluid control volumes and complex fluid, waves, and thermal
//! exchange, each keeping its constitutive equations, clocks, heat and entropy balances and its
//! participating receiver. Exact over `Rat`; no float enters a law.

pub mod fluid;
pub mod information;
pub mod spacetime;
pub mod thermal;
pub mod wave;
