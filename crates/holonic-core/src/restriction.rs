//! **Restrictions `π` to coarser grains: the scale square or a typed defect.**
//!
//! [definition] A restriction is a power-preserving morphism (`Holon/Restriction.lean::IsMorphism`,
//! `Holon/Restriction.lean::power_pushforward`); the pushforward of a Dirac structure is Dirac
//! (`Holon/Restriction.lean::pushforwardD_isDirac`); a failed scale square is retained as
//! `Holon/Restriction.lean::squareDefect`; the Kron reduction is
//! `Holon/Restriction.lean::kron_exact`. Existing owners: `continuing_tower::{Tower, Transition,
//! Migration}`, `continuing_tube::SquareDefect`.
//!
//! Empty in phase 2; `Restriction` and `Descent` arrive in phase 6.
