//! **Generators `G`: initial configuration, clock and phase lift.**
//!
//! [definition] A lifted phase `θ̃ = θ + 2πn` (`Holon/Generator.lean::LiftedPhase`); a full-turn
//! jump is lossless (`Holon/Generator.lean::jump_lossless`) and carries winding
//! (`Holon/Generator.lean::jump_carries_winding`, `Holon/Generator.lean::jumps_are_carries`).
//! Existing owners: `CompiledGeneratorSite` content — `SituatedScrew`, `RationalPhase`, `Clock`,
//! `Odometer`.
//!
//! Empty in phase 2; `Generator` arrives in phase 5.
