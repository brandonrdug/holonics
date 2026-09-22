//! **The interconnection (Dirac) structure `𝒟 = 𝒟^⊥`.**
//!
//! [definition] A Dirac structure is a subspace equal to its bond-form orthogonal
//! (`Holon/Dirac.lean::IsDirac`); it is power neutral (`Holon/Dirac.lean::IsDirac.power_eq_zero`).
//! Its three presentations are the skew graph (`Holon/Dirac.lean::skewGraph`), the Kirchhoff
//! incidence (`Holon/Dirac.lean::kirchhoff`, Tellegen `Holon/Dirac.lean::tellegen`) and a kernel
//! pair; composition is `Holon/Dirac.lean::compose`. Existing owners: the `HolonicInteraction`
//! skew assembly and `junction_law::tellegen`.
//!
//! Empty in phase 2; `DiracStructure { Kernel | Incidence | Skew }` arrives in phase 3.
