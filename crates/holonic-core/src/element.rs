//! **Element relations `𝓔`: the constitution.**
//!
//! [definition] Storage, resistive, source, active and pump relations on the port kinds
//! (`Holon/Element.lean::Ports`, `Holon/Element.lean::PortHolon`); quadratic storage is
//! `Holon/Element.lean::storageEnergy`, and the power balance is
//! `Holon/Element.lean::PortHolon.power_balance`. The implicit midpoint balances exactly
//! (`Holon/Element.lean::midpoint_balance`); backward Euler reports its defect
//! (`Holon/Element.lean::backwardEuler_balance`). Existing owners: `SymmetricForm`/`Inertia`
//! (storage), `ContactFace`/`ContactDissipation` (resistive), `SourceCurrent` (source).
//!
//! Empty in phase 2; `ElementRelation` and `PowerTerm` arrive in phase 3.
