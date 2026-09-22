//! **The complex `K` and its connection-valued incidence `d_A`.**
//!
//! [definition] Oriented cells with boundary `∂`, `∂∘∂ = 0` validated; a connection twists the
//! incidence (`Holon/Complex.lean::connectionIncidence`) so `d_A² = F_A` is the curvature face
//! (`Holon/Complex.lean::dA_squared`, `Holon/Complex.lean::cell_curvature`); a flat connection is
//! exactly closed (`Holon/Complex.lean::exact_closed_iff_flat`). Existing owners:
//! `GradedCausalComplex`, `HodgeOperator`, the device `NativeFieldDeclaredIncidence`.
//!
//! Empty in phase 2; `CellComplex` and `Connection` arrive in phase 4.
