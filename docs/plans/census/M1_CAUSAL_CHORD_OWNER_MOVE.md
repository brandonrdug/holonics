# M1 causal-chord owner move

`holonics::receiver::causal_chord` owns the exact `(A, B, C)` linearization, transfer function and its
cancellation witnesses, pole and mode readings, probe separation, and storage-rate forms. The
top-level `receiver` namespace now has this populated specialized receiver. `holonics::law::receiver`
remains the owner of passive linear readings, widths, and release vocabulary; joint active reception
and receipts remain separate construction work. Its
production imports are only existing `holonics` owners (`geometry`, `exact_linear`, `exact_value`,
`inertia`, `rational_polynomial`) plus numeric, serde and error crates; it has no CUDA or engine
runtime dependency. The Lean peer is `Foundation/CausalChord.lean`.

The portable synthetic law and checked-wire tests move beside the main owner. The engine keeps
three cross-owner checks as `tests/causal_chord_engine.rs`: agreement with `lattice_gauge::exact_spectrum`,
the rigid-triangle construction using `physical_constraint_complex`, `physical_constraint_grading`
and `rigidity_receiver`, and the two ignored M5 measurements using those same rigidity owners and
the authenticated local structure release. The current schema `holonics.causal-chord.v1` and
validated wire shapes are preserved. No old `holonic_engine::causal_chord` forwarding path remains.

Verification is pending the stacked CUDA-mount branch gate. Focused gates:

- `cargo test -p holonics --lib receiver::causal_chord::tests`
- `cargo test -p holonic-engine --test causal_chord_engine` (M5 measurements remain ignored)
- `cargo check --locked -p holonics -p holonic-engine --all-targets`
