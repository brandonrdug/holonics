# M1 standing owner move

`holonic-engine::standing` was a source-neutral, exact receiver/retention object and now lives at
`holonics::receiver::standing`. This is an internal Rust path move under M1 (#69): the core library
already owns the exact rational matrix/restriction operations and the receiver's face/width law.
The main library therefore owns the executable standing law alongside its receiver-facing
contract, without creating an additional package or a compatibility module.

The full owner moves together: `GeneratorFamily`, `SourcePopulation`, `StandingLaw`,
`ReceiverReading`, `FutureObservation`, the future-sufficiency verdict and descent, `TimedFace`,
`MemoryLaw`, fidelity reconstruction, `ApertureChain`, contraction certificates, and the
receiver-relative extinction decision. The extinction decision reads each pair of future faces
with `law::receiver::width_over_readings` and keeps its certificate/search distinctions. No second
width or event-history archive is introduced. The theorem-mapped tests move with the source;
the release-width test now calls the core width owner on the same two exact faces.

`holonic-engine::evaluation_discipline` was the only production Rust consumer outside the module;
it now imports `holonics::receiver::standing::TimedFace`. The engine no longer owns standing or
its theorem-citation test entry. Lean remains at
`ElementaryHolonics/Foundation/Standing.lean` (`Soma.Holonics.Foundation.Standing`) until the
separate Lake path/namespace migration. The move adds no wire decoder: the standing types derive
`Serialize` but not `Deserialize`, and their invariants still require their checked constructors.

## Verification

Source audit and `rustfmt` on the touched files completed; `git diff --check` passes. Cargo builds
and tests were intentionally not run while the root workspace check was active. Run these after
restacking onto the verified Phase 12b session cut:

- `cargo test --locked -j2 -p holonics receiver::standing::tests`
- `cargo check --locked -j2 -p holonic-engine --all-targets`
- `cargo check --locked -j2 --workspace --all-targets`

The main-library test exercises the complete moved standing suite; the engine check covers the
`TimedFace` caller and remaining receiver-release integration; the workspace check validates the
new dependency direction. No Lean declaration changed, so no new Lean build obligation is created.
