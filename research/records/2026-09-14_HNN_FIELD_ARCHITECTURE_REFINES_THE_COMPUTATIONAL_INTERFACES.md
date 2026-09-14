# HNN field architecture refines the computational interfaces

[project-postulate] Brandon requested an HNN counterpart of a complete transformer diagram:
encoding, internal transport and decoding, with complex dimensionality represented through
interacting toroidal regions and whole-field generation. Transformer, diffusion and SSM are
coarse comparisons to operations within HNN, not three architectures to add together. He also
made explicit that upgraded mathematical constructions must refine the affected libraries and
interfaces, rather than remain isolated formal deposits.

## Returned diagram and model explanation

[definition] The [model formula](../../docs/HNN_FORMULA.md#reading-the-field-architecture-diagram)
now contains the reusable architecture diagram and its mathematical reading. The same source
supports selection of reception, contact/attention, internal circulation and generation within
one visible object. Input is mounted into situated sections; attention combines participation,
phase/frame transport and values; internal state carries current/material and unresolved modes;
generation refines and reconstructs a joint field at its receiving boundary.

[established-bounded; computational-witness] The
[diagram source](../experiments/hnn_field_architecture/README.md) uses exact rational torus
stations, existing certified collision facets and one invertible polynomial material map
with determinant one. The map transforms all shown source geometry together. The colored
strands and coupling arcs are architecture-diagram marks, not simulated predictions.
Region addresses are integers; section rank, phase coordinates, spatial projection and
fractal dimension are not identified. Browser arithmetic acts only on integer ink stations.

[definition] The transformer papers' field/reaction, attention-derivative, operator-splitting
and recursive-basin ideas are linked through the existing four-paper analysis. The diagram
uses those relations to explain the HNN object, rather than copying a fixed sequence stack.
A text codec may serialize a generated field, but its output-token index does not become the
model's integration coordinate. Internal receiving/generation uses the same construction.

## Source audit and implemented refinements

[established-bounded; source-inspected] The audit followed `crates/holonics`,
`relational-geometry` frame/receiver interfaces, `holonic-engine` exact linear/bilinear,
normalization, scalar/graded diffusion and operative native fields, plus the public
`holonics-hna` coupled body. It found useful existing operations with fragmented binding;
no absence of mathematical machinery was inferred merely from a missing familiar class name.

[established-bounded; implemented-exact] `BilinearOperator`, `BilinearProductCore` and
`BilinearRealization` now supply input differentials and covector pullbacks. For
`C=R[(Ax)⊙(By)]`, their existing factorized core computes

```text
δC=R[(Aδx)⊙(By)+(Ax)⊙(Bδy)],
λ_x=Aᵀ[(By)⊙Rᵀλ],        λ_y=Bᵀ[(Ax)⊙Rᵀλ].
```

No output tensor expansion is needed during these operations. The mixed finite-change term
stays explicitly separate; material derivatives retain their own operands. Covectors are not
silently identified with vectors in a Euclidean metric. `precompose_ports` composes declared
new-to-old maps into the factors and rederives the entire receiver family, including new
freedom introduced by rank reduction. It deliberately admits noninvertible maps without
calling them invertible recharts. No generic Holon wrapper or competing model owner was added.

[proved-derived] The diffusion audit exposed an important energy distinction. The implicit
finite-step equation obeys

```text
E_after−E_before = source_work−conductive_dissipation−implicit_step_defect.
```

The last term is `||φ_after−φ_before||²_C/2`. Total stored-energy decrease therefore cannot
be routed wholesale into a physical thermal state. In the existing unit two-node case,
`energy_departed=2/9`, comprising `1/9` conduction and `1/9` step defect. With one unit of
source on the first node, source work is `4/3`, conduction `4/9`, step defect `5/18`, and
stored energy grows by `11/18`.

[established-bounded; implemented-exact] `DiffusionReceipt::energy_balance` and
`ExactSheafDiffusionLaw::energy_balance(receipt,event)` return the same exact balance type.
Both enactment owners consume that identity. The graded method binds the receipt to its
actual law/certificate and grade, not just equal dimensions, and uses both lower and upper
Hodge terms. Its grade-one regression has zero upper compatibility but positive conductive
dissipation `2/9`; dropping the lower term would fail the energy relation.
The existing native circulation adapter consumes the balance and retains it through the
original receipt. Existing serialized receipt fields and API identifiers are preserved.

[definition] Existing delayed-observation APIs were retained: a prediction does not already
possess a future observation. Likewise an exterior JSON inspection is a legitimate receiver,
but it is not the resident Holon itself. These scopes do not justify a new universal response
wrapper. The actual field/body assembly remains the source/material/operator connection
already recorded in the model contract.

## Checks and scope

[established-bounded; process-audit] Relevant checks passed:

- `cargo test -p holonic-engine exact_linear::bilinear::tests --lib`: 13 tests, including exact
  finite differences, duality, coordinate covariance, shape refusals and rank-change receivers.
- `cargo test -p holonic-engine --no-default-features --lib diffusion::tests`: 10 scalar/sheaf
  tests, including source work, harmonic state, lower-coboundary energy and source mismatch.
- `cargo test -p life --lib native_intelligence::circulation_diffusion::tests`: 2 public adapter
  tests with the actual native boundary fixture.
- Browser execution: all four operation selections, no script errors and no narrow-screen
  horizontal overflow. Desktop and narrow output were rendered and visually inspected.
- Formatting was restricted to changed Rust owners; the final diff has no whitespace errors.

[established-bounded; source-inspected] The Holon, model, Rust, fluid and architecture guides
now carry these interfaces and diagram meanings. The implementation method explicitly carries
a mathematical correction into its actual library/consumer equation within the same return.
The pre-existing native construction draft and unrelated local files were preserved.

[open] This completes the requested diagram and the scoped interface refinements, not the
whole native Athena assembly or a full native continuum Q-field solver. The new exact
operations are reusable constituents at their stated library/consumer scopes. Their diagram
is neither a benchmark nor evidence of a trained frontier model.
