# Joint source, condition and material keep their product constraints

[project-postulate] This continues the roadmap's coupled responsibilities 1–4. The previously
identified gap was a representation that retains a source family and condition family together
with their actual mixed products. A linear relaxation that makes those products independent
can admit sources that no generating parameters realize.

## Returned exact owner

[definition] `exact_linear::JointBilinearFibre` retains an existing bilinear realization, two
affine maps from one shared parameter vector, and an affine returned-face map. With homogeneous
coordinate θ̂=(θ,1), its exact Preimage Fibre is

`{ θ | F(S θ̂, H θ̂) − Y θ̂ = 0 }`.

The constant observed-face constructor is the specialization with only Y's last column nonzero.
The same parameter vector may contain distinct source, condition, intermediate and material
coordinates. Their relationship comes from the declared joint maps and equations, not from
assuming independent coordinates or identifying unrelated observations by equal dimensions.
This owner has an exact rational computational chart; it is not a general algebraic-root solver.

[definition] The retained polynomial face has columns
`(1, θ_i, θ_i θ_j for i≤j)`, with count `1+p+p(p+1)/2` derived from the parameter extent.
Off-diagonal coefficients combine the two ordered tensor terms. `evaluate` constructs all mixed
terms from θ itself. A solution of `polynomial().apply(z)=0` on an independently supplied z is
only a relaxation and is not accepted as a source. `restrict` composes both ports AND the returned
map with one affine parameter map whose last row preserves the homogeneous coordinate.

[definition] `JointBilinearSystem` retains a conjunction over that one parameter family. It
compiles the residual cores and their complete receiver into one existing bilinear realization.
Its affine reduction stacks all equations. Only when the entire quadratic block cancels does
it call the existing exact affine preimage solver. It returns the full parameter family, an
explicit equation separator, or `Nonlinear`. The last disposition preserves the implicit fibre
and does not assert emptiness. Parameters belonging to distinct occurrences must remain distinct
unless a supplied joining relation actually shares them; reusable material coordinates may be
shared explicitly across those occurrences.

## The joining coordinate makes a material inference lawful

[established-bounded; implemented-exact] The retained application uses θ=(x,h,z,m) and both
constraints `x*h=z` and `m*z=24`:

| Parameter occurrence | Source-junction residual | Material-output residual |
|---|---|---|
| `(2,3,6,4)` | `0` | `0` |
| `(2,3,8,3)` | `−2` | `0` |
| `(3,2,6,4)` | `0` | `0` |

The second row fits the output while violating the retained source junction. The joint system
keeps that failure visible. At the supplied cut `(x,h,z)=(2,3,6)`, the complete system reduces
to an affine material fibre with particular `m=4` and no free directions. At `(2,3,8)`, the
complete system has no compatible material: its equation separator is `(1,0)`. Looking only at
the material-output equation would incorrectly admit `m=3` there.

[established-bounded; implemented-exact] The [application receipt](2026-09-11_joint_fibre_receipts/cycle.json)
also applies the derived material coordinate 4 to a new junction input 15 through the existing
native bilinear operator and returns 60. The affine solve is exterior mathematical apparatus;
this is not a claim that the coupled Athena session has deposited that material. The receipt
states `native_athena_material_deposited:false`.

## Native constraint evaluation

[definition] `ResidentJointBilinearFibre` mounts the complete system's residual realization and
passes the **same resident parameter packet** to both affine ports. The existing packet
contraction now has an affine mode: its last column reads the packet denominator as the
homogeneous numerator, so the added coordinate is exactly one. The returned evaluation borrows the actual parameter occurrence and retains the complete
implicit model alongside its residual sections. No parameter or anchor is reconstructed through
a host readout. The ordinary non-affine mode remains the prior primitive.
Both modes retain denominator/pointness validation, checked wide arithmetic, exact normalization
and representation-overflow refusal.

[established-bounded; implemented-exact] Native tests cover non-dyadic shared parameters,
condition restrictions and conjunctive material constraints. Correlated ports `(θ,1−θ)` and
oppositely paired ports `(1−θ,θ)` have the same marginal affine ranges but different dot-product
residuals. Against observed face 1, the native readings at θ=0 are 0 and −1; at θ=1/3 they are
−4/9 and −5/9. Every measured result agrees with the exact owner. Intermediate section readout
counts remain zero before terminal observation. A nonzero residual remains a measured difference,
not a kernel error or an invented point solution.

## Formal return

[proved-derived; formal-checked] `Mathematics/GeneratorFactorization.lean` now proves the affine
bilinear expansion for a shared scalar parameter, the finite shared-parameter expansion of a
scalar-port bilinear linear map, and its fixed-port specialization. Together with the existing
finite tensor coefficient certificate these state the component algebra used by the constructor.
The new control proves `1+z=0` admits z=−1 while no real θ satisfies `1+θ²=0`; replacing a genuine
mixed coordinate with a free variable changes the represented family. The final finite-sum proof
explicitly transports scalar actions and swaps the nested finite sums. Earlier incomplete
simplifier drafts were repaired before the framework build was accepted.

## The remaining native incorporation binding

[open; source-inspected] The actual `NormalCoupledComparison` still owns the original producing
source, condition, relation and observed difference. Its source is further constrained by the
retained normal anchor ball. The new generic polynomial owner does not erase or replace that
bound. The next implementation must compile the actual native relation/paired coefficients into
a shared constraint chart on device, retaining the source cut, condition/material association
and anchor. It must then define the constitutive consequence used by the existing condition
contact and formation owners and stage one complete contemporary successor. Compatibility alone
is not a material-update law; a reference parameter solution is not an automatic native commit.
Pending returns must be consumed once and their extended constraint/encoding cut persisted.

[definition] No unrestricted nonlinear root solver, universal point gate, new learning engine,
foreign-model intake or broad cultivation was introduced. The representation gap identified in
the preceding return now has an exact executable owner and native evaluator; compilation from
the bounded wave source and its consuming lifecycle remain explicit implementation work.

## Verification

[established-bounded; process-audit] Final checks passed:

- Four exact joint-fibre tests, including cross terms, fixed-port reduction and the conjunctive
  material separator.
- Seven serial packet/joint-fibre tests with ignored CUDA tests included: the three new joint
  checks plus the prior four packet checks. The final warm selection returned in 1.33 seconds;
  an earlier six-case selection incurred cold kernel startup and returned in 188.80 seconds.
  Neither timing is a cultivation-throughput claim.
- The final `hephaestus_joint_fibre` build and execution, with the actual receipt above.
- `lake build ElementaryHolonics.Framework.Computation`, including the corrected finite-sum
  theorem; no proof assistant runs in native inference.

[definition] Reproduction from the repository root:

```sh
cargo test -p holonic-engine --lib exact_linear::joint_bilinear --no-default-features
cargo test -p holonic-engine --lib resident_section::bilinear --no-default-features -- --include-ignored --test-threads=1
cargo run -p holonic-engine --example hephaestus_joint_fibre --no-default-features -- OUTPUT.json
```
