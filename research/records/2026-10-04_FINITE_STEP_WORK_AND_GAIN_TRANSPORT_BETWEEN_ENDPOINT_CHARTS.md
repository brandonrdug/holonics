# Finite-step work and gain transport between endpoint charts

**Date:** 2026-10-04. **Refs:** [#62](https://github.com/brandonrdug/holonics/issues/62),
[#73](https://github.com/brandonrdug/holonics/issues/73),
[#63](https://github.com/brandonrdug/holonics/issues/63).
**Grade:** [proved-derived; formal-checked in isolated development and the complete
patched actual owner] for the two
finite transpose-algebra statements, with complete objects and clean axiom audits;
[proved-derived; source-only] for gain-order equivalence, Hermitian extension and
unresolved residual derivations; [proposed] for canonical root integration and
native consuming joins. The candidate is applied only in an isolated pinned snapshot.

## 1. The recovered owners and three outstanding joins

The elementary objects remain the vocabulary: a Holon's motion, its constitution,
pair contacts, receivers, deposition, navigator phases and clocks, tube and tower.
The construction is read in the six objects of the winding guide: helix; pair; faces
and placement; cell holonomy; tube; tower thread. This calculation concerns the
chart of a motion and its storage reading. It supplies neither an egg-to-material
identification nor a new topology or a receiver family.

The source search recovered the atlas, September 25/26 records, actual owners and
consumers, and matching operations in the pre-reset tree `13f8c734`. It did not find, before this work,
an existing theorem of the finite endpoint identity below. Historical expressions
are source premises; no retired realization is restored.

| Join | Existing source | Concrete remaining equality and consumer |
|---|---|---|
| Finite work under changing charts, including material return | [Motion, moving-metric energy law](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Geometry/Motion.lean#L910); [CausalChord, constant-chart congruence](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Foundation/CausalChord.lean#L495); atlas `motion.energy-moving-metric`, `receipt.rate-reading` | `F_hat = V0^T F V0`, for `F=T^T G1 T-G0`, then the complete affine energy reading and native opening/deposition residual. Derived in §§2–6. The prospective formal owner is the existing `Geometry/Motion` file. |
| A geometric motion's actual pair-rate and power port | [HelicalPairInteraction, pair-rate congruence](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Transport/HelicalPairInteraction.lean#L164); atlas `pair.rate-port-congruence`, `pair.medium-port`, `chain.jacobian-columns`; [helical geometry guide](https://github.com/brandonrdug/holonics/blob/3a242c99/docs/HELICAL_GEOMETRY.md) | Construct the actual state/rate decoder `C(q)` at the native contact and consume `power_native = w (J C(q) v)^T D (J C(q) v)`. A stored contact potential also needs its complete Hessian, including stress times the second derivative of the slip map. A drawn egg, tube or toroid does not supply this decoder, metric or material law. The general pair congruence already exists; this is its missing native consuming square. |
| Chart/material/phase changes and the admitted future quotient | [CausalRelevance](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Foundation/CausalRelevance.lean); [HNN/ModeQuotient](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/HNN/ModeQuotient.lean); [retention guide](https://github.com/brandonrdug/holonics/blob/3a242c99/docs/ELEMENTARY_OBJECTS.md#the-retention-contract) | Consume `q T_a = Tbar_a q`, `D q = R`, the source square and `q Dep_a = Depbar_a q` for the actual admitted actions and admission policy. Fixed-publication ring descent does not establish the adaptive aeon's quotient. The phase-sensitive comparison must retain its producing phase transports. The exact separator in §7 prevents energy neutrality being mistaken for future silence. |

The [September 26 shadow/egg record §5](https://github.com/brandonrdug/holonics/blob/3a242c99/research/records/2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md#L103)
already derives the continuous moving-chart relation
`A_hat=P A P^-1+Pdot P^-1`, `G_hat=P^-T G P^-1`,
`Sigma_hat=P^-T Sigma P^-1`. Its instantaneous signature is not a bound on a finite
passage. The result below supplies the finite work form and certificate transport.

The [recorded lessons](https://github.com/brandonrdug/holonics/blob/3a242c99/research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
fix the choices here. An endpoint identity must not be sold as certified deposition
(lesson 5), a local algebraic fixture as Athena usefulness (lesson 7), or an authored
answer routine as learning (lesson 1). Exact rational checks below check the law
outside HNN. They supply no predictor or task solution to it. The source-only choice
also avoids a resource refusal being answered with a larger limit (lesson 9).

## 2. The finite work form and its transport

[proved-derived; source-only] Let the motion's declared finite-dimensional affine
step be `x1 = T x0 + b`. At the two receiver sections the storage forms are `G0,G1`.
Let `y0=P0 x0`, `y1=P1 x1`, with inverses `Vk=Pk^-1`. Then

```text
T_hat = P1 T V0,       b_hat = P1 b,
G0_hat = V0^T G0 V0,  G1_hat = V1^T G1 V1,
F = T^T G1 T - G0.
```

**Finite endpoint identity:**

```text
F_hat = T_hat^T G1_hat T_hat - G0_hat
      = V0^T F V0.
```

The proof has no derivative, approximation, positive-definiteness or symmetry
hypothesis. It is valid over a commutative ring, using only `V1 P1=I` for the ending
chart's cancellation; `V0` may even be a rectangular pullback if only this matrix
identity is wanted. The proposed Lean statement uses square matrices to fit its
existing owner. Invertibility at both endpoints is required to interpret the
construction as two full coordinate charts.

Expand the first term:

```text
(P1 T V0)^T (V1^T G1 V1) (P1 T V0)
 = V0^T T^T (P1^T V1^T) G1 (V1 P1) T V0
 = V0^T T^T G1 T V0.
```

Subtract `V0^T G0 V0` and distribute. This is the complete proof.
The ending chart cancels because its metric is pulled back through the same inverse
as its state; a varying coordinate length does not become physical work.

## 3. Gain certificates and the exact affine work

[proved-derived; source-only] For a declared real gain bound `r` put
`F_r=T^T G1 T-r G0`. The same proof gives

```text
F_r_hat = V0^T F_r V0.
```

For real symmetric forms and an invertible initial-chart inverse `V0`,
`F_r <= 0` as a quadratic form iff `F_r_hat <= 0`. This uses real quadratic-form
order; it is not an order assertion over the general commutative ring of the
matrix identity. Initial invertibility is needed for the reverse implication.
For the forward direction apply `z^T F_r_hat z=(V0 z)^T F_r(V0 z)`.
For the reverse choose `z=P0 x`. Thus a certificate
`T^T G1 T <= rho^2 G0` is preserved. If these forms define an energy norm, require
them positive definite separately. No gain bound is obtained just by recharting.
In particular, an instantaneous inertia count alone does not certify this inequality.

If `G1` is symmetric, twice the actual affine work is

```text
2 DeltaE = (T x0+b)^T G1 (T x0+b) - x0^T G0 x0
         = x0^T F x0 + 2 x0^T T^T G1 b + b^T G1 b.
```

Every term is transported, not only the homogeneous form:

```text
T_hat^T G1_hat b_hat = V0^T T^T G1 b,
b_hat^T G1_hat b_hat = b^T G1 b,
y0^T F_hat y0 = x0^T F x0.
```

The common inverse cancels in each equation. The factor two follows from the two
equal cross terms of a symmetric form. For complex motion the corresponding
analytical identity uses conjugate transpose and twice the real part of the cross
term; this proposed insertion is the real/transpose algebra, not a checked
Hermitian bridge.

## 4. Physical material change and the reached state

[proved-derived; source-only] Changing coordinates and changing the constitution
are distinct operations. With `DeltaG=G1-G0`,

```text
F = (T^T G0 T-G0) + T^T DeltaG T,
DeltaE = [E_G0(x1)-E_G0(x0)] + 1/2 x1^T DeltaG x1.
```

The second line prices deposition at the actual reached state, including any source
motion in that state. It is the decomposition in the existing
[deposition_work and commit_balance](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/Holon/Deposition.lean#L125).
The endpoint covariance says that these physical readings survive a simultaneous
coordinate change; it does not permit `DeltaG` to be suppressed or counted twice.
Time parity still concerns oriented boundary incidence and exchange; this identity
contains no assertion of time reversal.

## 5. Decoder and unresolved-opening residual

[proved-derived; source-only] Assume `G1ᵀ=G1`. A realized affine block may decode as
`x1=T x0+b+eta`, with an explicit unresolved motion `eta` at its declared grain.
Put `v=T x0+b`. Its complete undivided energy residual is

```text
2 DeltaE - [x0^T F x0 + 2 x0^T T^T G1 b + b^T G1 b]
 = 2 eta^T G1 v + eta^T G1 eta.
```

Under `eta_hat=P1 eta`, `v_hat=P1 v`, and the ending metric above, both right-hand
terms are invariant. An unresolved fibre is not set to zero because its coordinate
representative failed to move. This identity is exact and is not a small-error
estimate. A bound would additionally need an admitted norm and an enclosure of
`eta`; neither is silently introduced.

## 6. The native consuming equation and acceptance

[executable; source-inspected] The existing
[ContactCut::continue_deposited](https://github.com/brandonrdug/holonics/blob/3a242c99/crates/holonics/src/hnn/word/continuation.rs#L232)
checks the same-state work `committed-before=deposition_work`, then returns
`opening-committed=opening_difference`. Its exact
[focused continuation consumer](https://github.com/brandonrdug/holonics/blob/3a242c99/crates/holonics/src/hnn/reference/continuation.rs)
changes contact C while preserving its geometric coupling and ports, pump phase and
clock. The next exact tick responds; the lattice case names its unresolved next
contact representative. No new execution of that fixture is claimed here.

[proposed] At the actual consumer, a claimed pure change of storage chart must supply
its decoder/transport/metric squares, for example on an admitted invertible block:

```text
D1 T_native(E0 x,u) = T x + B u + eta,
Dk Ek = I,
G_native,k = Dk^T Gk Dk.
```

The `eta` above is the decoded residual, not an invented extra source. The receipt's
opening difference must be calculated through these operands and through separately
computed physical port, pump, dissipation and deposition work. The endpoint
difference alone telescopes by definition; it cannot independently certify those
fluxes. Perturbing a physical flux must make that independent residual nonzero.
This is not a replacement for the executed field's already complete
[field_executed_balance_with_defects](https://github.com/brandonrdug/holonics/blob/3a242c99/lean/Holonics/HNN/Word.lean#L861).
It gives the chart equality that must consume it when a chart actually changes.

Acceptance is fixed before a larger build:

1. Check the proposed existing-owner theorem and its axiom audit with an admitted
   single bounded Lean invocation. Update its atlas row to formal-checked only then.
2. A pure endpoint chart change returns zero physical opening work, while a true
   same-state material change returns its independently computed deposition work.
3. A nonzero source retains both cross and self-energy terms; a decoded unresolved
   motion retains the complete §5 residual.
4. The receiving covector/phase and future action squares are checked separately;
   an energy-preserving physical phase move remains distinguishable by a receiver.
5. Native geometric changes or full Resident continuation are claimed only after
   the corresponding actual decoder, reached deposition, restore and flux consumer
   passes. No training substitutes for these invariants.

## 7. Exact falsification witnesses

All readings here are exact. They are algebraic fixtures outside the HNN, not a task
answer family and not a new Rust execution.

| Witness | Exact operands | Required result |
|---|---|---|
| Pure moving chart | `G0=G1=T=P0=I`, `P1=diag(2,1)`, `x0=(1,0)`, `b=0` | `G1_hat=diag(1/4,1)`, `F_hat=0`, `DeltaE=0`. Keeping the Euclidean form instead would invent `3/2` work. |
| Actual material work | Previous operands but `G1=diag(2,1)` | `F=diag(1,0)`, `DeltaE=1/2` in either chart. The physical material change remains. |
| Affine source | One dimension, `G0=G1=T=1`, `x0=b=1` | `DeltaE=3/2`: homogeneous work `0`, cross work `1`, source energy `1/2`. Dropping the cross term fails. |
| Unresolved opening | One dimension, previous source but `eta=1/2` | `x1=5/2`, `DeltaE=21/8`; the unresolved-motion work is `9/8`, so `3/2+9/8=21/8`. |
| Energy preservation is not future silence | `G=T^T G T=I`, `T=[[0,-1],[1,0]]`, receiver `R=(1,0)`, difference `k=(0,1)` | Present reading `Rk=0`, future reading `RTk=-1`. A fixed physical receiver distinguishes the phase turn. Recharting must also transport `R_hat=R V`. |

The last witness is a receiver-relative null contrast reopening, not empty
spacetime. Together the witnesses distinguish coordinate transport, deposition,
source work, unresolved motion and actual phase-sensitive reception.

## 8. Local receipt and integration boundary

The staged patch adds two theorems to `Geometry/Motion`: the finite work-form
congruence over a commutative ring and the undivided affine work expansion with a
symmetric ending metric. It adds no definitions, imports, runtime implementation,
library or compatibility alias. It also routes this record through the existing
records index, foundation supplement and geometry atlas, with source-only grades.

The original [source receipt](receipts/2026-10-04_finite-step-work/source-validation.json)
is preserved. Its last two fixtures recorded readings but omitted their operands
and checker; only the five displayed elementary witnesses were independently
auditable from that first packet. The [exact operands](receipts/2026-10-04_finite-step-work/exact-fixtures.json)
and [Fraction checker](receipts/2026-10-04_finite-step-work/check_exact_fixtures.py)
now support all seven. A [fresh execution receipt](receipts/2026-10-04_finite-step-work/exact-checks-02.json)
verifies all seven and reproduces both earlier non-diagonal readings. These are
computational witnesses, not a Lean verification. To reproduce without modifying
dated receipts, copy the checker, operands and original source receipt to a fresh
directory, then run the copied checker; it writes a new receipt there.

The isolated two-theorem Lean source imports only `Mathlib.Data.Matrix.Mul` and
`Mathlib.Tactic.Ring`, against the repository's pinned Lean4.33.0/Mathlib cache.
The existing import sealer binds its full transitive dependency closure. One
unchanged generic bounded runner then acquired the exact existing shared lease
once, but the fixed 8GiB available-memory gate refused before any compiler launch.
The lease was released quiescently; no retry or weakened floor followed. Local
`validation.json` records this follow-up separately from the first source-only
receipt, together with patch applicability and unchanged canonical owners.
A later user-authorized fresh admission passed that gate. Lean then exited at
runtime startup with `failed to create thread`, before elaboration, objects or
axiom output. Source/dependency seals stayed unchanged, no memory/deadline guard
fired, and the lease was released after reaping. This failed attempt is preserved
separately. At that checkpoint no third attempt or policy correction had occurred. The generic runner has an
additional finite address-space limit whose startup compatibility is unresolved;
the receipt alone does not establish the cause. That checkpoint had no successful formal check. Subsequent accepted development
is recorded below. No training, installation, external post, stage, commit, push
or merge occurred.

## Isolated elaboration receipt, October 4

The first admitted compiler invocation failed before elaboration with `failed to
create thread`. Its generic dispatcher imposed a 4 GiB virtual-address limit
absent from the established Lean policy. One authorized comparison corrected only
that supported configuration, with the same source/imports/compiler command,
one CPU, 17-second child deadline, 4 GiB group memory cap and 8 GiB/4 GiB memory
floors. It reached elaboration and ended in 1470217973 ns, with child peak
RSS 1782752 KiB and group peak 2612985856 bytes; no memory, floor or deadline
guard fired. The virtual-address discrepancy is therefore supported as the
startup blocker, although the runtime's allocation errno was not recorded.

`finite_work_form_rechart` elaborated and printed only `propext`,
`Classical.choice`, `Quot.sound`. `affine_quadratic_work` failed its `hT` rewrite:
an unscoped transpose rewrite also changed the nested right operand. Its
`sorryAx` output is a failed audit. The repair proposed at that checkpoint gave an explicit
three-step calculation transporting only the left operand, then associating
the matrix products. That repair was source-only at the checkpoint; no fourth run had occurred.
The failed module produced no accepted object.
The [submitted source](receipts/2026-10-04_finite-step-work/FiniteEndpointWork-submitted-03.lean),
[compiler diagnostic](receipts/2026-10-04_finite-step-work/compiler-03.log),
[prior startup error](receipts/2026-10-04_finite-step-work/startup-02.log) and
[development receipt](receipts/2026-10-04_finite-step-work/development-check-03.json)
preserve this incomplete read. Complete input seals remain in the local execution receipts.
The exact common lease was released after publication and the child was reaped.

This is proof-development evidence, not certification of a native contact or
Athena output. The rejected module was not acceptance. The source-only checkpoint and its
seven witnesses remain historical evidence beside the accepted check below.

## Accepted isolated algebra, October 4

The final [submitted module](receipts/2026-10-04_finite-step-work/FiniteEndpointWork-accepted-05.lean)
checks both `finite_work_form_rechart` and `affine_quadratic_work` with no warning,
error or `sorryAx`; both audits list only `propext`, `Classical.choice`, `Quot.sound`.
The explicit calc scopes the transpose transport, and `DecidableEq n` is now
required only by the first theorem. The [accepted receipt](receipts/2026-10-04_finite-step-work/finite-work-accepted-05.json)
and [compiler log](receipts/2026-10-04_finite-step-work/compiler-05.log) preserve
the complete-module result. Wall time was 946103970 ns against the fixed
17000000000 ns child deadline; child peak RSS was 1792272 KiB. Inputs and complete
import-part metadata stayed unchanged after execution; the owned child was reaped
and exact common lease released. Cgroup charged pages and child RSS are separate
readings; the actual child remained below 4 GiB.

These are accepted isolated proofs; the actual-owner check below is a separate
receipt. Integration targets the existing Motion owner and atlas in the
same change. Gain-order/Hermitian/general-action
bridges and the three concrete native joins in §1 retain their stated obligations.

## Complete actual-owner and combined import checks, October 4

The source proposal was applied only in a sparse snapshot pinned to `3a242c99`.
The baseline Motion and FrameTransport sources are byte-identical at public
`9a62a685`. The complete patched Motion owner compiled directly, producing fresh
objects; the [receipt](receipts/2026-10-04_canonical-geometric-integration/canonical-motion-09.json)
and [full log](receipts/2026-10-04_canonical-geometric-integration/canonical-motion-09.log)
record exit zero, 6,348,126,580 ns wall / 17,000,000,000 ns fixed child deadline,
3,804,076 KiB child RSS and 629,534,720 bytes charged group peak. These are distinct
memory readings. Its one unused `Matrix.head_cons` simp argument occurs in unchanged
pre-existing `sling_speed_gain` code, not either new work lemma.

The [combined consumer](receipts/2026-10-04_canonical-geometric-integration/CanonicalGeometricAudit.lean)
imports both freshly compiled actual owners and checks all nine new declarations.
Its [receipt](receipts/2026-10-04_canonical-geometric-integration/canonical-audit-10.json)
and [log](receipts/2026-10-04_canonical-geometric-integration/canonical-audit-10.log)
show exactly `propext`, `Classical.choice`, `Quot.sound` for each, no warning,
error or `sorryAx`, and 1,287,909,036 ns wall / the same fixed deadline.
It consumes owner declarations rather than copies of the proofs. All three native
Lean children were reaped, owned groups emptied and the exact lease released.
Complete import-part metadata remained unchanged under the recorded pre-launch
hash/stamp contract. No budget, runner or root source was changed.

The first Motion preparation lacked the installed Lake source root; a later
preparation exceeded the unchanged 17-second limit. Removing lookup roots that
selected no module preserved the complete graph and fitted the same limit.
The first complete Motion compiler attempt then refused because Lean selects
the first `Holonics` namespace root, while the sealer had assumed per-file
fallback. Exact already-sealed public dependency objects were placed in that
isolated namespace by symlink; no cached dependency was rewritten. Those failed
preparation/layout receipts remain local historical evidence. The accepted
preparation seals all 4,912 Motion modules and the combined check all 4,914.
These results establish actual-owner source integration in the pinned snapshot;
canonical root application, native physical work decoding and production joins
remain proposed.
