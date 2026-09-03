# The HNA4 morphology factor is occurrence-carried and the formal owners require a causal-cone adjoint return

**Date:** 2026-09-02  
**Truth status:** `counterexample` for the HNA4 realization; `definition` for the reconciled law  
**Evidence:** `source-inspected`, `measured`  
**Scope:** review of the HNA4 deed at commit `baa988a9` against the Lean owners of morphology
change. This record schedules nothing; Brandon's direct request of 2026-09-02 asked for a
rederivation or a reconciliation with the existing formalization.

## What the HNA4 realization does

[counterexample; source-inspected] The developmental occurrence carries the morphology factor.
`NativeFullOperationOccurrence` has the field `morphology_current`
(`crates/holonic-engine/src/holonic_intelligence/full_operation.rs:36`), and the HNA4 driver
supplies `Some({ significand: 2, exponent: 0 })` on it
(`crates/holonic-engine/examples/developmental_morphology_hna4.rs:77`). The operation does not
derive the factor. It reads the presented carrier and the reacted carrier, requires
`alignment(presented, reacted) > 0` (`full_operation.rs:396-406`, `alignment` at `:1745`), and
composes the caller's factor into `self.morphology`. `alignment` is the sum over coordinates of
the product of interval centres. For a positive scale of a nonzero carrier that sum is positive by
construction, so the gate cannot refuse the deed it was added to guard.

[counterexample; source-inspected] The retained morphology is one global scalar, not a local
constitutive change. `apply_morphology` (`full_operation.rs:821-836`) multiplies the output of
every later operation by the composed factor. After a factor of two at operation 41, each of the
remaining 1,233 operations of the cycle would double its carrier again; the exact grain would be
exceeded within a few operations. The HNA5 application matrix therefore ran with identity
morphology, and the HNA4 receipt covers exactly two operations.

[counterexample; source-inspected] Removing the driver's `morphology_current` and the alignment
gate changes nothing about the arithmetic the operation performs on its carrier. Under the HNA
blueprint's falsifiers, a driver that supplies the change owns the deed.

## Reconciliation with the formal owners

[established-bounded; source-inspected] The HNA0 owner does not state a morphology law.
`FiniteRecurrentOperation.advanceMorphology` is a free field of type
`Morphology → Occurrence → (Site → Carrier) → (Site → Carrier) → Morphology`
(`soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicRecurrentEcology.lean:204-205`),
consumed at `:237`. Its firing control lets the occurrence itself carry the increment
(`:346-347`). The Rust HNA4 is a faithful realization of that under-constrained owner. The
formal correction needed is not in HNA0's recurrence law, which is right, but in the absence of a
constitutive law for `advanceMorphology`.

[established-bounded; source-inspected] The owners that do constrain morphology change agree on
three requirements, none of which the HNA4 factor meets:

1. **The delta is the causal adjoint of a receiver difference.** `CultivationPassage.causalAdjoint
   : Difference → Delta` (`Computation/HolonicIntelligenceLifecycle.lean:186`);
   `GradientProposal.candidate morphology = morphology - learningRate • metric.gradient
   (differential morphology)` (`Computation/HolonicCultivationCharts.lean:48-60`); the gradient is
   the metric-raised covector (`Computation/HolonicAdjointNormalization.lean:42`); and the adjoint
   of a composed passage returns in reverse factor order
   (`HolonicAdjointNormalization.lean:62`).
2. **The change is supported on the causal cone and every outside site is unchanged.**
   `LocalCausalConeCultivation.outsideUnchanged`
   (`Computation/NativeMorphologyVariant.lean:111-119`). A global scalar applied to every later
   output has no outside.
3. **The carrier of the change is an additive factorized overlay on the cross-section, not an
   elementwise or global mask.** `FactorizedLinearOverlay.apply input = base input + outward
   (inward input)` (`HolonicCultivationCharts.lean:106`).

The reafference split that the 2026-09-02 correction removed lived in `CultivationPassage`'s
requirement of a genuinely later exterior return. The adjoint, cone, and overlay laws do not
depend on that split and survive it.

## The reconciled law

[definition] Let operation `t` present carrier `x`, react to `y`, and emit the face `observe(y)`
at its declared receiver. Let `o` be the next ordinary occurrence of the same recurrence, whether
self-emitted or application-produced. Then

```text
d   := D_y ℓ(observe(y), o)                        -- differential of the declared receiver comparison
δ   := adjoint(localCurrent word)(d)               -- reverse factor order through the cone
W'  := W - η · gradient_metric(δ ⊗ x) on causalCone(δ), W' = W outside it
advanceMorphology W o x y := W'
```

realized as `base + outward ∘ inward` over the packed resident base so the coefficient population
stays resident and exact, with rest and remount of the overlay as optional storage. For the tied
boundary the declared receiver is the normalized exponential receiver already formalized at
`HolonicAdjointNormalization.lean:95`, whose differential is the face minus the indicator of `o`
and is invariant under a common shift (`:112`). This fits the HNA0 signature exactly: the
occurrence argument of `advanceMorphology` is the next occurrence, not a carried factor. No
world verdict, reward, label, status, or commit enters; the comparison is with the next occurrence
of the loop, which is the next-token reading Brandon named. The learning rate and metric chart
are declared apparatus apertures and must be reported as such, never derived from a count.

[interpretation] The Complex Parametron storage law (`Millennium/HolonicComplexParametron.lean`,
`coupledStorage` at `:296`) supplies an alternative that needs no differential: storage pulled back
from the presented currents through the receiver constitutive form on the incident cone. It is
local and derived, but it is not the cultivation law of record in HIF4 and MVF0, which is the
adjoint return above.

## What implementing the reconciled law requires

[definition] The transposed contraction over the resident fixed-frame tile pool; exact pullback
through the RMS, GELU, causal-contact, and soft-cap reactions; the factorized overlay carrier on
the full-operator session with its cone bookkeeping; and a rerun of the HNA4 control in which the
driver supplies only the next occurrence. This is a construction deed and begins only from a
direct request. Until it returns, the HNA4 receipt is evidence that the session can retain and
apply a morphology projection across operations, and nothing more.
