# AC1: causal contact joins return propagation and its morphology derivative

[definition] This continues the [phase/relevance return](2026-09-09_AC1_AC2_REPEATED_FACES_RETAIN_PHASE_AND_EXCHANGE.md)
after `0bcc2522`. The new construction is an explicit candidate constitutive connection on the
existing contact population. Its phase follows learned contact overlap and actual source joins;
there is no independently selected rotation. Its physical calibration and usefulness for
cultivation are not inferred from its algebraic properties.

## The existing operations and the new composition

[established-bounded; source-inspected] `constitutive_field.cuh` already transports incoming
current by the seed's unit phase, reflects against held current and retains both branches.
`field_operative_reflection.cuh` additionally reflects through the operative contact map D and
its complete interior b. The latter's fixed-contact homogeneous interior has the real spectrum
derived in the preceding record. This identifies the scope of the missing composition; it does
not mean the whole engine lacks propagation or emission.

[definition] A contact e has the actual source and receiving occurrences retained in
`NativeOperativeContactBirth`. Within that one body's chronological population, e joins f when
`receiving(e)=source(f)`. A source without an incoming contact creates no invented join. Receiving
occurrences are unique and ordered; the source must precede its receiver. The exterior reference
validates these conditions. Native admission must obtain the addresses from its own field owner,
not equate numbers originating in different bodies.

[definition] Let d_e and d_f be the producing operative columns in their common root chart.
The declared dimensionless connection is `g=d_e†d_f`, using the existing unit current metrics.
At each join in receiving chronology, compose the paired reflection S_g with reversal J of the
second branch. This yields

```text
U_g = S_g J
    = 1/(1+|g|²) [ 1-|g|²    -2g     ]
                  [ 2 conjugate(g)  1-|g|² ].

(b_e,b_f) -> U_g (b_e,b_f).
```

The scalar two is the paired reflection's difference from the identity. The denominator is its
normal equation. These are generated relationships, not separately tuned phase constants.
Chronology orders overlapping joins; worker count or a shared receiver face does not commute them.

[proved-derived] Since S_g and J are unitary reflections, U_g is unitary. Direct multiplication
of the displayed matrix gives the same result. Thus the ordered word P_D preserves the complete
interior squared norm. Zero overlap gives identity. A contact rechart `d_e -> d_e γ_e`,
`b_e -> conjugate(γ_e)b_e` transports g covariantly and preserves the corresponding receiver.
This is a current norm at declared unit metrics, not an assertion of calibrated physical energy.

## The retained fibre becomes consequential through motion

[counterexample; implemented-exact; computational-witness] Three serial contacts with
`D=[1,1,1]` and `b=[1,-1,0]` have `Db=0`. Plain fixed-D reflection with zero exterior source
emits zero. The two actual contact joins give `P_D b=[1,0,1]`, and the subsequent same paired
reflection emits one while retaining interior squared norm one. The initial squared norm is two.
The complete balance holds; no source current was supplied to manufacture the emitted difference.

[proved-derived] Therefore ker D is not necessarily invariant under this admitted propagation
word, even with D fixed. Condensation through Db alone would lose future relevance. The
future-stable family from the [relevance foundation](2026-09-09_RELEVANCE_LOSS_AND_REALIZED_CLASSES.md)
must include P_D followed by the paired receiver. This is a concrete separating word, not a
general inverse or a claim that every hidden current is eventually visible.

## Complete return through the learned connection

[proved-derived] The connection differential is
`δg=(δd_e)†d_f+d_e†δd_f`. For an overlap covector z under the real complex pairing,
the corresponding column covectors are `G_e=d_f conjugate(z)` and `G_f=d_e z`.
The reverse pass traverses the retained forward word in reverse order, accumulating every
incident contribution. No later overlay replaces the morphology that supplied a forward g.

[proved-derived] For the complete propagated paired law, first return through the outer
reflection, then through P_D using its incoming-interior covector. Add both morphology returns.
The outer two-factor current term uses `k=P_D b_before-b_after`. The propagation contribution
can be represented `D_source H`, where each join contributes `H_ef=z`, `H_fe=conjugate(z)`.
Shared joins add their contributions. H is a sparse Hermitian return at the actual source cut;
it is not a second fit of D or a dense authored learning increment.

[established-bounded; implemented-exact; computational-witness] The reference retains the
actual per-join paired producers. Tests compare its tangent against an independent derivative
of the displayed rational matrix, including the changing denominator, then verify duality of
the complete propagated/reflected return. Holding the overlap fixed gives a different tangent.
The source-current generator control also rejects substituting unpropagated b_before in k.

## Family bounds and a finite numerical representation

[proved-derived] Direct multiplication gives

```text
(U_g-U_h)†(U_g-U_h) = 4|g-h|² / ((1+|g|²)(1+|h|²)) I.
```

Consequently `||U_g-U_h|| <= 2|g-h|`. With a complete Frobenius contact radius r_D, a join's
overlap error is at most `(||d_e||+||d_f||)r_D+r_D²`. Telescoping the unitary word bounds its
operator difference by twice the sum of these errors. For an incoming current ball centered at
b with radius r_b, an output radius is `r_b + 2 sum(overlap_errors) ||b||`. The implementation
uses exact component L1 upper bounds for these norms. The quadratic contact term remains.
With an exact contact map, this transport does not amplify the input ball radius.

[proved-derived] The finite numerical reference projects each returned component toward zero
at a declared dyadic grain. Each omitted component contributes at most one unit of that grain
to its local L1 error. Subsequent exact joins are unitary, so the sum of these local error bounds
encloses the complete exact word. Add this rounding radius to the source-family radius above.
This retains the full admitted family; it does not identify the projected point with its source.
The enclosure does not advertise a point derivative of quantization.

[established-bounded; implemented-exact; computational-witness] Exact/deformed-current controls
at several declared grains lie in the returned complete balls. The exact point return remains
available for derivative checks. Both representations share the same chronological join
construction and existing paired operator, without a native float or an independent learner.

## Actual material, cost and remaining native work

[established-bounded; implemented-exact; computational-witness] The
[full rational receipt](../experiments/normal_geometry_review/2026-09-09_causal_contact_propagation.json)
uses the entire 75-occurrence stored normal model: all 74 learned contacts and 73 joins.
The map radius is zero; the nonzero incoming current radius is retained unchanged. The complete
point norm is preserved, and exact coordinate witnesses separate both internal and Db boundary
balls. This is a prospective cold application to a stored operator, not an emitted Athena response.
Its input is the earlier actual conversation development, with no fixture-local learner.

[established-bounded; process-audit] The full rational calculation returns in 269.56 seconds.
An attempted interruption found the process already terminal with exit zero; it did not cancel
or invalidate the returned receipt. The cost motivates evaluating the same generator word at
the stored grain rather than expanding every rational current denominator.

[open] CUDA integration still owes resident evaluation of the word and its numerical residual,
the complete sparse overlap adjoint, and historical producer/decoder support for the additional
`D_source H` term. The existing rank-two journal cannot silently represent that contribution.
Preserve its actual source-map dependency and the propagated-before/current-after boundaries;
do not substitute the latest D, omit H, or keep whole dense source snapshots as the final reuse
design. This is the concrete AC1–AC2 construction following the reference return. No new native
propagation state has been committed by the exterior examples.

[established-bounded; implemented-exact; computational-witness; measured] The
[enclosed receipt](../experiments/normal_geometry_review/2026-09-09_causal_contact_propagation_enclosed.json)
evaluates the same complete 74-contact/73-join word at the source checkpoint's 72-bit grain in
1.5426 seconds. Both internal and boundary separators still return. The input radius
`40219/2361183241434822606848` gains rounding radius `73/2361183241434822606848`.
This is a comparison of exterior reference representations, not a measured native generation
speedup. The larger output ball retains the admitted source family; its center is not asserted
to equal the full rational current.

[established-bounded; process-audit] `cargo test -p holonic-engine --lib junction::producer:: --
--test-threads=1` passes 14 cases in 0.03 seconds. The unchanged native comparison is explicitly
ignored in that command. Both example processes exit zero; no CUDA kernel or Lean import changed.
Seven new controls cover joins/current balance, the hidden-current separator, complete
morphology return, contact recharting, malformed chronology, source-family enclosure and
dyadic-word enclosure. No tests of untouched native behavior were represented as new evidence.

[definition] Native continuation must preserve the newborn branch's original zero-input
constraint. If the new branch participates in propagation, its later nonzero current is caused
by that transport; the adjoint returns to the original constrained input. Derive the join
population from the actual field chronology and retain the numerical word/residual on the
device. The additional sparse H and its producing-map dependency belong in the return journal
and checkpoint before this law is enabled in cultivation or generation. Subsequent comparisons
use the actual conversation pipeline, without a phase-selection driver or a repetition filter.
