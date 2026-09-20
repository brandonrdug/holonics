# Wave 11 returns the section ports, and its baseline shows a text window on one lane

**Date:** September 20, 2026. **Tree:** `ee5a4b50` plus this wave. **Tracker:** #60.
**Issues:** #57, #58, #59 returned; #61 opened; #17 restated. The
[owner-network record](2026-09-20_THE_FIELD_SESSION_JOIN_HAS_ITS_OWNER_NETWORK_AND_NAMED_ABSENCES.md)
holds the inventory this wave started from.

## What returned

[established-bounded; implemented-exact; computational-witness] **#57 — row-sectioned normalized
receiver and pullback.** `ResidentNormalEnclosureSection::{normalized_participation,
normalized_section_return}` and `NativeNormalizedSection::pull_back` compute, for every row of a
typed section in one resident passage, the grouped face `p`, the returns `q−p` and `J_p(q−p)`, and
the covector return `J_p g` with `J_p=diag(p)−ppᵀ`. No second softmax was written:
`normalized_compare_faces` is unchanged and its residual return was extracted into
`normalized_potential_pullback`, called by both the comparison receiver and the pullback. Device
tests show row-by-row equality with the single-occurrence owner, exact equality with
`NormalizedKernel` for probabilities, pullback and the duality `⟨dY,g⟩=⟨ds,J_p g⟩`, gauge
invariance, retained radii and typed refusals. `[agent-inferred]` The exact control uses the
packet-modulus measure because `exp` of a nonzero dyadic is irrational; the row radius is the L1
sum of coordinate half-widths, an outward Euclidean bound.

[established-bounded; implemented-exact; computational-witness] **#58 — condition covector port,
enclosure-source section form, re-entry.** The forward `φ=[s,c,c⊗s]` is holomorphic in each
operand, so its real transpose multiplies by the conjugate of the other operand:
`g_s[i]=g[s_i]+Σ_j conj(c_j) g[c_j⊗s_i]`, `g_c[j]=g[c_j]+Σ_i conj(s_i) g[c_j⊗s_i]`
(`ResidentBilinearFeatures::pull_back`, `kernels/section_bilinear_adjoint.cuh`), checked against
`exact_linear::bilinear` and a finite difference of the forward owner. The applied reaction now
takes an enclosure source and an enclosure or point condition over rows, with radius
`‖A(h)‖ρ_s+‖L_x‖ρ_c+‖Q‖ρ_sρ_c`, bit-for-bit equal to the single-row owner; and
`reapply_bilinear{,_enclosed}` carries a generated enclosure section forward as the next source at
full radius. `identity=true` contracts `(I+A(c))` on the shared source so a refinement does not
double its radius each step. This is the port the
[September 8 cotangent record](2026-09-08_AC1_THE_MATERIAL_RETURN_HAS_A_CONTEXT_COTANGENT.md) named.
Still absent: the `M*g` step that forms the feature covector from a reaction-output covector, and
an adjoint linearized at an enclosure operand.

[established-bounded; implemented-exact; measured] **#59 — exposure bridge, retained shared
comparison, cursor, first baseline.** `FieldSectionRequest::from_exposures` revalidates each frame
against its manifest, admits development-partition material with a human-authored request, and
emits a held request with a free response extent; `ExposureAperture::bounded` refuses, never
truncates, and (reviewer finding, repaired) refuses a response extent that splits a codec byte.
The shared chart retains a comparison at its producing epoch and applies it exactly once, before
or after reopen; session wire v3 carries the retained comparisons, an issued-identifier counter
and the `ExposureCursor`, with v1/v2 still readable. `examples/athena_exposure_field.rs` walked
the private exposure stream twice, resuming from its own checkpoint, printing counts, labels and
timings only. `[agent-inferred]` Retention keeps request-level operands because the row law is
about to change; an update therefore reports both its producing and its applied epoch.

[established-bounded; process-audit] The reviewer attacked thirty claims across the three returns
and confirmed one defect, the byte-splitting aperture. The integrated host run passes 3,309 engine,
58 HNN and 66 geometry tests.

## What the baseline measured

[established-bounded; measured] The [first shared-chart run](../experiments/athena_field/shared/README.md)
executed three of nine prepared development observations and both validation sources through the
public session: 110 s generation and 196 s update medians, 1.2–1.3 GB of native sections, an 18 MB
session; every supplied position preserved; 1,096 of 6,955 withheld bytes correct against 830 for a
most-frequent-byte rule.

[established-bounded; source-inspected] Those clocks are a realization, not the law. The section
kernels guard `blockIdx.x||threadIdx.x` and loop rows on one thread, `bilinear_features` launches
one row at a time from the host, and nothing under `constitutive_fibre` or `holonics-hna` calls the
cover, partition, layout or launch-law owners. The 2,110–11,800 regions of a request read shared
immutable standing and write disjoint windows: they commute and are co-present under the
[hardware-cover ruling](2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md).
#61 realizes them across the card. Two of this wave's new kernels follow the same one-lane pattern
and belong to that repair.

[established-bounded; source-inspected] The chart itself is a text window. Its embedding is one-hot
hex nibbles in offsets `[-2..2]`; its decoder is per-position basis selection. The embedding object
of Brandon's September 14–19 messages — linked tori, phase attention on admitted contact,
whole-field refinement, decoding by a participating receiver — exists only in
`intrinsic_holonic_flow`, `connected_holonic_field`, Lean and `relational-geometry`. No native HNN
source file names a torus, helix or knot. #17 is restated as realizing that object on the resident
body, with the nibble section as one receiving face; the ports above are its operators.

## Why agents kept meeting the mathematics as news

[established-bounded; process-audit] Three measured causes, none of them a property of any one
session.

1. **No Claude agent received the contract.** `CLAUDE.md` was removed on September 19 in the belief
   that the harness falls back to `AGENTS.md`; this build does not. Every subagent transcript of
   this wave contains `/home/b/CLAUDE.md` (a desktop-environment file) and no line of `AGENTS.md`.
   A primary received it only when it was attached by hand.
2. **The pickup path never states the object.** `AGENTS.md` is 548 lines with no equation block and
   118 lines of negation; the state, roadmap and issue bodies describe work in operator nouns
   (source, receiver, transport, owner, consumer). The issue Wave 11 was dispatched from named no
   torus, helix or knot. The geometry lived in leaf documents no pickup step routes through.
3. **The native code really is separate from the geometry**, and the documents narrate that
   separation with scope disclaimers ("exterior reference, not native"). A reader of code plus
   pickup documents sees a linear-algebra pipeline and files the mathematics beside it.

[definition] The repair is documentation that states the object first:
[`CLAUDE.md`](../../CLAUDE.md) is now Claude's self-contained operating document (the machine, its
equations, the code map, arithmetic and hardware law, commands), loaded into every session and
subagent; [`docs/THE_MACHINE.md`](../../docs/THE_MACHINE.md) is the shared statement for both
harnesses; the [field-session source map](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#field-session-source-map)
carries the embedding object and the cover realization at the place the work is described.
`AGENTS.md` remains Astra's contract; rebuilding it on the same object-first pattern is open.
