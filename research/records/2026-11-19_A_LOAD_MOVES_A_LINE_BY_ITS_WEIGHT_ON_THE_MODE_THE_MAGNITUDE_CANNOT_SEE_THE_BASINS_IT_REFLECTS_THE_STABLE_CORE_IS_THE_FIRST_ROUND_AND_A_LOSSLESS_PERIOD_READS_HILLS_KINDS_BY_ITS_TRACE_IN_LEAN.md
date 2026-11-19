# A load moves a line by its weight on the mode, the magnitude cannot see the basins it reflects, the stable core is the first round, and a lossless period reads Hill's kinds by its trace, in Lean

November 19, 00:15 UTC. The seventh formalization pass over #410, its first set: the owed clauses of the
part-done boxes, beginning with the spectroscopy box's line shift and `H = H_min B`. Six new modules of
`lean/HolonicsResearch` and additions to four existing ones, each elaborated at the package's toolchain with no
`sorry`, no `axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Transport/SpectralLineShift` (new) | For a transpose-symmetric pencil `P(s) = s²C + sD + K` the left mode is the right mode, so wherever a line `s(ε)` and its mode `v(ε)` are differentiable with `P_ε(s(ε))v(ε) = 0`, `s′(0) vᵀ(2sC + D)v = −vᵀ(s²ΔC + sΔD + ΔK)v`: at a simple line this is `δs`, and the mode's own motion never enters (`line_shift_mul`, `line_shift`). The shift is linear in the load; on a lossless line mass slows the turn, stiffness quickens it and viscosity alone moves the decay; the record's witnesses `−9i/10` and `−104i/25`. | #410's spectroscopy box; the record of October 24, §1 | `spectro.load-line-shift` |
| `Transport/MinimumPhase` (new) | A factored rational response is `H = H_min B` (`response_eq_minPhase_mul_blaschke`), each hidden zero `|a| > 1` reflected to `1/ā`; `|B| = 1` on the circle, so `|H| = |H_min|` there with no hypothesis on `H`; the winding `(2πi)⁻¹∮ H′/H` is the zeros inside less the poles inside (`winding_response`, from `∮(z − a)⁻¹`, Cauchy outside); and `winding(H_min) − winding(H) = deg B` (`winding_deficit`). The record's witness `(z − 2)/(z − 1/3)`. | the same box; the same record, §4 and §5 | `spectro.hidden-basins` |
| `Holon/TorusMetricDimension` (new) | A translate of a resolving set resolves on a translation-invariant distance, so the refusals are read on the sets holding `0`: `C₄ □ C₄` needs four landmarks (256 triples in the kernel, about 17 s) and `C₅ □ C₅` three. | the box "Loop curvature"; the notebook `loop_curvature_checks.py` | `landmark.small-metric-dimensions` |
| `Compression/HeldFaceOrder` (new) | A release that holds the faces `Q` of `T(x, y)` lies in `⋂_(q∈Q) Fib_q`; on a finite space with a given mass the chain rule `H(X, Y) = H(Y) + H(X | Y)`, a face of what is held gains nothing, and for every reading order `σ` of a word's places `Σ_k H(d_σ(k) | d_σ(<k), F) = H(W | F)` and the per-place gains of a held face sum to `I(W; q | F)` (`gain_any_order`). | the box "The held face's reading order"; the record of October 23 on near misses, §3 and §6 | `radix.held-face-reading-order`, `arith.near-miss-kept-face-fibre` |
| `Compression/Landmark/ReleaseHealth` (new) | The family-to-class map is L1 nonexpansive with operator norm one, two posteriors inside their intervals give faces within `Σ_f (upper_f − lower_f)`, the class enclosure's widths sum to the posterior widths, and an enclosure that covers the simplex certifies no draw of `Population.certified_inverseCDF_class`. | the box "Release distribution and health"; `docs/RECEIVER_HOLARCHY.md`, "A mixture face's variation" | `receiver.population-receiving-face-health` (now `formal-checked`) |
| `HNN/HillFloquetKinds` (new) | The Cayley tick of a traceless rate has determinant one, and so has a period of ticks; on `det M = 1` the trace reads Hill's kinds: `|τ| < 2` no real multiplier and every complex one on the circle (turn), `τ > 2` a multiplier above one (boost in a tongue), `τ < −2` one below `−1` that flips the cell each period and grows (the subharmonic), `τ = ±2` the shear `(M ∓ 1)² = 0`; in a tongue `ν⁻ⁿMⁿ(αv + βw) → αv`, so the sign of the in-phase coordinate selects the sheet `±v`. | the box "Pump/Floquet locking"; `HNN/Floquet`'s open line on the subharmonic | `parametron.hill-floquet-kinds` (new) |
| `Compression/Landmark/SiteIsolation` (added) | The stable core both ways (`stable_core_converse`, `stable_core_iff`): with nonnegative news, `t ∈ P(σ)` exactly when `t` lies in the claim of every passage agreeing with this one within a section of `t`. Where a greater place reaches `t`, the passage cut to `t`'s section (the news before it silenced, the places after it removed) agrees there, its greatest place within the section is a site that reaches `t`, and `t` is outside its claim. | the box "The level's law of sites"; the record of November 13 on landmarks, §5 statement 5 | `code.site-isolation-landmark` |
| `Mathematics/RadixItinerary` (added) | The strands' digit (`strand_digit`): on the ring of the result's length `q + 1 = b^L`, with `k` digits written and the comparison `c ≡ −bᵏ s_k`, the `b`-th of the conjugate face `(−c) mod q` is the next digit at every `k < L`, the all-`(b − 1)` result being the ring's zero; for a positive result the length is the largest ring whose face at the start reads outside the first tenth (`length_is_largest_ring_outside`), and zero reads inside on every ring. | the box "The strands' release"; the record of October 26 on the strands, §2 and §4 | `hnn.tower-strands` |
| `Mathematics/CheckLoop` (added) | The loss joined to the pair potential: with `z_T = z − z₁` and `z_H = z − z₂` the loss's principal chart is a lift of the undivided ratio and the pair potential of `Physics/Fluid/Singularity` at strength `2π` (`−iℓ` at `−2πi`); its covector along the coordinate is the pair's clock `1/W`; real strength reads a source–sink pair, a boost, imaginary a vortex pair, a turn; every lift differs by whole laps `2πi n`. | the box "The check loop and the settling look"; the record of October 23 on the singularity, §2 | `ratio.loss-singularity-flow` |

The boxes of #410 these answer, by their opening words: "Information spectroscopy (#404)" (the line shift and
`H = H_min B`, so the box is whole with #1004); "Loop curvature" (whole, with #1003); "The level's law of sites"
(whole, with #998); "The held face's reading order" (whole, with #519); "The check loop and the settling look"
(whole, with #522); "The strands' release" (whole, with #524); "Release distribution and health" (the L1 law and
the widths; the release distribution and the producing-key relation stay); "Pump/Floquet locking" (whole: Hill's
kinds and the sheets' selection, the attraction read in direction at the growth's clock).

## 2. What the pass corrected

1. **A held face's zero gain was worded wrongly in the atlas.** `radix.held-face-reading-order` said a face `q(W)`
   of the release alone "gains nothing". As written that is false: `I(W; q(W) | F) = H(q(W) | F)`, zero only where
   `F` fixes `q(W)`. The record's §6 means a face the reader computes from what it has already written, and that
   is what `condEntropy_pair_comp` proves; the row now says so.
2. **The stable core's other direction holds at an integer grain.** `SiteIsolation`'s Limits read the record's
   construction ("give each earlier place less news than `u`") as having no integer form when `c_u` is one unit,
   and left the direction unstated. Silence serves in its place: a place of no news is greater than no place of
   positive news, and where the greatest place in the section carries no news it stands at the section's start,
   so the cut passage needs no news below one unit.
3. **"Truthful health" has no definition in its sources.** `docs/RECEIVER_HOLARCHY.md` names F5's numerical health
   (radius, robust count, operator bound, contraction) as a missing term, so `ReleaseHealth` states the L1 law, the
   widths and the enclosure, and names the rest.
4. **Hill's kinds were already `SiteKind`'s.** `Compression/Landmark/SiteKind` classifies a real move as a rotation,
   a boost or null by its eigenvalues; `HillFloquetKinds` reads those kinds on a period of the pump and adds only
   what the Floquet reading needs: the boost below `−2`, the shear at the edge, the lossless tick in `SL(2)` and the
   selection of a sheet.
5. **Stability is not used by the factorization.** `H = H_min B`, `|B| = 1` and the winding deficit hold for any
   zeros and poles off the circle; stability only makes `H_min` a stable response.

## 3. What each statement stands on

- **The line shift** assumes the differentiable branch: the implicit function theorem on `det P_ε` at a simple root
  is not proved, nor the lossy Rayleigh witness of the record's §1.
- **The minimum-phase face** is the factored rational form. Beurling's general inner–outer factorization, that
  `H_min` is fixed by `|H|`, and the causal cepstrum of §5 stand beside it.
- **The tori** are two finite checks; the general law for `C_m □ C_n` (three when a ring is odd, four when both are
  even) is the notebook's reading.
- **Hill's kinds** take the trace as given: which pump strengths and detunings put it above `2`, the Mathieu tongues,
  are the record's open construction, and the sheets attract in direction, with no saturating constitution.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eleven modules by name: `Build completed successfully (8772 jobs)`, exit 0,
79 s, no declaration elaborated with `sorry`; projected under 10 minutes, deadline 20 minutes, peak resident set not
read. Single-file checks of
each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision on a cloud host,
read by exit status (each `EXIT 0` with no output; `TorusMetricDimension` 21 s, the rest 4 to 8 s), for the reason
the first pass's record gives (`agent-inferred`). The research library's aggregator imports the six new modules.

Two workers on disjoint owner paths wrote five of the new modules; the lead wrote `HillFloquetKinds` and the four
additions, re-checked each file from the tree, and read every `L:` owner added to the atlas against its module's
declarations by `tools/link_check.py atlas` (`broken=0`).
