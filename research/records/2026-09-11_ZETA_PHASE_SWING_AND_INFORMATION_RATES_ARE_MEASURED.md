# ζ phase, Swing and situated information rates

[project-postulate] Brandon's September 11 direction makes ζ/RH-related spectral placement,
phase, gaps and generator relationships immediate Hephaestus applications. The purpose is
usable mathematics for Holonic Encoding and later algorithm/code construction. A proof of RH
is not the admission condition for those applications.

## Actual analytic return

[established-bounded; implemented-exact; computational-witness] The existing exact rational
η atlas was run over `2/5 ≤ Re(s) ≤ 3/5`, `12 ≤ Im(s) ≤ 36`, covering 24 integer-height
bands. It returned five winding-one zero localizations, each refined twice. No known zero
ordinates were supplied. Here `η(s) = (1 − 2^(1−s)) ζ(s)` and the prefactor has no zeros in
this strip. Each reflection-symmetric box contains one zero; ζ reflection therefore fixes its
real coordinate at `1/2`. This is a result about the scanned rectangle, not a claim to cover
all zeros of the complete critical strip below height 36.

| Occurrence | Retained ordinate interval | Gap to next occurrence |
|---|---|---|
| 0 | `[14,57/4]` | `[27/4,29/4]` |
| 1 | `[21,85/4]` | `[15/4,17/4]` |
| 2 | `[25,101/4]` | `[5,11/2]` |
| 3 | `[121/4,61/2]` | `[9/4,11/4]` |
| 4 | `[131/4,33]` | — |

[definition] Source is retained in the
[compressed exact atlas](2026-09-11_zeta_information_receipts/atlas-12-36.ron.gz);
[the receiver return](2026-09-11_zeta_information_receipts/information.json) retains full
intervals, phase masses, symbolic information, analytic residuals and source addresses.
Gzip is ordinary cold serialization, not evidence of native Holonic Compression.

[established-bounded; source-inspected; computational-witness] Creation uses the existing
Euler–Maclaurin analytic enclosure and boundary-winding owners. `verify_artifact` rederives
stored polygon windings, checks segment joins/enclosures, refinement partition and selection,
source settings, symmetry and interval relations. It does **not** independently recompute every
analytic enclosure on every boundary segment. The separate rational point evaluations below
exercise the analytic evaluator again; they do not close that independent-verifier boundary.
The source run reports 40,903 milliseconds excluding compilation. No native HNN run occurred.

## Measurements are receivers, with units and retained comparands

[definition] For occurrence weights μ(h) ≥ 0 with positive total mass, receiver information
I_R(h) has the situated rate

`rate_R = (Σ_h μ(h) I_R(h)) / (Σ_h μ(h))`.

The denominator records what counts as a measured holon occurrence, rather than an arbitrary
mesh-cell count. Here each zero-localization occurrence has mass one. Within it, exact source
contour L1 length distributes that mass among certified boundary segments. The chart, contour,
normalization and ambiguous signatures remain in the return. A different receiver can return
a different information rate over the same analytic object.

[proved-derived; formal-checked] `Foundation/SituatedInformationRate.lean` composes the existing
information owner with weighted occurrence rates. It proves invariance under an equivalence
between finite occurrence types, subdivision with conserved parent mass and inherited receiver
information, and the artifact of dividing fixed information by a duplicated unweighted count.
It also transports the existing cross-entropy = entropy + KL decomposition from nats to bits.
These laws do not assert that a subdivision discovering new receiver distinctions preserves
information, nor that every holon intrinsically carries the same number of bits.

[definition] The application keeps the following quantities separate:

| Receiver | Comparands and unit |
|---|---|
| Localization resolution | `−log₂(refined width / parent width)` bits, under the declared uniform height measure within the parent band |
| Phase-signature entropy | Uncertainty of certified enclosure signatures, in bits per normalized contour draw; averaged per zero-localization holon |
| Reference-code loss | `−Σ P(a) log₂ Q(a)` bits per the same draw, with any code-missing events retained separately |
| Parent/signature information | Pooled signature entropy minus mean conditional signature entropy, in bits |
| Gap comparison | Full oriented interval difference first; histogram entropy in bits per resolved comparison second |
| Analytic residual | Full complex enclosure of η at a declared rational representative, its squared norm and analytic remainder |
| Representation cost | Serialized witness bytes in the stated codec; distinct from information and executable compression |
| Computational work | Reported analytic time, 148 distinct measured boundary segments and 10 additional point evaluations; full arithmetic work is not instrumented here |

[established-bounded; implemented-exact] The point receiver is the midpoint of the retained
ordinate interval at real coordinate `1/2`. Its complex residual is retained, and the midpoint
is never installed as an exact zero. Reference-code support describes that particular code;
it is not a ruling that an event has no causal origin or relevance.

## Observed phase and gap differences

[definition] A certified complex rectangular enclosure is read through its possible closed
quadrants. Origin-excluding rectangles permit four singleton quadrants and four adjacent
pairs. Those eight possibilities derive from this receiver geometry; they are not an intrinsic
byte/octet capacity. Pair signatures retain uncertainty across an axis. The distribution is
of **enclosure signatures**, not a distribution of exact phase angles. Contour subdivision or
tighter analytic bounds may refine those signatures and change this reading.

[established-bounded; implemented-exact; computational-witness] The returned measurements are:

| Reading | Exact value or outward rational display enclosure (bits) |
|---|---|
| Localization gain, each occurrence | `2` |
| Total localization gain | `10` across measure `5` |
| Mean conditional phase-signature entropy | `[351/128,703/256]` |
| Pooled phase-signature entropy | `[47/16,753/256]` |
| Parent/signature mutual information | `[49/256,25/128]` |
| Uniform eight-signature reference loss | `3` |
| Later windows read through the first window's phase code | `[195/64,781/256]` |

The last lower endpoint exceeds `3`: this particular local code transfers worse than the
uniform geometric code. The comparison uses later **spectral windows**, not physical time or
native HNN prediction. It is a directly observed restriction on reuse; it supplies no universal
spectral-statistical law. Exact symbolic forms, rather than decimal approximations, are stored.

[established-bounded; implemented-exact] Adjacent gap differences are `[-7/2,-5/2]`,
`[3/4,7/4]`, `[-13/4,-9/4]`: decreasing, increasing, decreasing. All three signs are resolved.
Their histogram entropy is `log₂(3) − 2/3` bits per comparison; the uniform binary reference
loss is one bit. These triples overlap, so this histogram is not an independent-process entropy
rate. A future unresolved interval remains unresolved rather than receiving a midpoint sign.

## Swing and transported phase

[proved-derived; implemented-exact] `Geometry/CrossRatio.lean` and `Geometry/SwingPotential.lean`
already own cross-ratio and receiver/history transport laws. The atlas relation owner now
accepts retained ordinate intervals directly. For `t ↦ −t`, the application obtains the same
ordered cross-ratio enclosures `[258/187,57/32]` and `[45/44,152/115]`. Signed gaps reverse.
It separately conjugates the complex η field: quadrant indices permute, source L1 length is
preserved, and signature entropy agrees exactly. Ten point evaluations also check conjugate
analytic enclosures at the five rational representatives and their reflections.

[definition] The information rate above is a quotient of weighted quantities; Swing's
projective receiver compares four ordered marks. They are related through transported
receivers, not interchangeable operations. Under a general rechart the source measure must be
pushed forward with the object and receiver. Declaring a new uniform measure after a projective
change is a different experiment. Conjugation does not assert `η(s)=η(1−s)`.

## Source changes and verification

[established-bounded; implemented-exact] `surprisal.rs` already represents exact information
as rational combinations of prime logarithms. This return fixes `log₂(2)=1` as an exact bit
coordinate, including signed coefficients and mixed forms, instead of enclosing `ln(2)/ln(2)`
independently. It also corrects a misleading comment: ordering finite rational-log expressions
is not mathematically undecidable; the existing comparison API can remain unresolved at its
declared enclosure grain.

[definition] Reproduction from the repository root (unpack the retained gzip to the indicated
local path to reuse the source instead of regenerating it):

```sh
cargo run -p relational-geometry --release --example holonic_eta_ratio_atlas -- 12 36 .local/artifacts/hephaestus-zeta-information/atlas-12-36.ron 4 2 24
cargo run -p holonic-engine --example zeta_information --no-default-features -- .local/artifacts/hephaestus-zeta-information/atlas-12-36.ron research/records/2026-09-11_zeta_information_receipts/information.json
cargo test -p holonic-engine --lib surprisal::tests --no-default-features
cargo test -p relational-geometry --lib
```

[established-bounded; process-audit] The scoped Rust suites passed: 16 surprisal tests and
50 relational-geometry tests, including exact dyadic information and transported interval
relations. The final application run returned successfully;
`lake build ElementaryHolonics.Framework.Information` passed with the new imported rate owner. These are exterior measurement/formal checks, not tests of a new native learner.

## Product consequence

[definition] The next useful comparison is a **changed generator with a fixed receiver**, then
a **changed receiver with transported source and measure**. Reuse the existing indexed analytic
head/tail and factor/word owners; preserve the complete complex return and analytic remainder.
Compare phase signature, gaps and code loss alongside actual work/representation costs.
Refinement must distinguish newly resolved analytic uncertainty from a changed source law.
The failed local-code transfer gives a concrete reason to study contextual applicability.

[definition] The coding segue is executable lowering of an admitted operator/recurrence word:
retain coefficient domain, exact arithmetic/overflow behavior, source/index clock, decoder,
residual and full successor relation. Existing native primitive/limb owners are the target.
Search cost, execution cost and information loss require separate measurements. No new compiler
or live Lean binding is introduced by this return; the roadmap retains the native incorporation
obligation before a Hephaestus application is called resident HNN conduct.

[interpretation] An automaton as a causal modulator is a useful computational correspondence
with a polymer or active site: exposed contact, internal state, input-conditioned response and
retained successor. Entropy diffusion alone does not distinguish life: inorganic crystals,
circuits and fluids also have internal dynamics. A sharper programme studies maintenance and
modulation of organization under repeated supplied stimuli, using those actual response maps.
