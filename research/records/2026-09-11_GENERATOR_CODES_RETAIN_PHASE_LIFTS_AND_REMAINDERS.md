# Generator codes retain phase lifts and remainders

[project-postulate] Brandon's latest direction joins surprise and literal code-length to
constituents per receiving holon, modulo/remainders, chain links, gyroparallelograms and
microbiology. The active generator-comparison increment now returns an executable exterior
comparison; native HNN development remains paused at its separately documented boundary.

## The denominator supplies a situated unit

[definition] Write a constituent family as `C(h)` over a receiving/containing holon `h`.
“Constituent holons per receiving holon” describes the fibre over one parent. Across multiple
parents, the established measured rate is `Σ μ(h) I_R(h) / Σ μ(h)`. The singular wording
names the unit; a plural denominator is also mathematically legitimate when it explicitly
aggregates several receiving occurrences. Numerator and denominator have different roles and
addresses even when both are called holons. Their types do not disappear by verbal cancellation.

[proved-derived] For a positive differentiable denominator M and numerator I,
`d(I/M) = (M dI − I dM)/M²`. An inverse change follows when I is held fixed; causally coupled
changes in both quantities need not be inversely related. Normalization therefore exposes a
comparison, while a constitutive/source law supplies the actual dynamics. Existing
`Foundation/SituatedInformationRate.lean` already proves transported measure and subdivision
laws. `Millennium/ReceiverIndexedCausalLengthTower.lean` separately types boundary count,
addressed passage length, clock, ruler and resource work, retaining the quotient–residue state.

## Changed generators, unchanged analytic receivers

[established-bounded; implemented-exact; computational-witness] The new
[`eta_generator_comparison.rs`](../../crates/holonic-engine/examples/eta_generator_comparison.rs)
uses the previous five localized-zero lineages and their rational representative receivers.
At each it compares the existing Euler–Maclaurin decomposition at N, the same analytic law at
2N, and the direct alternating η series at N terms with its summation-by-parts tail. The
representatives are not asserted to be exact zeros. All pairwise differences compared with
the first route contain the origin, and both Euler–Maclaurin routes resolve the same quadrant.
Each route retains its full complex enclosure and analytic remainder; overlap alone is not
used to prove two unspecified functions equal. The known source identities supply the common
analytic target.

| Receiver Im(s), Re(s)=1/2 | EM head cut N → 2N | Resolved η quadrant in both EM routes | Direct route |
|---|---|---|---|
| `113/8` | `9 → 18` | negative real, negative imaginary | all four quadrants remain possible |
| `169/8` | `12 → 24` | negative real, positive imaginary | all four remain possible |
| `201/8` | `13 → 26` | positive real, positive imaginary | all four remain possible |
| `243/8` | `15 → 30` | positive real, negative imaginary | all four remain possible |
| `263/8` | `16 → 32` | positive real, negative imaginary | all four remain possible |

[established-bounded; implemented-exact] In all five returns,
`2^-20 < remainder(2N)/remainder(N) < 2^-19` for the **source ζ remainder**. The fixed order
is m=10 and σ=1/2: the analytic decay factor is `N^(1−σ−2m)=N^(-39/2)`. This explains the
scale of the observed improvement; it is not a refinement of the de Bruijn–Newman threshold.
The direct route's bound remains too wide to resolve a quadrant at these term counts. Its
current is retained rather than mistaken for a precise η value.

[definition] `EtaChainDecomposition.remainder_radius` is the ζ remainder **before** multiplication
by `1−2^(1−s)`. The return names that source and bounds its transported η contribution by the
factor's complex L1 bound. It also reconstructs the head + integral + boundary half + Bernoulli
crossings + remainder and compares that result with the existing evaluator. The chain owner
currently re-evaluates its sum internally: recorded timings include that work. This is a
precision/representation comparison, not a claim of an optimized speedup. Full arithmetic work
is not yet instrumented.

## Surprise, literal words and packet residue

[proved-standard] Ideal information length is `ℓ(x)=−log₂ Q(x)`. A literal binary codeword
has integer length L(x). Shannon lengths `ceil(ℓ(x))` admit a prefix code with Kraft sum at
most one; their expected overhead above ideal length is below one bit per symbol. The exact
KL difference applies to ideal lengths; actual integer code-length differences retain their
rounding/redundancy terms. This distinction is now corrected in
[`TABLET_THE_COMPRESSION.md` §6](../../docs/canon/TABLET_THE_COMPRESSION.md).
[Shannon §§9–10](https://www.princeton.edu/~wbialek/rome/refs/shannon_48.pdf) provides the
coding construction and explicitly discusses transmitting a shared π generator instead of its
digits: the retained source knowledge changes what must be communicated.

[established-bounded; implemented-exact] The 60 head-term phase-enclosure signatures, in their
actual parent/term order, return this canonical exterior prefix code. Its distribution uses
**counting measure per term**, distinct from the previous normalized contour-length measure.
It is measured on this population, not a held-out prediction experiment.

| Signature mask | Count | Codeword | Literal bits |
|---|---|---|---|
| 1 | 9 | `100` | 3 |
| 2 | 13 | `101` | 3 |
| 3 | 5 | `1100` | 4 |
| 4 | 16 | `00` | 2 |
| 8 | 17 | `01` | 2 |

The payload has 152 bits and Kraft sum `13/16`. Its literal mean is `38/15` bits per term;
ideal mean lies in `[283/128,567/256]` and integer overhead in `[41/128,83/256]` bits.
The parent term populations are `(8,11,12,14,15)` and payload lengths `(20,27,32,35,38)`.
Thus the same return has 12 terms per receiving holon on average, and `152/5` payload bits per
receiving holon. Neither number is a universal holon capacity. The decoder/codebook and framing
remain required; their storage is not included in payload length.

[established-bounded; implemented-exact] All 153 bit cuts of the payload were checked. Decode
the available prefix, retain its incomplete word, prepend that remainder to the next fragment,
and the entire original signature sequence is recovered. With the caller's three-bit carrier
frame, `152=3·50+2`; the final residue is `01`. This is bit framing, not a claim that a bit is
a nucleotide. This decoder reconstructs **signature sequences**; prime words, amplitudes,
analytic currents and parent lineage remain in the separate retained source receipt.

## Phase and material paths

[established-bounded; implemented-exact] Every EM head term retains its prime factor address,
amplitude, full turn and complex current. The existing relation
`n^-s = exp(−σ log n) cis(−τ log n)` supplies both faces. Divide the turn enclosure by the
retained `2π` enclosure, split at integer seams, and keep `(winding, residue interval)` for
every intersected chart. Negative lifts and seam overlap are preserved. The residue chart is
an enclosure of the analytic phase, not a choice of its centre; the source turn and period
remain available with it.

[definition] Three remainders are now visibly distinct: an analytic unsummed current, a
within-cycle phase residue, and an incomplete received codeword. The existing clock–ruler
formalization reconstructs its scaled potential from quotient **and** residue. The new example
exercises analogous interval and packet boundaries without treating those different objects
as one scalar error.

[interpretation] The shared prime logarithm connects surprise and phase: `−log₂(p^-a)=a log₂ p`
is a coding-ruler reading, while `−τ log p` is an angular lift. A physical wavelength requires
a spatial phase chart: one cycle satisfies `Δφ=2π`; a calibrated constant phase gradient k
then gives `λ=2π/|k|`. Codeword count becomes physical length through an actual carrier spacing
or transport law. Equal information lengths alone do not determine equal wavelengths.

[definition] `Geometry/Gyrogroup.lean` already retains the gyration in composition and defines
based gyroparallelogram completion; its additive instance gives `left+right−source`.
`Millennium/HolonicPolygonGyroWinding.lean` binds polygon edge populations, turn ledgers and
route defects. For a chain-link model, retain the frame transported along each edge, contact
incidence and its ordered composition. Comparing two routes gives the frame mismatch; evolving
that frame supplies a precession receiver when a motion law is supplied. Material twist,
connection torsion and gyrogroup gyration keep their own definitions. The present scalar complex
phase experiment is an abelian transport instance and does not demonstrate nontrivial gyration.

## The microbiological return

[proved-standard] DNA pairs **bases**; coding regions are read as nucleotide triplets, with
codons specifying amino acids or termination. The reading frame is part of decoding. Multiple
codons can return the same amino acid, so the amino-acid face does not identify the original
codon. [NHGRI codons](https://www.genome.gov/genetics-glossary/Codon) and
[its coding/reading-frame primer](https://www.genome.gov/Pages/Careers/EducationalPrograms/ShortCourse/2016ShortCourse/2016-08-03ShortCourseGeneticsandGenomicsPrimer_BW.pdf)
support this biological chart.

[definition] The useful bridge is source word + reading frame → molecular sequence →
conformational family → contact-dependent kinetics → product and successor. Fixed codon length,
codon surprisal under a declared source distribution, polymer contour length and fold-dependent
reaction work are different receivers on that chain. A synonymous amino-acid output does not
by itself authorize discarding the source/assembly conditions required by later receivers.

[established-bounded; source-inspected] The existing
[sequence/fold/kinetics return](2026-09-10_SEQUENCE_FOLD_AND_REACTION_CURRENT_MAKE_THE_CAUSAL_THOUGHT_CHAIN_CONCRETE.md)
already supplies a concrete separator: coarse contact bins are not dynamically closed, and equal
fold marginals can hide different fold/occupancy correlations and binding currents. The reaction
owner retains labeled catalytic emission as well as successor occupancy. This makes chain-link
interiors computationally relevant through actual later conduct, even when a present face agrees.
Those models retain their declared lattice/kinetic scope; they are not a calibrated DNA decoder.

## Verification and next use

[definition] Run from the repository root with the previous atlas available:

```sh
cargo run -p holonic-engine --example eta_generator_comparison --no-default-features -- .local/artifacts/hephaestus-zeta-information/atlas-12-36.ron .local/artifacts/hephaestus-zeta-information/generator-comparison.json 3
cargo test -p holonic-engine --example eta_generator_comparison --no-default-features
```

[established-bounded; process-audit] The comparison returned successfully and all three focused
tests passed: negative phase seam lifts, partial-word continuation and rejection of a prefix
with no code continuation. The former ζ-information application was rerun after extracting its
shared phase-signature helper, with its result compared against the retained return. No Lean
source, CUDA semantics or native model changed; the existing formal owners were recovered and
read rather than claimed as new proofs. The full
[compressed exact return](2026-09-11_zeta_information_receipts/generator-comparison.json.gz)
retains source configurations, constituents, interval differences, payload and exterior timings.

[definition] Next, return these reusable generator/receiver relations through the existing
operator-scoped factor/word construction, with decoder, source clock and retained remainders.
The present study exposes which analytic continuation resolves the requested face; it does not
yet make that choice through native HNN contextual formation. The code-length receiver can price
a proposed retained representation, while its future-receiver law decides which distinctions
that representation must preserve. The roadmap remains the sole construction order.
