# The receiver atlas separates what one face cannot

[definition] This is a construction contract subordinate to [THE_ROADMAP](THE_ROADMAP.md). It
states the formalization and engineering intentions for the receiver side of the shared carrier
defined in [THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md).
A receiver is a participating Holon, not a display.

[project-postulate] The atlas belongs to the
[general embedding composition](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-general-embedding-and-its-consuming-composition).
Music/chords, protein structures and Athena outputs exercise receiving maps of that construction.
Keep the producing incidence, material, phase and joint source/receiver evolution attached to
each reading. A chord is a source-and-receiver response; it does not replace the contact dynamics
that produced it or turn the embedding into one spectral fingerprint.

## The governing correction

[definition] No object has one intrinsic face. Isospectral objects exist; one global spectrum
cannot identify an arbitrary source. Identity is carried by the organized family of responses
under admitted probes:

```text
A(X) = { y_{u,R}(t) : u in admitted sources, R in admitted receivers, t >= 0 }
```

The design goal is therefore never "assign each object its chord". It is to give each object a
reproducible, source-accountable, actively explorable family of responses whose invariances and
separations correspond to declared mathematical relations. Active local probing distinguishes what
one passive global reading cannot.

## The causal chord

[definition] For a local linearization `x' = A_x x + B_x u`, `y = C_x x`, the receiver-relative
transfer object is

```text
H_x(s) = C_x (sI - A_x)^-1 B_x
```

It carries strictly more than the spectrum of `A_x`: poles give modal frequency and decay or
growth, the source factor `B_x` says which modes can be excited, the receiver `C_x` says which are
observable, and the residues weight each source-mode-receiver path. Writing `lambda_j = sigma_j + i
omega_j`, the chord is

```text
C_R(x) = { (omega_j, sigma_j, support_j, residue_{R,j}) }_j
```

[definition] For a non-normal `A_x` the eigenvalues omit large transient amplification. The
receiver then uses the resolvent `C_x (i omega I - A_x)^-1 B_x` or its singular modes, so that the
amplified pathways actually available between a source and a receiver are read, not only the
asymptotic modes. This matters wherever linearized fluid or interface dynamics appear.

## Rate as a receiver reading

[proved-derived] With a differentiable Hermitian positive metric `G(t)` and `x' = A(t)x + s(t)`,
`E_G = x* G x / 2` gives

```text
E_G' = Re(x* G s) + x* (A*G + GA + G') x / 2
```

The first term is supplied port work. The Hermitian form `Sigma_G = A*G + GA + G'` measures the
source-free change of that reading and may carry positive, negative and null directions at once.
For a discrete transport the corresponding form is `T* G_next T - G`; a discrete reflection is not
its own continuous generator. Under a constant invertible chart the form transforms by congruence.

[definition] Integrating, differentiating, concentrating, maintaining, exploring and releasing are
situated roles of one current at a declared metric, source, receiver and clock. They are not
intrinsic capacities, not two engines, and not fixed by an operator's name. The decision content of
`Sigma_G` — which directions contract, expand or stay neutral, and whether that survives a chart
change — is already owned exactly and executably by
[`inertia.rs:375`](../../crates/holonic-engine/src/inertia.rs) `inertia`, `:597` `congruence`, which
refuses singular charts by name, and `:728` `pullback_inertia_bound`, which returns the bound with a
basis of the degenerate directions. The intention is to connect that owner to the rate reading, not
to build a second one. The one-dimensional case is already discharged at
`Physics/PortEnergyHeat.lean:157`, whose second term is the moving-metric contribution.

[definition] A rise in a receiver intensity or a change in coarse information entropy is not heat.
Physical homeostasis additionally owes storage, incoming and outgoing power and a dissipation law.
`Physics/PortEnergyHeat.lean:74` proves storage plus heat against external port power for its
declared port; `Physics/TwoCellEntropyTransport.lean:22,39,59` proves the entropy reading for two
positive cells and one oriented flux and no further; `diffusion.rs` carries conservation and energy
refusals at `:469,476,499` and no entropy reading at all.

## The reflection algebra shared by seam and swing

[proved-derived] The graph projection `P_D` and its Swing `R_D = 2 P_D - I` distribute a one-port
current into two shares and recombine them, conserving the complete joint norm while individual
receivers gain and lose. Self-adjointness is a declared realization condition (`Dt = D^T`,
`K = I + D D^T`), not a consequence of arbitrary `D`;
`Computation/HolonicConstitutiveCirculation.lean:376` warns of exactly this and `:408` proves the
involution. Centering the conjugate reflection at one half gives `J = 2 P_+ - I`, the same species:
the invariant component is the seam and the anti-invariant component the transverse defect. The
coefficient one half is the normalization separating one current into those two exact parts.

[definition] `L*G + GL = G` is equivalent to `L - I/2` being `G`-skew. With `G` positive definite,
this implies every eigenvalue has real part one half. An indefinite conserving form does not
imply that placement. The converse requires semisimplicity; the usable statement is that a
positive definite `G` with `A` `G`-skew exists
exactly when `A` is semisimple with purely imaginary spectrum. The remaining obstruction to a seam
theorem is the absent spectral realization, not the rate algebra.

## Receivers to construct

[definition] **R1 — Causal chord owner. Returned.** Poles, residues, eigenvector support and
resolvent response as a first-class receiver over any object supplying a linearization, with its
source, excitation, transport path, approximation error and residual returned alongside every
audible or visible component. The owners are
[`causal_chord.rs`](../../crates/holonic-engine/src/causal_chord.rs) and
[`Foundation/CausalChord.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/CausalChord.lean),
built on `exact_linear`'s exact matrix algebra, `rational_polynomial`'s gcd, squarefree
decomposition, prime-lifting root census and Sturm isolation, `exact_value`'s Sturm certificate,
`lattice_gauge.rs:1039`'s exact spectrum and `inertia.rs:375,597`.

[proved-derived; formal-checked; implemented-exact] `H(s) = C adj(sI−A) B / det(sI−A)` is built by
one exact Faddeev–LeVerrier recurrence that keeps its intermediate matrices, so the adjugate and the
characteristic polynomial come from the same pass and are cross-checked against the existing
`exact_linear.rs:336` owner at every reading. Pole/zero cancellation is performed by exact gcd and
**returned**: every entry carries its raw numerator, the cancelled factor, and the reduced pair, and
the transfer matrix additionally carries `atlas_cancellation` — `det(sI−A)` over the lcm of the
reduced entry denominators — which is the population of modes no declared source excites or no
declared receiver observes. `ModeSupport` names the same modes structurally through their right and
left eigenvectors. Poles are named by exact squarefree factors with multiplicity as the index;
residues at rational poles are exact Laurent heads and at algebraic poles are elements of
`Q[x]/(factor)`, computed from the shift `D(x+u)` whose first `m` coefficients are certified to
vanish. The chart-change law `(TAT⁻¹, TB, CT⁻¹)` leaves the whole object fixed, in Lean
(`rebase_numerator`, `rebase_denominator`, `rebase_transfer`) and in Rust.

[proved-derived; implemented-exact] The repository had **no** half-plane root counter, so
`causal_chord.rs` founds one: axis roots with multiplicity from `gcd(P,Q)` for
`p(iω) = P(ω) + iQ(ω)`, left and right from the Cauchy index of the signed remainder sequence —
Routh–Hurwitz in its Sturm form — evaluated at a rational shift whose stopping condition
`left + axis + right = degree` is a certificate rather than a tolerance. For a symmetric operator
the same reading is Sylvester's signature and routes to `inertia.rs:375` instead; the two are held
to exact agreement. Real-root isolation is **not** refounded: it is
`exact_value::{IntegerPolynomial::distinct_root_count, AlgebraicRoot::isolate}` through
`rational_polynomial::rational_root_census`, rescaled from the monic companion.

[definition] **The counter now lives beside the root-counting owner (2026-09-18).** The signed
remainder sequence a Cauchy index reads *is* the Sturm chain, read at `±∞` instead of at a point,
so the polynomial-level routine moved to `rational_polynomial.rs` beside `exact_value::SturmChain`
and `rational_root_census`, and `causal_chord` re-exports `HalfPlaneCount`, `half_plane_count`,
`axis_root_count`, `cauchy_index` and `distinct_real_root_count` at their old paths, with their old
signatures and its own refusal species. The sequence is built over `Z` by
`SturmChain::from_pair`, whose sign discipline the index needs exactly: numerator and denominator
signs are **relative**, so the owner takes `signed_primitive_integer_form` rather than the
sign-normalizing one — normalizing one and not the other flips the index, and
`the_cauchy_index_flips_when_only_the_numerator_flips` pins that. The cross-check against
`inertia.rs`'s signature on symmetric operators is unchanged and now also runs on the measured M5
chord.

[established-bounded; measured] The non-normal clause is discharged concretely. The realifications
over `Q` of `[[i,1],[0,i]]` and `diag(i,i)` are 4×4, isospectral with characteristic polynomial
`(s²+1)²` and spectrum entirely on the imaginary axis; their minimal polynomials differ, and probed
at the Gaussian-rational point `s = i + δ` the defective resolvent's exact squared Frobenius norm
grows by more than `10³` per decade of `δ` while the semisimple one grows by less. **The resolvent,
not the spectrum, governs response**, and the exact resolvent at any Gaussian-rational probe point
is built by realifying `sI − A` over `Q`. The plan's lemma is corrected in both owners: the
provable direction and the counterexample to the naive converse are Lean theorems
(`gSkew_eigenvalue_re_eq_zero`, `seam_eigenvalue_re_eq_half`,
`semisimple_imaginary_has_conserving_receiver`, `jordan_has_no_conserving_receiver`), and
`conserving_receiver_space` solves `AᵀG + GA = 0` exactly and refutes positive definiteness for the
*whole* solution space by exhibiting a diagonal coordinate that vanishes on all of it. The direction
"`A` `G`-skew for some positive definite `G` ⟹ `A` semisimple" remains unformalized and is named as
such; it needs the spectral theorem through `G^{1/2}`, not rate algebra.

[established-bounded; measured] The governing correction is measured rather than restated. Two
Laplacian-cospectral non-isomorphic graphs on six vertices — degree sequences `(4,2,2,2,2,2)` and
`(3,3,3,2,2,1)`, shared characteristic polynomial `s⁶+14s⁵+73s⁴+176s³+192s²+72s` — are separated by
the response atlas at thirty-two of the thirty-six probe/readout pairs, including the driving-point
response at vertex `0`. The Lean theorem is `spectrum_does_not_determine_response`, and its positive
counterpart `full_atlas_determines_the_operator_fin_two` shows the complete atlas *does* determine
the operator. Applied to a real object: on the authenticated M5 `designed-free-rbx1.cif`, the
rigidity receiver's exact Jacobian on a declared five-residue RBX1 window, with the declared
elastic-network form `A = −JᵀJ` (overdamped relaxation at unit mobility) and a declared probe and
readout coordinate, returns extent 15, `rank J = 9`, spectrum `(left, axis, right) = (9, 6, 0)`
whose axis count is exactly `dim ker J = 6` computed independently by R4 as a rank, characteristic
degree 15, atlas denominator degree 10, five cancelled modes and residual exactly zero. That
measurement is `#[ignore]`d and its synthetic twin runs by default.

[established-bounded; measured] **`PoleReading::Certified` became affordable at degree fifteen
(2026-09-18).** It was not before: the certified reading isolates through `rational_root_census`,
whose descent started at the *absolute* Cauchy bound of the monic companion — a magnitude, and on a
characteristic polynomial built from a physical operator a magnitude is astronomically wider than
the roots. The census now descends from `rational_polynomial::certified_real_root_enclosure`: a
`k`-th root bound with the positive and negative sides counted separately, each returned only once
a Taylor shift proves `f(x + B)` coefficientwise nonnegative past it, and capped by the Cauchy
bound it replaced so it is never the worse of the two. On `x⁸ − 10¹²` that is a bound below `10³`
against a Cauchy bound of `10¹² + 1`. Measured on the same M5 chord in release: the `Named`
reading costs **2.37 s** and the `Certified` reading **2.64 s** — ten Sturm-certified real
isolations on the degree-ten denominator for eleven percent more — and the degree-fifteen
Routh–Hurwitz half-plane count costs **16.0 ms** and returns `(9, 6, 0)`, exactly Sylvester's
signature on the same symmetric operator.
`the_certified_chord_reads_the_same_m5_presentation` is that measurement.

[definition] **R2 — Acoustic receiver sharing one modal population. Returned.** A bank of causal
resonators `r_b' = (-gamma_b + i Omega_b) r_b + sum_m kappa_bm A_m(t)` consumes the same co-present
mode population the colour receiver consumes, so colour and timbre factor through one current and
one lineage. The checked mathematical owner is
[`Foundation/AcousticReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/AcousticReceiver.lean),
built on the causal-chord and colour-receiver contracts. The standalone
`holonic-engine::acoustic_receiver` Rust mirror and its PCM/WAV exporter were retired under R1
(issue #65) because no current Rust caller or example consumed them. Its method correspondence and
resource ceilings below document that historical implementation. The separate native Athena
acoustic charts under `holonic-life::native_intelligence::membrane_acoustic` are a different law and
remain in the R2 life-lineage audit.

[established-bounded; source-inspected] **What the colour receiver actually is, and where it
lives.** The plan named it only by its law; it is
[`dimensional_wave.rs`](../../crates/holonic-engine/src/dimensional_wave.rs), and it has three
separable parts. `ExactReceiverPhasePopulation` is **the type that carries the co-present mode
population** — a `BTreeMap<DimensionalWaveModeId, ExactComplexWaveCurrent>` of exact Gaussian
rationals plus a neutral `support_multiplicity` — and its `receive` sums same-mode currents *in
mode*, which is the one place relative phase reinforces or cancels. `ExactReceiverPrimaryDoctrine::transduce`
is the colour law: the three exact nonnegative quadratic phase responses
`(|Re A|², |Im A|², |Re A + Im A|²)` accumulated across the co-present modes after that
superposition, plus the neutral support response, and only then the saturating aperture
`P_j/(aperture + ΣP)`. The integer quantization is a **third** step further downstream still, in
`examples/arithmetic_dimensional_receiver.rs`, after the doctrine has run. The former R2 Rust
mirror consumed *that type* and called *that doctrine*; it founded no second population and
restated no colour law. The plan's phrase "and only then quantizes" therefore covers two
distinct nonlinearities in the existing colour receiver, the saturating aperture and the
integer readout, and the retired acoustic mirror respected both
orderings: superposition in the population, the bank linear over it, the one-dimensional pressure
projection last, and integer readout last. The retired standalone mirror's PCM/WAV exporter was an
exterior readout; it was not the separate native Athena acoustic chart.

[historical Rust implementation; current checked Lean law] The exact resonator bank,
its resource ceilings, PCM/WAV export and measurements below describe the standalone
`holonic-engine` mirror before its R1 retirement. They are scoped evidence, not current Rust
APIs or an alternate owner of the Lean law. The separate native Athena acoustic chart has
its own owner and scope.

[proved-derived; formal-checked; historical Rust mirror] **The exact discrete law is the Cayley map, not
an approximated exponential.** `exp(lambda t)` is not rational, so it is not the law. The declared
law is `z_b = (2 + h lambda_b)/(2 - h lambda_b)` with input gain `g_b = h/(2 - h lambda_b)` at a
declared rational step `h`, a **Gaussian rational** carried by `ExactComplexWaveCurrent` — the same
carrier the colour receiver's own currents use, so the two receivers share one arithmetic and not
only one population. It is **total**: `Re(2 - h lambda) = 2 + h gamma >= 2`, so the step needs no
guard and no branch. It **preserves stability exactly**:
`‖2 + h lambda‖² - ‖2 - h lambda‖² = 8 h Re lambda`, so the open left half plane maps into the open
unit disc and the axis onto the unit circle, decided by the sign of `gamma` alone with no tolerance
(`normSq_cayley_lt_one`, `normSq_cayley_eq_one`, `cayley_den_ne_zero`). The bank is R1's
**block-diagonal `Linearization`**: band `b` realified over `Q` as `[[-gamma_b, -Omega_b], [Omega_b,
-gamma_b]]`, excitation column `2m` mode `m`'s real quadrature and `2m+1` its imaginary one, and one
readout row carrying the pressure projection. Every audible component's source mode, excitation,
transport path, exact pole factor, multiplicity, residue, participating support, approximation error
and residual is therefore `ChordComponent` **itself**, obtained by calling R1; `AudibleComponent`
adds only which declared mode the excitation names and which band's factor the pole is.
`charpoly_realBlock` proves that factor is exactly `X² + 2 gamma X + (gamma² + Omega²)`, which is
what keeps a component's pole exact even when the `Omega` that produced it was read off an interval.

[proved-derived; formal-checked; historical Rust mirror] **The ordering is law, with both
counterexamples exhibited.** Superposition holds exactly through the whole bank from rest, at every
step, in the state and in the pressure (`run_add`, `superposition_holds_through_the_bank`), and the
pressure projection is itself linear (`pressure_add`) — so the projection is *not* where the ordering
matters. It matters at the two nonlinear readings, and each has a concrete counterexample:
`colour_does_not_distribute` doubles one mode's amplitude and quadruples its response where summing
two separate responses only doubles it, and the sharper face of the same fact is that two opposite
currents on one mode cancel to exactly zero response in the population while their separate responses
do not; `quantize_then_superpose_ne_superpose_then_quantize` exports two half-step pressures as
silence and their superposition as one step. What a quantize-first reading discards is the relative
phase — the cross-term of `|Σ z_j|² = Σ|z_j|² + 2 Re Σ_{j<k} conj(z_j) z_k` from the
[September 7 record](../../research/records/2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md).
The declared quadratic energy `Σ_b e_b ‖r_b‖²` is nonincreasing at zero input and strictly
decreasing wherever `gamma_b > 0` (`energy_advance_le`, `energy_advance_lt`), and that reading is
**tied** to the continuous rate form rather than asserted beside it: `rate_form` through
`causal_chord.rs` returns exactly `diag(-2 gamma_b e_b)` — the rotation part of each block cancels
against its transpose — and `inertia.rs:375` reads its signature, negative on each dissipating band
and null on each conservative one, in exact agreement with `‖z_b‖ < 1` and `‖z_b‖ = 1`.

[proved-derived; formal-checked; historical Rust mirror] **One lineage, and neither receiver refines the
other.** `joint_reading` takes one `ExactReceiverPhasePopulation` and returns both readings. Equal
colour does not imply equal timbre: exchanging which of two co-present modes carries which quadrature
leaves the colour triple *identical*, because the colour law accumulates its quadratic response
across modes and cannot see which mode supplied it, while a bank that consumes the two modes at
**unequal** `kappa` returns a different excitation and a different state (`metamer_sounds_different`).
The inequality is what does the work and the witnesses say so: Lean's `metamerBank` couples both
modes at `kappa = (1, 2)`, so the exchange sends the excitation `1 + 2i` to `2 + i`, and the Rust
`worked_bank` gives the two modes two different bands. A bank consuming them at equal `kappa` would
sum them and be exactly as blind to the exchange as colour is. Equal timbre does not imply equal
colour: current placed on a mode no resonator couples to is exactly invisible to the bank and plainly
visible to colour, and the bank **reports** that mode rather than dropping it
(`unison_looks_different`). A change of the population moves both (`population_change_moves_both`).
`Omega_b` is a **declared readout** whenever it comes from a spectrum: an irrational eigenvalue has no
rational value, so `RateProvenance::IsolatingIntervalMidpoint` carries the Sturm-certified interval
beside the rate and the constructor *checks* that the declared rate really is that interval's
midpoint. The plan's standing caution is stated in both owners and built into no gate: a bank with
positive decay settles, and that says nothing about whether what it settled onto is true.

[established-bounded; measured; historical Rust mirror] **Applied to a real object.** Driven by R3's exact grade-zero Hodge
spectrum of the authenticated M5 RBX1 window (24 residues, 8 Å aperture, unit metric, free boundary),
with the four lowest positive eigenvalues as bands, `gamma = 1/10` and step `h = 1/8` declared, and
one declared unit current per mode, the exact bank state after eight steps **separates all three
presentations** — at every one of the four band rates, at the exact final pressure and at the exact
declared energy, with no float anywhere. The lowest band reproduces R3's published gap through
`refine_spectral_gap` at width `10^-5`: `3368679/16777216 ≈ 0.200788` for the designed structure
against `451451/4194304 ≈ 0.107633` for the free prediction and `1813253/16777216 ≈ 0.108079` for the
CUL1-bound one. Cost: `≈ 60–83 s` per structure, dominated as R3 records by the naive Sturm sequence;
the whole measurement is one marked, ignored test and its always-runnable synthetic twin drives the
same bridge from the path-on-four and star-on-four spectra. An optional exterior WAV face is written
under `.local/artifacts/`, in integers, with its exact rational quantization residual bounded inside
half a step — and its length is a measured property of exactness rather than a choice: the state
gains one Cayley denominator's bit length per step and the pressure carries the product over bands,
so sixty-four samples return in seconds where two hundred and fifty-six take minutes. The exact
state is the object; the face is the thing that gets shortened. That measurement was then a **bound**
and not only a caution — see `STEP_WORK_CEILING` below.

[historical; proved-derived; implemented-exact at the recorded tree] **Five defects an authoritative review found in the returned
mirror, repaired, each with a regression test that separates the repair from its absence.**

- *Band attribution was aliasing.* `audible_components` attributed each component to the **first**
  band whose `characteristic_factor()` equalled the component's `pole_factor`. That factor is
  `X^2 + 2 gamma X + (gamma^2 + Omega^2)` and sees `Omega` only through `Omega^2`, so two distinctly
  named bands with mirror-signed rates carried the identical factor and both components were handed
  the first band's name. The repaired attribution was **structural**: the excitation column names the mode,
  the declared coupling names which blocks that mode drives at a nonzero `kappa`, and
  `AudibleComponent::originating_bands` returned exactly those blocks whose factor is the component's
  pole factor. `band` and the then-new `band_index` were `Some` exactly when that set is a single block;
  when one column drives two bands sharing `gamma` and `Omega^2` the reduced denominator carries the
  factor once, the pole is genuinely pooled, and the fields recorded `None` rather than picking one.
  `mirror_bands_are_attributed_by_block_and_not_by_polynomial_equality` builds the mirror pair,
  attributes each component to its own block, and then executes the superseded rule to exhibit that
  it returns the wrong name.
- *The step ceiling did not bound the work.* `STEP_CEILING = 2^16` bounds the **retained trace** and
  nothing else, while the exact state gains a whole Cayley coefficient's bit length at every step, so
  the arithmetic is quadratic in the length and a declaration far inside that ceiling could run for
  hours. `ResonatorBank::step_bit_length` projected the per-step growth from the declared step's
  own Cayley coefficients, `projected_run_work` formed `steps x projected state bit length` under
  checked arithmetic, and both `run` and `run_held` refused above the then-new `STEP_WORK_CEILING` of
  `2^25` bit-steps by the then-new `AcousticRefusal::RunWorkAboveCeiling`, **before** the loop.
  The measured basis is stated in the constant's doc and held to it by assertion: the worked
  two-band bank's widest Cayley coefficient is seventeen bits, its thousand-and-twenty-four-step run
  takes about five seconds and is admitted, and its two-thousand-and-forty-eight-step run takes
  about thirty-three seconds and is refused. The bound is on the work and not on the count — a bank
  declared over three-hundred-bit rationals is refused at a length the narrow bank passes.
  `a_run_under_the_step_ceiling_is_refused_by_the_projected_work`.
- *The export face's ceiling was bypassable.* `PressureExportFace` had fully public fields, so a
  caller could assemble one with an arbitrarily large `samples` vector and hand it to `wav_bytes`,
  going around the `SAMPLE_CEILING` refusal `export_pcm16` performs. The fields were made private with
  accessors; the type derived `Serialize` and not `Deserialize`, had no `Default`, no second
  constructor and no mutator, so `export_pcm16` was the only way a face could come into existence and the
  guarantee is a compile-level one rather than a checked one.
  `a_face_above_the_sample_ceiling_cannot_be_produced`.
- *One refusal named the wrong defect.* `wav_bytes` reported a sample-rate multiplication overflow as
  `ZeroSampleRate`, which it plainly was not; it gained its own
  `AcousticRefusal::SampleRateOverflowsByteRate` with an accurate message.
  `a_sample_rate_that_overflows_the_byte_rate_refuses_by_its_own_name`.
- *A Lean witness was weaker than its docstring.* `metamerBank` was documented as "both modes
  coupled" while its body was definitionally `workedBank`, with mode `1` uncoupled. It now couples
  both modes at `kappa = (1, 2)` and `metamer_sounds_different` is proved over that richer bank,
  with the supporting `bandGain_metamerBank_ne_zero`. Every theorem in the file depends on
  `propext`, `Classical.choice` and `Quot.sound` and on nothing else. The retired Rust module header
  carried a machine-readable correspondence table naming all forty-four declarations of
  the Lean owner against its then-current implementation, making a stale citation checkable at that revision.

[established-bounded; measured] **A finding the plan did not anticipate, about R3 rather than R2.**
R3's default isolation returns intervals certified to *separate* the eigenvalues, not intervals
narrowed to a declared width, and it exposes a narrowing owner — `refine_spectral_gap` — **only for
the spectral gap**. On the designed M5 window the gap's readout interval is `71/8388608 ≈ 8.5·10^-6`
wide while the second, third and fourth bands' are `71/128`, `71/32` and `71/128` — the third band's
readout interval is nearly as wide as the eigenvalue it names, `71/32 ≈ 2.22` against a midpoint of
`149/64 ≈ 2.33`. A midpoint readout of a non-gap
eigenvalue is therefore coarse, and R2 says so by carrying the interval beside every rate rather than
presenting the midpoint as a value. The concrete absent owner is a per-eigenvalue refinement on
`ExactHodgeSpectrum` with the same declared-width contract `refine_spectral_gap` already has; until
it exists, any consumer of a non-gap Hodge eigenvalue is consuming a separation certificate and not a
measurement. The separation reported above does not depend on it: the three presentations are told
apart by rates whose intervals are disjoint at the gap and by the exact state at every band.

[definition] **R3 — Hodge and spectral receivers on a complex. Returned.** `Delta_k = d_{k-1}
d_{k-1}* + d_k* d_k` over the incidence complex `physical_constraint_grading` returns, under a
declared metric and declared boundary conditions, exposing exact, coexact and harmonic components,
localized modes, multiplicity and spectral gaps. The owners are
[`hodge_receiver.rs`](../../crates/holonic-engine/src/hodge_receiver.rs) and
[`Foundation/HodgeReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/HodgeReceiver.lean),
built on `sheaf_diffusion.rs:274`'s coboundary and `:307`'s unit-metric Hodge operator,
`exact_linear.rs:987`'s metric adjoint,
`rebase_invariants.rs:440`'s Smith normal form, `lattice_gauge.rs:946`'s characteristic polynomial
and `exact_value::{IntegerPolynomial::distinct_root_count, SturmIsolationCertificate}`'s Sturm
count and isolation certificate.

[proved-derived; formal-checked; implemented-exact] **The metric is a declaration, and the unit
metric is one of them.** `MetricLaw::Unit` is written down like any other law; a non-positive
weight, an unnamed grade and an unnamed cell are each refused by name, because positive
definiteness is the single hypothesis every projection below rests on. The codifferential is
reached through `exact_linear`'s `metric_adjoint` and never written as a transpose, and
`unitMetric_codiff₀` is the one place the two coincide. Boundary conditions are `Free` (the
absolute complex) or `VanishingOn` a subcomplex, refused unless that set is closed under boundary.
The three-way decomposition is computed as exact `W`-orthogonal projections and **re-derived at
every reading**: the three components sum back, the three pairings vanish, and the harmonic part is
annihilated by `Delta_k`, by `d_k` and by `d_{k-1}*` separately. `dim ker Delta_k` is refused
unless it equals the Betti number the integer Smith normal form returns, and torsion is retained
beside it because the rational Hodge theory cannot see it.

[proved-derived; implemented-exact] **The spectrum is held, never approximated.** The
characteristic polynomial over `Q`, its squarefree decomposition keyed by multiplicity, every
rational eigenvalue completely, and every irrational eigenvalue as a polynomial plus a rational
interval plus its Sturm sign-variation certificate. `Delta_k` is self-adjoint and positive
semidefinite in the declared metric, so the spectrum is real and lies in `[0, tr Delta_k]` — that
bound, not the Cauchy bound of the coefficients, is what the isolation descends from, which is why
the isolation half of `lattice_gauge.rs:1039`'s census is replaced here while its rational half
(`rational_roots_by_lifting`) is used unchanged. The spectral gap is an `ExactInterval`, a point
interval exactly when the smallest positive eigenvalue is rational, and `refine_spectral_gap`
narrows the certificate to any declared width. Mode localization is the exact support and rational
participation ratio of the eigenspace where the eigenvalue is rational, and where it is not, the
exact statement that every eigenvector is supported inside the decoupled blocks of `Delta_k` whose
own squarefree characteristic factor changes sign across the isolating interval — no eigenvector is
written down and none is needed.

[established-bounded; measured] **The finding on the Open family.** On the worked presentation the
two bounds have *equal* Betti numbers and *different* characteristic polynomials: the refusing
member is a path with spectral gap exactly `1`, the admitting member is a filled triangle with
spectral gap exactly `3`. An open contact can therefore be invisible to homology and visible to the
spectrum, so a receiver reading only Betti numbers would report the open class as bookkeeping. It
is not, and neither bound may be taken for the answer.

[established-bounded; measured] On the authenticated M5 release, over the same 24-residue RBX1
window and 8 Å aperture `rigidity_receiver` measures, the clique complex separates the three
presentations by cell population and by cavity count — 70/59/50 one-cells, 79/56/32 two-cells,
`b_2 = 32/20/5` with `b_0 = 1` and `b_1 = 0` throughout — and the exact grade-zero spectral gap
separates all three as **disjoint rational intervals**: the designed structure at `≈ 0.20079`
against `≈ 0.10764` for the free prediction and `≈ 0.10808` for the CUL1-bound one. The two
predictions differ by under five parts in ten thousand and are still told apart exactly, with no
float anywhere.

[established-bounded; measured] **Cost, after the root-counting owner was consolidated (2026-09-18).**
The dominant cost *was* that `exact_value::sturm_sequence` was a naive Euclidean remainder sequence
over `Q` rebuilt at every count. It is now `exact_value::SturmChain`: a sign-tracked primitive
pseudo-remainder sequence over `Z`, built **once per polynomial** and counted against many times,
with each sign read by integer Horner on the homogenized member. Measured on the same three
structures, same machine, same readings:

| | before | after |
|---|---|---|
| 24-root isolation, release | 10.62 / 12.28 / 9.46 s | **3.72 / 4.05 / 3.14 s** |
| narrowing the gap to `10⁻⁵`, release | 1.22 / 1.18 / 0.91 s | **1.2 / 1.3 / 1.1 ms** |
| whole ignored measurement, debug | 644 s | **210 s** (70.9 / 79.6 / 58.4 s per structure) |

The readings are **unchanged**, which is the point: the isolating gaps are the same
`[7/64, 85/128]`, `[7/128, 11/64]`, `[49/512, 25/128]`, the narrowed certificates and the isolation
depths `11, 13, 13` are identical, and the ordering of the three presentations still holds. The
refinement's thousandfold drop is the cache alone — `refine_spectral_gap` used to rebuild a
rational remainder sequence per halving. The isolation itself is now
`rational_polynomial::isolate_against_chain`; this receiver supplies the `[0, tr Δ_k]` enclosure
positive semidefiniteness gives it and no longer carries its own descent. The spectral measurement
remains a marked, ignored test: three seconds per structure in release is a measurement, not a law,
and the default suite still takes the decomposition and Betti reading only.

[definition] **R4 — Rigidity receiver. Returned.** The constraint Jacobian `J_eta`, its nullity and
infinitesimal motions, `ker J_eta*` as the self-stress and reaction space, rigid clusters, hinges
and contact-removal sensitivity. The owners are
[`rigidity_receiver.rs`](../../crates/holonic-engine/src/rigidity_receiver.rs) and
[`Foundation/RigidityReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/RigidityReceiver.lean),
built on `physical_constraint_grading`'s family and on `exact_linear`'s existing exact `rank`,
`kernel_basis` and `cokernel_annihilator`.

[proved-derived; formal-checked; implemented-exact] The Jacobian is identified with the
differential by the exact expansion `F_c(q + t v) = F_c(q) + t (J v)_c + t^2 |dv|^2`, which needs
no analysis and no complete field, so the rational Rust matrix is the object the Lean owner
differentiates. Both rank-nullity identities are re-derived at every reading. The trivial motions
are **measured** as an exact rank of generators linearized about the configuration and cross-checked
against `d + d(d-1)/2 - (d-k)(d-k-1)/2` for `k` the affine span dimension: six for a spanning or
coplanar configuration in space, five for a collinear one, three for a coincident one. Nothing
assumes six. Contact-removal sensitivity is the self-stress support, not a second computation: a
constraint's removal moves `dim ker J` exactly when no self-stress is supported at it.

[established-bounded; measured] On the authenticated M5 release the receiver separates three
presentations of one RBX1 window sharply — rank 62 with `dim ker J = 10` and `dim ker J^T = 8`
for the designed structure, 53/19/6 for the free prediction and 50/22/0 for the CUL1-bound
prediction — so the Maxwell count is a strict bound on two of the three and exact only on the third.
An `Open` contact makes the constraint set plural in the same way it makes the complex plural, and
on a worked presentation the two bounds differ in motion dimension.

[definition] **R5 — Topological receiver. Returned.** Loops, cycles, linking and writhe where an
embedding exists, contact-community persistence, connected components, cavities and entanglement.
Knot-like structure is claimed only where cycles, linking, holonomy or nontrivial gluing actually
exist. The owners are
[`topological_receiver.rs`](../../crates/holonic-engine/src/topological_receiver.rs) and
[`Foundation/TopologicalReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/TopologicalReceiver.lean),
built on `physical_constraint_complex`'s exact squared-distance trichotomy, on
`rebase_invariants`'s integer Smith normal form, on `rigidity_receiver`'s `ExactConfiguration`
and on `ContinuingTower`'s `Tower`.

[proved-derived; formal-checked; implemented-exact] The aperture filtration is the exact
squared-distance Vietoris–Rips filtration: a cell's entry value is its exact interval, a higher
simplex's is the componentwise maximum over its edges, and **the order is decided by exact
comparison only**. Where two entry intervals overlap without coinciding the order is `Open` and is
**not** tie-broken: `open_order_pairs` returns every such pair and the persistence reading becomes
a family whose two bounds, `ByLowerBound` and `ByUpperBound`, are constructed, with a `Declared`
order refused when it contradicts a decided comparison. The work is admitted before it is done:
`ApertureFiltration::found` takes a declared `cell_bound` checked at the occurrence population, at
the `n(n−1)/2` candidate-pair count and at every founded cell, and `persistence` takes a declared
`work_bound`; each is refused by name rather than run unbounded. Persistence runs over a declared
field — `ℚ` exactly, or `𝔽_p` for a declared prime *decided* within `MODULUS_BIT_CEILING` (64
bits), with compositeness and an over-wide modulus each refused by name — and the **integral**
invariants are read beside it through `rebase_invariants_on`, so torsion is returned and
`field_dependence_primes` names the primes at which the fields must part. The six-vertex real
projective plane is the worked separation: `β_ℚ = (1,0,0)`, `β_{𝔽₂} = (1,1,1)`, `β_{𝔽₃} = (1,0,0)`,
integral torsion `[2]`. The grade-zero reading is computed twice — by the matrix reduction and by
an elder-rule union–find with the presented components retained — and the two death multisets are
required to agree: `grade_zero_agreement` computes both and returns `GradeZeroReadingsDisagree`
when they part, and `persistence` itself runs it before returning any reading at all, so the
requirement is enforced on the production path and not only where it is tested, and
contact-community persistence is a cross-check rather than one computation reported twice.
`persistence_with_grade_zero_agreement` returns the agreement beside the reading for a caller that
wants the communities as well. `ApertureFiltration`'s wire route is gated through `TryFrom`, which
re-runs the coherence its declared constructor enforces, and `contact_loops` looks its chain
positions up rather than indexing them, so a remounted filtration carrying a simplex label outside
its occurrence population is a typed refusal instead of a panic. `Filtration.toTower` fits the filtration to `ContinuingTower.Tower` **on the order
dual**, with `restrict` the inclusion; it does not fit on the index order itself, because `Tower`'s
transport is contravariant and a filtration's is covariant. `multiplicity_eq` proves the pairing is
an inclusion–exclusion of four persistent ranks, hence independent of the reduction, its pivots and
every tie-break inside it.

[proved-standard; formal-checked; implemented-exact] Linking is exact and **refuses rather than
perturbs**. The projection is `x ↦ (⟨w×e, x⟩, ⟨w×(w×e), x⟩)` with height `⟨w,x⟩`, all rational; a
crossing sign is `sgn det[t_over, t_under, w]`. A segment parallel to the direction, two projected
segments collinear and overlapping, a crossing at a segment endpoint, two strands at equal height,
a zero-length step and two curves sharing a place are each a typed `ProjectionDegeneracy` naming
the curves and segments. The linking number is returned as an exact integer and the two half-sums
are computed separately and required to agree at every reading, which discharges computationally
the one hypothesis the Lean owner cannot prove. Invariance under `w ↦ −w` and under positive
rescaling is proved; invariance under an arbitrary admissible projection change is an open `Prop`
and is tested across a declared candidate family. **The writhe is not an invariant and none is
claimed**: the projected writhe is returned per declared direction, and
`the_projected_writhe_is_not_projection_invariant` exhibits one exact polygon whose projected
writhes under two admissible directions are `1` and `0`.

[established-bounded; measured] On the authenticated M5 release, over a declared twenty-residue
RBX1 window at an eight-angstrom aperture and top grade three, the receiver separates the three
presentations by structure rather than by degree: the designed structure carries 52 contacts, 23
tetrahedra, **five** backbone loops closed by contacts (the longest spanning eight residues) and
two persistent 1-cycles at exact squared apertures `[11921841/500000, 26747387/1000000)` and
`[25734977/1000000, 13178189/500000)`; the free prediction carries 43 contacts, **two** loops and
two later cycles; and the CUL1-bound prediction carries 41 contacts, **no loop and no persistent
cycle at all**, so the receiver returns the typed `NoCycle` refusal and not a zero. No cavity and
no torsion appears in any of the three, and no pair of loops is entangled, so no knot-like claim is
admitted anywhere on this window.

[established-bounded; measured] A finding the plan did not anticipate: **the deposited decimal
precision, not the geometry, decides whether the aperture order is decided.** The intake's
coordinate box is one last place wide on each side, so the designed structure's three-decimal
deposition leaves 62 `Open` order comparisons and its two family bounds return *different*
pairings, while the two six-decimal predictions leave none. An exterior precision declaration is
therefore a receiver-visible property of a presentation and not bookkeeping.

[established-bounded; implemented-exact; formal-checked] A second finding of this receiver, **now
repaired at the owner**: `PhysicalConstraintComplex` carried only cross-component contact families,
so the intra-chain contact that closes a backbone loop had no presented family and this receiver
read its contacts from the filtration instead. The owner now founds the within-component family —
`found_within_component_contact_family`, at a caller-declared sequence separation `k ≥ 2`, exact
population `C(n − k + 1, 2)` (`withinComponentPairs_card`), disjoint from every cross family that
mentions the component (`withinPairs_disjoint_crossPairs`) — and `presented_contact_loops` takes
the loop reading from it with the filtration held to agreement, refusing by name on a disagreement
and preferring neither source. `contact_loops` remains the reading available when a caller holds a
filtration and no presentation. The covalent chain step is `EdgeProvenance::Polygonal` and stands
in every member of the apertured family, so an admitted intra-chain contact `(i, j)` closes a
`1`-cycle of `j − i + 1` one-cells whose cycle module is free of rank one
(`backboneContactCycle_is_cycle`, `segment_cycles_are_multiples`).

[established-bounded; measured] On the same three M5 twenty-residue windows at `k = 4` the two loop
readings agree exactly: five loops, two loops, and the typed `NoCycle` refusal. At the eight-
angstrom aperture the intra-chain open class is **empty** on all three presentations, at the
declared centres and at the deposited enclosures alike — a last-place-wide coordinate box moves a
squared distance by parts in a thousand and no intra-chain pair sits that close to `64`. The 62
`Open` comparisons above are comparisons of *entry order*, not contact classifications; deposited
precision changes which of two cells enters first and does not, here, change whether a contact
stands.

[definition] **R6 — Receiver width and release. Returned.** For a compatible family and horizon
`h`, the width `w_R(h) = diam { R(Phi_h(x,u)) }` over compatible states and admitted inputs. A face
is released when the width falls inside its **declared** tolerance; otherwise the lawful returns
are exactly `Hold`, `Widen`, `Ask`, `ReleaseCoarser` and `NoContinuationBridges`. The owners are
[`receiver_release.rs`](../../crates/holonic-engine/src/receiver_release.rs) and
[`Foundation/ReceiverRelease.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverRelease.lean),
built on `causal_chord.rs`'s `Linearization` as the first real dynamics, on `exact_linear`'s exact
matrix algebra, and on `receiver_atlas`'s preimage fibre and refinement order.

[definition] **Why R6 has its own owner rather than extending `receiver_atlas`.** The atlas
contributes exactly two things to this item — the preimage fibre and the refinement order — and
both are *cited*. What the width adds is dynamics: an exact `h`-step map, an admitted-input word,
an enclosure closed under exact linear images, a computed probe direction and a caller-declared
decision law. None of those is a chart, a transition or a gluing, and `receiver_atlas` has no place
to put them without becoming a second module under one name. R7, by contrast, **is** an atlas
statement and extends `receiver_atlas` in place.

[proved-derived; formal-checked; implemented-exact] **The three laws of the width.** `width_mono`:
a narrower fibre has no larger width. `width_nonExpansive_factor`: a coarser receiver `g ∘ R` whose
factor map never increases a separation has no larger width — and
`expansive_factor_increases_width` is the counterexample when it does, `q ↦ 2q` being a perfectly
lawful coarsening that strictly widens `1` to `2`. `width_eq_zero_iff` and
`releasable_at_every_tolerance_iff_width_zero`: width zero, constancy of `R ∘ Phi_h` on the fibre,
and releasability at every tolerance are one statement. The Rust owner does not assume
non-expansiveness: `FactoredReading::verify_non_expansive` checks it on the fibre actually read and
returns `FactorIsExpansive` with the pair and the coordinate that refute it.

[proved-derived; formal-checked; implemented-exact] **An event can be future-stable while its
timing is not.** The exact system is the rational doubling recurrence `x_{t+1} = 2 x_t` — a
`Linearization` with `state = [[2]]` — the compatible fibre is `{1/8, 1/4}` and the horizon is `3`.
The receiver "the event occurs by horizon 3" has width exactly `0` and is released at *every*
tolerance; the receiver "the time of the event" has width exactly `1` and is released at no
tolerance below `1`. One fibre, two receivers, two opposite verdicts, so there is no scalar
attached to the fibre that could have produced both answers.
`timeOfEvent_crosses` and `timeOfEvent_is_least` earn the second receiver's name — the returned
step really is the first step of the exact trajectory that reaches the threshold — and
`timingInsufficiency` is the exact `Foundation/Receiver.lean::ReceiverInsufficiency` witness that
the released coarse face does not determine the unreleased fine one.

[proved-derived; implemented-exact] **The enclosure is exact and `Ask` is computed, not guessed.**
The image of a box under an exact linear map is not a box but is an exact **zonotope**, so
`ExactZonotope` carries the centre and the generators over `Q` and `horizon_image` pushes a box of
compatible states and a box of admitted inputs through `Phi_h(x, u) = A^h x + Σ_{k<h} A^{h−1−k} B
u_k` with a fresh admitted input at every step. The sup-norm diameter is `2·max_i Σ_j |G_ij|`,
exact and linear in the generator count. `Ask` is the generator whose exact observation reduces
that diameter most, returned with its provenance — which state coordinate, or which input port at
which step — and with the exact width observing it would leave; over an enumerated fibre the same
question is answered over a declared candidate family of observations by the level sets they
induce. `ReleaseCoarser` walks a declared coarsening tower and **checks the factoring at every
step**, refusing with `CoarserDoesNotFactor` and the two fibre members that refute it, so a tower
that is not a coarsening is named as one; the search walks past the first step and returns which
step it stopped at (`the_coarser_search_walks_past_the_first_tower_step`).

[established-bounded; implemented-exact] **A finding, returned as a refusal rather than hidden.**
The *squared Euclidean* diameter of a zonotope is attained at a vertex of its generator cube, so an
exact computation would enumerate `2^k` sign patterns. The module therefore declares the sup-norm
as the exact norm on an enclosure and refuses the squared-Euclidean norm on one by name
(`NormNotExactOnEnclosure`); on an enumerated family both norms are exact and both are computed.
The generator count of an `h`-step image is `states + horizon·inputs`, formed with checked
arithmetic and compared against a declared ceiling **before** the first allocation. Bounding that
product alone is not enough and the owner says so: an admitted-input box with **no width**
contributes no generator at all, so the horizon itself carries its own declared ceiling, checked
first, and a test with a width-free input box is what would catch its removal. A hostile horizon is
a typed refusal and never a memory request. The horizon ceiling is not enough on its own either:
each step is `extent³` exact rational products and the extent comes from a caller-declared matrix,
so the carrier extent carries its own ceiling and the product `horizon · extent³` is formed with
checked arithmetic and compared before the first matrix is built. The declared coarsening tower's
step count and the declared candidate-observation count are bounded the same way, before the first
step or candidate is read.

[definition] **Release is receiver-relative and no global gate was built.** AGENTS.md: *a plural
fibre does not impose a universal certainty gate on generation.*
`release_is_receiver_relative_not_a_global_gate` is that clause proved — the same fibre releases
one receiver at every tolerance and fails another at every tolerance below `1` — and the library is
built to match it. `DecisionLaw` is a caller-supplied trait with no default and no blanket
implementation; `no_default_among_the_lawful_returns` exhibits two lawful laws with the same
tolerance returning different arms on the same reading. Nothing in this owner exposes a predicate
on a fibre that any generator is obliged to consult.

[proved-derived; formal-checked; implemented-exact] **Every lawful return that names a tolerance is
inside it, and `ReleaseCoarser` is one of them.** `release` refuses `ReleasedOutsideTolerance`,
`ProbeNotOffered`, `CoarserNotOffered` and `CoarserReleasedOutsideTolerance` by name: the coarser
arm recomputes `width ≤ tolerance` against the options' own declared tolerance rather than only
matching the offered `(receiver, width)`. A `CoarserRelease` carries the tolerance it was searched
under, and `LawfulOptions::assemble` refuses one searched under a different tolerance, so a coarser
invariant found inside tolerance `10` cannot be assembled against tolerance `1/2` and released
through two ordinary public calls (`a_coarser_release_searched_under_a_wider_tolerance_is_refused`).
`ReceiverWidth`, `LawfulOptions` and `CoarserRelease` carry private fields with accessors,
constructed only by `width_enumerated`, `width_enclosed`, `release_coarser` and `assemble`, and a
remounted `ReceiverWidth` is re-checked structurally through `TryFrom`. In Lean the `releaseCoarser`
constructor **carries** `coarserWidth ≤ tolerance` as an argument, so the arm cannot be formed
outside tolerance at all, and
`every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance` collects the
three arms that name a tolerance: `released` inside the law's own, `widen w` inside the `w` it
names (`ReleaseLaw.widenSound`), and `releaseCoarser` by the carried inequality.

[definition] **R7 — Separating atlas theorem. Returned.** For a declared bounded class, any two
inequivalent objects admit some probe, receiver and time at which their responses differ — when the
atlas is rich enough, and R7 is the statement of *which* atlas is. It extends `receiver_atlas` in
place: `ReceiverAtlas::admit_at` gives every chart a declared time, `separate` returns a
`Separator` naming the probe, the receiver and the time or the typed
`IndistinguishableToThisAtlas` with the charts it read and the charts the declared horizon bound
excluded, and `is_separating` scans a declared bounded class and returns either `Separating` or a
`NotSeparating` carrying an `AtlasInsufficiency` witness. In Lean the statement type is
`Foundation/ReceiverAtlas.lean::Separates`, with `Separates.mono` and `Separates.of_refinement`.

[proved-derived; formal-checked; implemented-exact] **(a) The exact linear systems of bounded
dimension are separated by the full probe atlas, at every `n`, at time one.**
`SeparatingAtlas.fullProbeAtlas` reads the Markov parameter `(A^k)[j][i]` at every excitation
coordinate, readout coordinate and time, and `fullProbeAtlas_separates` proves it separates the
whole class for every `n`. This **generalizes `full_atlas_determines_the_operator_fin_two` from
`Fin 2` to `Fin n`**, and the plan's expectation is corrected along the way: the degree-`n − 2`
cofactor expansion of `adjugate (charmatrix A)` that the `Fin 2` name records as missing is **not
needed at all** once the atlas is read through Markov parameters rather than through the adjugate,
because with `B = C = I` the `k = 1` parameter is `A` itself
(`identity_probe_determines_the_operator`, all `n`).

[proved-derived; formal-checked; implemented-exact] **And the classical `2n` bound is not about the
full atlas.** It belongs to the *declared-port* case. What is proved here is the Cayley–Hamilton
truncation: `pow_eq_aeval_modByMonic_charpoly` writes every `A^k` as the evaluation at `A` of
`X^k mod charpoly(A)`, of degree below `n`, and `markov_truncation` concludes that two generators
sharing a characteristic polynomial whose declared-port responses agree at every time below `n`
agree at *every* time — bound `n`, not `2n`, bought by the shared characteristic polynomial. The
full declared-port statement at `2n`, without that hypothesis, is stated as the open Prop
`MarkovTwoNSuffices` and is **not proved**: it needs the block-Hankel rank argument and the Kalman
decomposition, neither of which is in this file. The Rust mirror
`every_markov_parameter_is_a_combination_of_the_first_n` computes the truncation exactly at `n = 3`
for times `0..8`.

[established-bounded; formal-checked; implemented-exact] **(b) For finite complexes the R3 + R5
atlas is *not* separating, and that is the result.** The declared class is the finite
one-dimensional complexes on six occurrences with seven contacts and the declared atlas is what R3
and R5 actually supply for such a complex with no configuration: the grade-0 and grade-1 Hodge
spectra under the unit metric, the integral Betti numbers with torsion, and the persistence of the
dimension filtration. On the two Laplacian-cospectral non-isomorphic graphs of
`causal_chord.rs::cospectral_graphs_are_separated_by_the_response_atlas` — degree sequences
`(4,2,2,2,2,2)` and `(3,3,3,2,2,1)` — the whole atlas returns **one** reading: characteristic
polynomials `X⁶ − 14X⁵ + 73X⁴ − 176X³ + 192X² − 72X` at grade 0 and `X` times it at grade 1,
`β = (1, 2)`, no torsion, and the same eight-pair persistence diagram. The grade-1 agreement is
structural, not luck: for a one-dimensional complex `Δ₁ = d₀d₀*` and `Δ₀ = d₀*d₀` share every
nonzero eigenvalue with multiplicity, and the owner checks `charpoly(Δ₁) = X^{E−V}·charpoly(Δ₀)` as
an exact polynomial identity. The insufficiency is
`SeparatingAtlas.spectralTopologicalInsufficiency`, an exact
`Foundation/Receiver.lean::ReceiverInsufficiency`, and
`no_transformer_from_the_spectral_topological_reading` proves no receiver-to-receiver transformer
recovers the missing reading from the coarse one. **The richer receiver that does separate them is
R1's driving-point response**: its numerators at occurrence zero are `12 + 46s + 62s² + 37s³ +
10s⁴ + s⁵` against `12 + 52s + 73s² + 43s³ + 11s⁴ + s⁵`.

[established-bounded; measured] **A second finding the plan did not anticipate.** The persistence
*positions* of the two graphs differ and their persistence *diagrams* agree. Every occurrence
enters the dimension filtration at `0` and every contact at `1`, so the reduction's cell order is
an exact tie broken by address; the pair positions it returns are an artifact of that tie-break,
and only the multiset of exact birth/death **values** is the receiver's reading. A persistence
comparison taken on positions would have reported a separation that is not there.

[established-bounded; implemented-exact] **The contracts, as typed laws with a computed ledger.**
`AtlasContract` names the six — rebase equivariance, declaration independence, source
accountability, energy balance, the gluing law including interface coupling, and stability away
from bifurcation — and `contract_ledger()` returns twenty-four rows over R1, R3, R4 and R5 whose
seven `Satisfied` rows are **recomputed at every call** against the receivers' own owners. That is
enforced by the types and not by convention: `ContractStatus::Satisfied` carries a `Recomputed`
token whose only constructor is private to `receiver_atlas`, so the arm has no literal anywhere,
and every row that is not recomputed carries a `StandingStatus`, which has no `Satisfied` arm at
all. `ledger_entries()` publishes the table and
`the_contract_ledger_recomputes_every_satisfied_row` enumerates it generically, so a `Satisfied`
row cannot be added without a verifier behind it.

[established-bounded; implemented-exact] **Verified:** R1's rebase equivariance (the transfer
object is entrywise identical under `(A,B,C) ↦ (TAT⁻¹, TB, CT⁻¹)`, which is `rebase_transfer` and
is also stated in Lean as `causalChord_is_rebase_equivariant`), R1's source accountability (every
returned chord component carries its excitation port, transport path, lineage and an exactly zero
residual), R3's **declaration independence** — the metric-freedom of the harmonic dimension, which
is `Foundation/ReceiverAtlas.lean::DeclarationIndependent` and a different contract from rebase
equivariance — R3's energy balance (the three Hodge components recombine exactly and their three
pairings are exactly zero), R4's rebase equivariance under the exact rational rigid motion
`[[3/5,−4/5],[4/5,3/5]]` plus a translation with the trivial-motion dimension *measured*, R4's
source accountability through the self-stress support re-derived by actual row deletion, and R5's
source accountability, whose verifier takes a persistence reading on synthetic exact material and
runs `topological_receiver::grade_zero_agreement` on it. That last row's witness is true of the
production path and not only of the verifier: `topological_receiver::persistence` runs the
grade-zero cross-check before returning any reading at all, so a reading whose matrix reduction
and elder-rule union–find part is refused where it is taken.

[established-bounded; implemented-exact] **Refuted:** R5's rebase equivariance, because
`the_projected_writhe_is_not_projection_invariant` already exhibits one exact polygon whose
projected writhes under two admissible directions are `1` and `0`; and R5's declaration
independence, because the declared coefficient field decides the reading — the projective plane
separates `ℚ` from `𝔽₂` — and an `Open` aperture order makes the two order bounds two readings of
one presentation. Neither dependence is hidden: `integral_profile` returns the integral torsion
beside the field reading and `sublevel_family` returns both order bounds. **Unproved, with the
concrete open law named in each row:** the general receiver gluing laws with interface coupling.
The later two-media `holonic_chain` supplies a bounded R1 interconnection and R4 hinge reading;
these do not automatically discharge R7's general atlas-law declarations. R3's Mayer–Vietoris or
interface-coupled Laplacian and R5's persistence gluing remain open, with their distinct maps
connected in the [tube contract](THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md#the-governing-statements).
Also open: every
receiver's stability away from bifurcation, R1's energy balance, R3's source accountability, and
R3's rebase equivariance, because `hodge_receiver` declares no chart-change action on a graded
complex for a reading to be equivariant under. **Not applicable, with the reason named:** energy
balance for R4 and for R5, and declaration independence for R1 and R4, neither of which takes a
supplied structure beside the object it reads.

[established-bounded; measured] **The M5 reading, and the finding it produced.** Over the same
declared five-residue RBX1 window and 8 Å aperture the R1 chord measures, at the declared rational
probe point `s = 1` — never a pole, because `A = −JᵀJ` is negative semidefinite — the exact chord
responses `H(1)` of the three presentations are three rationals of about two hundred digits,
approximately `−0.0204126` for the designed structure, `+0.0113721` for the free prediction and
`−0.0323448` for the CUL1-bound one. The **width of the R1 chord response over that family** is
the exact rational of a 198-digit numerator over a 200-digit denominator, approximately
`0.0437169`, attained between the free and CUL1-bound predictions. Each receiver separates the
designed structure from both predictions — the designed window carries ten contacts, grade-0
characteristic polynomial `X⁵ − 20X⁴ + 150X³ − 500X² + 625X`, `(rank J, dim ker J, dim ker Jᵀ) =
(9, 6, 1)` and `β = (1, 6)` — and **only R1 separates the two predictions from each other**: at
this window they carry the same seven contacts, the same grade-0 characteristic polynomial
`X⁵ − 14X⁴ + 70X³ − 146X² + 105X`, the same `(rank J, dim ker J, dim ker Jᵀ) = (7, 8, 0)` and the
same `β = (1, 3)`, so R3, R4 and R5 are each blind at this aperture to a distinction the response
atlas sees exactly. That is a scope correction to the earlier R3/R4/R5 M5 readings, which separate
all three presentations over a twenty-to-twenty-four-residue window: **separation is
window-dependent, and the five-residue window is where the combinatorial receivers run out.** The atlas verdict is `Separating` over all three
pairs, and it is separating **because** R1 covers the pair the combinatorial receivers cannot —
which is the plan's thesis measured on a real object. The measurement is `#[ignore]`d at 28–30 s and
its synthetic twin, in which R3, R4 and R5 read one complex and only R1 separates, runs by
default.

## Engineering consumers

[definition] The receivers are constructed against objects that already exist: finite graphs and
cell complexes first, then physical constraint complexes, then proof states and field sections.
Sound and colour are guidance receivers and never truth oracles; formal certification, exact
arithmetic and numerical enclosure retain their separate roles, and a construction may reach an
acoustically stable equilibrium under an incomplete receiver while remaining false.
