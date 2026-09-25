# The music is in the holes: hearing multiplies by ζ, and a quasicrystal is a helix that never locks

[historical] On September 25 Brandon asked to take "hearing the music" from interpretation to
formal mathematics and into the elementary objects and the libraries. His request covered fractal
strings (Lapidus–Maier's "hearing the shape"), hearing versus listening, nullity, pain, the
intruder, the real part as a half-turn, lattices and transport tubes, lightning, spin and
quasicrystals, and the earlier golden-ratio work on RH. His own statements across the logs set the
subject:
- July 13, the first axiom: "What gets bigger the more you take away? A hole … The music is not in
  the sound itself, it is in the absence of sound in between the notes."
- September 11: gap statistics "are actually like causal residues".
- September 13: whether `φ = (φ−1)⁻¹` is related to ζ. The
  [golden reciprocal record](2026-09-12_GOLDEN_RECIPROCAL_JOINS_GAMMA_ZETA_AND_SPOKE_GAPS.md)
  answered with `L′(0,χ₅) = log φ`, `ζ_(ℚ(√5)) = ζ·L(·,χ₅)` and the Fibonacci dynamical zeta.
- September 14: an organism finds the differences "by settling its own differences with the
  environment and listening to where the noise isn't dying down."

Codex GPT-6 Sol derived and audited the program. Its corrections are kept below where they
change a claim.

## 1. A fractal string is the string of holes

[definition] A **fractal string** `ℒ = (ℓ_j)` is the family of lengths of the complementary
intervals (the holes) of a compact subset of an interval (Lapidus; Lapidus–van Frankenhuijsen,
*Fractal Geometry, Complex Dimensions and Zeta Functions*, second edition). Its normalized
frequencies are `k·ℓ_j⁻¹`, `k ≥ 1`; the Dirichlet eigenvalue of that mode is `(π k/ℓ_j)²`. It has
two counts:
- the geometric count `N_ℒ(x) = #{j : ℓ_j⁻¹ ≤ x}`;
- the spectral count `N_ν(x) = #{(j,k) : k ℓ_j⁻¹ ≤ x} = Σ_j ⌊x ℓ_j⌋`.

It has two faces: the geometric zeta `ζ_ℒ(s) = Σ_j ℓ_j^s` and the spectral zeta
`ζ_ν(s) = Σ_(j,k) (k/ℓ_j)^(−s)`.

[proved-derived; formal-checked] **The Cantor string is FractalPacking's sibling gaps.** The word
`w` of `FractalPacking` addresses the cell `descend w root` of width `3^(−|w|)`. Its sibling gap is
`(1/3)^(|w|+1)` (`FractalString.cantor_gap_length`), and depth `n` carries `2^n` such gaps
(`cantor_depth_gaps`). The first axiom's hole is literally this object: removing the middle
thirds makes the string of holes grow at every depth.
- [open] That these gaps exhaust the complement of the Cantor set needs the limit set, which
  `FractalPacking` does not construct.

## 2. Hearing multiplies by ζ; listening divides by it, exactly

[proved-derived; formal-checked] **Hearing is exact.** For a finite family of holes and any `K`
with `x ℓ_j < K + 1`,
`N_ν(x) = Σ_(k=1)^K N_ℒ(x/k)` (`spectralCount_eq_sum_geometricCount`).
- Every count of an infinite string at scale `x` sees only the finite set of holes with
  `ℓ_j ≥ 1/x`, so the finite statement is the whole count.
- The interval of length `ℓ_j` is the reflection half of a ring of circumference `2ℓ_j`. Its
  Dirichlet modes are that ring's reflection-reversing modes, and the harmonic `k` is their winding.

[proved-standard; formal-checked] **The spectral face factors through ζ.** For `Re s > 1`,
`Σ_j Σ_k (k/ℓ_j)^(−s) = ζ(s)·Σ_j ℓ_j^s` (`spectralZeta_eq_riemannZeta_mul_geometricZeta`). To hear
a string of holes is to multiply its face by the Riemann zeta.

[proved-derived; formal-checked] **Listening is exact at full resolution.** Under the same bound,
`N_ℒ(x) = Σ_(k=1)^K μ(k) N_ν(x/k)` (`geometricCount_eq_sum_moebius_spectralCount`, from the
general finite inversion `sum_moebius_smul_sum_mul`).
- Division by ζ is Möbius inversion, `1/ζ = Σ μ(k) k^(−s)`.
- The complete spectrum recovers the length multiset, multiplicities included.
- It does not recover where the holes were placed.
- As a Dirichlet series, the inversion holds only where `Σ μ(k)k^(−s)` converges absolutely. One
  cannot divide through a zero of ζ in the analytic chart (Sol's correction).

[proved-standard] **Where hearing loses a difference.** Take an ordinary fractal string of
Minkowski dimension `D ∈ (0,1)` whose boundary is Minkowski measurable with content `M`.
Lapidus–Pomerance (1993, *Proc. London Math. Soc.*) prove
`N_ν(x) = |Ω| x − c_D M x^D + o(x^D)`, with `c_D = 2^(D−1)(1−D)(−ζ(D)) > 0`.

The inverse spectral problem `(ISP)_D` asks the converse: for every such string, does a
nonoscillating second spectral term force Minkowski measurability? Lapidus–Maier (1995,
*J. London Math. Soc.* 52, 15–34) prove, for each `D ∈ (0,1)`:
- `(ISP)_D` holds **if and only if** ζ has no zero on `Re s = D`;
- hence RH is equivalent to `(ISP)_D` for every `D ∈ (0,1) ∖ {½}`;
- `(ISP)_½` fails, because ζ has infinitely many zeros on the critical line (Hardy, 1914).

The mechanism: a geometric complex dimension `ω` contributes a residue to the geometric count. In
the spectral count that residue is multiplied by `ζ(ω)`, so a zero of ζ at `ω` cancels that
oscillation (under the continuation and growth hypotheses of the explicit formulas).

[proved-standard] **The spectral operator** (Herichi–Lapidus 2012; book 2017; Lapidus 2015).
`𝔞_c = ζ(∂_c)` acts on `H_c = L²(ℝ, e^(−2ct)dt)`.
- For fixed `c ≥ 0`, its quasi-invertibility (invertibility of every spectral truncation) is
  equivalent to ζ having no zero on `Re s = c`. RH is equivalent to quasi-invertibility for every
  `c ∈ (0,1) ∖ {½}`.
- Ordinary invertibility is stronger. It fails for `½ < c < 1` unconditionally, by universality.
  RH is equivalent to ordinary invertibility for every `0 < c < ½`.

These are two criteria, not one phase transition.

[interpretation] **Nullity.** Nullity is Brandon's "when you cannot receive a difference". Here
it is the kernel of a declared receiver at its grain: a difference is null to a receiver when the
receiver's face cannot separate it.
- The zeros of ζ are exactly the dimensions at which the two-term asymptotic receiver cannot hear
  a geometric oscillation of that order.
- RH says that, among these asymptotic receivers, only the one at dimension ½ is deaf.
- [correction, Sol] The zeros are not the only nullity. Every finite-resolution or restricted
  receiver has its own kernel, and the exact count has none for the length multiset (§2 above).
  Nullity is always relative to a receiver and its grain.

## 3. Complex dimensions: a dilation and a rotation

[proved-derived; formal-checked] **Self-similar strings.** For ratios `r_i ≥ 0` and one gap `g`,
the holes at depth `n` contribute `g^s (Σ_i r_i^s)^n` (`selfSimilar_depth_sum`).
[proved-standard; formal-checked] Where `‖Σ_i r_i^s‖ < 1`, `ζ_ℒ(s) = g^s / (1 − Σ_i r_i^s)`
(`selfSimilarZeta_eq`).
[proved-standard] The complex dimensions are the poles of that closed form, the roots of the Moran
equation `Σ_i r_i^ω = 1`. Lean proves the pole equation only for the Cantor denominator.
- The Cantor string: `ζ_CS(s) = 3^(−s)/(1 − 2·3^(−s))` for `Re s > log 2/log 3`
  (`cantorStringZeta_eq`).
- Its complex dimensions are `ω_k = log 2/log 3 + 2πik/log 3` (`cantor_complex_dimensions`), with
  `2·3^(−D) = 1` (`cantor_moran_dimension`) and `½ < D < 1` (`cantor_dimension_mem`).

[proved-derived] `x^ω = x^(Re ω) · e^(i Im ω log x)`. **The real part of a complex dimension is a
dilation exponent. The imaginary part is a rotation in the log-scale chart.** The Cantor string's
real part is `log_3 2`, not ½.

[proved-standard] **Lattice and nonlattice.** Lattice ratios give vertically periodic complex
dimensions and persistent oscillation; nonlattice ratios give Minkowski measurability
(Lapidus–van Frankenhuijsen, Ch. 2–3 for the complex dimensions; Ch. 8, Theorems 8.23 and 8.36, for
Minkowski measurability).

[proved-derived; formal-checked] **The golden string**, Lapidus–van Frankenhuijsen's nonlattice
example. Its ratios are `2^(−1)` and `2^(−φ)`, with one first gap of length one. Where
`‖2^(−s) + 2^(−φs)‖ < 1`,
`ζ_GS(s) = 1/(1 − 2^(−s) − 2^(−φs))` (`goldenStringZeta_eq`).
- [proved-standard] Its complex dimensions solve `2^(−ω) + 2^(−φω) = 1`.
- [proved-standard] The Fibonacci convergents of `φ` give its lattice approximants, with common
  scale `2^(−1/q)`.
- [proved-standard] The book describes the quasiperiodic pattern of these complex dimensions; it
  gives no exact period.

The golden ratio enters as the ratio of two log-scales. This join, the golden record's
`L′(0,χ₅) = log φ` and the Fibonacci dynamical zeta `1/(1 − z − z²)` are three genuine, distinct
constructions. [correction, Sol] None of them implies anything about the zeros of ζ.

[definition; agent-inferred] **A self-similar navigator's resonating modes.** For a fractal
navigator whose words restrict by ratios `r_i`, the Moran roots are its resonating modes in scale:
- their real part is the dilation at which its word family fills scale;
- their imaginary parts are the log-periodic rotations it can ring with.

This gives the Holonic Compression row's "resonating modes of a fractal navigator" a formula for
the self-similar case. It is also the similarity dimension the
[framework survey](2026-09-22_THE_FRAMEWORK_SURVEY_BINDS_LOSS_MOMENTS_FRACTAL_GENERATORS_AND_ENCODING_TO_EXISTING_OWNERS.md)
listed as unformalized, recovered as a pole. Hausdorff dimension under the open-set condition
(Moran 1946; Hutchinson 1981) remains outside Lean.

## 4. The half and the pivot: three different halves

[proved-derived; formal-checked] **ξ is invariant under the Swing about ½.**
- `combReflection = AffineSwing.swing (½)` (`Zeta/Seam.combReflection_eq_swing`), and
  `completedRiemannZeta (swing ½ s) = completedRiemannZeta s` (`completedRiemannZeta_swing_half`).
- The conjugate reflection `s ↦ 1 − s̄` is that Swing after the conjugation mirror
  (`conjugateReflection_eq_swing_conj`). Its fixed set is the critical line (the existing
  `theSeamIsTheFixedLocusOfTheConjugateReflection`).
- A plain half-turn fixes only the point ½.

[proved-standard] **Mellin–Plancherel.** Put `g(y) = e^(y/2) f(e^y)`; then `∫|g|²dy = ∫|f|²dx`.
The unitary Fourier transform of `g` is the Mellin transform on `s = ½ + it`, with kernel
`x^(−½−it)` under the convention `ℳf(s) = ∫ f(x) x^(−s) dx` (with the kernel `x^(s−1)` the line
is read at `s = ½ − it`). The characters of the multiplicative group with respect to Haar measure `dx/x` are
`x^(it)`; the factor `x^(−½)` is the half-density correction for `dx`.

[proved-standard] **Spin.** `SU(2) → SO(3)` is a double cover. A rotation by `θ` acts on spin ½
through the half-angle, `exp(−iθ σ·n/2)`, so a whole turn is `−1 = e^(iπ)`. Berry (1984, *Proc.
R. Soc. A*): a spin eigenstate transported adiabatically around a closed circuit of field
directions acquires `∓Ω/2`. That phase is a holonomy on a declared circuit.

[interpretation; correction] **Brandon's question: "The real part is always a half turn? The
complex part is like the kind of face that is pivoting/swinging maybe?"**
- The functional equation's half-turn is the Swing about the anchor ½. The real part ½ is where
  that Swing and the conjugation mirror agree.
- On the critical line the imaginary part is a pure rotation `e^(−it log x)` in the log chart:
  the pivoting face.
- The real part is not always a half-turn. Mellin's ½ is a half-density weight; a complex
  dimension's real part is a dilation (`log_3 2` for Cantor); spin's ½ is a representation's
  half-angle.
- The missing term that would make any two of these halves one derivation is an intertwiner: a
  map carrying one declared action to the other and preserving phases (Sol). Another occurrence
  of ½ is not that.

## 5. Quasicrystals: a helix that never locks

[definition] **The carry word of a helix at a real rate.** A helix of rate `α` and phase `ρ`,
read against the integer section clock, winds `⌊nα + ρ⌋` sections by tick `n`. Its carry is
`s_n = ⌊(n+1)α + ρ⌋ − ⌊nα + ρ⌋`: the classical mechanical word. Owner:
`Geometry/MechanicalWord`.

[proved-derived; formal-checked] What it proves:
- **Helix = circle + carry.** The carries count the winding (`sum_carry`); each carry is `⌊α⌋` or
  `⌊α⌋ + 1` (`carry_mem`). At a rational rate `p/q` with rational phase `r/q` and tick `n ≥ 0`
  (`p, q, r, n` natural, `q > 0`), the real carry is the integer odometer's carry shifted by the
  whole turns `⌊p/q⌋` (`carry_rational_eq_phaseCarry`, joined to `PhaseCarry`).
- **A rational rate is a lock: a crystal.** Rate `p/q` makes the word periodic with period `q`,
  carrying exactly `p` per period (`carry_periodic_of_rational`,
  `sum_carry_period_of_rational`).
- **An irrational rate never locks: a quasicrystal.** An eventually periodic word forces a
  rational rate (`rational_of_eventually_periodic`, `eventually_periodic_iff`), so an irrational
  rate's address never closes (`not_eventually_periodic_of_irrational`).
- **The mediant bounds the period.** A lock strictly between two Farey neighbours recurs no
  sooner than their mediant's period (`period_ge_mediant_of_between`, joined to
  `PairResonance`).
- **Balance.** Any two factors of equal length differ in carries by at most one
  (`carry_balanced`).
- **The golden approximants** (joined to `Turn` §6). At rate `φ⁻¹` from phase 0, the first
  `F_(n+1)` ticks carry `F_n` for even `n` and `F_n − 1` for odd `n` (`sum_carry_golden_of_even`,
  `_of_odd`). The crystal of rate `F_n/F_(n+1)` carries exactly `F_n` over the same span
  (`sum_carry_golden_crystal`). The phase error is the golden clock residue, which alternates in
  orientation (`fib_succ_mul_inv_goldenRatio`).
  - The Fibonacci fixed word of `0 ↦ 01, 1 ↦ 0` is the word of rate `φ⁻²` at intercept `φ⁻²`.
    The rate-`φ⁻¹` word is its complementary coding up to intercept and shift, so the intercept
    must be stated.
- **Beatty positions.** For `0 < α < 1` at phase `0` the ones sit at `⌈k/α⌉ − 1` and the zeros at
  `⌊k/(1 − α)⌋` (`carry_eq_one_iff_beattySeq'`, `carry_eq_zero_iff_beattySeq`). Rayleigh's
  theorem (Mathlib) is the statement that the word partitions the ticks. At the golden rate these
  are the Wythoff pair `φ, φ²` (`carry_golden_iff`).

[proved-derived; formal-checked] **Lattices, tubes and window faces.** This is Brandon's "lattices
and transport tubes as pathways, but the faces of things constrain the pathways":
- The lattice points `(n,m)` in the strip `nα + ρ − 1 < m ≤ nα + ρ` are exactly `m = ⌊nα + ρ⌋`
  (`mem_tube_iff`). In the internal coordinate `nα − m` the strip is the window `[−ρ, 1 − ρ)`
  (`internal_mem_window_iff`).
- [correction, Sol] The strip alone projects onto all of `ℤ`. The quasicrystal needs the physical
  projection `n + βm`. Consecutive selected sites are spaced `1 + β s_n`, two lengths in the order
  of the carry word (`physicalSite_succ_sub`). Aperiodicity comes from `α` irrational; `β`
  irrational makes the projection injective on `ℤ²` (`physicalProjection_injective`).
- The lattice supplies the pathways and the window face selects them.
- [proved-standard] What a receiver hears from the result: regular model sets (compact window,
  boundary of measure zero) have pure point diffraction, with Bragg intensity proportional to
  `|1̂_W(k*)|²` at the projected dual lattice (Hof 1995, *Comm. Math. Phys.* 169; Schlottmann
  2000). The window selects the sites, and its Fourier transform is the heard face.
- [interpretation] The mutual constraint Brandon names, faces constraining pathways and pathways
  constraining what is heard, is this pair: window to sites, window transform to diffraction.
- [open] It becomes a Holonic derivation when an existing tube's restriction and receiver map are
  shown to equal these two projections.

[proved-standard] **Gap statistics of a rotation navigator.** For irrational `α`, the points
`{jα}`, `0 ≤ j < N`, cut the circle into gaps of at most three lengths; when three occur, the
largest is the sum of the other two (Steinhaus; Sós, Świerczkowski, Surányi 1958).
- With convergents `p_n/q_n`, errors `δ_n = |q_nα − p_n|` and `N = cq_n + q_(n−1) + r`, where
  `1 ≤ c ≤ a_(n+1)` and `0 ≤ r < q_n`, the lengths are `δ_n`, `δ_(n−1) − cδ_n` and their sum. A
  length with zero multiplicity is omitted; at `r = 0` two lengths occur.
- This is the exact answer to "gap statistics are causal residues" for a rotation navigator: the
  gaps are the continued-fraction residues.
- It does not make every causal residue obey a three-gap law.
- `φ = [1;1,1,…]` has the Fibonacci convergents and the infinite alternating Stern–Brocot address.
  Hurwitz's constant gives `liminf q‖qφ‖ = 1/√5`, the asymptotic sense in which the golden rotation
  is hardest to lock.
- [correction, Sol] Greene's golden last-invariant-circle criterion (1979) is a numerical and
  renormalization program, not a proved general theorem.

[proved-derived; correction] **The zeros of ζ are not a Fourier quasicrystal in the standard
sense.**
- Dyson (2009) suggested reading the explicit formula as quasicrystal structure. The Guinand–Weil
  formula relates the zeros to weighted prime powers plus archimedean and pole terms; it is not a
  pure Poisson equality between two combs.
- Olevskii–Ulanovskii (2020) characterize positive unit-mass Fourier quasicrystals on `ℝ`, which
  obey `μ(a,b) ≤ C(1 + b − a)`. The zero count grows as `T log T/2π`, even under RH.
- So "the zeros form a Fourier quasicrystal iff RH" is false for that definition. A renormalized
  notion would be a new definition [open]. Kurasov–Sarnak (2020) construct genuine Fourier
  quasicrystals from stable polynomials.

## 6. Lightning: where the field reaches a fractal frontier

[proved-standard] **Growth laws.**
- DLA (Witten–Sander 1981) attaches random walkers at their first hit.
- The dielectric breakdown model (Niemeyer–Pietronero–Wiesmann 1984) grows a boundary site with
  probability proportional to `|∇φ|^η` of the discrete harmonic potential.
- Hastings–Levitov (1998) give conformal-map growth.
- Kesten (1987) proves that planar lattice DLA has radius `O(n^(2/3))` after `n` particles, almost
  surely. The fractal dimensions of DLA and DBM are numerical estimates, not theorems.

[proved-standard; correction] **Harmonic measure.** Harmonic measure is the distribution of
Brownian first hits on a boundary: the boundary reading of the harmonic flux. Makarov (1985,
*Proc. London Math. Soc.* 51) proves it has measure dimension one on any simply connected planar
domain. This concerns the measure, not the frontier's support: however fractal the leader, the
flux concentrates on a dimension-one part of it.

[interpretation; open] **Lightning as deposition.** "The frontier grows where the field's flux
reaches it" reads as Deposition from the covector that actually reached that locus. It becomes a
derivation only with three missing terms:
- a harmonic boundary-flux carrier;
- the `η` constitutive relation;
- a receiver-to-deposition equality using only reached loci (`Objects/Deposition` owns the
  reached-locus rule).

Seeing and hearing lightning, the light and the thunder, are two receivers of one discharge. Their
maps from the channel's current are physical laws not yet charted here.

## 7. Hearing, listening, nullity and response, typed

[proved-derived; formal-checked] **What is heard now, and what any admitted future can
distinguish.** Let `F_now` be a receiver's current face and `F_fut` the future face map over
admitted receivers and words, including the empty word, with the current receiver among the
admitted ones. Then `ker F_fut ⊆ ker F_now`
(`Foundation/CausalRelevance.futureCollapsed_le_presentCollapsed`; atlas `info.relevance-kernel`).
- [correction, Sol] My draft typed "heard but not listened" as `ker F_fut ∖ ker F_now`. That set is
  empty: visibility to a future face is not listening.
- For nonlinear states the object is the equivalence relation `x ∼ y ⇔ F(x) = F(y)`, not a vector
  kernel.

[definition] **Listening** is typed by a separate reached-action map `A_R`: the difference
reaches a locus and changes its retained state there (its constitution entries, their carried
remainders, or its clock). Heard-but-not-listened is `ker A_R ∖ ker F_now`.

[proved-derived; formal-checked] **The HNN's deposit is an instance** (`HNN/LatticeDeposit`):
- **Heard and counted, not deposited.** At the deposit that advances a locus's clock to `m`, an
  entry whose update lies in the half-cell of the fine grain `2^(−L−k_m)` keeps its value and its
  carried remainder. The deposit releases the update whole, `e = Δ_i` (`carry_entry_below_grain`):
  the receipt reports the difference exactly, and that entry of the constitution does not change.
- The locus's clock still counts the deposit whenever its update is nonzero: an epoch at the
  locus's section. A deposit whose only nonzero entry lies below the grain therefore refines the
  grain of every later deposit. The difference reaches the clock component of `A_R` and none of the
  entry's components: it is counted, not deposited.
- **Listening refines with age.** The grain refines as the locus ages
  (`listening_grain_refines`), so an older locus deposits finer differences. The total it releases
  since its founding stays below `u/2` in magnitude (`release_bounded_since_founding`).

[proved-derived; formal-checked] **"If you can't listen to it then you can't respond to it."**
Equal standing forces every admitted future face to agree
(`Foundation/Standing.StandingLaw.futureAgreement_of_retain_eq`). A difference that never changed
the retained quotient cannot change any later release. Conversely, a differing response proves
the standing differed (`separating_future_refutes_the_standing`). At an HNN locus the retained
state includes the clock, so a below-grain difference that ticked the clock can still change
later deposits through the grain.

[proved-derived; interpretation] **"It dies with whoever heard it and listened, but they too can
propagate it."** For a Holarchy with admitted future receivers `r` and words `w`, the differences
null to that whole future are `⋂_(r,w) ker(r∘T_w)`: the natural grain's kernel
(`Compression/Core/FaceMap`, the
[natural-grain record](2026-09-25_THE_NATURAL_GRAIN_IS_THE_FUTURE_QUOTIENT_AND_REFLECTION_INTEGRATES_A_FRACTAL_PACKING.md)).
Deposition changes a constitution, and a later release carries a new difference to another
receiver. A word dies relative to that future exactly when its effect lies in the joint kernel. No
tape is implied.

[proved-standard; limitation] **"Relative to what you can't listen to because you cannot relate
to it, you are effectively nothing."**
- In finite dimension, `(ker F)^⊥ = im F*`: the coholons the face pulls back (what the receiver
  can read) are exactly those annihilating its nullity. In Hilbert spaces the image needs its
  closure. Listening still needs the reached-action map `A_R`.
- A zero pairing `⟨Ȟ_R|H⟩ = 0` is symmetric as a face.
- Response and causal influence are not symmetric: an active, dissipative or nonreciprocal
  interconnection can act in one direction only.

## 8. Pain and the intruder

[interpretation] **Pain** is "the difference is extreme and irrational, disruptive … changing
local configurations".
- A defensible receiver predicate compares received work, storage change, dissipation and active
  supply with a declared admissible capacity, over an interval, in the port ledger
  `Ė + P_out + D = P_in + P_active`.
- The disruptive face is a breach of the material limit, or a state that leaves no admissible
  control correction.
- "Irrational" should name the actual mismatch: no lock in the receiver's clock family, or a
  residual outside its ring or lattice.
- [correction, Sol] An irrational frequency ratio alone is not harmful. It can drive bounded
  quasiperiodic motion, while a rational lock can drive destructive resonance.
- Decision 22's lattice budget is a representation constraint, not a theorem about pain.

[proved-standard; interpretation] **The intruder as a fractal navigator.** A finite similarity IFS
with ratios `r_i` under the open-set condition has dimension `D` solving `Σ r_i^D = 1` (Moran
1946; Hutchinson 1981): the real Moran root of §3. A self-replicating intruder would be an
unadmitted navigator whose words found copies and change the local constitution. That reading
needs the navigator family, its source-to-offspring map and the demonstrated constitution change.
It is not a biological model of cancer.

[proved-standard; correction] **"Listening to where the noise isn't dying down."** For a passive
linear system `ẋ = (J − D)x` with `J* = −J` and `D ⪰ 0`, stored energy decreases at rate `⟨x, Dx⟩`.
Under LaSalle's hypotheses (1960), trajectories approach the **largest invariant subset** of
`ker D`. That subset is what the receiver's own dissipation does not kill; the harmonic summand of
the Hodge split is a different object. Reading it as "the music" is an interpretation until those
modes are shown invariant and distinguishable at the receiver.

## 9. What else fractals, rotation and quasicrystals offer

Brandon asked "What else aren't we doing?". Four standard results join existing owners once their
missing terms exist:
1. **Minkowski's `?(x)`** maps Stern–Brocot addresses to binary addresses and is singular. It is
   an exact address-to-face map for `HolonicsResearch/Geometry/Farey` and `navigator::address`. The missing term
   is the prefix-compatible map with its decoding fibre.
2. **Penrose tilings** arise by cut and project from `ℤ⁵` (de Bruijn's pentagrid, 1981), with
   golden inflation. They are the two-dimensional successor of §5. They need a typed projection,
   window, inflation and diffraction receiver; a golden ratio in a tile is not enough.
3. **The almost-Mathieu operator** couples an irrational rotation to a lattice Schrödinger
   operator. Its spectrum is a Cantor set for every irrational frequency and nonzero coupling
   (Avila–Jitomirskaya 2009, the Ten Martini problem). A rotation hears a fractal spectrum there,
   if a constitution is shown to equal the operator.
4. **Magnetic helicity** `∫A·B` measures linked flux. For thin tubes its cross terms are linking
   numbers times tube fluxes (Moffatt 1969). It joins linked tubes to a port current once the
   field, gauge and flux owner are declared.

## 10. What was built, and the receipt

[proved-derived; formal-checked] New and extended Lean owners, all without `sorry` or new axioms
(the first three in the `Holonics` library, the last in `HolonicsResearch`):
- `Foundation/FractalString`, registered in `Framework/Geometry`: the two counts, hearing,
  listening, the ζ factorization, self-similar strings, the Cantor string and its complex
  dimensions, and the golden string.
- `Geometry/MechanicalWord`, registered in `Framework/Geometry`: the carry word, locks, the
  quasicrystal, balance, the mediant, the tube and window, the physical projection, the golden
  approximants, and the Beatty/Wythoff positions.
- `HNN/LatticeDeposit`: `carry_entry_below_grain` (with `carry_entry_zero` now its corollary)
  and `listening_grain_refines`.
- `HolonicsResearch/Zeta/Seam`: the Swing about ½.

Receipt: `bash tools/lean_check.sh Holonics HolonicsResearch.Zeta.Seam` completes with 9,271 jobs,
with no new warnings; `cargo check --workspace --all-targets` passes.

[definition; agent-inferred] No Rust is added. No runtime consumer exists yet for a spectral
receiver, an irrational address, a diffraction receiver or a growth simulator, and unconsumed Rust
is deleted by rule. The consumer that will call the reached-action map `A_R` is the HNN's receipt
to adjoint-locus selection (`receiver/reception.rs`, `compression/face_map.rs`, `hnn`).

[open] Owed in #62:
- the three-distance theorem and Sturmian complexity `n + 1` (Morse–Hedlund 1940);
- Lapidus–Pomerance and Lapidus–Maier in Lean (Minkowski content, spectral counting, Tauberian
  machinery);
- Herichi–Lapidus (the weighted shift and its functional calculus);
- Mellin–Plancherel;
- regular-model-set diffraction;
- Makarov's theorem;
- the four receiver maps as commuting equations: gap to frequency face, projected site to
  diffraction face, harmonic flux to reached deposition covector, and spin circuit to any proposed
  ξ or Mellin action.
