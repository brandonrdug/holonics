# Every proper Lorentz map is a pair's move, three distances hold at every real rate, recurrence is a ledger with a deadline, and a level's sites are read from isolation, in Lean

November 18, 23:00 UTC. The fourth formalization pass of the day, over boxes of #410. Nine modules of
`lean/HolonicsResearch`, 376 declarations, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`, and five proofs elsewhere in the libraries moved off `native_decide`. Nothing
here touches the engine, a state or a run. The passes before it are
[the first](2026-11-18_THE_THEORYS_CORE_STATED_IN_LEAN_RINGS_CLOSE_AT_THEIR_LCM_AND_CARRIES_AT_THEIR_PRODUCT_IDENTITY_IS_THE_MODES_SHARED_READINGS_AND_A_PROOF_IS_THE_ORBIT_OF_A_FINITE_MAP.md),
[the second](2026-11-18_A_NUMBER_IS_THE_HOMOLOGY_OF_ITS_PLACES_A_LAW_OF_COMPOSITION_IS_ITS_CHARACTERS_A_SYMBOLS_WORD_OBEYS_KRAFT_AND_A_RETURN_MAPS_NECKLACES_ARE_COUNTED_IN_LEAN.md)
and [the third](2026-11-18_TWO_N_MARKOV_PARAMETERS_SEPARATE_SOURCES_A_SHIFTS_RATE_IS_ITS_SPECTRAL_RADIUS_A_PAIRS_MOVE_IS_A_PROPER_LORENTZ_MAP_READ_TWICE_AND_A_CHANGE_MOVES_ONE_CONTACT_A_TICK_IN_LEAN.md).

Refs #410, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/LorentzOnto` | The map `A ↦ (X ↦ Aᴴ X A)` of the third pass is onto: every real-linear map of `ℝ⁴` that keeps the Minkowski pairing, has determinant one and keeps the direction of time is the move of some `A` of determinant one, and exactly of `A` and `−A` (`lorentz_onto`, `image_lorentz`, `restricted_two_moves`). The construction is the polar one: the image `v` of the time axis has the closed-form root `B = herm((v + e₀)/√(2v₀ + 2))`, `B² = herm v`, positive definite of determinant one; what remains fixes time and is a rotation of space, a half-turn `i·herm b` about a bisector followed by a turn about an axis (`lorentz_polar`, `rotation_onto`). | the Einstein record of November 11, §11; `Physics/Spacetime/LorentzCover` | `lorentz.pair-move-double-cover` |
| `Aeon/Clock/ThreeDistance` | For arcs on any linear order with one rule of combination, every gap among the readings `0..n` is the first gap, the last gap, or the two combined (`gap_mem`, by moving a gap back one tick). So the gaps of `{iα}` take at most three lengths for every real `α` and every `n`, the largest the sum of the other two (`three_distance`, `three_distance_largest`); the same on `ℤ/q` for any step (`three_distance_ring`); and in the ratio chart with no logarithm, the neighbour ratios of `a^i/b^e` in `[1, b)` are the first, the last or their product (`three_ratios`), with the fifths at `N = 5` and `N = 12` as rulers. | `Aeon/Clock/CarryWord`'s closing paragraph; the records of September 25 and October 5 | `rotation.three-gap-shift` (new), `rotation.three-distance`, `aeon.three-distance-open`, `rotation.fifth-gap-recursion` |
| `Aeon/Clock/SturmianComplexity` | The carry word of a rate in `[0, 1)` has at most `n + 1` factors of length `n`, and exactly `n + 1` when the rate is irrational (`ncard_factors_le`, `ncard_factors_eq`); any word whose count of factors does not grow at some length is eventually periodic (`eventually_periodic_of_ncard_le`). | the same | `rotation.sturmian-complexity` (new), `rotation.mechanical-carry` |
| `Aeon/Production/Recurrence` | For a motion that keeps a measure and a measurable section `A`, with `S_n` the states not crossing `A` at epochs `1..n`: `Σ_(n<N) μ(A ∩ S_n) + μ(S_N) = μ(X)` at every `N`, from the keeping alone (`ledger`); so `(n + 1) μ(A ∩ S_n) ≤ μ(X)` (`rate`), and where `μ(X) < (n + 1) μ(A)` a state of `A` is back within `n` epochs (`exists_return_le`). In a finite measure almost every state of `A` returns (`measure_never_return`, from the ledger; Mathlib's infinitely-often form beside it), and Kac's lemma holds: `∫_A τ_A dμ + μ(never entering) = μ(X)`, equal to `μ(X)` for an ergodic motion and a section of nonzero measure (`kac`, `kac_ergodic`). The chain of a map of a finite set makes `Kac.survival` the indicator of `S_n`, so `Kac.kac_ledger` is this ledger's instance. On the circle the deadline is a clock's near-return: `(n + 1) ε > 1` gives `‖k a‖ ≤ ε` for some `1 ≤ k ≤ n`, and the least of the candidates gives Dirichlet's `‖k a‖ ≤ 1/(N + 1)` with `k ≤ N` (`dirichlet`, `dirichlet_real`, `rotation_recurrent`). | `Aeon/Production/Kac`; the near-return owners | `aeon.recurrence-deadline` (new), `rotation.dirichlet-from-ledger` (new), `aeon.kac-ledger`, `aeon.kac-grain-ratio` |
| `Compression/Landmark/SiteIsolation` | Over any ordered commutative ring, so at an integer grain: a place is a site of the first round exactly when its isolation is a section or more (`site_iff_isolation`, `isolation_eq_min`); a place of a section of news or more is a site; two sites of the claim stand a section or more apart; the first round shrinks as the section grows; the claim exists and is one set, and holds the first round (`claim_isClaim`, `claim_unique`, `site_subset_claim`); a site of the first round is in the claim of every passage that agrees within a section of it (`stable_core`); a stretch repeating with a period of less than a section holds no site a period or more after its start; a site stands at every section. Rulers over ℤ by `decide`. | the landmarks record of November 13, §5 | `code.site-isolation-landmark` |
| `HNN/PhaseChart` | At equal news with a section over six places, place `k` stands at phase `k/6` and the chart `1, cos 2πφ, sin 2πφ, cos 4πφ, sin 4πφ, cos 6πφ` is invertible: `H Hᵀ = diag(6, 3, 3, 3, 3, 6)`, a linear equivalence of the six places' rows in any real module (`chart_mul_transpose`, `chartEquiv`). A level founded with its prolongation at zero keeps every face of the field it is founded on (`founded_level_keeps_every_face`, citing `HNN/FoundingAtZero`); a covector at a place reaches the prolongation as an outer pairing and the level's state as zero at founding; the level's clock `τ_j` has strides of one or more between sites, `j ≤ τ_j`, and the strides in news sum to the news between the first anchor and the last. | the design record of November 13, §4.5 and §4.9 | `tower.level-phase-chart-orthogonal` (new), `tower.field-scale-packets`, `code.site-isolation-landmark` |
| `Foundation/InformationUpdate` | A comparison deposits `Λ′ = Λ + Hᵀ W H` and `η′ = η + Hᵀ W y`; any order and the stacked comparison give one pair (`depositAll_perm`, `precision_stacked`). With `P = Λ⁻¹` and `S = R + H P Hᵀ`: `Λ′⁻¹ = P − P Hᵀ S⁻¹ H P = (1 − K H) P`, `K = P Hᵀ S⁻¹ = Λ′⁻¹ Hᵀ R⁻¹`, and `μ + K(y − Hμ) = Λ′⁻¹ η′` (`covariance_form`, `gain_eq`, `mean_update`), proved from the one line `Λ′ (P Hᵀ) = Hᵀ R⁻¹ S`. The cost's slope is `Λ′ x − η′`, and over ℝ the stationary state costs least; one reading along `f` at precision `w` deposits `w f fᵀ`. | the learner record of September 27 | `deposition.information-form-update` (new) |
| `Compression/SternBrocotCode` | A word in the two shears `L`, `R` from `(1, 1)` is a positive rational in lowest terms and every positive rational is one word, by Euclid's subtraction (`value_bijective`, `path_node`, `node_path`); a run of `k` letters adds `k` times the other part; `\|w\| + 2 ≤ a + b`. The paths are no prefix code (`L` is `1/2` and a prefix of `LL`, `1/3`), and with any prefix-free code of the length written first they are one, with Kraft's sum at most one (`code_prefixFree`, `kraft_code`, through Mathlib's Kraft–McMillan). | the same | `code.stern-brocot-length-prefix` (new), `lock.euclid-address`, `lock.stern-brocot-generators`, `code.kraft-shannon` |
| `Compression/Landmark/AffineLandmark` | For an affine navigator (`c = 0`): infinity is fixed, the finite fixed point of `a ≠ d` is `b/(d − a)`, the paths scale about it by `a/d` (`iterate_sub_fixed`), and one of the multipliers `a/d`, `d/a` is below one in size exactly when the trace is not zero (`attracting_iff_trace_ne_zero`); convergence from every start for `\|a\| < \|d\|`, escape for `\|d\| < \|a\|`, a half-turn at trace zero, a shear at `a = d`. The sign law: for `D > 0` the sign of `p + q√D` is read from `p + q`, `p` and `p² − D q²` with no root taken (`sign_add_mul_sqrt`, `lt_iff_quadSign`). | `Compression/Landmark/FixedPoint` | `landmark.affine-fixed-point` (new), `ratio.quadratic-sign-law` (new), `landmark.attracting-repelling` |

The boxes of #410 these answer, by their opening words: "`PSL(2, ℂ) ≅ SO⁺(1, 3)`" (whole, as a bijection with the
reversed product law beside it); "The three-distance theorem and Sturmian factor complexity"; "Mathlib's
Poincaré recurrence joined to `Aeon/Production/Kac`"; "The level's law of sites" (the landmark clause, the
separation, the nesting of the first round, the claim, the stable core's forward half, the repeating
stretch); "The level's phase chart and founding"; of "Classical results cited in the learner record" the
Stern–Brocot prefix code and the information-form update; of "Möbius and quadratic landmarks" the affine case
and the sign law.

## 2. What the pass corrected

1. **The claim's non-nesting example was not on the clock of news.** The record of November 13 and the scope
   of `code.site-isolation-landmark` gave "news 3, 2, 1 arriving at 0, 1.5, 2.4". With `S_t = Σ c_v` that news
   arrives at 3, 5, 6, and its claims are nested (`record_example_is_nested`). The arrivals belong to news
   3, 1.5, 0.9: at the section 1 the claim keeps the first two places and at the section 2 the first and the
   third (`claim_not_nested`). The row carries the corrected figures.
2. **A place of little news is dark only under a hypothesis.** News 1, 5 at the section 5 has the first
   place a site. `faint_place_is_dark` asks that the place before carry at least its news.
3. **The repeating stretch is sharper than the row.** With the earlier-is-greater order, every place a period
   or more after the stretch's start is dark; sites stand only in the first period.
4. **The six-harmonic chart is orthogonal, with squares 6, 3, 3, 3, 3, 6.** The prolongation through the same
   harmonics returns the rows only after the weights `1/6, 1/3, 1/3, 1/3, 1/3, 1/6`
   (`prolong_weighted_moments`); the engine's learned `A` and `B` absorb them, and
   `tower.field-scale-packets` now says so.
5. **Three distances hold for every real rate.** `rotation.three-distance` and `aeon.three-distance-open`
   said "α irrational". The three values hold for every `α` and every `N`, coincident readings standing a
   whole turn apart; irrationality enters only where the lengths are named as continued-fraction residues.
   `aeon.three-distance-open` moves from `open` to `formal-checked` and keeps its id.
6. **The trace law of attraction fails as worded at `c = 0` with both fixed points finite.** There the
   navigator is the identity (`finite_form_fails`). The affine law reads the second fixed point at infinity,
   and `Compression/Landmark/FixedPoint` and `landmark.attracting-repelling` now say so.
7. **A length prefix serves, and is not the only recoding that does.** The learner record's "a prefix code
   only with its length coded first" is proved without the "only".
8. **Five proofs closed by `native_decide`, which rests on the compiler's evaluation (`Lean.ofReduceBool`)
   and which gate 4 does not read** (the review thread's finding of this evening: twelve in seven files).
   Replaced here: `Foundation/HigherDifferenceTransport.threeAxisSecondOrderAllocation_card` (`simp`),
   `Foundation/CoordinateSubsetReceiver.threeDimensionalMassExponent_univ` and
   `Fluid/NavierStokesReciprocalDifferenceRecurrence.quadraticDenominatorFace_card` (`decide`), and the two
   Maillet matrices of `Mathematics/NormRelation` (`decide +kernel`; plain `decide` stops at `ZMod`
   inversion, and their docstrings had said "computed by `decide`"). `bsd.norm-relation-falsifiers` now
   rests on the kernel alone. The seven left are lattice counts of the elliptic-curve family
   (`FamilyWaldspurgerGate`, `FamilyTunnellShimuraLift`, `FamilyTunnellHeckeIntertwining`), over boxes of up
   to 251³ points; their replacement is a reduced count, a double sum with a decided square test, and is in
   work. `bsd.shimura-lift-coefficients` rests on the compiled evaluation until it lands.

## 3. What each statement stands on, and the constructions beside it

- **The Lorentz map.** The bijection is of sets, with `Λ(AB) = Λ(B)Λ(A)` beside it; the group isomorphism on
  `PSL(2, ℂ)` is `A ↦ Λ(A⁻¹)` and is one packaging step. Uniqueness of the polar factors is the uniqueness of
  a positive square root.
- **Three distances.** The lengths themselves are the continued fraction's: `δ_n = |q_n α − p_n|` and the
  counts `N = c q_n + q_(n−1) + r`. The construction is `gap_mem`'s two special gaps read at the convergents
  of `Aeon/Clock/NearReturn`.
- **Sturmian words.** The count at a rational rate is `min(n + 1, q)`, by the same arcs with coincident cuts.
- **Recurrence.** The deadline is the pigeonhole of the ledger and names no tick; the ticks that realize a
  clock's returns are the convergents. Abramov's formula for a general ergodic motion is the same ledger
  applied to the word of one coarse epoch, as `Kac` does on a finite chain. A torus of several clocks has the
  ledger with a product of arcs.
- **The law of sites.** The stable core's converse is a construction at a real grain: give each earlier place
  less news than the site (at an integer grain with one unit of news there is no such value, so the converse
  is a statement over a divisible ring). The `3σ` stride of the claim and the share `c̄/(2x + c̄)` of places
  with isolation `x` or more are the record's and stand on the definitions.
- **The phase chart.** General `n` is the discrete Fourier basis on `n` phases with the same weights; a
  winding interior (strides of several sections) reads the harmonics off the equal-news grid.
- **The information form.** No probability law is stated; the Gaussian reading is the chart in which `Λ` is
  an inverse covariance. The cost is stated doubled, so it holds over any field.
- **Stern–Brocot codes.** The path's length as the sum of the partial quotients less one stands on the run
  lemmas; the join to continued fractions is the lock address's box.
- **Affine landmarks.** Infinity is read in the chart `w = 1/z`; no projective line is built.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the nine modules by name with the eight others this change touches
(`Holonics.Compression.Landmark.FixedPoint`, `Holonics.Aeon.Clock.CarryWord`, `Holonics.Aeon.Production.Kac`
and `HolonicsResearch.Physics.Spacetime.LorentzCover` for their docstrings;
`Holonics.Foundation.HigherDifferenceTransport`, `HolonicsResearch.Foundation.CoordinateSubsetReceiver`,
`HolonicsResearch.Fluid.NavierStokesReciprocalDifferenceRecurrence` and
`HolonicsResearch.Mathematics.NormRelation` for their proofs): `Build completed successfully (8829 jobs)`, exit 0, no declaration elaborated with `sorry`. Projected under 15 minutes from the
single-file checks (5 to 13 s a module) and the foundation modules' rebuild, deadline 30 minutes, measured
58 s of wall time on four cores shared with four workers' checks; peak resident set not read. The
library's aggregator imports the nine modules; the whole research library was not rebuilt.

The check ran on a cloud host at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision, for the reason the first pass's record gives (`agent-inferred`).

Four workers on disjoint owner paths wrote eight of the modules (the information form, the Stern–Brocot code
and the affine landmark; the Lorentz map; the sites and the phase chart; the three distances and the Sturmian
count), and the lead wrote the recurrence ledger and the five replacements; each file was re-checked by the
lead before the gate, and every `L:` owner added to the atlas was read against its module's declarations.
