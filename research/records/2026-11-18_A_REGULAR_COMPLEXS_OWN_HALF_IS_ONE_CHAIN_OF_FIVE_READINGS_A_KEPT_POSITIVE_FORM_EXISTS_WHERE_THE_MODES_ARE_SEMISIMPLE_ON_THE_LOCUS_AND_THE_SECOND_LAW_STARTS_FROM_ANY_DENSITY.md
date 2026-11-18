# A regular complex's own half is one chain of five readings, a kept positive form exists where the modes are semisimple on the locus, and the second law starts from any density

November 18, 2026, 22:41 to 23:40 UTC. Derivations with their Lean proofs and a host ruler, the second set of the
evening. Nothing ran on a learner or on the card, and no line was touched. Each paragraph carries its grade: `tree`
(read in this repository), `from training` (a result of the literature, named) or `agent-inferred` (this record's
join). A statement cited as Lean names its module and theorem; every such module builds with no `sorry`, no added
axiom and no `native_decide` (§11). Refs #410.

This record continues [the first set](2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_A_FINITE_COMPLEX_HAS_ITS_ZEROS_AND_COUNT_IN_LEAN_COUPLED_LOCKS_KEEP_THE_CIRCLE_TWO_TORIS_INDEX_THEOREM_IS_A_NORM_AND_BELOW_REYNOLDS_ONE_THE_COUNT_DECIDES.md)
(called "the first record" below), whose mechanism it keeps: a move with a reversal builds a form the move scales;
where the form is positive every mode sits at the half, and its negative squares count the modes that left.

Owners touched: `receipt.seam-g-skew`, `receipt.semisimple-conserving-receiver`, `key.scaled-form-places-modes`,
`trace.regular-norm-form`, `rh.finite-weil-criterion`, `trace.ihara-zeta`, `trace.prime-cycle-half-rank`,
`trace.power-cyclic-words`, `ns.laminar-class-reynolds`, `aeon.driven-jarzynski-crooks`, `floor.landauer-erasure`.
Eight atlas rows enter, one row is regraded and six gain Lean owners (§11).

Receipts: [`second_ruler.py`](2026-11-18_A_REGULAR_COMPLEXS_OWN_HALF_IS_ONE_CHAIN_OF_FIVE_READINGS_A_KEPT_POSITIVE_FORM_EXISTS_WHERE_THE_MODES_ARE_SEMISIMPLE_ON_THE_LOCUS_AND_THE_SECOND_LAW_STARTS_FROM_ANY_DENSITY_receipts/second_ruler.py),
four sections, every check an assert, all pass, 47 seconds on one thread of the cloud container's host (integer and
rational arithmetic for the prime cycles and the three faces, double floats for the spectra and the Li numbers,
printed as the ruler's readings); its output
[`second_ruler_output.txt`](2026-11-18_A_REGULAR_COMPLEXS_OWN_HALF_IS_ONE_CHAIN_OF_FIVE_READINGS_A_KEPT_POSITIVE_FORM_EXISTS_WHERE_THE_MODES_ARE_SEMISIMPLE_ON_THE_LOCUS_AND_THE_SECOND_LAW_STARTS_FROM_ANY_DENSITY_receipts/second_ruler_output.txt)
and the guesses fixed before it ran,
[`guesses.txt`](2026-11-18_A_REGULAR_COMPLEXS_OWN_HALF_IS_ONE_CHAIN_OF_FIVE_READINGS_A_KEPT_POSITIVE_FORM_EXISTS_WHERE_THE_MODES_ARE_SEMISIMPLE_ON_THE_LOCUS_AND_THE_SECOND_LAW_STARTS_FROM_ANY_DENSITY_receipts/guesses.txt)
(stamped 23:02:42 UTC by `date -u`).

## 1. The frame

The first record proved, in six charts, that a positive form built from a move and its reversal places the modes at
the half. Three converses stood there as one direction or as a derivation by hand: that such a form exists only where
the motion is semisimple on its locus (the first record's §3.3 cited `Foundation/CausalChord` for the generator's
form, whose header names that direction as not formalized); that its negative squares count the modes that left (the
first record's §4.4 and §6.2, by hand); and that the count's bound at every length forces the half (the first
record's §5.3 proved the bound from the half only). This record proves the three (§3 to §5) and joins them on one
complex into one chain of five readings (§6). It then proves the product side of the complex's zeta (§7), carries the
fluid's laminar class to every mode at once and proves it stable (§8), and starts the second law from a density that
is not at equilibrium, with Landauer's bound and the price of a quotient as corollaries (§9).

## 2. What the tree held

`tree`, read before each statement was written.

- `Foundation/CausalChord`: the rate form `Σ_G = A*G + GA` (`rateForm`), the implication from `G ≻ 0` and `Σ_G = 0`
  to an imaginary spectrum (`gSkew_eigenvalue_re_eq_zero`), the seam at `Re = 1/2` (`seam_eigenvalue_re_eq_half`),
  the certificate of a diagonalized generator (`semisimple_imaginary_has_conserving_receiver`) and the Jordan block
  with no conserving receiver (`jordan_has_no_conserving_receiver`). Its header: the direction "`G`-skew for some
  positive `G` implies semisimple" is not formalized there and needs the spectral theorem transported through
  `G^{1/2}`. Atlas `receipt.seam-g-skew`, `receipt.semisimple-conserving-receiver`. #410's box "the moving metric's
  spectral reading: the implication needing `G ≻ 0` and its converse needing semisimplicity".
- `Holon/Inertia`: the indices `posIndex` and `negIndex` of a symmetric form, their invariance under congruence and
  the pullback bound (atlas `inertia.pullback-bound`), with no value computed on a diagonal.
- `Compression/Landmark/NecklaceIntegrality` (merged the same evening by the Lean thread): the closed walks of a
  matrix of natural numbers, their necklaces, `tr Mⁿ = Σ_(d∣n) d·p_d`, the Möbius form and the horizon-truncated
  Euler product (atlas `trace.power-cyclic-words`); `Compression/Landmark/PrimitiveCycle` the case of a map;
  `Aeon/Production/Zeta` the zeta of a transfer as `exp(Σ tr Tⁿ uⁿ/n)`. Atlas `trace.ihara-zeta` held Ihara's
  product as `proved-standard` with a host owner only.
- The first record's modules: `Landmarks/RegularComplexZeros` (zeros, trace formula, one direction of the count),
  `Zeta/FiniteWeilCriterion`, `Landmarks/RegularGraphNormForm`, `Fluid/NavierStokesLaminarClass`,
  `Fluid/NavierStokesGalerkinInstance` (the finite comb and the truncated fluid), `Aeon/Production/Jarzynski` (the
  work equality and the second law from an equilibrium opening). `Aeon/Production/PathReversal` holds A6.
- Atlas `floor.landauer-erasure` (`proved-standard`, no Lean owner) and `standing.erasure-is-merge`.

## 3. A positive form that the motion keeps exists where and only where its modes are semisimple on the locus

`agent-inferred` for the joins, the theorems classical (`from training`: the spectral theorem for a Hermitian
matrix, Lyapunov's conserved quadratic form, Cayley's transform). Lean `Coupling/MovingMetricSpectral`.

**3.1 The statements.** Over `n × n` complex matrices, with a chart `S` invertible and modes a diagonal `d`, the
shapes of `CausalChord`:

- a positive definite `G` with `A*G + GA = 0` exists if and only if `A = S·diag(d)·S⁻¹` with every `Re d_i = 0`
  (`gSkew_iff_imaginary_chart`);
- a positive definite `G` with `A*G = GA` exists if and only if the same holds with every `d_i` real
  (`gSelfAdjoint_iff_real_chart`);
- a positive definite `G` with `L*G + GL = G` exists if and only if every `Re d_i = 1/2` (`seam_iff_half_chart`);
- for `q > 0`, a positive definite `G` with `B*GB = qG` exists if and only if every `|d_i|² = q`
  (`similitude_iff_circle_chart`);
- for a real `A`, a real symmetric positive definite `G` with `AᵀG + GA = 0` exists if and only if `A` read over `ℂ`
  has an imaginary chart (`real_gSkew_iff_imaginary_chart`): the real part of a complex receiver is a receiver.

Under the hypotheses of the first, `(A − μ)²v = 0` gives `(A − μ)v = 0` (`no_jordan_block_of_gSkew`), and the tree's
Jordan block has no imaginary chart (`jordanI_has_no_imaginary_chart`).

**3.2 How.** A positive definite `G` is a Gram form `C*C` with `C` invertible (`exists_unit_conjTranspose_mul_self`,
`C = √Λ·U*` from `G`'s own spectral theorem). Then `A*G = GA` says `CAC⁻¹` is Hermitian, which has a unitary chart with
real modes, and `A` has the chart `C⁻¹V`. The skew case is `iA`, and the seam is `L − 1/2`. For the group form, with
`B*GB = qG` put `W = B/√q`; a real `t` with `P = (t − i) − (t + i)W` invertible exists because the spectrum is finite,
and `H = i((t − i) + (t + i)W)P⁻¹` is `G`-self-adjoint, so `W` has a chart with modes `(t − i)(h − i)/((t + i)(h + i))`
of modulus one. Mathlib at this pin has no spectral theorem for normal matrices, which is why the Cayley transform
carries the unitary case to the Hermitian one.

**3.3 Reading.** `agent-inferred`. `G` is a receiver's metric. Against a receiver, a rate splits into a skew turn and a
self-adjoint boost (the Swing's split). The theorems say when a receiver exists against which the motion is all
turn: if and only if the motion is semisimple with its modes on the axis. A mode off the axis, or a Jordan block on
it, is a motion that no positive receiver reads as conserved; it is not a matter of finding the receiver. With the
first record's §3 (a positive scaled form places every mode at `|α|² = q` with no Jordan block), the group form is
now an equivalence: a positive scaled form exists if and only if the move is semisimple with its modes at the half.
That is the parametron's certificate `M_TᵀGM_T ⪯ ρ²G` in its equality case, with existence decided by the spectrum.

## 4. The negative squares count the modes that left

`from training` for Sylvester's law of inertia (1852); the counts `agent-inferred` in the first record, now Lean
`Holon/InertiaCount`.

**4.1 Sylvester on a diagonal.** Over any linearly ordered field, `n₊(diag d) = #{d_i > 0}` and
`n₋(diag d) = #{d_i < 0}` (`posIndex_diagonal`, `negIndex_diagonal`), and a congruence `PᵀAP = diag d` with `P`
invertible gives those counts for `A` (`posIndex_of_congr_diagonal`, `negIndex_of_congr_diagonal`). The proofs are two
bounds by linear maps (`posIndex_le_card_of_ker_nonpos`, `card_le_posIndex_of_pos`).

**4.2 The regular complex's norm form.** `K = [[q, A/2], [A/2, 1]]` on `V ⊕ V` has quadratic form
`q‖a‖² + ⟨a, Ab⟩ + ‖b‖²`, the tree's `normForm` (`quad_normMatrix_eq_normForm`). The eigenvector chart on both halves
and then the shear `b ↦ b + λa/2` make it `diag(q − λ_i²/4) ⊕ 1` (`normMatrix_congr_diagonal`). So
`n₋(K) = #{λ_i² > 4q}` (`negIndex_normMatrix`), `n₊(K) = |V| + #{λ_i² < 4q}` (`posIndex_normMatrix`), and the modes at
`λ² = 4q` are in neither (`index_add_null_normMatrix`). The trivial mode `λ = q + 1` with `q ≠ 1` is one negative square,
since `(q + 1)² − 4q = (q − 1)²` (`one_le_negIndex_normMatrix_of_trivial`).

**4.3 Weil's form.** For a finite family with an involution `σ` and positive weights it keeps, the symmetric matrix
`H_(i, σi) = m_i` has `2n₋(H) = #{σ i ≠ i}` and `2n₊(H) = 2#{σ i = i} + #{σ i ≠ i}` (`two_mul_negIndex_weilMatrix`,
`two_mul_posIndex_weilMatrix`): its negative squares number the exchanged pairs, and `n₋ = 0` if and only if `σ`
fixes every place (`negIndex_weilMatrix_eq_zero_iff`). The first record's criterion becomes the vanishing of a count.

**4.4 Read.** Ruler B: on the Petersen complex, `K₄` and the prism of two rings of 21 (`q = 2` on each), the negative
squares are 1, 1 and 5 and equal the modes with `λ² > 8`; the positive squares are 19, 7 and 79, the cells plus the
modes inside; no mode sits at the edge. Planted null: a form with `q + 3` in place of `q` has no negative square
against the prism's five, so the ruler separates the form from its neighbour.

## 5. The count's bound has its converse

`from training` (X.-J. Li 1997; Bombieri and Lagarias 1999, the criterion as a statement about multisets), the finite
case proved in Lean `Zeta/FiniteLiCriterion`, the join `agent-inferred`.

**5.1 The return of finitely many turns.** For `|u_i| = 1`, every `ε > 0` and every `N` there is `n ≥ N` with every
`|u_iⁿ − 1| < ε` at once (`exists_pow_near_one`): the powers lie in a compact torus, so some two far apart are close,
and their quotient is a power near one. This is the step that is not the triangle inequality: a mode off the circle
is heard at some length, because the modes of largest modulus return together near their opening phase
(`exists_re_count_gt`).

**5.2 The criterion.** With modes `w_i`, weights `m_i > 0` and a map `σ` with `w_(σi) = 1/conj(w_i)`, three
statements are one (`count_criterion_tfae`): every `|w_i| = 1`; `|Σ m_i w_iⁿ| ≤ Σ m_i` at every length; and
`Re Σ m_i(1 − w_iⁿ) ≥ 0` at every `n ≥ 1`, the Li numbers. Without a reversal the bound at every length holds if and
only if every mode is in the closed disc (`count_bounded_iff_norm_le_one`). In the scaled chart, modes `α_i ≠ 0`
closed under `α ↦ q/conj(α)` keep `|Σ m_i α_i^l| ≤ (Σ m_i)·q^(l/2)` at every length if and only if every `|α_i|² = q`
(`count_bound_iff_normSq`). On the line, modes `ρ_i ≠ 0, 1` closed under `ρ ↦ 1 − conj(ρ)` have every Li number
`Re Σ m_i(1 − (1 − 1/ρ_i)ⁿ) ≥ 0` if and only if every `Re ρ_i = 1/2` (`li_line_criterion`). The involution and the
invariance of the weights are not used and are not assumed.

**5.3 Read.** Ruler A, with guesses G1 to G3 fixed first. On the Petersen complex (tempered) no length to 400 leaves
either bound and every Li number is nonnegative, the smallest 0.00564. On the prism of 21 (not tempered) the
two-sided bound, the one-sided bound and the first negative Li number all first fail at length 10. The last two are
one inequality: with `w = α/√q` and total weight `2N`, `Re li_l < 0` says `rem(l) > 2N·q^(l/2)`, so the ruler reads
the identity; the length 10 matches the first record's ruler 13. The remainder computed from the roots agrees with
`tr(B^l)` minus the smooth part to `4·10⁻¹⁴` of `q^l` at every length to 24, the float's reading.

## 6. A regular complex's own half, as one chain

`agent-inferred` for the chain; Lean `Landmarks/RegularComplexHalf`, joining `RegularComplexZeros`,
`FiniteLiCriterion` and `InertiaCount` on one complex.

**6.1 The remainder is a count over root pairs.** For a complex with `q + 1` darts at every cell and `q ≥ 1`, the
smooth part of the closed-walk count at length `l` is `(|E| − |V|)(1 + (−1)^l) + Σ_counts (λ/(q + 1))^l (q^l + 1)`,
where a count is a mode at `λ² = (q + 1)²` (its cell roots are `±q`, `±1`, `trivial_pair_pow`). The remainder
`rem(l) = tr(B^l) − smooth(l)` is `Σ_(other modes) (α_i^l + β_i^l)` (`rem_cast`), where `α_i, β_i` are the roots of
`X² − λ_iX + q`: a conjugate pair at `|·|² = q` in the gap `λ² ≤ 4q`, two reals `r` and `q/r` past it
(`normSq_rootA_of_le`, `rootA_reversal_of_gt`). The family is closed under `γ ↦ q/conj(γ)`, fixing a pair in the gap
and swapping a real pair past it (`gam_rev`), and its count is the remainder (`count_gam`): §5's hypothesis.

**6.2 The chain** (`half_tfae`). For `q ≥ 1` these five hold together or fail together:

1. tempered: every mode other than the counts has `λ² ≤ 4q`;
2. the zeros are on the circle: every zero of `det(1 − uB)` with `u² ≠ 1` and `u ≠ ±1/q` has `|u|² = 1/q`;
3. the count at every length: `|rem(l)| ≤ 2N·q^(l/2)`, `N` the number of modes other than the counts;
4. the count on one side, Li's form: `rem(l) ≤ 2N·q^(l/2)` at every `l ≥ 1`;
5. the index: the negative squares of the norm form number the counts at `λ² > 4q`.

The implications 1 ⇒ 2 and 1 ⇒ 3 are the first record's; 2 ⇒ 1 needs a real zero off the circle that is also away
from `±1` and `±1/q` (`exists_zero_off_circle`, since those four would force `λ = ±(q + 1)`); 4 ⇒ 1 is §5
(`tempered_of_rem_le`); 1 ⇔ 5 is §4 (`tempered_iff_negIndex_filter`). For `q ≥ 2` the index reads simply "the negative
squares number the counts" (`tempered_iff_negIndex`), since `(q + 1)² > 4q`. The reversal `u ↦ 1/(qu)` permutes the
zeros (`zero_reversal`), a tempered complex's zeros have `‖u‖ = q^(−1/2)` (`norm_zero_of_tempered`), and with
`u = q^(−s)`, `q ≥ 2`, tempered is the same as every such zero at `Re s = 1/2` (`tempered_iff_re_half`).

**6.3 Reading.** `agent-inferred`. A finite complex's own Riemann hypothesis is one statement read five ways: a band
for the modes, a line for the zeros, a square root for the count's error at every length, the same with only its upper
excursions watched, and a count of negative squares of the complex's own form. The fifth is the cause the lens
names: the reversal's form, positive on what stays and negative on exactly what left. For the integers the same
five faces are Weil's positivity, the zeros on the line, the prime number theorem with error `x^(1/2 + ε)`, Li's
criterion and a count of negative squares; what the complex has and the integers lack in this chain is a finite
form whose index can be counted, which is the construction the first record's §8 names.

## 7. The darts' Euler product

`from training` (Ihara 1966, Hashimoto 1989, Bass 1992, Bowen and Lanford 1970); Lean
`Landmarks/IharaEulerProduct`, the instance of `NecklaceIntegrality` on the dart operator, joined to `IharaBass`.

**7.1 The statements.** `dartMatrix` is the dart operator with entries in `ℕ`; its cast to any commutative ring is
the tree's `hashimoto` (`dartMatrix_map`). A closed walk of `n` darts with no backtrack and no tail is a cyclic word
`ZMod n → E ⊕ E`; the owner's closed walks of the dart matrix are these words by an equivalence that carries
rotation to rotation (`loopEquiv`, `loopEquiv_rot`), so they number `tr Bⁿ` (`card_closedWalk`) and those of least
period `d` number `d·N_d`, `N_d = primeCycles d` the prime cycles of `d` darts (`card_primitive_closedWalk`). Then
`tr Bⁿ = Σ_(d∣n) d·N_d` for `n ≥ 1` in every commutative ring (`trace_hashimoto_pow`), `Σ_(d∣n) μ(n/d) tr B^d = n·N_n`
over `ℤ` (`primeCycles_moebius`), `N_1` is twice the loops (`primeCycles_one`), and
`det(1 − uB) ≡ ∏_(d ≤ N) (1 − u^d)^(N_d)` modulo `u^(N+1)` over `ℚ`, `ℤ` and every commutative ring
(`ihara_euler_product_coeff`, `ihara_euler_product_int`, `ihara_euler_product_ring`); with `Aeon/Production/Zeta`, the
zeta times the truncated product is `1` to order `N` (`ihara_zeta_euler_product_coeff`).

**7.2 Three faces.** With Bass's identity, in `R[u]` and with no division,
`(1 − u²)^|V| · ∏_(d ≤ N)(1 − u^d)^(N_d) ≡ det(1 − uA + u²(D − 1)) · (1 − u²)^|E|` modulo `u^(N+1)`
(`ihara_three_faces`): the prime cycles, the darts and the cells are one series. One cell with one loop is the
smallest instance: two prime cycles of one dart, none longer, and both sides `(1 − u)²` (`prod_oneLoop`).

**7.3 Read.** Ruler C: prime cycles of `K₄` at lengths 1 to 8 are `0, 0, 8, 6, 0, 12, 24, 18` by Möbius inversion of
the traces and by direct enumeration of primitive closed walks, and of the Petersen complex at 1 to 9 are
`0, 0, 0, 0, 24, 20, 0, 30, 40`, the first record's ruler 13 counts; the dart determinant and the product agree through
`u^8` and `u^9` and first differ one power higher, and the three faces agree to the same horizon. Planted null: with
backtracking allowed, the necklaces of `K₄` are `0, 6, 8, 18, 48, 116` and the three faces differ already at `u²`.

## 8. Below Reynolds one: every mode at once, and stability

`from training` (Lei and Lin 2011, the critical class on `ℝ³`; Beale, Kato and Majda 1984 for what a bound on `∫Y`
controls), the finite comb from the first record; Lean `Fluid/NavierStokesLaminarAllModes` and
`Fluid/NavierStokesLaminarStability`. Every statement is about a solution given as a hypothesis; none constructs one.

**8.1 Every mode.** Over a countable family of modes with weights `w_k > 0`, put `X = Σ'‖u_k‖/w_k` and
`Y = Σ' w_k‖u_k‖`, and ask the feed's bound `Σ_(k∈S)‖N_k‖/w_k ≤ c·X·Y` only on finite windows `S` (`ClassSolution`;
`ClassSolution.of_triads` builds it from the triad bound over disjoint fibres). Then `(Σ'‖u_k‖)² ≤ X·Y`
(`tsum_norm_sq_le`); on every window and then on all modes `X(t₂) + ν∫Y ≤ X(t₁) + c∫X·Y` (`ClassSolution.window_balance`,
`ClassSolution.balance`); with `c·X(0) < ν`, `X(t) ≤ X(0)` and `∫₀ᵗY ≤ X(0)/(ν − c·X(0))` at every `t`, with no
horizon in the bound (`ClassSolution.critical_le_initial`, `ClassSolution.integral_dissipation_le`); and with any data
`X(t) ≤ X(0)·exp(c∫₀ᵗY)` (`ClassSolution.critical_le_mul_exp`). A finite comb is a class solution
(`ClassSolution.of_combSystem`), and so is the fluid's law on all wave vectors `κ_p + κ_q = κ_k` with injective `κ`,
`‖P_k‖ ≤ 1` and incompressible amplitudes, with `c = 1` (`FourierSolution.classSolution`), on the lattice `ℤⁿ∖0` among
others (`torus_critical_le_initial`, `torus_integral_dissipation_le`).

**8.2 Stability and uniqueness.** For two solutions `u`, `v` of one bilinear comb and `δ = u − v`: the feed's
difference splits bilinearly and `Σ‖N(u) − N(v)‖/w ≤ (c/2)(Y_δ(X_u + X_v) + X_δ(Y_u + Y_v))`
(`BilinearComb.sum_combFeed_sub_le_half`), so `D⁺X_δ ≤ −(ν − (c/2)(X_u + X_v))Y_δ + (c/2)(Y_u + Y_v)X_δ`
(`BilinearComb.differenceSlope_le`). Inside the laminar class the difference stays within a fixed multiple of its
opening, `X_δ(t) ≤ K·X_δ(0)` with `K = exp((c/2)(X_u(0)/(ν − cX_u(0)) + X_v(0)/(ν − cX_v(0))))`, at most
`exp(cR/(ν − cR))` when both openings are at most `R` (`BilinearComb.critical_sub_le`,
`BilinearComb.critical_sub_le_of_le`): a constant that names neither the modes nor their number. With no smallness,
Young's split gives `X_δ(t) ≤ X_δ(0)·exp((c²/4ν)∫(A_u + A_v)²)`, so one opening state gives one solution at every size
of the data (`BilinearComb.eq_of_initial_eq`). With a least weight `w₀`, `w₀²X ≤ Y`, and everything relaxes:
`X(t) ≤ X(0)·exp(−(ν − cX(0))w₀²t)` and the difference at the same rate times `K`
(`CombSystem.critical_le_mul_exp_decay`, `BilinearComb.critical_sub_le_mul_exp_decay`). The truncated fluid is a
bilinear comb on the amplitudes across their wave vectors (`Truncation.bilinearComb`), and each statement holds for it
with `c = 1` (`Truncation.critical_sub_le`, `Truncation.eq_of_initial_eq`, `Truncation.critical_sub_le_mul_exp_decay`).

**8.3 Reading.** `agent-inferred`. Below Reynolds one, read as `X/ν`, the count of triads decides three things at
once: the critical reading never rises, two flows that open near each other stay near by a factor fixed by their
Reynolds numbers alone, and both settle at the lowest mode's rate. None of the constants depends on how many modes
the comb carries, which is what lets §8.1 pass from finite windows to the countable family. Above the threshold the
first record's §10.5 stands: the class's bound gives way to `exp(c∫Y)`, and what decides there is the triads' own
conservation and phase, not their count.

## 9. The second law from any density, and the price of a quotient

`from training` (Gibbs; Clausius; the data processing inequality; Landauer 1961 and Bennett 1982); Lean
`Aeon/Production/Landauer`, on the driven aeon of `Aeon/Production/Jarzynski`.

**9.1 The free energy of a density.** For energies `E_t` and `β > 0`, put `F_t(p) = Σ p E_t + β⁻¹ Σ p log p`. Then
`F_t(p) = F_t + β⁻¹ D(p‖π_t)`, `π_t` the equilibrium of tick `t` (`freeEnergyOf_eq`, `freeEnergyOf_sub_gibbs`): the
guide's law "the free energy of `p` over the equilibrium `q` is `k_BT·D(p‖q)`", in Lean. `D(p‖q) ≥ 0` with equality only
at `p = q` (`kl_nonneg`, `kl_eq_zero_iff`), and no stochastic map raises it: `D(pM‖qM) ≤ D(p‖q)` (`kl_push_le`), the
zero columns handled.

**9.2 The second law from any opening.** One tick of a driven aeon is work (the energy changes under a held density)
then heat (a kernel keeping `π_(t+1)` moves the density). The work half changes `F` by the mean work
(`freeEnergyOf_work_step`); the heat half lowers it by `β⁻¹` times the divergence the kernel removes
(`freeEnergyOf_heat_step`, `kl_push_gibbs_le`). Summed: `F_n(p_n) − F_0(p_0) = ⟨W⟩ − β⁻¹Σ_t(D(p_t‖π_(t+1)) −
D(p_(t+1)‖π_(t+1)))` (`freeEnergyOf_sub_eq`), each term nonnegative (`production_nonneg`), so
`F_n(p_n) − F_0(p_0) ≤ ⟨W⟩` from any opening density (`second_law_density`); the built second law is the case
`p_0 = π_0` (`second_law_of_density`), now without Jarzynski's equality. With the first law
`⟨W⟩ − ⟨Q⟩ = Σ p_n E_n − Σ p_0 E_0` (`first_law`): `β⟨Q⟩ = S(p_0) − S(p_n) + production` (`clausius_eq`), Clausius'
inequality `S(p_0) − S(p_n) ≤ β⟨Q⟩` (`clausius`).

**9.3 Landauer and the quotient's price.** A uniform opening on `m` states and a point at the close give
`log m ≤ β⟨Q⟩` (`landauer_card`), `log 2` for one bit (`landauer_bit`), and with the first and last energies one
constant the same in work (`landauer_card_work`). A quotient `f : S → R` with fibres of one size `m` moves the uniform
density to the uniform density (`pushforward_uniform_of_fibres`) and removes `log m` nats of entropy
(`entropy_removed_of_fibres`); a protocol that closes at no more entropy than the quotient leaves pays
`log m/β ≤ ⟨Q⟩` (`quotient_price`).

**9.4 Reading.** `agent-inferred`. Retention is a quotient (the retention contract). §9.3 says what a quotient costs:
merging `m` distinguishable states into one class is heat of at least `log m` nats times the temperature, whatever the
schedule, and a reversible rebase (a bijection, `m = 1`) costs nothing. §9.2 says what a store at a temperature does
from any state: each tick of a kernel that keeps its equilibrium removes divergence, and the free energy above
equilibrium is that divergence in nats over `β`. Of the deposit's rate read as a temperature (atlas
`deposition.rate-temperature-standing-spread`) the statement is a floor and a direction, not a schedule.

## 10. Guesses and scores, and what follows for the machine

**10.1 Guesses** (fixed at 23:02:42 UTC, scored from the ruler's output). G1: the prism's one-sided bound first fails
at length 10, the length of the first record's two-sided failure: hit. G2: its first negative Li number at 10: hit.
G3: every Petersen Li number to 400 nonnegative, the smallest above 1: half (nonnegative, the smallest 0.00564). G4:
prime cycles of `K₄` 8, 6, 0 at lengths 3, 4, 5 and the product agreeing through `u^8`: hit. G5: the prism's norm form
has 9 negative squares: miss, it has 5; the theorem's count holds, and my count of the prism's modes past `λ² = 8` was
the miss.

**10.2 Tests offered** (`agent-inferred`; none run on a learner).

- A ring's conserved receiver exists only where its monodromy is semisimple on its circle (§3). A pump set at two
  coincident multipliers (the edge of a bifurcation, a Jordan block) has no conserved receiver, so a certificate that
  fails there fails by the theorem, not by its search. Before fitting a certificate on a saved state's rings, read
  whether the monodromy's minimal polynomial is squarefree, at the integers' widths.
- The number of a constitution's modes outside its band is a count of negative squares (§4): a congruence to a
  diagonal by integer pivots of a form built from a move and its reversal gives it with no eigenvalue solve and no
  float, a ruler for how many modes left the half.
- One side suffices (§5, §6): a receiver that watches only the upper excursions of a return count above its smooth
  part, at every length, decides whether every mode sits at the half.
- Landmarks as prime cycles (§7): the prime cycles of a contact graph are read by Möbius inversion of the traces of
  its dart operator, in integers, and the product over them is the graph's determinant to any horizon.
- Forgetting has a floor (§9): a quotient that merges `m` states into one class costs at least `log m` nats of heat at
  the store's temperature.

**10.3 What does not transfer.** No statement here is about an unending family: the zeta function's zeros, a complex
of growing size, a fluid with a solution constructed, or an erasing protocol that attains Landauer's bound. Each is
the construction named where its section stands: a form on the unending family whose index can be counted (§6.3),
the limit of truncations with the class's constants (§8.3), and a kernel that realizes a quotient (§9.3).

## 11. Lean, atlas and receipts

**11.1 Lean.** Eight modules under `lean/HolonicsResearch/`, each importing Mathlib and earlier modules of the tree
or of this list. Each builds with no `sorry`, no added axiom and no `native_decide`, and every audited theorem depends
on `propext`, `Classical.choice` and `Quot.sound` alone.

| Module | Lines | Theorems | Holds |
|---|---|---|---|
| `Coupling/MovingMetricSpectral` | 810 | 30 | §3: a kept positive form exists if and only if the modes are semisimple on the locus |
| `Holon/InertiaCount` | 748 | 35 | §4: Sylvester on a diagonal, the norm form's and Weil's form's counts |
| `Zeta/FiniteLiCriterion` | 534 | 20 | §5: the return of turns, the count criterion, the scaled and line charts |
| `Landmarks/RegularComplexHalf` | 856 | 43 | §6: the remainder over root pairs, the chain of five readings |
| `Landmarks/IharaEulerProduct` | 546 | 33 | §7: prime cycles, the Möbius form, the product to a horizon, three faces |
| `Fluid/NavierStokesLaminarAllModes` | 1,040 | 52 | §8.1: the laminar class on a countable family of modes |
| `Fluid/NavierStokesLaminarStability` | 1,058 | 51 | §8.2: stability, uniqueness and relaxation |
| `Aeon/Production/Landauer` | 958 | 56 | §9: the free energy of a density, the second law from any opening, Landauer |

Where it was checked. In this thread's cloud container with the project's pinned toolchain and Mathlib's cached
build: each file by `lake env lean`, each module by `lake build`, and all eight by `bash tools/lean_check.sh` on their
module names (gate 4). The root `HolonicsResearch.lean` gains their eight imports. The reason the guide gives for
building on the PC (the card, the CUDA toolchain, the Lean cache and the private passages) does not reach a kernel
check of a proof under the pinned toolchain, as the first record's §14.1 states (`agent-inferred`).

**11.2 Atlas.** Eight rows enter: `receipt.conserving-receiver-iff-semisimple`, `inertia.negative-squares-count-modes`
and `aeon.second-law-from-any-density` (objects); `trace.ihara-euler-product` and `trace.regular-half-chain`
(geometry); `rh.finite-li-criterion`, `ns.laminar-class-all-modes` and `ns.laminar-stability-uniqueness` (targets).
`trace.ihara-zeta` is regraded `formal-checked`: its truncated product is Lean, and the product over every length is
read coefficientwise. `key.scaled-form-places-modes`, `trace.regular-norm-form`, `rh.finite-weil-criterion`,
`trace.prime-cycle-half-rank`, `ns.laminar-class-reynolds` and `floor.landauer-erasure` gain owners from this set.

**11.3 #410.** The box "the moving metric's spectral reading: the implication needing `G ≻ 0` and its converse needing
semisimplicity" is answered by `Coupling/MovingMetricSpectral:gSkew_iff_imaginary_chart` and its companions (§3). The
box "`trace.ihara-zeta`, `trace.ihara-two-frames`" is answered for `trace.ihara-zeta` (`IharaBass` and
`IharaEulerProduct`); `trace.ihara-two-frames` (the source graph and the face dual as two frames) is not touched.
`Foundation/CausalChord`'s header sentence naming the converse as not formalized now points to the module.

**11.4 Receipts.** The ruler, its output and the guesses, named at the head of this record. Its four sections: A the
one-sided bound and the Li numbers on a tempered and an untempered complex; B the negative squares on three complexes;
C prime cycles by enumeration and by Möbius inversion, the product and the three faces; D the moving metric on a
semisimple imaginary generator and on a Jordan block. Each null is held to a planted instance in the same run (the
untempered prism in A, a shifted form in B, the operator with backtracking in C, a diagonal generator whose conserved
forms span two dimensions in D).
