# A number is the homology of its places, a law of composition is its characters, a symbol's word obeys Kraft, and a return map's necklaces are counted, in Lean

November 18, 22:14 UTC. The second formalization pass of the day, over boxes of #410 that the records of
September 27 and November 8 to 12 left as statements for Lean. Eight modules of `lean/HolonicsResearch`,
294 declarations, each elaborated at the package's toolchain with no `sorry`, no `axiom` and no
`native_decide`. Nothing here touches the engine, a state or a run. The first pass is
[the record of 22:00](2026-11-18_THE_THEORYS_CORE_STATED_IN_LEAN_RINGS_CLOSE_AT_THEIR_LCM_AND_CARRIES_AT_THEIR_PRODUCT_IDENTITY_IS_THE_MODES_SHARED_READINGS_AND_A_PROOF_IS_THE_ORBIT_OF_A_FINITE_MAP.md).

Refs #410, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Mathematics/PlaceComplex` | The place complex: the boundary of a carry edge is `(b − x)·xᵏ`, two chains name one value at `x = b` if and only if they differ by a boundary, the carry chain is unique, and chains modulo boundaries are the ring by evaluation at `x = b`; for digit lists, `ofDigits b L = ofDigits b M` if and only if their chains differ by `(b − x)·t`; `a + b = (a ⊕ b) + 2(a ∧ b)`. The increment `s_b(n + 1) − s_b(n) = 1 − (b − 1)·v_b(n + 1)` at every radix `b ≥ 2`, and `(b − 1)·Σ_(k ≤ N) v_b(k) = N − s_b(N)`. At a prime radix Kummer's and Legendre's valuations are the total of the carry chain, `v_p C(m + n, m) = t(1)` and `v_p(N!) = t(1)`; at radix 10 and `N = 5` the summed valuation reads 0 against 1, and Lucas's congruence fails at radix 4. Newton's residual squares in any ring, commutative or not, with the carried form, the released step `1 − A(X(2 − AX) + r) = E² − A·r` and the bottom end's doubling. A result's width from its operands' widths: sums, sums of `n` terms, products, and a low section meeting a signed one. | the number record of November 8, §2 to §5 and §10 | `radix.place-complex`, `radix.digit-face-calculus`, `radix.product-decomposition`, `arith.inversion-two-ends`, `radix.width-need` (new) |
| `Physics/CochainCount` | On a finite complex over ℝ with `∂₁∂₂ = 0`, the cochains that are closed and co-closed have dimension `E − rank ∂₁ − rank ∂₂`, and none stands if and only if the two ranks fill `E`; a filled triangle holds none and a hollow one holds the all-ones cochain. A junction's Hermitian form: `n² = n + 2·C(n, 2)`; each pair's block has `det = t² − z² − \|X_ij\|²` with `t = ½(X_ii + X_jj)`; the block is kept by that pair's moves of determinant one; an amplitude's form `ψψ*` reads zero on every pair; the times sum to `(n − 1)/2 · tr X`. | the Einstein record of November 11, §11 and §14.12 | `gr.source-free-charge-hole`, `lorentz.junction-hermitian-times` |
| `Mathematics/CharacterTriad` | On every finite abelian group `[x = L + R] = (1/\|G\|) Σ_ψ ψ(x) conj ψ(L) conj ψ(R)`, each triad reading 1 on the law. On `ℤ/n` the terms for `k` and `−k` are conjugate, and the real parts of `⌊n/2⌋ + 1` triads hold the law, with weight 1 at `k = 0` and at `2k = n` and weight 2 elsewhere. With the two legs fair and independent, each leg and the sum meet once in every pair of values: a pair term reads nothing. | the triad record of November 12, §3.1 | `code.triad-character-of-composition`, `contact.pair-product-owes-site-leg` |
| `Compression/SymbolWord` | Functions on a product of finite rings are the sum, over the sets `J` of rings, of their terms on `J`; a term on `J` reads only the rings of `J` and has mean zero along each of them, and those two properties name the terms on `J`; the terms are projections that annihilate each other, and the space on `J` has dimension `Π_(j ∈ J) (m_j − 1)`, so the first order holds `1 + Σ_j (m_j − 1)` rows and the whole series `Π_j m_j`. On `ℤ/M` with pairwise coprime rings the same through the Chinese remainder. Kraft's sum for symbols read on rings of any sizes: symbols told apart on a ring both read have `Σ_u Π_(i ∈ S(u)) m_i⁻¹ ≤ 1`, and the located lengths (the least prefix no other symbol holds) satisfy it whenever the keys are distinct. | the symbol record of November 12, §8.1 and §8.2 | `code.symbol-word-located-rings`, `radix.residue-address`, `code.kraft-shannon` |
| `HNN/NearestQuotient` | `⌊(aK + ⌊mK/2⌋)/(mK)⌋ = ⌊(2a + m)/(2m)⌋` for every `K > 0`, and `⌊(a + ⌊m/2⌋)/m⌋` equals it, so a contact's currents and shares at multiplier 1 are the integers they are at `2^62`. The engine's `div_nearest` (a half going away from zero) is `sign x · ⌊(\|x\| + ⌊m/2⌋)/m⌋`, keeps its value under a common factor and stands within half a unit: `−m ≤ 2(x − m·q) ≤ m`. | the engine record of November 12, §9 | `radix.nearest-quotient-of-the-ratio` |
| `Compression/Landmark/NecklaceIntegrality` | For a square matrix `M` of natural numbers, the closed walks of `n` edges number `tr(Mⁿ)`, rotation acts on them, and with `p_n` the rotation orbits of least period `n`: `tr(Mⁿ) = Σ_(d ∣ n) d·p_d` and `Σ_(d ∣ n) μ(n/d)·tr(M^d) = n·p_n`, so `n` divides the Möbius sum and the quotient is a count. Every coefficient of order `k ≤ N` of `det(1 − T·M)` is that of `∏_(d ≤ N) (1 − T^d)^(p_d)`. Rulers: `[[2]]` reads `2, 1, 2, 3, 6, 9` and the golden-mean shift `1, 1, 1, 1, 2, 2`. | `Compression/Landmark/PrimitiveCycle`'s closing paragraph | `landmark.primitive-cycle-count`, `landmark.euler-product`, `arith.fermat-ring-partition`, `trace.power-cyclic-words` (new) |
| `Physics/Thermal/MeanOfStates` | On a quadratic code the code at the mean of `n` states stands under the mean of their codes by `1/(2n²)` times the sum over unordered pairs of the curvature along their difference; for draws with one covariance about one mean the mean of that saving is `(1 − 1/n)` of the standing cost `½ tr(HΣ)`; under the information equality the standing cost is `¼ tr(PH)`, and one entry's standing cost is the least excess of an estimate from `w = 2/(P_ii H_ii)` sites; a lap-mean difference is the weighted sum `Σ i·ε + Σ (n − i)·ε` of the two laps' increments, with its own and shared second moments. | the rate record of November 11, §2 item 6 and §4 | `deposition.rate-temperature-standing-spread`, `deposition.lap-mean-quarter-floor` |
| `Compression/ReceiverRelease` | On a finite viable set, `D(Q‖P₀) + E_Q[c_R − log₂ L_R] = D(Q‖Q_R) − log₂ Z_R` for every law `Q`, so `Q_R ∝ P₀·L_R·2^(−c_R)` is the one law of least value; a mixture over rungs codes within `−log₂ π_j` of each rung; with `k` switches among `N` transitions the rung `⌈log₂(N/k)⌉` pays at most `k log₂(N/k) + 4k`. | the learner record of September 27, §14.3 and §14.6 | `release.receiver-conditioned-law`, `switching.hazard-ladder-bound` |

The boxes of #410 these answer, by their opening words: "The number owner's laws"; "On a finite complex the
closed and co-closed cochains"; "A junction's forms"; "A law of composition across a place is held by
triads"; "The tensor decomposition of functions on `ℤ/M`"; "Kraft's inequality for a symbol's lengths"; "A
nearest quotient keeps its bits"; "Necklace integrality and the infinite Euler product"; "The saving of a
mean of states"; "A lap-mean difference is its weights"; "A rate is a window"; "The receiver-conditioned
release"; and "The hazard-ladder mixture bound".

## 2. What the pass corrected

1. **The nearest quotient needs no even factor.** The box and the engine record's §9 ask for an even `K`.
   The identity holds for every `K > 0` (`common_factor`), as the atlas row already said; the evenness was
   the occasion (`2^62`), never a hypothesis.
2. **The released remainder has a sign.** `arith.inversion-two-ends` wrote `e′ = e² − a·r` "with the
   remainder `r`". The sign holds with `r` the released value less the unreleased one (`newton_released`),
   and the row now says so.
3. **The saving of a mean asks no symmetry.** The box states it for a symmetric stiffness. The identity
   holds for any bilinear `B`, because only the symmetric part of a stiffness enters a quadratic code
   (`saving_eq_unordered_pairs`).
4. **Five triads, four of them not constant.** The triad record's §3.1 reads "Four triads hold it whole"
   from its ruler on `ℤ/8`, where the count is `⌊8/2⌋ + 1 = 5`. Both stand: the triad at `k = 0` is the constant one
   (`term_zero`), and the atlas row's scope now says which is counted.
5. **The cycle owner no longer lists the general return map as unformalized.** The closing paragraph of
   `Holonics/Compression/Landmark/PrimitiveCycle` pointed at #62 for the necklace count and the infinite
   product; it now names the module that proves them, by applying that owner's own counts to the rotation
   of closed walks.
6. **Mathlib's names for the box on the number owner's laws.** Legendre's formula is
   `sub_one_mul_padicValNat_factorial` in the root namespace, Kummer's `padicValNat_choose`, and Lucas's
   `Choose.choose_modEq_prod_range_choose`.

## 3. What each statement stands on, and the constructions beside it

- **Carries.** Kummer and Legendre are joined to the place complex through the total `t(1)` of the carry
  chain, which the complex makes unique. Reading the chain's coefficients one by one as the schoolbook
  carries is `kummer_sum_of_carries`' place-by-place form. The XOR-and-shift loop's stopping time is a
  statement about the support of that chain (one more than its longest run), and a closing edge (a ring, a
  twist, a Solinas modulus) is one more edge from the top place back to a low one: both are constructions
  on the complex as it now stands.
- **The harmonic count** is rank and nullity with a positive form, over ℝ. The record's sheet of nine cells
  with cells removed is the same theorem at a larger ruler; the triangle is its least instance.
- **The junction.** A pair's block is kept by that pair's moves. A move of one pair changes the blocks of
  the pairs that share an end with it, and the whole form's determinant is kept by
  `Physics/TwoWayField.det_kept`: the junction's invariant under every move is the form of degree `n`.
- **Characters.** The pair-term clause is proved as independence in counting form on the uniform law of the
  two legs. With an entropy on finite laws it reads `I(x; L) = I(x; R) = 0` at once.
- **The symbol's word.** The terms are realized as products of the kernels `δ − 1/m_i` on the rings of `J`
  and `1/m_i` off it, the same projections the characters trivial off `J` span. The first-order identity of
  a key's move (the symbol record's §8.3) takes these terms as its domain.
- **Necklaces.** Divisibility is proved where the Möbius sum counts, for nonnegative entries; for a signed
  integer matrix it is Gauss's congruence, which has no counting model and is cited. The product is proved
  coefficient by coefficient, which is what a product over unboundedly many factors means in `ℚ⟦T⟧`.
- **The mean of states** takes the draws' second moments as its hypothesis and any real-linear mean as its
  expectation, so it holds for a finite weighted mean and for an integral alike.
- **The release** is one receiver's law on one viable set at one state; the ladder's bound takes the fixed
  share's charge from `Compression/Landmark/Context/Dormancy`.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eight modules by name with `Holonics.Physics.Thermal.LapMean` and
`Holonics.Compression.Landmark.PrimitiveCycle`, the two foundation modules whose docstrings changed:
`Build completed successfully (8747 jobs)`, exit 0, no declaration elaborated with `sorry`. Projected under
5 minutes from the single-file checks (5 to 13 s a module) and the foundation modules the necklace count
imports, deadline 25 minutes, measured 92 s of wall time on four cores; peak resident set not read. The
library's aggregator imports the eight modules; the whole research library was not rebuilt.

The check ran on a cloud host at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision, as the first pass's did and for the reason its record gives: a Lean type-check of modules that
import Mathlib and the foundation library reads neither the card, the CUDA toolchain nor a private passage
(`agent-inferred`).

Four workers on disjoint owner paths wrote the eight modules (the thermal mean and the release; the place
complex and the cochain count; the characters, the symbol's word and the nearest quotient; the necklaces);
each file was re-checked by the lead before the gate, and every `L:` owner added to the atlas was read
against its module's declarations.
