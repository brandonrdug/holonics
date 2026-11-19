# The carry chain's law is Eulerian, a scope reads neutral only where it holds a repeated prime's fibre, a source upstream of an equal sink closes its body, and the minors' gcd is the invariants' product, in Lean

November 19, 04:00 UTC. The eighth formalization pass over #410, its eighth set, after
[the seventh](2026-11-19_MAXWELL_KEEPS_GAUSS_ALONG_EVERY_MOTION_HEAT_ON_A_PARTITION_RAISES_ENTROPY_BY_HALF_ITS_FISHER_INFORMATION_A_READINGS_LEVERAGE_IS_A_SERIES_OVER_ITS_PIVOTS_AND_THE_RANK_FALLS_WHERE_A_PRIME_DIVIDES_EVERY_MINOR_IN_LEAN.md)
(#1017). Eight new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #405, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Mathematics/CarryChainEulerian` | Adding `n` numbers of uniform digits in base `b`, the carry out `⌊(c + Σ d)/b⌋` of a carry `c < n` is below `n` and the counts from every carry sum to `bⁿ`, so the carry is a Markov chain on `0, …, n − 1` (`carryOut_lt`, `sum_count`, `trans_row_sum`); summing a digit is a box and a unit step across `n` boxes is a step over the whole box (`iterate_box`, `fwdDiff_box`); in the binomial basis `C(c, k)` the count matrix is upper triangular with diagonal `b^(n−k)` (`countMat_mul_binMat`, `binMat_det`, `triMat_diag`), so the chain's characteristic polynomial is `Π_(k<n) (X − b^(−k))` (`countMat_charpoly`, `trans_charpoly`); the Eulerian numbers `A(n, j) = Σ_(r≤j) (−1)^r C(n + 1, r)(j + 1 − r)ⁿ` (`eulerian`) satisfy `Σ_i A(n, i) N(i, j) = bⁿ A(n, j)` (`stationary_count`), sum to `n!` (`sum_eulerian`), vanish for `j ≥ n` and are positive below it (`eulerian_eq_zero_of_le`, `eulerian_succ_succ`, `eulerian_pos`), so `A(n, j)/n!` is the chain's stationary law, a probability law charging every carry (`stationary_law`, `stationary_prob`, `stationary_pos`); `A(3, ·) = 1, 4, 1` (`eulerian_three`, `stationary_three`). | #410's box "Association is evaluation, and a number is a word at a level of the base's tower" (its owed rest); the record of October 23, §4 | `radix.carry-chain-eulerian` |
| `Mathematics/NeutralCriterion` | A neutral scope reads `0` on every coset (`coset_readings_eq_zero`), so every Dirichlet character trivial on the scope has Gauss sum `0` (`charSum_eq_zero_of_neutral`); where the scope holds no repeated prime's fibre, one character trivial on it is nontrivial on every fibre (`exists_hom_ne_one_of_primes`, `exists_char_ne_one_on_fibres`, `ker_le_of_fibreUnit_mem`), and that character's Gauss sum is not `0` (`gaussSum_ne_zero_of_isPrimitive`, `isPrimitive_of_not_factorsThrough`, `gaussSum_changeLevel_prime_mul`, `gaussSum_ne_zero_of_fibres`); so `Tr_H(ζ_n) = 0` iff `n = p m` with `p` prime, `p ∣ m` and `ker((ℤ/n)ˣ → (ℤ/m)ˣ) ≤ H` (`scopeReading_eq_zero_iff`). | #410's box "The neutral criterion" (its owed converse); the record of October 26, §4 and §10(p) | `colour.neutral-fibre` |
| `Landmarks/ClosureKeyMenus` | With operands below `b³` the lines force `s b (b − 1) ≡ 0` beside `s b (b + 1) ≡ 0` (`wide_necessity`), `ofScale` closes every line where `2b·s = 0` and `b(b + 1)·s = 0` (`wide_ofScale_closure`), and a linear key exists modulo `q` iff `q ∣ b·gcd(2, b + 1)`, modulo a prime iff `p ∣ 2b` (`wide_exists_iff`, `wide_zmod_exists_iff`, `wide_prime_exists_iff`; base 10: modulo 10, `wide_ten`); differences with `−` reflecting force their moves and close every line to `s(x − y − c)` over every ring, so they carry no torsion and tell the reflected hand apart (`minus_forced`, `minusKey_closure`, `minus_exists`, `minus_exists_both`, `minus_tells_apart`), and with `=` reflecting `q ∣ 2b` (`equals_zmod_exists_iff`); on one menu of sums and differences the sum lines force the shared moves (`MenuKey.sum_moves`), and the key exists modulo `q` iff `q ∣ 2` with no reflector or with `c₀` in the hand in force, `q ∣ b·gcd(2, b + 1)` with `−` reflecting and `c₀` in the starting hand, and `q ∣ b(b + 1)` with `−` reflecting and `=` restarting, one key reading `c mod b(b + 1)` in both families (`MenuKey.plain_zmod_exists_iff`, `MenuKey.minus_zmod_exists_iff`, `MenuKey.inForce_zmod_exists_iff`, `MenuKey.restart_exists_iff`, `MenuKey.restart_zmod_exists_iff`, `MenuKey.restart_reads`; `ℤ/110` in base 10, `MenuKey.torsion110_menu`). | #410's box "The closure key's torsion" (operands below `b³`, `−` reflecting, the mixed menu); the record of October 25, §§6, 10, 11 | `key.newline-closure-torsion`, `key.newline-closure-reflection` |
| `Landmarks/SmithMinors` | Cauchy–Binet, `det(A B) = Σ_S det A[·, S] det B[S, ·]` over the `k`-subsets of the inner index (`cauchyBinet`, `det_submatrix_mul`); a divisor of every `k × k` minor of `A` divides those of `U A V`, so a unimodular change keeps the divisors and the rational rank (`dvd_minors_unimodular_iff`, `ratRank_unimodular`); on a diagonal form `c` divides every `r × r` minor iff `c ∣ Π d_i` (`dvd_minors_rectDiag_iff`); for `A = U D V` over ℤ, and for any Mathlib Smith form of `A`'s range, `rank_ℚ A` is the count of nonzero invariants, the maximal minors' gcd is `|Π d_i|`, and `p` drops the rank iff `p ∣ Π d_i` (`ratRank_smith`, `gcd_maxMinors_smith`, `modRank_lt_ratRank_smith_iff`, `ratRank_eq_of_smith`, `gcd_maxMinors_of_smith`, `modRank_lt_ratRank_of_smith_iff`); on `SmithCokernel.smith`, `p` drops the rank iff it divides the product of the nonzero invariants, which is the minors' gcd up to sign (`modRank_lt_ratRank_iff_smith`, `gcd_maxMinors_smith_eq`). | #410's box "The closure key's torsion" (its Smith-invariant form) | `linalg.smith-normal-form`, `linalg.rank-falls-mod-p` |
| `Physics/Fluid/RankineOval` | A source `m` at `−a` and a sink `−m` at `+a` in a stream `U` along `x`: above the axis `ψ = U y − (m/2π) α` with `α = y ∫_(−a)^(a) ds/((x − s)² + y²)` (`ovalStream`, `subtended_eq_mul_anglePerHeight`), `α/y` strictly decreasing in `y` (`anglePerHeight_strictAntiOn`), so with `L² = a² + m a/(π U)` each station `|x| < L` has exactly one height on `ψ = 0` and each `|x| ≥ L` none (`exists_root_iff`, `station_existsUnique`, `station_none`), below `m/(2U)` (`oval_width`); the height is continuous and tends to `0` at `±L` (`continuous_height`, `tendsto_height_ends`), where the velocity vanishes (`ovalVelocity_ends`, `ovalStream_station`); the loop through `±L`, the upper heights and their mirror is closed, on `ψ = 0`, injective on `[0, 1)` and bounded (`ovalLoop_closed`, `ovalLoop_stream`, `ovalLoop_injOn`, `ovalLoop_bounds`, `rankine_oval_closes`), winds once about each site (`ovalLoop_winding`), and `Body`'s necessity reads it back as `m + (−m) = 0` (`rankine_oval_net_zero`). | #410's box "Rankine oval sufficiency"; `Physics/Fluid/Body` §4; the egg record of September 24 | `fluid.closed-body-net-zero`, `fluid.rankine-oval-closes` (new) |
| `Zeta/GraphDirectedDimensions` | With every row sum of `M` at most `C` and `‖r^s‖·C < 1`, the graph-directed zeta's depth faces are summable (`summable_depthFace`, `depthFace_eq`), `D(s) = det(1 − r^s M) ≠ 0` (`scaleDet_ne_zero`) and `ζ(s) = N(s)/D(s)` with `N(s) = 1_Sᵀ adj(1 − r^s M) γ(s)` (`resolvent_entries`, `hasSum_depthFace`, `graphDirectedZeta_eq_div`), the two faces being the formal identity's polynomials at `T = r^s` (`scaleDet_eq_eval`, `scaleNumerator_eq_eval`); for `r > 0` and positive gaps `N/D` is differentiable wherever `D ≠ 0` and equals `ζ` on the disc (`differentiableAt_continuation`, `graphDirectedZeta_eqOn`, `differentiableOn_graphDirectedZeta`), so a point where the continuation fails to be differentiable is a zero of `D` (`scaleDet_eq_zero_of_not_differentiableAt`); a zero of `D` need not be a pole (`zero_of_scaleDet_not_pole`); the one-state map, the Cantor string and the golden-mean shift as instances (`oneState_graphDirectedZeta`, `cantor_graphDirectedZeta`, `cantor_dimensions_of_not_differentiableAt`, `goldenShift_scaleDet`). | #410's box "Graph-directed complex dimensions"; `Foundation/FractalString` | `fractal.graph-directed-words`, `fractal.graph-directed-dimensions` (new) |
| `EllipticCurve/EggFamily` | With `u = 2wx + a² + w²`, `A = (a − w)²`, `B = (a + w)²`, `4w²(uy)² + b² u(u − A)(u − B) = 4w² u (u y² − b²(a² − x²))` in any field (`egg_twist_polynomial_identity`), so off the asymptote `u = 0` the egg is the Legendre curve twisted by `−(b/2w)²` (`twistEq_of_eggEq`, `eggEq_iff_twistEq`, `eggTwistEquiv`), over the base field the twist by `−1` (`eggTwist_iff_minusOne`); `λ = A/B = ((1 − β)/(1 + β))² = k⁻⁴`, and in the rapidity chart `k = e^χ`, `λ = e^(−4χ)` (`branch_ratio_beta`, `lambda_eq_inv_kSq_sq`, `branch_ratio_eq_inv_k_pow_four`, `rapidity_chart`); the cubic's discriminant `(a − w)⁴(a + w)⁴(4aw)²` vanishes in `0 ≤ w ≤ a` only at `w = 0`, the ellipse, and `w = a`, a line and a conic crossing at `(−a, ±b)` (`egg_discr`, `egg_discr_orders`, `egg_discr_eq_zero_iff`, `ellipse_fibre`, `neck_fibre`, `neck_singular_points`); smooth off them, at infinity too (`egg_smooth`, `egg_smooth_at_infinity`); for `0 < w < a` the real points are a compact connected oval over `[−a, a]` and an unbounded branch left of the asymptote (`exists_point_iff`, `egg_oval_isCompact`, `egg_oval_isConnected`, `branch_unbounded`); a rational egg reaches the elliptic curve `V² = X(X + A)(X + B)` over ℚ with `Δ = 256a²w²(a² − w²)⁴`, `j = j(λ)`, depending on `β` alone, its vertices two-torsion (`egg_to_eggCurve`, `eggCurve_Δ`, `eggCurve_isElliptic`, `eggCurve_j`, `eggCurve_scale`, `vertices_two_torsion`, `egg_211`); `K(√(1 − λ)) − ½ log(16/λ) → 0` as `λ → 0⁺`, so the record's closed form of the period exceeds `(1/(2ab)) log(1/λ)` by a term tending to `2 log 2/(ab)` at the neck (`ellipticK_neck`, `egg_period_neck`). | #410's box "The egg as an elliptic family"; the egg record of September 24, §§1–3, with the scope correction of September 26 | `egg.elliptic-family` (new), `egg.period-coefficients` |
| `Physics/Spacetime/WignerGeneral` | In the disk chart any two boosts compose into the boost of the Möbius sum and a turn, `B(z₁)B(z₂) = B(z₁ ⊕ z₂)R(θ)`, with `cos θ`, `sin θ` rational in `1 + z̄₁z₂` (`disk_composition`, `mob_in_disk`); `boostX k₁ · boostAlong k₂ c s` is a pure boost times `R(θ)` with `τ = γβ₁γβ₂/((1 + γ₁)(1 + γ₂))`, `sin θ (1 + τc) = −τs(1 + cos θ)`, Wigner's γ-form and the half-angle in the half-rapidities (`general_decomposition`, `general_unit`, `general_half_angle`, `general_gamma_form`, `half_angle_rapidity`), the perpendicular case recovered and the collinear case a pure boost `k₁k₂^(±1)` (`wigner_decomposition_of_general`, `collinear_pure_boost`, `collinear_doppler`); the Möbius velocity disk is a gyrogroup (`mobiusGyrogroup`) whose gyration return acts on the hyperboloid as the general turn (`gyration_on_hyperboloid`, `gyrationCurvatureReturn_is_wigner`), nontrivial at `k = (2, 3)` (`gyration_nontrivial_two_three`), the composite velocity being Einstein's sum (`composite_velocity_is_einstein_sum`); for the right triangle `∫₀^α ∫₀^ρ(θ) sinh r dr dθ = π/2 − α − β`, its side on the geodesic (`side_on_geodesic`, `gauss_bonnet`), and the perpendicular turn is by that area (`wigner_rotation_turns_by_area`). | #410's box "Wigner"; `Physics/Spacetime/Wigner`; the null-cone record of September 24, §1 | `lorentz.wigner-general` (new), `lorentz.thomas-wigner-holonomy`, `gr.route-curvature`, `ym.gyration-curvature` |

The boxes these answer, by their opening words: "Association is evaluation, and a number is a word at a level of the
base's tower" (its owed carry chain); "The neutral criterion" (its owed converse); "Rankine oval sufficiency";
"Graph-directed complex dimensions lie among the zeros of `det(1 − r^s M)`"; and "Wigner: the Gauss–Bonnet area,
non-perpendicular composition and the gyration join". Five boxes in all; "The egg as an elliptic family" is part done,
and "The closure key's torsion" stays part done with one clause left (§3).

## 2. What the pass corrected

1. **The neutral criterion's prime.** The record of October 26 and atlas `colour.neutral-fibre` wrote "for some
   `p² ∣ n`" without "prime"; with `p = 1` the criterion would call every reading neutral. #410's box had the prime;
   the atlas row now does.
2. **Operands below `b³` admit a key modulo `q` iff `q ∣ b·gcd(2, b + 1)`, not iff `q ∣ 2b`.** The box's "those of
   `2b`" holds for primes. For a composite modulus the lines add `s b (b − 1) ≡ 0` to `s b (b + 1) ≡ 0`, so base 10 has
   a key modulo 10 and none modulo 4 or 20 (`wide_ten`).
3. **The sum lines force the shared moves.** The box takes `θ(newline, y) = θ(+, y)` and `θ(x, +) = θ(x, =)` as a
   hypothesis on the key; on one menu of sums and differences the sum lines force them (`MenuKey.sum_moves`).
4. **"Every maximal minor (the product of the Smith invariants)".** A maximal minor here is an `r × r` minor with
   `r = rank_ℚ A`, and what the product of the nonzero invariants is, is the minors' gcd up to sign (`|Π d_i|`), never a
   minor itself; no divisibility chain is needed for it.
5. **The Rankine box names the arrangement loosely.** "Zero net strength in a uniform stream" covers arrangements that
   close no body; what is proved is a source and an equal sink on the stream's axis, the source upstream. The level set
   `ψ = 0` holds the oval and the axis beyond `±L`, so the oval is the loop through `±L`, not the whole level set.
6. **The graph-directed sentence in `Foundation/FractalString` was stale and too strong.** It held the continuation as
   "owed in #62" (closed October 22, its obligations carried to #410). "Where the series converges it is that polynomial
   over `det(1 − r^s M)`" is proved on the row-sum disc `‖r^s‖·C < 1`, which the sentence did not name; and "the poles
   lie among the zeros" holds, while a zero need not be a pole and the series can converge at one: for `M = diag(2, 3)`
   and `S = {0}`, `N` cancels the factor `1 − 3 r^s`. `FractalString` and `Aeon/Production/Zeta` now point to the module.
7. **The egg "equals" the twisted Legendre form off one line.** The transport `(x, y) ↦ (u, uy)` sends the asymptote
   `u = 0` whole to `(0, 0)`, which lies on the twisted curve for every `y`; the two curves are equivalent off `u = 0`
   (birational), and for `0 < w < a`, `b ≠ 0` the egg has no affine point on that line.
8. **Over ℚ the twist is a square class, so the rational curve forgets `b`.** `−b²/(4w²)` is `−1` times a square, so a
   rational egg is the `−1` twist of Legendre and depends on `β = w/a` alone (`eggCurve_scale`). Its discriminant
   `256 a² w² (a² − w²)⁴` is the Weierstrass normalization, sixteen times the cubic's.
9. **The egg's smoothness needs less than `0 < w < a`.** Affinely `a, b ≠ 0` and `a ≠ ±w` suffice; `w ≠ 0` matters only at
   the point at infinity `[0 : 1 : 0]`.
10. **The Wigner box points at a module whose owed sentences cited a closed issue, and presumes an instance the tree did
    not hold.** `Physics/Spacetime/Wigner` held the area, the general composition and the gyration join as "owed (#62)";
    the work is `WignerGeneral`, and `Wigner` now points to it. "The gyration join" presumed an Einstein-velocity
    gyrogroup; `HolonicCurvedArcEinstein` had the class and the flat additive instance only. The join is made through the
    Möbius gyrogroup of the velocity disk, Einstein's addition read as the composite velocity. The sentence "non-collinear
    composition carries winding" is §1 of the null-cone record of September 24, not of the egg record.
11. **The area in Lean is a polar integral.** `gauss_bonnet` states the right triangle's area as
    `∫₀^α ∫₀^ρ(θ) sinh r dr dθ`; that `sinh r dr dθ` is the hyperboloid's induced area and that the polar region is the
    triangle as a set are not stated.

## 3. What each statement stands on, and what is left

- **The carry chain** is for `n ≥ 1` summands and any base `b ≥ 1`; the descent reading of `A(n, j)`, the riffle shuffle,
  the eigenvectors beyond the triangular basis and the convergence `Pᵐ → π` are not stated.
- **The neutral criterion** is for `ζ` in `ℂ`; the size of a reading that is not neutral and `|τ(χ)|` are not stated.
- **The closure key's torsion** is part done, with one clause left: the general pair key's torsion, every pair its own
  move, whose minors' gcds `b(b + 1)`, `2b` and `b(b − 1)` the record computes over the finite line sets (bases 3 to 10
  and 12). Every clause for keys linear in the digit values, and the Smith-invariant form, are stated.
- **The Smith-invariant form** is over ℤ, for a given factorization `U D V` and for Mathlib's form; the chain
  `d₁ ∣ d₂ ∣ ⋯`, the invariants' uniqueness and the smaller determinantal divisors are not stated.
- **The Rankine oval** is for one source and an equal sink on the axis; a general zero-sum arrangement, the half-width at
  `x = 0`, the height's differentiability and a Jordan interior are not stated.
- **The graph-directed dimensions** are for lattice strings on the row-sum disc; uniqueness of the continuation, the
  order of a pole and the spectral-radius disc are not stated.
- **The egg as an elliptic family** is part done: left are the null monodromy (the unipotent monodromies `[[1, 4], [0, 1]]`
  at the neck and `[[1, 2], [0, 1]]` at the ellipse, with Kodaira's types) and the period as the oval's integral (the
  substitution that makes the record's closed form `∫_egg ω`); the logarithmic growth is proved for the closed form.
  `E(ℝ) ≅ S¹ × ℤ/2` and ranks are not stated.
- **Wigner** is in 2 + 1 dimensions with positive Doppler ratios; the area is stated for the right triangle (the
  perpendicular composition) as a polar integral, and the triangle of a non-perpendicular composition, an Einstein-ball
  gyrogroup and gyrocommutativity are not stated.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eight modules, the six modules whose docstrings changed
(`Physics/Fluid/Body`, `Foundation/FractalString`, `Aeon/Production/Zeta` and `Physics/Spacetime/Wigner` of `Holonics`;
`Landmarks/ClosureKeyTorsion` and `Mathematics/ColourScope`) and the research library: the library target built 10,582
of its 10,587 jobs and stopped on one file, `Compression/Landmark/SieveTower`, an untracked draft of the next set that the
library's glob of `HolonicsResearch.*` reads from the working tree; the root module's closure (`+HolonicsResearch`, which
reaches every tracked research module, `tools/lean_census.py` reading `unbuilt=0 unrooted=0`) then read `Build completed
successfully (10585 jobs)`, exit 0, and `bash tools/lean_check.sh Holonics` read `Build completed successfully (9166
jobs)`, exit 0, with no declaration elaborated with `sorry`. The library had been built at the six earlier modules
before, so the closing runs took 52 s, 6 s and 9 s of wall time on a four-core cloud host. `tools/link_check.py atlas` and
`links` read `broken=0`, and `tools/test_records_index.py` passes (8 passed). Single-file checks of each module at the
package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision, read by exit status (each `EXIT 0` with no
output). `#print axioms` on the main theorems reads `propext`, `Classical.choice` and `Quot.sound` alone (`RankineOval`
keeps its audit section; the others were read on scratch copies). The research library's aggregator imports the eight
modules.

Workers on disjoint owner paths, at most three at a time, wrote the eight modules; the lead re-checked each file from
the tree, repointed the owed sentences in `Body`, `FractalString`, `Aeon/Production/Zeta`, `Wigner`, `ColourScope` and
`ClosureKeyTorsion`, and read every `L:` owner added to the atlas against its module's declarations by
`tools/link_check.py atlas`.
