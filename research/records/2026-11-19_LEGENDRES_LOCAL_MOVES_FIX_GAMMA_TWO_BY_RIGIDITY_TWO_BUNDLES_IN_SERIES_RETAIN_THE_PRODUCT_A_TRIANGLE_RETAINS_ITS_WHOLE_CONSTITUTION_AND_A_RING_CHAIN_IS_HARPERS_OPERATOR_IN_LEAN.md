# Legendre's local moves fix Γ(2) by rigidity, two bundles in series retain the product, a triangle retains its whole constitution, and a ring chain is Harper's operator, in Lean

November 19, 11:33 UTC. The twentieth formalization pass over #410, its twenty-first set, after [the
twentieth](2026-11-19_A_METRICS_JET_BUILDS_THE_TIDE_AND_THE_PLANE_WAVES_TYPE_N_A_MENU_ON_A_GROUP_HAS_KEYS_EXACTLY_WHERE_IT_IS_FLAT_AND_A_RELEASE_CERTIFIES_ITS_CAPTURE_ON_THE_WHOLE_BOX_IN_LEAN.md)
(#1032). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Geometry/HypergeometricMonodromy` | Gauss's operator on `K⟦X⟧` acts on coefficients by `(n + 1)(n + c) f_(n+1) − (n + a)(n + b) fₙ` and on `λ^r` by `r(r + c − 1)λ^r − (r + a)(r + b)λ^(r+1)`, so its exponents are `{0, 1 − c}` at `0`, `{0, c − a − b}` at `1` (through `λ ↦ 1 − λ`, which carries `L_(a,b,c)` to `L_(a,b,a+b+1−c)`) and `{a, b}` at `∞`, summing to `1` (`coeff_op`, `twisted_one_eq_indicial`, `opPoly_comp_one_sub`, `twistedInf_eq`, `roots_indicialZero`, `roots_indicialOne`, `roots_indicialInf`, `fuchs`); Legendre's exponents are `(0, 0)`, `(0, 0)`, `(½, ½)` and the triangle's differences `½`, `⅓`, `0` (`legendre_exponents`, `triangle_exponents`); `₂F₁(½, ½; 1; ·)` is annihilated, its coefficients over ℝ are those of `K(√λ)`, and there is one `G` with `G(0) = 0` making `Fℓ + G` a solution, on which `ℓ ↦ ℓ + 2πi` acts by `A = [[1, 2], [0, 1]]` (`op_legendreF`, `coeff_legendreF_real`, `legendre_log_solution`, `shiftLog_legendreBasis`, `continuation_round_zero`); over a field with `2 ≠ 0` two moves of trace `2` whose product has trace `−2` are conjugate to `(A, B⁻¹)` and generate a conjugate of Sanov's group, `Γ(2)/±1` in `PSL(2, ℤ)` (`legendre_rigidity`, `legendre_monodromy_group`, `range_sanov_map_proj`), and two moves of traces `0` and `1` whose product has trace `−2` are conjugate to `(S, U)` and generate the modular group (`triangle_rigidity`, `triangle_monodromy_group`, `closure_s_u`) | #410's box "Monodromy as a group of moves" (part); `Geometry/LegendreLevelTwo`'s, `Geometry/ModularFreeProduct`'s and `Geometry/CompleteEllipticSeries`' limits; the record of September 27, §5 | `lock.riemann-scheme-rigidity` (new); `lock.gamma-two-index`, `lock.modular-free-product` (scope), `landmark.hypergeometric-residues` (owners) |
| `Objects/RetentionSeries` | A part that steps as a smaller medium under a map of letters reads that medium's futures (`part_transportWord`, `part_reading_iff`); on two bundles in series a source balances iff its charge is zero, the first bundle carries the series current `σ₁ + σ₂` and the second `σ₂`, each split by its own shares, so each part steps as its bundle under its folded source and two composite presents share every future iff each part shares every future on its own bundle (`series_flux`, `firstPart_stepConstitution`, `secondPart_stepConstitution`, `series_futureAgreement_iff`); under the square law the classes are pairs of the bundles' classes (each part equal or both uniform) and the minimal retention is the pair of the bundles' minimal retentions, lawful and least (`series_square_futureAgreement_iff`, `seriesMinimalRetain_eq_iff_futureAgreement`, `seriesMinimalStanding_exists`, `seriesMinimalRetain_factors_through_every_standing`); under the Joule law each bundle scales by its own factor and the classes are pairs of projective classes, strictly finer than the whole's projective class (`series_joule_step_scales`, `series_joule_futureAgreement_iff`, `series_joule_witness`); on the triangle the unit sources `0 → 1` and `1 → 2` read every ratio, so the present observation reads exactly the projective class (`projectivelyEqual_of_two_reads`, `triangle_observe_iff_projectivelyEqual`), no constitution takes both unit strokes in proportion (`not_both_strokes_proportional`), and under the square law two presents share every future iff their constitutions are equal: the constitution is the minimal retention (`triangle_square_futureAgreement_iff`, `triangle_constitution_factors_through_every_standing`); `(1, 4, 4)` and `(2, 8, 8)` agree after the stroke `0 → 1` and are separated by the stroke `1 → 2` (`triangle_witness`) | #410's box "The explicit classes of the square law's minimal retention" (part); `Objects/RetentionClasses`' "What is not claimed"; `Objects/Retention`'s `[open]` paragraph; `Foundation/MinimalRetention` | `deposition.series-bundles-product-retention`, `deposition.triangle-retains-constitution` (new); `deposition.minimal-retention-general`, `deposition.pendant-edge-forgotten` (scope) |
| `Physics/HarperChain` | On a chain of rings with chain bonds `1` and ring bonds `e^(2πiαn)` at column `n`, every unit cell is a closed walk whose transport is `e^(2πiα)` (`cell_isWalk`, `cell_holonomy`, in `Holon/Complex`'s `walkTransport`), and a reversed bond carries the conjugate (`transport_reverseEdge`); on `ψ(n, m) = χ(m) φ(n)` with a ring character of phase `θ` the hopping is Harper's operator `φ(n + 1) + φ(n − 1) + 2cos(2παn + θ) φ(n)`, on the plane and on a cylinder of `L` rings (`hop_ringBloch`, `hop_bloch`, `hop_cylinder`), and the potential reads only the helix's open phase (`harperPotential_eq_openPhase`); at `α = p/q` the operator on Bloch functions is a Hermitian `q × q` matrix whose eigenvectors are the cells of Bloch solutions (`blochMatrix_isHermitian`, `bloch_eigen_iff`, `hop_eq_harperBloch`, `harper_eigen_iff`); with the transfer matrices' trace over a period `Δ(E)`, `E` is an eigenvalue of `H(k)` iff `Δ(E) = 2cos k` for every `q`, and `det(E − H(k)) = Δ(E) − 2cos k` at `q = 2, 3` (`det_eq_zero_iff_discriminant`, `harper_det_eq_zero_iff`, `chambers_two`, `chambers_three`); for coprime `p, q` each gap `r` has one label `t` with `−q < 2t ≤ q` and `r ≡ tp (mod q)`, and `r/q = s + t·(p/q)` (`existsUnique_gapLabel`, `IsGapLabel.density`); a label `N = s + tα ∈ [0, 1)` has `s = −windings(tα)` and `N = openPhase(tα)`, the windings being the carry word's carries over the `|t|` ticks between tick `0` and tick `t` (`label_split`, `IsGapLabel.whole_eq_neg_sum_carry`, `IsGapLabel.whole_eq_sum_carry_before`) | #410's box "A library constitution equal to the Harper/almost-Mathieu operator" (part); the record of October 5, joint J1 and §4 item 3 | `gap.harper-ring-chain` (new); `gap.label-chern-edge` (expression, scope) |

The boxes these answer, by their opening words, each part done: "Monodromy as a group of moves"; "The explicit classes
of the square law's minimal retention"; and "A library constitution equal to the Harper/almost-Mathieu operator".

## 2. What the pass corrected

1. The brief's rigidity hypotheses "`X, Y ≠ 1`" and "`XY ≠ −1`" follow from the traces and are dropped
   (`legendre_nontrivial`, `triangle_mul_ne_neg_one`). Its "by `diag(1, 2)`" holds for the convention `g ↦ D⁻¹gD`; under
   `g ↦ DgD⁻¹`, the one stated, the matrix is `diag(2, 1)`. In the triangle's sketch, `c = 1` comes from `tr Y =
   tr(X⁻¹(−T)) = c`. The record of September 27 puts the triangle in the chart `(1/12, 5/12; 1)`, with the cusp at `0`,
   and the brief in `(1/12, 1/12; ½)`, with the cusp at `∞`; both are proved. "The monodromy `Γ(2)`" of
   `CompleteEllipticSeries` and the box is loose in `SL(2)`: the group two local moves generate there is Sanov's, of
   index two in `Γ(2)` and without `−1`, and `Γ(2)` is the monodromy as `Γ(2)/±1` in `PSL(2, ℤ)`;
   `CompleteEllipticSeries`' limits now say so. Mathlib's `ordinaryHypergeometricCoefficient` takes its junk value at `c
   ∈ {0, −1, …}`, so `op_hyperSeries` carries `n + c ≠ 0`.
2. `RetentionClasses`' expectation for the series, "the product of the two bundles', each driven by the series current",
   holds under both laws, for any law pair that agrees with each bundle's law on its edges. The brief expected that on
   the triangle "a stroke followed by a source reveals the total"; one fixed stroke need not: the stroke `0 → 1` on `(1,
   4, 4)` deposits a multiple of the constitution, `(1, 4, 4)/9`, so `(1, 4, 4)` and `(2, 8, 8)` stay together after it,
   and the stroke `1 → 2` separates them. The box's phrase "the orbit structure of deposition on projective classes"
   describes neither the bundle's classes nor the triangle's: on the triangle the present reads the projective class and
   the square law's classes are single constitutions.
3. The brief wrote Chambers' relation as `Δ(E) − 2cos(qk)` beside corner entries `e^(±ik)`: with those corners `k` is
   the Bloch phase across one period and the relation is `Δ(E) − 2cos k`; `2cos(qk)` belongs to a phase `k` a site. The
   record's J1 and the atlas row stated TKNN as `r = s_r q + t_r p` without the range that fixes `t`; without it `(s,
   t)` is fixed only up to `(s − jp, t + jq)`, and the row now carries `−q/2 < t ≤ q/2`. The brief's "the label's whole
   part is the epoch count of the carry word over `t` ticks" holds with a sign: for `t ≥ 0` the whole part is minus that
   count, and for `t < 0` it is the count over the `|t|` ticks before tick `0`. Every result holds from `q ≥ 1`, not
   only `q ≥ 2`. The record's other route, the carry word's own operator, was not built; the ring chain was taken.

## 3. What each statement stands on, and what is left

- `Geometry/HypergeometricMonodromy` states the monodromy side as finite algebra: Riemann's scheme, the logarithm at a
  double exponent, and rigidity. The analytic continuation of the solutions (that the monodromy of Gauss's equation has
  these local data, the formal `ℓ` read as `log λ`), the convergence of `G`, the connection matrix between the bases at
  `0` and `1` (so `M₁ = B⁻¹` is read from rigidity, not from Legendre's periods), the Schwarz map as a conformal map
  onto the triangle with its inverse `1728/j`, and conjugacy inside `SL(2, K)` or `GL(2, ℤ)` are not stated. The box
  stays part done.
- `Objects/RetentionSeries` computes the classes on two bundles in series and on the triangle. Graphs with several
  cycles that do not share their two ends (a wheel, a grid, two triangles on one edge), cycles of four or more edges,
  the Joule law on the triangle, deposition laws beyond the square and Joule laws (beyond the series reduction, which
  takes any agreeing law pair), series of three or more bundles and the convergence of repeated deposition are not
  stated. The box stays part done.
- `Physics/HarperChain` builds the ring chain and reads Harper's operator, its Bloch matrix, the eigenvalues as the
  zeros of `Δ(E) − 2cos k` and the gap labels with their carry-word reading. Chambers' polynomial identity for general
  `q` (the multiplicities), the integrated density of states as a spectral count (each band carrying `1/q`), the Cantor
  spectrum at irrational `α`, that the gap labelled `t` is open, the Hall conductance and Chern number with Středa's `t
  = ∂N/∂α`, the edge receiver with `t` channels and the Thouless pump are not stated. The box stays part done.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated or owed (`Geometry/LegendreLevelTwo`'s, `Geometry/ModularFreeProduct`'s and `Geometry/CompleteEllipticSeries`' limits on the monodromy, the last also on "the monodromy `Γ(2)`"; `Objects/RetentionClasses`' "What is not claimed", `Objects/Retention`'s `[open]` paragraph and `Foundation/MinimalRetention`'s on the classes; the `Holonics` module and its importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (8809 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10629 jobs)`, exit 0; `Holonics`, with `Objects/Retention` and its importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
