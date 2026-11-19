# The restoring leg's zero production is the limit of finite legs, ζ's jets bound a capture square, and the egg's period is its oval's integral, in Lean

November 19, 15:08 UTC. The twenty-fifth formalization pass over #410, its twenty-sixth set, after [the
twenty-fifth](2026-11-19_AN_L_FUNCTION_IS_A_CYCLE_MACHINE_WHOSE_PRIME_SITES_CARRY_THEIR_OWN_CLOCKS_CHAMBERS_IDENTITY_HOLDS_FOR_EVERY_PERIOD_AND_FREE_FALL_DEVIATES_BY_THE_TIDE_OF_ANY_TORSION_FREE_CONNECTION_IN_LEAN.md)
(#1037). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/InformationPort` | The restoring leg as `N` quench-and-relax steps: step `k` produces `D(q_k‖q_(k+1))` by the owner's free relaxation at the next levels, and its work is the drop of `θ log Z` plus `θ` times that production, so the leg's work is the owner's `restoreWork` plus `θ Σ_k D(q_k‖q_(k+1))`, the discrete second law (`stepProduction_eq`, `stepWork_eq`, `legWork_eq`, `legHeat_eq`, `leg_first_law`); by Hoeffding's bound on consecutive canonical states, `D(canonical E‖canonical(E + η)) ≤ ((b − a)/θ)²/8` for `a ≤ η ≤ b`, the leg produces at most `(b − a)²/(8Nθ²)`, and its production, work and heat tend to the quasi-static leg's, the work never below it (`kl_canonical_shift_le`, `legProduction_le`, `legProduction_tendsto`, `legWork_tendsto`, `legHeat_tendsto`); a population moved by a flux on edges keeps its total, and moving a unit from `i` to `j` costs `log(q_i/q_j)` (`sum_edgeRate`, `edgeRate_population_term`, `hasDerivAt_crossEntropy_edges`); with nonnegative masses the cross-entropy against a positive reference keeps its two-sided rate, while at an entrance `p = rt` the relative entropy's right quotient tends to `−∞` and the entropy's to `+∞`, and the cross-entropy tends to `+∞` where the reference leaves a populated cell (`moving_support_rate`, `entrance_relTerm`, `entrance_entTerm`, `entrance_relativeEntropy`, `crossEntropy_tendsto_atTop`); a ring held about the target's phase by a torsional store of energy `alignCost` has effort `½ q_c Δ_c`, its power balance pairs effort with the ring's rate, and overdamped it relaxes as `Δ_c(0)e^(−γq_c t/4)`, dissipating the whole initial `alignCost`, indifferent to a common winding (`ringEffort_gradient`, `hasDerivAt_alignCost_path`, `phaseGap_ringRelax`, `ring_energy_rate`, `ringHeat_tendsto`, `ring_winding`); the lifted log ratio `ℓ = effort/(2θ) + iΔ` gives the thermal port's level shift and the ring's gap, a produced motion drives both ports by `R⁻¹dR`, and the two returns add to `θD(p‖q) + alignCost` (`logRatio_split`, `modulus_face_readings`, `covector_drives_ports`, `two_ports_return`); the lifted face determines no ring return (`lifted_face_determines_no_ring_return`); the two-level port at `N = 1, 10` and one ring channel (`twoLevel_witness`, `ring_witness`) | #410's box "The information port (`Physics/Information`)" (ticked); `Physics/Information`'s `[open]` paragraph, `Information/CrossEntropyRate`'s scope line and `Information/PortWork`'s last paragraph | `info.moving-support`, `info.finite-step-quasistatic`, `info.ring-port`, `info.covector-two-ports`, `info.lifted-face-no-ring-return` (new) |
| `Mathematics/ZetaJets` | At complex `s`, `‖y^(−s) − a^(−s)‖ ≤ ‖s‖(a^(−σ) − y^(−σ))/σ` by the rate of `y^(−s)`, so each term's comparison with its unit integral is bounded and, telescoped, ζ's tail lies within `‖s‖N^(−σ)/σ` of `N^(1−s)/(s − 1)` for `Re s > 1`, the complex receiver disc (`norm_cpow_neg_sub_le`, `norm_zetaTailC_sub_le`, `riemannZeta_mem_disc`); η's pairs converge absolutely for `Re s > 0` with tail at most `‖s‖(2K + 1)^(−σ)/σ`, sum to `(1 − 2^(1−s))ζ(s)` for `Re s > 1`, and at real `s > 0` are the owner's `η` (`summable_norm_etaPair`, `norm_tsum_etaPair_tail_le`, `tsum_etaPair`, `ofReal_eta_eq_tsum_etaPair`); ζ's jets are `ζ^(k)(s) = (−1)^k Σ (log n)^k n^(−s)` through Mathlib's `LSeries_iteratedDeriv`, and with elementary primitives `P_k` of `(log x)^k x^(−σ)` their tails are bounded uniformly on `Re s ≥ σ₀ > 1` by `(log N)^k N^(−σ₀) + P_k(σ₀, N) → 0` (`iteratedDeriv_riemannZeta`, `logTail_bracket`, `norm_jetTail_le`, `tendsto_jetTailBound`), which supplies the capture square's `q` and maps a box into a box (`zeta_deriv_capture_datum`, `zeta_image_box`); η′ at real `s > 0` is bracketed by its alternating partial sums from `n + 1 ≥ e^(1/s)` and is η's rate for `s > 1` (`etaDeriv_mem_uIcc`, `abs_etaDeriv_sub_le`, `hasDerivAt_eta`); the `B₂` step brackets `(f(a) + f(a + 1))/2 − Δf′/12 − ΔF` in `[−Δf‴/384, 0]` when `f⁗ ≥ 0`, through the Peano kernel `t²(1 − t)²/24` with no integral taken, so for real `s > 1` ζ's tail lies within `s(s + 1)(s + 2)N^(−s−3)/384` below `N^(1−s)/(s − 1) + N^(−s)/2 + sN^(−s−1)/12`, and an explicit `N` releases it at `2^(−k)` (`trapezoid_B2`, `zetaTail_euler_maclaurin_two`, `emStart_spec`); witnesses at `2 + i`, `ζ′(2)` and `π²/6` within `10⁻⁶` from ten terms (`zeta_two_add_I_disc`, `deriv_riemannZeta_two_mem`, `zeta_two_enclosure_ten`) | #410's box "`series.log-atanh`, …, `analytic.euler-maclaurin-eta`" (part done; its third note); `Mathematics/CertifiedCapture`'s "What is not claimed" | `analytic.zeta-complex-box`, `analytic.zeta-jets`, `analytic.euler-maclaurin-b2` (new); `analytic.euler-maclaurin-eta` (scope) |
| `EllipticCurve/EggPeriod` | `x = a cos 2θ` carries the oval `(−a, a)` to the Legendre form's quarter circle, `u = B cos²θ + A sin²θ` and `(u − A)(B − u) = 4w²(a² − x²)`, with a Lebesgue change of variables that needs no integrability at the ends (`integral_comp_cos`, `eggU_cos_two_eq`, `oval_factor`); so for `0 ≤ w < a` the oval's integral `∫_(−a)^a dx/(b√(u(a² − x²)))` is `(2/(b(a + w))) K(√(1 − λ))` (`integral_oval`), and with both arcs `±y₊` on the egg the period of `ω = dx/F_y` round the oval is that closed form (`upperArc_eggEq`, `ovalPeriod_integrand`, `ovalPeriod_eq`); at the ellipse it is `π/(ab)` and toward the neck it grows as `log(1/λ)/(2ab)` plus `2 log 2/(ab)`, the owner's `egg_period_neck` read on the oval (`ovalPeriod_ellipse`, `ovalPeriod_neck`, `ovalPeriod_neck_log`), and `∫_A^B du/√(u(u − A)(B − u)) = (2/√B)K(√(1 − λ))` (`integral_legendre_form`); round the neck every continuous lift of `λ(β)` gains `4πi` and of `1 − λ` nothing, round the ellipse a lift of `1 − λ` gains `2πi` and of `λ` nothing (`neck_lambda_gain`, `neck_one_sub_gain`, `ellipse_one_sub_gain`, `ellipse_lambda_gain`, through the owner's `continuous_lift_unique`); the owner's formal continuation shifted by these gains moves the period basis at `λ = 0` by `A² = [[1, 4], [0, 1]]` at the neck, and in the chart `μ = 1 − λ` by `A` at the ellipse, a move conjugate to the owner's `B⁻¹ = S A S⁻¹` (`shiftLog_legendreBasis_four`, `neck_move`, `ellipse_move`, `B_inv_eq_conj_A`); both are shears of trace `2`, with entries the discriminant's orders `4` and `2` (`moves_are_shears`, `shear_entries_discriminant_orders`); the egg `(2, 1, 1)` with `λ = 1/9` and period `(2/3)K(√(8/9))` (`egg_211_period`) | #410's box "The egg as an elliptic family" (ticked); `EllipticCurve/EggFamily`'s "What is not claimed" and `egg_period_neck`'s docstring | `egg.oval-period`, `egg.null-monodromy` (new); `egg.elliptic-family` (scope) |

The boxes these answer, by their opening words: "The information port" (ticked); "The egg as an elliptic family"
(ticked); and "`series.log-atanh`, … `analytic.euler-maclaurin-eta`" (part done).

## 2. What the pass corrected

1. The box joins `R⁻¹dR` to `physics::information::apply`, which retired with `crates/holonics` (C8 of #603, held at
   `d5ed4adc1`); the join is made to the Lean owners, and `Physics/Information`'s `[open]` paragraph, which said "Owed
   in #62" (#62 closed into #410 on October 22), now names the module. The paragraph also said the restoring leg's zero
   production "presupposes" the finite-step limit; in Lean that zero is a theorem of the computed end states
   (`restore_production_zero`), and what is added is that it is also the limit of finite legs. `PortWork` calls
   `log(qᵢ/pᵢ)` "the ratio covector", which is twice the real part of `Objects/Ratio.logRatio`, while
   `Objects/RatioPhase` keeps "covector" for `R⁻¹dR`, its derivative: two senses of one word. And the thermal port's
   return `θD(p‖q)` reads the modulus face weighted by the population, while the lifted excess's code face `D(q‖p)`
   reads it weighted by the target, opposite orientations of the divergence that neither owner named
   (`modulus_face_readings` states both).
2. The brief gave η′'s series as `Σ (−1)^n log(n + 1)(n + 1)^(−s)`; that is `−η′(s)`, and the module uses `η′(s) = Σ
   (−1)^(n+1) log(n + 1)(n + 1)^(−s)`. The atlas row `analytic.euler-maclaurin-eta` and `CertifiedCapture`'s "What is
   not claimed" said the jets, complex `s`, the higher Bernoulli terms and the start from a grain were not stated; both
   now name this module for what it states and keep the rest. The constant of the `B₂` remainder is `1/384` against the
   classical `1/720`: the bracket's sign matches the classical term's, and the sharper constant is left.
3. The brief said the ellipse's loop is "carried to `λ = 0` by `legendre_comp_one_sub`"; that theorem is about
   polynomials, and a formal power series in `λ` admits no substitution `λ ↦ 1 − λ`, so carrying the basis at `1` to the
   basis at `0` is the connection matrix, which the owner leaves uncomputed. The module reads `ellipse_move` in the
   chart `μ = 1 − λ` and takes the conjugation from `B⁻¹ = S A S⁻¹` with the owner's rigidity. `EggFamily`'s "What is
   not claimed" named "`[[1, 2], [0, 1]]` at the ellipse" without "conjugate to": in the basis at `λ = 0` that move is
   `B⁻¹ = [[1, 0], [−2, 1]]`, and it is `A` only in the basis at `λ = 1`; the paragraph now says so. The brief stated
   the integral for `0 < w < a` and `b > 0`; it holds for `0 ≤ w < a` and every `b`, with `b > 0` needed only for the
   differential, and `w ≥ 0` is load-bearing because `K(√(1 − λ))` reads `K(0)` when `λ > 1`.

## 3. What each statement stands on, and what is left

- `Physics/InformationPort` stands on `PortWork`'s protocol and canonical states, `Objects/Ratio`'s `logRatio`,
  `Objects/RatioPhase`'s `alignCost` and `ratioCovector`, the first law's continuous chart, and `HNN/Ratio/Resolution`'s
  Hoeffding bound (`klDivergence_face_shift_le`, atlas `receiver.resolution-tilt-divergence`), reused rather than proved
  again. Left: a continuum (measure) transport of the aperture with Reynolds' theorem, the port's own protocol on a
  moving support, a quantum phase port, the HNN's discrete phase step and grain chart, and the sharpness of the `1/N`
  bound.
- `Mathematics/ZetaJets` stands on `CertifiedCapture`'s `zetaTail`, `eta` and `image_box_subset_box`, and on Mathlib's
  `LSeries_iteratedDeriv`, `zeta_eq_tsum_one_div_nat_cpow` and `hasDerivAt_tsum_of_isPreconnected`. Left: η's jets at
  complex `s`, ζ and η's identity on `0 < Re s ≤ 1` (the continuation), the Euler–Maclaurin terms past `B₂` with their
  Bernoulli numbers and rising products, the complex `B₂` term, the sharp `1/720`, the owner's least start by bisection,
  and `ComplexJet2` as data.
- `EllipticCurve/EggPeriod` stands on `EggFamily`'s curve, branch points and closed form,
  `Geometry/HypergeometricMonodromy`'s formal logarithm and rigidity, `Geometry/EggModular`'s `eggLambda` and
  `Objects/RatioPhase`'s continuous lifts. Left: Kodaira's types and the resolved surface, the analytic continuation of
  `K` or of the period in complex `β` (the moves are formal), the monodromy on `H₁` of the actual cycles, the connection
  matrix between the bases at `0` and `1`, the vanishing cycle's period, and the period as a contour integral on the
  curve.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as unstated (`Physics/Information`'s `[open]` paragraph, `Information/CrossEntropyRate`'s scope line and `Information/PortWork`'s paragraph on the phase face; `EllipticCurve/EggFamily`'s "What is not claimed" and `egg_period_neck`'s docstring; `Mathematics/CertifiedCapture`'s "What is not claimed"), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules (8,864 jobs), on `+HolonicsResearch` (10,644 jobs) and on `Holonics` (9,166 jobs, rebuilding `Physics/Information`, `Information/CrossEntropyRate` and `Information/PortWork` and their importers) completed with exit 0; the only warnings from a changed file are `Information/PortWork`'s two at lines 413 and 432, which stood one line higher before this change (its diff is its docstring alone). Run on the cloud session's four-core host, which rule 4 reaches for a Lean check.
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
