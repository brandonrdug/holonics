# Maxwell keeps Gauss along every motion, heat on a partition raises entropy by half its Fisher information, a reading's leverage is a series over its pivots, and the rank falls where a prime divides every minor, in Lean

November 19, 02:30 UTC. The seventh formalization pass over #410, its seventh set, after
[the sixth](2026-11-19_THE_STRENGTH_IS_THREE_TIMES_THE_FREE_FUNCTIONS_OF_THREE_VARIABLES_SHEETS_DO_NOT_COARSEN_WHERE_A_WORD_CROSSES_BACK_THE_SURVIVORS_ARE_THE_CYCLE_FIBRE_AND_A_KEYS_MOVE_IS_THE_DERIVATIVE_OF_THE_CODE_IN_LEAN.md)
(#1016). Eight new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #405, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/MaxwellComplexFlow` | Ampère–Maxwell and Faraday on a complex as a flow, `Ḋ = d₁ᵀ P_m B − J` and `Ḃ = −d₁ P_e D` as `HasDerivAt` at every time (`MaxwellFlow`); the charge read moves by `−d₀ᵀ J` (`gauss_rate`), so with continuity Gauss's law at one time holds at every time, for every vertex coboundary `d₀` with `d₁ d₀ = 0` (`gauss_preserved`, `charge_constant`); `d₂ B` is constant (`magnetic_gauss_preserved`); with symmetric constitutions the stored energy moves by `−⟨P_e D, J⟩` (`energy_rate`); under a change of edge chart `P` with a left inverse `Q` the incidences still form a complex, the charge and the pairing are unchanged and a flow stays a flow (`rechart_complex`, `charge_rechart`, `pairing_rechart`, `MaxwellFlow.rechart`), an orientation reversal among them (`flip_charge`). | #410's box 9 | `maxwell.complex-flow` (new), `maxwell.stokes-dirac` |
| `HNN/ReadingLeverageSeries` | A bordered matrix has determinant `det A · (d − wᵀ A⁻¹ u)` (`det_border`); one more pivot multiplies the minor by its Schur complement, `Δ_(k+1) = Δ_k s` (`delta_succ`), the border entry is `Γ_k = Δ_k t` (`gamma_eq`), and the leverage grows by `t²/s` (`lev_succ`), so `h_r = Σ_(k<r) Γ_k²/(Δ_k Δ_(k+1))` (`lev_eq_series`) and the bordered corner is `−Δ_r` times that series (`corner_eq_series`), every pivot positive on a positive definite Gram (`delta_pos_of_posDef`). | #410's box 267 (its owed series); the record of October 24, §9 | `contact.reading-leverage` |
| `HNN/ReadingLeverageError` | For white noise, `E[(β + Σ_s c_s e_s)²] = β² + σ² Σ_s c_s²` (`integral_white_sq`); the fitted form's error at a new reading is the bias `⟨v, w⟩ − ⟨v, G⁻ G w⟩` plus a combination of the noises (`error_eq`), its mean square is `bias² + σ²(1 + \|X G⁻ᵀ v\|²)` (`meanSquare_error`), and in range, for any generalized inverse, the bias vanishes whatever the true form and the mean square is `σ²(1 + h)` with `h = vᵀ G⁻ v = uᵀ G u` (`range_identities`, `meanSquare_error_of_mem_range`). | #410's box 267 (its owed error); the record of October 24, §10 | `contact.reading-leverage` (both modules) |
| `Aeon/Production/ComplexEntropyBalance` | Stokes on a complex and the total rate of a balanced density (`stokes`, `sum_divergence_eq_zero`, `hasDerivAt_total`, `hasDerivAt_total_production`); passive and linear constitutions (`passive_linear`, `production_linear`, `linear_production_eq_zero_iff`, `sub_mul_log_sub_nonneg`); on the pair complex of a master equation the local balance `ṡ_x + Σ_y J_s(x,y) + φ_x = σ_x` (`hasDerivAt_density`, `hasDerivAt_density_complex`), the summed `dH/dt = σ − Σφ` (`hasDerivAt_entropy`), and the total production is `PathReversal`'s epoch production, zero exactly under detailed balance (`totalProduction_eq_epochProduction`, `totalProduction_eq_zero_iff`); the bath flux reads the affinity clock (`bathFlux_eq_affinity`). | #410's box 242; the record of October 22 on order and torsion, §5 | `aeon.complex-entropy-balance` (new) |
| `Aeon/Production/PartitionDeBruijn` | Heat flow `ṗ = L p` on a partition with symmetric weights raises the entropy at `½ J_part(p)`, `J_part = Σ_(x,y) w (p_x − p_y)(log p_x − log p_y)` (`hasDerivAt_entropy_heat`, through `laplacian_eq_neg_outflow`, `bathFlux_eq_zero`, `totalProduction_eq_half_fisher`); `J_part ≥ 0`, zero exactly when the law is constant across every contact of positive weight (`fisherPartition_nonneg`, `fisherPartition_eq_zero_iff`); `J_part = 2σ`, zero exactly under detailed balance (`fisherPartition_eq_two_mul_epochProduction`, `fisherPartition_eq_zero_iff_detailedBalance`); mass is kept and the entropy rises (`sum_laplacian_eq_zero`, `entropy_monotone_heat`); two cells give `Physics/TwoCellEntropyTransport`'s production (`hasDerivAt_entropy_twoCell`). | #410's box 241; the same record, §5 | `thermal.partition-de-bruijn` (new), `xent.two-cell-production` |
| `Landmarks/ClosureKeyTorsion` | `r ≤ rank A` iff some `r × r` minor is nonzero (`le_rank_iff_exists_minor`); for an integer system `rank_p A ≤ rank_ℚ A`, with `rank_p A < rank_ℚ A` iff `p` divides every maximal minor iff the kernel modulo `p` is wider (`modRank_le_ratRank`, `modRank_lt_ratRank_iff`, `finrank_ker_lt_iff`), each such prime a factor of any nonzero maximal minor (`torsion_prime_mem_primeFactors`); a minor prime to `p` and a kernel with a `δ`-times-identity block certify both ranks (`rank_certificate`); on `ℤ/(b + 1)` a leading-first digit word is its word of half-turns and its alternating digit sum (`halfTurn_step`, `readLeading_halfTurns`, `readLeading_alternatingSum`), `ℤ/110 ≅ ℤ/10 × ℤ/11` (`newlineTorsionSplit_natCast`); keys linear in the digits for sums exist modulo `q` exactly when `q ∣ b(b + 1)` (`SumKey.zmod_exists_iff`), with base ten's keys modulo 11, 10 and 110 (`SumKey.eleven_moves`, `SumKey.units_moves`, `SumKey.torsion110_closure`); for differences exactly when `q ∣ 2b` (`DiffKey.zmod_exists_iff`, `DiffKey.twenty_moves`, `DiffKey.exact_closure`); for sums with `=` reflecting exactly when `q ∣ b(b − 1)` (`SumKey.zmod_reflected_exists_iff`). | #410's box 270 (#405); `tower_ring::{rational_rank, closure_key}` at `700649f67`; the newline record of October 25, §§2, 5, 10, 11 | `linalg.rank-falls-mod-p` (new), `hnn.tower-ring-closure`, `key.newline-closure-torsion`, `key.newline-closure-differences`, `key.newline-closure-reflection`, `radix.cheap-faces` |
| `HNN/LetterPriceAndLoudReturn` | On a base-two face, `F` letters founded at logit `c` raise every standing code by `Δ = log₂(1 + F·2^c/Σ_a 2^(z_a))` (`price_eq`, `price_nonneg`, `price_le`), the fresh classes' joint share is `q` with `1 − q = 2^(−Δ)` (`freshShare_eq`, `one_sub_freshShare`), each standing share falls by `p·q`, between `0` and `q`, by `q` relative to itself, the faces `2q` apart in summed absolute difference (`share_drop_le`, `relative_drop`, `l1_eq`), and where every standing logit is at least `c`, `q ≤ F/(A + F)` and `Δ ≤ log₂(1 + F/A)` (`freshShare_le_of_cMin`, `price_le_of_cMin`); the loud face's code covectors `δb = δβ`, `δκ_ℓ = δβ λ_ℓ`, `δλ_ℓ = δβ κ_ℓ` with `δβ = Σ_a (p_a − [a = t]) v_a` (`hasDerivAt_code_b`, `hasDerivAt_code_kappa`, `hasDerivAt_code_loudness`), the radial part along the lane (`hasDerivAt_loudness`, `hasDerivAt_code_radial`, `radial_eq_smul`), and at the grain the release's step (`grain_flat`, `grain_not_smooth`, `central_difference_near`). | #410's boxes 147 and 382; the opening's room record of November 12, §4 item 4; #826; `Constitution::{lettered, loud_beta, loud_return, tied_sharp}` | `tower.field-letter-founding-price` (new), `tower.face-loud-return-adjoint` (new) |
| `HNN/ReactionCovector` | For `x^(k+1) = T_k x^k − κ R_k x^k` founded at `κ = 0` (`traj_zero`), the orbit's tangent is `−Σ_(k<n) P_(k+1→n) ρ^k` (`hasDerivAt_traj`, `tangent_eq`), the reverse sweep is `λ^N = Φ′`, `λ^k = λ^(k+1) ∘ DT_k` (`adj_last`, `adj_step`), and the code's derivative in `κ` is `−Σ_k λ^(k+1)(ρ^k)` (`hasDerivAt_code`), so the box's `Σ_k ⟨λ^(k+1), ρ^k⟩` is the descent covector (`hasDerivAt_neg_code`), by places `−Σ_k Σ_j ⟨γ_j^(k+1), ρ_j^k⟩` (`hasDerivAt_code_inner`). | #410's box 154; the junction record of November 13, §13.8 | `tower.field-reaction-founding-covector` (new) |

The boxes these answer, by their opening words: "Maxwell's equations on the complex in `HasDerivAt` form"; "The
leverage of a new reading" (its owed series and error); "de Bruijn's identity on a receiver's partition"; "The entropy
balance on a complex"; "The founding of a letter at the least class bias"; "The reader's reaction at its founding"; "The
loud face's return is the adjoint of its forward". Seven boxes in all, and "The closure key's torsion" part done (§3).

## 2. What the pass corrected

1. **The sixth set closed nineteen boxes, not eighteen.** Its record counted eighteen; the boxes it lists are nineteen,
   and #410's tick of #1016 ticked nineteen. Its record now says nineteen.
2. **Box 9's "a coboundary independent of the incidence" has no recorded source.** No record states it. It is read two
   ways, both proved (`agent-inferred`): the vertex coboundary is any `d₀` with `d₁ d₀ = 0`, never built from `d₁`; and
   the charge it reads is the same in every chart of the edges. The rechart needs only a left inverse, `Q P = 1`.
3. **The entropy balance as worded holds only where no entropy goes to the medium.** `∂ₜ s + d*J_s = σ` needs the bath
   flux `φ_x = ½ Σ_y j log(W_xy/W_yx)` beside it unless the rates are symmetric: `ṡ + d*J_s + φ = σ`. `σ = Σ_c J_c A_c`
   counts each contact once, which is `½ Σ` over ordered pairs; and the split of production and current between a
   contact's two ends is one choice, of which only the total is fixed.
4. **De Bruijn's `½` is a convention of the generator.** It holds for `L` summed over ordered pairs, or `½L` over
   unordered contacts. The partition's Fisher information is the Dirichlet form `Σ w (Δp)(Δ log p) = Σ w (Δp)²/Λ` with
   the logarithmic mean `Λ`, the continuum's `|∇p|²/p` only with `Λ` in place of `p`, and its vanishing is edgewise.
5. **The closure key's box writes `b` for two things.** "Written differences with `b ≤ a < b²`" uses `b` for the base
   and the subtrahend; the record's §10 means the subtrahend at most the minuend, below the base squared. The atlas row
   now reads `y ≤ x < b²`. The sums clause needs the key's scale `s` a unit (else the zero key always exists), and it
   holds for every modulus, not only primes. "Wider than the rational kernel's reduction" is proved as a comparison of
   widths, since the reduction is a subspace only through the kernel's integral saturation. "Every maximal minor (the
   product of the Smith invariants)": the product is the minors' gcd.
6. **A letter's price is a mass ratio, and the share is something else.** "The fresh classes' share at the least bias
   over the face's standing sum" names `F·2^(c_min)/Σ 2^(z_a)`, a ratio of masses; the joint share is
   `q = M/(S + M) ≤ M/S`, and `q` is what bounds each standing share's fall. A bound in `F` and `A` alone needs every
   standing logit at least `c_min`; a plain face below zero breaks it.
7. **The reader's reaction covector is the descent covector.** `Σ_j ⟨λ_j^(k+1), ρ_j⟩` with `λ` the code's gradient is
   `−d(code)/dκ`, which matches the junction record's `d(code)/dκ = −Σ A`.
8. **"The derivative of the code at the grain" is false as written.** The grain's release is a step: `κ ↦ round(κ λ)`
   has derivative `0` at the founding for every `λ` and is never differentiable with derivative `λ` for `λ ≠ 0`
   (`grain_not_smooth`). What holds is the smooth derivative read at the grain's representative, which is what a
   central difference of step `h` reads within `1/(2h)`. The power's unit moves `∂z/∂κ_ℓ` (it adds a constant to every
   `λ_ℓ`) and neither `∂z/∂b` nor the radial part.
9. **The leverage's series is stated on the pivot block.** Its pivots are the block's leading minors; that an
   elimination passing zero pivots reads exactly these is the elimination's own and is not stated.

## 3. What each statement stands on, and what is left

- **Maxwell** is on a closed complex over ℝ; the boundary's Poynting flux and the continuum limit are not stated.
- **The leverage's error** is for white noise on a probability space and any generalized inverse; the charge
  `½ log₂(1 + h)` and the off-range limit `ε vᵀ(G + εI)⁻¹v → |(I − GG⁺)v|²` are not stated.
- **The entropy balance and de Bruijn** read the real chart with `p > 0` and rates of symmetric support; the flow
  `exp(tL)` is assumed of the path, and the continuum identity, its Gaussian instance, the scaling limit and
  Schnakenberg's cycle decomposition are not stated.
- **The closure key's torsion** is part done: left are the Smith-invariant form (Mathlib carries no determinantal
  divisors), the general pair key's torsion (the record's minors' gcds over the finite line sets), operands below `b³`
  (the primes of `2b`), differences with `−` reflecting, and the menu of sums and differences with `−` reflecting and
  `=` restarting.
- **The letter's price and the loud return** are on the face at temperature one in the smooth chart; the blank clock's
  route on a paced head and the chart's own route into the plain face are not stated.
- **The reader's reaction** is first order at the founding, with the ticks differentiable and the route continuous along
  the orbit; passivity `κ m² < 4` and second order are not stated.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the eight modules and `HolonicsResearch`: `Build completed successfully (10578
jobs)`, exit 0, with no declaration elaborated with `sorry`; 48 min 24 s of wall time (150 min of user time) on a
four-core cloud host, read beside three workers' single-file checks, so the time is the shared host's and not the
build's alone. `tools/lean_census.py` reads `unbuilt=0 unrooted=0`, and `tools/link_check.py atlas` and `links` read
`broken=0`. Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision on a cloud host, read by exit status (each `EXIT 0` with no output), for the reason the first pass's record
gives (`agent-inferred`). The research library's aggregator imports the eight modules.

Three workers on disjoint owner paths wrote five of the modules (`Aeon/Production/ComplexEntropyBalance`,
`Aeon/Production/PartitionDeBruijn`, `Landmarks/ClosureKeyTorsion`, `HNN/LetterPriceAndLoudReturn`,
`HNN/ReactionCovector`); the lead wrote `Physics/MaxwellComplexFlow`, `HNN/ReadingLeverageSeries` and
`HNN/ReadingLeverageError`, re-checked each file from the tree, and read every `L:` owner added to the atlas against its
module's declarations by `tools/link_check.py atlas`.
