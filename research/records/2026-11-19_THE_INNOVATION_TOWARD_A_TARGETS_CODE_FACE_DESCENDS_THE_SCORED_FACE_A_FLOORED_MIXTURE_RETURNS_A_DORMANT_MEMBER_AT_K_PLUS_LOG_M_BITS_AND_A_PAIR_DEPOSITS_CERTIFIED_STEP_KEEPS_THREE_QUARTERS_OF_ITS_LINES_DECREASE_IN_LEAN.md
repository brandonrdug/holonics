# The innovation toward a target's code face descends the scored face, a floored mixture returns a dormant member at K plus log M bits, and a pair deposit's certified step keeps three quarters of its line's decrease, in Lean

November 19, 07:59 UTC. The fourteenth formalization pass over #410, its fifteenth set, after [the
fourteenth](2026-11-19_ROUTES_BETWEEN_FRAMES_AGREE_WHERE_THEIR_CYCLES_ARE_FLAT_THE_LOADED_RINGS_TICK_IS_THE_MODE_QUOTIENTS_SYSTEM_AND_A_WIDE_FACE_IS_READ_ON_ITS_MANTISSA_WITH_A_ONE_SIDED_WIDENING_IN_LEAN.md)
(#1025). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `HNN/TargetFaceDescent` | The base-2 code length `ℓ_t(z) = −z_t + log₂ Σ_c 2^(z_c)` has gradient `p(z) − q` along every direction, the chart's `ln 2` cancelling (`hasDerivAt_codeLength`), lies above its tangents by Jensen and is convex on segments (`codeLength_tangent`, `codeLength_segment_le`); the innovation toward the code face `χ = m e_t` therefore pairs with the reached covector as `⟨q − p(z), χ − z⟩ ≥ ℓ_t(z) − ℓ_t(χ) ≥ ℓ_t(z) − 1/L` under the margin law, and descends the scored face strictly on the whole segment wherever the face codes the target worse than the code face (`innovation_descends`, `codeFace_innovation_descends`); for any normalized face `r`, the odometer's `p̃` included, `⟨q − r, χ − z⟩ = Σ_(c≠t) r_c (m − (z_t − z_c))`, the margin's shortfall weighed by the face, positive when every margin is below `m`, gauge-free (`pairing_shortfall`, `pairing_pos`, `odometer_pairing_innovation`, `pairing_gauge`); at the locus the rank-one map direction pairs as `⟨q − r, χ − W f⟩⟨f, f⟩` (`map_pairing`, `map_innovation_descends`); one reached sample's exogenous step moves the logits along the innovation with gain `s = w⟨f, H′⁻¹f⟩ ∈ [0, 1]`, proved from `⟨f, u⟩ = ⟨u, H u⟩ + w⟨f, u⟩²` without Sherman–Morrison, so the receiving locus's own deposit descends the scored face below the chord `(1 − s) ℓ_t(W f) + s ℓ_t(χ)` (`gain_mem_unit`, `exogenous_one_sample_descends`, `exogenousDeposit_codeFace_descends`); witnesses: the innovation is not the covector at `z = (0, 0, 1)`, `m = 2` (pairing `2`), and a two-sample window on one feature raises the summed score at rate `2/15` (`innovation_is_not_the_covector`, `window_first_order_rise`) | #410's box "Descent of the scored cross-entropy face"; `HNN/TargetFace`'s open paragraph; the campaign one record of September 25 (Decisions 26 and 27); `HNN/Ratio` (`codeLength`, `odometerWeight`) | `hnn.target-face-descent` (new), `hnn.target-code-face`, `hnn.exogenous-normal-law`, `receiver.odometer-pairing` |
| `Compression/Landmark/FlooredSwitching` | One context's executed chart, abstracted to three laws (each weight at least its rounded product `ρ_t w_t(f) P_t(f)`, the total at most `(1 + ε_t)` times the meeting `V_t`, and the member taken up at a switch at least `2^(−K)` of every member), codes along every path within `−log₂(w_0(σ_0)/W_0) + Σ_t (−log₂ P_t(σ_t)) + k (K + log₂ M) + Σ_t (log₂(1 + ε_t) − log₂ ρ_t)`, `k` the switches before the last tick, since at a switch the member taken up holds at least `2^(−K)/M` of the total (`path_share`, `segment_telescope`, `segment_code`); `log₂(1 + y) ≤ 2y` and `−log₂(1 − x) ≤ 3x` bound the drift by `3 r 2^(−R) + M φ 2^(1−K)` (`drift_le`); the floor `û(f) = max(u(f), 2^(−K) max_g u(g))` raises the total by at most `M 2^(−K)` of it and not at all where it does not bind, keeps the leader, holds every member at `2^(−K)` of every member and zeroes none, so a chart opened at a prior, multiplied, rounded and floored meets the three laws and codes within the box's bound with its drift certified (`floor_raise`, `floor_leader`, `floor_holds`, `floor_keeps_dormant`, `executed_laws`, `executed_floor_code`); two members exchanged on `0^N 1^N` (faces `7/8`, `1/8`): the static mixture codes `N log₂ 7` bits above the switching path, the floored chart at most `K + 2 + 8N 2^(−K)`, and at `N = 2`, `K = 2` the floored product `1537/25600` beats each member's `49/4096` (`static_bayes_pays_what_it_fell_behind`, `floored_codes_below_every_member`); at `π = 1/M` each context pays at most `log₂ M` over its best member, and contexts on their own clocks sum (`uniform_local_mixture_code`, `floored_local_code`) | #410's box "The executed floor's segment/switching bound"; the retired `receiver/population/local.rs` (`4fd4b973b^`) and the record of September 28, §5; `Compression/Landmark/Context/{Population,LocalWeighing,Dormancy}` | `receiver.population-floored-switching` (new), `receiver.population-local-mixture` |
| `HNN/PairDepositStep` | A pair deposit's oriented reads, each a slip `Δ_r = v_r − (E − B) e_(x_r)` of the carried image of the antecedent's prior against the learned part of the consequence's column, give a score `Q = Σ_r |Δ_r|²` that is a quadratic along any step, `Q(E + ηD) = Q − ηa + ½η²C` for every `η`, with `C ≥ 0` and `C > 0` wherever `a > 0`, so `quadratic_upper_model` is attained (`Reads.score_along`, `Reads.score_ray`, `Reads.curvature_pos`); the certified exponent `min(⌊log₂(a/C)⌋, ⌊log₂(1/c)⌋)` through `Int.log 2` is the largest `k` with `2^k C ≤ a` and `2^k c ≤ 1`, monotone in `a`, `C`, `c`, its halving keeps both bounds (`certExp`, `admits_iff`, `certStep_spec`, `certExp_mono`, `halved_admits`); at it `Q′ ≤ Q − ½ηa`, the line's minimizer is `a/C` at `Q − a²/(2C)`, and where the curvature binds the certified step lies in `(η*/2, η*]` and keeps three quarters of that decrease (`Reads.certified_descent`, `Reads.line_minimizer`, `Reads.certified_three_quarters`); the source port's normal law with one-hot features moves the port by the unit step `D e_k = S_k/(h_k + n_k)`, whose alignment `a = 2 Σ_k |S_k|²/(h_k + n_k)` is nonnegative and zero only where nothing moves, and any chart `D = G M` with `⟨v, M v⟩ ≥ 0` aligns (`Reads.normal_unit_step`, `Reads.unit_step_alignment`, `Reads.unit_step_alignment_eq_zero_iff`, `Reads.chart_alignment_nonneg`); `Q = 0` iff `(E − B) T = U B` on the menu's classes (`Reads.consumer`); at the opening with one read per class and `h + 1 = 2^j`, `c(h + 1) ≤ 1`, the certified step is the minimizer `h + 1` and closes every slip (`Reads.opening_certified`); the record's order-2 numbers `Q = 120`, `a = 120`, `C = 60`, `c = 1/2` certify `η = 2` and close the slip, and a port of two rows and three classes under a quarter turn closes at `η = 2` with entries in `{0, ±½, ±1}` (`order_two_certificate`, `order_two_reading`, `port_deposit`) | #410's box "The pair deposit's certified quadratic step"; the retired `hnn/executed.rs` and `holon/deposition.rs` at `d5ed4adc1` (`pair_deposit`, `deposit_reads`, `CertifiedStep::certify`); the record of October 5 on located keys; `Holon/Deposition`, `HNN/Normal`, `HNN/PairedDeposit` | `hnn.pair-deposit`, `holon.certified-step` |

The boxes these answer, by their opening words: "Descent of the scored cross-entropy face"; "The executed floor's
segment/switching bound"; "The pair deposit's certified quadratic step".

## 2. What the pass corrected

1. **The relation the box asked for is a weighted margin shortfall, and the window's step can rise.** The pairing of the
   reached covector with the innovation is the face's mean, over the other classes, of `m − (z_t − z_c)`, for the smooth
   face and the odometer's masses alike; "zero exactly where every margin equals `m`" holds only with one-sided margins,
   and `pairing_zero_needs_one_side` (`r` uniform, `z = (0, −1, −3)`, `μ = 2`) shows it vanishing elsewhere. The descent
   bound in code length holds for the smooth face's covector `q − p(z)`; the odometer's `q − p̃` enters through the
   identity alone, positive under margins below `m`, with no code-length bound of its own. Decision 26 left descent
   open, and Decision 27 of the same record retired the exogenous target in campaign 1 because averaging one-hot code
   faces in the log chart settles the logits at `m p̄`, a flatter face than `p̄`: `window_first_order_rise` states that
   reading at first order. `HNN/TargetFace`'s open paragraph now points here and names Decision 27, and its docstrings
   no longer call a target, a receipt or an integer law exact; it still said descent was "owed in #62", which closed on
   October 22 into #410.
2. **The box's bound needs its terms read as stated here.** Its `−log₂ π_(f₀)` is the opening's share
   `−log₂(w_0(f_0)/W_0)`, which is the prior's only where the opening is a prior; its `k` counts the switches before the
   last tick, since a switch at the passage's end costs nothing; and the drift's two inequalities, `−log₂(1 − x) < 3x`
   and `log₂(1 + y) < 2y` in the retired header and the record, are equalities at `0` and are stated with `≤`. The Rust
   header and the record call the unfloored mixture's weights and faces "exact"; the theorem is named for what it
   measures, `static_bayes_pays_what_it_fell_behind`. The atlas row `receiver.population-local-mixture` said the segment
   telescope was owed in #62 and the uniform prior's per-context bound was not in Lean; both now are, and the row points
   to the new one.
3. **The deposit takes the certified dyadic step, not the line minimizer.** The retired law table called the deposit's
   step "its exact line minimizer"; the step is the largest dyadic the curvature and the covector scale admit, which is
   the minimizer `a/C` only at the opening with `h + 1` dyadic, lies in `(η*/2, η*]` where the curvature binds, and can
   be smaller where the covector bound binds. The atlas row `hnn.pair-deposit` said the quadratic holds "exactly"; it
   holds for every `η`, and the row now says so, with the grade `formal-checked` and the run's adoption checks named as
   not stated. For the pair deposit `a > 0` forces `C > 0`, so the retired `certify`'s branch for a positive alignment
   with neither bound present is never reached. The row and the Rust doc call `c` the largest covector entry of one
   return, where `deposit_reads` takes the largest entry over every read's slip at once. `holon.certified-step` listed
   the machine's dyadic step as not in Lean; it now is.

## 3. What each statement stands on, and what is left

- `HNN/TargetFaceDescent` stands on `HNN/TargetFace` (`codeFace`, `MarginCodes`, `margin_rule_codeLength`,
  `exogenousStep`, `exogenousDeposit`, `targetWindow`), `HNN/Ratio` (`codeLength`, `odometerWeight`) and Mathlib's
  `convexOn_exp`. Not stated: strict decrease of the grain-quantized score (`quantized_score_has_grain_plateau` refuses
  it), the comparison's phase part, the prox step's proxy, a descent law for a window of two or more samples (only the
  first-order rise is read, not the change at the window's endpoint), the gain's bound at an executed chart `X̂`, and
  the odometer's sign where margins pass `m`.
- `Compression/Landmark/FlooredSwitching` stands on `Compression/Landmark/Context/Population.local_mixture_code`,
  `LocalWeighing.{static_mixture, neg_logb_le_of_le}` and `Dormancy.stay_code_le`. Not stated: the gating ladder's
  choice of rung and its charge `⌈log₂ |ladder|⌉`; the `PassageCode` enclosures; that the retired Rust's product of a
  64-bit mantissa and a face lands within `[1 − 2^(−62), 1]` of the unrounded product and that its counters count `r`
  and `φ` (hypotheses here); a member at zero likelihood; the floor's comparison with the declared fixed share on the
  hazard ladder (`Dormancy.share_path_code_le`), which the record names as owed; and any rate over a family of passages
  beyond the one witness.
- `HNN/PairDepositStep` stands on `Holon/Deposition.{certified_step_descends, quadratic_upper_model}` and
  `HNN/Normal.{depositLocus, frobenius_chart}`, with Mathlib's `Int.log`. Not stated: the entry bound `2³`, the
  constitution's storage growth and its budget, the retention fibre the normal law reads, the ring's transport `P^(t_r)`
  (abstracted as the carried image), and `c` as the run read it; the normal law's step assumes `h_k + n_k ≠ 0` at every
  class, since a class no read reaches with `h_k = 0` makes the Gram singular. `Holon/Deposition`'s open paragraph still
  says the certified step is owed in #62; it is left as it stands because editing that module rebuilds most of the
  `Holonics` library, and this module and its atlas rows carry the pointer.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repaired the open paragraph of `lean/Holonics/HNN/TargetFace.lean` (it now points to the new descent module and names Decision 27, and its docstrings no longer call a target, a receipt or an integer law exact; the module and its importers were rebuilt), and wrote the atlas rows and this record. No guide sentence named these three statements as owed. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3716 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10611 jobs)`, exit 0; `Holonics`, with `HNN/TargetFace` and its importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused simp arguments, unused variables, universe notes), none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
