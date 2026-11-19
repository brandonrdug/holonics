# Routes between frames agree where their cycles are flat, the loaded ring's tick is the mode quotient's system, and a wide face is read on its mantissa with a one-sided widening, in Lean

November 19, 07:40 UTC. The thirteenth formalization pass over #410, its fourteenth set, after [the
thirteenth](2026-11-19_A_CONGRUENCES_RATE_IS_A_BOOST_AND_A_TURN_AND_FOCUSES_WITHIN_N_OVER_ITS_EXPANSION_A_CIRCULANTS_INERTIA_IS_READ_BY_ITS_WINDINGS_AND_AN_ACTION_CLOSES_ON_A_KERNELS_MODES_OR_RETURNS_ITS_SEPARATING_DIRECTION_IN_LEAN.md)
(#1024). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73, #145.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Geometry/FrameRoutes` | In any group of relations, a route between frames (the owner's chained word `Aeon K a b` of `Aeon/Clock/Groupoid`, each relation crossed forward by its map or backward by its inverse) transports by the product of its steps, a concatenation by the composite and a reversal by the inverse (`transport_append`, `routeTransport_concat`, `routeTransport_reverse`); every two routes with the same ends transport alike exactly when every closed route's holonomy is the identity, and where every frame is reached from one base, exactly when the relations are a potential's differences (`routeIndependent_iff_flat`, `routeIndependent_iff_potential`); a change of charts conjugates transport and keeps flatness (`transport_regauge`, `flat_regauge_iff`), declared cells make it a homotopy invariant (`transport_wordHomotopic`, `classTransport`), and it is the owner's `followedByWord` and `parallelTransport` in their conventions (`transport_op`, `transport_perm`); a triangle is route-independent exactly when `r₀r₁ = r₂`, three translations by `e₁` disagree (`2e₁` against `e₁`), and a serial chain forces the route (`triangle_routeIndependent_iff`, `shift_routes_disagree`, `serialChain_routeIndependent`); the receiver's perspective ray is central projection from the focus `(0, 0, −f)`, stereographic projection is the ray at `f = −1`, and the receiver refuses a point exactly where the law's denominator vanishes (`perspective_central`, `stereographicMap_eq_perspectiveMap`, `ProjectionLaw.project_eq_none_iff`); over ℝ the projected rates are the retired formulas (`hasDerivAt_perspective`, `hasDerivAt_stereographic`, `hasDerivAt_orthographic`, `hasDerivAt_isometric`), the image is unbounded toward a focal-plane or pole-plane point off the axis, so no continuous extension exists (`perspective_no_continuous_extension`, `stereographic_no_continuous_extension`); the fibres are lines through the focus, the north pole, along `(0, 0, 1)` and along `(1, 1, 1)`, stereographic projection is injective on the sphere less the north pole with its rational inverse, and the isometric axes have squared length `2/3` (`perspective_fibre`, `stereographic_injOn`, `isometric_axes`) | #410's box "`frame.local-chart-relations`, `frame.receiver-projection`"; the retired `crates/holonics/src/geometry/{model,projection}.rs` (removed at `d329cb541`); `Aeon/Clock/Groupoid`, `Transport/CellHolonomy`, `Transport/MoveConventions`, `Transport/SerialScrewChain`, `Foundation/TransportWord`; the receiver records of September 14 and 17 | `frame.local-chart-relations`, `frame.receiver-projection` |
| `HNN/ModeQuotientRing` | The loaded ring's tick, owned as one linear operand by `HNN/LoadedRing.stepMap`, has as its blocks the four maps of `HNN/ModeQuotient`'s system: with `ω₀ = M_t⁻¹(2Cw − hK_t u)`, `T_t(u, w) = (u + hω₀, 2ω₀ − w)`, `B_t e = (hM_t⁻¹(he), 2M_t⁻¹(he))`, `ρ_t(u, w) = −(2/Y)ω₀`, `D_t e = e − (2/Y)M_t⁻¹(he)`, and at the ring's solve `(u + hω, 2ω − w) = T_t x + B_t e`, `ringOut Y e ω = ρ_t x + D_t e` (`stepMap_blocks`, `loaded_tick_linear_system`), the inverse existing and two-sided under `HNN/Ring`'s certificate (`ring_inverse_exists`, `leftInverse_of_certified`); a periodic stiffness with two-sided inverses makes the system periodic (`inverse_periodic`, `loaded_periodic_of_inverse`); the quotient's run of the pump's phase family is the ring's own word `LoadedRing.resonance` and its returned wave `resonanceOut` (`run_eq_resonance`, `read_eq_resonanceOut`), so the period lift, the shared chart and the descended run hold on the ring's data (`loaded_period_lift`, `loaded_release_silent`, `loaded_descended_run_reads`); a release lies in `ker K_t × ker C` for a chart closing every square, and the phase family's kernel at every phase `i < P` (`chart_release_storage_null`, `phase_kernel_storage_null`); the material variation is the blocks `φ_t x + H_t e` of one map, pairs with the solved covector as `loaded_tick_material_variation` does, and its gain covector summed along the ring's word descends through a chart it factors through, which the capacity and dissipation families do for every closing chart and the stiffness and pump families do when the pump holds a half-turn (`variation_pairs`, `ringGain_eq_resonance_sum`, `loaded_gain_descends`, `capacity_gain_factors`, `dissipation_gain_factors`, `stiffness_pump_gain_factors`); a one-dimensional witness at `M = 7/2` | #410's box "The mode quotient on the concrete ring"; `HNN/ModeQuotient`, `HNN/Ring` §2 and §2′, `HNN/LoadedRing`; `docs/HNN_FORMULA.md` §4 | `hnn.mode-quotient-loaded-tick` (new), `hnn.mode-quotient-period-lift`, `hnn.mode-quotient-one-chart`, `hnn.mode-quotient-descended-run`, `hnn.mode-quotient-storage-null`, `hnn.mode-quotient-gain-descent` |
| `Compression/WideFaceReading` | A natural `N ≥ 2^G` read on its top `G` bits `m = ⌊N/2^s⌋`, `s = ⌊log₂ N⌋ + 1 − G`, has `2^(G−1) ≤ m < 2^G` and `s + log₂ m ≤ log₂ N < s + log₂(m + 1)` (`mantissa_bounds`, `logb_mantissa_encl`, `residual_lt` through `Tree.rebase_log_residual`); `log₂(m + 1) − log₂ m ≤ 1/(m ln 2) ≤ 2^(1−G)/ln 2 < 3·2^(−G)`, from `ln 2 > 2/3`, so an enclosure `[lo, hi]` of `log₂ m` widens to `[s + lo, s + hi + 3·2^(−G)]` of `log₂ N`, narrow faces included (`logb_succ_sub_lt`, `widen`), and below the grid at `G = O + 2` (`widening_lt_grid`); a positive rational face read on its own mantissa, the first Rust form, encloses `−log₂ q` in `[lo − 3·2^(−G), hi]` (`faceMantissa_bounds`, `face_widen`); with each binary log a floor read at `B` fraction bits (`BinaryLog.log_encl` gives it, `floorRead_of_encl`), `−log₂(n/d)` is enclosed at width `2^(1−B) + 6·2^(−G)` (`codeLength_encl`, `codeHi_sub_codeLo`); a product kept to `K` significant bits after each factor, rounded down on one side and up on the other, encloses the product and spreads by at most `(1 + 2^(1−K))^(2k)` over `k` factors (`kept_bounds`, `product_encl`, `productUpper_le`, `productUpper_div_le`); the witness `N = 2^100 + 2^99 + 1` at `G = 98` reads `s = 3`, `m = 2^97 + 2^96`, `100.5 ≤ log₂ N ≤ 100.625 + 3·2^(−98)` (`witness_encl`) | #410's box "The wide-face reading"; the landmark tree's record of September 26, §3 and §4; the retired `hnn/landmark.rs` (`4934cd163`) and `compression/landmark/context.rs` (`b09cc1192^`: `code_length`, `ratio_code_length`, `ProductBound`); `Compression/Landmark/Context/{Tree,BinaryLog}` | `hnn.wide-face-reading` (new), `hnn.passage-code`, `receiver.merge-code-length-pair`, `receiver.priced-birth` |

The boxes these answer, by their opening words: "`frame.local-chart-relations`"; "The mode quotient on the concrete
ring"; "The wide-face reading".

## 2. What the pass corrected

1. **Route independence is flatness, not a unique route.** `frame.local-chart-relations` read "geometry is compared only
   along a unique route or an explicitly supplied route", and the retired `transport` refused, as ambiguous, every pair
   joined by two simple paths, a flat cycle included, where every route gives one value; the law is that routes agree
   exactly when every closed route's holonomy is the identity, a tree being only the case with no cycle, and the row now
   says so. The perspective ray's unbounded approach needs `f ≠ 0` (at `f = 0` the map is zero). The retired refusal
   message "the point is the stereographic receiver pole" fired on the whole plane `z = 1`, the pole only on the unit
   sphere; the module names the pole plane. The retired `depth` (`z`, `f + z`, `1 − z` by law) was an ordering, not the
   refusal's denominator, and the module keeps the two apart (`ProjectionLaw.denom`, `1` for the orthographic chart).
2. **The bridge runs through `HNN/LoadedRing`, and periodicity needs two-sided inverses.** The box named "`HNN/Ring`'s
   loaded tick", while the tick as one linear operand, its run and its phase are `HNN/LoadedRing`'s; the four maps are
   that owner's blocks, so no copy of the tick was made. A periodic stiffness makes the maps periodic only when the
   inverses are two-sided or themselves periodic: an executed right inverse per tick need not be (`inverse_periodic`
   states the condition). `ModeQuotient`'s header item 4 stated `K_rel ⊆ ker K_t × ker C` as proved while
   `hnn.mode-quotient-storage-null` marked it "not in Lean"; it is now proved for chart kernels and for the phase
   family's kernel at every phase, and the row's note is retired. The half-turn's factoring needs `g_K, g_P ≠ 0`, which
   `half_turn_separates` assumes; the row says so. `ModeQuotient`'s cycle lemmas fix their spaces in `Type` (one
   universe for the face map), so the period-lift corollaries here take `E : Type`.
3. **The widening falls on one end, and the record's form had already moved.** "Its enclosure widened by `3·2^(−G)`"
   widens the upper end of `log₂ N`, the lower end of `−log₂ q`: the first Rust read the face's own mantissa and widened
   once (`face_widen`), while reading `n` and `d` apart pays it twice, `6·2^(−G)`, which is the width itself and not
   only a bound (`codeHi_sub_codeLo`). The record of September 26 says the wide-face reading is "stated in Rust and
   checked by tests"; that form stood from `4934cd163` to `aaeff7ff7` that day, and by the last Rust (`b09cc1192^`) the
   wide face was read inside `binary_log`'s founding (`hi = lo + 1` at `P = 125`), with no separate `3·2^(−G)` term,
   which is why the box found no owner. `receiver.merge-code-length-pair` and `receiver.priced-birth` listed the 127-bit
   product bounds as not in Lean; their enclosure and spread are now, while the KT price decision on them is not, and
   the rows say so.

## 3. What each statement stands on, and what is left

- `Geometry/FrameRoutes` stands on the owners' words and holonomies (`Aeon/Clock/Groupoid`, `Transport/CellHolonomy`,
  `Transport/MoveConventions`, `Transport/SerialScrewChain`, `Foundation/TransportWord`) and on Mathlib's one-variable
  derivatives and filters. Not stated: the retired simple-path counting itself, a general tree theorem (only the serial
  chain), `LocalChart`'s origin, basis, Gram and orientation, the hinge and Cayley relations, the receiver's spins and
  gauge, the moving-frame rate `Lṗ + L̇p + ḃ`, conics, hinges and crossing diagrams (`frame.receiver-topology`), the
  focal-plane point `(0, 0, −f)` itself, and jets past the first derivative.
- `HNN/ModeQuotientRing` stands on `HNN/ModeQuotient` (the period lift, the shared chart, the descended run, the
  released pair's storage, the gain covector and its factoring lemmas), `HNN/LoadedRing` (`stepMap`, `resonance`,
  `resonanceOut`, `phaseAt`) and `HNN/Ring` (the certificate's nonsingular denominator, the material variation, the
  gained families). Not stated: the costate's recursion on the ring's ports and `learning_chart_le_kernel` on the ring,
  the converse of the storage result, stiffness or pump factoring without a half-turn (barred at a standing pump at
  threshold), the executed lattice chart and split, and the retired `hnn::modes`. `ModeQuotient`'s own docstring words
  ("under the exact law", "The exact condition") are left for a curation pass, since `HNN/ModeQuotient` sits under
  `Holonics/HNN` and an edit there rebuilds much of the library.
- `Compression/WideFaceReading` stands on `Compression/Landmark/Context/Tree.rebase_log_residual`,
  `Compression/Landmark/Context/BinaryLog.log_encl` and Mathlib's bounds on `log 2`. Not stated: the certified
  `binary_log` algorithm itself (its owner is `BinaryLog`), how the Rust chose a ratio's shift from bit lengths,
  `interval_sum`'s rounding of an enclosure out to the grid, `ProductBound`'s machine words and `times_bound`, the log
  form of the spread, and the KT and CTW bounds.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the sentences of `docs/HNN_FORMULA.md` (the loaded ring's mode quotient), `docs/RECEIVER_HOLARCHY.md` (the retired optical control) and `docs/HOLON.md` (geometry and incidence) to the new modules, and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3747 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10608 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused simp arguments, unused variables, universe notes), none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
