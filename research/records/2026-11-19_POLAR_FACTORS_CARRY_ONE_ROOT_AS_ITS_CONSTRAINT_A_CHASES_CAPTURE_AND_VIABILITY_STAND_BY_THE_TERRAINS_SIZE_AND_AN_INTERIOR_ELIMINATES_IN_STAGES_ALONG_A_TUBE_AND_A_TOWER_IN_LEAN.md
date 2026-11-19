# Polar factors carry one root as its constraint, a chase's capture and viability stand by the terrain's size, and an interior eliminates in stages along a tube and a tower, in Lean

November 19, 06:03 UTC. The tenth formalization pass over #410, its eleventh set, after [the
tenth](2026-11-19_THE_PONTRYAGIN_BOUND_PLACES_A_SKEW_GENERATORS_MODES_A_REVERSED_CARRIER_PASSES_THE_TRACE_FACES_A_REVOLUTE_JOINT_MOVES_AT_ITS_CAYLEY_RATE_LEFT_TO_RIGHT_IS_THE_OPPOSITE_GROUP_AND_THE_CARRY_TOWER_IS_THE_B_ADIC_TOWER_IN_LEAN.md)
(#1020). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #27, #148.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Holon/DtNTubeTower` | Eliminating an interior in two stages gives the boundary relation and the harmonic extension of eliminating it at once, the joint block's determinant the product of the stages' (`staged_elimination`, `staged_harmonicExtension`, `det_joint`), and the stations eliminate in either order (`stations_eliminate_in_any_order`); two segments glued at a station eliminate to the Schur complement of their summed blocks, two-ports to `ab/(a + b)`, and a path of `n + 1` edges with conductances `g_k > 0` to `(Σ 1/g_k)⁻¹`, resistances adding, by induction through the staged law (`glue_dtn`, `series_conductance`, `path_eliminates_in_series`), `Membrane`'s `2/3` its case (`path_witness`); with no direct block between a tube's ends, the end-to-end block of `Λ_DN` is `−B_L A⁻¹ B_R`, of rank at most the interior's and either coupling's (`neck_block`, `neck_rank`); for `L ⪰ 0` the boundary relation is the least energy over the interior's continuations and positive semidefinite, positive definite for `L ≻ 0` (`dirichlet_principle`, `dtn_posSemidef`, `dtn_posDef`), and raising `L` never lowers it (`rayleigh_monotone`); the positive definite faces on `Fin n` with restriction by eliminating the top sites form a `ContinuingTower.Tower` whose every restriction is `kron_exact`'s, with plural gluing (`eliminationTower`, `eliminationTower_restrict_is_kron`, `eliminationTower_gluing`). | #410's box "The `Λ_DN` join"; `Objects/Membrane`, `Holon/Restriction`, `Foundation/ContinuingTower`; the record of August 9 on the interior as an integral over its boundary | `tube.staged-elimination` (new), `tube.dirichlet-rayleigh` (new), `tower.elimination-tower` (new), `tube.dn-elimination`, `tube.series-path-dtn`, `tube.kron-exact` |
| `Geometry/ChaseConsumer` | The move pair on `ℤ[i]`: `v̄·Δv` pairs the power and the signed turn, `|v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²`, and for `v ≠ 0` the traction disk `|Δv|² = |k − 1|²|v|²` with the turn, boost, fall and stop tests on `k = v′/v` (`pairing_faces`, `quadrance_after_sub_before`, `traction_disk_lattice`, `turn_test`, `boost_test`); on a finite terrain the capture basins `C_(n+1) = C_n ∪ Pre C_n` rise and the viability kernels `K_(n+1) = K_n ∩ Pre K_n` fall, both standing from `n = |Z|`, the first the least set holding the target closed under `Pre`, the second the greatest set inside `K₀` viable under it (`captureBasin_stands`, `captureBasin_isLeast`, `viabilityKernel_isGreatest`), and the least capture time obeys `τ = 1 + min_u max_w τ(T z u w)` off the target, finite exactly when it is at most `|Z|` (`leastCapture_step`, `leastCapture_lt_top_iff`); a basin's complement is the kernel under the dual quantifiers (`compl_captureBasin`); zero relative velocity outside the capture disk persists and the bearing turns at `det(r, ṙ)/|r|²` (`capture_is_not_lock`, `bearing_rate`); Adler's `φ̇ = δ − K sin φ` rests iff `|δ| ≤ K`, with one stable and one unstable rest point a turn inside the band and a solution slipping at least `(|δ| − K)` a unit of time outside it (`adler_rest_iff`, `adler_two_rest_points`, `adler_slip`), and robust inward control at an interval's ends reads `Pre`'s quantifiers (`phase_inward`); the expected-capture triple `(U, S, W)` is a commutative monoid whose shift distributes over `⊕` on the readings the recursion produces, a fibre's reading the `⊕` of its members' and the least `⊕` of independent choices the `⊕` of the leasts (`shift_plus`, `reading_union`, `reading_fits`, `isLeast_plus`); and under an embedding of the coarse grain's moves into the fine one's, read alike by the runner, the fine least capture is at most the coarse one, with the grain `g ↦ kg` keeping every bound (`finer_grain_least_capture`, `grain_bound_scale`). | #410's box "The chase consumer"; the records of September 27 (§6, §13, §14.4) and September 28; `holarchy::terrain::pursuit` at `d5ed4adc1` | `pursuit.capture-viability-recursions` and `pursuit.constant-bearing-lock` and `lock.phase-viability` (now formal-checked), `motion.move-pair`, `motion.traction-disk`, `pursuit.capture-is-not-lock`, `pursuit.capture-basin-fibre`, `pursuit.viable-tube`, `pursuit.expected-capture`, `pursuit.move-set` |
| `Geometry/PolarConstraint` | On two coordinates `X² = (tr X)X − (det X)1`, so with `s² = det M` and `t² = tr M + 2s` the matrix `P = (M + s·1)/t` squares to `M` with determinant `s` and trace `t` over any field (`constraintRoot_mul_self`, `constraintRoot_det`, `constraintRoot_trace`); over an ordered field it is the only positive definite root, and `M` has one exactly when the field holds the two positive constraint roots (`constraintRoot_unique`, `exists_root_iff`); for an invertible move `A`, `s = |det A|` is already in the field and `t² = tr AᵀA + 2|det A|` is the one new root: `P = (AᵀA + |det A|·1)/t` and `U = AP⁻¹` give `A = UP`, `UᵀU = 1`, `det U = sign det A`, the pair is unique, and the factors exist over a field exactly when it holds `t` (`polarTurn_mul_polarBoost`, `polarTurn_orthogonal`, `polar_unique`, `exists_polar_iff`), with the left form on the same `t` (`polar_left_unique`); in Motion's charts `U` is a turn, after the reflection `diag(1, −1)` when `det A < 0` (`polarTurn_eq_turnChart`, `polarTurn_eq_turnChart_reflect`); the shear has `t² = 5`, so its polar factors live over `ℚ(√5)` and not over ℚ while its Iwasawa factors stay rational (`shear_polar`, `shear_no_rational_polar`, `shear_iwasawa`, `sl2_polar_and_iwasawa`); `Real.sqrt` gives the unique real pair (`real_existsUnique_polar`), and over ℂ the boost `(AᴴA + s·1)/t` with the real root `s` of `|det A|²` is positive definite and `AP⁻¹` unitary (`complex_polar`). | #410's box "Polar factors over exact square-root extensions"; `Geometry/Motion`'s closing paragraph; the motion record of September 28, §9 | `motion.polar-constraint` (new) |

The boxes these answer, by their opening words: "The `Λ_DN` join"; "The chase consumer"; "Polar factors over exact
square-root extensions" (the box's word; the module carries the roots as their constraints).

## 2. What the pass corrected

1. **Membrane's open paragraph named another join, Dirichlet needs less, and a lossless restriction was called exact.**
   `Objects/Membrane`'s `[open]` names `Λ_DN` with a region's own clock, a different join from the box's tube and tower;
   it now points here for the latter and keeps the former open. Dirichlet's principle needs only an invertible interior
   block under `L ⪰ 0`; positive definiteness of that block enters only Rayleigh's monotonicity, to carry invertibility
   to `L′`. `Holon/Restriction` called Kron elimination "an exact restriction" in the sense of lossless; it now reads "a
   restriction that preserves power", the name `kron_exact` and the atlas id kept.
2. **The chase's laws lived in `pursuit`, a basin's complement is the dual kernel, and "finer" means a multiple.** The
   box named `holarchy::terrain::chase`, but the recursions, the triple, the move set and the least capture were
   `holarchy::terrain::pursuit`'s (the terrain and the traction law were `chase`'s, the move pair
   `geometry::motion::Move`'s). The record's §14.4 and atlas `pursuit.capture-viability-recursions` write one `Pre` for
   both recursions while the mover differs: the chaser moves in the basin and the runner in the tube, and the complement
   of the chaser's basin is the kernel under `∀u ∃w`, not the runner's `∃u ∀w` kernel; the row now says so. "A finer
   grain never raises the least capture" (the box, `pursuit.move-set`) holds for a grain `kg` with an integer `k ≥ 1`
   (`½ℤ` does not lie in `⅓ℤ`) and only when the runner reads an embedded chaser alike at every grain; the row and the
   module carry both. `pursuit.expected-capture`'s shift distributes over `⊕` only on readings with `U ≤ |Θ|` and `W =
   0` when `U = |Θ|`, which every reading the recursion produces meets. The box's "exact expected-capture recursion"
   means an equality, not a bound.
3. **A real move's polar factors need one new root, not several, and "exact" was the box's word.** The box, the motion
   record's §9 and Motion's closing sentence said "exact square-root extensions" and "an exact field with square roots";
   for a real 2×2 move `s = |det A|` lies in the field already and only `t² = tr AᵀA + 2|det A|` is new (two roots are
   needed for the root of a general positive definite form, and over ℂ, where `s` is the real root of `|det A|²`).
   Motion's sentence now points to the module without the word. A pure boost `diag(a, 1/a)` has `U = 1` only for `a >
   0`; for `a < 0` the turn is the half-turn `−1`. The constraint identity `P² = M` holds for every 2×2 `M` over any
   field, and a symmetric `M` with positive constraint roots is already positive definite. `LorentzOnto`'s
   `lorentz_polar` and `exists_herm_sqrt` carry `[proved-standard]` without `formal-checked`.

## 3. What each statement stands on, and what is left

- **The `Λ_DN` join**: an arbitrary order of `n` stations as one theorem (it follows by adjacent swaps), a
  `ContinuingTube` carrying the elimination tower along a longitudinal transport, connection-valued incidence, a
  continuum Dirichlet-to-Neumann operator and `Λ_DN` as the boundary receiver of a time-extended interior are not
  stated.
- **The chase**: the expected-capture value over adaptive strategies on a belief state, `E.U = 0` exactly when the basin
  certifies the fibre (with `b ≤ W`), the time-expanded viable tube, the capture reach, the continuous
  Hamilton–Jacobi–Isaacs reading, and a solution of Adler's equation joined to the tongue's scaling are not stated.
- **The polar factors**: the decomposition on `n ≥ 3` coordinates (it needs the eigenvalues), the uniqueness of the
  complex factors and the complex left form, the singular case `det A = 0`, the factors read against a receiver metric
  other than the unit one, and the join of the finite factors to Motion's infinitesimal split of a rate are not stated.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owed sentences (`Geometry/Motion`, `Objects/Membrane`, the elementary objects' §7), replaced "an exact restriction" in `Holon/Restriction` by the power-preserving restriction it names, and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules and the three `Holonics` modules whose docstrings changed (`Geometry/Motion`, `Objects/Membrane`, `Holon/Restriction`) read `Build completed successfully (3539 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10599 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused simp arguments, unused section variables, universe notes); the three in `Geometry/Motion` (unused simp arguments at its lines 649 and 1018) predate this change, which touches only its module docstring. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
