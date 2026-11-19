# The Cantor string's tube beats with its complex dimensions, a continuum clock splits as a complex's does, and a passive word moves by the sum of its steps' changes, in Lean

November 19, 09:44 UTC. The seventeenth formalization pass over #410, its eighteenth set, after [the
seventeenth](2026-11-19_A_DECLARED_DIMENSION_IS_CERTIFIED_BY_ITS_ELIMINANTS_LOCK_AND_KEY_DEPOSITED_ON_BOTH_SIDES_MEET_AT_THE_MATCHED_PAIR_NEAREST_THEIR_OPENING_AND_A_PORT_HAMILTONIAN_AEON_PRODUCES_WHAT_ITS_RESISTANCE_DISSIPATES_IN_LEAN.md)
(#1029). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Foundation/FractalStringTube` | A hole's inner tube has measure `min(2ε, b − a)` and a string's tube volume `V(ε) = Σ_j min(2ε, ℓ_j)` splits as `2ε·N(ε)` plus the short holes' lengths (`volume_hole_tube`, `tubeVolume_split`); the Cantor string, matched to `FractalString`'s holes (`cantorString_depth`, `tubeVolume_cantorString`), has `V(ε) = 2ε(2^m − 1) + (2/3)^m` on each band and `V(ε/3) = (2/3)(V(ε) + ε)` (`cantorTube_band`, `cantorTube_third`); `ε^(1−D) ≤ V(ε) ≤ 2^(2−D)ε^(1−D)`, so `log V/log ε → 1 − D` with `D = log 2/log 3` (`cantorTube_bounds`, `tendsto_log_cantorTube_div_log`); the normalized tube `f = ε^(D−1)V` has `f(ε/3) = f(ε) + ε^D`, its band profile `(1 + c)(2/c)^(1−D)`, the limits `2^(2−D)` and `(3/2)·4^(1−D)` along two scale sequences, and no limit at `0⁺`, with `limsup = 2^(2−D)` and `liminf` the profile at `(1 − D)/D` (`normalizedTube_third`, `normalizedTube_band`, `normalizedTube_not_tendsto`, `limsup_normalizedTube`, `liminf_normalizedTube`) | #410's box "Fractal strings" (part); `Foundation/FractalString`'s paragraph on the Cantor string; the record of September 25 on the music in the holes | `fractal.cantor-tube-content` (new) |
| `Aeon/Production/ContinuumHodgeTime` | On the circle a continuous clock form splits uniquely as its winding rate `h = ∫₀¹ f` plus the derivative of a periodic C¹ state potential, and an aeon reads `h` times its lifted displacement plus the potential's drop (`Circle.split`, `Circle.split_unique`, `Circle.reading_split`); the state part is fixed by the endpoints' phases, a form is boundary-determined exactly when `h = 0`, and a closed aeon of winding `N` reads `h·N`, so the circle carries no production (`Circle.state_boundary_determined`, `Circle.boundaryDetermined_iff`, `Circle.no_production`); on the flat torus `dφ` reads its potential's drop, the constant part reads `h` times the displacement, and Green on a rectangle makes the production part the only one a cell boundary reads, as the flux of its curvature `−Δβ` (`Torus.state_reading`, `Torus.winding_reading`, `Torus.green`, `Torus.cellReading_split`, `Torus.production_cellReading`); at a declared Fourier width each mode `k ≠ 0` splits uniquely along `k` and `k^⊥`, the mode `0` is the winding part, and a form is closed exactly when its production coefficients vanish (`Torus.mode_split`, `Torus.trig_split`, `Torus.trig_split_unique`, `Torus.trig_closed_iff`); `cos(2πy) dx` is coexact, its loops at heights `0` and `½` read `1` and `−1`, and they differ by the curvature flux `2` (`Torus.cosForm_homologous_loops`), and `dx` is not boundary-determined (`Torus.dxForm_winding_not_boundary_determined`) | #410's box "The Hodge split of a continuum clock"; `Aeon/Production/HodgeTime`'s scope line; the record of September 24, §A1 and §A2 | `aeon.continuum-hodge-time` (new); `aeon.a2-hodge-time` takes owners and a new scope |
| `HNN/WordSensitivity` | Two Cayley steps of passive elements at `h` differ by `h(I − (h/2)K₁)⁻¹(K₁ − K₂)(I − (h/2)K₂)⁻¹`, so `‖dCay‖ ≤ h‖dK‖`, with no sign on the difference (`cayley_step_sensitivity`, `cay_sub_cay`, `norm_cay_sub_le`); a word telescopes to `Σ_i (∏_(j≠i) ρ_j) L_i`, so a word of passive steps moves by `Σ_i h_i‖dK_i‖` at every length while an active step's gain enters every other locus's sensitivity (`word_sensitivity`, `passive_word_sensitivity`, `cay_word_sensitivity`); a read across loci moves by `Σ_ℓ K_ℓ‖dx_ℓ‖`, and on loci carried by `LatticeDeposit` the certificate `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)` keeps it within half the receiver's grain (`read_hybrid`, `carried_read_within_certificate`); the receiver then reads the same grain point or its neighbour, the same point with a strict margin from every tie (`reading_within_neighbour`, `reading_same_with_margin`); the counterfactual trajectory has the product bound, and for passive maps stays within `u/2` of the unrounded one at every length, the releases of an entry summing below `u/2` in absolute value (`counterfactual_trajectory`, `abs_releaseAt_sum_lt`, `carried_trajectory_within_half_unit`); `K = ½·I` gives `Cay_1 = (5/3)·I`, whose word attains the active bound (`active_word_witness`) | #410's box "Word sensitivity and the counterfactual trajectory bound"; the record of September 25 on the deposition remainder, its obligations; `HNN/LatticeDeposit`'s and `HNN/LatticeWord`'s open paragraphs | `hnn.word-sensitivity` (new); `hnn.release-since-founding`, `holon.passive-cayley-contraction` and `receipt.commit-chain-residual` take owners |

The boxes these answer, by their opening words: "Fractal strings" (part); "The Hodge split of a continuum clock"; and
"Word sensitivity and the counterfactual trajectory bound".

## 2. What the pass corrected

1. **The two limits differ by a numerical fact, and the correction sum starts at `i = 0`.** The brief reduced
   `(3/2)·4^(1−D) < 2^(2−D)` to `(log 3 − log 2)² > 0`; that reduction was invalid, since the inequality is `2^D > 3/2`,
   that is `D² + D > 1`, which holds because `D ≈ 0.631` exceeds `(√5 − 1)/2 ≈ 0.618`, here from `2^8 > 3^5`
   (`cantorDim_gt_five_eighths`, `cantorDim_sq_add_gt_one`). The brief's correction `Σ_(i<k)(ε 3^(−i−1))^D` was off by
   one: at `k = 1` it must give `f(ε/3) − f(ε) = ε^D`, so the sum is `Σ_(i<k)(ε 3^(−i))^D = 2(1 − 2^(−k))ε^D`
   (`normalizedTube_third_pow`, `correction_eq`). The persistent oscillation of a lattice string is Lapidus–van
   Frankenhuijsen's dichotomy (Ch. 8), not Lapidus–Pomerance's 1993 criterion (`ℓ_j ∼ L j^(−1/D)`), and the module
   attributes each. `FractalString`'s docstring called its identities and counts "exact"; it now calls them identities,
   and its paragraph on the Cantor string points here.
2. **A coexact form reads its loops by height, not zero.** The brief's witness had `cos(2πy) dx` read `0` on the
   horizontal closed aeons at `y = 0` and `½`; the loop at height `y` reads `cos(2πy)`, which is `1` and `−1` there (it
   reads `0` at `¼` and `¾` and on vertical loops). The witness carries what the discrete law states: the harmonic
   prediction `h·N = 0` fails on both loops, and the two homologous loops differ by the curvature flux through the strip
   between them. The atlas row `aeon.a2-hodge-time` gave the continuum case as owed in #62, which closed into #410; its
   scope now names the continuum owner, and `HodgeTime`'s scope line, which left the continuum clock forms outside it,
   points here.
3. **The record's `‖dCay‖ ≤ ‖dK‖` is the bound at `h = 1`, and it needs both elements passive.** At a step `h` the bound
   is `h‖dK‖`; with one element passive the change is bounded by `(h/2)‖(K₁ − K₂)(y₂ + p)‖`, which reads the other
   step's output (`cayley_step_sensitivity_at`). The brief's margin "at distance at least `|r − r′|` from every tie"
   fails because `round` reads a tie upward (`r = 3/10`, `r′ = 1/2`, `u = 1`): the margin is strict
   (`margin_strict_witness`). A Lipschitz propagation consumes the releases' absolute sum, where
   `release_bounded_since_founding` and the atlas row `hnn.release-since-founding` bound the signed sum; the absolute
   form holds by the same per-deposit bound and the Kraft tail (`abs_releaseAt_sum_lt`), and the row now states it.
   `LatticeDeposit`'s and `LatticeWord`'s open paragraphs on the counterfactual bound now point here.

## 3. What each statement stands on, and what is left

- `Foundation/FractalStringTube` stands on `Foundation/FractalString` and `FractalPacking` (the holes and their words)
  and Mathlib's Lebesgue measure, logarithms and weighted means. Not stated, so the box stays part done:
  Lapidus–Pomerance's spectral asymptotic and its Tauberian machinery, their criterion for measurability, the nonlattice
  case, Lapidus–Maier's inverse problem and its failure at `½`, Herichi–Lapidus's weighted shift, Makarov's theorem, and
  the placement of the holes as disjoint intervals exhausting the Cantor complement (so `V` is the measure of a set).
- `Aeon/Production/ContinuumHodgeTime` stands on Mathlib's interval integrals, periodic integrals and divergence theorem
  on a box; it cites `HodgeTime` without importing it. Not stated: the smooth Hodge theorem for every C¹ form on the
  torus (the convergence of its Fourier series) or on a compact Riemannian manifold, Green beyond rectangles, the
  converse that a C¹ form all of whose cell boundaries read `0` is closed (stated at declared width as
  `trig_closed_iff`), and the agent-inferred reading of relative completeness.
- `HNN/WordSensitivity` stands on `Holon/Cayley` (`resolvent_bound`, `cayley_contraction`, `cayley_bijective`),
  `Transport/AccumulatedReceiverDefect.distance_le_budget` and `HNN/LatticeDeposit` (`within_one_unit_since_founding`,
  `release_bounded`, `gamma_window_lt_one`). Not stated: the engine's own sensitivities `K_ℓ` (deposition, transient and
  inverse charts, ports, junctions) as numbers, a bound for a nonlinear chart beyond its Lipschitz constant, that the
  engine's deposit map is `1`-Lipschitz at the carried operands, and a passivation of an active port, which enters only
  through its gain.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated or owed (`Foundation/FractalString`'s paragraph on the Cantor string, whose "exact" wording it also retired; `Aeon/Production/HodgeTime`'s scope line on the continuum clock forms; `HNN/LatticeDeposit`'s and `HNN/LatticeWord`'s open paragraphs on the counterfactual bound; the four `Holonics` modules and their importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3902 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10620 jobs)`, exit 0; `Holonics`, with `Foundation/FractalString`, `Aeon/Production/HodgeTime`, `HNN/LatticeDeposit` and `HNN/LatticeWord` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
