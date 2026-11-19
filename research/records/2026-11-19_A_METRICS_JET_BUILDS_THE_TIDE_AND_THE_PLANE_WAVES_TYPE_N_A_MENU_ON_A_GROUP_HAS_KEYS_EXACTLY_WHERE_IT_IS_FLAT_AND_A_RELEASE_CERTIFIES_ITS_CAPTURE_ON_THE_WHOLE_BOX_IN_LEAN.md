# A metric's jet builds the tide and the plane wave's type N, a menu on a group has keys exactly where it is flat, and a release certifies its capture on the whole box, in Lean

November 19, 10:54 UTC. The nineteenth formalization pass over #410, its twentieth set, after [the
nineteenth](2026-11-19_PETROVS_TYPES_PLACE_THE_EIGENVALUES_OF_THE_TIDE_JOINED_TO_THE_FRAME_DRAGGING_A_FOREST_RETAINS_NOTHING_A_PARALLEL_BUNDLE_FORGETS_ONLY_ITS_UNIFORM_TOTAL_AND_THE_MOMENT_STAYS_LOSSY_ACROSS_RE_KEYS_IN_LEAN.md)
(#1031). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/CurvatureJets` | A metric's 2-jet at a point builds its Christoffel symbols, whose rate along a coordinate line is their first jet through the inverse's rate `−g⁻¹(∂g)g⁻¹`, and its Riemann tensor, which is the commutator `∂_cA_d − ∂_dA_c + [A_c, A_d]` of the connection's transports (`hasDerivAt_inv_metric`, `hasDerivAt_christoffel`, `riemann_eq_commutator`); the curvature is linear in the second jet and quadratic in the first, so where the first jet vanishes it is the second jet's linear form `K`, which has every algebraic curvature symmetry (`riemannLower_eq_add`, `riemannLower_scale`, `riemannLower_of_firstJet_zero`, `linearCurvature_symmetries`); at `η` a Ricci-flat jet's curvature is a Weyl tensor whose electric part is the tide, a boost with no turn (`vacuum_weyl`, `vacuum_tide`, `tide_is_boost`); the weak static field `h_ab = −2Φδ_ab` has the tide `Φ_ij`, no magnetic part and `R_ab = ∇²Φ δ_ab`, so `R₀₀ = ∇²Φ`, the trace-reversed dust equation is Poisson's `∇²Φ = 4πGρ`, and the density focuses (`weakField_tide`, `weakField_ricci`, `weakField_poisson`, `weakField_focusing`); the plane wave `H = x² − y²`, its jets read by Mathlib's derivatives, is Ricci-flat with nonzero curvature at its origin, the first nonzero instance of `WeylSymmetries`, of type N (`wave_curvature_built`, `wave_weyl`, `wave_classify`), and the point mass's weak field at `(r, 0, 0)` is Weyl with tide `(M/r³)·diag(−2, 1, 1)`, of type D (`pointMass_weyl`, `pointMass_classify`) | #410's boxes "Einstein: the continuum realization …, the weak-field limit" (part) and "Curvature's strain and rotation" (part); `Physics/Spacetime/Einstein`'s `[open]` paragraph; `Physics/Spacetime/StressEnergy`'s weak-field sentence; `Raychaudhuri`'s and `PetrovTypes`' "What is not claimed" | `coupling.curvature-jets` (new); `coupling.weyl-electric-magnetic`, `coupling.petrov-types` (scope), `gr.trace-reversal-newtonian`, `gr.curvature-commutator` (owners and scope) |
| `HNN/GroupKeys` | On a menu whose contacts carry elements of a group, a key (`x(tgt e) = g_e x(src e)`) is carried along every walk by its holonomy, so every closed walk of a menu a key produced closes (`key_transports`, `key_closes`, `produced_closes`); on a connected menu keys exist iff every closed walk at the base has trivial holonomy, and they are then one orbit of the right gauge, free and transitive, with exactly one key fixed at the base (`exists_key_iff`, `keys_torsor`, `keys_eq_orbit`, `gauge_fix_unique`); a change of base or of frame conjugates the holonomy (`hol_rebase`, `hol_regauge`); a tree carries keys for every assignment, and only the chords off a spanning tree decide (`tree_has_keys`, `tree_reading_decides`); for phases on `ℝ/ℤ` the holonomy is the signed offset sum, keys exist iff every cycle sum is an integer, and the cost `Σ_e (1 − cos 2π(θ_tgt − θ_src − ψ_e))` vanishes exactly at keys, blind to windings and a global phase (`phase_keys_iff`, `phase_key_global_phase`, `phaseCost_eq_zero_iff`); the triangle with offsets `⅓` closes and with offsets `¼` has no key and a positive cost at every lift (`third_has_key`, `quarter_no_key`, `quarter_cost_pos`); for rotations of `ℝ³` a double contact carrying `1` and a quarter-turn has no key, and two quarter-turns that do not commute move the triangle's holonomy under a change of frame (`rotation_double_no_key`, `quarterTurns_noncommute`, `rotation_regauge_moves_hol`); for an additive group `Geometry/Frustration`'s frustration vanishes exactly when a key exists (`frustration_eq_zero_iff`) | #410's box "Continuous keys" (part); `HNN/Keys`' closing paragraph; `HNN/ContactFixedPoint` | `key.group-holonomy-keys` (new); `key.continuous-fibre` (scope), `key.connection-cheeger` (owners) |
| `Mathematics/CertifiedCapture` | On a convex region where `f` is complex differentiable with `‖f′‖ ≤ M` the image moves by at most `M` times the source's displacement, and on the owner's square `B∞(c, r)` with `|Re f′| + |Im f′| ≤ q` and an anchor within `β` of `f(c)` in each part, `β + q r ≤ r′` puts the whole image in `B∞(c′, r′)`, so the capture square holds every later release (`norm_sub_le_of_deriv_le`, `box_mean_value`, `image_box_subset_box`, `box_capture_square`, `box_capture_square_iterate`); an enclosure inside one cell of the grain's reading certifies every member's reading, and a box is captured or holds two points read apart (`capture_certifies`, `no_enclosure_certifies`, `box_capture_or_obstruction`); a release law run over a finite horizon returns a capture, an obstruction or an exhaustion with its depth and the face it retains, which holds `g^[d]` of the whole source face, and with a sound test a capture puts `g^[d] z` in its target for every point of the source box (`release_face`, `release_capture_sound`, `release_capture_stays`, `boxLaw_capture_sound`); outward rounding to `2^(−k)` keeps every value of an enclosure, widens it by less than two grains and leaves a grain point fixed (`roundOut_mem`, `roundOut_width`, `round_grain`, `cbox_subset_roundOut`); for real `s > 0` the alternating partial sums converge to `η(s)`, bracket it and lie within `(N + 1)^(−s)` of it (`tendsto_etaPartial`, `eta_mem_enclosure`, `abs_eta_sub_le`); for real `s > 1` and `N ≥ 1`, `0 ≤ Σ_(n≥N) n^(−s) − N^(1−s)/(s − 1) − N^(−s)/2 ≤ s N^(−s−1)/8`, which encloses Mathlib's `riemannZeta s` (`zetaTail_euler_maclaurin`, `zeta_mem_enclosure`); `η(s) = (1 − 2^(1−s)) ζ(s)` (`eta_eq_mul_zeta`); four terms hold `π²/6` within `1/256`, and `η(1) = log 2` (`zeta_two_enclosure`, `eta_one`, `log_two_mem_eta_enclosure`) | #410's box "`series.log-atanh`, …, `analytic.certified-capture`, `analytic.euler-maclaurin-eta`" (part); `Mathematics/ConstantNavigators`' "What is not claimed"; the retired `geometry/exact_analysis` owners ([history](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics/src/geometry/exact_analysis)) and the guide `docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md` | `analytic.certified-capture`, `analytic.euler-maclaurin-eta` (expression, owners, scope, grade); `series.log-atanh`, `series.log-atanh-exp` (owners, scope) |

The boxes these answer, by their opening words, each part done: "Einstein: the continuum realization" and "Curvature's
strain and rotation"; "Continuous keys"; and "`series.log-atanh`, `series.log-atanh-exp`, …,
`analytic.euler-maclaurin-eta`".

## 2. What the pass corrected

1. The isotropic weak field gives the brief's claim whole: the linearized Ricci tensor is `R_ab = ∇²Φ δ_ab` (`R₀₀ =
   ∇²Φ`, `R_0j = 0`, `R_jk = ∇²Φ δ_jk`) and needs no symmetry of `Φ`'s Hessian. The point mass's first jet `∂Φ` does not
   vanish at `(r, 0, 0)`, so its statements, like the weak field's, are about the linearized curvature `K(∂∂h)`, and
   `riemannLower_scale` states what "linearized" means: the term of first order in the perturbation's scale, the rest
   carrying its square. `PetrovTypes`' "`μ` … up to the sign convention" is settled under Misner–Thorne–Wheeler's
   convention, `μ = +M/r³`. The plane wave here travels along `z`, so its `E = diag(−1, 1, 0)` and `H` differ from
   `PetrovTypes`' plane wave along `x`; both are of type N. `StressEnergy` is a `Holonics` module, and the owner's
   focusing lemma over ℚ was replaced by the definition of the rate and `raychaudhuriRate_le` over ℝ.
2. The menu is `Geometry/Frustration`'s indexed family of contacts rather than a list (a list of `n` contacts is the
   family on `Fin n`, several contacts may join one pair of ports), which also gives the join to its frustration; a walk
   is a predicate on lists of signed steps rather than a dependent type. The brief named both triangles "frustrated":
   only the one with offsets `¼` is, since the cycle sum `1` of the offsets `⅓` is an integer. Since keys are carried by
   left multiplication, a change of frame `h` sends a based holonomy to `h(v₀) hol h(v₀)⁻¹`, the brief's `k⁻¹ hol k` at
   `k = h(v₀)⁻¹`. Real rotation matrices do not evaluate under `decide`; their membership in the rotation group and the
   quarter-turn's nontriviality are read from their entries.
3. The row's "capture square" is the guide's square `B∞(m, r)` that the release maps into itself (`β + q r ≤ r`), and a
   capture at a declared grain is a cell of the reading; the module states both, the square as a target that `g` maps
   into itself and the cell as the test's target, and a capture certifies the reading, not that each member first
   arrives at that depth. The owner's code is at `13f8c734` (removed at `d329cb541`), not in the tree. The row's
   `uses:navigator.zeta` named the dynamical zeta of a map; Riemann's ζ with its first-order remainder joins
   `rh.actual-fractional-zeta-source`'s integral form, and the relation is repointed. For `0 < s ≤ 1` η's series is not
   summable in Lean's unconditional sense, so η is the limit of its partial sums (the `tsum` for `s > 1`). The trapezoid
   bound takes no integral: it compares derivatives about the midpoint against a named primitive.

## 3. What each statement stands on, and what is left

- `Physics/Spacetime/CurvatureJets` reads curvature at one point. The full Riemann tensor where the first jet does not
  vanish is defined and split but its symmetries, Ricci tensor and tide are not read there, and the quadratic part's
  size as a perturbation shrinks is not stated; the second jet's symmetry is a hypothesis, the point mass's Hessian is
  given as numbers, and no metric field, change of coordinates or construction of normal coordinates is stated. The
  deviation equation along a geodesic, the Bianchi identity (the 3-jet), a fluid-plus-thermal constitution solving `G +
  Λg = κT` and the Regge construction stay with their boxes, and no metric of type I, II or III is built. Both boxes
  stay part done.
- `HNN/GroupKeys` locates keys on configuration spaces that are groups, for every finite menu. Noisy keys (a menu no key
  fits, and the cost's minimizers), a deposition law that locates a phase or rotation key (a descent of the cosine cost
  and its convergence), curved strands with the helical pair's nonlinear reading, and keys on homogeneous spaces that
  are not groups (a direction on the sphere, moved by a rotation with a stabilizer) are not stated; the chords' count
  `|E| − |V| + 1` and a cycle basis are not formalized, and the connection Cheeger bound is cited, not restated. The box
  stays part done.
- `Mathematics/CertifiedCapture` states the release on the points a face encloses, the outward rounding, and ζ and η at
  real `s` with their first-order remainder. The jets in `s` (the owner's `ComplexJet2` and `HeadJet`) and their uniform
  derivative bounds, complex `s` with the owner's rising-product remainder, the higher Euler–Maclaurin terms with their
  Bernoulli numbers and the start `N` derived from a declared grain, the guide's contraction to a unique fixed point,
  and interval arithmetic through sums, products and reciprocals are not stated; the source's rational evaluation over a
  box, which supplies `M`, `q` and `β`, is the caller's. Read against `ConstantNavigators.log_two_enclosure`, the
  alternating navigator's stated remainder reaches the width of four atanh terms only from `N = 78731` terms on. The box
  stays part done.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated or owed (`HNN/Keys`' closing paragraph on continuous keys; `Physics/Spacetime/Einstein`'s `[open]` paragraph and `Physics/Spacetime/StressEnergy`'s weak-field sentence; `Physics/Spacetime/Raychaudhuri`'s and `Physics/Spacetime/PetrovTypes`' "What is not claimed" on the curvature built from a metric; `Mathematics/ConstantNavigators`' "What is not claimed" on the capture, ζ, η and the rounding; the `Holonics` modules and their importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3916 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10626 jobs)`, exit 0; `Holonics`, with `HNN/Keys`, `Physics/Spacetime/StressEnergy` and `Physics/Spacetime/Einstein` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
