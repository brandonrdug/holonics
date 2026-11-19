# A metric's tide is a self-adjoint boost on its screen, a curved slice adds k/A² to Friedmann's equations, and every cycle retains its whole constitution, in Lean

November 19, 15:37 UTC. The twenty-sixth formalization pass over #410, its twenty-seventh set, after [the
twenty-sixth](2026-11-19_THE_RESTORING_LEGS_ZERO_PRODUCTION_IS_THE_LIMIT_OF_FINITE_LEGS_ZETAS_JETS_BOUND_A_CAPTURE_SQUARE_AND_THE_EGGS_PERIOD_IS_ITS_OVALS_INTEGRAL_IN_LEAN.md)
(#1038). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/TidalScreen` | a symmetric first jet gives `Γ^a_bc = Γ^a_cb` and `∂_c g_ab = Γ_acb + Γ_bca`, and at a zero second jet compatibility cancels half of the connection's rate against its square: `R(g, dg, 0)_abcd = g_ef(Γ^e_bc Γ^f_ad − Γ^e_bd Γ^f_ac)`, a difference of a pairing symmetric in each pair and under their exchange, so with the owner's split `R = K(ddg) + R(g, dg, 0)` the curvature of any metric's 2-jet has both antisymmetries, the pair exchange and the cyclic identity (`christoffelLower`, `riemannLower_zero_eq_quadratic`, `connectionPair_exchange`, `riemannLower_zero_symmetries`, `riemannLower_symmetries`); the tidal form `T(ξ, η) = R_abcd ξ^a u^b η^c u^d` is then symmetric and kills `u` on both sides, and the owner's `R(·, u)u = g⁻¹T` is `g`-self-adjoint, maps into the screen `u^⊥` (Mathlib's orthogonal complement under `g`) and is a boost at `g` with turn `0` (`tidalForm_symm`, `tidal_riemann`, `tidalMap_selfAdjoint`, `tidalMap_mem_screen`, `metric_tidal`, `metric_tidal_is_boost`), with `ℝu ⊕ u^⊥` wherever `uᵀgu ≠ 0` (`isCompl_screen`, `timelike_split`); in a frame adapted at `u` (`EᵀgE = diag(σ, 1, …, 1)`) the owner's frame tide is `EᵀTE`, symmetric with zero first row and column (`AdaptedFrame.inv_eq`, `frameTidal_eq`, `metric_frameTidal`), so `J″ = −𝓡J` reduces to the screen, where Raychaudhuri's equation holds at `−θ²/k`, `rotation_law`'s symmetry premise is met and the shear's tidal term is the trace-free screen tide (`screen_deviation`, `screen_raychaudhuri`, `screen_shear_law`), joined to the owner's families of geodesics whose connection is a metric's at the base point (`families_tide`, `families_rotation_law`, `families_screen_raychaudhuri`); witnesses: Minkowski's screen tide is the owner's `tide` and its electric part for any symmetric jets, the flat FLRW jet's is `−(C/A)·1`, and the round sphere's `R_φθφθ = sin²θ` with frame tide `diag(0, 1)` and screen tide `1` (`minkowski_tide`, `frw_screen`, `sphere_riemannLower`, `sphere_screen`) | #410's box "Curvature's strain and rotation" (ticked); `Raychaudhuri`'s and `GeodesicDeviation`'s "What is not claimed", `CurvatureJets`' and `FriedmannFluid`'s sentences on the curvature's symmetries | `coupling.metric-curvature-symmetries`, `coupling.tidal-screen` (new); `coupling.geodesic-deviation`, `coupling.raychaudhuri-riccati`, `coupling.curvature-jets` (scope) |
| `Objects/RetentionCycles` | on every incidence `cΘ` and `Θ` carry one flux under every solvable source and every drop on `cΘ` is the drop on `Θ` over `c`, so a square-law stroke deposits `j²` on both and is in proportion to `Θ` iff every edge dissipates one power, and a Joule stroke deposits `Γ/c` against `Γ`, proportional to `Θ` iff its drops share one magnitude (`strokeFlux_scale`, `strokeDrop_scale`, `squareProportional_iff_equal_power`, `joule_deposit_proportional_iff`); the abstract lemma: where the present reads the projective class and every constitution admits a stroke out of proportion, the square law's classes are the constitutions, and the same for the Joule law with drops not of one magnitude, with the constitution the least lawful retention (`square_futureAgreement_iff_of_reads`, `square_futureAgreement_iff_of_two_strokes`, `joule_futureAgreement_iff_of_reads`, `constitution_factors_through_every_standing_of_iff`); two tests on the incidence alone, the cycle test (agreement on every source makes the weighted drops `(Θ/Θ′)dψ` orthogonal to every cycle) and a potential that slips one edge and not another (`cycle_test`, `readsProjectiveClass_of_weights`, `stroke_of_separatesEdges`), which the bundle fails (`bundle_not_separatesEdges`, `bundle_equalDrops`); the cycle of `N` nodes: a source admits a balance iff its charge is zero, the unit source across `k` sends `R_far/R` through `k` and `r_k/R` round the far path, the present reads exactly the projective class, the stroke across `k` is in proportion iff `Θ_f = (N − 1)²Θ_k` off `k`, so for `N ≥ 3` no constitution takes two in proportion and no unit stroke has one drop magnitude, and under both laws the classes are the constitutions (`cycle_solvable_iff`, `cycle_unit_flux`, `cycle_readsProjectiveClass`, `cycle_unit_squareProportional_iff`, `cycle_not_two_strokes_proportional`, `cycle_unit_not_equalDrops`, `cycle_square_futureAgreement_iff`, `cycle_joule_futureAgreement_iff`); the triangle recovered from the lemma and under the Joule law (`triangle_square_futureAgreement_iff_of_reads`, `triangle_joule_futureAgreement_iff`); the diamond, two triangles on one shared edge, under both laws through the two tests (`diamond_readsProjectiveClass`, `diamond_separatesEdges`, `diamond_square_futureAgreement_iff`, `diamond_joule_futureAgreement_iff`); on the 4-cycle `(1, 1, 1, 1)` and `(2, 2, 2, 2)` agree now and are separated by one unit stroke under each law, where the 4-edge bundle merges them (`cycle4_witness`) | #410's box "The explicit classes of the square law's minimal retention on a general weighted graph" (part done); `Objects/Retention`'s `[open]` paragraph, `RetentionClasses`' and `RetentionSeries`' "What is not claimed" | `deposition.dilation-stroke-proportion`, `deposition.classes-two-tests`, `deposition.cycle-retains-constitution`, `deposition.triangle-joule-retains-constitution`, `deposition.diamond-retains-constitution`, `deposition.cycle4-uniform-witness` (new); `deposition.triangle-retains-constitution`, `deposition.minimal-retention-general` (scope) |
| `Physics/Spacetime/CurvedFriedmann` | the field `g = diag(−1, a²ψ⁻², a²ψ⁻², a²ψ⁻²)` with `ψ = 1 + k(x₁² + x₂² + x₃²)/4`, its rates read by Mathlib's derivatives along every coordinate line where `ψ ≠ 0`, and at the centre the owner's value and first jet with the new second-jet entries `∂_j∂_l g_ii = −kA²δ_jl`, its Christoffel symbols the flat ones and their rate the owner's `christoffelJet` of that jet (`hasDerivAt_curvedField`, `curvedSecondJet_eq_smul`, `curved_christoffel`, `curved_christoffel_rate`); an added symmetric second jet enters the curvature through the owner's linear form alone (`riemannLower_add`), so `R₀₀ = −3C/A`, `R_ij = (AC + 2B² + 2k)δ_ij`, the scalar `6(C/A + H² + k/A²)`, `G₀₀ = 3(H² + k/A²)`, `G_ij = −(2AC + B² + k)δ_ij` and the tide `−ACδ_ij` unchanged (`curved_ricci`, `curved_scalar`, `curved_einstein`, `curved_tide`), and the full tensor `R_abcd = κ_ab(g_ac g_bd − g_ad g_bc)` with `C/A` on time planes and `(B² + k)/A²` on slice planes, the flat jet's included (`frw_riemann`, `curved_riemann`); the slice from its own 3-jet has curvature `(k/A²)(h_ac h_bd − h_ad h_bc)` and sectional curvature `k/A²`, and Gauss's equation with `K_ij = ABδ_ij` joins it to spacetime (`slice_riemann`, `slice_sectional`, `curved_gauss`); the comoving fluid solves the field equation iff `3(H² + k/A²) = κρ + Λ` and `2C/A + H² + k/A² = Λ − κp`, the acceleration equation is unchanged, `ρ′ = −3H(ρ + p)` follows where the equation holds near `t`, and at `Λ = 0` `Ω − 1 = k/(A²H²)` takes `k`'s sign (`curved_friedmann_iff`, `curved_accel`, `curved_continuity`, `curved_barotropic`, `density_excess`, `density_sign`); built solutions: Einstein's static universe, Milne's (flat at the centre) and de Sitter's closed slicing, every plane of the last curving by `Λ/3` as the owner's flat slicing does (`einsteinStatic_field`, `milne_field`, `milne_flat`, `deSitterClosed_field`, `deSitterClosed_riemann`, `deSitterFlat_riemann`) | #410's box "Einstein: the continuum realization" (part done); `FriedmannFluid`'s "What is not claimed" and its sentence on the full Riemann tensor, `CurvatureJets`' "What is not claimed" | `gr.flrw-curved-jet`, `gr.slice-sectional-gauss`, `gr.friedmann-curvature`, `gr.curved-friedmann-solutions` (new); `gr.flrw-fluid-bath` (scope) |

The boxes these answer, by their opening words: "Curvature's strain and rotation" (ticked); "The explicit classes of the
square law's minimal retention on a general weighted graph" (part done); and "Einstein: the continuum realization" (part
done).

## 2. What the pass corrected

1. The brief said the symmetric tide "discharges `rotation_law`'s and `shear_law`'s symmetry premise"; the owner's
   `shear_law` takes no symmetry premise, only `rotation_law` does, so the module meets `rotation_law`'s and reads the
   shear's tidal term as the trace-free screen tide (`shear_of_symm`). The brief's adapted frame was orthonormal for `η
   = diag(−1, 1, …, 1)`, while one of its witnesses, the round sphere, is Riemannian; the frame is stated for `EᵀgE =
   diag(σ, 1, …, 1)` with any `σ ≠ 0`, `σ = −1` for Minkowski and Friedmann and `σ = 1` for the sphere. `CurvatureJets`'
   "What is not claimed" said the symmetries of a 2-jet whose first jet does not vanish are not read and
   `coupling.curvature-jets`' scope still listed the deviation equation along a general geodesic as unstated; both now
   point to their owners.
2. The owner's triangle reads its total by "two strokes", and the atlas row says so ("two strokes read the total that
   one fixed stroke can miss"); that holds for fixed unit strokes. A source that depends on the constitution, the one a
   node potential draws on it (`potentialSource`), is out of proportion under both laws on every incidence where some
   potential slips one edge and not another, so one such stroke suffices on every graph that is not a bundle; the
   diamond is done this way and the cycles by the brief's unit strokes. The box's phrase "the orbit structure of
   deposition on projective classes" has no content on these graphs: under both laws their classes are single
   constitutions, and the orbit structure stands only where a class is wider (the bundle's uniform class, the Joule
   bundle's projective class). The brief's "a second edge then forces `(n − 1)² = 1`" needs a third edge, which `N ≥ 3`
   gives (`exists_third`).
3. The brief read the slice's Ricci tensor at the centre, `2kδ_ij`, as saying "`k` is the slice's sectional curvature";
   that holds for the comoving slice (`A = 1`) only. The slice at scale `A` has sectional curvature `k/A²`, and its
   Ricci tensor reads `2kδ_ij = 2(k/A²)h_ij`, the same components because Ricci's components do not change under a
   constant rescaling of the metric; the module states it so (`slice_sectional`, `slice_ricci`). The record of August
   19, §7.2, calls `k` a "spatial-curvature sign" while its F.2 uses it as a curvature in `−k/a²`; it is `±1` or `0`
   only once `a` is normalized, and here `k` is any real number. `FriedmannFluid`'s "What is not claimed" said the flat
   jet's full Riemann tensor is used only through its Ricci contraction and its tide; its closed form now stands here
   and its symmetries in `TidalScreen`.

## 3. What each statement stands on, and what is left

- `Physics/Spacetime/TidalScreen` stands on `CurvatureJets`' `riemannLower_eq_add`, `contract_inv`,
  `linearCurvature_symmetries` and `tide`, `GeodesicDeviation`'s `tidal`, `frameTidal` and `families_raychaudhuri`,
  `Raychaudhuri`'s `raychaudhuri`, `rotation_law` and `shear_law`, `FriedmannFluid`'s jet and frame, and
  `Geometry/Motion`'s turn and boost. Left: the null (Sachs) screen, an accelerated congruence, the differential Bianchi
  identity, that a parallel frame stays adapted along the geodesic, Sylvester's inertia (every unit timelike `u` has an
  adapted frame), the first row's evolution, the screen tide's spectrum, and a manifold.
- `Objects/RetentionCycles` stands on `RetentionClasses`' `squareLawOn`, `jouleLawOn`, `ProjectivelyEqual`,
  `observeConstitution_scale` and the bundle's classes, `RetentionSeries`' triangle reads and strokes, and
  `Objects/Retention`'s solve, step and future agreement. Left: the two tests for a general graph whose cycles do not
  all share their two ends (a wheel, a grid, a complete graph), a converse (that a medium failing one test has coarser
  classes), the diamond's solve and unit fluxes, laws beyond the square and Joule laws, and convergence or the long-run
  orbit of repeated deposition.
- `Physics/Spacetime/CurvedFriedmann` stands on `FriedmannFluid`'s flat jet, diagonal formulas, comoving fluid, residual
  and `continuity`, `CurvatureJets`' split `riemannLower_eq_add`, `linearCurvature` and `hasDerivAt_christoffel`, and
  `Fluid/NavierStokesCurvedTransport`'s `einsteinResidual`. Left: homogeneity (that every point is the centre of such a
  chart), a global slice, the closed form's symmetries as `CurvatureSymmetries`, Codazzi's equation and Gauss's for a
  general hypersurface, `Ω` with `Λ ≠ 0`, Milne mapped onto Minkowski space, the static universe's instability, de
  Sitter's hyperboloid, and from the box perturbations, the Bianchi identity in general and the Regge construction.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as unstated (`Physics/Spacetime/Raychaudhuri`'s and `GeodesicDeviation`'s "What is not claimed", `CurvatureJets`' "What is not claimed" and `FriedmannFluid`'s, with its sentence on the full Riemann tensor; `Objects/Retention`'s `[open]` paragraph and `RetentionClasses`' and `RetentionSeries`' "What is not claimed"), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules (3,605 jobs), on `+HolonicsResearch` (10,647 jobs) and on `Holonics` (9,166 jobs, rebuilding `Objects/Retention` and its importers) completed with exit 0, with no warning from a new or changed file. Run on the cloud session's four-core host, which rule 4 reaches for a Lean check.
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
