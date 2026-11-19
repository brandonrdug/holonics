# An L-function is a cycle machine whose prime sites carry their own clocks, Chambers' identity holds for every period, and free fall deviates by the tide of any torsion-free connection, in Lean

November 19, 14:18 UTC. The twenty-fourth formalization pass over #410, its twenty-fifth set, after [the
twenty-fourth](2026-11-19_A_DRIVEN_RINGS_ENERGY_IS_ITS_GROWTH_PLUS_ITS_PORTS_SUPPLY_A_ZEROS_TANK_IS_POSITIVE_REAL_ONLY_ON_THE_SEAM_AND_HEAT_RUNS_BELOW_A_FINITE_FRONT_AND_HOLDS_A_GRADIENT_IN_A_POTENTIAL_IN_LEAN.md)
(#1036). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Landmarks/CharacterSites` | The owner's cycle machine with a clock of its own at each site, `diag(θ_i e^(−sℓ_i))`, has the Euler product as its transfer determinant and `Σθ_iᵏe^(−ksℓ_i)` as its closed-word faces (`clockedMachine_det`, `clockedMachine_trace_pow`); with the prime sites' clocks a Dirichlet character's values it is the truncated Euler product of `L(χ, s)`, whose inverse tends to `L(χ, s)` for `Re s > 1`, and mod 1 the owner's prime machine and `ζ` (`characterMachine_det`, `characterMachine_tendsto_L`, `characterMachine_trace_pow_term`, `characterMachine_modOne_tendsto_zeta`); a site is silent at a prime of the modulus and elsewhere turns with an order dividing `φ(N)`, its material a boost `p^(−Re s)` times that turn (`site_silent`, `site_clock_closes`, `site_boost_turn`); the log-derivative `−L′/L(χ, s)` is the sum over sites of their closed-word faces weighted by the length `log p` (`site_vonMangoldt_term`, `neg_logDeriv_eq_sum_sites`); off the real locus a zero paired with its conjugate is the real site `companion(2σ′, |ρ′|²)`, whose trace is the distance from the seam, whose determinant is positive for every zero but `0` and whose discriminant `−4γ²` makes it a rotation at nonzero height (`pairSite_charpoly_map`, `pairSite_faces`, `pairSite_kind`); the quadruple's tanks have the real quartic as their characteristic polynomial and sum to a real impedance on the real axis (`quadrupleQuartic_map`, `quadruple_tank_real`, `quadruple_impedance_real`); at nonzero height the site is the boost `σ′` and the turn `γ` in a real frame, its flow `e^(σ′t)` times a turn at `γ` (`pairSite_similar`, `realify_turn_boost`, `realify_flow`); its quarter turn is the owner's heat chart, it is the tank site on the seam and a shear on the real axis (`heat_is_quarter_turn`, `heat_charpoly`, `pairSite_seam`, `pairSite_axis_not_similar`); `χ₄`'s half-turn at `3` and the real chart of `ρ′ = ½ + i` (`witness_chi4_machine`, `witness_real_chart`) | #410's box "Per-site clocks for L-functions, and the Foster tank chart off the real locus" (ticked; its reading `agent-inferred`); `Landmarks/PrimeCycles` and `Landmarks/ZeroPairSite` | `rh.character-site-clocks`, `rh.foster-tank-pair-chart` (new) |
| `Physics/HarperChambers` | The open chain's determinants are continuants obeying their three-term recursion, and the owner's transfer product holds them as entries, so the discriminant is `Δ(E) = D_q(a) − D_(q−2)(a↑)` (`continuant_succ_succ`, `transferProd_zero_zero`, `transferProd_one_one`, `discriminant_eq_continuant`); subtracting the two corners one entry at a time through cofactors gives the determinant of the cornered chain for any complex corners (`det_sub_smul_single`, `adjugate_updateRow_openChain`, `det_cornered`), and with the Bloch corners `e^(±ik)` Chambers' identity `det(E − H(k)) = Δ(E) − 2cos k` holds for every `q ≥ 1` (`blochMatrix_eq_openChain`, `chambers`); as polynomials the characteristic polynomial is the monic discriminant of degree `q` minus the level `2cos k`, whose roots with multiplicity are the Hermitian eigenvalues (`charpoly_blochMatrix`, `discriminantPoly_monic`, `roots_level`, `rootMultiplicity_level`); the Bloch phase moves only the level, an energy is an eigenvalue at some phase exactly when `Δ(E)` is real in `[−2, 2]`, and `Δ` is real on the real axis (`det_sub_det`, `det_eq_zero_iff_level`, `exists_det_eq_zero_iff`, `discriminant_real`); for Harper's potential (`harper_chambers`, `harper_charpoly`); the free four-cycle `Δ = E⁴ − 4E² + 2` with its double root at `k = 0`, a multiplicity the root set does not see (`chambers_free_four`, `rootMultiplicity_free_four_zero`, `zeros_free_four_zero`) | #410's box "A library constitution equal to the Harper/almost-Mathieu operator" (part done); `Physics/HarperChain`'s "What is not claimed", first item | `gap.harper-chambers` (new); `gap.harper-ring-chain` (expression, scope) |
| `Physics/Spacetime/GeodesicDeviation` | For a connection given by its coefficients and their jet, with the owner's Riemann formula (`riemannOf`, of which the owner's `riemann` of a metric's 2-jet is the Levi-Civita case, `riemann_eq_riemannOf`), the covariant derivative along a curve has the rate the chain and product rules give (`covD`, `hasDerivAt_gammaForm`, `hasDerivAt_covD`); along a family of curves the commutator of the two covariant derivatives is the curvature, for any connection (`curvature_apply`, `covD_commutator`); for a torsion-free connection the deviation's covariant derivative is the velocity's along the family, and on a family of geodesics the deviation accelerates by minus the tide, `D_τ²ξ^a = −R^a_bcd u^bξ^cu^d` (`covD_symm`, `curvature_deviation`, `deviation`, `deviation_tidal`); at the Minkowski frame the tidal matrix at `e₀` is the owner's tide (`tidal_observer`, `tide_eq_tidal`); in a parallel frame the frame components of `n` families on one geodesic obey `J″ = −𝓡J`, `𝓡 = E⁻¹R(·, u)uE`, in the shape of `Raychaudhuri`'s premise, so its equation follows (`frame_deviation`, `families_frame_deviation`, `families_raychaudhuri`); witnesses: lines in a flat connection, a constant connection of curvature `−k²` through its parallel frame and Raychaudhuri's equation, and the round sphere's meridians through the owner's `christoffel`, where `D_τ²ξ = −ξ` (`lines_deviation`, `constΓ_deviation`, `constΓ_raychaudhuri`, `sphere_christoffel`, `sphere_deviation`) | #410's box "Curvature's strain and rotation" (part done); `Physics/Spacetime/CurvatureJets`' and `Raychaudhuri`'s "What is not claimed" | `coupling.geodesic-deviation` (new); `coupling.raychaudhuri-riccati` (scope) |

The boxes these answer, by their opening words: "Per-site clocks for L-functions" (ticked); "A library constitution
equal to the Harper/almost-Mathieu operator" (part done); and "Curvature's strain and rotation" (part done).

## 2. What the pass corrected

1. The box carries no text past its title; the module reads "per-site clocks" as a phase of finite order at each prime
   site beside the common clock `s` (a Dirichlet character's value) and "the tank chart off the real locus" as the zero
   paired with its conjugate, and marks both readings `agent-inferred`. The brief's quarter turn was stated for both
   roots and holds for one: `−iρ′ = γ − iσ′` is a root of the heat chart, while the other heat root `γ + iσ′` is `iρ̄′`,
   the conjugate of `−iρ′`, so the heat chart is the pair site of the quarter-turned zero `−iρ′` with its conjugate. The
   brief's similarity of the real site to `σ′·1 + γJ` needs `γ ≠ 0`: on the real axis the site `companion(2σ′, σ′²)` is
   a shear (null in SiteKind's trichotomy, with positive determinant and zero discriminant), not a boost, and is similar
   to no `σ′·1` (`pairSite_axis_not_similar`). `Landmarks/ZeroPairSite`'s paragraph that ended on the tank chart having
   no real face off the seam now names the paired chart.
2. The owner's `discriminant_eq_two_cos_of_det` and `det_eq_zero_iff_discriminant` carry a periodicity hypothesis on the
   potential that the matrix statement does not need: it is used only by their route through the infinite chain, and
   `det_eq_zero_iff_level` holds for every potential. The brief's corner form `det = A − (c + d) + c·d·B` holds with `B
   = −D_(q−2)(a↑)`, the transfer product's lower-right entry. `Physics/HarperChain`'s "What is not claimed" and the
   atlas row `gap.harper-ring-chain` named the identity for general `q` as unstated; both now name this module. The
   record of the twenty-first set (#1033), §3, reads the identity as proved at `q = 2, 3` only, which was its reading
   that day.
3. The box reads "Raychaudhuri's equation from a Lorentzian metric, connection and congruence"; the deviation step needs
   only a torsion-free connection, and a metric enters only for the symmetric tide read on the screen orthogonal to a
   timelike velocity, which is what stays. Neither `Raychaudhuri`'s `R_ij = R_(iajb)u^au^b` nor `CurvatureJets`' `R_ij =
   R_(i0j0)` on the lowered tensor is the general matrix in `J″ = −RJ`: that matrix is `𝓡 = E⁻¹R(·, u)uE`, built from
   the tensor with one index up, and the lowered forms agree with it in an orthonormal frame, which `tide_eq_tidal`
   checks at the Minkowski frame. `CurvatureJets`' sentence that the deviation equation along a general geodesic "stays
   owed" and `Raychaudhuri`'s that it is derived from no metric's connection now name this module.

## 3. What each statement stands on, and what is left

- `Landmarks/CharacterSites` states the character machine with its Euler product, closed-word faces, site clocks and
  log-derivative per site, and the paired real chart of an off-seam zero's tank with its faces, its boost and turn, the
  quadruple's real impedance and the quarter turn to the heat chart. Hecke and Artin `L`-functions, the continuation of
  `L(χ, s)` and its zeros, the generalized Riemann hypothesis, the explicit formula, the conjugation symmetry of the
  zeros (a premise), and a realization of the quadruple's impedance, which off the seam has two poles in `Re w > 0` (an
  active one-port), are not stated. The box is ticked.
- `Physics/HarperChambers` states Chambers' identity for every period with its polynomial form and multiplicities. The
  integrated density of states as a spectral count (each band carrying one eigenvalue for each Bloch phase, which needs
  the oscillation of `Δ`), the band edges, the Cantor spectrum, the open gaps, the Chern number and Hall conductance,
  the edge receiver with `t` channels and the Thouless pump are not stated. The box stays part done.
- `Physics/Spacetime/GeodesicDeviation` states the deviation equation along a general geodesic of a torsion-free
  connection and its frame form, the premise of `Raychaudhuri`. The family's partial derivatives are given at a point
  rather than derived from a `C³` family, geodesics and a parallel frame are hypotheses, and the reduction to the screen
  orthogonal to a timelike velocity, the tide's symmetry from metric compatibility, conjugate points and the Morse
  index, and a manifold without coordinates are not stated. The box stays part done.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as unstated (`Landmarks/ZeroPairSite`'s paragraph on the tank chart off the seam, `Physics/HarperChain`'s "What is not claimed" on Chambers' identity for general `q`, and `Physics/Spacetime/CurvatureJets`' and `Raychaudhuri`'s sentences on the deviation equation), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (8907 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10641 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0 (no file of the `Holonics` library changed in this set; every repointed owner is a research module). The messages printed are other modules' notes, none in a new or changed file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
