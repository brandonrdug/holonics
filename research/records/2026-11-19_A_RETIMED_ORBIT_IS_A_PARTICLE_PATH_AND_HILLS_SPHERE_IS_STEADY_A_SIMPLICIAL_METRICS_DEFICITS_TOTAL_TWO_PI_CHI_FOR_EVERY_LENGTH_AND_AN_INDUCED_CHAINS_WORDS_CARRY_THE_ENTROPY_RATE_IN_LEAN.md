# A re-timed orbit is a particle path and Hill's sphere is steady, a simplicial metric's deficits total 2πχ for every length, and an induced chain's words carry the section's entropy rate, in Lean

November 19, 16:15 UTC. The twenty-seventh formalization pass over #410, its twenty-eighth set, after [the
twenty-seventh](2026-11-19_A_METRICS_TIDE_IS_A_SELF_ADJOINT_BOOST_ON_ITS_SCREEN_A_CURVED_SLICE_ADDS_K_OVER_A_SQUARED_TO_FRIEDMANN_AND_EVERY_CYCLE_RETAINS_ITS_WHOLE_CONSTITUTION_IN_LEAN.md)
(#1041). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Fluid/HillVortex` | the clock `2π|W|²` is positive off the pair's sites and rescales the generator's field to the velocity, `(2π|W|²)⁻¹ conj(c) W = conj F′` (`clockRate_pos`, `clock_rescales_field`); through a local inverse of the clock the orbit moves at `conj F′`, and along a whole orbit that avoids the sites the clock increases strictly and has a left inverse continuous at each reading, so the re-timed orbit is a particle path (`particle_velocity`, `exists_left_inverse`, `orbit_is_particle_path`); Hill's spherical vortex on the meridian half-plane: the stream functions give the velocity on each side (`hasDerivAt_streamIn_s` to `hasDerivAt_streamOut_z`), continuity holds, `ω = (15U/2a²)s` inside and `0` outside with `ω/s` carried by the flow, and `E²ψ = −15Us²/(2a²)` inside (`continuity_in`, `continuity_out`, `vorticity_in`, `vorticity_out`, `stokesOperator_in`, `vorticity_transported_in`, `vorticity_transported_out`); for any meridian flow with `ω = A s` Bernoulli's pressure `H − Aψ − ½|u|²` balances the advection, so Hill's flow is a steady Euler flow on both sides (`momentum_balance`, `euler_in`, `euler_out`); on `r = a` both stream functions vanish and the velocity and the pressure match, so no vortex sheet stands there, with `ψ > 0` inside and `ψ < 0` outside (`velocity_match_sphere`, `velocity_tangent_sphere`, `pressure_match_sphere`, `streamIn_pos`, `streamOut_neg`); the exterior is the stream past a sphere, a uniform stream and a dipole of strength `Ua³/2` with its far-field bounds (`streamOut_eq_uniform_add_dipole`, `hasDerivAt_potentialOut_s`, `far_field`); the one flow across the sphere has its first derivatives everywhere and vanishes exactly on the sphere (`hasDerivAt_ite_of_eq`, `hillStream_hasDerivAt`, `hillStream_eq_zero_iff`, `hill_continuousAt_sphere`); the circulation over the meridian half-disc is `5Ua`, the speed on the sphere `(3/2)U sin θ`, the poles stagnation points, and the core `(a/√2, 0)` a stagnation point at `ψ = 3Ua²/16` whose traceless gradient is a rotation site (`circulation`, `speed_on_sphere`, `poles_stagnation`, `core_is_rotation_site`) | #410's box "Norbury's vortex-ring family, from a torus to Hill's sphere" (part done); `Physics/Fluid/Singularity`'s `[open]` paragraph | `fluid.streamline-clock-particle-path`, `fluid.hill-spherical-vortex` (new); `fluid.singularity-arrival-singular-aeon` (scope) |
| `Physics/Spacetime/ReggeDeficit` | for lengths with the strict triangle inequalities the corner opposite `a` is `arccos((b² + c² − a²)/(2bc))`, in `(0, π)`, the angle of every Euclidean triangle with those sides (the law of cosines), such a triangle stands in `ℂ`, and the three corners sum to `π` by Mathlib's angle sum (`cornerAngle`, `angle_eq_cornerAngle`, `triangle_exists`, `cornerAngle_add`); on a closed triangulated surface, every side met by two triangle-corner slots, `2E = 3F`, the corners sum to `πF`, and the deficit `ε_v = 2π − Σ` corners at `v` totals `2π(V − E + F)` for every length assignment, so the two-dimensional Regge action carries no dynamics (`ClosedSurface.two_mul_card_edges`, `SimplicialMetric.sum_angleAt`, `SimplicialMetric.gauss_bonnet`, `regge_action_two_invariant`), built as the owner's `TriangulatedGaussBonnetLedger`, whose bulk curvature is the deficit (`SimplicialMetric.toLedger`, `SimplicialMetric.deficit_eq_bulkCurvature`); witnesses: at unit lengths `ε_v = (π/3)(6 − deg v)`, the tetrahedron's deficits `π` and the octahedron's `2π/3`, both totalling `4π`, and the cube's corner with `π/2` at the apex and `7π/6` at the other three (`unitMetric_deficit`, `tetrahedron_total`, `octahedron_total`, `cubeCorner_witness`); in three dimensions the hinge deficit `ε_e = 2π − Σ_σ θ_σ(e)` and the action `Σ_e ℓ_e ε_e`, with the regular tetrahedron's dihedral angle `arccos(1/3)` (`TetraComplex.hingeDeficit`, `TetraComplex.reggeAction`, `dihedralAngle_regular`, `regularTetra_reggeAction`) | #410's box "Einstein: the continuum realization" (part done); `Physics/Spacetime/Einstein`'s `[open]` paragraph | `gr.regge-deficit-gauss-bonnet` (new); `ns.polygon-gauss-bonnet` (scope) |
| `Aeon/Production/InducedWords` | the owner's first-step equations have one solution, a solution is its truncated series plus the field still avoiding the section, which is bounded by the survival mass and dies out, so for a nonnegative observable the solution is the series `Σ_n avoidⁿ f` (`firstReturnSolution_eq`, `firstReturn_split`, `avoid_iterate_tendsto_zero`, `firstReturnSolution_hasSum`); the induced chain `P_A(y, y′)`, the solution for `f = P(·, y′)`, is the series of first landings, nonnegative, with rows of mass one on `A` because the landing fields add to the solution the constant `1` also gives (`inducedKernel_hasSum`, `inducedKernel_row`, `inducedKernel_stochastic`); with `π` stationary the owner's `kac_observable` at `f = P(·, y′)` gives `Σ_(y∈A) π_y P_A(y, y′) = π_(y′)`, so `π_A = π|_A/π(A)` is stationary for the induced chain (`occupation_stationary`, `induced_stationary`, `sectionLaw_stationary`); the words of successive coarse epochs form a chain through the end state's kernel `Q_N`, whose block entropy obeys the chain rule and from a stationary law is `n` times the per-word entropy (`endKernel_succ`, `blockEntropy_succ`, `twoWord_chain_rule`, `blockEntropy_of_stationary`); as `N → ∞`, `H_N(y) → H(W_y)` and `Q_N → P_A`, so from `π_A` `n` words carry `n·Σ π_A H(W_y) = n·Σ π h/π(A)`, the word chain's entropy rate `h(T)/μ(A)` (`wordEntropy_tendsto`, `endKernel_tendsto`, `wordChain_blockEntropy_tendsto`, `wordChain_abramov`, `wordChain_entropyRate`); witness on three states with `P_A = [[1/2, 1/2], [1, 0]]`, `π_A = (2/3, 1/3)` and rate `(2/3) log 2` (`loop_inducedKernel`, `loop_sectionLaw`, `loop_wordChain`) | #410's box "The Kolmogorov–Sinai entropy of the induced shift" (part done); `Aeon/Production/Kac`'s `[open]` paragraph | `aeon.induced-chain-stationary`, `aeon.word-chain-entropy-rate` (new); `aeon.abramov-ledger` (meaning), `aeon.abramov-induced-chain` (expression and scope), `aeon.a4-entropy-clock-change` (scope) |

The boxes these answer, by their opening words: "Norbury's vortex-ring family" (part done); "Einstein: the continuum
realization" (part done); and "The Kolmogorov–Sinai entropy of the induced shift" (part done).

## 2. What the pass corrected

1. The egg record of September 24 (§4) grades Norbury's torus-to-sphere family `[proved-standard]` (Norbury 1973).
   Norbury computed the members between the ends numerically, and only the ends are closed forms (Hill's sphere, and the
   thin ring as a limit); the grade holds for the ends, and the module builds the sphere end. The box files the family
   under the planar owner `Physics/Fluid/Singularity`: Hill's flow is axisymmetric, its meridian velocity is not
   divergence-free in `(s, z)` (continuity carries the factor `s`), so it is not one of that owner's Möbius-navigator
   flows; it joins the owner through the clock and through the site kind of its core's gradient. The brief gave the
   inner vorticity as `−(15U/2a²)s`; with the convention it stated (`u_s = −(1/s)∂_zψ`, `ω = ∂_z u_s − ∂_s u_z`) it is
   `+(15U/2a²)s`, and `E²ψ = −15Us²/(2a²)` and the circulation `5Ua` agree with the module. The atlas row
   `fluid.singularity-arrival-singular-aeon` called the reparametrization "not yet formalized"; it now points to the
   clock built here.
2. `Physics/Spacetime/Einstein`'s `[open]` reads the Regge construction as "`G` is the boundary of the moment of
   rotation `F`" (Misner–Thorne–Wheeler §15.4). In the book's account, as the worker recalled it and without a check
   against the text (`agent-inferred`), the Einstein tensor is (the dual of) the moment of rotation, and its
   conservation is "the boundary of a boundary is zero" applied to the moment of rotation of each cell's faces; read
   that way the owner's `G = ∂₂F` puts the moment of rotation one level below the book's. The owner's sentence is kept
   and given a pointer; the level is to be read against §15.4 before the four-dimensional step is built. The August 10
   record's combinatorial charge `6 − |link(v)|` is `(3/π)ε_v` at unit lengths only where the link is one cycle; the
   module counts corners (`deg v`) and says so. The ledger the box needed stood in `Fluid/NavierStokesCurvedTransport`
   with its corners, budgets and incidence supplied; here they are built.
3. `Aeon/Production/Kac`'s `[open]` paragraph and the atlas rows `aeon.abramov-induced-chain` and
   `aeon.a4-entropy-clock-change` named the statement "owed in #62", which closed on October 22 into #410; they now
   point to #410 and to this module. `aeon.abramov-induced-chain` wrote "`H_N(y) → M(y)`" where the owner defines no
   pointwise `M` and proves only the information-rate limit; the pointwise limit is now `wordEntropy_tendsto`, the
   series `Σ_n (avoidⁿ h)(y)`. The owner called `H_N` "the truncation of the first-step solution of `h`", while that
   solution exists over `ℚ` and `h` is real; it now reads "the truncation of the series `Σ_n avoidⁿ h`". The owner's
   prose and `aeon.abramov-ledger` called the ledger and its rationals "exact", which the precision law bars; the word
   is gone from both. The new statements take no sign of `π`, where the owner's `abramov` takes `π ≥ 0`: the ledger's
   tail dies by `avoid_iterate_tendsto_zero`.

## 3. What each statement stands on, and what is left

- `Physics/Fluid/HillVortex` stands on `Physics/Fluid/Singularity`'s generator field, potential and Cayley site kinds
  and on Mathlib's derivatives, inverse-function derivative and interval integrals. Left: Norbury's family between its
  ends, the thin ring's Kelvin speed, stability, swirl, uniqueness of Hill's vortex and existence from initial data, its
  impulse and energy, the one flow's second derivatives on the sphere, and the clock built as the integral of `2π|W|²`
  along an orbit.
- `Physics/Spacetime/ReggeDeficit` stands on Mathlib's law of cosines and angle sum and on
  `Fluid/NavierStokesCurvedTransport`'s `TriangulatedGaussBonnetLedger`. Left: Schläfli's identity and Regge's equations
  `∂S/∂ℓ_e = ε_e`, the dihedral angle as the angle between a realized tetrahedron's faces and the Cayley–Menger
  realizability, the four-dimensional moment of rotation and `G` built from it, the holonomy reading of a deficit as a
  theorem, the continuum limit and Lorentzian signature.
- `Aeon/Production/InducedWords` stands on `Aeon/Production/Kac`'s `avoid`, `survival`, `FirstReturnEquations`,
  `kac_observable`, `firstReturn_existsUnique`, `wordLaw`, `wordEntropy_succ` and `abramov_ledger`, and
  `Foundation/SituatedInformationRate`'s `informationRate`. Left: the Kolmogorov–Sinai entropy as a supremum over
  partitions and the generator theorem that would identify it with the word chain's entropy rate, Abramov's formula for
  a general ergodic measure-preserving map, countable state spaces, the block entropy of the unconditioned mixture
  (within `log |A|`), a path-space measure with the strong Markov property, `H(W_y)` as the entropy of the untruncated
  word law, and the limits in the other order.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the texts that named these statements as unstated (`Physics/Fluid/Singularity`'s `[open]` paragraph, `Physics/Spacetime/Einstein`'s `[open]` paragraph with a pointer beside its sentence on the Regge construction, and `Aeon/Production/Kac`'s `[open]` paragraph, whose prose also lost the word "exact"), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules (3,530 jobs), on `+HolonicsResearch` (10,650 jobs) and on `Holonics` (9,166 jobs, rebuilding `Physics/Fluid/Singularity`, `Physics/Spacetime/Einstein` and `Aeon/Production/Kac` and their importers) completed with exit 0, with no warning from a new or changed file. Run on the cloud session's four-core host, which rule 4 reaches for a Lean check.
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
