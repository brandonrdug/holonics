# A declared dimension is certified by its eliminants, lock and key deposited on both sides meet at the matched pair nearest their opening, and a port-Hamiltonian aeon produces what its resistance dissipates, in Lean

November 19, 09:02 UTC. The sixteenth formalization pass over #410, its seventeenth set, after [the
sixteenth](2026-11-19_A_PARTS_ADDRESS_ON_A_SPAN_IS_READ_FROM_ITS_LAST_CELLS_A_COMPLEX_RELATION_IS_MADE_PASSIVE_BY_A_CLIP_AVERAGED_OVER_THE_QUARTER_TURN_AND_AN_ENCLOSURE_SHARES_THE_WORD_EVERY_VALUE_IN_IT_READS_IN_LEAN.md)
(#1028). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Compression/Landmark/EliminantCertificate` | The eliminant certificate of a declared dimension `d` (a nonzero generator whose variables lie in every set of `d + 1` coordinates) is a finite check on the declared variable sets (`EliminantCertificate`, `CoversSets`, `eliminantCertificate_iff_coversSets`); with generators vanishing on `V` it makes every `d + 1` coordinates algebraically dependent in the coordinate ring, bounds every independent family of coordinate functions by `d`, and on an irreducible `V` bounds the transcendence degree by `d`, a transcendence basis being chosen among the coordinates (`coordinates_dependent`, `mk_le_of_certificate`, `trdeg_le_of_certificate`); at `d = 0` it is finiteness (`finite_iff_exists_eliminantCertificate_zero`); without it the plane declared a curve lets the axis chart invent the identity `y` (`not_eliminantCertificate_univ`, `axis_chart_invents_an_identity`); the identities in a finite family's span are the joint kernel of its chart pullbacks (`mem_ker_familyPullback_iff`, `ker_familyPullback_eq_identities`); and a candidate that is not one is refused at one of `deg N + Σ deg D_i + 1` parameters (`exists_param_nonroot`, `exists_alternatingParameter_nonroot`); the circle and the twisted cubic witness it (`circle_trdeg_le_one`, `twisted_cubic_certificate`) | #410's box "The executable dimension and eliminant certificate of `compression::landmark::identity`"; the retired `compression/landmark/identity.rs` (`2d34b819`); `Compression/Landmark/Identity`, `Compression/Landmark/ChartDensity`; Mathlib's `exists_isTranscendenceBasis_subset` | `landmark.eliminant-certificate` (new) |
| `HNN/ContactFixedPoint` | Two-sided deposition across a contact, `x ← x − αAᵀΔ` and `y ← y + βBᵀΔ` on the slip `Δ = Ax − By − c`, is the step `z ← z − DMᵀ(Mz − c)` (`step_joint`); its fixed points are the minimizers of the slip square, the matched pairs whenever one exists, and every fixed slip is the one cokernel residual of the offset, which persists at every state (`isFixed_iff_minimizes`, `normal_iff_matched`, `slip_eq_of_normal`, `residual_unique`, `residual_persists`); under the step bound the slip square falls by `⟨MᵀΔ, DMᵀΔ⟩`, strictly off the fixed points (`quadrance_step_le`, `quadrance_step_lt`); each step conserves the inverse-rate pairing with the readings' kernel, so the iterates converge geometrically, the spectral gap discharged by compactness, to the inverse-rate-nearest fixed point to the opening (`wpair_step`, `meeting_nearest`, `exists_meeting`, `exists_gap`, `converges_geometric`, `tendsto_meeting'`); at rate zero one side stays while the other does all the moving, and exchanging the sides exchanges the updates (`twoStep_rate_zero`, `twoStep_swap`); for a linear menu the keys are an affine fibre gauged by `ker M`, and deposition locates the one gauge-fixed by the opening (`keys_eq_orbit`, `gauge_fix_unique`, `deposition_locates_key`); the scalar contact meets at `(½, ½)` from `(1, 0)` (`witness_equal_rates`, `witness_meeting`) | #410's boxes "The fixed point of two-sided deposition across a contact" and "Continuous keys" (part); the record of October 5, §J9; `HNN/Keys`, `Compression/Core/Keys` | `contact.two-sided-deposition` (new), `key.continuous-fibre` (new) |
| `Aeon/Production/PortHamiltonian` | An aeon of implicit-midpoint steps of a port-Hamiltonian Holon produces `Σ_k h⟨e_k, R e_k⟩/T ≥ 0`, additive over epochs and under concatenation, equal to the first law's remainder `T σ = supplied work − ΔH`, zero exactly when the resistive part annihilates every effort (`production_nonneg`, `production_add`, `production_concat`, `first_law`, `production_eq_zero_iff`); the skew interconnection carries no power, so a lossless aeon stores every supplied work and on a cycle the supplied work is `T σ ≥ 0` (`interconnection_power_zero`, `step_power`, `lossless`, `cycle_unsupplied`, `clausius`); the pair contact produces `⟨Jv, D Jv⟩/T`, its dissipated power over `T` (`contactProduction_nonneg`, `contactProduction_eq_power`, `production_contactMaterial`); a continuous-time chain's uniformized epoch production is `h σ_rate` for every `h ≠ 0`, so the rate inherits the discrete owner's sign and zero set (`epochProduction_uniformized`, `productionRate_nonneg`, `productionRate_eq_zero_iff`, `production_uniformized`); and `(a − b) log(a/b) ≥ 2(a − b)²/(a + b)` puts every Markov production above the quadratic dissipation of its net currents (`onsager_le`, `epochProduction_ge_quadraticDissipation`, `dissipation_effort_form`) | #410's box "Production beyond Markov chains: `production(aeon)` for port-Hamiltonian instances"; the aeon record of September 24, §A5 and §A6; `Aeon/Production/PathReversal`, `Holon/Element.midpoint_balance`, `Holon/Dirac`, `Holon/Conformance.pairContact_resistive` | `aeon.port-hamiltonian-production` (new), `aeon.generator-production-rate` (new), `aeon.a5-production-clock` |

The boxes these answer, by their opening words: "The executable dimension and eliminant certificate"; "The fixed point
of two-sided deposition across a contact"; "Production beyond Markov chains"; and "Continuous keys" (part).

## 2. What the pass corrected

1. **The check that runs reads declared variable sets.** The box asks for an executable certificate; Mathlib's
   `MvPolynomial.vars` is noncomputable, so the certificate on polynomials is decidable by an instance Lean does not
   compile, and the check that `decide` runs is `CoversSets` on the declared variable sets, joined to the polynomial
   statement by `eliminantCertificate_iff_coversSets`. The Galilean fibre `C² − 1` carries the point certificate only in
   its one coordinate `C`; in the owner's coordinates `(C, S)` it is two lines and fails it, which is the owner's
   refusal of `C = 1` declared a point (`line_declared_point_refused`, `point_chart_invents_an_identity`).
   `Compression/Landmark/Identity`'s open paragraph and `ChartDensity`'s "What is not claimed" named a curve's dimension
   certificate as unstated; both now point to the module.
2. **The key alone reaches the matched pair in one step only at the full rate.** The brief's witness put the key alone
   at `α = ½, β = 0` reaching `(0, 0)` in one step; one step at those rates reaches `(½, 0)` with the slip halved, and
   `(0, 0)` in one step needs `α = 1`, the step bound with equality (`witness_key_alone` states both). The spectral gap
   is taken as `G² ⪰ μG` for every covector, which needs no restriction to `range M` and is what the inverse-rate
   contraction reads; its existence is proved. The record's consumer `hnn::keys` is the Rust owner retired with the
   October machine; the consumer is the Lean `HNN/Keys`, whose closing sentence, with `SurvivorsCycleFibre`'s, now
   points to the module for linear contacts.
3. **The Holon reading of production has owners.** The aeon record's §A5 marked "σ is the resistive term `⟨Jv, D Jv⟩/T`;
   the Dirac interconnection and the Cayley reaction contribute zero" `agent-inferred`, and the atlas row
   `aeon.a5-production-clock` carried it as "Holon reading agent-inferred"; both halves are now proved for the midpoint
   aeon, and the row is graded `formal-checked` with that scope. The zero set needs `h > 0` and reads only the symmetric
   part of `R`: for a positive semidefinite `R` with a skew part, the condition is `(R + Rᵀ)e_k = 0`. The uniformization
   identity holds for every `h ≠ 0`; the bound `h|L_xx| ≤ 1` gives the nonnegativity the discrete owner reads, and
   stochasticity comes from the rows of `L` summing to zero, which only additivity needs. The edge coefficient `(J_xy +
   J_yx)/2` maps an affinity to a current, a conductance in circuit words, and is named `onsagerCoefficient`.
   `Aeon/Production/PathReversal`'s closing note now points to the module.

## 3. What each statement stands on, and what is left

- `Compression/Landmark/EliminantCertificate` stands on `Compression/Landmark/Identity.{identityIdeal,
  certified_eval_iff}`, `ChartDensity.{finite_iff_coordinate_certificates, unitCircle_irreducible,
  circleChart_image_ideal}` and Mathlib's transcendence bases. Not stated: the lower bound `trdeg = d`, a chart's
  density in a component of dimension `d` beyond the plane curve, primary decomposition, the elimination of eliminants
  from arbitrary generators, charts of two or more parameters, the rational chart's pullback numerator, Gröbner
  completion with `J = ker(face)` and Richardson undecidability (the last two stay in #410's identity-atlas box).
- `HNN/ContactFixedPoint` stands on Mathlib's finite-dimensional linear algebra and compactness alone; it cites
  `HNN/Keys` and `Compression/Core/Keys` without importing them. Not stated: nonlinear readings and curved configuration
  spaces (phase and rotation keys), which keep the continuous-keys box part done; noise; a law for the rates; and the
  equivalence of the gap form with a bound on `range M`.
- `Aeon/Production/PortHamiltonian` stands on `Aeon/Production/PathReversal.RealChart.{epochProduction,
  epochProduction_nonneg, epochProduction_eq_zero_iff, production_eq_mul}`, `Holon/Element.midpoint_balance`,
  `Holon/Dirac.{skewGraph_isDirac, IsDirac.power_eq_zero}` and `Holon/Conformance.pairContact_resistive`. Not stated:
  the path-measure production of a noisy port-Hamiltonian system, the continuum limit of the midpoint aeon, the
  Kolmogorov–Sinai entropy, the first-order equality near detailed balance, a temperature varying along the aeon, and
  the reading of `T σ` as heat delivered to a bath.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owners that named these statements as unstated (`Compression/Landmark/Identity`'s open paragraph and `ChartDensity`'s "What is not claimed" on a curve's dimension certificate; `HNN/Keys`' and `SurvivorsCycleFibre`'s closing sentences on continuous keys; `Aeon/Production/PathReversal`'s closing note on the port-Hamiltonian form of production; the three `Holonics` modules and their few importers were rebuilt), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (8780 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, with `lean_census.py` reading unrooted=0) read `Build completed successfully (10617 jobs)`, exit 0; `Holonics`, with `Compression/Landmark/Identity`, `HNN/Keys` and `Aeon/Production/PathReversal` and their importers rebuilt, read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' linter notes, none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
