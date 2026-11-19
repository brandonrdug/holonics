import Holonics.Physics.Information
import Holonics.HNN.Ratio
import Holonics.HNN.Ratio.Resolution

/-!
# The information port: the finite-step limit, a moving support, the phase face, `R⁻¹dR` at both ports

[definition] Rebuild step 6, K4 (#75), continuing `Physics/Information`. This module answers the #410
box "The information port (`Physics/Information`): moving supports; the phase-face port; the HNN's
`R⁻¹dR` (`HNN/Ratio`) joined to `physics::information::apply`; the finite-step quasi-static limit".
The box restates the `[open]` paragraph of `Physics/Information`, the scope line of
`Physics/Information/CrossEntropyRate` ("a moving support needs a one-sided or measure transport")
and the last paragraph of `Physics/Information/PortWork` ("the phase face of the covector … is
retained for a port that receives phase"). The Rust consumer `physics::information::apply` stood in
`crates/holonics`, retired with C8 of #603 (held at `d5ed4adc1`): it is named here as the retired
consumer and not restated, and the join is made to the Lean owners: `PortWork` (the thermal port),
`Objects/Ratio` and `Objects/RatioPhase` (the lifted log ratio, `R⁻¹dR` as `ratioCovector`, and
`alignCost`), `HNN/Ratio` (whose `receivingPhase_phase_pullback` and `alignCost_turns` read the same
`alignCost` through the receiving ring) and `HNN/Ratio/Resolution` (Hoeffding's lemma on a face).
Atlas rows: `info.port-work`, `info.cross-entropy-rate`, `info.learning-covector`,
`info.equal-face-different-effort`, `ratio.two-sided-covector`, `receiver.resolution-tilt-divergence`,
`hnn.align-cost-turns`, `xent.network-entropy-production`, `info.contact-kl-diffusion`.

Conventions. As in `PortWork`, `p` is the port's population and `q` its canonical reference at levels
`E` and thermal scale `θ = k_B T`; work is done on the ensemble, so the owner's
`restoreWork θ E δ = θ log Z(E + δ) − θ log Z(E)` is the quasi-static leg's work on it. As in
`Objects/Ratio`, `ℓᵢ = log̃ z^T_i − log̃ z^H_i` with `T` the target and `H` the produced; at the port
the target is the reference `q` and the produced is the population `p`. As in `Objects/RatioPhase`,
the ring's angle is the produced imaginary logit `y`, with `φ^H = y/2` and gap `Δ_c = φT_c − y_c/2`.

[proved-derived; formal-checked] What is proved (Hoeffding's lemma and the entrance limits are
`[proved-standard; formal-checked]`).

1. **The finite-step quasi-static limit.** The restoring leg from `E + δ` to `E` runs as `N` steps:
   levels `E_k = E + (1 − k/N)δ` (`legLevel`), states `q_k`, the canonical state of `E_k`
   (`legState`); step `k` is the owner's quench (`stepWork`, the owner's `quenchWork` of
   `E_(k+1) − E_k` on `q_k`) and relaxation (`stepHeat`, the owner's `relaxHeat`).
   (a) Each step produces `D(q_k‖q_(k+1))` (`stepProduction_eq`, the owner's
   `free_relaxation_production` at `E_(k+1)`), its entropy change less its heat over `θ`
   (`stepProduction_heat`), under its first law (`step_first_law`); summed, the leg's production is
   its entropy change less its heat over `θ` (`legProduction_heat`, the `N`-step form of the owner's
   `restoreProduction`), and its first law runs between the owner's end states (`leg_first_law`).
   (b) One step's bound: `D(canonical E ‖ canonical (E + η)) ≤ ((b − a)/θ)²/8` for `a ≤ η ≤ b`, and
   `≤ (M/θ)²/2` for `|η| ≤ M` (`kl_canonical_shift_le`, `kl_canonical_shift_le_abs`): Hoeffding's
   lemma on the owner's face (`HNN/Ratio/Resolution.klDivergence_face_shift_le`, through
   `PortWork.canonicalState_eq_face`).
   (c) Each of the `N` steps produces at most `((b − a)/(Nθ))²/8` (`stepProduction_le`), so the leg
   produces at most `(b − a)²/(8Nθ²)` (`legProduction_le`), never less than `0`
   (`legProduction_nonneg`), and its production tends to the owner's zero `restoreProduction` as
   `N → ∞` (`legProduction_tendsto`).
   (d) The discrete second law. A step's work is its drop in `θ log Z` plus `θ D(q_k‖q_(k+1))`
   (`stepWork_eq`, the owner's `extracted_work_general` with a canonical population), so the leg's work
   is `restoreWork + θ Σ_k D(q_k‖q_(k+1))` (`legWork_eq`): it never falls below `restoreWork` and
   tends to it (`legWork_tendsto`); its heat is `restoreHeat − θ Σ_k D(q_k‖q_(k+1))` and tends to
   `restoreHeat` (`legHeat_eq`, `legHeat_tendsto`). The owner's zero production on the restoring leg
   (`restore_production_zero`) is this limit.
2. **A moving support.** (a) A flux on edges (`edgeRate`, `ṗᵢ = Σⱼ (J_ji − J_ij)`) keeps the total
   (`sum_edgeRate`), and against a positive reference the population term of the rate is
   `−Σ ṗᵢ log qᵢ = Σ_(i,j) J_ij log(qᵢ/qⱼ)` (`edgeRate_population_term`): a unit moved from `i` to `j`
   costs `log(qᵢ/qⱼ)`, and that is the cross-entropy's rate at a fixed reference
   (`hasDerivAt_crossEntropy_edges`, through the owner's `FirstLaw.hasDerivAt_crossEntropy`).
   (b) No positivity is asked of the population: with nonnegative masses the cross-entropy against a
   positive reference keeps the two-sided rate `−Σ ṗ log q − Σ p q̇/q`, and a cell empty at `t` has
   two-sided rate `0` (`moving_support_rate`), so a mass enters at a nonzero rate only one-sidedly.
   (c) At an entrance (`p(t) = r t` for `t ≥ 0`, `r > 0`) the relative entropy's term `p log(p/q)` has
   a right difference quotient tending to `−∞` (`entrance_relTerm`) and the entropy's term one tending
   to `+∞` (`entrance_entTerm`), while the cross-entropy's term has the finite right rate `−r log q`
   (`entrance_crossTerm`); over a population whose other cells are populated with right rates, the
   relative entropy (what free relaxation at the port produces) moves at `−∞` from the right
   (`entrance_relativeEntropy`).
   (d) A reference cannot leave a populated cell at finite code: if `pᵢ ≥ c > 0` while `qᵢ → 0⁺`,
   the cross-entropy tends to `+∞` (`crossEntropy_tendsto_atTop`).
3. **The phase-face port.** Each channel `c` is a ring at angle `y_c` held about the target's phase by
   a torsional store of stiffness `q_c`, with energy the owner's `alignCost q φT y`. (a) Its effort is
   `½ q_c Δ_c` (`ringEffort`), minus the owner's gradient (`ringEffort_gradient`, from
   `hasDerivAt_alignCost`), and along any motion the store's energy moves at `−Σ_c effort_c ẏ_c`
   (`hasDerivAt_alignCost_path`). (b) Through a resistive contact (the ring overdamped,
   `ẏ = γ · effort`, `γ > 0`) the gap relaxes as `Δ_c(t) = Δ_c(0) e^(−γ q_c t/4)` (`ringRelax`,
   `ringRelax_zero`, `phaseGap_ringRelax`, `hasDerivAt_ringRelax`); the energy falls at
   `−γ Σ effort²` (`ring_energy_rate`) and tends to `0` (`ring_energy_tendsto`); the heat dissipated
   from `0` to `t` (`ringHeat`) is the energy's drop (`ringHeat_eq`) and tends to the initial
   `alignCost` (`ringHeat_tendsto`): the phase face's free relaxation. (c) A common whole winding
   leaves the port's energy and every effort (`ring_winding`, through `phaseGap_winding`).
4. **`R⁻¹dR` at the two ports.** The lifted log ratio has modulus face `Re ℓᵢ = ½ log(qᵢ/pᵢ)` and
   phase face `Im ℓᵢ = θTᵢ − θHᵢ` (`logRatio_re`, `logRatio_im`): the thermal port's matched effort is
   `2θ Re ℓᵢ` (`effort_eq_logRatio_re`) and the ring port's gap is `Im ℓᵢ` at `θH = y/2`
   (`logRatio_im_eq_phaseGap`), so `ℓᵢ = effortᵢ/(2θ) + i Δᵢ` (`logRatio_split`). Read by the
   population, the modulus face gives `−D(p‖q)`, and `θ` times it is the matched quench work; read by
   the target it gives `D(q‖p)`, the code face of the owner's lifted excess (`modulus_face_readings`).
   Along a produced motion `(s, φ)` the owner's `ratioCovector` is `R⁻¹dR` and drives both ports: the
   thermal flow is `ṗᵢ = −2pᵢ Re(R⁻¹dR)ᵢ`, the ring flow `ẏ_c = −2 Im(R⁻¹dR)_c`, and the thermal store
   `θ D(p‖q)` and the ring store `alignCost` each move at minus its effort paired with its flow
   (`covector_drives_ports`). The returns: the matched shift extracts `θ D(p‖q)` reversibly (the
   owner's `extracted_work`, `reversible_production_zero`), the ring port dissipates `alignCost`
   through a resistive contact, and the two returns add (`two_ports_return`).
5. **Witnesses.** The two-level port `E = δ = (0, 1)` at `θ = 1` has
   `restoreWork = log(1 + e⁻²) − log(1 + e⁻¹)` (`twoLevel_restoreWork`); its leg produces at most
   `1/8` at `N = 1` and at most `1/80` at `N = 10`, and the ten-step work exceeds `restoreWork` by the
   ten-step production (`twoLevel_witness`). One ring channel relaxing from `Δ = 1` has gap
   `e^(−t/4)`, holds `1/2`, and dissipates heat tending to `1/2` (`ring_witness`).

[counterexample; formal-checked] **The lifted face determines no ring return.** Against the uniform
target with zero phases, a ring turned to `y = (2, −2)` and an aligned ring return one lifted
cross-entropy, code and phase faces both, yet store `alignCost` `1/2` and `0`
(`lifted_face_determines_no_ring_return`); the owner's `equal_face_different_effort` is the same
obstruction for the thermal effort.

What is not claimed. A continuum (measure) transport of the aperture on `ℝ` with Reynolds' theorem:
the moving support here is a finite set of cells with edge fluxes and one-sided entrances. The Rust
consumer `physics::information::apply` itself. A quantum (unitary) phase port: the ring port is a
classical torsional store with a resistive contact. The HNN's grain chart of the covector
(`HNN/Ratio` items 5 and 6): every statement here is on real logits. The thermal port's protocol on a
moving support: its states are canonical and fully supported, so 2(c) and 2(d) are stated on
populations and references, not on the port's legs. The ring's overdamped flow is a continuous
resistive contact, not the HNN's discrete phase step. The bound `(b − a)²/(8Nθ²)` is not claimed
sharp, and the leading coefficient of the leg's production in `1/N` is not derived.

The computational object is the helical pair interaction, read here as the pair contact of the
produced and the target Holon: its ratio `R = Ĝ_(T←H)`, channel by channel, carries a modulus face
that reaches a thermal port as a level shift (a slip that produces `D` when quenched off its match,
and none when matched or when the restoring leg is cut into many small steps) and a phase face that
twists a ring against a torsional store (a slip that a resistive contact dissipates as heat). Of the
winding guide's six general objects this touches the helix (the ring's whole winding, the log's
branch, which cancels), the pair (the ratio of two Holons, and the flux on an edge between two
cells), faces and placement (the canonical faces, and a support whose cells empty and fill) and the
tube (the restoring leg as a clocked span of `N` quench-and-relax steps); cell holonomy and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.InformationPort

open Filter Topology
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Holonics.Computation.HolonicAdjointNormalization (NormalizedExponential.face)
open Holonics.Foundation.HolonicMembraneActionTransport (finiteCrossEntropy)
open Holonics.Physics.InformationDifference
open Holonics.Physics.Information.PortWork
open Holonics.Objects.Ratio (logRatio liftedLog amplitude)
open Holonics.Objects.RatioPhase (alignCost phaseGap hasDerivAt_alignCost phaseGap_winding
  ratioCovector)

variable {ι : Type*} [Fintype ι]

/-! ## 1. The finite-step quasi-static limit -/

section QuasiStatic

/-- [definition] The levels after `k` of the restoring leg's `N` steps, `E_k = E + (1 − k/N)δ`. -/
def legLevel (E δ : ι → ℝ) (N k : ℕ) : ι → ℝ := fun i => E i + (1 - (k : ℝ) / N) * δ i

/-- [definition] The shift of step `k`, `E_(k+1) − E_k`. -/
def stepShift (E δ : ι → ℝ) (N k : ℕ) : ι → ℝ :=
  fun i => legLevel E δ N (k + 1) i - legLevel E δ N k i

variable [Nonempty ι]

/-- [definition] The canonical state of the levels after `k` steps, `q_k`. -/
def legState (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) : PositiveProbabilitySection ι :=
  canonicalState θ (legLevel E δ N k)

/-- [definition] Step `k`'s quench work, `⟨E_(k+1) − E_k⟩_(q_k)`: the owner's `quenchWork`. -/
def stepWork (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) : ℝ :=
  quenchWork (stepShift E δ N k) (legState θ E δ N k)

/-- [definition] Step `k`'s relaxation heat at `E_(k+1)`: the owner's `relaxHeat`. -/
def stepHeat (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) : ℝ :=
  relaxHeat θ (legLevel E δ N k) (stepShift E δ N k) (legState θ E δ N k)

/-- [definition] Step `k`'s production: free relaxation at `E_(k+1)` from `q_k` to `q_(k+1)`. -/
def stepProduction (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) : ℝ :=
  freeProduction θ (legLevel E δ N (k + 1)) (legState θ E δ N k) (legState θ E δ N (k + 1))

/-- [definition] The leg's work over its `N` steps. -/
def legWork (θ : ℝ) (E δ : ι → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, stepWork θ E δ N k

/-- [definition] The leg's heat over its `N` steps. -/
def legHeat (θ : ℝ) (E δ : ι → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, stepHeat θ E δ N k

/-- [definition] The leg's production over its `N` steps. -/
def legProduction (θ : ℝ) (E δ : ι → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, stepProduction θ E δ N k

omit [Fintype ι] [Nonempty ι] in
/-- [proved-derived; formal-checked] Step `k`'s shift carries `E_k` to `E_(k+1)`. -/
theorem shifted_stepShift (E δ : ι → ℝ) (N k : ℕ) :
    shifted (legLevel E δ N k) (stepShift E δ N k) = legLevel E δ N (k + 1) := by
  funext i
  simp [shifted, stepShift]

omit [Fintype ι] [Nonempty ι] in
/-- [proved-derived; formal-checked] Each of `N ≠ 0` steps shifts the levels by `−δ/N`. -/
theorem stepShift_eq {N : ℕ} (hN : N ≠ 0) (E δ : ι → ℝ) (k : ℕ) :
    stepShift E δ N k = fun i => -(δ i / N) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  funext i
  simp only [stepShift, legLevel]
  push_cast
  field_simp
  ring

omit [Fintype ι] [Nonempty ι] in
/-- [proved-derived; formal-checked] The leg starts at the shifted levels `E + δ`. -/
theorem legLevel_zero (E δ : ι → ℝ) (N : ℕ) : legLevel E δ N 0 = shifted E δ := by
  funext i
  simp [legLevel, shifted]

omit [Fintype ι] [Nonempty ι] in
/-- [proved-derived; formal-checked] After `N ≠ 0` steps the leg stands at `E`. -/
theorem legLevel_last {N : ℕ} (hN : N ≠ 0) (E δ : ι → ℝ) : legLevel E δ N N = E := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  funext i
  simp [legLevel, div_self hN']

/-- [proved-derived; formal-checked] Step `k` relaxes to `q_(k+1)`: the owner's `relaxed` state. -/
theorem relaxed_step (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) :
    relaxed θ (legLevel E δ N k) (stepShift E δ N k) = legState θ E δ N (k + 1) := by
  rw [relaxed, shifted_stepShift]
  rfl

/-- [proved-derived; formal-checked] **Each step produces `D(q_k‖q_(k+1))`**: the owner's
`free_relaxation_production` at `E_(k+1)`. -/
theorem stepProduction_eq {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) (N k : ℕ) :
    stepProduction θ E δ N k = klDivergence (legState θ E δ N k) (legState θ E δ N (k + 1)) :=
  free_relaxation_production hθ (canonicalState_canonical hθ _)

/-- [proved-derived; formal-checked] **A step's production is its entropy change less its heat
over `θ`**, the owner's `restoreProduction` read on one step. -/
theorem stepProduction_heat (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) :
    stepProduction θ E δ N k = (entropy (legState θ E δ N (k + 1)) - entropy (legState θ E δ N k)) -
      stepHeat θ E δ N k / θ := by
  unfold stepProduction stepHeat freeProduction relaxHeat
  rw [relaxed_step, shifted_stepShift]

/-- [proved-derived; formal-checked] **A step's first law**: its work and heat are the energy
change from `(E_k, q_k)` to `(E_(k+1), q_(k+1))`. -/
theorem step_first_law (θ : ℝ) (E δ : ι → ℝ) (N k : ℕ) :
    stepWork θ E δ N k + stepHeat θ E δ N k =
      energyExpectation (legLevel E δ N (k + 1)) (legState θ E δ N (k + 1)) -
        energyExpectation (legLevel E δ N k) (legState θ E δ N k) := by
  have hq : energyExpectation (legLevel E δ N (k + 1)) (legState θ E δ N k) =
      energyExpectation (legLevel E δ N k) (legState θ E δ N k) + stepWork θ E δ N k := by
    simp only [energyExpectation, stepWork, quenchWork, stepShift, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold stepHeat relaxHeat
  rw [relaxed_step, shifted_stepShift]
  linarith

/-- [proved-derived; formal-checked] **A step's work is its drop in `θ log Z` plus `θ` times its
production**, from the owner's `extracted_work_general` with the population canonical. -/
theorem stepWork_eq {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) (N k : ℕ) :
    stepWork θ E δ N k =
      θ * Real.log (partition θ (legLevel E δ N k)) -
        θ * Real.log (partition θ (legLevel E δ N (k + 1))) +
        θ * klDivergence (legState θ E δ N k) (legState θ E δ N (k + 1)) := by
  have h := extracted_work_general hθ (canonicalState_canonical hθ (legLevel E δ N k))
    (p := legState θ E δ N k) (stepShift E δ N k)
  have h0 : freeEnergy θ (legLevel E δ N k) (legState θ E δ N k) -
      freeEnergy θ (legLevel E δ N k) (canonicalState θ (legLevel E δ N k)) = 0 := sub_self _
  rw [relaxed_step, h0, zero_sub] at h
  unfold restoreWork at h
  rw [shifted_stepShift] at h
  unfold stepWork
  linarith

/-- [proved-derived; formal-checked] **The discrete second law of the leg**: its work is the
owner's `restoreWork` plus `θ` times its production `Σ_k D(q_k‖q_(k+1))`. -/
theorem legWork_eq {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) {N : ℕ} (hN : N ≠ 0) :
    legWork θ E δ N = restoreWork θ E δ + θ * legProduction θ E δ N := by
  unfold legWork legProduction
  simp only [stepWork_eq hθ, stepProduction_eq hθ, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_range_sub' (fun k => θ * Real.log (partition θ (legLevel E δ N k))),
    legLevel_zero, legLevel_last hN]
  rfl

/-- [proved-derived; formal-checked] **The leg's production is its entropy change less its heat
over `θ`**, the `N`-step form of the owner's `restoreProduction`. -/
theorem legProduction_heat (θ : ℝ) (E δ : ι → ℝ) {N : ℕ} (hN : N ≠ 0) :
    legProduction θ E δ N =
      (entropy (canonicalState θ E) - entropy (relaxed θ E δ)) - legHeat θ E δ N / θ := by
  unfold legProduction legHeat
  simp only [stepProduction_heat]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => entropy (legState θ E δ N k)),
    ← Finset.sum_div]
  simp only [legState, legLevel_zero, legLevel_last hN]
  rfl

/-- [proved-derived; formal-checked] **The leg's first law**: its work and heat are the energy
change from the relaxed state at `E + δ` to the canonical state of `E`. -/
theorem leg_first_law (θ : ℝ) (E δ : ι → ℝ) {N : ℕ} (hN : N ≠ 0) :
    legWork θ E δ N + legHeat θ E δ N =
      energyExpectation E (canonicalState θ E) -
        energyExpectation (shifted E δ) (relaxed θ E δ) := by
  unfold legWork legHeat
  rw [← Finset.sum_add_distrib]
  simp only [step_first_law]
  rw [Finset.sum_range_sub (fun k => energyExpectation (legLevel E δ N k) (legState θ E δ N k))]
  simp only [legState, legLevel_zero, legLevel_last hN]
  rfl

/-- [proved-derived; formal-checked] **The leg's heat is the owner's `restoreHeat` less `θ` times
its production.** -/
theorem legHeat_eq {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) {N : ℕ} (hN : N ≠ 0) :
    legHeat θ E δ N = restoreHeat θ E δ - θ * legProduction θ E δ N := by
  have h₁ := leg_first_law θ E δ hN
  have h₂ := legWork_eq hθ E δ hN
  unfold restoreHeat
  linarith

/-- [proved-standard; formal-checked] **One step's bound.** For `θ > 0` and a level shift `η` in
`[a, b]`, `D(canonical E ‖ canonical (E + η)) ≤ ((b − a)/θ)²/8`: Hoeffding's lemma on the owner's
face (`HNN/Ratio/Resolution.klDivergence_face_shift_le`). -/
theorem kl_canonical_shift_le {θ : ℝ} (hθ : 0 < θ) (E η : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ η i)
    (hb : ∀ i, η i ≤ b) :
    klDivergence (canonicalState θ E) (canonicalState θ (fun i => E i + η i)) ≤
      ((b - a) / θ) ^ 2 / 8 := by
  rw [canonicalState_eq_face, canonicalState_eq_face]
  have hsplit : (fun i => -(E i + η i) / θ) = (fun i => -E i / θ) + fun i => -η i / θ := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [hsplit]
  refine (Holonics.HNN.Ratio.Resolution.klDivergence_face_shift_le _ _ (a := -b / θ)
    (b := -a / θ) (fun i => ?_) (fun i => ?_)).trans_eq ?_
  · exact div_le_div_of_nonneg_right (neg_le_neg (hb i)) hθ.le
  · exact div_le_div_of_nonneg_right (neg_le_neg (ha i)) hθ.le
  · ring

/-- [proved-standard; formal-checked] **One step's bound, quadratic in the shift**: `|ηᵢ| ≤ M`
gives `D ≤ (M/θ)²/2`. -/
theorem kl_canonical_shift_le_abs {θ : ℝ} (hθ : 0 < θ) (E η : ι → ℝ) {M : ℝ}
    (hM : ∀ i, |η i| ≤ M) :
    klDivergence (canonicalState θ E) (canonicalState θ (fun i => E i + η i)) ≤ (M / θ) ^ 2 / 2 :=
  (kl_canonical_shift_le hθ E η (a := -M) (b := M) (fun i => (abs_le.mp (hM i)).1)
    (fun i => (abs_le.mp (hM i)).2)).trans_eq (by ring)

/-- [proved-derived; formal-checked] **Each of the `N` steps produces at most
`((b − a)/(Nθ))²/8`** when the leg's shift lies in `[a, b]`. -/
theorem stepProduction_le {θ : ℝ} (hθ : 0 < θ) (E δ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ δ i)
    (hb : ∀ i, δ i ≤ b) {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    stepProduction θ E δ N k ≤ ((b - a) / (N * θ)) ^ 2 / 8 := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hnext : legLevel E δ N (k + 1) = fun i => legLevel E δ N k i + -(δ i / N) := by
    funext i
    have h := congrFun (stepShift_eq hN E δ k) i
    simp only [stepShift] at h
    linarith
  rw [stepProduction_eq hθ.ne', legState, legState, hnext]
  refine (kl_canonical_shift_le hθ _ _ (a := -b / N) (b := -a / N) (fun i => ?_)
    (fun i => ?_)).trans_eq ?_
  · rw [neg_div]; exact neg_le_neg (div_le_div_of_nonneg_right (hb i) hN'.le)
  · rw [neg_div]; exact neg_le_neg (div_le_div_of_nonneg_right (ha i) hN'.le)
  · field_simp
    ring

/-- [proved-derived; formal-checked] **The leg's production is at most `(b − a)²/(8Nθ²)`.** -/
theorem legProduction_le {θ : ℝ} (hθ : 0 < θ) (E δ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ δ i)
    (hb : ∀ i, δ i ≤ b) {N : ℕ} (hN : N ≠ 0) :
    legProduction θ E δ N ≤ (b - a) ^ 2 / (8 * N * θ ^ 2) := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc legProduction θ E δ N ≤ ∑ _k ∈ Finset.range N, ((b - a) / (N * θ)) ^ 2 / 8 :=
        Finset.sum_le_sum fun k _ => stepProduction_le hθ E δ ha hb hN k
    _ = (b - a) ^ 2 / (8 * N * θ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- [proved-derived; formal-checked] The leg's production is nonnegative. -/
theorem legProduction_nonneg {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) (N : ℕ) :
    0 ≤ legProduction θ E δ N :=
  Finset.sum_nonneg fun k _ => by
    rw [stepProduction_eq hθ]
    exact klDivergence_nonnegative _ _

omit [Nonempty ι] in
/-- [proved-standard; formal-checked] A coordinate is bounded by the sum of absolute values. -/
theorem abs_le_sum_abs (δ : ι → ℝ) (i : ι) : |δ i| ≤ ∑ j, |δ j| :=
  Finset.single_le_sum (f := fun j => |δ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- [proved-derived; formal-checked] **The finite-step quasi-static limit**: the leg's production
`Σ_k D(q_k‖q_(k+1))` tends to `0` as `N → ∞`, the owner's zero `restoreProduction`. -/
theorem legProduction_tendsto {θ : ℝ} (hθ : 0 < θ) (E δ : ι → ℝ) :
    Tendsto (legProduction θ E δ) atTop (𝓝 (restoreProduction θ E δ)) := by
  rw [restore_production_zero hθ.ne']
  set M := ∑ j, |δ j|
  have hup : Tendsto (fun N : ℕ => ((M - -M) ^ 2 / (8 * θ ^ 2)) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun N => legProduction_nonneg hθ.ne' E δ N) ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  refine (legProduction_le hθ E δ (a := -M) (b := M) (fun i => (abs_le.mp (abs_le_sum_abs δ i)).1)
    (fun i => (abs_le.mp (abs_le_sum_abs δ i)).2) hN).trans_eq ?_
  rw [div_div]
  ring

/-- [proved-derived; formal-checked] **The leg's work tends to the quasi-static work** `restoreWork`,
and never falls below it at `θ > 0`. -/
theorem legWork_tendsto {θ : ℝ} (hθ : 0 < θ) (E δ : ι → ℝ) :
    Tendsto (legWork θ E δ) atTop (𝓝 (restoreWork θ E δ)) ∧
      ∀ N : ℕ, N ≠ 0 → restoreWork θ E δ ≤ legWork θ E δ N := by
  have hP := legProduction_tendsto hθ E δ
  rw [restore_production_zero hθ.ne'] at hP
  refine ⟨?_, fun N hN => ?_⟩
  · have h := (hP.const_mul θ).const_add (restoreWork θ E δ)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (legWork_eq hθ.ne' E δ hN).symm
  · rw [legWork_eq hθ.ne' E δ hN]
    have := mul_nonneg hθ.le (legProduction_nonneg hθ.ne' E δ N)
    linarith

/-- [proved-derived; formal-checked] **The leg's heat tends to the owner's `restoreHeat`.** -/
theorem legHeat_tendsto {θ : ℝ} (hθ : 0 < θ) (E δ : ι → ℝ) :
    Tendsto (legHeat θ E δ) atTop (𝓝 (restoreHeat θ E δ)) := by
  have hP := legProduction_tendsto hθ E δ
  rw [restore_production_zero hθ.ne'] at hP
  have h := (hP.const_mul θ).const_sub (restoreHeat θ E δ)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact (legHeat_eq hθ.ne' E δ hN).symm

end QuasiStatic

/-! ## 2. A moving support -/

section MovingSupport

/-- [definition] **The rate a flux on edges gives a population**, `ṗᵢ = Σⱼ (J_ji − J_ij)`:
`J i j` is the mass moved from `i` to `j` a unit of the clock. -/
def edgeRate (J : ι → ι → ℝ) (i : ι) : ℝ := ∑ j, (J j i - J i j)

/-- [proved-derived; formal-checked] **Transport on edges keeps the total**: `Σ ṗ = 0`. -/
theorem sum_edgeRate (J : ι → ι → ℝ) : ∑ i, edgeRate J i = 0 := by
  simp only [edgeRate, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  exact sub_self _

/-- [proved-derived; formal-checked] **A unit moved from `i` to `j` costs `log(qᵢ/qⱼ)`**: against a
positive reference the population term of the rate is `−Σ ṗᵢ log qᵢ = Σ_(i,j) J_ij log(qᵢ/qⱼ)`. -/
theorem edgeRate_population_term (J : ι → ι → ℝ) (q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    -∑ i, edgeRate J i * Real.log (q i) = ∑ i, ∑ j, J i j * Real.log (q i / q j) := by
  simp only [edgeRate, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib,
    Real.log_div (hq _).ne' (hq _).ne', mul_sub]
  rw [Finset.sum_comm (f := fun i j => J j i * Real.log (q i))]
  ring

/-- [proved-derived; formal-checked] **The cross-entropy's rate under transport on edges**: a
population moved by `J` against a fixed positive reference changes its cross-entropy at
`Σ_(i,j) J_ij log(qᵢ/qⱼ)` (the owner's `FirstLaw.hasDerivAt_crossEntropy` with `q̇ = 0`). -/
theorem hasDerivAt_crossEntropy_edges (p : ℝ → ι → ℝ) (J : ι → ι → ℝ) (q : ι → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun s => p s i) (edgeRate J i) t) (hq : ∀ i, 0 < q i) :
    HasDerivAt (fun s => finiteCrossEntropy (p s) q)
      (∑ i, ∑ j, J i j * Real.log (q i / q j)) t := by
  have h := Holonics.Aeon.Production.FirstLaw.hasDerivAt_crossEntropy (q := fun _ => q)
    (dq := fun _ => 0) hp (fun _ => hasDerivAt_const t _) hq
  refine h.congr_deriv ?_
  rw [← edgeRate_population_term J q hq]
  simp

/-- [proved-derived; formal-checked] **A moving support keeps the two-sided rate, and an empty cell
moves at rate `0`.** No positivity is asked of the population: with nonnegative masses (a cell may
be empty) the cross-entropy against a positive reference moves at `−Σ ṗ log q − Σ p q̇/q`, and at a
cell that is empty at `t` a two-sided rate is `0` (an empty cell is a minimum), so an entrance at a
nonzero rate is one-sided. -/
theorem moving_support_rate (p q : ℝ → ι → ℝ) (dp dq : ι → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun s => p s i) (dp i) t)
    (hq : ∀ i, HasDerivAt (fun s => q s i) (dq i) t) (hqpos : ∀ i, 0 < q t i)
    (hnn : ∀ s i, 0 ≤ p s i) :
    HasDerivAt (fun s => finiteCrossEntropy (p s) (q s))
        (-∑ i, dp i * Real.log (q t i) - ∑ i, p t i * (dq i / q t i)) t ∧
      ∀ i, p t i = 0 → dp i = 0 := by
  refine ⟨(Holonics.Aeon.Production.FirstLaw.hasDerivAt_crossEntropy hp hq hqpos).congr_deriv
    (by ring), fun i hi => ?_⟩
  have hmin : IsLocalMin (fun s => p s i) t :=
    Eventually.of_forall fun s => by simp only [hi]; exact hnn s i
  exact hmin.hasDerivAt_eq_zero (hp i)

/-- [definition] The relative entropy's term of one cell, `x log(x/y)`. -/
def relTerm (x y : ℝ) : ℝ := x * Real.log (x / y)

/-- [definition] The entropy's term of one cell, `−x log x`. -/
def entTerm (x : ℝ) : ℝ := -(x * Real.log x)

/-- [definition] The cross-entropy's term of one cell, `−x log y`. -/
def crossTerm (x y : ℝ) : ℝ := -(x * Real.log y)

/-- [proved-standard; formal-checked] **At an entrance the relative entropy's term moves at `−∞`**:
a mass entering at rate `r > 0` from zero (`p(t) = r t`, `t ≥ 0`) against `q > 0` gives
`p log(p/q)` a right difference quotient tending to `−∞` at `0`. -/
theorem entrance_relTerm {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    Tendsto (fun h => (relTerm (r * h) q - relTerm (r * 0) q) / h) (𝓝[>] 0) atBot := by
  have hlog : Tendsto (fun h => r * Real.log (r / q) + r * Real.log h) (𝓝[>] 0) atBot :=
    tendsto_atBot_add_const_left _ _ (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hr)
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  simp only [relTerm, mul_zero, zero_mul, sub_zero]
  rw [mul_div_right_comm, Real.log_div (mul_pos hr hh).ne' hq.ne',
    Real.log_mul hr.ne' hh.ne', Real.log_div hr.ne' hq.ne']
  field_simp
  ring

/-- [proved-standard; formal-checked] **At an entrance the entropy's term moves at `+∞`.** -/
theorem entrance_entTerm {r : ℝ} (hr : 0 < r) :
    Tendsto (fun h => (entTerm (r * h) - entTerm (r * 0)) / h) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun h => -(r * Real.log r + r * Real.log h)) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp
      (tendsto_atBot_add_const_left _ _ (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hr))
  refine hlog.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  simp only [entTerm, mul_zero, zero_mul, neg_zero, sub_zero]
  rw [Real.log_mul hr.ne' hh.ne']
  field_simp

/-- [proved-standard; formal-checked] **At an entrance the cross-entropy's term moves at the finite
rate `−r log q`**, one-sided from the right. -/
theorem entrance_crossTerm (r q : ℝ) :
    HasDerivWithinAt (fun h => crossTerm (r * h) q) (-(r * Real.log q)) (Set.Ici 0) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul r).mul_const (Real.log q) |>.neg
  refine (h.congr_deriv (by simp)).hasDerivWithinAt.congr_of_mem ?_ Set.self_mem_Ici
  · intro x _
    simp [crossTerm]

/-- [proved-derived; formal-checked] **A reference cannot leave a populated cell at finite code**:
if a cell's population stays at least `c > 0` while the reference's mass there tends to `0⁺`, the
cross-entropy tends to `+∞`. -/
theorem crossEntropy_tendsto_atTop {α : Type*} {l : Filter α} (p : α → ι → ℝ)
    (q : α → PositiveProbabilitySection ι) (i : ι) {c : ℝ} (hc : 0 < c)
    (hnn : ∀ s j, 0 ≤ p s j) (hpi : ∀ s, c ≤ p s i)
    (hq : Tendsto (fun s => (q s).mass i) l (𝓝[>] 0)) :
    Tendsto (fun s => finiteCrossEntropy (p s) (q s).mass) l atTop := by
  have hle1 : ∀ s j, (q s).mass j ≤ 1 := fun s j => by
    rw [← (q s).normalized]
    exact Finset.single_le_sum (f := (q s).mass) (fun k _ => (q s).nonnegative k)
      (Finset.mem_univ j)
  have hlog0 : ∀ s j, Real.log ((q s).mass j) ≤ 0 := fun s j =>
    Real.log_nonpos ((q s).nonnegative j) (hle1 s j)
  have hlim : Tendsto (fun s => c * -Real.log ((q s).mass i)) l atTop :=
    (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hq)).const_mul_atTop hc
  refine tendsto_atTop_mono (fun s => ?_) hlim
  have hterm : ∀ j, 0 ≤ -(p s j * Real.log ((q s).mass j)) := fun j => by
    have := mul_nonpos_of_nonneg_of_nonpos (hnn s j) (hlog0 s j)
    linarith
  have hsingle := Finset.single_le_sum (f := fun j => -(p s j * Real.log ((q s).mass j)))
    (fun j _ => hterm j) (Finset.mem_univ i)
  have hci : c * -Real.log ((q s).mass i) ≤ -(p s i * Real.log ((q s).mass i)) := by
    have := mul_le_mul_of_nonneg_right (hpi s) (neg_nonneg.mpr (hlog0 s i))
    linarith
  simp only [finiteCrossEntropy, ← Finset.sum_neg_distrib]
  exact hci.trans hsingle

/-- [proved-derived; formal-checked] **The relative entropy moves at `−∞` from an entrance.** A
population entering cell `i₀` at rate `r > 0` from zero, every other cell populated at `0` with a
right rate, against a fixed positive reference: `D(p‖q) = Σ p log(p/q)` has a right difference
quotient tending to `−∞` at `0`. -/
theorem entrance_relativeEntropy [DecidableEq ι] (p : ℝ → ι → ℝ) (q dp : ι → ℝ) (i₀ : ι) {r : ℝ}
    (hr : 0 < r) (hq : ∀ j, 0 < q j) (hent : ∀ h, 0 ≤ h → p h i₀ = r * h)
    (hpos : ∀ j, j ≠ i₀ → 0 < p 0 j)
    (hp : ∀ j, j ≠ i₀ → HasDerivWithinAt (fun s => p s j) (dp j) (Set.Ici 0) 0) :
    Tendsto (fun h => (∑ j, relTerm (p h j) (q j) - ∑ j, relTerm (p 0 j) (q j)) / h) (𝓝[>] 0)
      atBot := by
  have hsplit : ∀ h, (∑ j, relTerm (p h j) (q j) - ∑ j, relTerm (p 0 j) (q j)) / h =
      (relTerm (p h i₀) (q i₀) - relTerm (p 0 i₀) (q i₀)) / h +
        ∑ j ∈ ({i₀}ᶜ : Finset ι), (relTerm (p h j) (q j) - relTerm (p 0 j) (q j)) / h := by
    intro h
    rw [← Finset.sum_sub_distrib, Finset.sum_div,
      Fintype.sum_eq_add_sum_compl i₀ (fun j => (relTerm (p h j) (q j) - relTerm (p 0 j) (q j)) / h)]
  simp only [hsplit]
  have hfirst : Tendsto (fun h => (relTerm (p h i₀) (q i₀) - relTerm (p 0 i₀) (q i₀)) / h) (𝓝[>] 0)
      atBot := by
    refine (entrance_relTerm hr (hq i₀)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    rw [hent h hh.le, hent 0 le_rfl]
  refine hfirst.atBot_add (tendsto_finsetSum (a := fun j =>
    dp j * Real.log (p 0 j / q j) + p 0 j * ((dp j / q j) / (p 0 j / q j))) _ fun j hj => ?_)
  have hj' : j ≠ i₀ := by simpa using hj
  have hd : HasDerivWithinAt (fun s => relTerm (p s j) (q j))
      (dp j * Real.log (p 0 j / q j) + p 0 j * ((dp j / q j) / (p 0 j / q j))) (Set.Ici 0) 0 :=
    (hp j hj').mul (((hp j hj').div_const (q j)).log (div_pos (hpos j hj') (hq j)).ne')
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Set.Ici_sdiff_left] at hs
  refine hs.congr' (Eventually.of_forall fun h => ?_)
  simp only [slope_def_field, sub_zero]

end MovingSupport

/-! ## 3. The phase-face port: a ring held by a torsional store -/

section RingPort

/-- [definition] **The ring port's effort** on channel `c`, `½ q_c Δ_c`: the torque the torsional
store of stiffness `q_c` exerts on the ring at angle `y_c`. -/
def ringEffort (q φT y : ι → ℝ) (c : ι) : ℝ := (1 / 2) * q c * phaseGap φT y c

/-- [proved-derived; formal-checked] **The effort is minus the store's gradient**: the owner's
`hasDerivAt_alignCost` along `y_c`. -/
theorem ringEffort_gradient [DecidableEq ι] (q φT y : ι → ℝ) (c : ι) :
    HasDerivAt (fun t => alignCost q φT (fun i => y i + t * (Pi.single c (1 : ℝ) : ι → ℝ) i))
      (-ringEffort q φT y c) 0 :=
  (hasDerivAt_alignCost q φT y c).congr_deriv (by unfold ringEffort; ring)

/-- [proved-derived; formal-checked] **The ring port's power balance**: along any motion `y(t)` the
store's energy moves at minus the effort paired with `ẏ`, `d/dt alignCost = −Σ_c effort_c ẏ_c`. -/
theorem hasDerivAt_alignCost_path (q φT : ι → ℝ) (y : ℝ → ι → ℝ) (v : ι → ℝ) (t : ℝ)
    (hy : ∀ c, HasDerivAt (fun s => y s c) (v c) t) :
    HasDerivAt (fun s => alignCost q φT (y s)) (-∑ c, ringEffort q φT (y t) c * v c) t := by
  have hterm : ∀ c ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun s => q c * phaseGap φT (y s) c ^ 2)
        (q c * (2 * phaseGap φT (y t) c * (-(v c) / 2))) t := by
    intro c _
    have hgap : HasDerivAt (fun s => phaseGap φT (y s) c) (-(v c) / 2) t := by
      unfold phaseGap
      exact ((hy c).div_const 2).const_sub (φT c) |>.congr_deriv (by ring)
    exact ((hgap.pow 2).const_mul (q c)).congr_deriv (by push_cast; ring)
  refine ((HasDerivAt.fun_sum hterm).const_mul (1 / 2 : ℝ)).congr_deriv ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun c _ => by unfold ringEffort; ring

/-- [definition] **The overdamped ring's motion** from `y₀`, through a resistive contact of
conductance `γ`: `y_c(t) = 2(φT_c − Δ_c(0) e^(−γ q_c t/4))`. -/
def ringRelax (q φT y₀ : ι → ℝ) (γ t : ℝ) : ι → ℝ :=
  fun c => 2 * (φT c - phaseGap φT y₀ c * Real.exp (-(γ * q c * t) / 4))

omit [Fintype ι] in
/-- [proved-derived; formal-checked] The overdamped ring starts at `y₀`. -/
theorem ringRelax_zero (q φT y₀ : ι → ℝ) (γ : ℝ) : ringRelax q φT y₀ γ 0 = y₀ := by
  funext c
  simp only [ringRelax, phaseGap, mul_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

omit [Fintype ι] in
/-- [proved-derived; formal-checked] **The gap relaxes geometrically**,
`Δ_c(t) = Δ_c(0) e^(−γ q_c t/4)`. -/
theorem phaseGap_ringRelax (q φT y₀ : ι → ℝ) (γ t : ℝ) (c : ι) :
    phaseGap φT (ringRelax q φT y₀ γ t) c = phaseGap φT y₀ c * Real.exp (-(γ * q c * t) / 4) := by
  change φT c - 2 * (φT c - phaseGap φT y₀ c * Real.exp (-(γ * q c * t) / 4)) / 2 = _
  ring

omit [Fintype ι] in
/-- [proved-derived; formal-checked] **The overdamped ring solves `ẏ = γ · effort`.** -/
theorem hasDerivAt_ringRelax (q φT y₀ : ι → ℝ) (γ t : ℝ) (c : ι) :
    HasDerivAt (fun s => ringRelax q φT y₀ γ s c) (γ * ringEffort q φT (ringRelax q φT y₀ γ t) c) t := by
  have hlin : HasDerivAt (fun s => -(γ * q c * s) / 4) (-(γ * q c) / 4) t := by
    have := (((hasDerivAt_id t).const_mul (γ * q c)).neg).div_const 4
    exact this.congr_deriv (by ring)
  have h := ((hlin.exp.const_mul (phaseGap φT y₀ c)).const_sub (φT c)).const_mul 2
  refine h.congr_deriv ?_
  rw [ringEffort, phaseGap_ringRelax]
  ring

/-- [proved-derived; formal-checked] **The overdamped ring dissipates**: its store's energy falls at
`−γ Σ_c effort_c²`. -/
theorem ring_energy_rate (q φT y₀ : ι → ℝ) (γ t : ℝ) :
    HasDerivAt (fun s => alignCost q φT (ringRelax q φT y₀ γ s))
      (-(γ * ∑ c, ringEffort q φT (ringRelax q φT y₀ γ t) c ^ 2)) t := by
  refine (hasDerivAt_alignCost_path q φT _ _ t fun c => hasDerivAt_ringRelax q φT y₀ γ t c)
    |>.congr_deriv ?_
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

/-- [proved-derived; formal-checked] **The overdamped ring's energy tends to `0`** for `γ > 0` and
positive stiffnesses. -/
theorem ring_energy_tendsto (q φT y₀ : ι → ℝ) {γ : ℝ} (hγ : 0 < γ) (hq : ∀ c, 0 < q c) :
    Tendsto (fun t => alignCost q φT (ringRelax q φT y₀ γ t)) atTop (𝓝 0) := by
  have hexp : ∀ c, Tendsto (fun t => Real.exp (-(γ * q c * t) / 4)) atTop (𝓝 0) := fun c => by
    have hk : 0 < γ * q c / 4 := by have := hq c; positivity
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)).congr ?_
    intro t
    simp only [Function.comp, id]
    ring_nf
  have hsum : Tendsto (fun t => (1 / 2 : ℝ) * ∑ c, q c * (phaseGap φT y₀ c *
      Real.exp (-(γ * q c * t) / 4)) ^ 2) atTop (𝓝 ((1 / 2 : ℝ) * ∑ c : ι, q c * (phaseGap φT y₀ c * 0) ^ 2)) :=
    (tendsto_finsetSum _ fun c _ => (((hexp c).const_mul _).pow 2).const_mul _).const_mul _
  simp only [mul_zero, zero_pow two_ne_zero, Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  unfold alignCost
  simp only [phaseGap_ringRelax]

/-- [definition] **The heat the resistive contact dissipates** from `0` to `t`,
`∫₀ᵗ γ Σ_c effort_c² ds`. -/
def ringHeat (q φT y₀ : ι → ℝ) (γ t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, γ * ∑ c, ringEffort q φT (ringRelax q φT y₀ γ s) c ^ 2

/-- [proved-derived; formal-checked] **The heat is the store's energy drop**:
`∫₀ᵗ γ Σ effort² = alignCost(y₀) − alignCost(y(t))`. -/
theorem ringHeat_eq (q φT y₀ : ι → ℝ) (γ t : ℝ) :
    ringHeat q φT y₀ γ t = alignCost q φT y₀ - alignCost q φT (ringRelax q φT y₀ γ t) := by
  have hcont : Continuous fun s => γ * ∑ c, ringEffort q φT (ringRelax q φT y₀ γ s) c ^ 2 := by
    simp only [ringEffort, phaseGap_ringRelax]
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => -alignCost q φT (ringRelax q φT y₀ γ s))
    (fun s _ => (ring_energy_rate q φT y₀ γ s).neg.congr_deriv (neg_neg _))
    (hcont.intervalIntegrable 0 t)
  rw [ringHeat, h, ringRelax_zero]
  ring

/-- [proved-derived; formal-checked] **The phase face's free relaxation**: the heat dissipated
from `0` to `t` tends to the initial `alignCost`. -/
theorem ringHeat_tendsto (q φT y₀ : ι → ℝ) {γ : ℝ} (hγ : 0 < γ) (hq : ∀ c, 0 < q c) :
    Tendsto (fun t => ringHeat q φT y₀ γ t) atTop (𝓝 (alignCost q φT y₀)) := by
  have h := (ring_energy_tendsto q φT y₀ hγ hq).const_sub (alignCost q φT y₀)
  rw [sub_zero] at h
  exact h.congr fun t => (ringHeat_eq q φT y₀ γ t).symm

/-- [proved-derived; formal-checked] **A common whole winding leaves the ring port**: target and
ring wound by `2πn` and `2·2πn` leave the store's energy and every effort (`phaseGap_winding`). -/
theorem ring_winding (q φT y : ι → ℝ) (n : ι → ℤ) :
    alignCost q (fun i => φT i + 2 * Real.pi * n i) (fun i => y i + 2 * (2 * Real.pi * n i)) =
        alignCost q φT y ∧
      ∀ c, ringEffort q (fun i => φT i + 2 * Real.pi * n i)
        (fun i => y i + 2 * (2 * Real.pi * n i)) c = ringEffort q φT y c := by
  refine ⟨?_, fun c => by unfold ringEffort; rw [phaseGap_winding]⟩
  unfold alignCost
  simp only [phaseGap_winding]

end RingPort

/-! ## 4. `R⁻¹dR` at the two ports -/

section Join

/-- [proved-derived; formal-checked] **The modulus face of the lifted log ratio**,
`Re ℓᵢ = ½ log(Tᵢ/Hᵢ)`. -/
theorem logRatio_re (target produced : PositiveProbabilitySection ι) (θT θH : ι → ℝ) (i : ι) :
    (logRatio target produced θT θH i).re = (1 / 2) * Real.log (target.mass i / produced.mass i) := by
  simp only [logRatio, liftedLog, Complex.sub_re]
  rw [Real.log_div (target.ne_zero i) (produced.ne_zero i)]
  ring

/-- [proved-derived; formal-checked] **The phase face of the lifted log ratio**, `Im ℓᵢ = θTᵢ − θHᵢ`. -/
theorem logRatio_im (target produced : PositiveProbabilitySection ι) (θT θH : ι → ℝ) (i : ι) :
    (logRatio target produced θT θH i).im = θT i - θH i := by
  simp only [logRatio, liftedLog, Complex.sub_im]

/-- [proved-derived; formal-checked] **The thermal port's matched effort is `2θ` times the modulus
face**, with the port's canonical reference as the target and its population as the produced. -/
theorem effort_eq_logRatio_re (θ : ℝ) (p q : PositiveProbabilitySection ι) (θT θH : ι → ℝ) (i : ι) :
    effort θ p q i = 2 * θ * (logRatio q p θT θH i).re := by
  rw [logRatio_re, effort]
  ring

/-- [proved-derived; formal-checked] **The ring port's gap is the phase face**, under the convention
`φ^H = y/2`. -/
theorem logRatio_im_eq_phaseGap (q p : PositiveProbabilitySection ι) (φT y : ι → ℝ) (c : ι) :
    (logRatio q p φT (fun i => y i / 2) c).im = phaseGap φT y c := by
  rw [logRatio_im]
  rfl

/-- [proved-derived; formal-checked] **The lifted log ratio splits into the two ports' efforts**:
`ℓᵢ = effortᵢ/(2θ) + i Δᵢ`, the thermal port's level shift and the ring port's gap. -/
theorem logRatio_split {θ : ℝ} (hθ : θ ≠ 0) (p q : PositiveProbabilitySection ι) (φT y : ι → ℝ)
    (i : ι) :
    logRatio q p φT (fun c => y c / 2) i =
      ((effort θ p q i / (2 * θ) : ℝ) : ℂ) + (phaseGap φT y i : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rw [effort_eq_logRatio_re θ p q φT (fun c => y c / 2)]
    field_simp
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    exact logRatio_im_eq_phaseGap q p φT y i

/-- [proved-derived; formal-checked] **The two readings of the modulus face.** Read by the port's
population, `Σ pᵢ 2Re ℓᵢ = −D(p‖q)`, and `θ` times it is the matched quench work; read by the
target, `Σ qᵢ 2Re ℓᵢ = D(q‖p)`, the code face of the owner's `liftedCrossEntropy_excess`. -/
theorem modulus_face_readings (θ : ℝ) (p q : PositiveProbabilitySection ι) (θT θH : ι → ℝ) :
    ∑ i, p.mass i * (2 * (logRatio q p θT θH i).re) = -klDivergence p q ∧
      quenchWork (effort θ p q) p = θ * ∑ i, p.mass i * (2 * (logRatio q p θT θH i).re) ∧
      ∑ i, q.mass i * (2 * (logRatio q p θT θH i).re) = klDivergence q p := by
  have hp : ∑ i, p.mass i * (2 * (logRatio q p θT θH i).re) = -klDivergence p q := by
    rw [klDivergence_eq_logDifference, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logRatio_re, log_ratio]
    ring
  refine ⟨hp, ?_, ?_⟩
  · rw [hp, quenchWork_eq]
    ring
  · unfold klDivergence
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logRatio_re]
    ring

/-- [proved-derived; formal-checked] **`R⁻¹dR` drives the two ports.** Along a produced motion
`(s, φ)` the owner's `ratioCovector` is `R⁻¹dR`; the thermal flow is `ṗᵢ = −2pᵢ Re(R⁻¹dR)ᵢ`, the ring
flow `ẏ_c = −2 Im(R⁻¹dR)_c` (`y = 2φ`), and each store, `θ D(p‖q)` and `alignCost`, moves at minus its
effort paired with its flow. -/
theorem covector_drives_ports [Nonempty ι] (θ : ℝ) (q : PositiveProbabilitySection ι)
    (w φT : ι → ℝ) {s φ : ℝ → ι → ℝ} {ds dφ : ι → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x)
    (hφ : ∀ i, HasDerivAt (fun y => φ y i) (dφ i) x) :
    (∀ i, ∃ R' : ℂ,
      HasDerivAt (fun y => amplitude q φT i / amplitude (NormalizedExponential.face (s y)) (φ y) i)
        R' x ∧
      (amplitude q φT i / amplitude (NormalizedExponential.face (s x)) (φ x) i)⁻¹ * R' =
        ratioCovector (NormalizedExponential.face (s x)) ds dφ i) ∧
    (∀ i, HasDerivAt (fun y => (NormalizedExponential.face (s y)).mass i)
      (-2 * (NormalizedExponential.face (s x)).mass i *
        (ratioCovector (NormalizedExponential.face (s x)) ds dφ i).re) x) ∧
    (∀ c, HasDerivAt (fun y => 2 * φ y c)
      (-2 * (ratioCovector (NormalizedExponential.face (s x)) ds dφ c).im) x) ∧
    HasDerivAt (fun y => θ * klDivergence (NormalizedExponential.face (s y)) q)
      (-∑ i, effort θ (NormalizedExponential.face (s x)) q i *
        (-2 * (NormalizedExponential.face (s x)).mass i *
          (ratioCovector (NormalizedExponential.face (s x)) ds dφ i).re)) x ∧
    HasDerivAt (fun y => alignCost w φT (fun c => 2 * φ y c))
      (-∑ c, ringEffort w φT (fun c => 2 * φ x c) c *
        (-2 * (ratioCovector (NormalizedExponential.face (s x)) ds dφ c).im)) x := by
  set H := NormalizedExponential.face (s x) with hH
  have hflow : ∀ i, HasDerivAt (fun y => (NormalizedExponential.face (s y)).mass i)
      (-2 * H.mass i * (ratioCovector H ds dφ i).re) x := fun i => by
    refine (Holonics.Objects.RatioPhase.hasDerivAt_face_mass_curve hs i).congr_deriv ?_
    simp [ratioCovector]
    ring
  have hring : ∀ c, HasDerivAt (fun y => 2 * φ y c) (-2 * (ratioCovector H ds dφ c).im) x :=
    fun c => ((hφ c).const_mul 2).congr_deriv (by simp [ratioCovector])
  refine ⟨fun i => Holonics.Objects.RatioPhase.ratio_logDerivative_curve q φT hs hφ i, hflow,
    hring, ?_, hasDerivAt_alignCost_path w φT _ _ x hring⟩
  have hkl := Holonics.Physics.Information.CrossEntropyRate.hasDerivAt_kl
    (fun y i => (NormalizedExponential.face (s y)).mass i) (fun _ i => q.mass i) _ (fun _ => 0) x
    hflow (fun _ => hasDerivAt_const x _) (fun i => H.ne_zero i) (fun i => q.ne_zero i)
    (fun y => (NormalizedExponential.face (s y)).normalized)
  have hfun : (fun y => θ * klDivergence (NormalizedExponential.face (s y)) q) =
      fun y => θ * ∑ i, (NormalizedExponential.face (s y)).mass i *
        (Real.log ((NormalizedExponential.face (s y)).mass i) - Real.log (q.mass i)) := by
    funext y
    rw [klDivergence_eq_logDifference]
  rw [hfun]
  refine (hkl.const_mul θ).congr_deriv ?_
  simp only [zero_div, mul_zero, Finset.sum_const_zero, sub_zero, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [effort, log_ratio]
  ring

/-- [proved-derived; formal-checked] **The log ratio's two returns.** The lifted log ratio
splits into the thermal port's matched shift and the ring port's gap; the matched shift extracts
`θ D(p‖q)` reversibly (the owner's `extracted_work`, `reversible_production_zero`); the ring port,
of stiffness the target's masses, dissipates `alignCost` through a resistive contact; and the two
returns add. -/
theorem two_ports_return [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) (φT y : ι → ℝ) {γ : ℝ}
    (hγ : 0 < γ) :
    (∀ i, logRatio q p φT (fun c => y c / 2) i =
      ((effort θ p q i / (2 * θ) : ℝ) : ℂ) + (phaseGap φT y i : ℂ) * Complex.I) ∧
    -(quenchWork (effort θ p q) p + restoreWork θ E (effort θ p q)) = θ * klDivergence p q ∧
    protocolProduction θ E (effort θ p q) p = 0 ∧
    Tendsto (fun t => -(quenchWork (effort θ p q) p + restoreWork θ E (effort θ p q)) +
        ringHeat q.mass φT y γ t) atTop (𝓝 (θ * klDivergence p q + alignCost q.mass φT y)) := by
  have hW := (extracted_work hθ hq (p := p)).1.trans (extracted_work hθ hq (p := p)).2
  refine ⟨fun i => logRatio_split hθ p q φT y i, hW, reversible_production_zero hθ hq, ?_⟩
  rw [hW]
  exact (ringHeat_tendsto q.mass φT y hγ q.positive).const_add _

/-- [definition] A produced ring configuration on two channels: `y = (2, −2)` (`true ↦ 2`). -/
def turnedRing : Bool → ℝ := fun b => if b then 2 else -2

/-- [definition] The two produced phase configurations: turned (`true`) and aligned (`false`). -/
def ringConfig (a : Bool) : Bool → ℝ := if a then turnedRing else fun _ => 0

/-- [counterexample; formal-checked] **The lifted face determines no ring return.** Against the
uniform target with zero phases, the turned and aligned rings return one lifted cross-entropy (code
and phase faces), yet store `alignCost` `1/2` and `0`, so no function of the lifted face returns the
ring port's energy (beside the owner's `equal_face_different_effort` for the thermal effort). -/
theorem lifted_face_determines_no_ring_return :
    liftedCrossEntropy halfSection halfSection (fun c => ringConfig true c / 2) =
        liftedCrossEntropy halfSection halfSection (fun c => ringConfig false c / 2) ∧
      alignCost halfSection.mass (fun _ => 0) (ringConfig true) = 1 / 2 ∧
      alignCost halfSection.mass (fun _ => 0) (ringConfig false) = 0 ∧
      ¬ ∃ factor : ℂ → ℝ, ∀ a : Bool,
        alignCost halfSection.mass (fun _ => 0) (ringConfig a) =
          factor (liftedCrossEntropy halfSection halfSection (fun c => ringConfig a c / 2)) := by
  have hface : liftedCrossEntropy halfSection halfSection (fun c => ringConfig true c / 2) =
      liftedCrossEntropy halfSection halfSection (fun c => ringConfig false c / 2) := by
    apply Complex.ext
    · rfl
    · simp [liftedCrossEntropy, phaseMean, halfSection, ringConfig, turnedRing]
  have htrue : alignCost halfSection.mass (fun _ => 0) (ringConfig true) = 1 / 2 := by
    simp [alignCost, phaseGap, halfSection, ringConfig, turnedRing]
    norm_num
  have hfalse : alignCost halfSection.mass (fun _ => 0) (ringConfig false) = 0 := by
    simp [alignCost, phaseGap, ringConfig]
  refine ⟨hface, htrue, hfalse, ?_⟩
  rintro ⟨factor, hfactor⟩
  have h₁ := hfactor true
  have h₀ := hfactor false
  rw [hface, htrue] at h₁
  rw [hfalse] at h₀
  rw [← h₀] at h₁
  norm_num at h₁

end Join

/-! ## 5. Witnesses -/

section Witness

/-- [definition] The two-level port's levels `E = (0, 1)` (`false ↦ 0`, `true ↦ 1`), also used as
the shift `δ`: the upper level is raised by one and restored. -/
def twoLevel : Bool → ℝ := fun b => if b then 1 else 0

/-- [proved-derived; formal-checked] **The two-level port's quasi-static work**, at `θ = 1`:
`restoreWork = log(1 + e⁻²) − log(1 + e⁻¹)`. -/
theorem twoLevel_restoreWork :
    restoreWork 1 twoLevel twoLevel = Real.log (1 + Real.exp (-2)) - Real.log (1 + Real.exp (-1)) := by
  simp only [restoreWork, partition, shifted, twoLevel, Fintype.sum_bool]
  norm_num
  rw [add_comm (Real.exp (-2)), add_comm (Real.exp (-1))]

/-- [proved-derived; formal-checked] **The two-level witness**: the leg's production lies in
`[0, 1/8]` at `N = 1` and in `[0, 1/80]` at `N = 10`, and the ten-step work exceeds `restoreWork` by
the ten-step production. -/
theorem twoLevel_witness :
    (0 ≤ legProduction 1 twoLevel twoLevel 1 ∧ legProduction 1 twoLevel twoLevel 1 ≤ 1 / 8) ∧
      (0 ≤ legProduction 1 twoLevel twoLevel 10 ∧ legProduction 1 twoLevel twoLevel 10 ≤ 1 / 80) ∧
      legWork 1 twoLevel twoLevel 10 =
        restoreWork 1 twoLevel twoLevel + legProduction 1 twoLevel twoLevel 10 := by
  have ha : ∀ b, (0 : ℝ) ≤ twoLevel b := fun b => by cases b <;> norm_num [twoLevel]
  have hb : ∀ b, twoLevel b ≤ 1 := fun b => by cases b <;> norm_num [twoLevel]
  refine ⟨⟨legProduction_nonneg one_ne_zero _ _ _, ?_⟩,
    ⟨legProduction_nonneg one_ne_zero _ _ _, ?_⟩, ?_⟩
  · exact (legProduction_le one_pos _ _ ha hb one_ne_zero).trans_eq (by norm_num)
  · exact (legProduction_le one_pos _ _ ha hb (by norm_num : (10 : ℕ) ≠ 0)).trans_eq (by norm_num)
  · rw [legWork_eq one_ne_zero _ _ (by norm_num : (10 : ℕ) ≠ 0), one_mul]

/-- [proved-derived; formal-checked] **One ring channel relaxing from `Δ = 1`**: stiffness `1`,
target phase `0`, ring at `y₀ = −2`, conductance `1`: the gap is `e^(−t/4)`, the store holds `1/2`,
and the heat dissipated tends to `1/2`. -/
theorem ring_witness :
    (∀ t, phaseGap (fun _ : Unit => (0 : ℝ))
        (ringRelax (fun _ => 1) (fun _ => 0) (fun _ => -2) 1 t) () = Real.exp (-t / 4)) ∧
      alignCost (fun _ : Unit => (1 : ℝ)) (fun _ => 0) (fun _ => -2) = 1 / 2 ∧
      Tendsto (ringHeat (fun _ : Unit => (1 : ℝ)) (fun _ => 0) (fun _ => -2) 1) atTop (𝓝 (1 / 2)) := by
  have hcost : alignCost (fun _ : Unit => (1 : ℝ)) (fun _ => 0) (fun _ => -2) = 1 / 2 := by
    simp only [alignCost, phaseGap, Finset.univ_unique, Finset.sum_singleton]
    norm_num
  refine ⟨fun t => ?_, hcost, ?_⟩
  · rw [phaseGap_ringRelax]
    simp only [phaseGap]
    ring_nf
  · have h := ringHeat_tendsto (fun _ : Unit => (1 : ℝ)) (fun _ => 0) (fun _ => -2) one_pos
      (fun _ => one_pos)
    rwa [hcost] at h

end Witness

end Holonics.Physics.InformationPort
