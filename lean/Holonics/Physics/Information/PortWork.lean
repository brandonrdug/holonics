import Holonics.Physics.InformationDifference

/-!
# The ratio covector at a thermal port: work, heat, entropy and the Gibbs/KL identity

[definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`; CLAUDE.md, "loss is
the logarithm of a ratio of Holons". Cross-entropy acts physically only through a stated material
or port return. Here the compared population `p` is an actual physical ensemble on the energy
levels `E` of a thermal port at thermal scale `θ = k_B T`. The port's own constitution is its
levels: the partition function `Z(E) = Σ exp(−Eᵢ/θ)` (`partition`) and the canonical Gibbs state
computed from them, `exp(−Eᵢ/θ)/Z(E)` (`canonicalState`), which is canonical
(`canonicalState_canonical`) and is the only canonical state of its levels: any reference `q` with
`θ log qᵢ = −Eᵢ − θ log Z` (`Canonical`, the hypothesis of the owner's
`InformationDifference.thermal_crossEntropy_identity`) has `Z(E) = exp(log Z)`
(`partition_of_canonical`) and is the computed state (`canonicalState_eq`).

A covector reaches the port as a **level shift** `δ` (`shifted`). The protocol: quench the levels
to `E + δ` with the population frozen (work `quenchWork`); relax at the shifted levels to their
canonical state `q′` (`relaxed`, heat `relaxHeat` from the energy balance at fixed levels);
restore the levels quasi-statically to `E` (work `restoreWork`, read from the two partition
functions; heat `restoreHeat` from the leg's energy balance), ending in the canonical state of `E`,
computed from the levels. The **matched** shift is the modulus face of the full ratio covector,
`δᵢ = θ log(qᵢ/pᵢ)` (`effort`; the modulus face of `log(ψ_T/ψ_H)` is twice its real part).

[proved-derived; formal-checked] Over any finite nonempty level set and `θ ≠ 0`:

* **The restoring leg produces no entropy** (`restore_production_zero`): its heat is computed from
  its energy balance and the partition functions, and the entropy change of the computed canonical
  states equals it over `θ`, by the Gibbs relation at both ends. This is a theorem of the computed
  end states, not a definition of the heat.
* **The protocol produces the relative entropy of the relaxation**, `σ = D(p‖q′) ≥ 0`
  (`protocol_production`, `protocol_production_nonneg`, reusing `free_relaxation_production` at the
  shifted levels), with its first law, the two legs' balances (`protocol_first_law`).
* **The second law at the port.** The work extracted is the free-energy drop less `θ` times the
  production, `−(W_q + W_r) = F(p) − F(q) − θD(p‖q′)` (`extracted_work_general`), so it never
  exceeds `F(p) − F(q) = θD(p‖q)` for `θ > 0` (`extracted_work_le`).
* **The matched covector is reversible.** At `δ = θ log(q/p)` the population is canonical for the
  shifted levels (`quenched_canonical`), so `q′ = p` (`matched_relaxed`), the production vanishes
  (`reversible_production_zero`), the restoring work vanishes (`matched_restoreWork`), the quench
  work is `−θD(p‖q)` (`quenchWork_eq`), and the whole free-energy drop is extracted:
  `−W = F(p) − F(q) = θD(p‖q)` (`extracted_work`, reusing
  `freeEnergy_difference_eq_thermalScale_mul_kl`).
* **Free relaxation** (no port: `W = 0`, `Q = ΔU`) produces exactly `D(p‖q) ≥ 0`
  (`free_relaxation_production`, `free_relaxation_production_nonneg`), and in general the port
  extracts as work what free relaxation would dissipate less what the protocol dissipates,
  `−W = θ(σ_free − σ)` (`work_or_production`): the literal physical effect of the relative entropy.

[counterexample; formal-checked] **A scalar face does not determine the port effort.** The
populations `(1/3, 2/3)` and `(2/3, 1/3)` return equal cross-entropy against the uniform reference,
yet their efforts differ, so no function of the scalar returns the effort
(`equal_face_different_effort`, through `InformationDifference.no_current_factor_of_equal_crossEntropy`).

The phase face of the covector (direction and winding, `InformationDifference.liftedCrossEntropy`)
is not consumed by this port; it is retained for a port that receives phase.
-/

noncomputable section

namespace Holonics.Physics.Information.PortWork

open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Holonics.Foundation.HolonicMembraneActionTransport
open Holonics.Physics.InformationDifference

variable {ι : Type*} [Fintype ι]

/-! ## 1. The port's constitution: levels, partition function and canonical state -/

/-- [definition] **The canonical Gibbs reference** of the levels `E` at thermal scale `θ`. -/
def Canonical (θ : ℝ) (E : ι → ℝ) (logZ : ℝ) (q : PositiveProbabilitySection ι) : Prop :=
  ∀ i, θ * Real.log (q.mass i) = -E i - θ * logZ

/-- [definition] **The partition function** `Z(E) = Σ exp(−Eᵢ/θ)` of the levels. -/
def partition (θ : ℝ) (E : ι → ℝ) : ℝ := ∑ i, Real.exp (-E i / θ)

theorem partition_pos [Nonempty ι] (θ : ℝ) (E : ι → ℝ) : 0 < partition θ E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- [definition] **The canonical state computed from the levels**, `exp(−Eᵢ/θ)/Z(E)`. -/
def canonicalState [Nonempty ι] (θ : ℝ) (E : ι → ℝ) : PositiveProbabilitySection ι where
  mass i := Real.exp (-E i / θ) / partition θ E
  positive i := div_pos (Real.exp_pos _) (partition_pos θ E)
  normalized := by
    rw [← Finset.sum_div]
    exact div_self (partition_pos θ E).ne'

/-- [proved-derived; formal-checked] The computed state is canonical at `log Z(E)`. -/
theorem canonicalState_canonical [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) (E : ι → ℝ) :
    Canonical θ E (Real.log (partition θ E)) (canonicalState θ E) := by
  intro i
  simp only [canonicalState]
  rw [Real.log_div (Real.exp_pos _).ne' (partition_pos θ E).ne', Real.log_exp]
  field_simp

/-- [proved-derived; formal-checked] **A canonical reference fixes the partition function**:
`Z(E) = exp(log Z)`. -/
theorem partition_of_canonical {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    partition θ E = Real.exp logZ := by
  have hi : ∀ i, Real.exp (-E i / θ) = q.mass i * Real.exp logZ := fun i => by
    have hlog : Real.log (q.mass i) = -E i / θ - logZ := by
      have := hq i
      field_simp
      linarith
    rw [← Real.exp_log (q.positive i), hlog, Real.exp_sub, div_mul_cancel₀ _ (Real.exp_pos _).ne']
  simp only [partition, hi, ← Finset.sum_mul, q.normalized, one_mul]

/-- [proved-derived; formal-checked] **The canonical reference is the computed state.** -/
theorem canonicalState_eq [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) : canonicalState θ E = q := by
  have hZ := partition_of_canonical hθ hq
  have hm : ∀ i, Real.exp (-E i / θ) / partition θ E = q.mass i := fun i => by
    have hlog : Real.log (q.mass i) = -E i / θ - logZ := by
      have := hq i
      field_simp
      linarith
    rw [hZ, ← Real.exp_sub, ← hlog, Real.exp_log (q.positive i)]
  rcases q with ⟨m, hmpos, hmnorm⟩
  simp only [canonicalState, PositiveProbabilitySection.mk.injEq]
  exact funext hm

/-- [proved-derived; formal-checked] The Gibbs relation of a canonical state:
`θ S(q) = U(E, q) + θ log Z`. -/
theorem entropy_canonical {θ : ℝ} {E : ι → ℝ} {logZ : ℝ} {q : PositiveProbabilitySection ι}
    (hq : Canonical θ E logZ q) : θ * entropy q = energyExpectation E q + θ * logZ := by
  have h := thermal_crossEntropy_identity θ E logZ q q hq
  rwa [crossEntropy_self_eq_entropy] at h

/-! ## 2. The protocol for any level shift -/

/-- [definition] **The shifted levels** `E + δ`. -/
def shifted (E δ : ι → ℝ) : ι → ℝ := fun i => E i + δ i

/-- [definition] **The quench work** `W_q = Σ pᵢ δᵢ`: levels move, the population is frozen. -/
def quenchWork (δ : ι → ℝ) (p : PositiveProbabilitySection ι) : ℝ := ∑ i, p.mass i * δ i

/-- [definition] **The relaxed state** `q′`: the canonical state of the shifted levels. -/
def relaxed [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) : PositiveProbabilitySection ι :=
  canonicalState θ (shifted E δ)

/-- [definition] **The relaxation heat** at the shifted levels, `U(E + δ, q′) − U(E + δ, p)`. -/
def relaxHeat [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) (p : PositiveProbabilitySection ι) : ℝ :=
  energyExpectation (shifted E δ) (relaxed θ E δ) - energyExpectation (shifted E δ) p

/-- [definition] **The restoring work** of the quasi-static leg, read from the partition functions:
`F_eq(E) − F_eq(E + δ) = θ log Z(E + δ) − θ log Z(E)`. -/
def restoreWork (θ : ℝ) (E δ : ι → ℝ) : ℝ :=
  θ * Real.log (partition θ (shifted E δ)) - θ * Real.log (partition θ E)

/-- [definition] **The restoring heat** from the leg's energy balance,
`Q_r = U(E, canonical E) − U(E + δ, q′) − W_r`. -/
def restoreHeat [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) : ℝ :=
  energyExpectation E (canonicalState θ E) - energyExpectation (shifted E δ) (relaxed θ E δ) -
    restoreWork θ E δ

/-- [definition] The restoring leg's entropy production `ΔS − Q_r/θ` (units of `k_B`). -/
def restoreProduction [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) : ℝ :=
  (entropy (canonicalState θ E) - entropy (relaxed θ E δ)) - restoreHeat θ E δ / θ

/-- [proved-derived; formal-checked] **The restoring leg produces no entropy**: the Gibbs relation
at both computed end states. -/
theorem restore_production_zero [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ) :
    restoreProduction θ E δ = 0 := by
  have h₁ := entropy_canonical (canonicalState_canonical hθ E)
  have h₂ := entropy_canonical (canonicalState_canonical hθ (shifted E δ))
  unfold restoreProduction restoreHeat restoreWork relaxed
  field_simp
  linarith

/-- [definition] **Free relaxation** at levels `E` from `p` to `q`: no port, so `W = 0`, `Q = ΔU`,
and the production is `ΔS − ΔU/θ`. -/
def freeProduction (θ : ℝ) (E : ι → ℝ) (p q : PositiveProbabilitySection ι) : ℝ :=
  (entropy q - entropy p) - (energyExpectation E q - energyExpectation E p) / θ

/-- [proved-derived; formal-checked] **Free relaxation produces exactly the relative entropy.** -/
theorem free_relaxation_production {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    freeProduction θ E p q = klDivergence p q := by
  have hpq := thermal_crossEntropy_identity θ E logZ p q hq
  have hqq := entropy_canonical hq
  have hkl := crossEntropy_excess_eq_kl p q
  unfold freeProduction
  field_simp
  linear_combination hqq - hpq + θ * hkl

/-- [proved-derived; formal-checked] The free relaxation's production is nonnegative. -/
theorem free_relaxation_production_nonneg {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    0 ≤ freeProduction θ E p q := by
  rw [free_relaxation_production hθ hq]
  exact klDivergence_nonnegative p q

/-- [definition] **The protocol's entropy production**: the ensemble's entropy change less the
heat it drew over both legs, over `θ`. -/
def protocolProduction [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) (p : PositiveProbabilitySection ι) :
    ℝ :=
  (entropy (canonicalState θ E) - entropy p) - (relaxHeat θ E δ p + restoreHeat θ E δ) / θ

/-- [proved-derived; formal-checked] **The protocol produces `D(p‖q′)`**: the relaxation at the
shifted levels produces it (`free_relaxation_production`), the restoring leg nothing. -/
theorem protocol_production [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ)
    (p : PositiveProbabilitySection ι) :
    protocolProduction θ E δ p = klDivergence p (relaxed θ E δ) := by
  have hrel := free_relaxation_production hθ (canonicalState_canonical hθ (shifted E δ)) (p := p)
  have hres := restore_production_zero hθ E δ
  unfold restoreProduction at hres
  unfold protocolProduction
  rw [show relaxed θ E δ = canonicalState θ (shifted E δ) from rfl, ← hrel]
  unfold freeProduction relaxHeat relaxed at *
  field_simp at hres ⊢
  linarith

/-- [proved-derived; formal-checked] The protocol's production is nonnegative. -/
theorem protocol_production_nonneg [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) (E δ : ι → ℝ)
    (p : PositiveProbabilitySection ι) : 0 ≤ protocolProduction θ E δ p := by
  rw [protocol_production hθ]
  exact klDivergence_nonnegative _ _

/-- [proved-derived; formal-checked] **The first law of the protocol**: the ensemble's energy
change is the two works and the two heats, each leg's heat its energy balance. -/
theorem protocol_first_law [Nonempty ι] (θ : ℝ) (E δ : ι → ℝ) (p : PositiveProbabilitySection ι) :
    energyExpectation E (canonicalState θ E) - energyExpectation E p =
      quenchWork δ p + restoreWork θ E δ + relaxHeat θ E δ p + restoreHeat θ E δ := by
  have hq : energyExpectation (shifted E δ) p = energyExpectation E p + quenchWork δ p := by
    simp only [energyExpectation, quenchWork, shifted, mul_add, Finset.sum_add_distrib]
  unfold relaxHeat restoreHeat
  linarith

/-- [proved-derived; formal-checked] **The work extracted is the free-energy drop less `θ` times the
production**: `−(W_q + W_r) = F(p) − F(q) − θD(p‖q′)`. -/
theorem extracted_work_general [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) (δ : ι → ℝ) :
    -(quenchWork δ p + restoreWork θ E δ) =
      (freeEnergy θ E p - freeEnergy θ E q) - θ * klDivergence p (relaxed θ E δ) := by
  have hkl := freeEnergy_difference_eq_thermalScale_mul_kl θ E logZ p q hq
  have hZ : Real.log (partition θ E) = logZ := by
    rw [partition_of_canonical hθ hq, Real.log_exp]
  have hq' := canonicalState_canonical hθ (shifted E δ)
  have hpq' := thermal_crossEntropy_identity θ (shifted E δ) _ p _ hq'
  have hpq := thermal_crossEntropy_identity θ E logZ p q hq
  have hx' := crossEntropy_excess_eq_kl p (relaxed θ E δ)
  have hx := crossEntropy_excess_eq_kl p q
  have hshift : energyExpectation (shifted E δ) p = energyExpectation E p + quenchWork δ p := by
    simp only [energyExpectation, quenchWork, shifted, mul_add, Finset.sum_add_distrib]
  rw [hkl]
  unfold restoreWork relaxed at *
  rw [hZ]
  linear_combination hpq' - hpq - θ * hx' + θ * hx + hshift

/-- [proved-derived; formal-checked] **The second law at the port**: for `θ > 0` the work
extracted never exceeds the free-energy drop `θD(p‖q)`. -/
theorem extracted_work_le [Nonempty ι] {θ : ℝ} (hθ : 0 < θ) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) (δ : ι → ℝ) :
    -(quenchWork δ p + restoreWork θ E δ) ≤ θ * klDivergence p q := by
  rw [extracted_work_general hθ.ne' hq, freeEnergy_difference_eq_thermalScale_mul_kl θ E logZ p q hq]
  have := mul_nonneg hθ.le (klDivergence_nonnegative p (relaxed θ E δ))
  linarith

/-- [proved-derived; formal-checked] **Work or production**: the port extracts as work what free
relaxation would dissipate less what the protocol dissipates, `−W = θ(σ_free − σ)`. -/
theorem work_or_production [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) (δ : ι → ℝ) :
    -(quenchWork δ p + restoreWork θ E δ) =
      θ * (freeProduction θ E p q - protocolProduction θ E δ p) := by
  rw [extracted_work_general hθ hq, free_relaxation_production hθ hq, protocol_production hθ,
    freeEnergy_difference_eq_thermalScale_mul_kl θ E logZ p q hq]
  ring

/-! ## 3. The matched covector -/

/-- [definition] **The effort**: the modulus face of the ratio covector, `ℓᵢ = log(qᵢ/pᵢ)`, pulled
back to the level port, `θℓᵢ`. -/
def effort (θ : ℝ) (p q : PositiveProbabilitySection ι) (i : ι) : ℝ :=
  θ * Real.log (q.mass i / p.mass i)

theorem log_ratio (p q : PositiveProbabilitySection ι) (i : ι) :
    Real.log (q.mass i / p.mass i) = Real.log (q.mass i) - Real.log (p.mass i) :=
  Real.log_div (ne_of_gt (q.positive i)) (ne_of_gt (p.positive i))

/-- [proved-derived; formal-checked] **The matched quench work is `−θ D(p‖q)`.** -/
theorem quenchWork_eq (θ : ℝ) (p q : PositiveProbabilitySection ι) :
    quenchWork (effort θ p q) p = -(θ * klDivergence p q) := by
  rw [klDivergence_eq_logDifference]
  unfold quenchWork effort
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [log_ratio]
  ring

/-- [proved-derived; formal-checked] **After the matched quench, `p` is canonical** for the shifted
levels at the same `log Z`. -/
theorem quenched_canonical {θ : ℝ} {E : ι → ℝ} {logZ : ℝ} {p q : PositiveProbabilitySection ι}
    (hq : Canonical θ E logZ q) : Canonical θ (shifted E (effort θ p q)) logZ p := by
  intro i
  have h := hq i
  simp only [shifted, effort, log_ratio]
  linarith

/-- [proved-derived; formal-checked] **The matched covector relaxes to `p` itself**: `q′ = p`. -/
theorem matched_relaxed [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    relaxed θ E (effort θ p q) = p :=
  canonicalState_eq hθ (quenched_canonical hq)

/-- [proved-derived; formal-checked] **The matched protocol is reversible**: it produces no
entropy. -/
theorem reversible_production_zero [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    protocolProduction θ E (effort θ p q) p = 0 := by
  rw [protocol_production hθ, matched_relaxed hθ hq, klDivergence_eq_logDifference]
  simp

/-- [proved-derived; formal-checked] **The matched restoring leg does no work**: both partition
functions are `exp(log Z)`. -/
theorem matched_restoreWork [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    restoreWork θ E (effort θ p q) = 0 := by
  rw [restoreWork, partition_of_canonical hθ (quenched_canonical hq), partition_of_canonical hθ hq,
    sub_self]

/-- [proved-derived; formal-checked] **The Gibbs/KL identity at the port**: the matched covector
extracts the whole free-energy drop, `−W = F(p) − F(q) = θ D(p‖q)`. -/
theorem extracted_work [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 0) {E : ι → ℝ} {logZ : ℝ}
    {p q : PositiveProbabilitySection ι} (hq : Canonical θ E logZ q) :
    -(quenchWork (effort θ p q) p + restoreWork θ E (effort θ p q)) =
        freeEnergy θ E p - freeEnergy θ E q ∧
      freeEnergy θ E p - freeEnergy θ E q = θ * klDivergence p q := by
  have hkl := freeEnergy_difference_eq_thermalScale_mul_kl θ E logZ p q hq
  refine ⟨?_, hkl⟩
  rw [matched_restoreWork hθ hq, add_zero, hkl, quenchWork_eq, neg_neg]

/-! ## The scalar face does not determine the effort -/

/-- [definition] The two actions' populations `(1/3, 2/3)` and `(2/3, 1/3)` read against the
uniform reference. -/
def swapReceiver : FiniteCrossEntropyReceiver Bool Bool where
  reference := fun _ => 1 / 2
  emitted := fun a => if a then entropyControlLeft.mass else entropyControlRight.mass
  reference_nonnegative := fun _ => by norm_num
  reference_normalized := by norm_num [Fintype.sum_bool]
  emitted_positive := fun a i => by
    cases a
    · exact entropyControlRight.positive i
    · exact entropyControlLeft.positive i
  emitted_normalized := fun a => by
    cases a
    · exact entropyControlRight.normalized
    · exact entropyControlLeft.normalized

/-- [counterexample; formal-checked] **Equal cross-entropy, different efforts.** The two populations
return one scalar face, but at `θ ≠ 0` their efforts at the uniform port differ, so no function of
the scalar returns the effort. -/
theorem equal_face_different_effort {θ : ℝ} (hθ : θ ≠ 0) :
    swapReceiver.face true = swapReceiver.face false ∧
      effort θ entropyControlLeft halfSection ≠ effort θ entropyControlRight halfSection ∧
      ¬ ∃ factor : ℝ → (Bool → ℝ), ∀ a : Bool,
        effort θ (if a then entropyControlLeft else entropyControlRight) halfSection =
          factor (swapReceiver.face a) := by
  have hface : swapReceiver.face true = swapReceiver.face false := by
    simp [FiniteCrossEntropyReceiver.face, finiteCrossEntropy, swapReceiver, entropyControlLeft, entropyControlRight, entropyControlLeftMass,
      entropyControlRightMass]
    ring
  have hsep : effort θ entropyControlLeft halfSection ≠ effort θ entropyControlRight halfSection := by
    intro h
    have h0 := congrFun h false
    simp only [effort, halfSection, entropyControlLeft, entropyControlRight, entropyControlLeftMass,
      entropyControlRightMass] at h0
    have hlog : Real.log ((1 / 2 : ℝ) / (1 / 3)) = Real.log ((1 / 2 : ℝ) / (2 / 3)) :=
      mul_left_cancel₀ hθ h0
    have := Real.log_injOn_pos (by norm_num : (0 : ℝ) < (1 / 2) / (1 / 3))
      (by norm_num : (0 : ℝ) < (1 / 2) / (2 / 3)) hlog
    norm_num at this
  refine ⟨hface, hsep, ?_⟩
  exact no_current_factor_of_equal_crossEntropy swapReceiver
    (fun a => effort θ (if a then entropyControlLeft else entropyControlRight) halfSection)
    hface (by simpa using hsep)

section Audit

#print axioms partition_of_canonical
#print axioms canonicalState_canonical
#print axioms canonicalState_eq
#print axioms entropy_canonical
#print axioms restore_production_zero
#print axioms free_relaxation_production
#print axioms free_relaxation_production_nonneg
#print axioms protocol_production
#print axioms protocol_production_nonneg
#print axioms protocol_first_law
#print axioms extracted_work_general
#print axioms extracted_work_le
#print axioms work_or_production
#print axioms quenchWork_eq
#print axioms quenched_canonical
#print axioms matched_relaxed
#print axioms reversible_production_zero
#print axioms matched_restoreWork
#print axioms extracted_work
#print axioms equal_face_different_effort

end Audit

end Holonics.Physics.Information.PortWork
