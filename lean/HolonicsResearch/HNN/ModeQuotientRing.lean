import Holonics.HNN.ModeQuotient
import Holonics.HNN.LoadedRing

/-!
# HNN.ModeQuotientRing: the mode quotient on the concrete loaded ring

[definition] The box of #410: "The mode quotient on the concrete ring: bridge
`HNN/ModeQuotient`'s linear statements (`periodic_lift_exact`, `descended_run_reads`, …) to
`HNN/Ring`'s loaded tick; gain covectors factor through the retention chart `V`." `HNN/ModeQuotient`
opens on the sentence that a loaded ring "ticks … as one linear system per pump phase:
`x′ = T_t x + B_t e`, `s′ = ρ_t x + D_t e`", and proves its laws over abstract linear `T_t`, `B_t`,
`ρ_t`, `D_t`; nothing tied those maps to the ring's solve. This file reads them off the ring.

Sources: `HNN/ModeQuotient` (its open paragraph and items 1, 3, 4 and 5); `HNN/Ring` §2 and §2′
(`ringOperator`, `ringRight`, `ringOut`, `ring_cayley_denominator_nonsingular`,
`loaded_tick_material_variation`, `gainedCapacity`, `gainedDissipation`, `gainedStiffness`);
`HNN/LoadedRing` §1 and §2, the owner of the tick as one linear operand (`rateMap`, `stepMap`) and of
the word's run (`resonance`, `resonanceOut`, `resonanceRate`, `phaseAt`), whose blocks the four maps
here are; `docs/HNN_FORMULA.md` §4, "The loaded ring's mode quotient"; the atlas rows
`hnn.mode-quotient-period-lift`, `hnn.mode-quotient-one-chart`, `hnn.mode-quotient-descended-run`,
`hnn.mode-quotient-storage-null` (its note "not in Lean: port admitted ⇒ `K_rel ⊆ ker K_t × ker C`"),
`hnn.mode-quotient-gain-descent`, `hnn.loaded-ring-material`, `hnn.loaded-ring-stage` and
`parametron.ring-denominator`.

The ring at tick `t`: capacity `C`, stiffness `K_t` (the pump's phase block), an executed inverse
`M_t⁻¹` of `M_t = 2C + (h/Y) I + hD + (h²/2) K_t`, and with `ω₀ = M_t⁻¹(2Cw − hK_t u)`

```text
T_t (u, w) = (u + h ω₀, 2ω₀ − w)            B_t e = (h M_t⁻¹(h e), 2 M_t⁻¹(h e))
ρ_t (u, w) = −(2/Y) ω₀                       D_t e = e − (2/Y) M_t⁻¹(h e)
```

[proved-derived; formal-checked] What is proved (`factor_of_ker_le` alone is
[proved-standard; formal-checked], the factor theorem of linear algebra over a field).

1. **The loaded tick is the quotient's linear system** (`tickT`, `tickB`, `tickRead`, `tickD`,
   their `_apply` lemmas, `stepMap_blocks`, `loaded_tick_linear_system`). The four maps are the
   blocks of `LoadedRing.stepMap` (`→L[ℝ]`, read as `→ₗ[ℝ]` by `toLinearMap`), and at the ring's
   solve `M ω = 2Cw + he − hKu`, with `M⁻¹` a left inverse, `(u + hω, 2ω − w) = T x + B e` and
   `ringOut Y e ω = ρ x + D e`. The inverse is the ring's own: under `HNN/Ring`'s certificate
   (`C, D, K ⪰ 0`, `Y, h > 0`, finite dimension) a two-sided inverse exists
   (`ring_inverse_exists`) and every right inverse is one (`leftInverse_of_certified`).
2. **The pump's period makes the system periodic** (`inverse_periodic`, `loaded_periodic`,
   `loaded_periodic_of_inverse`, `phased_periodic`). A `P`-periodic stiffness with two-sided
   inverses has `P`-periodic inverses, so `T_t`, `B_t`, `ρ_t`, `D_t` are `P`-periodic; the pump's
   phase family `t ↦ A_((τ + t) mod P)` always is.
3. **The quotient's run is the ring's word** (`run_eq_resonance`, `read_eq_resonanceOut`,
   `cycle_eq_resonance`, `free_read_eq_resonanceOut`): `ModeQuotient.run` of the phase family
   opened at `τ` is `LoadedRing.resonance`, its returned wave `ρ_t x_t + D_t e_t` is
   `resonanceOut`, and the cycle `Φ t` is the undriven word. Hence on the ring's data:
   `periodic_lift_exact` (`loaded_period_lift`: the ring's undriven port wave is silent at every
   tick exactly when the state lies in the period lift's kernel); one chart for every phase
   (`loaded_release_silent`: a state a shared chart releases returns no wave at any tick); and
   `descended_run`, `descended_run_reads` (`loaded_descended_run`, `loaded_descended_run_reads`:
   the descended run is the chart of the ring's word and returns the ring's own wave
   `resonanceOut` for every drive sequence).
4. **The release stores nothing on the ring** (`released_rate_null`, `tick_release_storage_null`,
   `chart_release_storage_null`, `phase_kernel_storage_null`). A state silent at the port on
   itself and on its tick has zero rate, and `ModeQuotient.released_pair_storage_null` gives
   `C k_w = 0`, `K_t k_u = 0`. So a chart that closes every square with the port admitted releases
   inside `ker K_t × ker C` at every tick, and the phase family's kernel lies in
   `ker K_i × ker C` at every phase `i < P`: the atlas note on `hnn.mode-quotient-storage-null`.
5. **Gain covectors factor through the retention chart** (`variationMap`, `variationPhi`,
   `variationH`, `variation_blocks`, `variation_at_solve`, `variation_pairs`, `ringGain`,
   `ringGain_eq_resonance_sum`, `factor_of_ker_le`, `loaded_gain_descends`,
   `gain_factors_of_release_null`, `released_variation`, `capacity_gain_factors`,
   `dissipation_gain_factors`, `stiffness_pump_gain_factors`). The material variation of
   `loaded_tick_material_variation`, `2δC(w − ω) − hδD ω − hδK_t(u + hω/2)`, is `φ_t x + H_t e`
   with `φ_t`, `H_t` the blocks of one linear map, and paired with the solved covector `r̄` it is
   the output variation's pairing (`variation_pairs`). Summed along the ring's own word it is
   `ModeQuotient.gainCovector` (`ringGain_eq_resonance_sum`). Where `φ_t = φ̄_t V`, `descended_gain`
   and `gain_fibre_invariant` apply (`loaded_gain_descends`); a variation null on `ker V` factors
   (`factor_of_ker_le`). On the gained ring `C = g_C² C₀`, `D = g_D² D₀`,
   `K_t = g_K² K₀ + g_P² Π_t`, along `δ = 2g·base`, with `h, Y ≠ 0` and right inverses `M_t⁻¹`:
   the capacity family (`g_C ≠ 0`) and the dissipation family factor through every chart that
   closes every square with the port admitted,
   and the stiffness and pump families do when the pump's cycle holds a half-turn
   (`Π_(t₁) = −Π_(t₀)`, which an unpumped ring, `Π = 0`, holds), `g_K, g_P ≠ 0`: each gain covector
   is then the same at `x₀ + k` for every released `k`.
6. **A witness** (`wOne`, `wInv`, `witness_operator`, `witness_inverse`, `witness_blocks`,
   `witness_tick`, `witness_run`). On `E = ℝ`, `C = K = 1`, `D = 0`, `Y = h = 1`, a constant pump:
   `M = 7/2`, `M⁻¹ = 2/7`, `T = [[5/7, 4/7], [−4/7, 1/7]]`, `B = (2/7, 4/7)`, `ρ = (4/7, −8/7)`,
   `D = 3/7`. From `(u, w, e) = (1, 1, 1)` the solve is `ω = 4/7`, the tick `(11/7, 1/7)` and the
   returned wave `−1/7`, which `T x + B e`, `ρ x + D e` and one step of `ModeQuotient.run` return.

What is not claimed. The Rust realization `holonics::hnn::modes` (retired at U2, held at `1bdacc8f`)
is not tied to these statements. Learning beyond the gain covector (the costate's recursion on the
ring's ports, the deposit's step, a learning aeon's chart, `ModeQuotient.learning_chart_le_kernel`
on the ring) is not stated here. The executed lattice chart and split (`HNN/LatticeWord`, `HNN/Ring`
§2) are not stated: every map here runs the law's solve through a declared inverse. The converse
of item 4 (a subspace of `ker K_t × ker C` closing a chart) is not claimed, nor is a stiffness or pump
family factoring without the half-turn (`ModeQuotient.standing_pump_threshold_reads_release` bars it
at a standing pump at threshold).

The computational object is the helical pair interaction, read on the loaded ring: the ring is a
parametron whose pump moves its stiffness phase by phase, its port is the pair contact through which
the element's wave enters and the returned wave leaves, and the mode quotient is what one chart keeps
of the contact's state for every admitted future. Of the winding guide's six general objects this
touches the helix (the pump's phase `t mod P`, whole periods carried by the period lift), the tube
(the tick-indexed run as a clocked span, and its descended run) and faces and placement (the port's
reading and the gain covectors as faces of the state); the pair, cell holonomy and tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.ModeQuotientRing

open Holonics.HNN.Ring Holonics.HNN.LoadedRing Holonics.HNN.ModeQuotient
open Holonics.Compression.Core.FaceMap

/-! ## 1. The loaded tick is the quotient's linear system -/

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The tick on the state** at zero drive, the state block of `stepMap`:
`T (u, w) = (u + hω₀, 2ω₀ − w)`, `ω₀ = M⁻¹(2Cw − hKu)`. -/
def tickT (C K Minv : E →L[ℝ] E) (Y h : ℝ) : (E × E) →ₗ[ℝ] E × E :=
  LinearMap.fst ℝ (E × E) E ∘ₗ (stepMap C K Minv Y h).toLinearMap ∘ₗ LinearMap.inl ℝ (E × E) E

/-- [definition] **The drive's source** on the state: `B e = (h M⁻¹(h e), 2 M⁻¹(h e))`. -/
def tickB (C K Minv : E →L[ℝ] E) (Y h : ℝ) : E →ₗ[ℝ] E × E :=
  LinearMap.fst ℝ (E × E) E ∘ₗ (stepMap C K Minv Y h).toLinearMap ∘ₗ LinearMap.inr ℝ (E × E) E

/-- [definition] **The port's reading of the state**: `ρ (u, w) = −(2/Y) ω₀`. -/
def tickRead (C K Minv : E →L[ℝ] E) (Y h : ℝ) : (E × E) →ₗ[ℝ] E :=
  LinearMap.snd ℝ (E × E) E ∘ₗ (stepMap C K Minv Y h).toLinearMap ∘ₗ LinearMap.inl ℝ (E × E) E

/-- [definition] **The port's feedthrough**: `D e = e − (2/Y) M⁻¹(h e)`. -/
def tickD (C K Minv : E →L[ℝ] E) (Y h : ℝ) : E →ₗ[ℝ] E :=
  LinearMap.snd ℝ (E × E) E ∘ₗ (stepMap C K Minv Y h).toLinearMap ∘ₗ LinearMap.inr ℝ (E × E) E

/-- [proved-derived; formal-checked] The state block, read on the ring's data. -/
theorem tickT_apply (C K Minv : E →L[ℝ] E) (Y h : ℝ) (u w : E) :
    tickT C K Minv Y h (u, w) =
      (u + h • Minv ((2 : ℝ) • C w - h • K u), (2 : ℝ) • Minv ((2 : ℝ) • C w - h • K u) - w) := by
  have hs := stepMap_apply C K Minv Y h u w 0
  simp only [ringRight, smul_zero, add_zero] at hs
  change (stepMap C K Minv Y h ((u, w), 0)).1 = _
  rw [hs]

/-- [proved-derived; formal-checked] The drive's block, read on the ring's data. -/
theorem tickB_apply (C K Minv : E →L[ℝ] E) (Y h : ℝ) (e : E) :
    tickB C K Minv Y h e = (h • Minv (h • e), (2 : ℝ) • Minv (h • e)) := by
  have hs := stepMap_apply C K Minv Y h 0 0 e
  simp only [ringRight, map_zero, smul_zero, zero_add, sub_zero] at hs
  change (stepMap C K Minv Y h ((0, 0), e)).1 = _
  rw [hs]

/-- [proved-derived; formal-checked] The port's reading, read on the ring's data. -/
theorem tickRead_apply (C K Minv : E →L[ℝ] E) (Y h : ℝ) (u w : E) :
    tickRead C K Minv Y h (u, w) = -((2 / Y) • Minv ((2 : ℝ) • C w - h • K u)) := by
  have hs := stepMap_apply C K Minv Y h u w 0
  simp only [ringRight, smul_zero, add_zero] at hs
  change (stepMap C K Minv Y h ((u, w), 0)).2 = _
  rw [hs, ringOut, zero_sub]

/-- [proved-derived; formal-checked] The port's feedthrough, read on the ring's data. -/
theorem tickD_apply (C K Minv : E →L[ℝ] E) (Y h : ℝ) (e : E) :
    tickD C K Minv Y h e = e - (2 / Y) • Minv (h • e) := by
  have hs := stepMap_apply C K Minv Y h 0 0 e
  simp only [ringRight, map_zero, smul_zero, zero_add, sub_zero] at hs
  change (stepMap C K Minv Y h ((0, 0), e)).2 = _
  rw [hs, ringOut]

/-- [proved-derived; formal-checked] **One tick is the four blocks**:
`stepMap (x, e) = (T x + B e, ρ x + D e)`. -/
theorem stepMap_blocks (C K Minv : E →L[ℝ] E) (Y h : ℝ) (x : E × E) (e : E) :
    stepMap C K Minv Y h (x, e) =
      (tickT C K Minv Y h x + tickB C K Minv Y h e,
        tickRead C K Minv Y h x + tickD C K Minv Y h e) := by
  have hxe : ((x, e) : (E × E) × E) = (x, 0) + (0, e) := by simp
  rw [hxe, map_add]
  rfl

/-- [proved-derived; formal-checked] **The loaded tick is the quotient's linear system.** At the
ring's solve `M ω = 2Cw + he − hKu`, with `M⁻¹` a left inverse of `M`, the tick and the returned
wave are `(u + hω, 2ω − w) = T x + B e` and `ringOut Y e ω = ρ x + D e`. -/
theorem loaded_tick_linear_system (C D K Minv : E →L[ℝ] E) {Y h : ℝ}
    (hMl : ∀ v, Minv (ringOperator C D K Y h v) = v) {u w e ω : E}
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w e) :
    (u + h • ω, (2 : ℝ) • ω - w) = tickT C K Minv Y h (u, w) + tickB C K Minv Y h e ∧
      ringOut Y e ω = tickRead C K Minv Y h (u, w) + tickD C K Minv Y h e := by
  have hω : Minv (ringRight C K h u w e) = ω := by rw [← hsolve, hMl]
  have hb := stepMap_blocks C K Minv Y h (u, w) e
  rw [stepMap_apply, hω] at hb
  exact ⟨congrArg Prod.fst hb, congrArg Prod.snd hb⟩

/-- [proved-derived; formal-checked] **The ring's certificate gives its inverse**: with
`C, D, K ⪰ 0`, `Y, h > 0` in finite dimension, `M` has a two-sided continuous inverse. -/
theorem ring_inverse_exists [FiniteDimensional ℝ E] (C D K : E →L[ℝ] E)
    (hC : ∀ v, 0 ≤ inner ℝ v (C v)) (hD : ∀ v, 0 ≤ inner ℝ v (D v))
    (hK : ∀ v, 0 ≤ inner ℝ v (K v)) {Y h : ℝ} (hY : 0 < Y) (hh : 0 < h) :
    ∃ Minv : E →L[ℝ] E, (∀ v, ringOperator C D K Y h (Minv v) = v) ∧
      ∀ v, Minv (ringOperator C D K Y h v) = v := by
  obtain ⟨_, hsolve⟩ := (ring_cayley_denominator_nonsingular C D K hC hD hK).1 hY hh
  have hbij : Function.Bijective (ringOperator C D K Y h : E →ₗ[ℝ] E) := by
    refine ⟨fun a b hab => ?_, fun r => ?_⟩
    · simp only [ContinuousLinearMap.coe_coe] at hab
      exact (hsolve _).unique hab rfl
    · obtain ⟨ω, hω, _⟩ := hsolve r
      exact ⟨ω, by simpa using hω⟩
  let L := (LinearEquiv.ofBijective _ hbij).toContinuousLinearEquiv
  exact ⟨(L.symm : E →L[ℝ] E), fun v => L.apply_symm_apply v, fun v => L.symm_apply_apply v⟩

/-- [proved-derived; formal-checked] Under the ring's certificate every right inverse of `M` is a
left inverse (the solve is unique). -/
theorem leftInverse_of_certified [FiniteDimensional ℝ E] (C D K Minv : E →L[ℝ] E)
    (hC : ∀ v, 0 ≤ inner ℝ v (C v)) (hD : ∀ v, 0 ≤ inner ℝ v (D v))
    (hK : ∀ v, 0 ≤ inner ℝ v (K v)) {Y h : ℝ} (hY : 0 < Y) (hh : 0 < h)
    (hM : ∀ v, ringOperator C D K Y h (Minv v) = v) (v : E) :
    Minv (ringOperator C D K Y h v) = v := by
  obtain ⟨_, hsolve⟩ := (ring_cayley_denominator_nonsingular C D K hC hD hK).1 hY hh
  exact (hsolve _).unique (hM _) rfl

end Blocks

/-! ## 2. The tick-indexed system and the pump's period -/

section System

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] The state transport at tick `t`, stiffness `K_t`, inverse `M_t⁻¹`. -/
def loadedT (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (Y h : ℝ) (t : ℕ) :
    (E × E) →ₗ[ℝ] E × E :=
  tickT C (Kt t) (Minvt t) Y h

/-- [definition] The drive's source at tick `t`. -/
def loadedB (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (Y h : ℝ) (t : ℕ) : E →ₗ[ℝ] E × E :=
  tickB C (Kt t) (Minvt t) Y h

/-- [definition] The port's reading at tick `t`. -/
def loadedRead (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (Y h : ℝ) (t : ℕ) :
    (E × E) →ₗ[ℝ] E :=
  tickRead C (Kt t) (Minvt t) Y h

/-- [definition] The port's feedthrough at tick `t`. -/
def loadedD (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (Y h : ℝ) (t : ℕ) : E →ₗ[ℝ] E :=
  tickD C (Kt t) (Minvt t) Y h

/-- [definition] **The pump's phase family opened at the field's tick `τ`**: tick `k` takes the
phase `(τ + k) mod P` (`LoadedRing.phaseAt`). -/
def phased {α : Type*} (A : ℕ → α) (P τ : ℕ) : ℕ → α := fun k => A (phaseAt P (τ + k))

/-- [proved-derived; formal-checked] The phase family has the pump's period. -/
theorem phased_periodic {α : Type*} (A : ℕ → α) (P τ : ℕ) : Periodic P (phased A P τ) := by
  intro t
  simp only [phased, phaseAt]
  rw [← Nat.add_assoc, Nat.add_mod_right]

/-- [proved-derived; formal-checked] **A periodic stiffness has periodic inverses**: two-sided
inverses of `M_t` and `M_(t+P) = M_t` agree. -/
theorem inverse_periodic (C D : E →L[ℝ] E) {Kt Minvt : ℕ → E →L[ℝ] E} {Y h : ℝ} {P : ℕ}
    (hK : Periodic P Kt) (hR : ∀ t v, ringOperator C D (Kt t) Y h (Minvt t v) = v)
    (hL : ∀ t v, Minvt t (ringOperator C D (Kt t) Y h v) = v) : Periodic P Minvt := by
  intro t
  ext v
  calc Minvt (t + P) v = Minvt (t + P) (ringOperator C D (Kt (t + P)) Y h (Minvt t v)) := by
        rw [hK t, hR t]
    _ = Minvt t v := hL (t + P) _

/-- [proved-derived; formal-checked] **The pump's period makes the system periodic**: periodic
`K_t` and `M_t⁻¹` give periodic `T_t`, `B_t`, `ρ_t`, `D_t`. -/
theorem loaded_periodic (C : E →L[ℝ] E) {Kt Minvt : ℕ → E →L[ℝ] E} {Y h : ℝ} {P : ℕ}
    (hK : Periodic P Kt) (hM : Periodic P Minvt) :
    Periodic P (loadedT C Kt Minvt Y h) ∧ Periodic P (loadedB C Kt Minvt Y h) ∧
      Periodic P (loadedRead C Kt Minvt Y h) ∧ Periodic P (loadedD C Kt Minvt Y h) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩ <;>
    simp only [loadedT, loadedB, loadedRead, loadedD, hK t, hM t]

/-- [proved-derived; formal-checked] A `P`-periodic stiffness with two-sided inverses at every tick
gives a `P`-periodic system. -/
theorem loaded_periodic_of_inverse (C D : E →L[ℝ] E) {Kt Minvt : ℕ → E →L[ℝ] E} {Y h : ℝ}
    {P : ℕ} (hK : Periodic P Kt) (hR : ∀ t v, ringOperator C D (Kt t) Y h (Minvt t v) = v)
    (hL : ∀ t v, Minvt t (ringOperator C D (Kt t) Y h v) = v) :
    Periodic P (loadedT C Kt Minvt Y h) ∧ Periodic P (loadedB C Kt Minvt Y h) ∧
      Periodic P (loadedRead C Kt Minvt Y h) ∧ Periodic P (loadedD C Kt Minvt Y h) :=
  loaded_periodic C hK (inverse_periodic C D hK hR hL)

variable (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ)

/-- [proved-derived; formal-checked] **The quotient's run is the ring's word**: `ModeQuotient.run`
of the phase family opened at `τ` is `LoadedRing.resonance`. -/
theorem run_eq_resonance (e : ℕ → E) (x₀ : E × E) (t : ℕ) :
    run (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h)
        (loadedB C (phased Kp P τ) (phased Minvp P τ) Y h) e x₀ t =
      resonance C Kp Minvp Y h P τ e x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run, ih]
    change _ = (stepMap C (Kp (phaseAt P (τ + t))) (Minvp (phaseAt P (τ + t))) Y h
      (resonance C Kp Minvp Y h P τ e x₀ t, e t)).1
    rw [stepMap_blocks]
    rfl

/-- [proved-derived; formal-checked] **The returned wave is the ring's**: `ρ_t x_t + D_t e_t` on the
quotient's run is `LoadedRing.resonanceOut`. -/
theorem read_eq_resonanceOut (e : ℕ → E) (x₀ : E × E) (t : ℕ) :
    loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h t
        (run (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h)
          (loadedB C (phased Kp P τ) (phased Minvp P τ) Y h) e x₀ t) +
      loadedD C (phased Kp P τ) (phased Minvp P τ) Y h t (e t) =
      resonanceOut C Kp Minvp Y h P τ e x₀ t := by
  rw [run_eq_resonance]
  change _ = (stepMap C (Kp (phaseAt P (τ + t))) (Minvp (phaseAt P (τ + t))) Y h
    (resonance C Kp Minvp Y h P τ e x₀ t, e t)).2
  rw [stepMap_blocks]
  rfl

/-- [proved-derived; formal-checked] **The descended run is the chart of the ring's word**
(`ModeQuotient.descended_run` on the ring). -/
theorem loaded_descended_run {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q)
    (T' : ℕ → Q →ₗ[ℝ] Q)
    (hsq : ∀ t, V ∘ₗ loadedT C (phased Kp P τ) (phased Minvp P τ) Y h t = T' t ∘ₗ V)
    (e : ℕ → E) (x₀ : E × E) (t : ℕ) :
    V (resonance C Kp Minvp Y h P τ e x₀ t) =
      run T' (fun t => V ∘ₗ loadedB C (phased Kp P τ) (phased Minvp P τ) Y h t) e (V x₀) t := by
  rw [← run_eq_resonance, descended_run V _ T' _ hsq]

/-- [proved-derived; formal-checked] **The descended ring returns the ring's own wave**
(`ModeQuotient.descended_run_reads` on the ring): for every drive sequence, the descended run's
reading is `resonanceOut`. -/
theorem loaded_descended_run_reads {Q : Type*} [AddCommGroup Q] [Module ℝ Q]
    (V : (E × E) →ₗ[ℝ] Q) (T' : ℕ → Q →ₗ[ℝ] Q) (ρ' : ℕ → Q →ₗ[ℝ] E)
    (hsq : ∀ t, V ∘ₗ loadedT C (phased Kp P τ) (phased Minvp P τ) Y h t = T' t ∘ₗ V)
    (hρ : ∀ t, loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h t = ρ' t ∘ₗ V)
    (e : ℕ → E) (x₀ : E × E) (t : ℕ) :
    ρ' t (run T' (fun t => V ∘ₗ loadedB C (phased Kp P τ) (phased Minvp P τ) Y h t) e (V x₀) t) +
        loadedD C (phased Kp P τ) (phased Minvp P τ) Y h t (e t) =
      resonanceOut C Kp Minvp Y h P τ e x₀ t := by
  rw [descended_run_reads V _ T' _ _ ρ' _ hsq hρ e x₀ t, read_eq_resonanceOut]

end System

/-! ## 3. The period lift and one chart on the ring's port -/

section Lift

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) {P : ℕ} (τ : ℕ)

/-- [proved-derived; formal-checked] **The cycle is the undriven word**: `Φ t x` is the ring's
resonance from `x` at zero drive. -/
theorem cycle_eq_resonance (x : E × E) (t : ℕ) :
    cycle (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h) t x =
      resonance C Kp Minvp Y h P τ (fun _ => 0) x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change loadedT C (phased Kp P τ) (phased Minvp P τ) Y h t
        (cycle (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h) t x) =
      (stepMap C (Kp (phaseAt P (τ + t))) (Minvp (phaseAt P (τ + t))) Y h
        (resonance C Kp Minvp Y h P τ (fun _ => 0) x t, 0)).1
    rw [ih, stepMap_blocks, map_zero, add_zero]
    rfl

/-- [proved-derived; formal-checked] The admitted reading `ρ_t Φ t x` is the ring's undriven port
wave. -/
theorem free_read_eq_resonanceOut (x : E × E) (t : ℕ) :
    loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h t
        (cycle (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h) t x) =
      resonanceOut C Kp Minvp Y h P τ (fun _ => 0) x t := by
  rw [cycle_eq_resonance]
  change _ = (stepMap C (Kp (phaseAt P (τ + t))) (Minvp (phaseAt P (τ + t))) Y h
    (resonance C Kp Minvp Y h P τ (fun _ => 0) x t, 0)).2
  rw [stepMap_blocks]
  simp only [map_zero, add_zero]
  rfl

/-- [proved-derived; formal-checked] **The period lift reads the ring** (`periodic_lift_exact` on
the loaded ring): the undriven port wave from `x` is silent at every tick exactly when `x` lies in
the kernel of the face map of the period navigator `Φ P` read by the phase-offset port readings. -/
theorem loaded_period_lift (hP : 0 < P) (x : E × E) :
    (∀ t, resonanceOut C Kp Minvp Y h P τ (fun _ => 0) x t = 0) ↔
      x ∈ LinearMap.ker (faceMap (liftedRead (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h)
        (fun _ : Unit => loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h) P)
        (fun _ : Unit => cycle (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h) P)) := by
  have hper := loaded_periodic C (phased_periodic Kp P τ) (phased_periodic Minvp P τ) (Y := Y)
    (h := h)
  rw [← periodic_lift_exact _ (fun _ : Unit => loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h)
    P hper.1 (fun _ => hper.2.2.1) hP x]
  simp only [free_read_eq_resonanceOut]
  exact ⟨fun hx _ t => hx t, fun hx t => hx () t⟩

/-- [proved-derived; formal-checked] **What one chart for every phase releases is silent at the
ring's port** (`shared_chart_le_phase_kernel` and `phase_kernel_le_cycle` on the loaded ring): if
`V` closes the square of every phase `i < P` and the port reads through it, every `k ∈ ker V`
returns no wave at any tick of the undriven word. -/
theorem loaded_release_silent (hP : 0 < P) {Q : Type} [AddCommGroup Q] [Module ℝ Q]
    (V : (E × E) →ₗ[ℝ] Q) (T' : Fin P → Q →ₗ[ℝ] Q) (ρ' : Unit × Fin P → Q →ₗ[ℝ] E)
    (hsq : ∀ i : Fin P, V ∘ₗ loadedT C (phased Kp P τ) (phased Minvp P τ) Y h i = T' i ∘ₗ V)
    (hread : ∀ i : Fin P, loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h i = ρ' ((), i) ∘ₗ V)
    {k : E × E} (hk : V k = 0) (t : ℕ) :
    resonanceOut C Kp Minvp Y h P τ (fun _ => 0) k t = 0 := by
  have hper := loaded_periodic C (phased_periodic Kp P τ) (phased_periodic Minvp P τ) (Y := Y)
    (h := h)
  have hker := shared_chart_le_phase_kernel (loadedT C (phased Kp P τ) (phased Minvp P τ) Y h)
    (fun _ : Unit => loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h) P V T' ρ' hsq
    (fun ri => hread ri.2) (LinearMap.mem_ker.mpr hk)
  rw [← free_read_eq_resonanceOut]
  exact phase_kernel_le_cycle _ (fun _ : Unit => loadedRead C (phased Kp P τ) (phased Minvp P τ) Y h)
    P hper.1 (fun _ => hper.2.2.1) hP hker () t

end Lift

/-! ## 4. The release stores nothing on the ring -/

section Storage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **A state silent at the port moves no rate**:
`ρ k = 0` gives `M⁻¹(2C k_w − hK k_u) = 0`. -/
theorem released_rate_null (C K Minv : E →L[ℝ] E) {Y h : ℝ} (hY : Y ≠ 0) {k : E × E}
    (hk : tickRead C K Minv Y h k = 0) : Minv ((2 : ℝ) • C k.2 - h • K k.1) = 0 := by
  obtain ⟨u, w⟩ := k
  rw [tickRead_apply, neg_eq_zero] at hk
  exact (smul_eq_zero.mp hk).resolve_left (div_ne_zero two_ne_zero hY)

/-- [proved-derived; formal-checked] **A state silent at the port on itself and on its tick stores
nothing** (`ModeQuotient.released_pair_storage_null` on the ring's solve): `C k_w = 0`,
`K k_u = 0`. -/
theorem tick_release_storage_null (C D K Minv : E →L[ℝ] E) {Y h : ℝ} (hh : h ≠ 0) (hY : Y ≠ 0)
    (hR : ∀ v, ringOperator C D K Y h (Minv v) = v) {k : E × E}
    (hk : tickRead C K Minv Y h k = 0)
    (hk' : tickRead C K Minv Y h (tickT C K Minv Y h k) = 0) : C k.2 = 0 ∧ K k.1 = 0 := by
  obtain ⟨u, w⟩ := k
  rw [tickT_apply, tickRead_apply, ← neg_smul] at hk'
  rw [tickRead_apply, ← neg_smul] at hk
  have h0 := released_pair_storage_null (ringOperator C D K Y h : E →ₗ[ℝ] E) (C : E →ₗ[ℝ] E)
    (K : E →ₗ[ℝ] E) (u := u) (w := w) hh hY (hR _) hk (hR _) hk'
  simpa only [ContinuousLinearMap.coe_coe] using h0

/-- [proved-derived; formal-checked] **A chart that closes every square with the port admitted
releases inside `ker K_t × ker C` at every tick.** -/
theorem chart_release_storage_null (C D : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) {Y h : ℝ}
    (hh : h ≠ 0) (hY : Y ≠ 0) (hR : ∀ t v, ringOperator C D (Kt t) Y h (Minvt t v) = v)
    {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q) (T' : ℕ → Q →ₗ[ℝ] Q)
    (ρ' : ℕ → Q →ₗ[ℝ] E) (hsq : ∀ t, V ∘ₗ loadedT C Kt Minvt Y h t = T' t ∘ₗ V)
    (hρ : ∀ t, loadedRead C Kt Minvt Y h t = ρ' t ∘ₗ V) {k : E × E} (hk : V k = 0) (t : ℕ) :
    C k.2 = 0 ∧ Kt t k.1 = 0 := by
  have hsilent : tickRead C (Kt t) (Minvt t) Y h k = 0 := by
    change loadedRead C Kt Minvt Y h t k = 0
    rw [hρ, LinearMap.comp_apply, hk, map_zero]
  have hsilent' : tickRead C (Kt t) (Minvt t) Y h (tickT C (Kt t) (Minvt t) Y h k) = 0 := by
    change loadedRead C Kt Minvt Y h t (loadedT C Kt Minvt Y h t k) = 0
    rw [hρ, LinearMap.comp_apply, ← LinearMap.comp_apply V, hsq, LinearMap.comp_apply, hk,
      map_zero, map_zero]
  exact tick_release_storage_null C D (Kt t) (Minvt t) hh hY (hR t) hsilent hsilent'

/-- [proved-derived; formal-checked] **The phase family's kernel stores nothing** (the atlas note
on `hnn.mode-quotient-storage-null`): a state silent to the port after every word of the phase
family lies in `ker K_i × ker C` at every phase `i < P`. -/
theorem phase_kernel_storage_null {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C D : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) {Y h : ℝ} (hh : h ≠ 0) (hY : Y ≠ 0)
    (hR : ∀ t v, ringOperator C D (Kt t) Y h (Minvt t v) = v) (P : ℕ) {x : E × E}
    (hx : x ∈ LinearMap.ker (faceMap (phaseRead (fun _ : Unit => loadedRead C Kt Minvt Y h) P)
      (phaseTransport (loadedT C Kt Minvt Y h) P))) (i : Fin P) :
    C x.2 = 0 ∧ Kt i x.1 = 0 := by
  rw [LinearMap.mem_ker] at hx
  have h0 := congrFun hx (((), i), [])
  have h1 := congrFun hx (((), i), [i])
  exact tick_release_storage_null C D (Kt i) (Minvt i) hh hY (hR i) h0 h1

end Storage

/-! ## 5. Gain covectors factor through the retention chart -/

section Gain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The material variation at the solve** (`HNN/Ring.loaded_material_rate_tangent`'s
right side), one linear map of state and drive:
`((u, w), e) ↦ 2δC(w − ω) − hδD ω − hδK(u + (h/2)ω)`, `ω = M⁻¹(2Cw + he − hKu)`. -/
def variationMap (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) : (E × E) × E →L[ℝ] E :=
  (2 : ℝ) • dC.comp ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E) -
      rateMap C K Minv h) -
    h • dD.comp (rateMap C K Minv h) -
    h • dK.comp ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E) +
      (h / 2) • rateMap C K Minv h)

/-- [proved-derived; formal-checked] The variation, read on the ring's data. -/
theorem variationMap_apply (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) (u w e : E) :
    variationMap dC dD dK C K Minv h ((u, w), e) =
      (2 : ℝ) • dC (w - Minv (ringRight C K h u w e)) - h • dD (Minv (ringRight C K h u w e)) -
        h • dK (u + (h / 2) • Minv (ringRight C K h u w e)) := by
  simp only [variationMap, _root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', rateMap_apply]

/-- [definition] **The variation's state part** `φ`. -/
def variationPhi (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) : (E × E) →ₗ[ℝ] E :=
  (variationMap dC dD dK C K Minv h).toLinearMap ∘ₗ LinearMap.inl ℝ (E × E) E

/-- [definition] **The variation's drive part** `H`. -/
def variationH (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) : E →ₗ[ℝ] E :=
  (variationMap dC dD dK C K Minv h).toLinearMap ∘ₗ LinearMap.inr ℝ (E × E) E

/-- [proved-derived; formal-checked] The variation is `φ x + H e`. -/
theorem variation_blocks (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) (x : E × E) (e : E) :
    variationMap dC dD dK C K Minv h (x, e) =
      variationPhi dC dD dK C K Minv h x + variationH dC dD dK C K Minv h e := by
  have hxe : ((x, e) : (E × E) × E) = (x, 0) + (0, e) := by simp
  rw [hxe, map_add]
  rfl

/-- [proved-derived; formal-checked] The state part, read on the ring's data, with
`ω₀ = M⁻¹(2Cw − hKu)`. -/
theorem variationPhi_apply (dC dD dK C K Minv : E →L[ℝ] E) (h : ℝ) (u w : E) :
    variationPhi dC dD dK C K Minv h (u, w) =
      (2 : ℝ) • dC (w - Minv ((2 : ℝ) • C w - h • K u)) -
        h • dD (Minv ((2 : ℝ) • C w - h • K u)) -
        h • dK (u + (h / 2) • Minv ((2 : ℝ) • C w - h • K u)) := by
  change variationMap dC dD dK C K Minv h ((u, w), 0) = _
  rw [variationMap_apply]
  simp only [ringRight, smul_zero, add_zero]

/-- [proved-derived; formal-checked] **The gained family's variation at the solve is
`φ x + H e`**: at `M ω = 2Cw + he − hKu`, with `M⁻¹` a left inverse,
`2δC(w − ω) − hδD ω − hδK(u + (h/2)ω) = φ (u, w) + H e`. -/
theorem variation_at_solve (C D K Minv dC dD dK : E →L[ℝ] E) {Y h : ℝ}
    (hMl : ∀ v, Minv (ringOperator C D K Y h v) = v) {u w e ω : E}
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w e) :
    (2 : ℝ) • dC (w - ω) - h • dD ω - h • dK (u + (h / 2) • ω) =
      variationPhi dC dD dK C K Minv h (u, w) + variationH dC dD dK C K Minv h e := by
  have hω : Minv (ringRight C K h u w e) = ω := by rw [← hsolve, hMl]
  rw [← variation_blocks, variationMap_apply, hω]

/-- [proved-derived; formal-checked] **The solved covector pairs the family `φ x + H e`**
(`HNN/Ring.loaded_tick_material_variation` on the blocks): the output variation's pairing with the
costates is `⟨r̄, φ (u, w) + H e⟩`. -/
theorem variation_pairs [CompleteSpace E] (C D K Minv dC dD dK : E →L[ℝ] E) {Y h : ℝ}
    (hMl : ∀ v, Minv (ringOperator C D K Y h v) = v) {u w e ω : E}
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w e) (uBar' wBar' sBar' rBar : E)
    (hAdj : ContinuousLinearMap.adjoint (ringOperator C D K Y h) rBar =
      h • uBar' + (2 : ℝ) • wBar' - (2 / Y) • sBar')
    {δω : E} (hImplicit : ringOperator C D K Y h δω + (2 : ℝ) • dC ω + h • dD ω +
      (h ^ 2 / 2) • dK ω = (2 : ℝ) • dC w - h • dK u) :
    inner ℝ uBar' (h • δω) + inner ℝ wBar' ((2 : ℝ) • δω) + inner ℝ sBar' (-(2 / Y) • δω) =
      inner ℝ rBar (variationPhi dC dD dK C K Minv h (u, w) + variationH dC dD dK C K Minv h e) := by
  rw [← variation_at_solve C D K Minv dC dD dK hMl hsolve]
  exact loaded_tick_material_variation _ dC dD dK u w ω uBar' wBar' sBar' rBar hAdj hImplicit

/-- [definition] The variation's state part at tick `t`, with direction `(δC, δD, δK_t)`. -/
def loadedPhi (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (dC dD : E →L[ℝ] E)
    (dKt : ℕ → E →L[ℝ] E) (h : ℝ) (t : ℕ) : (E × E) →ₗ[ℝ] E :=
  variationPhi dC dD (dKt t) C (Kt t) (Minvt t) h

/-- [definition] The variation's drive part at tick `t`. -/
def loadedH (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (dC dD : E →L[ℝ] E)
    (dKt : ℕ → E →L[ℝ] E) (h : ℝ) (t : ℕ) : E →ₗ[ℝ] E :=
  variationH dC dD (dKt t) C (Kt t) (Minvt t) h

/-- [definition] **The ring's gain covector** over `N` ticks: `ModeQuotient.gainCovector` of the
ring's system and the family's variation, with the solved covectors read by `a t`. -/
def ringGain (a : ℕ → E →ₗ[ℝ] ℝ) (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E)
    (dC dD : E →L[ℝ] E) (dKt : ℕ → E →L[ℝ] E) (Y h : ℝ) (e : ℕ → E) (x₀ : E × E) (N : ℕ) : ℝ :=
  gainCovector a (loadedPhi C Kt Minvt dC dD dKt h) (loadedH C Kt Minvt dC dD dKt h)
    (loadedT C Kt Minvt Y h) (loadedB C Kt Minvt Y h) e x₀ N

/-- [proved-derived; formal-checked] **The gain covector is the family's variation along the ring's
own word**: on the phase family opened at `τ`, each term pairs
`2δC(w_t − ω_t) − hδD ω_t − hδK_t(u_t + (h/2)ω_t)` at the resonance's state and rate. -/
theorem ringGain_eq_resonance_sum (a : ℕ → E →ₗ[ℝ] ℝ) (C : E →L[ℝ] E)
    (Kp Minvp dKp : ℕ → E →L[ℝ] E) (dC dD : E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ) (e : ℕ → E)
    (x₀ : E × E) (N : ℕ) :
    ringGain a C (phased Kp P τ) (phased Minvp P τ) dC dD (phased dKp P τ) Y h e x₀ N =
      ∑ t ∈ Finset.range N, a t
        ((2 : ℝ) • dC ((resonance C Kp Minvp Y h P τ e x₀ t).2 -
            resonanceRate C Kp Minvp Y h P τ e x₀ t) -
          h • dD (resonanceRate C Kp Minvp Y h P τ e x₀ t) -
          h • dKp (phaseAt P (τ + t)) ((resonance C Kp Minvp Y h P τ e x₀ t).1 +
            (h / 2) • resonanceRate C Kp Minvp Y h P τ e x₀ t)) := by
  unfold ringGain gainCovector
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [run_eq_resonance]
  change a t (variationPhi dC dD (dKp (phaseAt P (τ + t))) C (Kp (phaseAt P (τ + t)))
    (Minvp (phaseAt P (τ + t))) h (resonance C Kp Minvp Y h P τ e x₀ t) +
      variationH dC dD (dKp (phaseAt P (τ + t))) C (Kp (phaseAt P (τ + t)))
        (Minvp (phaseAt P (τ + t))) h (e t)) = _
  rw [← variation_blocks, variationMap_apply]
  rfl

/-- [proved-standard; formal-checked] **A map null on a chart's kernel factors through it**: over a
field, `ker V ≤ ker φ` gives `φ = φ̄ V`. -/
theorem factor_of_ker_le {K : Type*} [Field K] {X Q F : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Q] [Module K Q] [AddCommGroup F] [Module K F] (V : X →ₗ[K] Q) (φ : X →ₗ[K] F)
    (hle : LinearMap.ker V ≤ LinearMap.ker φ) : ∃ φ' : Q →ₗ[K] F, φ = φ' ∘ₗ V := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((LinearMap.ker V).liftQ φ hle ∘ₗ V.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  have hq : V.quotKerEquivRange.symm ⟨V x, LinearMap.mem_range_self V x⟩ =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  have hgx := LinearMap.congr_fun hg ⟨V x, LinearMap.mem_range_self V x⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, hq,
    Submodule.liftQ_apply] at hgx
  rw [LinearMap.comp_apply, hgx]

/-- [proved-derived; formal-checked] **The ring's gain covector descends** where the variation reads
the state through the chart (`ModeQuotient.descended_gain`, `gain_fibre_invariant` on the ring):
it is the same pairing on the descended run, and the same at `x₀ + k` for released `k`. -/
theorem loaded_gain_descends (a : ℕ → E →ₗ[ℝ] ℝ) (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E)
    (dC dD : E →L[ℝ] E) (dKt : ℕ → E →L[ℝ] E) {Y h : ℝ} {Q : Type*} [AddCommGroup Q]
    [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q) (T' : ℕ → Q →ₗ[ℝ] Q)
    (hsq : ∀ t, V ∘ₗ loadedT C Kt Minvt Y h t = T' t ∘ₗ V) (φ' : ℕ → Q →ₗ[ℝ] E)
    (hφ : ∀ t, loadedPhi C Kt Minvt dC dD dKt h t = φ' t ∘ₗ V) (e : ℕ → E) (x₀ : E × E)
    {k : E × E} (hk : V k = 0) (N : ℕ) :
    ringGain a C Kt Minvt dC dD dKt Y h e x₀ N =
        gainCovector a φ' (loadedH C Kt Minvt dC dD dKt h) T'
          (fun t => V ∘ₗ loadedB C Kt Minvt Y h t) e (V x₀) N ∧
      ringGain a C Kt Minvt dC dD dKt Y h e (x₀ + k) N = ringGain a C Kt Minvt dC dD dKt Y h e x₀ N :=
  ⟨descended_gain V _ T' _ hsq _ φ' hφ a _ e x₀ N,
    gain_fibre_invariant V _ T' _ hsq _ φ' hφ a _ e x₀ hk N⟩

/-- [definition] **A chart closes the ring's squares with the port admitted**: `V T_t = T̄_t V`
and `ρ_t = ρ̄_t V` at every tick. -/
def ChartCloses {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q)
    (T' : ℕ → Q →ₗ[ℝ] Q) (ρ' : ℕ → Q →ₗ[ℝ] E) (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E)
    (Y h : ℝ) : Prop :=
  (∀ t, V ∘ₗ loadedT C Kt Minvt Y h t = T' t ∘ₗ V) ∧ ∀ t, loadedRead C Kt Minvt Y h t = ρ' t ∘ₗ V

/-- [definition] **A gain family factors through the chart**: its state variation is `φ̄_t V` at
every tick, and its gain covector is the same at `x₀ + k` for every released `k`. -/
def GainFactors {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q) (C : E →L[ℝ] E)
    (Kt Minvt : ℕ → E →L[ℝ] E) (dC dD : E →L[ℝ] E) (dKt : ℕ → E →L[ℝ] E) (Y h : ℝ) : Prop :=
  (∃ φ' : ℕ → Q →ₗ[ℝ] E, ∀ t, loadedPhi C Kt Minvt dC dD dKt h t = φ' t ∘ₗ V) ∧
    ∀ (a : ℕ → E →ₗ[ℝ] ℝ) (e : ℕ → E) (x₀ k : E × E), V k = 0 → ∀ N,
      ringGain a C Kt Minvt dC dD dKt Y h e (x₀ + k) N = ringGain a C Kt Minvt dC dD dKt Y h e x₀ N

/-- [proved-derived; formal-checked] **A variation null on the release factors**: if `V` closes
every square and each `φ_t` vanishes on `ker V`, the family factors through `V`. -/
theorem gain_factors_of_release_null (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E)
    (dC dD : E →L[ℝ] E) (dKt : ℕ → E →L[ℝ] E) {Y h : ℝ} {Q : Type*} [AddCommGroup Q]
    [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q) (T' : ℕ → Q →ₗ[ℝ] Q)
    (hsq : ∀ t, V ∘ₗ loadedT C Kt Minvt Y h t = T' t ∘ₗ V)
    (hnull : ∀ t k, V k = 0 → loadedPhi C Kt Minvt dC dD dKt h t k = 0) :
    GainFactors V C Kt Minvt dC dD dKt Y h := by
  have hφ : ∀ t, ∃ φ' : Q →ₗ[ℝ] E, loadedPhi C Kt Minvt dC dD dKt h t = φ' ∘ₗ V := fun t =>
    factor_of_ker_le V _ fun k hk => LinearMap.mem_ker.mpr (hnull t k (LinearMap.mem_ker.mp hk))
  choose φ' hφ' using hφ
  exact ⟨⟨φ', hφ'⟩, fun a e x₀ k hk N =>
    (loaded_gain_descends a C Kt Minvt dC dD dKt V T' hsq φ' hφ' e x₀ hk N).2⟩

/-- [proved-derived; formal-checked] **On the release the variation is its storage part** (the
storage part of `ModeQuotient.released_variation_shift`, read at the release): the released rate is
zero, so `φ_t k = 2δC k_w − hδK_t k_u`. -/
theorem released_variation (C : E →L[ℝ] E) (Kt Minvt : ℕ → E →L[ℝ] E) (dC dD : E →L[ℝ] E)
    (dKt : ℕ → E →L[ℝ] E) {Y h : ℝ} (hY : Y ≠ 0) {Q : Type*} [AddCommGroup Q] [Module ℝ Q]
    (V : (E × E) →ₗ[ℝ] Q) (ρ' : ℕ → Q →ₗ[ℝ] E)
    (hρ : ∀ t, loadedRead C Kt Minvt Y h t = ρ' t ∘ₗ V) {k : E × E} (hk : V k = 0) (t : ℕ) :
    loadedPhi C Kt Minvt dC dD dKt h t k = (2 : ℝ) • dC k.2 - h • dKt t k.1 := by
  have hsilent : tickRead C (Kt t) (Minvt t) Y h k = 0 := by
    change loadedRead C Kt Minvt Y h t k = 0
    rw [hρ, LinearMap.comp_apply, hk, map_zero]
  have hω := released_rate_null C (Kt t) (Minvt t) hY hsilent
  obtain ⟨u, w⟩ := k
  change variationPhi dC dD (dKt t) C (Kt t) (Minvt t) h (u, w) = _
  rw [variationPhi_apply]
  simp only at hω
  rw [hω]
  simp

/-- [definition] The gained ring's stiffness at tick `t`: `g_K² K₀ + g_P² Π_t`. -/
def gainedK (gK gP : ℝ) (K₀ : E →L[ℝ] E) (Pm : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E :=
  fun t => gainedStiffness gK gP K₀ (Pm t)

variable (C₀ D₀ K₀ : E →L[ℝ] E) (Pm Minvt : ℕ → E →L[ℝ] E) {gC gD gK gP Y h : ℝ}
variable {Q : Type*} [AddCommGroup Q] [Module ℝ Q] (V : (E × E) →ₗ[ℝ] Q) (T' : ℕ → Q →ₗ[ℝ] Q)
  (ρ' : ℕ → Q →ₗ[ℝ] E)

/-- [proved-derived; formal-checked] **The capacity gain factors** through every chart that closes
the gained ring's squares with the port admitted (`g_C ≠ 0`; direction `δC = 2g_C C₀`). -/
theorem capacity_gain_factors (hgC : gC ≠ 0) (hh : h ≠ 0) (hY : Y ≠ 0)
    (hR : ∀ t v, ringOperator (gainedCapacity gC C₀) (gainedDissipation gD D₀)
      (gainedK gK gP K₀ Pm t) Y h (Minvt t v) = v)
    (hV : ChartCloses V T' ρ' (gainedCapacity gC C₀) (gainedK gK gP K₀ Pm) Minvt Y h) :
    GainFactors V (gainedCapacity gC C₀) (gainedK gK gP K₀ Pm) Minvt ((2 * gC) • C₀) 0
      (fun _ => 0) Y h := by
  obtain ⟨hsq, hρ⟩ := hV
  refine gain_factors_of_release_null _ _ _ _ _ _ V T' hsq fun t k hk => ?_
  rw [released_variation _ _ _ _ _ _ hY V ρ' hρ hk t]
  have hC := (chart_release_storage_null _ _ _ _ hh hY hR V T' ρ' hsq hρ hk t).1
  have hC₀ := squared_gain_variation_null hgC (C₀ : E →ₗ[ℝ] E) (v := k.2)
    (by simpa [gainedCapacity] using hC)
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe] at hC₀
  simp [hC₀]

/-- [proved-derived; formal-checked] **The dissipation gain factors** through every chart that
closes the ring's squares with the port admitted (direction `δD = 2g_D D₀`): the released rate is
zero. -/
theorem dissipation_gain_factors (C : E →L[ℝ] E) (Kt : ℕ → E →L[ℝ] E) (hY : Y ≠ 0)
    (hV : ChartCloses V T' ρ' C Kt Minvt Y h) :
    GainFactors V C Kt Minvt 0 ((2 * gD) • D₀) (fun _ => 0) Y h := by
  obtain ⟨hsq, hρ⟩ := hV
  refine gain_factors_of_release_null _ _ _ _ _ _ V T' hsq fun t k hk => ?_
  rw [released_variation _ _ _ _ _ _ hY V ρ' hρ hk t]
  simp

/-- [proved-derived; formal-checked] **The stiffness and pump gains factor when the pump's cycle
holds a half-turn** (`ModeQuotient.half_turn_separates` on the gained ring): with
`Π_(t₁) = −Π_(t₀)` and `g_K, g_P ≠ 0`, a released displacement lies in `ker K₀` and in `ker Π_t` at
every tick, so the directions `δK = 2g_K K₀` and `δK_t = 2g_P Π_t` factor. -/
theorem stiffness_pump_gain_factors (hgK : gK ≠ 0) (hgP : gP ≠ 0) (hh : h ≠ 0) (hY : Y ≠ 0)
    (hR : ∀ t v, ringOperator (gainedCapacity gC C₀) (gainedDissipation gD D₀)
      (gainedK gK gP K₀ Pm t) Y h (Minvt t v) = v)
    (hV : ChartCloses V T' ρ' (gainedCapacity gC C₀) (gainedK gK gP K₀ Pm) Minvt Y h)
    (hhalf : ∃ t₀ t₁, Pm t₁ = -Pm t₀) :
    GainFactors V (gainedCapacity gC C₀) (gainedK gK gP K₀ Pm) Minvt 0 0
        (fun _ => (2 * gK) • K₀) Y h ∧
      GainFactors V (gainedCapacity gC C₀) (gainedK gK gP K₀ Pm) Minvt 0 0
        (fun t => (2 * gP) • Pm t) Y h := by
  obtain ⟨hsq, hρ⟩ := hV
  obtain ⟨t₀, t₁, hPm⟩ := hhalf
  have hstore : ∀ k, V k = 0 → ∀ t, gK ^ 2 • K₀ k.1 + gP ^ 2 • Pm t k.1 = 0 := by
    intro k hk t
    have := (chart_release_storage_null _ _ _ _ hh hY hR V T' ρ' hsq hρ hk t).2
    simpa [gainedK, gainedStiffness] using this
  have hK₀ : ∀ k, V k = 0 → K₀ k.1 = 0 := by
    intro k hk
    have h₀ := hstore k hk t₀
    have h₁ := hstore k hk t₁
    rw [hPm, _root_.neg_apply, smul_neg, ← sub_eq_add_neg] at h₁
    exact (half_turn_separates (pow_ne_zero 2 hgK) (pow_ne_zero 2 hgP) (K₀ : E →ₗ[ℝ] E)
      (Pm t₀ : E →ₗ[ℝ] E) (u := k.1) (by simpa using h₀) (by simpa using h₁)).1
  have hP : ∀ k, V k = 0 → ∀ t, Pm t k.1 = 0 := by
    intro k hk t
    have h₀ := hstore k hk t
    rw [hK₀ k hk, smul_zero, zero_add] at h₀
    exact (smul_eq_zero.mp h₀).resolve_left (pow_ne_zero 2 hgP)
  refine ⟨gain_factors_of_release_null _ _ _ _ _ _ V T' hsq fun t k hk => ?_,
    gain_factors_of_release_null _ _ _ _ _ _ V T' hsq fun t k hk => ?_⟩
  · rw [released_variation _ _ _ _ _ _ hY V ρ' hρ hk t]
    simp [hK₀ k hk]
  · rw [released_variation _ _ _ _ _ _ hY V ρ' hρ hk t]
    simp [hP k hk t]

end Gain

/-! ## 6. A witness: the one-dimensional ring -/

section Witness

/-- [definition] The witness's capacity and stiffness, `1` on `ℝ`. -/
def wOne : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- [definition] The witness's inverse, `M⁻¹ = 2/7`. -/
def wInv : ℝ →L[ℝ] ℝ := (2 / 7 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- [proved-derived; formal-checked] At `C = K = 1`, `D = 0`, `Y = h = 1`: `M = 2 + 1 + 0 + ½ = 7/2`. -/
theorem witness_operator (v : ℝ) : ringOperator wOne 0 wOne 1 1 v = 7 / 2 * v := by
  simp only [ringOperator, wOne, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, _root_.zero_apply, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] `2/7` is the two-sided inverse of `M = 7/2`. -/
theorem witness_inverse :
    (∀ v, ringOperator wOne 0 wOne 1 1 (wInv v) = v) ∧
      ∀ v, wInv (ringOperator wOne 0 wOne 1 1 v) = v := by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;>
    simp only [witness_operator, wInv, _root_.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] <;> ring

/-- [proved-derived; formal-checked] **The four maps of the witness**: `T = [[5/7, 4/7], [−4/7, 1/7]]`,
`B = (2/7, 4/7)`, `ρ = (4/7, −8/7)`, `D = 3/7`. -/
theorem witness_blocks (u w e : ℝ) :
    tickT wOne wOne wInv 1 1 (u, w) = (5 / 7 * u + 4 / 7 * w, -(4 / 7) * u + 1 / 7 * w) ∧
      tickB wOne wOne wInv 1 1 e = (2 / 7 * e, 4 / 7 * e) ∧
      tickRead wOne wOne wInv 1 1 (u, w) = 4 / 7 * u - 8 / 7 * w ∧
      tickD wOne wOne wInv 1 1 e = 3 / 7 * e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tickT_apply]
    simp only [wOne, wInv, _root_.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rw [tickB_apply]
    simp only [wInv, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      Prod.mk.injEq]
    constructor <;> ring
  · rw [tickRead_apply]
    simp only [wOne, wInv, _root_.smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul]
    ring
  · rw [tickD_apply]
    simp only [wInv, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring

/-- [proved-derived; formal-checked] **One tick matches the solve**: from `(u, w, e) = (1, 1, 1)`
the solve is `ω = 4/7`, the tick `(1 + ω, 2ω − 1) = (11/7, 1/7)` is `T x + B e`, and the returned
wave `1 − 2ω = −1/7` is `ρ x + D e`. -/
theorem witness_tick :
    ringOperator wOne 0 wOne 1 1 (4 / 7) = ringRight wOne wOne 1 1 1 1 ∧
      ((1 : ℝ) + (1 : ℝ) • (4 / 7 : ℝ), (2 : ℝ) • (4 / 7 : ℝ) - 1) = (11 / 7, 1 / 7) ∧
      tickT wOne wOne wInv 1 1 (1, 1) + tickB wOne wOne wInv 1 1 1 = (11 / 7, 1 / 7) ∧
      ringOut 1 1 (4 / 7 : ℝ) = -1 / 7 ∧
      tickRead wOne wOne wInv 1 1 (1, 1) + tickD wOne wOne wInv 1 1 1 = -1 / 7 := by
  have hsolve : ringOperator wOne 0 wOne 1 1 (4 / 7) = ringRight wOne wOne 1 1 1 1 := by
    rw [witness_operator]
    simp only [ringRight, wOne, ContinuousLinearMap.id_apply, smul_eq_mul]
    norm_num
  obtain ⟨hstate, hwave⟩ := loaded_tick_linear_system wOne 0 wOne wInv witness_inverse.2 hsolve
  have hpair : ((1 : ℝ) + (1 : ℝ) • (4 / 7 : ℝ), (2 : ℝ) • (4 / 7 : ℝ) - 1) = (11 / 7, 1 / 7) := by
    simp only [smul_eq_mul, Prod.mk.injEq]
    constructor <;> norm_num
  have hout : ringOut 1 1 (4 / 7 : ℝ) = -1 / 7 := by
    simp only [ringOut, smul_eq_mul]
    norm_num
  exact ⟨hsolve, hpair, hstate.symm.trans hpair, hout, hwave.symm.trans hout⟩

/-- [proved-derived; formal-checked] **One step of `ModeQuotient.run`** on the witness under a
constant pump (period `1`) from `(1, 1)` at drive `1` is the tick `(11/7, 1/7)`, and the system is
`1`-periodic. -/
theorem witness_run :
    run (loadedT wOne (fun _ => wOne) (fun _ => wInv) 1 1)
        (loadedB wOne (fun _ => wOne) (fun _ => wInv) 1 1) (fun _ => 1) (1, 1) 1 = (11 / 7, 1 / 7) ∧
      Periodic 1 (loadedT wOne (fun _ => wOne) (fun _ => wInv) 1 1) := by
  refine ⟨?_, (loaded_periodic wOne (fun _ => rfl) (fun _ => rfl)).1⟩
  exact witness_tick.2.2.1

end Witness

end Holonics.HNN.ModeQuotientRing
