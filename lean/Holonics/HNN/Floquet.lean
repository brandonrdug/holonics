import Holonics.HNN.Ring
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# HNN.Floquet: the pumped ring's monodromy, its growth certificate and phase-sensitive amplification

[definition] The parametron re-derived from its constitution (`docs/ELEMENTARY_OBJECTS.md` §5,
September 29). The pump is a periodic modulation of the constitution; one period of executed ticks
composes the ring's **monodromy** `M_T = T_(T−1) ⋯ T_0` (the cell holonomy of the pump's cycle).
Its growth is certified by a positive form `G` with `M_Tᵀ G M_T ⪯ ρ² G`: attained by any exterior
means, certified inside exactly by Sylvester inertia (the Rust owner `hnn::ring`). This module
states what the certificate implies, and the pump's own geometry.

1. **The certificate bounds the energy.** [proved-derived; formal-checked] With the Loewner order
   read as a quadratic form, `x ⬝ᵥ (Mᵀ G M) x = E_G(M x)` (`energy_transport`,
   `certificate_reading`), so the certificate gives `E_G(M x) ≤ ρ² E_G(x)`
   (`floquet_energy_step`) and `E_G(Mᵐ x) ≤ ρ^(2m) E_G(x)` (`floquet_energy_iterate`); below the
   bifurcation (`ρ² ≤ 1`, `G ⪰ 0`) the ring is passive (`floquet_passive`). A partial period reads
   one certificate per tick in the same form, `E_G(T_k ⋯ T_1 x) ≤ (∏ σ_t²) E_G(x)`
   (`floquet_tick_product`).
2. **The consumer equation.** [proved-derived; formal-checked] Against a reference form `Q` with
   `γ_lo Q ⪯ G ⪯ γ_hi Q` and `γ_lo > 0`: `E_Q(Mᵐ x) ≤ (γ_hi/γ_lo) ρ^(2m) E_Q(x)`
   (`floquet_metric_change`): the certified growth the constitution's step reads through a pumped
   resonator, one change of metric and `ρ²` per period. A span from any pump phase is a partial
   period, `m` whole periods and a partial period, each partial product certified tick by tick
   (`partial_period_le_pow`): `E_Q(Post Mᵐ Pre x) ≤ (γ_hi/γ_lo) σ_post ρ^(2m) σ_pre E_Q(x)`
   (`floquet_span_reach`), the factor `hnn::ring::FloquetBound::reach` maximizes over the phases
   and `hnn::constitution` composes into its gains (`Holon/Deposition` §10).
3. **The pump's axes.** [proved-derived; formal-checked] The pumped node stiffness
   `kI − 2p [[cos ψ, sin ψ], [sin ψ, −cos ψ]]` at `cos ψ = c² − s²`, `sin ψ = 2cs` has the in-phase
   axis `a = (c, s) = e^{iψ/2}` at `k − 2p` and the quadrature `ia` at `k + 2p`
   (`pumped_inphase_axis`, `pumped_quadrature_axis`). A standing pump's bifurcation is `k − 2p = 0`,
   and the executed tick has the multiplier one exactly where the stiffness is singular: a state is
   fixed by the tick iff its rate and velocity vanish and `K u = 0` (`standing_fixed_point_iff`).
   Below it the storage form itself certifies passivity: at the law's solve, with no drive, the
   tick does not raise `E_Q` (`storage_form_certifies_passive`, from `HNN/Ring.ring_tick_port_balance`).
4. **Phase-sensitive amplification.** [proved-derived; formal-checked] Past the bifurcation, in the
   continuous chart at unit capacity, the in-phase axis has stiffness `−κ²`: its rate matrix
   `[[0, 1], [κ², 0]]` grows `(1, κ)` at `+κ` and squeezes `(1, −κ)` at `−κ` (`inphase_growing`,
   `inphase_squeezed`), and its growing amplitude is read by the covector `(κ, 1)`:
   `κ u_∥ + w_∥` (`inphase_growing_coordinate`), the input's in-phase projection; the quadrature
   turns, `[[0, 1], [−ω², 0]]² = −ω² I` (`quadrature_turns`). The Cayley tick keeps each eigen-axis
   with the multiplier `(2 + hλ)/(2 − hλ)` (`cayley_eigen`, `cayley_tick_eigen`). The lock's sheet is
   the sign of the growing amplitude: `cos(φ_in − ψ/2)` for an input on the displacement.
5. **Two pumps compose to a turn by their relative phase** (the square law). [proved-derived;
   formal-checked] The pump's block is a reflection `R_ψ = [[c, s], [s, −c]]`, `R_ψ² = 1`
   (`reflection_sq`); two reflections compose to the rotation by their relative phase
   (`reflection_mul_reflection`), whose trace `2(cc′ + ss′) = 2 Re(e^{iψ} e^{−iχ})` reads it
   (`reflection_pair_trace`, `reflection_pair_trace_carriers`). A monodromy through two pumped ticks
   carries that pairing in its second order in the pump.
6. **No linear threshold reads a relative phase.** [proved-derived; formal-checked] The relative
   pairing `Re(z_a z̄_b)` is even under the global half-turn (`relativePairing_halfTurn`), a linear
   reading is odd, so no linear map followed by a threshold reads it
   (`no_linear_threshold_reads_relative_phase`): the relative phase of two cells enters the lock
   only through the pump.

7. **The lattice's floor on a multiplier.** [proved-derived; formal-checked] The executed monodromy
   is `M = N/Δ` with `N` an integer matrix (the Rust owner carries each tick on integers). If `N` is
   invertible, `|det N| ≥ 1` and `det N` is the product of its multipliers, so one has modulus at
   least one (`integer_monodromy_floor`): `ρ(M) ≥ 1/Δ`. A sheet on an exact constitution that grows
   at all grows by at least one part in `Δ` per cycle; no reading approaches zero continuously.

[open] (#62) The singular, not nilpotent `N`: the same bound from the nonzero multipliers, whose
product is the lowest nonzero coefficient of `det(ν − N)`, an integer.

[open] That the principal-resonance monodromy of a rotating pump has a real multiplier below `−1`
(the subharmonic lock), and the Mathieu tongue boundaries, are not stated here (#62).

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.HNN.Floquet

open Matrix
open Holonics.HNN.Propagation
open Holonics.HNN.Ring
open scoped BigOperators

/-! ## 1. The certificate bounds the energy -/

section Certificate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The energy of a state in a form** `E_G(x) = x ⬝ᵥ G x`. -/
def energy (G : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (G *ᵥ x)

/-- [definition] **The Floquet certificate**: `Mᵀ G M ⪯ ρ² G` in the quadratic-form order. -/
def FloquetCertifies (G M : Matrix n n ℝ) (ρ2 : ℝ) : Prop :=
  ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ ((ρ2 • G - Mᵀ * G * M) *ᵥ x)

/-- [definition] A form is positive semidefinite in the quadratic-form order. -/
def FormNonneg (G : Matrix n n ℝ) : Prop := ∀ x : n → ℝ, 0 ≤ energy G x

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The pulled-back form reads the carried state**:
`x ⬝ᵥ (Mᵀ G M) x = E_G(M x)`. -/
theorem energy_transport (G M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Mᵀ * G * M) *ᵥ x) = energy G (M *ᵥ x) := by
  unfold energy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The certificate's gap read on a state**:
`x ⬝ᵥ (ρ²G − MᵀGM) x = ρ² E_G(x) − E_G(M x)`. -/
theorem certificate_reading (G M : Matrix n n ℝ) (ρ2 : ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((ρ2 • G - Mᵀ * G * M) *ᵥ x) = ρ2 * energy G x - energy G (M *ᵥ x) := by
  rw [Matrix.sub_mulVec, dotProduct_sub, energy_transport, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]
  rfl

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **One period grows the energy by at most `ρ²`.** -/
theorem floquet_energy_step {G M : Matrix n n ℝ} {ρ2 : ℝ} (hcert : FloquetCertifies G M ρ2)
    (x : n → ℝ) : energy G (M *ᵥ x) ≤ ρ2 * energy G x := by
  have h := hcert x
  rw [certificate_reading] at h
  linarith

/-- [proved-derived; formal-checked] **`m` periods grow the energy by at most `ρ^(2m)`.** -/
theorem floquet_energy_iterate {G M : Matrix n n ℝ} {ρ2 : ℝ} (hρ : 0 ≤ ρ2)
    (hcert : FloquetCertifies G M ρ2) (m : ℕ) (x : n → ℝ) :
    energy G ((M ^ m) *ᵥ x) ≤ ρ2 ^ m * energy G x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc energy G (M *ᵥ ((M ^ m) *ᵥ x)) ≤ ρ2 * energy G ((M ^ m) *ᵥ x) :=
          floquet_energy_step hcert _
      _ ≤ ρ2 * (ρ2 ^ m * energy G x) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ2 ^ (m + 1) * energy G x := by ring

/-- [proved-derived; formal-checked] **Below the bifurcation the ring is passive**: `ρ² ≤ 1` and
`G ⪰ 0` keep `E_G(Mᵐ x) ≤ E_G(x)` for every number of periods. -/
theorem floquet_passive {G M : Matrix n n ℝ} {ρ2 : ℝ} (hρ0 : 0 ≤ ρ2) (hρ1 : ρ2 ≤ 1)
    (hG : FormNonneg G) (hcert : FloquetCertifies G M ρ2) (m : ℕ) (x : n → ℝ) :
    energy G ((M ^ m) *ᵥ x) ≤ energy G x := by
  have h := floquet_energy_iterate hρ0 hcert m x
  have hp : ρ2 ^ m ≤ 1 := pow_le_one₀ hρ0 hρ1
  have hE := hG x
  nlinarith

/-- [proved-derived; formal-checked] **A partial period** reads one certificate per tick in the
same form: `E_G(T_k ⋯ T_1 x) ≤ (∏ σ_t²) E_G(x)` for ticks `T_t` with `T_tᵀ G T_t ⪯ σ_t² G`,
`σ_t² ≥ 0` (the list's head acts last). -/
theorem floquet_tick_product (G : Matrix n n ℝ) :
    ∀ ticks : List (Matrix n n ℝ × ℝ), (∀ t ∈ ticks, 0 ≤ t.2 ∧ FloquetCertifies G t.1 t.2) →
      ∀ x : n → ℝ, energy G ((ticks.map Prod.fst).prod *ᵥ x) ≤
        (ticks.map Prod.snd).prod * energy G x := by
  intro ticks
  induction ticks with
  | nil => intro _ x; simp
  | cons t rest ih =>
    intro h x
    have ht := h t (List.mem_cons_self)
    have hrest : ∀ u ∈ rest, 0 ≤ u.2 ∧ FloquetCertifies G u.1 u.2 :=
      fun u hu => h u (List.mem_cons_of_mem _ hu)
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mulVec_mulVec]
    calc energy G (t.1 *ᵥ ((rest.map Prod.fst).prod *ᵥ x))
        ≤ t.2 * energy G ((rest.map Prod.fst).prod *ᵥ x) := floquet_energy_step ht.2 _
      _ ≤ t.2 * ((rest.map Prod.snd).prod * energy G x) :=
          mul_le_mul_of_nonneg_left (ih hrest x) ht.1
      _ = t.2 * (rest.map Prod.snd).prod * energy G x := by ring

/-- [proved-derived; formal-checked] **The consumer equation: the certified growth in a reference
form.** With `γ_lo Q ⪯ G ⪯ γ_hi Q`, `γ_lo > 0`, `ρ² ≥ 0` and the certificate,
`E_Q(Mᵐ x) ≤ (γ_hi/γ_lo) ρ^(2m) E_Q(x)`. -/
theorem floquet_metric_change {G Q M : Matrix n n ℝ} {ρ2 γlo γhi : ℝ} (hρ : 0 ≤ ρ2)
    (hlo : 0 < γlo) (hbelow : ∀ x, γlo * energy Q x ≤ energy G x)
    (habove : ∀ x, energy G x ≤ γhi * energy Q x) (hcert : FloquetCertifies G M ρ2) (m : ℕ)
    (x : n → ℝ) :
    energy Q ((M ^ m) *ᵥ x) ≤ γhi / γlo * ρ2 ^ m * energy Q x := by
  have h1 := hbelow ((M ^ m) *ᵥ x)
  have h2 := floquet_energy_iterate hρ hcert m x
  have h3 := habove x
  have hp : 0 ≤ ρ2 ^ m := pow_nonneg hρ m
  have h4 : ρ2 ^ m * energy G x ≤ ρ2 ^ m * (γhi * energy Q x) := mul_le_mul_of_nonneg_left h3 hp
  have key : γlo * energy Q ((M ^ m) *ᵥ x) ≤ ρ2 ^ m * (γhi * energy Q x) := by linarith
  have e : γhi / γlo * ρ2 ^ m * energy Q x = ρ2 ^ m * (γhi * energy Q x) / γlo := by
    field_simp
  rw [e, le_div_iff₀ hlo]
  linarith

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] **A partial period's factor is at most the largest tick's
power**: ticks each certified at `0 ≤ σ_t² ≤ σ²` have `∏ σ_t² ≤ (σ²)^k` over `k` ticks. -/
theorem partial_period_le_pow (ticks : List (Matrix n n ℝ × ℝ)) {σ2 : ℝ}
    (h : ∀ t ∈ ticks, 0 ≤ t.2 ∧ t.2 ≤ σ2) :
    (ticks.map Prod.snd).prod ≤ σ2 ^ ticks.length := by
  induction ticks with
  | nil => simp
  | cons t rest ih =>
    have ht := h t List.mem_cons_self
    have hrest : ∀ u ∈ rest, 0 ≤ u.2 ∧ u.2 ≤ σ2 := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have hprod : 0 ≤ (rest.map Prod.snd).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
        exact (hrest u hu).1
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul ht.2 (ih hrest) hprod (ht.1.trans ht.2)

/-- [proved-derived; formal-checked] **The reach over a span from any pump phase** (the consumer's
factor, `hnn::ring::FloquetBound::reach`). A span of ticks starting at an unread pump phase is a
partial period `Pre` up to the phase where the certified period starts, `m` whole periods `M`, and
a partial period `Post`; with each partial product certified in `G` (`floquet_tick_product`, bounded
by `partial_period_le_pow`) and the metric's equivalence to the reference form,
`E_Q(Post Mᵐ Pre x) ≤ (γ_hi/γ_lo) σ_post ρ^(2m) σ_pre E_Q(x)`. The machine's reach is the largest of
these over the `T` phases the span can start at, `max_o ρ^(2m_o) (max_t σ_t²)^(s − T m_o)`. -/
theorem floquet_span_reach {G Q M Pre Post : Matrix n n ℝ} {ρ2 σpre σpost γlo γhi : ℝ}
    (hρ : 0 ≤ ρ2) (hpre0 : 0 ≤ σpre) (hpost0 : 0 ≤ σpost) (hlo : 0 < γlo)
    (hbelow : ∀ x, γlo * energy Q x ≤ energy G x) (habove : ∀ x, energy G x ≤ γhi * energy Q x)
    (hcert : FloquetCertifies G M ρ2)
    (hpre : ∀ x, energy G (Pre *ᵥ x) ≤ σpre * energy G x)
    (hpost : ∀ x, energy G (Post *ᵥ x) ≤ σpost * energy G x) (m : ℕ) (x : n → ℝ) :
    energy Q ((Post * M ^ m * Pre) *ᵥ x) ≤ γhi / γlo * (σpost * ρ2 ^ m * σpre) * energy Q x := by
  have hp : 0 ≤ ρ2 ^ m := pow_nonneg hρ m
  have hfactor : 0 ≤ σpost * ρ2 ^ m * σpre := mul_nonneg (mul_nonneg hpost0 hp) hpre0
  have hG : energy G ((Post * M ^ m * Pre) *ᵥ x) ≤ σpost * ρ2 ^ m * σpre * energy G x := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    calc energy G (Post *ᵥ ((M ^ m) *ᵥ (Pre *ᵥ x)))
        ≤ σpost * energy G ((M ^ m) *ᵥ (Pre *ᵥ x)) := hpost _
      _ ≤ σpost * (ρ2 ^ m * energy G (Pre *ᵥ x)) :=
          mul_le_mul_of_nonneg_left (floquet_energy_iterate hρ hcert m _) hpost0
      _ ≤ σpost * (ρ2 ^ m * (σpre * energy G x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpre x) hp) hpost0
      _ = σpost * ρ2 ^ m * σpre * energy G x := by ring
  have h1 := hbelow ((Post * M ^ m * Pre) *ᵥ x)
  have h3 := mul_le_mul_of_nonneg_left (habove x) hfactor
  have key : γlo * energy Q ((Post * M ^ m * Pre) *ᵥ x) ≤
      σpost * ρ2 ^ m * σpre * (γhi * energy Q x) := by linarith
  have e : γhi / γlo * (σpost * ρ2 ^ m * σpre) * energy Q x =
      σpost * ρ2 ^ m * σpre * (γhi * energy Q x) / γlo := by
    field_simp
  rw [e, le_div_iff₀ hlo]
  linarith

end Certificate

/-! ## 2. The pump's axes, the bifurcation and phase-sensitive amplification -/

section Axes

/-- [definition] **The pumped node stiffness** `kI − 2p [[cos ψ, sin ψ], [sin ψ, −cos ψ]]` with the
pump carrier written through its axis `a = (c, s) = e^{iψ/2}`: `cos ψ = c² − s²`, `sin ψ = 2cs`. -/
def pumpedStiffness (k p c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![k - 2 * p * (c ^ 2 - s ^ 2), -2 * p * (2 * c * s); -2 * p * (2 * c * s),
    k + 2 * p * (c ^ 2 - s ^ 2)]

/-- [proved-derived; formal-checked] **The in-phase axis softens**: `K a = (k − 2p) a`. The standing
pump's bifurcation is `k − 2p = 0`. -/
theorem pumped_inphase_axis {k p c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    pumpedStiffness k p c s *ᵥ ![c, s] = (k - 2 * p) • ![c, s] := by
  ext i
  fin_cases i <;> simp [pumpedStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination (-2 * p * c) * h
  · linear_combination (-2 * p * s) * h

/-- [proved-derived; formal-checked] **The quadrature stiffens**: `K (ia) = (k + 2p) (ia)`. -/
theorem pumped_quadrature_axis {k p c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    pumpedStiffness k p c s *ᵥ ![-s, c] = (k + 2 * p) • ![-s, c] := by
  ext i
  fin_cases i <;> simp [pumpedStiffness, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination (-2 * p * s) * h
  · linear_combination (2 * p * c) * h

/-- [definition] **The in-phase rate matrix past the bifurcation** (unit capacity, stiffness
`−κ²`): `d/dt (u_∥, w_∥) = [[0, 1], [κ², 0]] (u_∥, w_∥)`. -/
def inphaseGenerator (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; κ ^ 2, 0]

/-- [definition] **The quadrature's rate matrix** (stiffness `ω²`). -/
def quadratureGenerator (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -ω ^ 2, 0]

/-- [proved-derived; formal-checked] **The growing quadrature**: `(1, κ)` grows at `+κ`. -/
theorem inphase_growing (κ : ℝ) : inphaseGenerator κ *ᵥ ![1, κ] = κ • ![1, κ] := by
  ext i
  fin_cases i
  · simp [inphaseGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [inphaseGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- [proved-derived; formal-checked] **The squeezed quadrature**: `(1, −κ)` decays at `−κ`. -/
theorem inphase_squeezed (κ : ℝ) : inphaseGenerator κ *ᵥ ![1, -κ] = (-κ) • ![1, -κ] := by
  ext i
  fin_cases i
  · simp [inphaseGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [inphaseGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- [proved-derived; formal-checked] **The growing amplitude is the covector `(κ, 1)`**:
`(κ, 1) A = κ (κ, 1)`, so the lock reads `κ u_∥ + w_∥`, the input's in-phase projection. -/
theorem inphase_growing_coordinate (κ : ℝ) :
    ![κ, 1] ᵥ* inphaseGenerator κ = κ • ![κ, 1] := by
  ext i
  fin_cases i
  · simp [inphaseGenerator, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [inphaseGenerator, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **The quadrature turns**: `A_⊥² = −ω² I`. -/
theorem quadrature_turns (ω : ℝ) : quadratureGenerator ω ^ 2 = -(ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadratureGenerator, sq, Matrix.mul_apply, Fin.sum_univ_two]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **The Cayley tick keeps an eigen-axis**: if `A v = λ v` and
`2 − hλ ≠ 0`, then `(1 − (h/2)A)(μ v) = (1 + (h/2)A) v` with `μ = (2 + hλ)/(2 − hλ)`. -/
theorem cayley_eigen (A : Matrix n n ℝ) (v : n → ℝ) {ev h : ℝ} (hA : A *ᵥ v = ev • v)
    (hden : 2 - h * ev ≠ 0) :
    (1 - (h / 2) • A) *ᵥ (((2 + h * ev) / (2 - h * ev)) • v) = (1 + (h / 2) • A) *ᵥ v := by
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, hA]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- [proved-derived; formal-checked] **The Cayley tick's multiplier on an eigen-axis**: with the
tick's denominator invertible, `U v = ((2 + hλ)/(2 − hλ)) v` for
`U = (1 − (h/2)A)⁻¹ (1 + (h/2)A)`. -/
theorem cayley_tick_eigen (A : Matrix n n ℝ) (v : n → ℝ) {ev h : ℝ} (hA : A *ᵥ v = ev • v)
    (hden : 2 - h * ev ≠ 0) (hdet : IsUnit (1 - (h / 2) • A).det) :
    ((1 - (h / 2) • A)⁻¹ * (1 + (h / 2) • A)) *ᵥ v = ((2 + h * ev) / (2 - h * ev)) • v := by
  rw [← Matrix.mulVec_mulVec, ← cayley_eigen A v hA hden, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

end Axes

/-! ## 3. The standing pump's bifurcation in the executed tick -/

section Standing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **The multiplier one is where the stiffness is singular.** At
the law's solve with no drive (`M ω = 2C w − h K u`), `h ≠ 0`, the executed tick fixes `(u, w)`
exactly when `ω = 0`, `w = 0` and `K u = 0`. -/
theorem standing_fixed_point_iff (C D K : E →L[ℝ] E) {Y h : ℝ} (hh : h ≠ 0) {u w ω : E}
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w 0) :
    (u + h • ω = u ∧ (2 : ℝ) • ω - w = w) ↔ (ω = 0 ∧ w = 0 ∧ K u = 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hω : ω = 0 := by
      have : h • ω = 0 := by simpa using h1
      exact (smul_eq_zero.mp this).resolve_left hh
    subst hω
    have hw : w = 0 := by
      have : (2 : ℝ) • w = 0 := by
        rw [smul_zero, zero_sub] at h2
        rw [two_smul]
        nth_rewrite 1 [← h2]
        simp
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    subst hw
    refine ⟨rfl, rfl, ?_⟩
    simp only [ringRight, map_zero, smul_zero, zero_sub, add_zero] at hsolve
    have : h • K u = 0 := by
      have := hsolve.symm
      rw [neg_eq_zero] at this
      exact this
    exact (smul_eq_zero.mp this).resolve_left hh
  · rintro ⟨rfl, rfl, -⟩
    simp

/-- [proved-derived; formal-checked] **Below the bifurcation the storage form certifies
passivity**: at the law's solve with no drive, `D ⪰ 0`, `Y > 0` and `h ≥ 0`, the executed tick
does not raise `E_Q` (composed from `HNN/Ring.ring_tick_port_balance` at `β = 0`). With
`K ≻ 0` the form `E_Q` is itself a Floquet certificate at `ρ = 1`. -/
theorem storage_form_certifies_passive (C D K : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) (hD : ∀ x, 0 ≤ inner ℝ x (D x)) {Y h : ℝ}
    (hY : 0 < Y) (hh : 0 ≤ h) {u w ω : E}
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w 0) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) ≤ contactEnergy C K u w := by
  have hb := ring_tick_port_balance C D K hC hK (h := h) hY.ne' u w 0 ω
  rw [hsolve, sub_self, inner_zero_right, add_zero] at hb
  have h1 : 0 ≤ h * inner ℝ ω (D ω) := mul_nonneg hh (hD ω)
  have h2 : 0 ≤ h * Y / 4 * ‖ringOut Y 0 ω‖ ^ 2 := by positivity
  have h0 : ‖(0 : E)‖ ^ 2 = 0 := by simp
  rw [h0] at hb
  nlinarith

end Standing

/-! ## 4. Two pumps compose to a turn by their relative phase -/

section Relative

variable {R : Type*} [CommRing R]

/-- [definition] **The pump's block is a reflection** `R_ψ = [[c, s], [s, −c]]` at the carrier
`(c, s) = (cos ψ, sin ψ)` (the node block is `−2p R_ψ`). -/
def reflection (c s : R) : Matrix (Fin 2) (Fin 2) R := !![c, s; s, -c]

/-- [proved-derived; formal-checked] A pump's reflection squares to one on the circle. -/
theorem reflection_sq {c s : R} (h : c ^ 2 + s ^ 2 = 1) : reflection c s * reflection c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h | ring

/-- [proved-derived; formal-checked] **Two pumps compose to the turn by their relative phase**:
`R_ψ R_χ = [[cc′ + ss′, cs′ − sc′], [sc′ − cs′, cc′ + ss′]]`, the rotation by `ψ − χ`. -/
theorem reflection_mul_reflection (c s c' s' : R) :
    reflection c s * reflection c' s' =
      !![c * c' + s * s', c * s' - s * c'; s * c' - c * s', c * c' + s * s'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflection, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [proved-derived; formal-checked] **The pair's trace reads the relative phase**:
`tr(R_ψ R_χ) = 2(cc′ + ss′)`. -/
theorem reflection_pair_trace (c s c' s' : R) :
    (reflection c s * reflection c' s').trace = 2 * (c * c' + s * s') := by
  rw [reflection_mul_reflection, Matrix.trace_fin_two]
  simp
  ring

/-- [proved-derived; formal-checked] In carriers: `tr(R_u R_u′) = 2 Re(u ū′)`, the relative
pairing of the two pump carriers. -/
theorem reflection_pair_trace_carriers (u u' : ℂ) :
    (reflection u.re u.im * reflection u'.re u'.im).trace = 2 * (u * star u').re := by
  rw [reflection_pair_trace]
  simp [Complex.mul_re]

end Relative

/-! ## 5. No linear threshold reads a relative phase -/

section Parity

/-- [definition] **The relative pairing of two cells** `Re(z_a z̄_b)`: `|z_a||z_b| cos(φ_a − φ_b)`. -/
def relativePairing (za zb : ℂ) : ℝ := (za * star zb).re

/-- [proved-derived; formal-checked] **The relative pairing is blind to the global half-turn.** -/
theorem relativePairing_halfTurn (za zb : ℂ) :
    relativePairing (-za) (-zb) = relativePairing za zb := by
  simp [relativePairing]

/-- [proved-derived; formal-checked] **No linear reading followed by a threshold reads a relative
phase**: a linear map is odd under the global half-turn and the relative pairing is even, so no
`L` has `0 < L(z_a, z_b) ⇔ 0 < Re(z_a z̄_b)` for every pair. -/
theorem no_linear_threshold_reads_relative_phase (L : ℂ × ℂ →ₗ[ℝ] ℝ) :
    ¬ ∀ za zb : ℂ, (0 < L (za, zb) ↔ 0 < relativePairing za zb) := by
  intro h
  have h1 := (h 1 1).mpr (by simp [relativePairing])
  have h2 := (h (-1) (-1)).mpr (by simp [relativePairing])
  have hneg : L (-1, -1) = -L (1, 1) := by
    rw [← map_neg]
    rfl
  linarith

end Parity

section Floor

/-- A product of finitely many values in `[0, 1)`, at least one, is below one. -/
theorem multiset_prod_lt_one (s : Multiset ℝ) (hs : s ≠ 0) (h0 : ∀ x ∈ s, 0 ≤ x)
    (h1 : ∀ x ∈ s, x < 1) : s.prod < 1 := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    rw [Multiset.prod_cons]
    have ha0 := h0 a (Multiset.mem_cons_self a s)
    have ha1 := h1 a (Multiset.mem_cons_self a s)
    have hs0 : 0 ≤ s.prod := Multiset.prod_nonneg fun x hx => h0 x (Multiset.mem_cons_of_mem hx)
    have hs1 : s.prod ≤ 1 := by
      by_cases he : s = 0
      · simp [he]
      · exact (ih he (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
          (fun x hx => h1 x (Multiset.mem_cons_of_mem hx))).le
    nlinarith

/-- [proved-derived; formal-checked] **An invertible integer monodromy has a multiplier of modulus
at least one**: so `M = N/Δ` has `ρ(M) ≥ 1/Δ`, the lattice's floor on a reading. -/
theorem integer_monodromy_floor {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (N : Matrix m m ℤ) (hN : N.det ≠ 0) :
    ∃ μ ∈ (N.map (Int.castRingHom ℂ)).charpoly.roots, 1 ≤ ‖μ‖ := by
  set M := N.map (Int.castRingHom ℂ)
  have hdet : M.det = M.charpoly.roots.prod :=
    Matrix.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)
  have hMdet : M.det = ((N.det : ℤ) : ℂ) := by
    simp only [M]
    exact ((Int.castRingHom ℂ).map_det N).symm
  have hcard : M.charpoly.roots.card = Fintype.card m := by
    rw [← M.charpoly_natDegree_eq_dim]
    exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))
  by_contra hcon
  push Not at hcon
  have hnorm : ‖M.det‖ = (M.charpoly.roots.map (‖·‖)).prod := by
    rw [hdet]
    exact Multiset.prod_hom M.charpoly.roots (normHom (α := ℂ)) |>.symm
  have hge : (1 : ℝ) ≤ ‖M.det‖ := by
    rw [hMdet, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hN
  have hne : M.charpoly.roots.map (‖·‖) ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    simp [hcard, Fintype.card_ne_zero] at this
  have hlt := multiset_prod_lt_one _ hne
    (fun x hx => by obtain ⟨μ, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg μ)
    (fun x hx => by obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx; exact hcon μ hμ)
  linarith

end Floor

section Audit

#print axioms energy_transport
#print axioms certificate_reading
#print axioms floquet_energy_step
#print axioms floquet_energy_iterate
#print axioms floquet_passive
#print axioms floquet_tick_product
#print axioms floquet_metric_change
#print axioms partial_period_le_pow
#print axioms floquet_span_reach
#print axioms pumped_inphase_axis
#print axioms pumped_quadrature_axis
#print axioms inphase_growing
#print axioms inphase_squeezed
#print axioms inphase_growing_coordinate
#print axioms quadrature_turns
#print axioms cayley_eigen
#print axioms cayley_tick_eigen
#print axioms standing_fixed_point_iff
#print axioms storage_form_certifies_passive
#print axioms reflection_sq
#print axioms reflection_mul_reflection
#print axioms reflection_pair_trace
#print axioms reflection_pair_trace_carriers
#print axioms relativePairing_halfTurn
#print axioms no_linear_threshold_reads_relative_phase
#print axioms integer_monodromy_floor

end Audit

end Holonics.HNN.Floquet
