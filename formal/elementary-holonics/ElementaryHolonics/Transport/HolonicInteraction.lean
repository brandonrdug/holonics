import ElementaryHolonics.Millennium.HolonicSnellInteraction
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The Holonic Interaction unit: a medium's contact exchange and its derived modal response

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/holonic_interaction.rs` implements. It is the **medium and contact**
half of the Holonic Interaction subject named in
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`; the derivation it
formalizes is the linear dissipative specialization written out in
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md` under "The general embedding and its
consuming composition".

The unit is the four bodies of the 2026-08-14 record: `|source⟩` emanating current, a STANDING
intermediary medium `H_int`, a DYNAMIC modulating field `H_pert`, and `⟨perspective|` — a
participating receiver with its own aperture. This file carries the *medium*: what its contact
faces exchange, and what its storage form's rate is.

## The contact form

With face `f` carrying an exact slip map `J_f` (relative slip `s_f = J_f v`), a constitutive
traction `t_f = −D_f s_f` and a declared positive weight `w_f` (its area/measure),

```text
   M_contact = Σ_f w_f J_fᵀ D_f J_f,        P_diss(v) = ⟨v, M_contact v⟩.
```

* `contactForm_nonneg` is `P_diss ≥ 0` from `D_f` positive semidefinite and `w_f ≥ 0`. Nothing
  here assumes `D_f` definite, and nothing assumes the medium's storage form `G` definite.
* `contactForm_quad_eq_zero_iff` characterizes the null cone face by face; under face
  definiteness `contactForm_quad_eq_zero_iff_no_slip` and `contactForm_kernel_iff` identify it
  with **the motions of zero slip on every dissipative face**, which is the kernel of the
  operator and not merely of the quadratic reading.
* `clockedEnergy` is `⟨δq, M_contact δq⟩ / h`: a position edit is not an energy until its clock
  is declared. `clockedEnergy_eq_duration_times_power` is the derivation — the energy dissipated
  over a duration `h > 0` at the constant velocity `v = δq/h`. T4's generic `W²`
  (`Transport/EditRigidity.lean::rethreadingWork`) is an authored edit metric's squared norm and
  is **not** automatically this energy; the Rust owner returns a typed comparison rather than a
  boolean.

## The port-Hamiltonian generator and its storage rate

[agent-inferred] The medium's local linear dynamics is taken in the port-Hamiltonian form
`q̇ = (Ω − M) G q + B u` with `G` the symmetric storage form (possibly indefinite), `Ω` skew and
`M` the contact dissipation form. This is inferred from the mathematics rather than declared by
the contract: `Ω` skew and `M` symmetric is exactly the splitting that makes the rate of the
storage reading `E_G = ½ ⟨q, G q⟩` equal to `−2` times the dissipated power and nothing else, and
it is the only splitting in which the contact form assembled above enters the generator as itself.

`port_storage_rate` is the identity

```text
   Aᵀ G + G A = −2 G M G            for A = (Ω − M) G, Gᵀ = G, Ωᵀ = −Ω, Mᵀ = M,
```

so `Foundation/CausalChord.lean::rateForm` — of which `rateFormQ` is the rational specialization,
the conjugate transpose being the transpose over `ℚ` — reads the medium's dissipation off the
generator. `port_storage_rate_zero_of_no_dissipation` is conservation at `M = 0`;
`storage_rate_reading` evaluates the rate at a motion as `−2 · P_diss(G v)`, and
`storage_rate_neg_of_active_slip` is strict decay exactly on the slip-active subspace.

## The defect this file refuses to hide

`indefiniteStorage_rate_form_vanishes` with `swapGenerator_has_a_right_half_plane_mode`:
`G = diag(1, −1)` and `A = [[0,1],[1,0]]` have `Aᵀ G + G A = 0` while `A` has the eigenvalue `+1`.
**A vanishing rate form licenses no spectral placement without positive definiteness of `G`.**
The Rust owner's spectral reading is therefore a typed two-armed return guarded by
`crate::inertia::inertia`, never a boolean.

## The interface between two media

Tangential agreement at the shared face of two consecutive media, with its retained normal
remainder, is already owned by `HolonicSnellInteraction.lean`
(`snellCompatible_iff`, `tangentialConservation_retainsNormalRemainder`,
`finiteInterfaceChain_eq_exterior` for a finite chain of such interfaces).
`interface_tangential_agreement_retains_normal_remainder` is that owner's statement in the form
this chain consumes: Snell compatibility is a condition on the tangential face alone, and the
normal face carries an explicit nonzero remainder across it. The discrete normal-jump/source half
is `Transport/JunctionLaw.lean::balanced_iff_divergence`, composed in Rust through
`crate::junction_law::check_junction`.

Truth status: every theorem below is `[proved-derived; formal-checked]` over exact rational
matrices; the port-Hamiltonian *form* is `[agent-inferred]` as stated above. No `sorry`.
-/

namespace Soma.Holonics.Transport.HolonicInteraction

open Matrix

variable {n r m : ℕ}

/-! ## 1. The quadratic reading -/

/-- [definition] The exact quadratic reading of a form at a motion: `⟨v, M v⟩`. -/
def quad (M : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) : ℚ := v ⬝ᵥ (M *ᵥ v)

/-- [proved-derived; formal-checked] The reading is additive in the form. -/
theorem quad_add (X Y : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    quad (X + Y) v = quad X v + quad Y v := by
  simp [quad, Matrix.add_mulVec, dotProduct_add]

/-- [proved-derived; formal-checked] The reading negates with the form. -/
theorem quad_neg (X : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ) :
    quad (-X) v = -quad X v := by
  simp [quad, Matrix.neg_mulVec, dotProduct_neg]

/-- [proved-derived; formal-checked] The reading is quadratic in the motion. -/
theorem quad_smul (M : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (v : Fin n → ℚ) :
    quad M (c • v) = c ^ 2 * quad M v := by
  simp only [quad, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-! ## 2. The contact form `M_contact = Σ_f w_f J_fᵀ D_f J_f` -/

/-- [definition] One contact face's contribution: its declared weight times the pullback of its
constitutive response along its slip map. -/
def faceForm (w : ℚ) (J : Matrix (Fin r) (Fin n) ℚ) (D : Matrix (Fin r) (Fin r) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  w • (Jᵀ * D * J)

/-- [definition] The configuration-space dissipation form assembled from a finite population of
contact faces. -/
def contactForm (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  ∑ f : Fin m, faceForm (w f) (J f) (D f)

/-- [proved-derived; formal-checked] **The adjoint identity.** One face's quadratic reading at a
motion is its constitutive response read at that motion's slip. This is the substitution step of
the carrier plan's derivation. -/
theorem quad_faceForm (w : ℚ) (J : Matrix (Fin r) (Fin n) ℚ) (D : Matrix (Fin r) (Fin r) ℚ)
    (v : Fin n → ℚ) :
    quad (faceForm w J D) v = w * ((J *ᵥ v) ⬝ᵥ (D *ᵥ (J *ᵥ v))) := by
  have congruent : v ⬝ᵥ ((Jᵀ * D * J) *ᵥ v) = (J *ᵥ v) ⬝ᵥ (D *ᵥ (J *ᵥ v)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [quad, faceForm, Matrix.smul_mulVec, dotProduct_smul, congruent, smul_eq_mul]

/-- [proved-derived; formal-checked] `P_diss(v) = Σ_f w_f ⟨s_f, D_f s_f⟩` with `s_f = J_f v`. -/
theorem quad_contactForm (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) (v : Fin n → ℚ) :
    quad (contactForm w J D) v
      = ∑ f : Fin m, w f * ((J f *ᵥ v) ⬝ᵥ (D f *ᵥ (J f *ᵥ v))) := by
  rw [quad, contactForm, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun f _ => quad_faceForm (w f) (J f) (D f) v

/-- [proved-derived; formal-checked] **`P_diss ≥ 0`**: the dissipation form is positive
semidefinite whenever every face response is positive semidefinite in the declared pairing and
every declared weight is nonnegative. Nothing about the medium's storage form is used. -/
theorem contactForm_nonneg (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) (hw : ∀ f, 0 ≤ w f)
    (hD : ∀ (f : Fin m) (s : Fin r → ℚ), 0 ≤ s ⬝ᵥ (D f *ᵥ s)) (v : Fin n → ℚ) :
    0 ≤ quad (contactForm w J D) v := by
  rw [quad_contactForm]
  exact Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hD f _)

/-- [proved-derived; formal-checked] **The null cone, face by face.** With strictly positive
weights, no dissipation is read exactly when every face's own reading of its slip vanishes. -/
theorem contactForm_quad_eq_zero_iff (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) (hw : ∀ f, 0 < w f)
    (hD : ∀ (f : Fin m) (s : Fin r → ℚ), 0 ≤ s ⬝ᵥ (D f *ᵥ s)) (v : Fin n → ℚ) :
    quad (contactForm w J D) v = 0
      ↔ ∀ f, (J f *ᵥ v) ⬝ᵥ (D f *ᵥ (J f *ᵥ v)) = 0 := by
  rw [quad_contactForm]
  have nonneg : ∀ g ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ w g * ((J g *ᵥ v) ⬝ᵥ (D g *ᵥ (J g *ᵥ v))) :=
    fun g _ => mul_nonneg (hw g).le (hD g _)
  constructor
  · intro vanishes f
    have term := (Finset.sum_eq_zero_iff_of_nonneg nonneg).mp vanishes f (Finset.mem_univ f)
    rcases mul_eq_zero.mp term with weight | reading
    · exact absurd weight (ne_of_gt (hw f))
    · exact reading
  · intro faces
    exact Finset.sum_eq_zero fun f _ => by rw [faces f, mul_zero]

/-- [proved-derived; formal-checked] **The kernel is the zero-slip motions.** When every face
response is definite on its face — a *dissipative* face — no dissipation is read exactly when the
motion slips on no face at all. -/
theorem contactForm_quad_eq_zero_iff_no_slip (w : Fin m → ℚ)
    (J : Fin m → Matrix (Fin r) (Fin n) ℚ) (D : Fin m → Matrix (Fin r) (Fin r) ℚ)
    (hw : ∀ f, 0 < w f) (hD : ∀ (f : Fin m) (s : Fin r → ℚ), 0 ≤ s ⬝ᵥ (D f *ᵥ s))
    (hdefinite : ∀ (f : Fin m) (s : Fin r → ℚ), s ⬝ᵥ (D f *ᵥ s) = 0 → s = 0) (v : Fin n → ℚ) :
    quad (contactForm w J D) v = 0 ↔ ∀ f, J f *ᵥ v = 0 := by
  rw [contactForm_quad_eq_zero_iff w J D hw hD v]
  constructor
  · intro faces f
    exact hdefinite f _ (faces f)
  · intro faces f
    rw [faces f]
    simp

/-- [proved-derived; formal-checked] A motion that slips on no face is annihilated by the whole
assembled operator, not merely by its quadratic reading. -/
theorem contactForm_mulVec_eq_zero_of_no_slip (w : Fin m → ℚ)
    (J : Fin m → Matrix (Fin r) (Fin n) ℚ) (D : Fin m → Matrix (Fin r) (Fin r) ℚ)
    {v : Fin n → ℚ} (hslip : ∀ f, J f *ᵥ v = 0) :
    contactForm w J D *ᵥ v = 0 := by
  rw [contactForm, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [faceForm, Matrix.smul_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hslip f]
  simp

/-- [proved-derived; formal-checked] **The kernel characterization.** Over dissipative faces the
operator's kernel, the quadratic reading's null cone and the zero-slip motions are one set. -/
theorem contactForm_kernel_iff (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) (hw : ∀ f, 0 < w f)
    (hD : ∀ (f : Fin m) (s : Fin r → ℚ), 0 ≤ s ⬝ᵥ (D f *ᵥ s))
    (hdefinite : ∀ (f : Fin m) (s : Fin r → ℚ), s ⬝ᵥ (D f *ᵥ s) = 0 → s = 0) (v : Fin n → ℚ) :
    contactForm w J D *ᵥ v = 0 ↔ ∀ f, J f *ᵥ v = 0 := by
  constructor
  · intro annihilated
    refine (contactForm_quad_eq_zero_iff_no_slip w J D hw hD hdefinite v).mp ?_
    rw [quad, annihilated, dotProduct_zero]
  · exact fun hslip => contactForm_mulVec_eq_zero_of_no_slip w J D hslip

/-! ## 3. The clocked edit energy -/

/-- [definition] The energy a position edit dissipates against a contact form over a declared
duration. **A position edit is not an energy until its clock is declared**; `h` is that clock. -/
def clockedEnergy (M : Matrix (Fin n) (Fin n) ℚ) (h : ℚ) (dq : Fin n → ℚ) : ℚ :=
  quad M dq / h

/-- [proved-derived; formal-checked] **The clocked energy identity.** Over an interval of duration
`h ≠ 0` traversed at the constant velocity `v = δq/h`, the dissipated energy `h · P_diss(v)` is
exactly `⟨δq, M δq⟩ / h`. -/
theorem clockedEnergy_eq_duration_times_power (M : Matrix (Fin n) (Fin n) ℚ) (h : ℚ)
    (hh : h ≠ 0) (dq : Fin n → ℚ) :
    clockedEnergy M h dq = h * quad M (h⁻¹ • dq) := by
  rw [clockedEnergy, quad_smul]
  field_simp

/-- [proved-derived; formal-checked] A positive semidefinite contact form and a strictly positive
clock read a nonnegative edit energy. -/
theorem clockedEnergy_nonneg {M : Matrix (Fin n) (Fin n) ℚ} {h : ℚ}
    (hM : ∀ v : Fin n → ℚ, 0 ≤ quad M v) (hh : 0 < h) (dq : Fin n → ℚ) :
    0 ≤ clockedEnergy M h dq :=
  div_nonneg (hM dq) hh.le

/-- [proved-derived; formal-checked] **The clock is not a scale that cancels.** Halving the
duration of the same edit doubles the energy: the reading depends on the declared clock and a
receipt that omits it names no energy. -/
theorem clockedEnergy_scales_inversely (M : Matrix (Fin n) (Fin n) ℚ) {h : ℚ} (hh : h ≠ 0)
    (dq : Fin n → ℚ) :
    clockedEnergy M (h / 2) dq = 2 * clockedEnergy M h dq := by
  rw [clockedEnergy, clockedEnergy]
  field_simp

/-! ## 4. The port-Hamiltonian generator and its storage rate -/

/-- [definition] The rate form over `ℚ`. This is the rational specialization of
`Foundation/CausalChord.lean::rateForm`, whose conjugate transpose is the transpose here. -/
def rateFormQ (A G : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ := Aᵀ * G + G * A

/-- [definition] The port-Hamiltonian generator `A = (Ω − M) G`: a skew structure `Ω`, the contact
dissipation `M`, acting on the storage form `G`. -/
def portGenerator (Omega M G : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (Omega - M) * G

/-- [proved-derived; formal-checked] **The storage-rate identity.**
`Aᵀ G + G A = −2 G M G` for `A = (Ω − M) G` with `G` symmetric, `Ω` skew and `M` symmetric. The
skew part cancels exactly; the dissipation is all that survives. -/
theorem port_storage_rate (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) :
    rateFormQ (portGenerator Omega M G) G = -(G * M * G) - G * M * G := by
  have adjoint : (portGenerator Omega M G)ᵀ = G * (-Omega - M) := by
    rw [portGenerator, Matrix.transpose_mul, Matrix.transpose_sub, hOmega, hM, hG]
  rw [rateFormQ, adjoint, portGenerator]
  noncomm_ring

/-- [proved-derived; formal-checked] The same identity with the scalar in front. -/
theorem port_storage_rate_smul (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) :
    rateFormQ (portGenerator Omega M G) G = (-2 : ℚ) • (G * M * G) := by
  rw [port_storage_rate Omega M G hG hOmega hM]
  module

/-- [proved-derived; formal-checked] **Conservation.** With no contact dissipation the storage
form's rate is exactly zero — for any storage form, definite or not. -/
theorem port_storage_rate_zero_of_no_dissipation (Omega G : Matrix (Fin n) (Fin n) ℚ)
    (hG : Gᵀ = G) (hOmega : Omegaᵀ = -Omega) :
    rateFormQ (portGenerator Omega 0 G) G = 0 := by
  have identity := port_storage_rate Omega 0 G hG hOmega (Matrix.transpose_zero)
  simpa using identity

/-- [proved-derived; formal-checked] The congruence `⟨v, G M G v⟩ = ⟨G v, M (G v)⟩` for symmetric
`G`: the dissipation the storage reading sees is the contact dissipation at the co-motion. -/
theorem quad_congruence (M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G) (v : Fin n → ℚ) :
    quad (G * M * G) v = quad M (G *ᵥ v) := by
  rw [quad, quad, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG]

/-- [proved-derived; formal-checked] **The rate at a motion is minus twice the dissipated power at
its co-motion.** This is the statement `causal_chord::rate_form` is read through. -/
theorem storage_rate_reading (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) (v : Fin n → ℚ) :
    quad (rateFormQ (portGenerator Omega M G) G) v = -2 * quad M (G *ᵥ v) := by
  rw [port_storage_rate Omega M G hG hOmega hM, sub_eq_add_neg, quad_add, quad_neg,
    quad_congruence M G hG]
  ring

/-- [proved-derived; formal-checked] The storage reading never grows against a positive
semidefinite contact form. -/
theorem storage_rate_nonpos (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M)
    (hMpsd : ∀ s : Fin n → ℚ, 0 ≤ quad M s) (v : Fin n → ℚ) :
    quad (rateFormQ (portGenerator Omega M G) G) v ≤ 0 := by
  rw [storage_rate_reading Omega M G hG hOmega hM]
  have := hMpsd (G *ᵥ v)
  linarith

/-- [proved-derived; formal-checked] **Strict decay exactly on the slip-active subspace.** -/
theorem storage_rate_neg_of_active_slip (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) {v : Fin n → ℚ}
    (hactive : 0 < quad M (G *ᵥ v)) :
    quad (rateFormQ (portGenerator Omega M G) G) v < 0 := by
  rw [storage_rate_reading Omega M G hG hOmega hM]
  linarith

/-! ## 5. The defect: a vanishing rate form places no spectrum without a definite storage form -/

/-- [definition] The indefinite storage form `diag(1, −1)`. -/
def indefiniteStorage : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- [definition] The exchange generator `[[0,1],[1,0]]`, whose spectrum is `{+1, −1}`. -/
def swapGenerator : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

/-- [proved-derived; formal-checked] The storage form is indefinite: it reads `+1` on one
coordinate and `−1` on the other. -/
theorem indefiniteStorage_is_indefinite :
    quad indefiniteStorage ![1, 0] = 1 ∧ quad indefiniteStorage ![0, 1] = -1 := by
  constructor <;>
    simp [quad, indefiniteStorage, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The rate form vanishes identically. -/
theorem indefiniteStorage_rate_form_vanishes :
    rateFormQ swapGenerator indefiniteStorage = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rateFormQ, swapGenerator, indefiniteStorage, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] …and yet the generator carries an eigenvalue `+1`. -/
theorem swapGenerator_has_a_right_half_plane_mode :
    swapGenerator *ᵥ ![1, 1] = (1 : ℚ) • (![1, 1] : Fin 2 → ℚ) := by
  ext i
  fin_cases i <;> simp [swapGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **No spectral placement without positive definiteness.**
A vanishing rate form together with an indefinite storage form is consistent with a mode that
grows. Any API that reads decay off `Aᵀ G + G A = 0` alone is refuted by this pair. -/
theorem vanishing_rate_form_places_no_spectrum :
    rateFormQ swapGenerator indefiniteStorage = 0
      ∧ swapGenerator *ᵥ ![1, 1] = (1 : ℚ) • (![1, 1] : Fin 2 → ℚ)
      ∧ quad indefiniteStorage ![0, 1] < 0 :=
  ⟨indefiniteStorage_rate_form_vanishes, swapGenerator_has_a_right_half_plane_mode, by
    rw [indefiniteStorage_is_indefinite.2]; norm_num⟩

/-! ## 6. The interface between two media -/

open Soma.Holonics.Millennium.HolonicSnellInteraction in
/-- [proved-derived; formal-checked] **Tangential agreement at a shared face retains the normal
remainder.** The existing Snell owner's pair is exhibited in the form the chain of media consumes:
the interface condition is a condition on the tangential face alone, and the normal face carries
an explicit nonzero remainder across it. The finite chain of such interfaces telescopes to its
exterior difference by that owner's `finiteInterfaceChain_eq_exterior`. -/
theorem interface_tangential_agreement_retains_normal_remainder :
    ∃ incoming outgoing : PhaseOccurrence,
      SnellCompatible incoming outgoing
        ∧ normalReceiver outgoing - normalReceiver incoming ≠ 0 := by
  obtain ⟨compatible, remainder⟩ := tangentialConservation_retainsNormalRemainder
  refine ⟨⟨1, 0⟩, ⟨1, Real.pi⟩, compatible, ?_⟩
  rw [remainder]
  norm_num

/-! ## Audit

[definition] Every declaration of this file's axiom dependencies, printed by the kernel. Only
`propext`, `Classical.choice` and `Quot.sound` are acceptable; `sorryAx` appears nowhere. -/

namespace Audit

#print axioms quad_add
#print axioms quad_neg
#print axioms quad_smul
#print axioms quad_faceForm
#print axioms quad_contactForm
#print axioms contactForm_nonneg
#print axioms contactForm_quad_eq_zero_iff
#print axioms contactForm_quad_eq_zero_iff_no_slip
#print axioms contactForm_mulVec_eq_zero_of_no_slip
#print axioms contactForm_kernel_iff
#print axioms clockedEnergy_eq_duration_times_power
#print axioms clockedEnergy_nonneg
#print axioms clockedEnergy_scales_inversely
#print axioms port_storage_rate
#print axioms port_storage_rate_smul
#print axioms port_storage_rate_zero_of_no_dissipation
#print axioms quad_congruence
#print axioms storage_rate_reading
#print axioms storage_rate_nonpos
#print axioms storage_rate_neg_of_active_slip
#print axioms indefiniteStorage_is_indefinite
#print axioms indefiniteStorage_rate_form_vanishes
#print axioms swapGenerator_has_a_right_half_plane_mode
#print axioms vanishing_rate_form_places_no_spectrum
#print axioms interface_tangential_agreement_retains_normal_remainder

end Audit

end Soma.Holonics.Transport.HolonicInteraction
