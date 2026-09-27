import Holonics.HNN.Word
import Holonics.HNN.LatticeWord
import Holonics.Aeon.Clock.Epoch

/-!
# HNN.Ring: the ring's mode tick, its storage form, its pump and its clock

[definition] Rebuild step 4 (#73), campaign 2, Lean item 8 (`docs/plans/THE_REBUILD.md`, (b) and
"Campaign 2", *The ring tick*). A ring is a complex parametron: it stores, oscillates and locks. Its
declared mode storage is the form `Q = diag(K, C)` on the pair `(u, w)` of displacement and rate
(node flux and node velocity): `E_Q(u, w) = ½⟨w, C w⟩ + ½⟨u, K u⟩`, the owner's
`HNN/Propagation.contactEnergy` (one storage form for the ring and the contact). Its tick is the
midpoint (Cayley) step of `ẋ = v`, `C v̇ = −K x + f`, executed in the descriptor form that needs no
`C⁻¹`:

```text
u′ = u + h ω ,   w′ = 2ω − w                         ω the midpoint rate
M ω = 2C w + h β − h K u ,   M = 2C + (h/Y) I + h D + (h²/2) K           one port of admittance Y
β_out = β − (2/Y) ω                                   the wave returned at the port
closed, lossless:  (2C + (h²/2) K) ω = 2C w − h K u    the ring's Cayley denominator
generator form:    ż = A z ,  A = [[0, 1], [−C⁻¹K, 0]] ,  U = (1 − A_h)⁻¹(1 + A_h) ,  A_h = (h/2) A
```

[proved-derived; formal-checked] What is proved.

1. **The storage form is kept, sign included** (`cayley_forms_agree`, `cayley_preserves_form`):
   for any generator with `AᵀQ + QA = 0` (`QSkew`) and symmetric `Q`, over any commutative ring,
   the Cayley tick `U = (1 + A)(1 − A)⁻¹` has `UᵀQU = Q` whenever its denominator is a unit; no
   definiteness of `Q` is used. **The ring's generator is `Q`-skew** (`ring_generator_qSkew`) for
   `Q = diag(K, C)` with `K, C` symmetric and `C` invertible, so the ring tick keeps its mode
   energy: `UᵀQU = Q` (`ring_tick_conserves_mode_energy`), and in the descriptor form that the
   executed tick solves, `E_Q(u′, w′) = E_Q(u, w)` (`ring_descriptor_tick_conserves`), which needs
   no `C⁻¹`.
2. **The denominator** (`ring_cayley_denominator_nonsingular`): with a port of admittance `Y > 0`
   and `C, D, K ⪰ 0`, `h > 0`, the executed operator `M` satisfies `⟨v, M v⟩ ≥ (h/Y)|v|²` and every
   solve is unique; closed and lossless, `2C + (h²/2) K` is bijective when `C + K` is definite
   (`ker C ∩ ker K = 0`). The hypothesis is load-bearing: on the two-node cycle, where
   `C = K = Bᵀ B` share the harmonic (dormant) mode `(1, 1)`, the closed denominator is singular
   (`ring_harmonic_mode_singular`), which is campaign 3's dormant mode.
3. **The executed balance** (`ring_tick_port_balance`, `ring_tick_executed_energy_balance`): for
   *any* executed rate `ω` (a chart's image split on a lattice), the mode energy moves by the port
   work `(hY/4)(|β|² − |β_out|²)` minus the dissipation `h⟨ω, D ω⟩` plus the chart defect
   `⟨ω, M ω − r⟩`; with the pump's storage change `K → K′` before the tick (its work
   `½⟨u, (K′ − K) u⟩`, `Holon/Deposition.deposition_work` at a fixed state) and the split of the
   carried state (`E(û′, ŵ′) − E(u′, w′)`), the whole executed tick closes exactly. Nothing is set
   to zero.
4. **The reference change** (`two_port_reference_balance`): for positive admittances `G₀, G₁`,
   `Γ = (G₀ − G₁)/(G₀ + G₁)` and the **power** transmission fraction `T = 4G₀G₁/(G₀ + G₁)²` obey
   `Γ² + T = 1`. The junction's two-port case at a zero held wave
   (`HolonicConstitutiveCirculation.emitted`, `successorHeld`, the owner of
   `HNN/Propagation.junctionSwing_twoPort`) returns the reflected wave `Γ i` in the old reference and
   the transmitted wave `(1 + Γ) i` in the new one, whose power there, `G₁|(1 + Γ) i|²`, is
   `T · G₀|i|²`: both powers are read in one frame, and `T` is not an amplitude.
5. **Crossings are epoch ticks** (`ring_crossings_are_epoch_ticks`): along the ring's rational
   clock passage, the arrivals on its section over `N` micro-steps from residue `r < d` are
   `(r + N)/d` (`Epoch.ring_arrivals_eq_ringCrossings`, `Parametron.ringCrossings_eq`); for `d ≥ 2`
   the section is transversal, so they are a certified section cutting the passage into
   `#ticks + 1` epochs (`Epoch.epoch_count`).
6. **The pump and the sheets** (`pump_half_turn_invariant`, `pump_blind_to_sheets`,
   `locked_sheet_receiver_face`): the pump storage `−p cos(2θ − ψ)` is the node block form
   `−p((x² − y²) cos ψ + 2xy sin ψ)` read at `(x, y) = r(cos θ, sin θ)` over `r²`, invariant under
   the half-turn (`PhaseCarrier.pumpStorage_halfTurnSheet`) and equal on the two sheets of its axis;
   on locked sheets the ring population's driven phase energy is the Ising energy and the threshold
   sheet minimizes it (`Objects/Parametron.{drivenPhaseEnergy_binaryPhase, thresholdSheet_minimizes,
   sheetReading_binaryPhase}`): the perceptron is that receiver face, not the ring.

7. **The executed solve's bound and a gain's backtrack** (`abs_mulVec_le_rowNorm`,
   `abs_dot_le_l1`, `loaded_solve_chart_bound`, `loaded_state_split_bound`,
   `gain_backtrack_midpoint`; Decision 38's repair). For a chart `X̂` with certificate
   `‖1 − M X̂‖∞ ≤ δ`, a right side with `|r_i| ≤ ρ` and an executed rate within `u` of `X̂ r`,
   `|⟨ω, M ω − r⟩| ≤ ‖ω‖₁ (δ ρ + ‖M‖∞ u)`; for a symmetric form and a carried state within `u` of its
   image, the split `½⟨ŷ, Q ŷ⟩ − ½⟨y, Q y⟩` is within `(u/2)‖Q(ŷ + y)‖₁`. The chart term no longer
   absorbs a wrong solve. A gain at the positive lattice coordinate `q` backtracks to
   `quot L (q·2^(−L)/2) = ⌊(q + 1)/2⌋ ∈ [1, q]`: positive, never past the admissible side.

[open] Pump/Floquet locking (that the pumped tick selects the two sheets as attracting basins) is
not proved; the sheets are read, not asserted to attract (#62).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Ring

open Matrix
open Holonics.HNN.Propagation
open Holonics.HNN.Word
open scoped BigOperators

/-! ## 1. The Cayley tick keeps its declared storage form -/

section Cayley

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- [definition] **A generator is skew for the storage form `Q`**: `AᵀQ + QA = 0`, i.e. `QA` is
skew. It is scale invariant, so it is stated for the half-step generator `A_h = (h/2) A`. -/
def QSkew (Q A : Matrix n n R) : Prop := Aᵀ * Q + Q * A = 0

/-- [definition] The Cayley denominator `1 − A` and numerator `1 + A` of the half-step generator. -/
def cayleyDen (A : Matrix n n R) : Matrix n n R := 1 - A

/-- [definition] See `cayleyDen`. -/
def cayleyNum (A : Matrix n n R) : Matrix n n R := 1 + A

/-- [definition] **The Cayley tick** `U = (1 + A)(1 − A)⁻¹`. -/
def cayleyTick (A : Matrix n n R) : Matrix n n R := cayleyNum A * (cayleyDen A)⁻¹

omit [DecidableEq n] in
theorem QSkew.smul {Q A : Matrix n n R} (hA : QSkew Q A) (c : R) : QSkew Q (c • A) := by
  unfold QSkew at *
  rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hA, smul_zero]

/-- [proved-derived; formal-checked] **The two halves of the tick carry one form**:
`(1 − A)ᵀQ(1 − A) = (1 + A)ᵀQ(1 + A)` for a `Q`-skew generator. -/
theorem cayley_forms_agree {Q A : Matrix n n R} (hA : QSkew Q A) :
    (cayleyDen A)ᵀ * Q * cayleyDen A = (cayleyNum A)ᵀ * Q * cayleyNum A := by
  unfold cayleyDen cayleyNum
  have hsub : ((1 : Matrix n n R) - A)ᵀ = 1 - Aᵀ := by rw [transpose_sub, transpose_one]
  have hadd : ((1 : Matrix n n R) + A)ᵀ = 1 + Aᵀ := by rw [transpose_add, transpose_one]
  rw [hsub, hadd]
  have key : (1 - Aᵀ) * Q * (1 - A) = (1 + Aᵀ) * Q * (1 + A) - 2 * (Aᵀ * Q + Q * A) := by
    noncomm_ring
  rw [key, show Aᵀ * Q + Q * A = 0 from hA, mul_zero, sub_zero]

/-- [proved-derived; formal-checked] **The Cayley tick keeps its storage form, sign included**:
`UᵀQU = Q` for a `Q`-skew generator whose denominator is a unit. `Q` need not be definite. -/
theorem cayley_preserves_form {Q A : Matrix n n R} (hA : QSkew Q A)
    (hD : IsUnit (cayleyDen A).det) :
    (cayleyTick A)ᵀ * Q * cayleyTick A = Q := by
  set D := cayleyDen A
  set N := cayleyNum A
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have hDt : (D⁻¹)ᵀ * Dᵀ = 1 := by rw [← transpose_mul, hDD, transpose_one]
  have hform := cayley_forms_agree hA
  change (N * D⁻¹)ᵀ * Q * (N * D⁻¹) = Q
  calc (N * D⁻¹)ᵀ * Q * (N * D⁻¹) = (D⁻¹)ᵀ * (Nᵀ * Q * N) * D⁻¹ := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (D⁻¹)ᵀ * (Dᵀ * Q * D) * D⁻¹ := by rw [hform]
    _ = ((D⁻¹)ᵀ * Dᵀ) * Q * (D * D⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hDt, hDD, Matrix.one_mul, Matrix.mul_one]

/-- [definition] **The ring's storage form** `Q = diag(K, C)` on `(u, w)`. -/
def modeForm (K C : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks K 0 0 C

/-- [definition] **The ring's generator** `A = [[0, 1], [−C⁻¹K, 0]]`: `u̇ = w`, `C ẇ = −K u`. -/
def ringGenerator (K C : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  fromBlocks 0 1 (-(C⁻¹ * K)) 0

/-- [proved-derived; formal-checked] **The ring's generator is skew for its mode storage**: with
`K, C` symmetric and `C` invertible, `AᵀQ + QA = 0` for `Q = diag(K, C)`: `QA = [[0, K], [−K, 0]]`
is skew. -/
theorem ring_generator_qSkew {K C : Matrix n n R} (hK : Kᵀ = K) (hC : Cᵀ = C)
    (hCinv : IsUnit C.det) : QSkew (modeForm K C) (ringGenerator K C) := by
  unfold QSkew modeForm ringGenerator
  have hCC : C * C⁻¹ = 1 := mul_nonsing_inv C hCinv
  have hCt : (C⁻¹)ᵀ = C⁻¹ := by rw [transpose_nonsing_inv, hC]
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_zero, transpose_one, transpose_neg, transpose_mul, hK, hCt,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [Matrix.mul_assoc, nonsing_inv_mul C hCinv, Matrix.mul_one, ← Matrix.mul_assoc, hCC,
    Matrix.one_mul, fromBlocks_add]
  simp only [add_zero, neg_add_cancel, add_neg_cancel, fromBlocks_zero]

/-- [proved-derived; formal-checked] **The ring tick conserves its mode energy**: the lossless,
unpumped ring tick `U` of the half-step generator `(h/2) A` keeps `Q = diag(K, C)`,
`UᵀQU = Q`, whenever its Cayley denominator is a unit (`cayley_preserves_form` over
`ring_generator_qSkew`). -/
theorem ring_tick_conserves_mode_energy {K C : Matrix n n R} (hK : Kᵀ = K) (hC : Cᵀ = C)
    (hCinv : IsUnit C.det) (c : R) (hD : IsUnit (cayleyDen (c • ringGenerator K C)).det) :
    (cayleyTick (c • ringGenerator K C))ᵀ * modeForm K C * cayleyTick (c • ringGenerator K C) =
      modeForm K C :=
  cayley_preserves_form ((ring_generator_qSkew hK hC hCinv).smul c) hD

end Cayley

/-! ## 2. The descriptor tick, its denominator and its executed balance -/

section Tick

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The ring's executed one-port operator**
`M = 2C + (h/Y) I + h D + (h²/2) K`: storage on the rate, the port of admittance `Y`, dissipation
on the rate, stiffness on the displacement. -/
def ringOperator (C D K : E →L[ℝ] E) (Y h : ℝ) : E →L[ℝ] E :=
  (2 : ℝ) • C + (h / Y) • ContinuousLinearMap.id ℝ E + h • D + (h ^ 2 / 2) • K

/-- [definition] The one-port solve's right side `r = 2C w + h β − h K u`. -/
def ringRight (C K : E →L[ℝ] E) (h : ℝ) (u w β : E) : E := (2 : ℝ) • C w + h • β - h • K u

/-- [definition] **The ring's closed Cayley denominator** `2C + (h²/2) K`: no port, no loss. -/
def closedOperator (C K : E →L[ℝ] E) (h : ℝ) : E →L[ℝ] E := (2 : ℝ) • C + (h ^ 2 / 2) • K

/-- [definition] The wave the port returns, `β_out = β − (2/Y) ω`. -/
def ringOut (Y : ℝ) (β ω : E) : E := β - (2 / Y) • ω

/-- [proved-derived; formal-checked] **The ring tick conserves its mode energy in the descriptor
form** the executed tick solves (no `C⁻¹`): closed and lossless, `(2C + (h²/2) K) ω = 2C w − h K u`
gives `E_Q(u + hω, 2ω − w) = E_Q(u, w)` for symmetric `C`, `K` of any sign. -/
theorem ring_descriptor_tick_conserves (C K : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {h : ℝ} {u w ω : E} (hsolve : closedOperator C K h ω = (2 : ℝ) • C w - h • K u) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) = contactEnergy C K u w := by
  have hω := congrArg (fun v => inner ℝ ω v) hsolve
  simp only [closedOperator, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right] at hω
  have hCw : inner ℝ w (C ω) = inner ℝ ω (C w) := by rw [← hC, real_inner_comm]
  have hKu : inner ℝ u (K ω) = inner ℝ ω (K u) := by rw [← hK, real_inner_comm]
  simp only [contactEnergy, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial, hCw, hKu]
  linear_combination hω

/-- [proved-derived; formal-checked] **The executed port balance.** For *any* rate `ω` (the
executed chart's image, split on a lattice) and symmetric `C`, `K`, the mode energy moves by the
port work less the dissipation, plus the chart defect `⟨ω, M ω − r⟩` of the solve actually
executed:
`E_Q(u + hω, 2ω − w) − E_Q(u, w) + h⟨ω, D ω⟩ = (hY/4)(|β|² − |β_out|²) + ⟨ω, M ω − r⟩`. The
defect vanishes exactly at the law's solve. -/
theorem ring_tick_port_balance (C D K : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {Y h : ℝ} (hY : Y ≠ 0) (u w β ω : E) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * Y / 4 * (‖β‖ ^ 2 - ‖ringOut Y β ω‖ ^ 2) +
        inner ℝ ω (ringOperator C D K Y h ω - ringRight C K h u w β) := by
  have hCw : inner ℝ w (C ω) = inner ℝ ω (C w) := by rw [← hC, real_inner_comm]
  have hKu : inner ℝ u (K ω) = inner ℝ ω (K u) := by rw [← hK, real_inner_comm]
  have hR : h * Y / 4 * (‖β‖ ^ 2 - ‖ringOut Y β ω‖ ^ 2) =
      h * inner ℝ ω β - h / Y * ‖ω‖ ^ 2 := by
    rw [ringOut, norm_sub_smul_sq, real_inner_comm β ω]
    field_simp
    ring
  rw [hR]
  simp only [contactEnergy, ringOperator, ringRight, map_add, map_sub, map_smul, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hCw, hKu, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq]
  ring

/-- [proved-derived; formal-checked] **The ring tick's executed energy balance.** The pump moves the
stiffness `K → K′` at the fixed state (its work `½⟨u, (K′ − K) u⟩`, the deposition work of a storage
change, `Holon/Deposition.deposition_work`), the tick runs at `K′` with any executed rate `ω`, and
the carried state `(û′, ŵ′)` is the image `(u + hω, 2ω − w)` split on its lattice:
`E_(K′)(û′, ŵ′) − E_K(u, w) = pump + port − dissipation + chart + split`, each term stated. -/
theorem ring_tick_executed_energy_balance (C D K K' : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y)) {Y h : ℝ} (hY : Y ≠ 0)
    (u w β ω u' w' : E) :
    contactEnergy C K' u' w' - contactEnergy C K u w =
      (1 / 2 : ℝ) * inner ℝ u ((K' - K) u) +
        h * Y / 4 * (‖β‖ ^ 2 - ‖ringOut Y β ω‖ ^ 2) - h * inner ℝ ω (D ω) +
        inner ℝ ω (ringOperator C D K' Y h ω - ringRight C K' h u w β) +
        (contactEnergy C K' u' w' - contactEnergy C K' (u + h • ω) ((2 : ℝ) • ω - w)) := by
  have hport := ring_tick_port_balance C D K' hC hK' (h := h) hY u w β ω
  have hpump : contactEnergy C K' u w - contactEnergy C K u w =
      (1 / 2 : ℝ) * inner ℝ u ((K' - K) u) := by
    simp only [contactEnergy, _root_.sub_apply, inner_sub_right]
    ring
  linear_combination hport + hpump

/-! ## 2′. A loaded resonator in the ring's word-local port -/

/-- [proved-derived; formal-checked] **The loaded resonator closes its port power exactly.** Its
descriptor equation is the existing `ringOperator` solve with `e` as the already-computed element
output. At the exact solve, the mode storage changes by the wave power it receives, less
dissipation. -/
theorem loaded_tick_port_balance (C D K : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {Y h : ℝ} (hY : Y ≠ 0) (u w e ω : E)
    (hsolve : ringOperator C D K Y h ω = ringRight C K h u w e) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * Y / 4 * (‖e‖ ^ 2 - ‖ringOut Y e ω‖ ^ 2) := by
  have hp := ring_tick_port_balance C D K hC hK (h := h) hY u w e ω
  rw [hsolve] at hp
  simpa [ringOut, ringRight] using hp

/-- [proved-derived; formal-checked] A change to capacity and stiffness at fixed state is exactly
their deposition work. The stiffness here may include the pump block. -/
theorem ring_material_commit_work (C K C' K' : E →L[ℝ] E)
    (u w : E) :
    contactEnergy C' K' u w - contactEnergy C K u w =
      (1 / 2 : ℝ) * inner ℝ w ((C' - C) w) +
        (1 / 2 : ℝ) * inner ℝ u ((K' - K) u) := by
  simp only [contactEnergy, _root_.sub_apply, inner_sub_right]
  ring

/-- [proved-derived; formal-checked] **The loaded element–resonator stage is the existing element
followed by the transient resonator.** If `e` is the existing element's output, the returned wave
`s'` changes the field wave store by `hY/4 (‖s'‖²−‖b‖²)`. Adding the resonator's mode change and
dissipation cancels its port transfer exactly, leaving the existing element's passive and contrast
work. -/
theorem loaded_word_stage_balance
    {ρ : Type*} [Fintype ρ]
    (Ws : E →L[ℝ] E) (A : ρ → E →L[ℝ] E) (σ : ρ → ℝ) (Wc : E →L[ℝ] E)
    (hA : ∀ r v, inner ℝ v (A r v) = 0)
    (C D K : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {Y h : ℝ} (hY : Y ≠ 0) (b c u w e ω : E)
    (hElement : ElementStep Ws A σ Wc b c e)
    (hSolve : ringOperator C D K Y h ω = ringRight C K h u w e) :
    h * Y / 4 * (‖ringOut Y e ω‖ ^ 2 - ‖b‖ ^ 2) +
        contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * Y / 2 * (inner ℝ (midpoint b e) (Ws (midpoint b e)) +
        inner ℝ (midpoint b e) (Wc c)) := by
  have he := reaction_stage_balance hA σ Wc hElement
  have hr := loaded_tick_port_balance C D K hC hK hY u w e ω hSolve
  linear_combination hr + (h * Y / 2) * he

/-- [proved-derived; formal-checked] **The loaded tick's executed balance includes both carried
state and returned-wave splits.** The exact wave returned by the resonator is `ringOut`; the
consumer may carry a nearby state and wave. Their two energy differences and the descriptor-solve
residual are reported explicitly, so the field/resonator interconnection still closes. -/
theorem loaded_tick_executed_interconnection_balance (C D K K' : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y))
    {Y h : ℝ} (hY : Y ≠ 0) (u w e ω u' w' sOut : E) :
    contactEnergy C K' u' w' - contactEnergy C K u w + h * inner ℝ ω (D ω) +
        h * Y / 4 * (‖sOut‖ ^ 2 - ‖e‖ ^ 2) =
      (1 / 2 : ℝ) * inner ℝ u ((K' - K) u) +
        inner ℝ ω (ringOperator C D K' Y h ω - ringRight C K' h u w e) +
        (contactEnergy C K' u' w' -
          contactEnergy C K' (u + h • ω) ((2 : ℝ) • ω - w)) +
        h * Y / 4 * (‖sOut‖ ^ 2 - ‖ringOut Y e ω‖ ^ 2) := by
  have he := ring_tick_executed_energy_balance C D K K' hC hK' hY u w e ω u' w'
    (h := h)
  linear_combination he

/-- [proved-derived; formal-checked] **The reverse loaded tick pairs with the exact local tangent.**
For a state/input tangent obeying the differentiated descriptor solve, first solve the transposed
descriptor system for `r̄`; the returned input and state covectors are exactly the listed pullback.
The solve here is the exact adjoint. A carried adjoint chart has the separate residual owned by
`HNN/LatticeWord`. -/
theorem loaded_tick_adjoint_pairing
    [CompleteSpace E] (C K M : E →L[ℝ] E) {h Y : ℝ}
    (uBar' wBar' sBar' rBar : E)
    (hAdj : ContinuousLinearMap.adjoint M rBar =
      h • uBar' + (2 : ℝ) • wBar' - (2 / Y) • sBar')
    {δu δw δe δω : E}
    (hTangent : M δω = (2 : ℝ) • C δw + h • δe - h • K δu) :
    inner ℝ uBar' (δu + h • δω) +
        inner ℝ wBar' ((2 : ℝ) • δω - δw) +
        inner ℝ sBar' (δe - (2 / Y) • δω) =
      inner ℝ (uBar' - h • ContinuousLinearMap.adjoint K rBar) δu +
        inner ℝ (-wBar' + (2 : ℝ) • ContinuousLinearMap.adjoint C rBar) δw +
        inner ℝ (sBar' + h • rBar) δe := by
  have hp := ContinuousLinearMap.adjoint_inner_left M δω rBar
  rw [hAdj] at hp
  rw [hTangent] at hp
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    real_inner_comm, conj_trivial] at hp ⊢
  simp only [real_inner_comm, inner_neg_right] at hp ⊢
  linear_combination hp

/-- [proved-derived; formal-checked] **Differentiate the descriptor equation in its materials.**
Holding `(u,w,e)` fixed, differentiating `Mω = 2Cw + he − hKu` yields the displayed equation;
collecting the rate terms gives the material-direction tangent used by the exact adjoint. -/
theorem loaded_material_rate_tangent (M dC dD dK : E →L[ℝ] E) {h : ℝ}
    (u w ω : E) {δω : E}
    (hImplicit : M δω + (2 : ℝ) • dC ω + h • dD ω +
      (h ^ 2 / 2) • dK ω = (2 : ℝ) • dC w - h • dK u) :
    M δω = (2 : ℝ) • dC (w - ω) - h • dD ω -
      h • dK (u + (h / 2) • ω) := by
  let A := (2 : ℝ) • dC w - h • dK u
  let B := (2 : ℝ) • dC ω + h • dD ω + (h ^ 2 / 2) • dK ω
  have hplus : M δω + B = A := by simpa [A, B, add_assoc] using hImplicit
  have hexpand : (2 : ℝ) • dC (w - ω) - h • dD ω -
      h • dK (u + (h / 2) • ω) = A - B := by
    simp only [map_sub, map_add, map_smul, A, B]
    module
  calc
    M δω = (M δω + B) - B := by abel
    _ = A - B := by rw [hplus]
    _ = (2 : ℝ) • dC (w - ω) - h • dD ω -
        h • dK (u + (h / 2) • ω) := hexpand.symm

/-- [proved-derived; formal-checked] **The material directional derivative of a loaded tick.**
Differentiating the actual descriptor equation, then applying its exact adjoint, pairs the output
variation with `2 dC (w−ω) − h dD ω − h dK (u+hω/2)`. -/
theorem loaded_tick_material_variation
    [CompleteSpace E] (M dC dD dK : E →L[ℝ] E) {h Y : ℝ}
    (u w ω uBar' wBar' sBar' rBar : E)
    (hAdj : ContinuousLinearMap.adjoint M rBar =
      h • uBar' + (2 : ℝ) • wBar' - (2 / Y) • sBar')
    {δω : E}
    (hImplicit : M δω + (2 : ℝ) • dC ω + h • dD ω +
      (h ^ 2 / 2) • dK ω = (2 : ℝ) • dC w - h • dK u) :
    inner ℝ uBar' (h • δω) + inner ℝ wBar' ((2 : ℝ) • δω) +
        inner ℝ sBar' (-(2 / Y) • δω) =
      inner ℝ rBar ((2 : ℝ) • dC (w - ω) - h • dD ω -
        h • dK (u + (h / 2) • ω)) := by
  have hp := ContinuousLinearMap.adjoint_inner_left M δω rBar
  rw [hAdj, loaded_material_rate_tangent M dC dD dK u w ω hImplicit] at hp
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    real_inner_comm, conj_trivial] at hp ⊢
  linear_combination hp

/-- [proved-derived; formal-checked] **Squared gain directions preserve the material chart.** For
`A(g)=g² A₀`, the directional material change is `dA=2g·dg·A₀`; this is the exact chain factor
used with `loaded_tick_material_variation` for each admitted scalar gain. -/
theorem squared_gain_direction (g dg : ℝ) (A₀ : E →L[ℝ] E) :
    (g + dg) ^ 2 • A₀ - g ^ 2 • A₀ = (2 * g * dg + dg ^ 2) • A₀ := by
  rw [add_sq]
  module

/-- [proved-derived; formal-checked] The squared-gain variation has the stated derivative term and
an exact quadratic remainder. This form keeps the first variation distinct from a finite update. -/
theorem squared_gain_first_variation (g dg : ℝ) (A₀ : E →L[ℝ] E) :
    ((g + dg) ^ 2 • A₀ - g ^ 2 • A₀) - (2 * g * dg) • A₀ = dg ^ 2 • A₀ := by
  rw [add_sq]
  module

/-- [proved-derived; formal-checked] A squared scalar gain preserves positive semidefiniteness of
its declared base form. -/
theorem squared_gain_preserves_nonneg (g : ℝ) (A₀ : E →L[ℝ] E)
    (hA : ∀ x, 0 ≤ inner ℝ x (A₀ x)) :
    ∀ x, 0 ≤ inner ℝ x ((g ^ 2) • A₀ x) := by
  intro x
  have hg : 0 ≤ g ^ 2 := sq_nonneg g
  simpa only [inner_smul_right, conj_trivial] using mul_nonneg hg (hA x)

/-- [definition; agent-inferred] The capacity relation under its scalar amplitude gain. -/
def gainedCapacity (gC : ℝ) (C₀ : E →L[ℝ] E) : E →L[ℝ] E := gC ^ 2 • C₀

/-- [definition; agent-inferred] The dissipation relation under its scalar amplitude gain. -/
def gainedDissipation (gD : ℝ) (D₀ : E →L[ℝ] E) : E →L[ℝ] E := gD ^ 2 • D₀

/-- [definition; agent-inferred] Stiffness and pump are separate admitted amplitudes over immutable
base relations; their powered contributions join as the tick's stiffness. -/
def gainedStiffness (gK gP : ℝ) (K₀ P₀ : E →L[ℝ] E) : E →L[ℝ] E :=
  gK ^ 2 • K₀ + gP ^ 2 • P₀

/-- [proved-derived; formal-checked] Squared gains preserve positive semidefiniteness of the
capacity and dissipation base forms. The stiffness/pump family remains its exact signed sum and is
certified at every pump phase by `ResonatorMaterial::certify`; pump work is reported by the tick
balance rather than treated as passive storage. -/
theorem loaded_gains_preserve_storage_dissipation (gC gD : ℝ)
    (C₀ D₀ : E →L[ℝ] E)
    (hC : ∀ x, 0 ≤ inner ℝ x (C₀ x)) (hD : ∀ x, 0 ≤ inner ℝ x (D₀ x)) :
    (∀ x, 0 ≤ inner ℝ x (gainedCapacity gC C₀ x)) ∧
      ∀ x, 0 ≤ inner ℝ x (gainedDissipation gD D₀ x) := by
  exact ⟨squared_gain_preserves_nonneg gC C₀ hC,
    squared_gain_preserves_nonneg gD D₀ hD⟩

/-- [proved-derived; formal-checked] **The gain family has the host's exact finite directional
increment.** Each first-order term is `2g·δg` times its immutable base form, with the quadratic
remainder kept explicitly. -/
theorem loaded_gain_family_increment (gC gK gD gP dC dK dD dP : ℝ)
    (C₀ K₀ D₀ P₀ : E →L[ℝ] E) :
    (gainedCapacity (gC + dC) C₀ - gainedCapacity gC C₀ =
      (2 * gC * dC + dC ^ 2) • C₀) ∧
    (gainedDissipation (gD + dD) D₀ - gainedDissipation gD D₀ =
      (2 * gD * dD + dD ^ 2) • D₀) ∧
    (gainedStiffness (gK + dK) (gP + dP) K₀ P₀ - gainedStiffness gK gP K₀ P₀ =
      (2 * gK * dK + dK ^ 2) • K₀ + (2 * gP * dP + dP ^ 2) • P₀) := by
  refine ⟨?_, ?_, ?_⟩
  · exact squared_gain_direction gC dC C₀
  · exact squared_gain_direction gD dD D₀
  · calc
      gainedStiffness (gK + dK) (gP + dP) K₀ P₀ - gainedStiffness gK gP K₀ P₀ =
          ((gK + dK) ^ 2 • K₀ - gK ^ 2 • K₀) +
            ((gP + dP) ^ 2 • P₀ - gP ^ 2 • P₀) := by
        simp only [gainedStiffness]
        abel
      _ = (2 * gK * dK + dK ^ 2) • K₀ + (2 * gP * dP + dP ^ 2) • P₀ := by
        rw [squared_gain_direction gK dK K₀, squared_gain_direction gP dP P₀]

omit [InnerProductSpace ℝ E] in
theorem existsUnique_of_injective [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : E →L[ℝ] E) (hinj : ∀ v, M v = 0 → v = 0) : ∀ r, ∃! ω, M ω = r := by
  have hinj' : Function.Injective (M : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hinj v (by simpa using hv)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj'
  intro r
  obtain ⟨ω, hω⟩ := hsurj r
  exact ⟨ω, hω, fun y hy => hinj' (by simp only [ContinuousLinearMap.coe_coe]; rw [hy, ← hω]; rfl)⟩

/-- [proved-derived; formal-checked] **The ring's Cayley denominator is nonsingular under its
declared hypotheses.** (1) With its port (`Y > 0`) and `C, D, K ⪰ 0`, `h > 0`:
`⟨v, M v⟩ ≥ (h/Y)|v|²`, so every executed solve is unique. (2) Closed and lossless, for `h ≠ 0`:
`2C + (h²/2) K` is bijective when `C, K ⪰ 0` and `C + K` is definite, i.e. `ker C ∩ ker K = 0`. -/
theorem ring_cayley_denominator_nonsingular [FiniteDimensional ℝ E] (C D K : E →L[ℝ] E)
    (hC : ∀ v, 0 ≤ inner ℝ v (C v)) (hD : ∀ v, 0 ≤ inner ℝ v (D v))
    (hK : ∀ v, 0 ≤ inner ℝ v (K v)) :
    (∀ {Y h : ℝ}, 0 < Y → 0 < h →
      (∀ v, h / Y * ‖v‖ ^ 2 ≤ inner ℝ v (ringOperator C D K Y h v)) ∧
        ∀ r, ∃! ω, ringOperator C D K Y h ω = r) ∧
      (∀ {h : ℝ}, h ≠ 0 → (∀ v, v ≠ 0 → 0 < inner ℝ v (C v) + inner ℝ v (K v)) →
        ∀ r, ∃! ω, closedOperator C K h ω = r) := by
  refine ⟨fun {Y h} hY hh => ?_, fun {h} hh hdef => ?_⟩
  · have hpos : ∀ v, h / Y * ‖v‖ ^ 2 ≤ inner ℝ v (ringOperator C D K Y h v) := by
      intro v
      simp only [ringOperator, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
        inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
      have := hC v; have := hD v; have := hK v
      have : 0 ≤ h ^ 2 / 2 * inner ℝ v (K v) := by positivity
      have : 0 ≤ h * inner ℝ v (D v) := by positivity
      nlinarith
    refine ⟨hpos, existsUnique_of_injective _ fun v hv => ?_⟩
    have := hpos v
    rw [hv, inner_zero_right] at this
    have hc : 0 < h / Y := div_pos hh hY
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  · refine existsUnique_of_injective _ fun v hv => ?_
    by_contra hne
    have hsum := hdef v hne
    have hzero := congrArg (fun x => inner ℝ v x) hv
    simp only [closedOperator, _root_.add_apply, _root_.smul_apply, inner_add_right,
      inner_smul_right, inner_zero_right] at hzero
    have h2 : 0 < h ^ 2 / 2 := by positivity
    have := hC v; have := hK v
    have hc0 : inner ℝ v (C v) = 0 := by nlinarith
    have hk0 : inner ℝ v (K v) = 0 := by nlinarith
    linarith

/-- [proved-derived; formal-checked] Under the ring owner's positive-semidefinite material and
positive port/tick hypotheses, every loaded rate solve exists and is unique. -/
theorem loaded_tick_solve_unique [FiniteDimensional ℝ E]
    (C D K : E →L[ℝ] E)
    (hC : ∀ v, 0 ≤ inner ℝ v (C v)) (hD : ∀ v, 0 ≤ inner ℝ v (D v))
    (hK : ∀ v, 0 ≤ inner ℝ v (K v)) {Y h : ℝ} (hY : 0 < Y) (hh : 0 < h)
    (u w e : E) : ∃! ω, ringOperator C D K Y h ω = ringRight C K h u w e := by
  obtain ⟨_, hsolve⟩ := (ring_cayley_denominator_nonsingular C D K hC hD hK).1 hY hh
  exact hsolve (ringRight C K h u w e)

end Tick

/-- [counterexample; formal-checked] **The harmonic mode makes the closed denominator singular.**
On the two-node cycle (branches `0 → 1` and `1 → 0`, incidence `B = [[−1, 1], [1, −1]]`) the ring's
capacity and stiffness `C = K = BᵀB` share the constant vector `(1, 1)` in their kernels, so for
every `h` the closed Cayley denominator `2C + (h²/2)K` sends it to zero: the ring's harmonic
(dormant) mode, campaign 3's, is where `C + K` is not definite. -/
theorem ring_harmonic_mode_singular (h : ℚ) :
    let B : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; 1, -1]
    ((2 : ℚ) • (Bᵀ * B) + (h ^ 2 / 2) • (Bᵀ * B)) *ᵥ ![1, 1] = 0 ∧ (![1, 1] : Fin 2 → ℚ) ≠ 0 := by
  intro B
  refine ⟨?_, fun h0 => by simpa using congrFun h0 0⟩
  ext i
  fin_cases i <;> simp [B, mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

/-! ## 3. A change of reference admittance: the power-normalized two-port -/

section Reference

open Holonics.Computation.HolonicConstitutiveCirculation

/-- [definition] The reflection `Γ = (G₀ − G₁)/(G₀ + G₁)` of a wave arriving in reference `G₀` at
reference `G₁`. -/
def reflection (G₀ G₁ : ℚ) : ℚ := (G₀ - G₁) / (G₀ + G₁)

/-- [definition] **The power transmission fraction** `T = 4G₀G₁/(G₀ + G₁)²` (not an amplitude). -/
def transmission (G₀ G₁ : ℚ) : ℚ := 4 * G₀ * G₁ / (G₀ + G₁) ^ 2

/-- [proved-derived; formal-checked] **The two-port reference balance.** For `G₀, G₁ > 0`,
`Γ² + T = 1`. The junction's two-port at a zero held wave (`emitted`, `successorHeld` of
`HolonicConstitutiveCirculation`, the owner of `HNN/Propagation.junctionSwing_twoPort`) reflects
`Γ i` in the old reference and transmits `(1 + Γ) i` into the new one; the power recharted into the
new reference is `G₁|(1 + Γ) i|² = T · G₀|i|²`, so both powers are read in one frame and the
weighted square energy balance (`weighted_square_energy`) is `Γ² + T = 1` times the incident power. -/
theorem two_port_reference_balance {G₀ G₁ : ℚ} (h₀ : 0 < G₀) (h₁ : 0 < G₁) (i : ℚ) :
    reflection G₀ G₁ ^ 2 + transmission G₀ G₁ = 1 ∧
      emitted G₀ G₁ i 0 = reflection G₀ G₁ * i ∧
      successorHeld G₀ G₁ i 0 = (1 + reflection G₀ G₁) * i ∧
      G₁ * successorHeld G₀ G₁ i 0 ^ 2 = transmission G₀ G₁ * (G₀ * i ^ 2) ∧
      G₀ * emitted G₀ G₁ i 0 ^ 2 + G₁ * successorHeld G₀ G₁ i 0 ^ 2 = G₀ * i ^ 2 := by
  have hs : G₀ + G₁ ≠ 0 := (add_pos h₀ h₁).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold reflection transmission; field_simp; ring
  · unfold emitted junctionVelocity reflection; field_simp; ring
  · unfold successorHeld junctionVelocity reflection; field_simp; ring
  · unfold successorHeld junctionVelocity transmission; field_simp; ring
  · have := weighted_square_energy (incoming := i) (held := 0) h₀ h₁
    simpa using this

end Reference

/-! ## 4. The ring's crossings are its epoch ticks -/

section Crossings

open Holonics.Objects.Parametron Holonics.Aeon.Clock.Epoch
open Holonics.Geometry.HolonicClockedPantographicSwing

variable {ClockAddress : Type*}

/-- [proved-derived; formal-checked] **Crossings are epoch ticks.** Along the ring's rational clock
passage, the arrivals on its section over `N` micro-steps from residue `r < d` number `(r + N)/d`
(`Epoch.ring_arrivals_eq_ringCrossings` over `Parametron.ringCrossings_eq`); for `d ≥ 2` the section
is transversal (`Epoch.ring_section_transversal`), and its certified section cuts every passage of
`N > 0` micro-steps into `#ticks + 1` epochs (`Epoch.epoch_count`). -/
theorem ring_crossings_are_epoch_ticks (passage : RationalClockPassage ClockAddress) (r N : ℕ)
    (hr : r < passage.denominator) :
    ((Finset.Ioc 0 N).filter
        (fun j => (ringOscillator passage).sectionMark (r + j) = true)).card =
        (r + N) / passage.denominator ∧
      (2 ≤ passage.denominator →
        Transversal (fun j => (ringOscillator passage).sectionMark (r + j))) ∧
      (0 < N → ((Finset.range N).image (epochOf
          (sectionOf (fun j => (ringOscillator passage).sectionMark (r + j)) N).ticks)).card =
        (sectionOf (fun j => (ringOscillator passage).sectionMark (r + j)) N).ticks.card + 1) :=
  ⟨(ring_arrivals_eq_ringCrossings passage r N).trans (ringCrossings_eq _ _ hr N),
    fun hd => ring_section_transversal passage hd r, fun hN => epoch_count _ hN⟩

end Crossings

/-! ## 5. The pump, the half-turn sheets and the locked-sheet face -/

section Pump

open Holonics.Physics.HolonicParametron Holonics.Objects.Parametron

/-- [definition] **The pump's node block form** `−p((x² − y²) cos ψ + 2xy sin ψ)` on a node's
complex amplitude `x + iy`: the doubled phase read as a quadratic form, the stiffness block
`−2p [[cos ψ, sin ψ], [sin ψ, −cos ψ]]` that the executed ring adds to `K` (`½ zᵀ K z`). -/
def pumpBlock (p ψ x y : ℝ) : ℝ := -p * ((x ^ 2 - y ^ 2) * Real.cos ψ + 2 * x * y * Real.sin ψ)

/-- [proved-derived; formal-checked] **The pump is invariant under the half-turn.** The block form at
`r(cos θ, sin θ)` is `r²` times the owner's pump storage `−p cos(2θ − ψ)`, which the half-turn
`θ ↦ θ + π` keeps (`PhaseCarrier.pumpStorage_halfTurnSheet`); on the amplitude the half-turn is
`(x, y) ↦ (−x, −y)`, which the block form keeps. -/
theorem pump_half_turn_invariant (p ψ θ r : ℝ) :
    pumpStorage p ψ (halfTurnSheet θ) = pumpStorage p ψ θ ∧
      pumpBlock p ψ (r * Real.cos θ) (r * Real.sin θ) = r ^ 2 * pumpStorage p ψ θ ∧
      ∀ x y, pumpBlock p ψ (-x) (-y) = pumpBlock p ψ x y := by
  refine ⟨pumpStorage_halfTurnSheet p ψ θ, ?_, fun x y => by unfold pumpBlock; ring⟩
  unfold pumpBlock pumpStorage
  rw [Real.cos_sub, Real.cos_two_mul, Real.sin_two_mul]
  have := Real.cos_sq_add_sin_sq θ
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
  rw [show (2 : ℝ) * Real.cos θ ^ 2 - 1 = Real.cos θ ^ 2 - Real.sin θ ^ 2 by rw [hc]; ring]
  ring

/-- [proved-derived; formal-checked] **The pump is blind to the sheets of its axis.** With the pump
at twice its axis, `ψ = 2φ`, the two sheets `θ = φ` and `θ = φ + π` carry the same pump storage
`−p`, its least value for `p > 0`. -/
theorem pump_blind_to_sheets (p φ : ℝ) (b : Bool) :
    pumpStorage p (2 * φ) (φ + binaryPhase b) = -p := by
  unfold pumpStorage
  cases b
  · simp [binaryPhase]
  · simp only [binaryPhase]
    rw [show 2 * (φ + Real.pi) - 2 * φ = 2 * Real.pi by ring, Real.cos_two_pi]
    ring

/-- [proved-derived; formal-checked] **The locked sheet has an Ising receiver face; the perceptron
is its threshold** (composing `Objects/Parametron`): on locked sheets the ring population's driven
phase energy is the driven Ising energy (`drivenPhaseEnergy_binaryPhase`), the sheet receiver reads
each locked sheet back (`sheetReading_binaryPhase`), and the threshold sheet of a site's local field
minimizes the energy given its neighbours (`thresholdSheet_minimizes`). The perceptron is this face
of the ring, not the ring (`perceptron_is_a_face`). -/
theorem locked_sheet_receiver_face {ι : Type*} [DecidableEq ι] [Fintype ι]
    (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (noLoop : ∀ e ∈ edges, e.1 ≠ e.2) (state : ι → Bool) (i : ι) :
    drivenPhaseEnergy edges weight drive (fun k => binaryPhase (state k)) =
        drivenIsingEnergy edges weight drive state ∧
      (∀ k, sheetReading (binaryPhase (state k)) = state k) ∧
      ∀ s, drivenIsingEnergy edges weight drive
          (Function.update state i (thresholdSheet (localField edges weight drive state i))) ≤
        drivenIsingEnergy edges weight drive (Function.update state i s) :=
  ⟨drivenPhaseEnergy_binaryPhase edges weight drive state,
    fun k => sheetReading_binaryPhase (state k),
    fun s => thresholdSheet_minimizes edges weight drive noLoop state i s⟩

end Pump

/-! ## 6. The executed solve's bound and a gain's backtrack -/

section ExecutedBound

open Holonics.HNN.LatticeWord (rowNorm l1 row_sum_le_rowNorm)
open Holonics.HNN.LatticeDeposit (quot unit unit_pos)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] A row of `A v` is within `‖A‖∞ c` when every coordinate of `v`
is within `c`. -/
theorem abs_mulVec_le_rowNorm (A : Matrix n n ℚ) (v : n → ℚ) {c : ℚ} (hc : 0 ≤ c)
    (hv : ∀ j, |v j| ≤ c) (i : n) : |(A *ᵥ v) i| ≤ rowNorm A * c := by
  calc |(A *ᵥ v) i| = |∑ j, A i j * v j| := rfl
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * c := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * c := (Finset.sum_mul _ _ _).symm
    _ ≤ rowNorm A * c := mul_le_mul_of_nonneg_right (row_sum_le_rowNorm A i) hc

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] A pairing is within `‖ω‖₁ c` when every coordinate of the
vector is within `c`. -/
theorem abs_dot_le_l1 (ω e : n → ℚ) {c : ℚ} (he : ∀ i, |e i| ≤ c) : |ω ⬝ᵥ e| ≤ l1 ω * c := by
  unfold l1
  calc |ω ⬝ᵥ e| = |∑ i, ω i * e i| := rfl
    _ ≤ ∑ i, |ω i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |ω i| * c := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
    _ = (∑ i, |ω i|) * c := (Finset.sum_mul _ _ _).symm

/-- [proved-derived; formal-checked] **The executed solve's chart term is bounded by its
certificate** (`hnn::ring::ResonatorStep::bound`, the contact's `transit_defect` alike). With
`‖1 − M X̂‖∞ ≤ δ`, `|r_i| ≤ ρ` and the executed (carried) rate within `u` of the chart's image,
`M ω − r = M(ω − X̂ r) − (1 − M X̂) r`, so `|⟨ω, M ω − r⟩| ≤ ‖ω‖₁ (δ ρ + ‖M‖∞ u)`. The balance's
chart term absorbs any executed rate; this bound is what refuses a wrong one. -/
theorem loaded_solve_chart_bound (M X : Matrix n n ℚ) (r ω : n → ℚ) {δ ρ u : ℚ}
    (hρ : 0 ≤ ρ) (hu : 0 ≤ u) (hR : rowNorm (1 - M * X) ≤ δ) (hr : ∀ i, |r i| ≤ ρ)
    (hω : ∀ i, |ω i - (X *ᵥ r) i| ≤ u) :
    |ω ⬝ᵥ (M *ᵥ ω - r)| ≤ l1 ω * (δ * ρ + rowNorm M * u) := by
  have hsplit : M *ᵥ ω - r = M *ᵥ (ω - X *ᵥ r) - (1 - M * X) *ᵥ r := by
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
    abel
  apply abs_dot_le_l1
  intro i
  rw [hsplit, Pi.sub_apply]
  have h1 := abs_mulVec_le_rowNorm M (ω - X *ᵥ r) hu (fun j => by simpa using hω j) i
  have h2 := abs_mulVec_le_rowNorm (1 - M * X) r hρ hr i
  have h3 := abs_add_le ((M *ᵥ (ω - X *ᵥ r)) i) (-(((1 - M * X) *ᵥ r) i))
  rw [abs_neg, ← sub_eq_add_neg] at h3
  have h4 : rowNorm (1 - M * X) * ρ ≤ δ * ρ := mul_le_mul_of_nonneg_right hR hρ
  linarith

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **A carried state's split is within its cells.** For a
symmetric form `Q` and a carried state `ŷ` within `u` of its image `y`,
`½⟨ŷ, Q ŷ⟩ − ½⟨y, Q y⟩ = ½⟨ŷ − y, Q(ŷ + y)⟩`, within `(u/2)‖Q(ŷ + y)‖₁`: the resonator's state
split on its `C` and on its phase's `K`. -/
theorem loaded_state_split_bound (Q : Matrix n n ℚ) (hQ : Qᵀ = Q) (y ŷ : n → ℚ) {u : ℚ}
    (hy : ∀ i, |ŷ i - y i| ≤ u) :
    |ŷ ⬝ᵥ Q *ᵥ ŷ / 2 - y ⬝ᵥ Q *ᵥ y / 2| ≤ u / 2 * l1 (Q *ᵥ (ŷ + y)) := by
  have hsym : y ⬝ᵥ Q *ᵥ ŷ = ŷ ⬝ᵥ Q *ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ, dotProduct_comm]
  have hid : ŷ ⬝ᵥ Q *ᵥ ŷ / 2 - y ⬝ᵥ Q *ᵥ y / 2 = (Q *ᵥ (ŷ + y)) ⬝ᵥ (ŷ - y) / 2 := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (Q *ᵥ ŷ) ŷ, dotProduct_comm (Q *ᵥ ŷ) y, dotProduct_comm (Q *ᵥ y) ŷ,
      dotProduct_comm (Q *ᵥ y) y, hsym]
    ring
  have hb := abs_dot_le_l1 (Q *ᵥ (ŷ + y)) (ŷ - y) (c := u) (fun i => by simpa using hy i)
  rw [hid, abs_div, abs_two]
  linarith

/-- [proved-derived; formal-checked] **A gain's backtrack is positive and on the admissible side**
(`hnn::constitution::GainBacktrack`). A gain at the positive lattice coordinate `q`,
`g = q·2^(−L)`, whose candidate step would reach `g ≤ 0`, carries to the midpoint `g/2` split at the
lattice by its nearest point, ties upward: the coordinate `⌊(q + 1)/2⌋`, between `1` and `q`. It is
exactly `q/2` for even `q`, and the gain holds at `q = 1`; deposition never releases a family. -/
theorem gain_backtrack_midpoint (L : ℕ) (q : ℤ) (hq : 1 ≤ q) :
    quot L (q * unit L / 2) = (q + 1) / 2 ∧ 1 ≤ (q + 1) / 2 ∧ (q + 1) / 2 ≤ q := by
  have hu : unit L ≠ 0 := (unit_pos L).ne'
  have hmid : (q : ℚ) * unit L / 2 / unit L = ((q + 1 : ℤ) : ℚ) / ((2 : ℕ) : ℚ) - 1 / 2 := by
    push_cast
    field_simp
    ring
  refine ⟨?_, by omega, by omega⟩
  unfold quot
  rw [hmid, round_eq, sub_add_cancel, Rat.floor_intCast_div_natCast]
  norm_num

end ExecutedBound

section Audit

#print axioms cayley_forms_agree
#print axioms cayley_preserves_form
#print axioms ring_generator_qSkew
#print axioms ring_tick_conserves_mode_energy
#print axioms ring_descriptor_tick_conserves
#print axioms ring_tick_port_balance
#print axioms ring_tick_executed_energy_balance
#print axioms loaded_tick_port_balance
#print axioms loaded_tick_solve_unique
#print axioms loaded_word_stage_balance
#print axioms loaded_tick_executed_interconnection_balance
#print axioms loaded_tick_adjoint_pairing
#print axioms loaded_material_rate_tangent
#print axioms loaded_tick_material_variation
#print axioms squared_gain_direction
#print axioms squared_gain_first_variation
#print axioms squared_gain_preserves_nonneg
#print axioms loaded_gains_preserve_storage_dissipation
#print axioms loaded_gain_family_increment
#print axioms ring_cayley_denominator_nonsingular
#print axioms ring_harmonic_mode_singular
#print axioms two_port_reference_balance
#print axioms ring_crossings_are_epoch_ticks
#print axioms pump_half_turn_invariant
#print axioms pump_blind_to_sheets
#print axioms locked_sheet_receiver_face
#print axioms abs_mulVec_le_rowNorm
#print axioms abs_dot_le_l1
#print axioms loaded_solve_chart_bound
#print axioms loaded_state_split_bound
#print axioms gain_backtrack_midpoint

end Audit

end Holonics.HNN.Ring
