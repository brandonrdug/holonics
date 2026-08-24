import ElementaryHolonics.Millennium.HolonicDifferenceCalculus

/-!
# The parametron is a driven half-turn receiver

**[proved-derived]** A parametrically driven phase carrier has a two-sheet receiver separated by
one half-turn.  The pump storage is invariant under that deck transformation, while the complex
carrier changes sign.  On the locked two-sheet population, cosine coupling is exactly the Ising
pairing.  The theorem deliberately retains the phase carrier before taking its binary receiver;
amplitude, pump chronology, damping, and the unlocked phase population are not identified with a
bit by these results.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.HolonicParametron

open Soma.Holonics.Millennium.HolonicDifferenceCalculus

/-! ## The pump creates a two-sheet phase population -/

/-- The phase carrier presented in the complex receiver. -/
def phaseCarrier (phase : ℝ) : ℂ :=
  Complex.exp (phase * Complex.I)

/-- The second sheet of the parametrically locked phase population. -/
def halfTurnSheet (phase : ℝ) : ℝ :=
  phase + Real.pi

/-- A simple averaged pump-storage face.  The doubled phase is the exact feature that leaves the
two half-turn-separated carrier phases degenerate. -/
def pumpStorage (strength pumpPhase carrierPhase : ℝ) : ℝ :=
  -strength * Real.cos (2 * carrierPhase - pumpPhase)

/-- The pump cannot distinguish the two half-turn sheets. -/
theorem pumpStorage_halfTurnSheet
    (strength pumpPhase carrierPhase : ℝ) :
    pumpStorage strength pumpPhase (halfTurnSheet carrierPhase) =
      pumpStorage strength pumpPhase carrierPhase := by
  unfold pumpStorage halfTurnSheet
  rw [show 2 * (carrierPhase + Real.pi) - pumpPhase =
      (2 * carrierPhase - pumpPhase) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-- The same deck transformation is visible to the complex carrier as multiplication by `-1`. -/
theorem phaseCarrier_halfTurnSheet (carrierPhase : ℝ) :
    phaseCarrier (halfTurnSheet carrierPhase) = -phaseCarrier carrierPhase := by
  unfold phaseCarrier halfTurnSheet
  rw [show ((carrierPhase + Real.pi : ℝ) : ℂ) * Complex.I =
      (carrierPhase : ℂ) * Complex.I + Real.pi * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The half-turn sheet is exactly the Euler/swing negation already owned by the difference
calculus. -/
theorem phaseCarrier_halfTurn_isSwingReceiver (carrierPhase : ℝ) :
    phaseCarrier (halfTurnSheet carrierPhase) =
      Complex.exp (Real.pi * Complex.I) * phaseCarrier carrierPhase := by
  rw [phaseCarrier_halfTurnSheet, eulerHalfTurn_actsByNegation]

/-! ## The binary receiver and its complete phase lift -/

/-- The two locked phase representatives.  `false` is the zero-phase sheet and `true` the
half-turn sheet. -/
def binaryPhase : Bool → ℝ
  | false => 0
  | true => Real.pi

/-- The sign receiver of a locked phase. -/
def spinFace : Bool → ℝ
  | false => 1
  | true => -1

/-- The two complex phase carriers return exactly the two real sign faces. -/
theorem phaseCarrier_binaryPhase (bit : Bool) :
    phaseCarrier (binaryPhase bit) = (spinFace bit : ℂ) := by
  cases bit <;> simp [phaseCarrier, binaryPhase, spinFace, Complex.exp_pi_mul_I]

/-- The binary receiver is not injective on the full phase line: a complete turn gives the same
carrier face while retaining a different source phase. -/
theorem phaseCarrier_fullTurn_fibre (phase : ℝ) :
    phaseCarrier (phase + 2 * Real.pi) = phaseCarrier phase := by
  unfold phaseCarrier
  rw [show (((phase + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (phase : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
        push_cast
        ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ## Locked phase coupling is exactly an Ising pairing -/

/-- One phase-coupling edge before the binary receiver is taken. -/
def phaseCoupling (weight firstPhase secondPhase : ℝ) : ℝ :=
  -weight * Real.cos (firstPhase - secondPhase)

/-- The corresponding signed edge after the locked-phase receiver. -/
def isingCoupling (weight : ℝ) (first second : Bool) : ℝ :=
  -weight * spinFace first * spinFace second

/-- Cosine interaction on the two locked sheets is exactly the Ising interaction. -/
theorem phaseCoupling_binaryPhase
    (weight : ℝ) (first second : Bool) :
    phaseCoupling weight (binaryPhase first) (binaryPhase second) =
      isingCoupling weight first second := by
  cases first <;> cases second <;>
    simp [phaseCoupling, isingCoupling, binaryPhase, spinFace, Real.cos_neg]

/-- A finite coupled parametron population before quotienting to signs. -/
def phaseNetworkEnergy
    {ι : Type*} [DecidableEq ι]
    (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (phase : ι → ℝ) : ℝ :=
  ∑ edge ∈ edges, phaseCoupling (weight edge.1 edge.2) (phase edge.1) (phase edge.2)

/-- The Ising receiver of the same addressed coupling population. -/
def isingNetworkEnergy
    {ι : Type*} [DecidableEq ι]
    (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (state : ι → Bool) : ℝ :=
  ∑ edge ∈ edges, isingCoupling (weight edge.1 edge.2) (state edge.1) (state edge.2)

/-- On the invariant locked-phase population, the complete finite phase energy descends exactly
to the Ising energy. -/
theorem phaseNetworkEnergy_binaryPhase
    {ι : Type*} [DecidableEq ι]
    (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (state : ι → Bool) :
    phaseNetworkEnergy edges weight (fun index ↦ binaryPhase (state index)) =
      isingNetworkEnergy edges weight state := by
  unfold phaseNetworkEnergy isingNetworkEnergy
  apply Finset.sum_congr rfl
  intro edge hedge
  simp only
  exact phaseCoupling_binaryPhase (weight edge.1 edge.2) (state edge.1) (state edge.2)

end Soma.Holonics.Millennium.HolonicParametron

#print axioms Soma.Holonics.Millennium.HolonicParametron.pumpStorage_halfTurnSheet
#print axioms Soma.Holonics.Millennium.HolonicParametron.phaseCarrier_halfTurnSheet
#print axioms Soma.Holonics.Millennium.HolonicParametron.phaseNetworkEnergy_binaryPhase
