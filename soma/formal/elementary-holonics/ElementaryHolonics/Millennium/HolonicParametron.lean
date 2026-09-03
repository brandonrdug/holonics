import ElementaryHolonics.Foundation.Holon

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
  rw [phaseCarrier_halfTurnSheet, Complex.exp_pi_mul_I]
  ring

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

/-! ## The exact winding lift of `i^i` -/

/-- The `n`th logarithmic winding occurrence above the receiver face `i`. -/
def windingLogI (n : ℤ) : ℂ :=
  (((Real.pi / 2 + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Every winding occurrence exponentiates to the same complex receiver face `i`. -/
theorem exp_windingLogI (n : ℤ) : Complex.exp (windingLogI n) = Complex.I := by
  rw [show windingLogI n = (Real.pi : ℂ) / 2 * Complex.I +
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        unfold windingLogI
        push_cast
        ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The same winding population is the quarter-turn phase family of the Complex Parametron. -/
theorem phaseCarrier_windingI (n : ℤ) :
    phaseCarrier (Real.pi / 2 + 2 * Real.pi * (n : ℝ)) = Complex.I := by
  change Complex.exp (windingLogI n) = Complex.I
  exact exp_windingLogI n

/-- The exponential receiver which forgets the logarithmic winding while retaining it in the
occurrence fibre. -/
def logarithmicWindingHolon : Soma.Holonics.Holon ℤ ℤ ℂ where
  Occurrence := ℤ
  source n := n
  target n := n + 1
  receive n := Complex.exp (windingLogI n)

@[simp] theorem logarithmicWindingHolon_receive (n : ℤ) :
    logarithmicWindingHolon.receive n = Complex.I :=
  exp_windingLogI n

/-- Every integer logarithmic branch is retained behind the single returned face `i`. -/
def logarithmicWindingReconstruction :
    logarithmicWindingHolon.PreimageFibre Complex.I ≃ ℤ where
  toFun occurrence := occurrence.1
  invFun n := ⟨n, exp_windingLogI n⟩
  left_inv occurrence := by
    cases occurrence
    rfl
  right_inv n := rfl

/-- The collapsed `i` face genuinely contains distinct winding occurrences. -/
theorem logarithmicWindingHolon_hasDistinctOccurrences :
    ∃ first second : logarithmicWindingHolon.Occurrence,
      first ≠ second ∧
        logarithmicWindingHolon.receive first =
          logarithmicWindingHolon.receive second := by
  change ∃ first second : ℤ,
    first ≠ second ∧
      Complex.exp (windingLogI first) = Complex.exp (windingLogI second)
  exact ⟨0, 1, by norm_num, (exp_windingLogI 0).trans (exp_windingLogI 1).symm⟩

/-- `i^i` evaluated after retaining the `n`th logarithmic winding occurrence. -/
def windingIPowerI (n : ℤ) : ℂ :=
  Complex.exp (Complex.I * windingLogI n)

/--
The exact winding-resolved `i^i` family.  The principal face is `n = 0`; changing the winding
index is an oriented logarithmic turn and changes the returned positive real magnitude.
-/
theorem windingIPowerI_eq (n : ℤ) :
    windingIPowerI n =
      (Real.exp (-Real.pi / 2 - 2 * Real.pi * (n : ℝ)) : ℂ) := by
  rw [Complex.ofReal_exp]
  unfold windingIPowerI windingLogI
  rw [show Complex.I *
        (((Real.pi / 2 + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I) =
      -((Real.pi / 2 + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) by
        calc
          _ = ((Real.pi / 2 + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) *
                (Complex.I * Complex.I) := by ring
          _ = -((Real.pi / 2 + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
            rw [Complex.I_mul_I]
            ring]
  congr 1
  push_cast
  ring

/-- The receiver face which keeps the branch current, its collapsed exponential, and the reopened
`i^i` current together rather than displaying any one of them as a bare scalar. -/
structure IPowerReceiverFace where
  logarithmicCurrent : ℂ
  exponentialFace : ℂ
  powerCurrent : ℂ

/-- The complete branch-resolved complex winding current as one occurrence-bearing holon. -/
def iPowerIChartHolon : Soma.Holonics.Holon ℤ ℤ IPowerReceiverFace where
  Occurrence := ℤ
  source n := n
  target n := n + 1
  receive n :=
    { logarithmicCurrent := windingLogI n
      exponentialFace := Complex.exp (windingLogI n)
      powerCurrent := windingIPowerI n }

@[simp] theorem iPowerIChartHolon_exponentialFace (n : ℤ) :
    (iPowerIChartHolon.receive n).exponentialFace = Complex.I :=
  exp_windingLogI n

@[simp] theorem iPowerIChartHolon_powerCurrent (n : ℤ) :
    (iPowerIChartHolon.receive n).powerCurrent =
      (Real.exp (-Real.pi / 2 - 2 * Real.pi * (n : ℝ)) : ℂ) :=
  windingIPowerI_eq n

/-- The winding index, its next oriented turn, and its exact complex current form a holon. -/
def iPowerIHolon : Soma.Holonics.Holon ℤ ℤ ℂ where
  Occurrence := ℤ
  source n := n
  target n := n + 1
  receive := windingIPowerI

@[simp] theorem iPowerIHolon_source (n : ℤ) : iPowerIHolon.source n = n := rfl

@[simp] theorem iPowerIHolon_target (n : ℤ) : iPowerIHolon.target n = n + 1 := rfl

@[simp] theorem iPowerIHolon_receive (n : ℤ) :
    iPowerIHolon.receive n =
      (Real.exp (-Real.pi / 2 - 2 * Real.pi * (n : ℝ)) : ℂ) :=
  windingIPowerI_eq n

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
#print axioms Soma.Holonics.Millennium.HolonicParametron.exp_windingLogI
#print axioms Soma.Holonics.Millennium.HolonicParametron.phaseCarrier_windingI
#print axioms Soma.Holonics.Millennium.HolonicParametron.logarithmicWindingReconstruction
#print axioms Soma.Holonics.Millennium.HolonicParametron.logarithmicWindingHolon_hasDistinctOccurrences
#print axioms Soma.Holonics.Millennium.HolonicParametron.windingIPowerI_eq
#print axioms Soma.Holonics.Millennium.HolonicParametron.iPowerIChartHolon_exponentialFace
#print axioms Soma.Holonics.Millennium.HolonicParametron.iPowerIChartHolon_powerCurrent
#print axioms Soma.Holonics.Millennium.HolonicParametron.iPowerIHolon_receive
