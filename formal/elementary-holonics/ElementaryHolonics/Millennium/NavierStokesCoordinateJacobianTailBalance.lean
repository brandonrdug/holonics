import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailDecay

/-!
# Balancing the complete Jacobian reconstruction fibre at a dyadic aperture

**[proved-derived]** The quantitative `H³` reconstruction fibre decays like the square root of
`(R+1)^(-1/6)`.  Choosing the literal lattice radius `2^(6 ceil(log₂ H))` therefore pays the
square root of the positive high-order receiver exactly: the sixfold dyadic depth turns the tail
into a fixed finite constant.  This owner performs only that receiver-local balance.  It neither
discards the reconstruction fibre nor assumes the still-required scale-uniform physical Hodge
kernel estimate for the middle bands.
-/

noncomputable section

open Set
open scoped ENNReal

namespace Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailBalance

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFrequencyComb
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-- Six dyadic depth payments match the `1/12` decay exponent left after Cauchy--Schwarz. -/
def jacobianTailDyadicDepth (highOrder : ℝ) : ℕ :=
  6 * shellDepth highOrder

/-- The literal lattice radius reached by the sixfold dyadic scale word. -/
def jacobianTailDyadicRadius (highOrder : ℝ) : ℕ :=
  2 ^ jacobianTailDyadicDepth highOrder

@[simp]
theorem jacobianTailDyadicRadius_cast (highOrder : ℝ) :
    (jacobianTailDyadicRadius highOrder : ℝ) =
      (2 : ℝ) ^ (6 * shellDepth highOrder) := by
  simp [jacobianTailDyadicRadius, jacobianTailDyadicDepth]

/-- Sixfold dyadic depth is still logarithmic in every receiver at least `e`. -/
theorem jacobianTailDyadicDepth_cast_le_log
    {highOrder : ℝ} (hhighOrder : Real.exp 1 ≤ highOrder) :
    (jacobianTailDyadicDepth highOrder : ℝ) ≤
      6 * ((Real.log 2)⁻¹ + 1) * Real.log highOrder := by
  have hone : 1 ≤ highOrder :=
    (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hhighOrder
  have hshell := (shellDepth_lt_logb_add_one hone).le
  have hlog : 1 ≤ Real.log highOrder := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log highOrder :=
        Real.log_le_log (Real.exp_pos 1) hhighOrder
  have hq : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  rw [Real.logb, div_eq_mul_inv] at hshell
  unfold jacobianTailDyadicDepth
  push_cast
  calc
    6 * (shellDepth highOrder : ℝ) ≤
        6 * ((Real.log highOrder * (Real.log 2)⁻¹) + 1) :=
      mul_le_mul_of_nonneg_left hshell (by norm_num)
    _ ≤ 6 * (((Real.log 2)⁻¹ + 1) * Real.log highOrder) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      nlinarith
    _ = 6 * ((Real.log 2)⁻¹ + 1) * Real.log highOrder := by ring

/-- Specialization to the actual positive differentiated receiver. -/
theorem jacobianTailDyadicDepth_coordinateLogH3Receiver_le
    (velocity : VelocityField) (t : ℝ) :
    (jacobianTailDyadicDepth (coordinateLogH3Receiver velocity t) : ℝ) ≤
      6 * ((Real.log 2)⁻¹ + 1) *
        Real.log (coordinateLogH3Receiver velocity t) :=
  jacobianTailDyadicDepth_cast_le_log
    (exp_one_le_coordinateLogH3Receiver velocity t)

/-- At the sixfold dyadic radius, the unsquared tail scale is at most `H⁻¹`. -/
theorem jacobianTailScale_dyadicRadius_le_inv
    {highOrder : ℝ} (hhighOrder : 1 ≤ highOrder) :
    jacobianTailScale (jacobianTailDyadicRadius highOrder) ≤ highOrder⁻¹ := by
  let depth : ℕ := shellDepth highOrder
  let radiusReal : ℝ := (2 : ℝ) ^ (6 * depth)
  have hhighOrderPos : 0 < highOrder := zero_lt_one.trans_le hhighOrder
  have hradiusPos : 0 < radiusReal := by
    dsimp [radiusReal]
    positivity
  have hbase : radiusReal ≤ radiusReal + 1 := by linarith
  have hscaleToPower :
      jacobianTailScale (jacobianTailDyadicRadius highOrder) ≤
        radiusReal ^ (-(1 / 6 : ℝ)) := by
    unfold jacobianTailScale
    have hcast : (jacobianTailDyadicRadius highOrder : ℝ) = radiusReal := by
      simp [jacobianTailDyadicRadius, jacobianTailDyadicDepth,
        radiusReal, depth]
    rw [hcast]
    exact Real.rpow_le_rpow_of_nonpos hradiusPos hbase (by norm_num)
  have hpower : radiusReal ^ (-(1 / 6 : ℝ)) =
      ((2 : ℝ) ^ (depth : ℝ))⁻¹ := by
    dsimp [radiusReal]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    push_cast
    ring
  have hdyadic : highOrder ≤ (2 : ℝ) ^ (depth : ℝ) := by
    dsimp [depth]
    exact le_two_rpow_shellDepth hhighOrder
  have hinv : ((2 : ℝ) ^ (depth : ℝ))⁻¹ ≤ highOrder⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) _)
      hhighOrderPos).mpr hdyadic
  exact hscaleToPower.trans (hpower.le.trans hinv)

/-- The tail scale and the high-order receiver multiply to at most one. -/
theorem jacobianTailScale_dyadicRadius_mul_le_one
    {highOrder : ℝ} (hhighOrder : 1 ≤ highOrder) :
    jacobianTailScale (jacobianTailDyadicRadius highOrder) * highOrder ≤ 1 := by
  have hscale := jacobianTailScale_dyadicRadius_le_inv hhighOrder
  have hnonneg := jacobianTailScale_nonneg (jacobianTailDyadicRadius highOrder)
  have hpositive : 0 < highOrder := zero_lt_one.trans_le hhighOrder
  calc
    jacobianTailScale (jacobianTailDyadicRadius highOrder) * highOrder ≤
        highOrder⁻¹ * highOrder :=
      mul_le_mul_of_nonneg_right hscale hpositive.le
    _ = 1 := inv_mul_cancel₀ hpositive.ne'

/-- Abstract square-root balance, retaining the finite lattice mass as an explicit receiver. -/
theorem sqrt_tailScale_mass_mul_sqrt_highOrder_le
    {highOrder : ℝ} (hhighOrder : 1 ≤ highOrder) :
    Real.sqrt
          (jacobianTailScale (jacobianTailDyadicRadius highOrder) *
            jacobianTailLatticeMass) *
        Real.sqrt highOrder ≤
      Real.sqrt jacobianTailLatticeMass := by
  have hscaleNonneg := jacobianTailScale_nonneg
    (jacobianTailDyadicRadius highOrder)
  have hmassNonneg := jacobianTailLatticeMass_nonneg
  have hhighNonneg : 0 ≤ highOrder := le_trans (by norm_num) hhighOrder
  rw [← Real.sqrt_mul (mul_nonneg hscaleNonneg hmassNonneg) highOrder]
  rw [show jacobianTailScale (jacobianTailDyadicRadius highOrder) *
        jacobianTailLatticeMass * highOrder =
      jacobianTailLatticeMass *
        (jacobianTailScale (jacobianTailDyadicRadius highOrder) * highOrder) by ring]
  apply Real.sqrt_le_sqrt
  calc
    jacobianTailLatticeMass *
        (jacobianTailScale (jacobianTailDyadicRadius highOrder) * highOrder) ≤
      jacobianTailLatticeMass * 1 :=
        mul_le_mul_of_nonneg_left
          (jacobianTailScale_dyadicRadius_mul_le_one hhighOrder) hmassNonneg
    _ = jacobianTailLatticeMass := mul_one _

/-- The literal actual Jacobian reconstruction fibre at the balanced aperture is bounded by a
fixed constant independent of the current `H³` receiver. -/
theorem openPeriodicJacobianCoefficientTailMass_balanced_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
        (frequencyCube
          (jacobianTailDyadicRadius (coordinateLogH3Receiver velocity t))) ≤
      (2 * Real.pi) * Real.sqrt 240 *
        Real.sqrt jacobianTailLatticeMass := by
  let highOrder : ℝ := coordinateLogH3Receiver velocity t
  have hhighOrder : 1 ≤ highOrder :=
    one_le_coordinateLogH3Receiver velocity t
  have htail :=
    openPeriodicJacobianCoefficientTailMass_frequencyCube_le_logReceiver
      solution ht (jacobianTailDyadicRadius highOrder)
  have hbalance := sqrt_tailScale_mass_mul_sqrt_highOrder_le hhighOrder
  calc
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
        (frequencyCube (jacobianTailDyadicRadius highOrder)) ≤
      (2 * Real.pi) *
        Real.sqrt
          (jacobianTailScale (jacobianTailDyadicRadius highOrder) *
            jacobianTailLatticeMass) * Real.sqrt (240 * highOrder) := htail
    _ = (2 * Real.pi) * Real.sqrt 240 *
        (Real.sqrt
          (jacobianTailScale (jacobianTailDyadicRadius highOrder) *
            jacobianTailLatticeMass) * Real.sqrt highOrder) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 240)]
      ring
    _ ≤ (2 * Real.pi) * Real.sqrt 240 *
        Real.sqrt jacobianTailLatticeMass := by
      exact mul_le_mul_of_nonneg_left hbalance (by positivity)

section Audit

#print axioms jacobianTailScale_dyadicRadius_le_inv
#print axioms jacobianTailDyadicDepth_cast_le_log
#print axioms jacobianTailDyadicDepth_coordinateLogH3Receiver_le
#print axioms jacobianTailScale_dyadicRadius_mul_le_one
#print axioms sqrt_tailScale_mass_mul_sqrt_highOrder_le
#print axioms openPeriodicJacobianCoefficientTailMass_balanced_le

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailBalance
