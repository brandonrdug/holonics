import ElementaryHolonics.Millennium.NavierStokesH2TriadShellLeverBound

/-!
# The dyadic separation kernel retained by the H2 triad swing

**[proved-derived; formal-checked]**  The exact high--high--low multiplier lever retains the
ratio of the advecting shell length to the exchanged shell length.  This owner identifies that
actual ratio as a half-power and sums a strictly separated finite row uniformly in its high level.

Comparable-scale and high--high--high interactions are outside every result in this file.  The
weighted statements only compose the already-proved single-triad estimate over a finite family;
they do not assert control of the complete nonlinear production current.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2DyadicSeparationKernel

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The actual dyadic ratio -/

/-- Under the weak ordering needed to form the natural-number difference, the actual ratio of
the existing dyadic outer radii is the corresponding power of one half. -/
theorem dyadicLowHighLengthRatio_eq_half_pow
    {lowLevel highLevel : ℕ} (hlowHigh : lowLevel ≤ highLevel) :
    dyadicLowHighLengthRatio lowLevel highLevel =
      ((1 : ℝ) / 2) ^ (highLevel - lowLevel) := by
  have hlevel : highLevel + 1 = (lowLevel + 1) + (highLevel - lowLevel) := by
    omega
  have hbase : (2 : ℝ) ^ (lowLevel + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold dyadicLowHighLengthRatio dyadicRadius
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hlevel]
  nth_rewrite 2 [pow_add]
  calc
    (2 : ℝ) ^ (lowLevel + 1) /
        ((2 : ℝ) ^ (lowLevel + 1) * (2 : ℝ) ^ (highLevel - lowLevel)) =
      1 / (2 : ℝ) ^ (highLevel - lowLevel) := by
        field_simp
    _ = ((1 : ℝ) / 2) ^ (highLevel - lowLevel) := by
      rw [div_pow]
      simp

/-! ## Uniform finite rows of genuinely separated levels -/

/-- The finite row indexed by a high level contains exactly its strictly lower shell levels.
Consequently every summand satisfies `lowLevel + 1 ≤ highLevel`; no comparable shell is inserted
by a zero-extension convention. -/
def strictDyadicSeparationRowSum (highLevel : ℕ) : ℝ :=
  ∑ lowLevel ∈ Finset.range highLevel,
    dyadicLowHighLengthRatio lowLevel highLevel

/-- The actual strictly-separated row is the initial geometric half-series, with its exact
unspent tail retained. -/
theorem strictDyadicSeparationRowSum_eq (highLevel : ℕ) :
    strictDyadicSeparationRowSum highLevel =
      1 - ((1 : ℝ) / 2) ^ highLevel := by
  let q : ℝ := (1 : ℝ) / 2
  calc
    strictDyadicSeparationRowSum highLevel =
        ∑ lowLevel ∈ Finset.range highLevel, q ^ (highLevel - lowLevel) := by
      unfold strictDyadicSeparationRowSum
      apply Finset.sum_congr rfl
      intro lowLevel hlowLevel
      exact dyadicLowHighLengthRatio_eq_half_pow
        (Nat.le_of_lt (Finset.mem_range.mp hlowLevel))
    _ = ∑ offset ∈ Finset.range highLevel, q ^ (offset + 1) := by
      rw [← Finset.sum_range_reflect (fun offset ↦ q ^ (offset + 1)) highLevel]
      apply Finset.sum_congr rfl
      intro lowLevel hlowLevel
      have hlt : lowLevel < highLevel := Finset.mem_range.mp hlowLevel
      congr 1
      omega
    _ = q * ∑ offset ∈ Finset.range highLevel, q ^ offset := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro offset _hoffset
      rw [pow_succ']
    _ = 1 - q ^ highLevel := by
      rw [geom_sum_eq (by norm_num [q] : q ≠ 1)]
      dsimp only [q]
      field_simp
      ring
    _ = 1 - ((1 : ℝ) / 2) ^ highLevel := rfl

/-- Every actual dyadic length ratio is nonnegative. -/
theorem dyadicLowHighLengthRatio_nonneg (lowLevel highLevel : ℕ) :
    0 ≤ dyadicLowHighLengthRatio lowLevel highLevel := by
  unfold dyadicLowHighLengthRatio
  positivity

/-- The exact separated row lies between zero and one, uniformly in its high shell. -/
theorem strictDyadicSeparationRowSum_nonneg_le_one (highLevel : ℕ) :
    0 ≤ strictDyadicSeparationRowSum highLevel ∧
      strictDyadicSeparationRowSum highLevel ≤ 1 := by
  rw [strictDyadicSeparationRowSum_eq]
  have hpowNonneg : 0 ≤ ((1 : ℝ) / 2) ^ highLevel := by positivity
  have hpowLe : ((1 : ℝ) / 2) ^ highLevel ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> linarith

/-- A finite nonnegative population weighted by the actual separated kernel has mass at most its
uniform weight bound.  This is the scale-row summation receiver used below; the kernel is not
replaced by `1` before the finite sum is formed. -/
theorem sum_dyadicLowHighLengthRatio_mul_le
    (highLevel : ℕ) (weight : ℕ → ℝ) (weightBound : ℝ)
    (hweightNonneg : ∀ lowLevel < highLevel, 0 ≤ weight lowLevel)
    (hweightBound : ∀ lowLevel < highLevel, weight lowLevel ≤ weightBound)
    (hboundNonneg : 0 ≤ weightBound) :
    0 ≤ ∑ lowLevel ∈ Finset.range highLevel,
        dyadicLowHighLengthRatio lowLevel highLevel * weight lowLevel ∧
      (∑ lowLevel ∈ Finset.range highLevel,
        dyadicLowHighLengthRatio lowLevel highLevel * weight lowLevel) ≤ weightBound := by
  constructor
  · exact Finset.sum_nonneg fun lowLevel hlowLevel ↦
      mul_nonneg (dyadicLowHighLengthRatio_nonneg lowLevel highLevel)
        (hweightNonneg lowLevel (Finset.mem_range.mp hlowLevel))
  · calc
      (∑ lowLevel ∈ Finset.range highLevel,
          dyadicLowHighLengthRatio lowLevel highLevel * weight lowLevel) ≤
          ∑ lowLevel ∈ Finset.range highLevel,
            dyadicLowHighLengthRatio lowLevel highLevel * weightBound := by
        exact Finset.sum_le_sum fun lowLevel hlowLevel ↦
          mul_le_mul_of_nonneg_left
            (hweightBound lowLevel (Finset.mem_range.mp hlowLevel))
            (dyadicLowHighLengthRatio_nonneg lowLevel highLevel)
      _ = strictDyadicSeparationRowSum highLevel * weightBound := by
        unfold strictDyadicSeparationRowSum
        rw [Finset.sum_mul]
      _ ≤ 1 * weightBound :=
        mul_le_mul_of_nonneg_right
          (strictDyadicSeparationRowSum_nonneg_le_one highLevel).2 hboundNonneg
      _ = weightBound := one_mul _

/-! ## Direct finite summation of the single-triad H2 lever -/

/-- The existing single-triad high--high--low estimate rewritten in its scale-normalized form.
The high-square aperture is common to the row, while the actual low/high ratio remains attached
to this interaction until after the exact exchanged cancellation and norm receiver. -/
theorem norm_h2ExchangedTriadTransfer_le_ratio_mul_high_sq
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖h2ExchangedTriadTransfer triad advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicLowHighLengthRatio lowLevel highLevel *
          (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
            ‖triadicEnergyFace triad.advecting triad.transported
              advectingMode transportedMode receiverMode‖ := by
  calc
    ‖h2ExchangedTriadTransfer triad advectingMode transportedMode receiverMode‖ ≤
        (primitiveTorusStokesScale *
          (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
            (dyadicRadius (highLevel + 1) : ℝ))) *
              ‖triadicEnergyFace triad.advecting triad.transported
                advectingMode transportedMode receiverMode‖ :=
      norm_h2ExchangedTriadTransfer_le_of_highHighLowDyadic triad lowLevel highLevel
        advectingMode transportedMode receiverMode hdivergence hseparated
        hadvecting htransported hreceiver
    _ = (primitiveTorusStokesScale *
        (6 * dyadicLowHighLengthRatio lowLevel highLevel *
          (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
            ‖triadicEnergyFace triad.advecting triad.transported
              advectingMode transportedMode receiverMode‖ := by
      rw [show 6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ) =
        6 * ((dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) by ring,
        dyadic_low_mul_high_eq_ratio_mul_high_sq]
      ring

/-- A finite row of actual exchanged H2 transfers is bounded by the ratio-weighted row of its
oriented triadic faces.  Every index in `range highLevel` is genuinely separated, so this theorem
does not include the comparable high shell or any high--high--high interaction. -/
theorem sum_norm_h2ExchangedTriadTransfer_le_ratioWeightedFaces
    (highLevel : ℕ)
    (triad : ℕ → AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ℕ → ComplexVector)
    (hdivergence : ∀ lowLevel < highLevel,
      complexDot (complexFrequencyVector (triad lowLevel).advecting)
        (advectingMode lowLevel) = 0)
    (hadvecting : ∀ lowLevel < highLevel,
      (triad lowLevel).advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : ∀ lowLevel < highLevel,
      (triad lowLevel).transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : ∀ lowLevel < highLevel,
      (triad lowLevel).receiver ∈ dyadicFrequencyShell highLevel) :
    (∑ lowLevel ∈ Finset.range highLevel,
      ‖h2ExchangedTriadTransfer (triad lowLevel) (advectingMode lowLevel)
        (transportedMode lowLevel) (receiverMode lowLevel)‖) ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
          ∑ lowLevel ∈ Finset.range highLevel,
            dyadicLowHighLengthRatio lowLevel highLevel *
              ‖triadicEnergyFace (triad lowLevel).advecting
                (triad lowLevel).transported (advectingMode lowLevel)
                (transportedMode lowLevel) (receiverMode lowLevel)‖ := by
  calc
    (∑ lowLevel ∈ Finset.range highLevel,
      ‖h2ExchangedTriadTransfer (triad lowLevel) (advectingMode lowLevel)
        (transportedMode lowLevel) (receiverMode lowLevel)‖) ≤
        ∑ lowLevel ∈ Finset.range highLevel,
          (primitiveTorusStokesScale *
            (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
              (dyadicLowHighLengthRatio lowLevel highLevel *
                ‖triadicEnergyFace (triad lowLevel).advecting
                  (triad lowLevel).transported (advectingMode lowLevel)
                  (transportedMode lowLevel) (receiverMode lowLevel)‖) := by
      apply Finset.sum_le_sum
      intro lowLevel hlowLevel
      have hlt : lowLevel < highLevel := Finset.mem_range.mp hlowLevel
      calc
        ‖h2ExchangedTriadTransfer (triad lowLevel) (advectingMode lowLevel)
            (transportedMode lowLevel) (receiverMode lowLevel)‖ ≤
          (primitiveTorusStokesScale *
            (6 * dyadicLowHighLengthRatio lowLevel highLevel *
              (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
                ‖triadicEnergyFace (triad lowLevel).advecting
                  (triad lowLevel).transported (advectingMode lowLevel)
                  (transportedMode lowLevel) (receiverMode lowLevel)‖ :=
          norm_h2ExchangedTriadTransfer_le_ratio_mul_high_sq
            (triad lowLevel) lowLevel highLevel (advectingMode lowLevel)
            (transportedMode lowLevel) (receiverMode lowLevel)
            (hdivergence lowLevel hlt) (by omega) (hadvecting lowLevel hlt)
            (htransported lowLevel hlt) (hreceiver lowLevel hlt)
        _ = (primitiveTorusStokesScale *
            (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
              (dyadicLowHighLengthRatio lowLevel highLevel *
                ‖triadicEnergyFace (triad lowLevel).advecting
                  (triad lowLevel).transported (advectingMode lowLevel)
                  (transportedMode lowLevel) (receiverMode lowLevel)‖) := by ring
    _ = (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
          ∑ lowLevel ∈ Finset.range highLevel,
            dyadicLowHighLengthRatio lowLevel highLevel *
              ‖triadicEnergyFace (triad lowLevel).advecting
                (triad lowLevel).transported (advectingMode lowLevel)
                (transportedMode lowLevel) (receiverMode lowLevel)‖ := by
      rw [Finset.mul_sum]

/-- If the oriented triadic faces in one strictly separated row share a finite norm bound, the
complete row of exchanged H2 transfers inherits that bound with a high-level-independent kernel
constant.  The remaining high-square factor is the physical multiplier scale, not row-count loss. -/
theorem sum_norm_h2ExchangedTriadTransfer_le_of_faceBound
    (highLevel : ℕ)
    (triad : ℕ → AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ℕ → ComplexVector)
    (faceBound : ℝ)
    (hdivergence : ∀ lowLevel < highLevel,
      complexDot (complexFrequencyVector (triad lowLevel).advecting)
        (advectingMode lowLevel) = 0)
    (hadvecting : ∀ lowLevel < highLevel,
      (triad lowLevel).advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : ∀ lowLevel < highLevel,
      (triad lowLevel).transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : ∀ lowLevel < highLevel,
      (triad lowLevel).receiver ∈ dyadicFrequencyShell highLevel)
    (hfaceBound : ∀ lowLevel < highLevel,
      ‖triadicEnergyFace (triad lowLevel).advecting
        (triad lowLevel).transported (advectingMode lowLevel)
        (transportedMode lowLevel) (receiverMode lowLevel)‖ ≤ faceBound)
    (hboundNonneg : 0 ≤ faceBound) :
    (∑ lowLevel ∈ Finset.range highLevel,
      ‖h2ExchangedTriadTransfer (triad lowLevel) (advectingMode lowLevel)
        (transportedMode lowLevel) (receiverMode lowLevel)‖) ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) * faceBound := by
  let commonScale : ℝ := primitiveTorusStokesScale *
    (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)
  let faceWeight : ℕ → ℝ := fun lowLevel ↦
    ‖triadicEnergyFace (triad lowLevel).advecting
      (triad lowLevel).transported (advectingMode lowLevel)
      (transportedMode lowLevel) (receiverMode lowLevel)‖
  have hweighted := sum_dyadicLowHighLengthRatio_mul_le highLevel faceWeight faceBound
    (fun lowLevel _hlt ↦ norm_nonneg _) hfaceBound hboundNonneg
  have hcommonNonneg : 0 ≤ commonScale := by
    dsimp only [commonScale]
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (by norm_num) (sq_nonneg _))
  calc
    (∑ lowLevel ∈ Finset.range highLevel,
      ‖h2ExchangedTriadTransfer (triad lowLevel) (advectingMode lowLevel)
        (transportedMode lowLevel) (receiverMode lowLevel)‖) ≤
      commonScale * ∑ lowLevel ∈ Finset.range highLevel,
        dyadicLowHighLengthRatio lowLevel highLevel * faceWeight lowLevel := by
          dsimp only [commonScale, faceWeight]
          exact sum_norm_h2ExchangedTriadTransfer_le_ratioWeightedFaces highLevel
            triad advectingMode transportedMode receiverMode hdivergence hadvecting
            htransported hreceiver
    _ ≤ commonScale * faceBound :=
      mul_le_mul_of_nonneg_left hweighted.2 hcommonNonneg
    _ = (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) * faceBound := rfl

section Audit

#print axioms dyadicLowHighLengthRatio_eq_half_pow
#print axioms strictDyadicSeparationRowSum_eq
#print axioms dyadicLowHighLengthRatio_nonneg
#print axioms strictDyadicSeparationRowSum_nonneg_le_one
#print axioms sum_dyadicLowHighLengthRatio_mul_le
#print axioms norm_h2ExchangedTriadTransfer_le_ratio_mul_high_sq
#print axioms sum_norm_h2ExchangedTriadTransfer_le_ratioWeightedFaces
#print axioms sum_norm_h2ExchangedTriadTransfer_le_of_faceBound

end Audit

end Soma.Holonics.Millennium.NavierStokesH2DyadicSeparationKernel
