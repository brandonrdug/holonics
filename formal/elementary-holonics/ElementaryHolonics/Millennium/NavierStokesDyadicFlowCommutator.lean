import ElementaryHolonics.Millennium.NavierStokesFourierTriads
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-!
# The finite dyadic flow commutator

**[proved-derived]** This owner keeps one finite population of advecting Fourier pins and compares
the two sides of the multiplier--interaction square.  At output `k`, an advecting address `p`
determines the transported address `q = k - p`; the square defect is exactly the multiplier
difference `m k - m q` acting on the existing advective interaction.

The dyadic specialization uses the direct Hodge-band multiplier already owned by the scale chain.
No norm, infinite sum, regularity hypothesis, or convergence assertion enters this finite identity.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-- The transported pin addressed by an output `k` and an advecting pin `p`. -/
def transportedFrequencyAt (k p : SpatialFrequency) : SpatialFrequency :=
  k - p

/-- The two retained pin addresses close on the requested output. -/
theorem advecting_add_transportedFrequencyAt (k p : SpatialFrequency) :
    p + transportedFrequencyAt k p = k := by
  simp only [transportedFrequencyAt]
  abel

/-- A finite-aperture advective coefficient, assembled from the existing addressed interaction.
The aperture restricts only the advecting address; its paired transported address remains visible
as `k - p` in every summand. -/
def finiteAdvectiveCoefficient
    (aperture : Finset SpatialFrequency)
    (advecting transported : SpatialFrequency → ComplexVector)
    (k : SpatialFrequency) : ComplexVector :=
  ∑ p ∈ aperture,
    complexAdvectiveInteraction p (transportedFrequencyAt k p)
      (advecting p) (transported (transportedFrequencyAt k p))

/-- A scalar Fourier multiplier acting on a vector-valued coefficient population. -/
def multiplierFilter
    (multiplier : SpatialFrequency → ℂ)
    (field : SpatialFrequency → ComplexVector) :
    SpatialFrequency → ComplexVector :=
  fun k ↦ multiplier k • field k

/-- The finite comparison between the path "interact, then filter the output" and the path
"filter the transported pin, then interact". -/
def finiteMultiplierFlowCommutatorCoefficient
    (aperture : Finset SpatialFrequency)
    (multiplier : SpatialFrequency → ℂ)
    (advecting transported : SpatialFrequency → ComplexVector)
    (k : SpatialFrequency) : ComplexVector :=
  multiplierFilter multiplier
      (finiteAdvectiveCoefficient aperture advecting transported) k -
    finiteAdvectiveCoefficient aperture advecting
      (multiplierFilter multiplier transported) k

/-- Scalar transport on the transported mode commutes through one existing advective interaction.
This is the local algebraic face used by the finite comparison square. -/
theorem complexAdvectiveInteraction_smul_transported
    (p q : SpatialFrequency) (advectingMode transportedMode : ComplexVector) (c : ℂ) :
    complexAdvectiveInteraction p q advectingMode (c • transportedMode) =
      c • complexAdvectiveInteraction p q advectingMode transportedMode := by
  unfold complexAdvectiveInteraction
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- **Exact finite multiplier gyroparallelogram.**  The commutator retains every intermediate
`p, q` address and is precisely the finite sum of multiplier differences along the transported
edge of each interaction face. -/
theorem finiteMultiplierFlowCommutatorCoefficient_eq_sum_difference
    (aperture : Finset SpatialFrequency)
    (multiplier : SpatialFrequency → ℂ)
    (advecting transported : SpatialFrequency → ComplexVector)
    (k : SpatialFrequency) :
    finiteMultiplierFlowCommutatorCoefficient aperture multiplier
        advecting transported k =
      ∑ p ∈ aperture,
        (multiplier k - multiplier (transportedFrequencyAt k p)) •
          complexAdvectiveInteraction p (transportedFrequencyAt k p)
            (advecting p) (transported (transportedFrequencyAt k p)) := by
  classical
  unfold finiteMultiplierFlowCommutatorCoefficient multiplierFilter
    finiteAdvectiveCoefficient
  rw [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [complexAdvectiveInteraction_smul_transported, sub_smul]

/-- The existing direct dyadic Hodge-band weight, viewed in the complex coefficient chart. -/
def dyadicHodgeBandMultiplier (scale : ℕ) : SpatialFrequency → ℂ :=
  fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ)

/-- The finite flow commutator for one exact direct dyadic Hodge band. -/
def finiteDyadicFlowCommutatorCoefficient
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (advecting transported : SpatialFrequency → ComplexVector)
    (k : SpatialFrequency) : ComplexVector :=
  finiteMultiplierFlowCommutatorCoefficient aperture
    (dyadicHodgeBandMultiplier scale) advecting transported k

/-- **Exact dyadic coefficient law for `[P_s, u·∇]v`.**  At output `k`, every finite
advecting pin `p` retains its transported partner `q = k-p`, and the entire square defect is the
dyadic multiplier difference `m_s(k)-m_s(q)` times that addressed advective interaction. -/
theorem finiteDyadicFlowCommutatorCoefficient_eq_sum_difference
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (advecting transported : SpatialFrequency → ComplexVector)
    (k : SpatialFrequency) :
    finiteDyadicFlowCommutatorCoefficient scale aperture advecting transported k =
      ∑ p ∈ aperture,
        ((dyadicHodgeBandWeight scale k : ℂ) -
            (dyadicHodgeBandWeight scale (transportedFrequencyAt k p) : ℂ)) •
          complexAdvectiveInteraction p (transportedFrequencyAt k p)
            (advecting p) (transported (transportedFrequencyAt k p)) := by
  exact finiteMultiplierFlowCommutatorCoefficient_eq_sum_difference
    aperture (dyadicHodgeBandMultiplier scale) advecting transported k

section Audit

#print axioms advecting_add_transportedFrequencyAt
#print axioms complexAdvectiveInteraction_smul_transported
#print axioms finiteMultiplierFlowCommutatorCoefficient_eq_sum_difference
#print axioms finiteDyadicFlowCommutatorCoefficient_eq_sum_difference

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
