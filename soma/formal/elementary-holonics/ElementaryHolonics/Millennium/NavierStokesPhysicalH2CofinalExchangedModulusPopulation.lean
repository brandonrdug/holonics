import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion

/-!
# Complete cofinal modulus population of physical H2 exchanged faces

**[proved-derived; formal-checked]** The literal completed exchanged face is absolutely
summable over the complete ordered transport-address population on every strict-interior slice.
The proof retains every address: transported-pin weight is reindexed from the already summable
receiver-pin population by the exact transport/receiver exchange, and the pointwise completed
face is their difference.

The coordinate `H2` nonlinear production current is at most one half of this complete modulus
population.  The factor is inherited from the exact signed finite exchanged-current identity;
the bound passes through the common three-pin cubes before taking the cofinal limit.

No time integrability, source payment, running service, packing, terminal estimate, or
Navier--Stokes closure claim is made.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCubeExhaustion
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Literal complete addressed modulus population -/

/-- The real complete modulus population
`Φ_F(t) = ∑' address, ‖physicalH2VelocityExchangedTriadFace u(t) address‖`. -/
def physicalH2CofinalExchangedModulusPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∑' address : CompleteTransportAddress,
    ‖physicalH2VelocityExchangedTriadFace
      (openPeriodicVelocityFourierMode solution t) address‖

/-- Transport-pin modulus is summable by the exact exchange equivalence applied to the public
receiver-weighted absolute population. -/
theorem summable_norm_completeOpenTransportedWeightedPhysicalH2VelocityAdvectionFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      ‖transportedWeightedPhysicalH2VelocityAdvectionFace
        (openPeriodicVelocityFourierMode solution t) address‖ := by
  have hreindexed :=
    (summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace
      solution t).comp_injective completeTransportExchange.injective
  refine hreindexed.congr fun address ↦ ?_
  change
    ‖receiverWeightedPhysicalH2VelocityAdvectionFace
      (openPeriodicVelocityFourierMode solution t)
      (completeTransportExchange address)‖ = _
  rw [receiverWeightedPhysicalH2VelocityAdvectionFace_exchange
    (openPeriodicVelocityFourierMode solution t) address
    (openPeriodicVelocityFourierMode_divergenceFree solution t address.1)]
  exact norm_neg _

/-- Absolute summability of the literal completed exchanged face over all ordered addresses. -/
theorem summable_norm_completeOpenPhysicalH2VelocityExchangedTriadFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution t) address‖ := by
  have htransported :=
    summable_norm_completeOpenTransportedWeightedPhysicalH2VelocityAdvectionFace
      solution t
  have hreceiver :=
    summable_norm_completeOpenReceiverWeightedPhysicalH2VelocityAdvectionFace solution t
  refine Summable.of_nonneg_of_le (fun _address ↦ norm_nonneg _)
    (fun address ↦ ?_) (htransported.add hreceiver)
  rw [physicalH2VelocityExchangedTriadFace_eq_transported_sub_receiver
    (openPeriodicVelocityFourierMode solution t) address
    (openPeriodicVelocityFourierMode_divergenceFree solution t address.1)]
  exact norm_sub_le _ _

theorem physicalH2CofinalExchangedModulusPopulation_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    0 ≤ physicalH2CofinalExchangedModulusPopulation solution t := by
  exact tsum_nonneg fun _address ↦ norm_nonneg _

/-! ## Common-cube passage to the coordinate production current -/

/-- The norm of each finite common-cube exchanged current is bounded by the same cube's literal
modulus population. -/
theorem norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_modulusPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ ≤
      ∑ address ∈ physicalH2VelocityTriadAperture radius,
        ‖physicalH2VelocityExchangedTriadFace
          (openPeriodicVelocityFourierMode solution t) address‖ := by
  unfold finiteOpenPhysicalH2VelocityExchangedTriadCurrent
    finitePhysicalH2VelocityExchangedTriadCurrent
  exact norm_sum_le _ _

/-- Every finite common-cube modulus population is bounded by the complete addressed population. -/
theorem finiteOpenPhysicalH2VelocityExchangedTriadModulusPopulation_le_complete
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    (∑ address ∈ physicalH2VelocityTriadAperture radius,
      ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution t) address‖) ≤
      physicalH2CofinalExchangedModulusPopulation solution t := by
  exact (summable_norm_completeOpenPhysicalH2VelocityExchangedTriadFace solution t).sum_le_tsum
    (physicalH2VelocityTriadAperture radius) (fun _address _haddress ↦ norm_nonneg _)

/-- The literal coordinate nonlinear production current is bounded by one half of the complete
cofinal exchanged-face modulus population.  The half is exact before the norm quotient. -/
theorem abs_coordinateH2NonlinearProductionCurrent_le_half_cofinalExchangedModulusPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    |coordinateH2NonlinearProductionCurrent velocity t.1| ≤
      (1 / 2 : ℝ) * physicalH2CofinalExchangedModulusPopulation solution t := by
  rw [← completePhysicalH2VelocityCurrent_eq_coordinateH2NonlinearProductionCurrent
    solution t]
  have hlimit :=
    tendsto_half_re_finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t
  have habs : Tendsto
      (fun radius : ℕ ↦
        |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re|)
      atTop (nhds |completePhysicalH2VelocityCurrent solution t|) :=
    continuous_abs.tendsto _ |>.comp hlimit
  apply le_of_tendsto habs
  exact Filter.Eventually.of_forall fun radius ↦ by
    calc
      |(1 / 2 : ℝ) *
          (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius).re| =
          (1 / 2 : ℝ) *
            |(finiteOpenPhysicalH2VelocityExchangedTriadCurrent
              solution t radius).re| := by
        rw [abs_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) *
          ‖finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius‖ :=
        mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm
            (finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius))
          (by norm_num)
      _ ≤ (1 / 2 : ℝ) *
          (∑ address ∈ physicalH2VelocityTriadAperture radius,
            ‖physicalH2VelocityExchangedTriadFace
              (openPeriodicVelocityFourierMode solution t) address‖) :=
        mul_le_mul_of_nonneg_left
          (norm_finiteOpenPhysicalH2VelocityExchangedTriadCurrent_le_modulusPopulation
            solution t radius) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * physicalH2CofinalExchangedModulusPopulation solution t :=
        mul_le_mul_of_nonneg_left
          (finiteOpenPhysicalH2VelocityExchangedTriadModulusPopulation_le_complete
            solution t radius) (by norm_num)

section Audit

#print axioms summable_norm_completeOpenTransportedWeightedPhysicalH2VelocityAdvectionFace
#print axioms summable_norm_completeOpenPhysicalH2VelocityExchangedTriadFace
#print axioms finiteOpenPhysicalH2VelocityExchangedTriadModulusPopulation_le_complete
#print axioms abs_coordinateH2NonlinearProductionCurrent_le_half_cofinalExchangedModulusPopulation

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CofinalExchangedModulusPopulation
