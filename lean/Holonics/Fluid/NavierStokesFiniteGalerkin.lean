import Holonics.Fluid.NavierStokesMildFourierNonlinearity

/-!
# The finite Galerkin Navier–Stokes vector field

[definition] One fixed finite carrier of Fourier addresses carries the Galerkin state. Its
vector field is the Stokes response of each retained mode minus the Leray-projected advective
interaction, assembled over a finite aperture of advecting addresses; the transported address of
each summand stays visible as `k - p`.

[proved-derived; formal-checked] The projected interaction is bilinear on the carrier, its
difference is exactly the two cross terms and the marked–marked term, and its norm is paid by
coordinate atoms of the two zero-extended states (the bounds the Picard chain's local Lipschitz
estimate reads). This is the finite carrier that the framework's changing-receiver instance
(`Physics/FluidReceiverClosure`) consumes; the Picard iteration, ancestry services and the rest of
the Navier–Stokes target chain build on it in `HolonicsResearch/Fluid`.

No continuum or Galerkin-limit claim is made here.
-/

noncomputable section

open Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Interval Nat

namespace Holonics.Fluid.NavierStokesFiniteGalerkin

open Holonics.Fluid.NavierStokesTorusFourier
open Holonics.Fluid.NavierStokesFourierTriads
open Holonics.Fluid.NavierStokesFiniteFourierHeat
open Holonics.Fluid.NavierStokesMildFourierNonlinearity

/-- The transported pin addressed by an output `k` and an advecting pin `p`. -/
def transportedFrequencyAt (k p : SpatialFrequency) : SpatialFrequency :=
  k - p

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

/-- One complete complex-vector Fourier population. -/
abbrev ComplexFourierModePopulation := SpatialFrequency → ComplexVector

/-- The finite advective coefficient followed by its exact pressure-eliminating receiver. -/
def finiteProjectedAdvectiveCoefficient
    (aperture : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation) :
    ComplexFourierModePopulation :=
  fun output ↦
    lerayProjectMode output
      (finiteAdvectiveCoefficient aperture advecting transported output)

theorem finiteAdvectiveCoefficient_add_add
    (aperture : Finset SpatialFrequency)
    (leftAdvecting highAdvecting leftTransported highTransported :
      ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    finiteAdvectiveCoefficient aperture
        (fun frequency ↦ leftAdvecting frequency + highAdvecting frequency)
        (fun frequency ↦ leftTransported frequency + highTransported frequency)
        output =
      finiteAdvectiveCoefficient aperture leftAdvecting leftTransported output +
        finiteAdvectiveCoefficient aperture highAdvecting leftTransported output +
        finiteAdvectiveCoefficient aperture leftAdvecting highTransported output +
        finiteAdvectiveCoefficient aperture highAdvecting highTransported output := by
  unfold finiteAdvectiveCoefficient
  simp_rw [show ∀ parent : SpatialFrequency,
      complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          (leftAdvecting parent + highAdvecting parent)
          (leftTransported (transportedFrequencyAt output parent) +
            highTransported (transportedFrequencyAt output parent)) =
        complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (leftAdvecting parent) (leftTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (highAdvecting parent) (leftTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (leftAdvecting parent) (highTransported (transportedFrequencyAt output parent)) +
          complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
            (highAdvecting parent) (highTransported (transportedFrequencyAt output parent)) by
    intro parent
    unfold complexAdvectiveInteraction
    simp only [complexDot, dotProduct_add]
    module]
  simp only [Finset.sum_add_distrib]

/-- Expanding a projected quadratic source around its low population leaves precisely three
terms, and every term carries the marked population in at least one parent slot. -/
theorem finiteProjectedAdvectiveCoefficient_add_self_sub
    (aperture : Finset SpatialFrequency)
    (low marked : ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    finiteProjectedAdvectiveCoefficient aperture
        (fun frequency ↦ low frequency + marked frequency)
        (fun frequency ↦ low frequency + marked frequency) output -
      finiteProjectedAdvectiveCoefficient aperture low low output =
        finiteProjectedAdvectiveCoefficient aperture marked low output +
          finiteProjectedAdvectiveCoefficient aperture low marked output +
          finiteProjectedAdvectiveCoefficient aperture marked marked output := by
  unfold finiteProjectedAdvectiveCoefficient
  rw [finiteAdvectiveCoefficient_add_add, lerayProjectMode_add,
    lerayProjectMode_add, lerayProjectMode_add]
  abel

/-- The canonical coordinate atom used only to measure the already-founded interaction. -/
def complexVectorCoordinateAtom (component : Fin 3) : ComplexVector :=
  Pi.single component 1

/-- The complete nine-atom operator cost at one addressed projected interaction. -/
def finiteProjectedInteractionAtomCost
    (output parent : SpatialFrequency) : ℝ≥0∞ :=
  ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
    ‖lerayProjectMode output
      (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
        (complexVectorCoordinateAtom advectingComponent)
        (complexVectorCoordinateAtom transportedComponent))‖ₑ

theorem finiteProjectedInteractionAtomCost_ne_top
    (output parent : SpatialFrequency) :
    finiteProjectedInteractionAtomCost output parent ≠ ∞ := by
  unfold finiteProjectedInteractionAtomCost
  apply ENNReal.sum_ne_top.2
  intro _advectingComponent _hadvectingComponent
  apply ENNReal.sum_ne_top.2
  exact fun _transportedComponent _htransportedComponent ↦ enorm_ne_top

theorem complexAdvectiveInteraction_add_advecting
    (parent transported : SpatialFrequency)
    (left right transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported (left + right) transportedMode =
      complexAdvectiveInteraction parent transported left transportedMode +
        complexAdvectiveInteraction parent transported right transportedMode := by
  unfold complexAdvectiveInteraction
  simp only [complexDot, dotProduct_add]
  module

theorem complexAdvectiveInteraction_smul_advecting
    (parent transported : SpatialFrequency) (amplitude : ℂ)
    (advectingMode transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported
        (amplitude • advectingMode) transportedMode =
      amplitude • complexAdvectiveInteraction parent transported
        advectingMode transportedMode := by
  unfold complexAdvectiveInteraction
  simp only [complexDot, dotProduct_smul]
  module

theorem complexAdvectiveInteraction_add_transported
    (parent transported : SpatialFrequency)
    (advectingMode left right : ComplexVector) :
    complexAdvectiveInteraction parent transported advectingMode (left + right) =
      complexAdvectiveInteraction parent transported advectingMode left +
        complexAdvectiveInteraction parent transported advectingMode right := by
  unfold complexAdvectiveInteraction
  module

theorem complexAdvectiveInteraction_sum_advecting
    (parent transported : SpatialFrequency) (terms : Fin 3 → ComplexVector)
    (transportedMode : ComplexVector) :
    complexAdvectiveInteraction parent transported
        (∑ component, terms component) transportedMode =
      ∑ component, complexAdvectiveInteraction parent transported
        (terms component) transportedMode := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp [complexAdvectiveInteraction, complexDot]
  | @insert component remaining hcomponent inductionHypothesis =>
      rw [Finset.sum_insert hcomponent, Finset.sum_insert hcomponent,
        complexAdvectiveInteraction_add_advecting, inductionHypothesis]

theorem complexAdvectiveInteraction_sum_transported
    (parent transported : SpatialFrequency) (advectingMode : ComplexVector)
    (terms : Fin 3 → ComplexVector) :
    complexAdvectiveInteraction parent transported advectingMode
        (∑ component, terms component) =
      ∑ component, complexAdvectiveInteraction parent transported
        advectingMode (terms component) := by
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp [complexAdvectiveInteraction]
  | @insert component remaining hcomponent inductionHypothesis =>
      rw [Finset.sum_insert hcomponent, Finset.sum_insert hcomponent,
        complexAdvectiveInteraction_add_transported, inductionHypothesis]

theorem projectedInteraction_eq_atomExpansion
    (output parent : SpatialFrequency) (advecting transported : ComplexVector) :
    lerayProjectMode output
        (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          advecting transported) =
      ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
        (advecting advectingComponent * transported transportedComponent) •
          lerayProjectMode output
            (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
              (complexVectorCoordinateAtom advectingComponent)
              (complexVectorCoordinateAtom transportedComponent)) := by
  rw [pi_eq_sum_univ' advecting, pi_eq_sum_univ' transported,
    complexAdvectiveInteraction_sum_advecting]
  simp_rw [complexAdvectiveInteraction_smul_advecting,
    complexAdvectiveInteraction_sum_transported,
    complexAdvectiveInteraction_smul_transported]
  rw [lerayProjectMode_sum]
  simp_rw [lerayProjectMode_smul, lerayProjectMode_sum]
  simp_rw [lerayProjectMode_smul, Finset.smul_sum, smul_smul]
  simp [complexVectorCoordinateAtom, Finset.sum_apply, Pi.single_apply]

theorem enorm_projectedInteraction_le_atomCost
    (output parent : SpatialFrequency) (advecting transported : ComplexVector) :
    ‖lerayProjectMode output
        (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
          advecting transported)‖ₑ ≤
      finiteProjectedInteractionAtomCost output parent *
        ‖advecting‖ₑ * ‖transported‖ₑ := by
  rw [projectedInteraction_eq_atomExpansion]
  calc
    ‖∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
        (advecting advectingComponent * transported transportedComponent) •
          lerayProjectMode output
            (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
              (complexVectorCoordinateAtom advectingComponent)
              (complexVectorCoordinateAtom transportedComponent))‖ₑ ≤
        ∑ advectingComponent : Fin 3, ∑ transportedComponent : Fin 3,
          ‖(advecting advectingComponent * transported transportedComponent) •
            lerayProjectMode output
              (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                (complexVectorCoordinateAtom advectingComponent)
                (complexVectorCoordinateAtom transportedComponent))‖ₑ := by
      exact (enorm_sum_le _ _).trans
        (Finset.sum_le_sum fun _advectingComponent _hadvectingComponent ↦
          enorm_sum_le _ _)
    _ ≤ finiteProjectedInteractionAtomCost output parent *
          ‖advecting‖ₑ * ‖transported‖ₑ := by
      unfold finiteProjectedInteractionAtomCost
      simp_rw [enorm_smul, enorm_mul]
      have hadvecting (component : Fin 3) :
          ‖advecting component‖ₑ ≤ ‖advecting‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
        rw [Pi.nnnorm_def]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun index ↦ ‖advecting index‖₊) (Finset.mem_univ component)
      have htransported (component : Fin 3) :
          ‖transported component‖ₑ ≤ ‖transported‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
        rw [Pi.nnnorm_def]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun index ↦ ‖transported index‖₊) (Finset.mem_univ component)
      calc
        (∑ i : Fin 3, ∑ j : Fin 3,
            ‖advecting i‖ₑ * ‖transported j‖ₑ *
              ‖lerayProjectMode output
                (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                  (complexVectorCoordinateAtom i)
                  (complexVectorCoordinateAtom j))‖ₑ) ≤
            ∑ i : Fin 3, ∑ j : Fin 3,
              (‖advecting‖ₑ * ‖transported‖ₑ) *
                ‖lerayProjectMode output
                  (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                    (complexVectorCoordinateAtom i)
                    (complexVectorCoordinateAtom j))‖ₑ := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul' (mul_le_mul' (hadvecting i) (htransported j)) le_rfl
        _ = _ := by
          let service := ‖advecting‖ₑ * ‖transported‖ₑ
          change (∑ i : Fin 3, ∑ j : Fin 3,
            service * ‖lerayProjectMode output
              (complexAdvectiveInteraction parent (transportedFrequencyAt output parent)
                (complexVectorCoordinateAtom i)
                (complexVectorCoordinateAtom j))‖ₑ) = _
          simp_rw [mul_comm service]
          simp_rw [← Finset.sum_mul]
          dsimp [service]
          ac_rfl

/-- The operator cost paid by every aperture parent at one output address. -/
def finiteProjectedInteractionOutputCost
    (output : SpatialFrequency) (aperture : Finset SpatialFrequency) : ℝ≥0∞ :=
  ∑ parent ∈ aperture, finiteProjectedInteractionAtomCost output parent

theorem finiteProjectedInteractionOutputCost_ne_top
    (output : SpatialFrequency) (aperture : Finset SpatialFrequency) :
    finiteProjectedInteractionOutputCost output aperture ≠ ∞ := by
  unfold finiteProjectedInteractionOutputCost
  exact ENNReal.sum_ne_top.2 fun parent _hparent ↦
    finiteProjectedInteractionAtomCost_ne_top output parent

/-- The complete finite projected coefficient is bounded by the sum of its addressed atom costs
times the actual two parent amplitudes. -/
theorem enorm_finiteProjectedAdvectiveCoefficient_le_atomPayments
    (aperture : Finset SpatialFrequency)
    (advecting transported : ComplexFourierModePopulation)
    (output : SpatialFrequency) :
    ‖finiteProjectedAdvectiveCoefficient aperture advecting transported output‖ₑ ≤
      ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent * ‖advecting parent‖ₑ *
          ‖transported (transportedFrequencyAt output parent)‖ₑ := by
  unfold finiteProjectedAdvectiveCoefficient finiteAdvectiveCoefficient
  rw [lerayProjectMode_finset_sum]
  exact (enorm_sum_le _ _).trans
    (Finset.sum_le_sum fun parent _hparent ↦
      enorm_projectedInteraction_le_atomCost output parent
        (advecting parent) (transported (transportedFrequencyAt output parent)))

/-- State space on one fixed finite Galerkin carrier. -/
abbrev FiniteGalerkinState (carrier : Finset SpatialFrequency) :=
  FiniteFourierState carrier

/-- Zero extension of one finite state to the complete address population. -/
def finiteGalerkinZeroExtension
    {carrier : Finset SpatialFrequency} (state : FiniteGalerkinState carrier) :
    ComplexFourierModePopulation :=
  fun frequency ↦ if hfrequency : frequency ∈ carrier then
    state ⟨frequency, hfrequency⟩ else 0

theorem enorm_finiteGalerkinZeroExtension_le
    {carrier : Finset SpatialFrequency} (state : FiniteGalerkinState carrier)
    (frequency : SpatialFrequency) :
    ‖finiteGalerkinZeroExtension state frequency‖ₑ ≤ ‖state‖ₑ := by
  by_cases hfrequency : frequency ∈ carrier
  · rw [finiteGalerkinZeroExtension, dif_pos hfrequency]
    simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact nnnorm_le_pi_nnnorm state ⟨frequency, hfrequency⟩
  · rw [finiteGalerkinZeroExtension, dif_neg hfrequency, enorm_zero]
    exact bot_le

/-- The bilinear projected Galerkin interaction, restricted back to the fixed carrier. -/
def finiteGalerkinProjectedInteraction
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) : FiniteGalerkinState carrier :=
  fun output ↦
    finiteProjectedAdvectiveCoefficient aperture
      (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension right) output.1

/-- The autonomous finite-dimensional Navier--Stokes Galerkin vector field. -/
def finiteGalerkinNavierStokesVectorField
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (state : FiniteGalerkinState carrier) : FiniteGalerkinState carrier :=
  fun output ↦
    -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • state output -
      finiteGalerkinProjectedInteraction carrier aperture state state output

section InteractionLinearity

variable {carrier : Finset SpatialFrequency} (aperture : Finset SpatialFrequency)

theorem finiteGalerkinZeroExtension_add (u v : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension (u + v) =
      fun p ↦ finiteGalerkinZeroExtension u p + finiteGalerkinZeroExtension v p := by
  funext p
  by_cases hp : p ∈ carrier <;> simp [finiteGalerkinZeroExtension, hp]

theorem finiteGalerkinProjectedInteraction_add_left (u v w : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture (u + v) w =
    finiteGalerkinProjectedInteraction carrier aperture u w + finiteGalerkinProjectedInteraction carrier aperture v w := by
  have h (output : SpatialFrequency) := finiteAdvectiveCoefficient_add_add aperture
    (finiteGalerkinZeroExtension u) (finiteGalerkinZeroExtension v)
    (finiteGalerkinZeroExtension w) (fun _ ↦ 0) output
  have hadd (output : SpatialFrequency) :
      finiteAdvectiveCoefficient aperture
        (fun p ↦ finiteGalerkinZeroExtension u p + finiteGalerkinZeroExtension v p)
        (finiteGalerkinZeroExtension w) output =
      finiteAdvectiveCoefficient aperture (finiteGalerkinZeroExtension u) (finiteGalerkinZeroExtension w) output +
      finiteAdvectiveCoefficient aperture (finiteGalerkinZeroExtension v) (finiteGalerkinZeroExtension w) output := by
    simpa [finiteAdvectiveCoefficient, complexAdvectiveInteraction, complexDot] using h output
  funext output
  simp only [finiteGalerkinProjectedInteraction, finiteProjectedAdvectiveCoefficient,
    finiteGalerkinZeroExtension_add, Pi.add_apply]
  rw [hadd, lerayProjectMode_add]

theorem finiteGalerkinProjectedInteraction_add_right (u v w : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture u (v + w) =
    finiteGalerkinProjectedInteraction carrier aperture u v + finiteGalerkinProjectedInteraction carrier aperture u w := by
  have h (output : SpatialFrequency) := finiteAdvectiveCoefficient_add_add aperture
    (finiteGalerkinZeroExtension u) (fun _ ↦ 0)
    (finiteGalerkinZeroExtension v) (finiteGalerkinZeroExtension w) output
  have hadd (output : SpatialFrequency) :
      finiteAdvectiveCoefficient aperture (finiteGalerkinZeroExtension u)
        (fun p ↦ finiteGalerkinZeroExtension v p + finiteGalerkinZeroExtension w p) output =
      finiteAdvectiveCoefficient aperture (finiteGalerkinZeroExtension u) (finiteGalerkinZeroExtension v) output +
      finiteAdvectiveCoefficient aperture (finiteGalerkinZeroExtension u) (finiteGalerkinZeroExtension w) output := by
    simpa [finiteAdvectiveCoefficient, complexAdvectiveInteraction, complexDot] using h output
  funext output
  simp only [finiteGalerkinProjectedInteraction, finiteProjectedAdvectiveCoefficient,
    finiteGalerkinZeroExtension_add, Pi.add_apply]
  rw [hadd, lerayProjectMode_add]

@[simp] theorem finiteGalerkinProjectedInteraction_zero_left (u : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture 0 u = 0 := by
  funext output
  simp [finiteGalerkinProjectedInteraction, finiteProjectedAdvectiveCoefficient,
    finiteGalerkinZeroExtension, finiteAdvectiveCoefficient, complexAdvectiveInteraction,
    lerayProjectMode, complexDot]

@[simp] theorem finiteGalerkinProjectedInteraction_zero_right (u : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture u 0 = 0 := by
  funext output
  simp [finiteGalerkinProjectedInteraction, finiteProjectedAdvectiveCoefficient,
    finiteGalerkinZeroExtension, finiteAdvectiveCoefficient, complexAdvectiveInteraction,
    lerayProjectMode, complexDot]

theorem finiteGalerkinProjectedInteraction_neg_left (u v : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture (-u) v = -finiteGalerkinProjectedInteraction carrier aperture u v := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← finiteGalerkinProjectedInteraction_add_left, neg_add_cancel, finiteGalerkinProjectedInteraction_zero_left]

theorem finiteGalerkinProjectedInteraction_neg_right (u v : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture u (-v) = -finiteGalerkinProjectedInteraction carrier aperture u v := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← finiteGalerkinProjectedInteraction_add_right, neg_add_cancel, finiteGalerkinProjectedInteraction_zero_right]

theorem finiteGalerkinProjectedInteraction_sub_left (u v w : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture (u-v) w =
    finiteGalerkinProjectedInteraction carrier aperture u w - finiteGalerkinProjectedInteraction carrier aperture v w := by
  simp only [sub_eq_add_neg, finiteGalerkinProjectedInteraction_add_left, finiteGalerkinProjectedInteraction_neg_left]

theorem finiteGalerkinProjectedInteraction_sub_right (u v w : FiniteGalerkinState carrier) : finiteGalerkinProjectedInteraction carrier aperture u (v-w) =
    finiteGalerkinProjectedInteraction carrier aperture u v - finiteGalerkinProjectedInteraction carrier aperture u w := by
  simp only [sub_eq_add_neg, finiteGalerkinProjectedInteraction_add_right, finiteGalerkinProjectedInteraction_neg_right]

end InteractionLinearity

@[simp]
theorem finiteGalerkinZeroExtension_sub
    {carrier : Finset SpatialFrequency} (left right : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension (left - right) =
      fun frequency ↦ finiteGalerkinZeroExtension left frequency -
        finiteGalerkinZeroExtension right frequency := by
  funext frequency
  by_cases hfrequency : frequency ∈ carrier
  · simp [finiteGalerkinZeroExtension, hfrequency]
  · simp [finiteGalerkinZeroExtension, hfrequency]

theorem finiteGalerkinZeroExtension_eq_add_sub
    {carrier : Finset SpatialFrequency} (left right : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension left =
      fun frequency ↦ finiteGalerkinZeroExtension right frequency +
        finiteGalerkinZeroExtension (left - right) frequency := by
  rw [finiteGalerkinZeroExtension_sub]
  funext frequency
  module

/-- The quadratic difference is reconstructed from the two cross terms and the marked--marked
remainder.  Here the marked state is the actual iterate difference, not an assumed derivative. -/
theorem finiteGalerkinProjectedInteraction_self_sub_self
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right =
      finiteGalerkinProjectedInteraction carrier aperture (left - right) right +
        finiteGalerkinProjectedInteraction carrier aperture right (left - right) +
        finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right) := by
  funext output
  change
    finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension left) output.1 -
      finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension right) (finiteGalerkinZeroExtension right) output.1 = _
  rw [finiteGalerkinZeroExtension_eq_add_sub left right]
  exact finiteProjectedAdvectiveCoefficient_add_self_sub aperture
    (finiteGalerkinZeroExtension right) (finiteGalerkinZeroExtension (left - right)) output.1

/-- Sum of all actual finite interaction costs seen by the fixed output carrier. -/
def finiteGalerkinInteractionExtendedCost
    (carrier aperture : Finset SpatialFrequency) : ℝ≥0∞ :=
  ∑ output ∈ carrier, finiteProjectedInteractionOutputCost output aperture

theorem finiteGalerkinInteractionExtendedCost_ne_top
    (carrier aperture : Finset SpatialFrequency) :
    finiteGalerkinInteractionExtendedCost carrier aperture ≠ ∞ := by
  unfold finiteGalerkinInteractionExtendedCost
  exact ENNReal.sum_ne_top.2 fun output _houtput ↦
    finiteProjectedInteractionOutputCost_ne_top output aperture

/-- The same finite interaction cost in the nonnegative-real chart required by Picard--Lindelöf. -/
def finiteGalerkinInteractionCost
    (carrier aperture : Finset SpatialFrequency) : ℝ≥0 :=
  (finiteGalerkinInteractionExtendedCost carrier aperture).toNNReal

theorem finiteProjectedInteractionOutputCost_le_total
    (carrier aperture : Finset SpatialFrequency) {output : SpatialFrequency}
    (houtput : output ∈ carrier) :
    finiteProjectedInteractionOutputCost output aperture ≤
      finiteGalerkinInteractionExtendedCost carrier aperture := by
  unfold finiteGalerkinInteractionExtendedCost
  exact Finset.single_le_sum
    (fun address _haddress ↦ (zero_le : (0 : ℝ≥0∞) ≤
      finiteProjectedInteractionOutputCost address aperture)) houtput

theorem enorm_finiteProjectedCoefficient_zeroExtension_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) (output : SpatialFrequency) :
    ‖finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension right) output‖ₑ ≤
      finiteProjectedInteractionOutputCost output aperture * ‖left‖ₑ * ‖right‖ₑ := by
  calc
    _ ≤ ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent *
          ‖finiteGalerkinZeroExtension left parent‖ₑ *
          ‖finiteGalerkinZeroExtension right
            (transportedFrequencyAt output parent)‖ₑ :=
      enorm_finiteProjectedAdvectiveCoefficient_le_atomPayments _ _ _ _
    _ ≤ ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent * ‖left‖ₑ * ‖right‖ₑ := by
      apply Finset.sum_le_sum
      intro parent _hparent
      exact mul_le_mul'
        (mul_le_mul' le_rfl
          (enorm_finiteGalerkinZeroExtension_le left parent))
        (enorm_finiteGalerkinZeroExtension_le right
          (transportedFrequencyAt output parent))
    _ = _ := by
      unfold finiteProjectedInteractionOutputCost
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Exact finite quadratic service in the fixed-carrier sup norm. -/
theorem nnnorm_finiteGalerkinProjectedInteraction_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left right‖₊ ≤
      finiteGalerkinInteractionCost carrier aperture * ‖left‖₊ * ‖right‖₊ := by
  apply pi_nnnorm_le_iff.mpr
  intro output
  have hmode := enorm_finiteProjectedCoefficient_zeroExtension_le
    carrier aperture left right output.1
  have hcost := finiteProjectedInteractionOutputCost_le_total
    carrier aperture output.2
  have hmode' :
      ‖finiteGalerkinProjectedInteraction carrier aperture left right output‖ₑ ≤
        finiteGalerkinInteractionExtendedCost carrier aperture * ‖left‖ₑ * ‖right‖ₑ :=
    hmode.trans (mul_le_mul' (mul_le_mul' hcost le_rfl) le_rfl)
  rw [← ENNReal.coe_toNNReal
    (finiteGalerkinInteractionExtendedCost_ne_top carrier aperture)] at hmode'
  apply ENNReal.coe_le_coe.mp
  simpa only [finiteGalerkinInteractionCost, enorm_eq_nnnorm, ENNReal.coe_mul]
    using hmode'

theorem norm_finiteGalerkinProjectedInteraction_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left right‖ ≤
      finiteGalerkinInteractionCost carrier aperture * ‖left‖ * ‖right‖ := by
  exact_mod_cast nnnorm_finiteGalerkinProjectedInteraction_le carrier aperture left right

/-- The actual quadratic difference bound.  Its third term is the marked--marked remainder, so no
linearization or unspecified derivative constant is hidden. -/
theorem norm_finiteGalerkinProjectedInteraction_self_sub_self_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right‖ ≤
      finiteGalerkinInteractionCost carrier aperture *
        (2 * ‖right‖ + ‖left - right‖) * ‖left - right‖ := by
  rw [finiteGalerkinProjectedInteraction_self_sub_self]
  calc
    _ ≤ ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) right +
          finiteGalerkinProjectedInteraction carrier aperture right (left - right)‖ +
        ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right)‖ :=
      norm_add_le _ _
    _ ≤ (‖finiteGalerkinProjectedInteraction carrier aperture (left - right) right‖ +
          ‖finiteGalerkinProjectedInteraction carrier aperture right (left - right)‖) +
        ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (finiteGalerkinInteractionCost carrier aperture * ‖left - right‖ * ‖right‖ +
          finiteGalerkinInteractionCost carrier aperture * ‖right‖ * ‖left - right‖) +
        finiteGalerkinInteractionCost carrier aperture * ‖left - right‖ * ‖left - right‖ := by
      gcongr
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture (left - right) right
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture right (left - right)
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture
          (left - right) (left - right)
    _ = _ := by ring

/-- An exact subtraction law separating the linear Stokes response from the quadratic
interaction difference. -/
theorem finiteGalerkinNavierStokesVectorField_sub
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    finiteGalerkinNavierStokesVectorField nu carrier aperture left -
        finiteGalerkinNavierStokesVectorField nu carrier aperture right =
      (fun output : {frequency // frequency ∈ carrier} ↦
        -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • (left - right) output) -
      (finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right) := by
  funext output
  unfold finiteGalerkinNavierStokesVectorField
  simp only [Pi.sub_apply]
  module

end Holonics.Fluid.NavierStokesFiniteGalerkin
