import ElementaryHolonics.Millennium.NavierStokesH2DyadicSeparationKernel

/-!
# Finite populations of strictly separated H2 triad swings

**[proved-derived; formal-checked]** The dyadic separation kernel controls one exchanged H2
triad at each low shell.  This owner retains an arbitrary finite population of actual closed
Fourier triads at every strictly lower shell, together with the actual modes carried by each
occurrence.  It first forms the signed complex current and only then applies the norm receiver.

The returned estimate preserves every occurrence through a nested ratio-weighted face-mass sum.
If each low shell's complete face mass has a common bound, the exact dyadic row sum removes any
loss proportional to the number of lower shells.  No statement here includes the comparable shell,
high--high--high interactions, an infinite triad population, or the complete nonlinear production
current.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2SeparatedTriadPopulationBound

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2DyadicSeparationKernel
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Occurrence population and retained complement -/

/-- The complete finite occurrence atlas for the admitted separated row.  The dependent pair
keeps the low-shell address beside the actual closed triad, so flattening the nested population
does not erase which scale occurrence supplied a current. -/
def separatedH2TriadOccurrences
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad) :
    Finset (Σ _lowLevel : ℕ, AddressedClosedFourierTriad) :=
  (Finset.range highLevel).sigma population

/-- Membership in the occurrence atlas returns both pieces of its reconstruction data: the
strictly separated low level and membership in that level's actual triad population. -/
theorem mem_separatedH2TriadOccurrences_iff
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (occurrence : Σ _lowLevel : ℕ, AddressedClosedFourierTriad) :
    occurrence ∈ separatedH2TriadOccurrences highLevel population ↔
      occurrence.1 < highLevel ∧ occurrence.2 ∈ population occurrence.1 := by
  simp [separatedH2TriadOccurrences]

/-- Flattening preserves the exact within-shell multiplicity: the occurrence atlas has the sum of
all admitted low-shell population cardinalities. -/
theorem card_separatedH2TriadOccurrences
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad) :
    (separatedH2TriadOccurrences highLevel population).card =
      ∑ lowLevel ∈ Finset.range highLevel, (population lowLevel).card := by
  simp [separatedH2TriadOccurrences, Finset.card_sigma]

/-- The actual signed exchanged-H2 current carried by all admitted low-shell occurrences below
one fixed high shell.  The two nested finite sums preserve shell address and within-shell
multiplicity until their complex currents join. -/
def separatedH2TriadPopulationCurrent
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector) : ℂ :=
  ∑ lowLevel ∈ Finset.range highLevel,
    ∑ triad ∈ population lowLevel,
      h2ExchangedTriadTransfer triad (advectingMode lowLevel triad)
        (transportedMode lowLevel triad) (receiverMode lowLevel triad)

/-- The signed nested current is exactly the current over the complete shell-addressed occurrence
atlas.  This equality is the finite convolution reconstruction receipt used by the norm bound. -/
theorem separatedH2TriadPopulationCurrent_eq_occurrenceSum
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector) :
    separatedH2TriadPopulationCurrent highLevel population
        advectingMode transportedMode receiverMode =
      ∑ occurrence ∈ separatedH2TriadOccurrences highLevel population,
        h2ExchangedTriadTransfer occurrence.2
          (advectingMode occurrence.1 occurrence.2)
          (transportedMode occurrence.1 occurrence.2)
          (receiverMode occurrence.1 occurrence.2) := by
  unfold separatedH2TriadPopulationCurrent separatedH2TriadOccurrences
  rw [Finset.sum_sigma']

/-- Complete norm mass of the still-oriented triadic faces at one low shell.  Distinct triads in
the finite population remain distinct summands. -/
def separatedH2TriadFaceMassAt
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector)
    (lowLevel : ℕ) : ℝ :=
  ∑ triad ∈ population lowLevel,
    ‖triadicEnergyFace triad.advecting triad.transported
      (advectingMode lowLevel triad) (transportedMode lowLevel triad)
      (receiverMode lowLevel triad)‖

/-- Actual ratio-weighted face mass of a strictly separated row.  The dyadic ratio is attached to
each shell before the row is condensed. -/
def separatedH2RatioWeightedFaceMass
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector) : ℝ :=
  ∑ lowLevel ∈ Finset.range highLevel,
    dyadicLowHighLengthRatio lowLevel highLevel *
      separatedH2TriadFaceMassAt population advectingMode transportedMode receiverMode lowLevel

/-- The reconstruction fibre deliberately excluded by the strict row: the comparable shell is
offset zero and every higher shell retains its original finite population at its exact offset. -/
def comparableAndHigherTriadPopulationFiber
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad) :
    ℕ → Finset AddressedClosedFourierTriad :=
  fun offset ↦ population (highLevel + offset)

/-- Offset zero of the retained complement is exactly the comparable high shell. -/
theorem comparableAndHigherTriadPopulationFiber_zero
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad) :
    comparableAndHigherTriadPopulationFiber highLevel population 0 = population highLevel := by
  simp [comparableAndHigherTriadPopulationFiber]

/-- Every population at or above the high shell is reconstructed exactly from the retained
complement fibre; no excluded interaction is silently assigned zero. -/
theorem comparableAndHigherTriadPopulationFiber_reconstruct
    (highLevel level : ℕ) (hhigh : highLevel ≤ level)
    (population : ℕ → Finset AddressedClosedFourierTriad) :
    comparableAndHigherTriadPopulationFiber highLevel population (level - highLevel) =
      population level := by
  unfold comparableAndHigherTriadPopulationFiber
  congr 1
  omega

/-! ## Actual finite-population bound -/

/-- The signed current of an arbitrary finite population of genuinely high--high--low triads is
bounded by the actual ratio-weighted sum of all its oriented face norms.  This is a population
composition of the exact exchanged transfer, not a detached scalar kernel proxy. -/
theorem norm_separatedH2TriadPopulationCurrent_le_ratioWeightedFaceMass
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector)
    (hdivergence : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        complexDot (complexFrequencyVector triad.advecting)
          (advectingMode lowLevel triad) = 0)
    (hadvecting : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖separatedH2TriadPopulationCurrent highLevel population
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
          separatedH2RatioWeightedFaceMass highLevel population
            advectingMode transportedMode receiverMode := by
  let commonScale : ℝ := primitiveTorusStokesScale *
    (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)
  calc
    ‖separatedH2TriadPopulationCurrent highLevel population
        advectingMode transportedMode receiverMode‖ ≤
      ∑ lowLevel ∈ Finset.range highLevel,
        ‖∑ triad ∈ population lowLevel,
          h2ExchangedTriadTransfer triad (advectingMode lowLevel triad)
            (transportedMode lowLevel triad) (receiverMode lowLevel triad)‖ := by
        unfold separatedH2TriadPopulationCurrent
        exact norm_sum_le _ _
    _ ≤ ∑ lowLevel ∈ Finset.range highLevel,
        ∑ triad ∈ population lowLevel,
          ‖h2ExchangedTriadTransfer triad (advectingMode lowLevel triad)
            (transportedMode lowLevel triad) (receiverMode lowLevel triad)‖ := by
      exact Finset.sum_le_sum fun lowLevel _hlowLevel ↦ norm_sum_le _ _
    _ ≤ ∑ lowLevel ∈ Finset.range highLevel,
        commonScale *
          (dyadicLowHighLengthRatio lowLevel highLevel *
            separatedH2TriadFaceMassAt population advectingMode transportedMode
              receiverMode lowLevel) := by
      apply Finset.sum_le_sum
      intro lowLevel hlowLevel
      have hlt : lowLevel < highLevel := Finset.mem_range.mp hlowLevel
      calc
        (∑ triad ∈ population lowLevel,
          ‖h2ExchangedTriadTransfer triad (advectingMode lowLevel triad)
            (transportedMode lowLevel triad) (receiverMode lowLevel triad)‖) ≤
          ∑ triad ∈ population lowLevel,
            commonScale *
              (dyadicLowHighLengthRatio lowLevel highLevel *
                ‖triadicEnergyFace triad.advecting triad.transported
                  (advectingMode lowLevel triad) (transportedMode lowLevel triad)
                  (receiverMode lowLevel triad)‖) := by
            apply Finset.sum_le_sum
            intro triad htriad
            calc
              ‖h2ExchangedTriadTransfer triad (advectingMode lowLevel triad)
                  (transportedMode lowLevel triad) (receiverMode lowLevel triad)‖ ≤
                (primitiveTorusStokesScale *
                  (6 * dyadicLowHighLengthRatio lowLevel highLevel *
                    (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
                    ‖triadicEnergyFace triad.advecting triad.transported
                      (advectingMode lowLevel triad) (transportedMode lowLevel triad)
                      (receiverMode lowLevel triad)‖ :=
                norm_h2ExchangedTriadTransfer_le_ratio_mul_high_sq triad lowLevel
                  highLevel (advectingMode lowLevel triad) (transportedMode lowLevel triad)
                  (receiverMode lowLevel triad) (hdivergence lowLevel hlt triad htriad)
                  (by omega) (hadvecting lowLevel hlt triad htriad)
                  (htransported lowLevel hlt triad htriad)
                  (hreceiver lowLevel hlt triad htriad)
              _ = commonScale *
                  (dyadicLowHighLengthRatio lowLevel highLevel *
                    ‖triadicEnergyFace triad.advecting triad.transported
                      (advectingMode lowLevel triad) (transportedMode lowLevel triad)
                      (receiverMode lowLevel triad)‖) := by
                dsimp only [commonScale]
                ring
        _ = commonScale *
            (dyadicLowHighLengthRatio lowLevel highLevel *
              separatedH2TriadFaceMassAt population advectingMode transportedMode
                receiverMode lowLevel) := by
          unfold separatedH2TriadFaceMassAt
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = commonScale *
        separatedH2RatioWeightedFaceMass highLevel population
          advectingMode transportedMode receiverMode := by
      unfold separatedH2RatioWeightedFaceMass
      rw [Finset.mul_sum]
    _ = (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) *
          separatedH2RatioWeightedFaceMass highLevel population
            advectingMode transportedMode receiverMode := rfl

/-! ## Uniform row consequence without multiplicity loss -/

/-- A common bound on each low shell's *total* face mass, rather than on each triad separately,
gives a high-level-uniform separated-row bound.  All within-shell multiplicity is paid inside the
shell mass; the exact dyadic row sum then contributes at most one. -/
theorem norm_separatedH2TriadPopulationCurrent_le_of_shellFaceMassBound
    (highLevel : ℕ)
    (population : ℕ → Finset AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode :
      ℕ → AddressedClosedFourierTriad → ComplexVector)
    (faceMassBound : ℝ)
    (hdivergence : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        complexDot (complexFrequencyVector triad.advecting)
          (advectingMode lowLevel triad) = 0)
    (hadvecting : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : ∀ lowLevel < highLevel,
      ∀ triad ∈ population lowLevel,
        triad.receiver ∈ dyadicFrequencyShell highLevel)
    (hfaceMassBound : ∀ lowLevel < highLevel,
      separatedH2TriadFaceMassAt population advectingMode transportedMode receiverMode
        lowLevel ≤ faceMassBound)
    (hboundNonneg : 0 ≤ faceMassBound) :
    ‖separatedH2TriadPopulationCurrent highLevel population
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) * faceMassBound := by
  let commonScale : ℝ := primitiveTorusStokesScale *
    (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)
  let shellFaceMass : ℕ → ℝ := fun lowLevel ↦
    separatedH2TriadFaceMassAt population advectingMode transportedMode receiverMode lowLevel
  have hshellNonneg : ∀ lowLevel < highLevel, 0 ≤ shellFaceMass lowLevel := by
    intro lowLevel _hlt
    dsimp only [shellFaceMass, separatedH2TriadFaceMassAt]
    exact Finset.sum_nonneg fun _triad _htriad ↦ norm_nonneg _
  have hrow := sum_dyadicLowHighLengthRatio_mul_le highLevel shellFaceMass faceMassBound
    hshellNonneg (fun lowLevel hlt ↦ hfaceMassBound lowLevel hlt) hboundNonneg
  have hcommonNonneg : 0 ≤ commonScale := by
    dsimp only [commonScale]
    exact mul_nonneg primitiveTorusStokesScale_pos.le
      (mul_nonneg (by norm_num) (sq_nonneg _))
  calc
    ‖separatedH2TriadPopulationCurrent highLevel population
        advectingMode transportedMode receiverMode‖ ≤
      commonScale * separatedH2RatioWeightedFaceMass highLevel population
        advectingMode transportedMode receiverMode := by
          dsimp only [commonScale]
          exact norm_separatedH2TriadPopulationCurrent_le_ratioWeightedFaceMass
            highLevel population advectingMode transportedMode receiverMode hdivergence
            hadvecting htransported hreceiver
    _ ≤ commonScale * faceMassBound := by
      apply mul_le_mul_of_nonneg_left _ hcommonNonneg
      unfold separatedH2RatioWeightedFaceMass
      dsimp only [shellFaceMass] at hrow
      exact hrow.2
    _ = (primitiveTorusStokesScale *
        (6 * (dyadicRadius (highLevel + 1) : ℝ) ^ 2)) * faceMassBound := rfl

section Audit

#print axioms mem_separatedH2TriadOccurrences_iff
#print axioms card_separatedH2TriadOccurrences
#print axioms separatedH2TriadPopulationCurrent_eq_occurrenceSum
#print axioms comparableAndHigherTriadPopulationFiber_zero
#print axioms comparableAndHigherTriadPopulationFiber_reconstruct
#print axioms norm_separatedH2TriadPopulationCurrent_le_ratioWeightedFaceMass
#print axioms norm_separatedH2TriadPopulationCurrent_le_of_shellFaceMassBound

end Audit

end Soma.Holonics.Millennium.NavierStokesH2SeparatedTriadPopulationBound
