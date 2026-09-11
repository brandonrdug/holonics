import ElementaryHolonics.Foundation.InformationReceiver

/-!
# Situated information rates

Information per holon is a receiver-relative quotient.  This file keeps the weighted occurrence
family, its total information, and its mass beside the quotient; it does not define a probability
or a governor.  A projective Swing is a separate four-point construction and is not this quotient.
-/

noncomputable section

namespace Soma.Holonics.Foundation.SituatedInformationRate

open scoped BigOperators

variable {Occurrence : Type*} [Fintype Occurrence]

def totalMass (weight : Occurrence → ℝ) : ℝ := ∑ occurrence, weight occurrence

def totalInformation (weight information : Occurrence → ℝ) : ℝ :=
  ∑ occurrence, weight occurrence * information occurrence

def informationRate (weight information : Occurrence → ℝ) : ℝ :=
  totalInformation weight information / totalMass weight

structure Reading (Occurrence : Type*) [Fintype Occurrence] where
  weight : Occurrence → ℝ
  information : Occurrence → ℝ
  nonnegative : ∀ occurrence, 0 ≤ weight occurrence
  positive_mass : 0 < totalMass weight

namespace Reading

variable (reading : Reading Occurrence)

def rate : ℝ := informationRate reading.weight reading.information

theorem rate_eq_quotient : reading.rate =
    totalInformation reading.weight reading.information / totalMass reading.weight := rfl

/- Reindexing carries both the measure and the receiver information. -/
theorem totalMass_equiv {Other : Type*} [Fintype Other]
    (e : Other ≃ Occurrence)
    (weight : Occurrence → ℝ) :
    totalMass (fun x : Other => weight (e x)) = totalMass weight := by
  exact Fintype.sum_equiv e (fun x => weight (e x)) weight (fun x => rfl)

theorem totalInformation_equiv {Other : Type*} [Fintype Other]
    (e : Other ≃ Occurrence)
    (weight information : Occurrence → ℝ) :
    totalInformation (fun x : Other => weight (e x)) (fun x => information (e x)) =
      totalInformation weight information := by
  exact Fintype.sum_equiv e (fun x => weight (e x) * information (e x))
    (fun x => weight x * information x) (fun x => rfl)

theorem rate_equiv {Other : Type*} [Fintype Other] (e : Other ≃ Occurrence) :
    informationRate (fun x : Other => reading.weight (e x))
      (fun x => reading.information (e x)) =
      reading.rate := by
  unfold informationRate Reading.rate
  rw [totalInformation_equiv e reading.weight reading.information,
    totalMass_equiv e reading.weight]
  rfl

/- Splitting every parent into a finite family of children preserves both mass and rate when the child weights
sum back to the parent's weight and the receiver information is inherited unchanged. -/
theorem split_rate {Child : Type*} [Fintype Child] (weight information : Occurrence → ℝ)
    (splitWeight : Occurrence → Child → ℝ)
    (mass_split : ∀ parent, ∑ child, splitWeight parent child = weight parent) :
    informationRate (fun child : Occurrence × Child => splitWeight child.1 child.2)
      (fun child => information child.1) = informationRate weight information := by
  have hm : totalMass (fun child : Occurrence × Child => splitWeight child.1 child.2) =
      totalMass weight := by
    simp only [totalMass, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun parent _ => mass_split parent)
  have hi : totalInformation
      (fun child : Occurrence × Child => splitWeight child.1 child.2)
      (fun child => information child.1) = totalInformation weight information := by
    simp only [totalInformation, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro parent hparent
    calc
      (∑ child, splitWeight parent child * information parent) =
          (∑ child, splitWeight parent child) * information parent := by
            rw [Finset.sum_mul]
      _ = weight parent * information parent := by
        rw [mass_split parent]
  rw [informationRate, informationRate, hi, hm]

/- Concrete duplication control: retain the same total-information numerator while doubling the
unweighted occurrence count.  The resulting information-per-count is exactly halved. -/
theorem duplicated_unweighted_rate_halves (information : Occurrence → ℝ) :
    informationRate (fun _ : Occurrence × Bool => 1)
        (fun x => information x.1 / 2) =
      informationRate (fun _ : Occurrence => 1) information / 2 := by
  simp [informationRate, totalInformation, totalMass, Fintype.sum_prod_type]
  ring

end Reading

def natsToBits (nats : ℝ) : ℝ := nats / Real.log 2

theorem natsToBits_crossEntropy_decomposition
    {Index : Type*} [Fintype Index]
    (reference emitted :
      Soma.Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection Index) :
    natsToBits (reference.crossEntropy emitted) =
      natsToBits reference.entropy + natsToBits (reference.klDivergence emitted) := by
  unfold natsToBits
  rw [Soma.Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection.crossEntropy_eq_entropy_add_kl]
  ring

end Soma.Holonics.Foundation.SituatedInformationRate
