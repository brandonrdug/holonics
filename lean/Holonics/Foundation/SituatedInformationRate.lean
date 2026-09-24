import Holonics.Foundation.InformationReceiver

/-!
# Situated information rates

Information per holon is a receiver-relative quotient.  This file keeps the weighted occurrence
family, its total information, and its mass beside the quotient; it does not define a probability
or a governor. A projective Swing is a separate four-point construction and is not this quotient.

Elapsed-time throughput is a different quotient, with the quantity and local clock supplied by
the caller. A delivered receiver face, a completed owner update, a bit and an arithmetic operation
are different quantities. The laws below compose measurements without identifying those units,
assuming an information distribution, or treating a resource-dependent ceiling as a universal
physical propagation speed. Signed clock reversal is algebra, not reversibility of a source law.
-/

noncomputable section

namespace Holonics.Foundation.SituatedInformationRate

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

/- The caller retains the event/receiver address, clock and units. Physical throughput uses a
positive elapsed interval; the bare quotient also supports oriented clock coordinates. -/
def throughput (quantity elapsed : ℝ) : ℝ := quantity / elapsed

theorem throughput_clock_rebase (quantity elapsed scale : ℝ) :
    throughput quantity (scale * elapsed) = throughput quantity elapsed / scale := by
  simp only [throughput, div_div]
  rw [mul_comm]

theorem throughput_affine_clock (quantity start finish scale origin : ℝ) :
    throughput quantity ((origin + scale * finish) - (origin + scale * start)) =
      throughput quantity (finish - start) / scale := by
  have h : (origin + scale * finish) - (origin + scale * start) =
      scale * (finish - start) := by ring
  rw [h, throughput_clock_rebase]

theorem throughput_oriented_clock_reversal (quantity elapsed : ℝ) :
    throughput quantity (-elapsed) = -throughput quantity elapsed := by
  unfold throughput
  ring

/- Aggregate disjoint serial observation windows using their elapsed durations. This is a
duration-weighted mean, not an unweighted mean of instantaneous rates. -/
theorem throughput_serial (quantity₁ quantity₂ elapsed₁ elapsed₂ : ℝ)
    (h₁ : elapsed₁ ≠ 0) (h₂ : elapsed₂ ≠ 0) :
    throughput (quantity₁ + quantity₂) (elapsed₁ + elapsed₂) =
      (elapsed₁ * throughput quantity₁ elapsed₁ +
        elapsed₂ * throughput quantity₂ elapsed₂) / (elapsed₁ + elapsed₂) := by
  simp only [throughput]
  congr 1
  field_simp

/- Total information per time factors through measured occurrence mass only when that mass
and the information mean refer to the same occurrence population. -/
theorem Reading.information_throughput (reading : Reading Occurrence) (elapsed : ℝ) :
    throughput (totalInformation reading.weight reading.information) elapsed =
      throughput (totalMass reading.weight) elapsed * reading.rate := by
  simp only [throughput, Reading.rate, informationRate]
  have hm := ne_of_gt reading.positive_mass
  field_simp

/- A capacity bound is conditional on a lower work cost for every counted event and an upper
available work budget over this very interval, in the same resource units. -/
theorem throughput_resource_ceiling (count elapsed work perEvent capacity : ℝ)
    (ht : 0 < elapsed) (hw : 0 < perEvent)
    (required : count * perEvent ≤ work)
    (available : work ≤ capacity * elapsed) :
    throughput count elapsed ≤ capacity / perEvent := by
  apply (div_le_div_iff₀ ht hw).2
  exact le_trans required available

def natsToBits (nats : ℝ) : ℝ := nats / Real.log 2

theorem natsToBits_crossEntropy_decomposition
    {Index : Type*} [Fintype Index]
    (reference emitted :
      Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection Index) :
    natsToBits (reference.crossEntropy emitted) =
      natsToBits reference.entropy + natsToBits (reference.klDivergence emitted) := by
  unfold natsToBits
  rw [Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection.crossEntropy_eq_entropy_add_kl]
  ring

/- Expected excess code rate, for the declared positive finite distributions and event rate.
This is not a claim that event frequency by itself determines cross-entropy. -/
theorem crossEntropy_throughput_decomposition
    {Index : Type*} [Fintype Index]
    (reference emitted :
      Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection Index)
    (eventRate : ℝ) :
    eventRate * natsToBits (reference.crossEntropy emitted) =
      eventRate * natsToBits reference.entropy +
      eventRate * natsToBits (reference.klDivergence emitted) := by
  rw [natsToBits_crossEntropy_decomposition, mul_add]

end Holonics.Foundation.SituatedInformationRate
