import ElementaryHolonics.Computation.HolonicCausalTailLens
import ElementaryHolonics.Mathematics.CopsonDeBruijnInfiniteBoundary

/-!
# Silent aperture extension for the holonic causal-tail lens

One new optional site enlarges the addressed pair population. Old pairs retain both endpoint
addresses, current, energy, and depth. Every pair touching the new site is silent and belongs to
one new final depth. This is exactly HTP5 zero extension at the causal-tail receiver.

Activating the new self-pair is a separate control: positive returned energy changes the final
suffix face. Nominally adding a site without these zero laws is not silent extension.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicCausalTailLens.HNA1

open scoped BigOperators NNReal
open Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

universe uS uC

variable {Site : Type uS} {Current : Type uC} [Fintype Site] [Zero Current]

/-- Preserve every old addressed pair and make every pair touching the new site silent. -/
def silentExtendCurrents {N : ℕ}
    (currents : AddressedPairSection Site Current) :
    AddressedPairSection (Option Site) Current
  | some target, some source => currents target source
  | _, _ => 0

/-- Old pairs retain their depth; every genuinely new pair belongs to the new final depth. -/
def silentExtendLens {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1))) :
    CausalTailLens (Option Site) Current (Fin (N + 2)) where
  depth target source := match target, source with
    | some target, some source => (lens.depth target source).castSucc
    | _, _ => Fin.last (N + 1)
  energy := lens.energy
  energy_zero := lens.energy_zero

@[simp] theorem silentExtendCurrents_old {N : ℕ}
    (currents : AddressedPairSection Site Current) (target source : Site) :
    silentExtendCurrents (N := N) currents (some target) (some source) =
      currents target source := rfl

@[simp] theorem silentExtendCurrents_new {N : ℕ}
    (currents : AddressedPairSection Site Current) (target source : Option Site)
    (hnew : ¬ (∃ t s, target = some t ∧ source = some s)) :
    silentExtendCurrents (N := N) currents target source = 0 := by
  cases target <;> cases source <;> simp_all [silentExtendCurrents]

theorem project_silentExtend_castSucc {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (depth : Fin (N + 1)) :
    (silentExtendLens lens).project (silentExtendCurrents (N := N) currents) depth.castSucc =
      lens.project currents depth := by
  simp [CausalTailLens.project, silentExtendLens, silentExtendCurrents, lens.energy_zero]

@[simp] theorem project_silentExtend_last {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    (silentExtendLens lens).project (silentExtendCurrents (N := N) currents)
      (Fin.last (N + 1)) = 0 := by
  simp [CausalTailLens.project, silentExtendLens, silentExtendCurrents, lens.energy_zero]

/-- Neural silent extension is exactly HTP5 zero extension at the tail receiver. -/
theorem project_silentExtend {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    (silentExtendLens lens).project (silentExtendCurrents (N := N) currents) =
      zeroExtend (lens.project currents) := by
  funext depth
  refine Fin.lastCases ?_ (fun oldDepth ↦ ?_) depth
  · simp
  · simp [project_silentExtend_castSucc]

/-- Silent extension maps the old preimage forward; it is not an equivalence with the larger population. -/
def silentExtendPopulationPreimage {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (face : Fin (N + 1) → NNReal) :
    lens.populationHolon.PreimageFibre face →
      (silentExtendLens lens).populationHolon.PreimageFibre (zeroExtend face) :=
  fun carried ↦
    ⟨silentExtendCurrents (N := N) carried.1, by
      change (silentExtendLens lens).project
        (silentExtendCurrents (N := N) carried.1) = zeroExtend face
      have hsource : lens.project carried.1 = face := carried.property
      calc
        (silentExtendLens lens).project (silentExtendCurrents (N := N) carried.1) =
          zeroExtend (lens.project carried.1) := project_silentExtend lens carried.1
        _ = zeroExtend face := congrArg zeroExtend hsource⟩

/-- The old pair embedding preserves source, target, and received current exactly. -/
theorem silentExtend_addressedPair_source_target_receive {N : ℕ}
    (currents : AddressedPairSection Site Current) (target source : Site) :
    let small := CausalTailLens.addressedPairHolon currents
    let large := CausalTailLens.addressedPairHolon (silentExtendCurrents (N := N) currents)
    large.source (some target, some source) = some (small.source (target, source)) ∧
      large.target (some target, some source) = some (small.target (target, source)) ∧
      large.receive (some target, some source) = small.receive (target, source) := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Exact HTP5 receiver preservation -/

theorem tailEnergy_project_silentExtend_castSucc {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (depth : Fin (N + 1)) :
    tailEnergy ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents))
        depth.castSucc =
      tailEnergy (lens.project currents) depth := by
  rw [project_silentExtend, tailEnergy_zeroExtend_castSucc]

theorem tailRadius_project_silentExtend_castSucc {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (depth : Fin (N + 1)) :
    tailRadius ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents))
        depth.castSucc =
      tailRadius (lens.project currents) depth := by
  rw [project_silentExtend, tailRadius_zeroExtend_castSucc]

@[simp] theorem tailEnergy_project_silentExtend_last {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    tailEnergy ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents))
      (Fin.last (N + 1)) = 0 := by
  rw [project_silentExtend, tailEnergy_zeroExtend_last]

@[simp] theorem tailRadius_project_silentExtend_last {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    tailRadius ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents))
      (Fin.last (N + 1)) = 0 := by
  rw [project_silentExtend, tailRadius_zeroExtend_last]

theorem mass_project_silentExtend {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    mass ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents)) =
      mass (lens.project currents) := by
  rw [project_silentExtend, mass_zeroExtend]

theorem tailSurface_project_silentExtend {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) :
    tailSurface ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents)) =
      tailSurface (lens.project currents) := by
  rw [project_silentExtend, tailSurface_zeroExtend]

/-- Padding by one silent final depth cannot decrease the sharp receiver coefficient. -/
theorem finiteSharpCoefficient_padding_mono (N : ℕ) :
    finiteSharpCoefficient N ≤ finiteSharpCoefficient (N + 1) :=
  finiteSharpCoefficient_mono N

/-! ## Activated-new-pair control -/

/-- Turn on exactly the new `(none, none)` addressed pair. -/
def activateNewPair {N : ℕ}
    (currents : AddressedPairSection Site Current) (pulse : Current) :
    AddressedPairSection (Option Site) Current
  | none, none => pulse
  | some target, some source => currents target source
  | _, _ => 0

theorem project_activateNewPair_last {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (pulse : Current) :
    (silentExtendLens lens).project (activateNewPair (N := N) currents pulse)
      (Fin.last (N + 1)) = lens.energy pulse := by
  simp [CausalTailLens.project, silentExtendLens, activateNewPair, lens.energy_zero]

/-- The final suffix energy records exactly the square of the activated pair's energy. -/
theorem tailEnergy_project_activateNewPair_last {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (pulse : Current) :
    tailEnergy ((silentExtendLens lens).project (activateNewPair (N := N) currents pulse))
      (Fin.last (N + 1)) = lens.energy pulse ^ 2 := by
  unfold tailEnergy
  rw [show (Finset.Ici (Fin.last (N + 1)) : Finset (Fin (N + 2))) =
      {Fin.last (N + 1)} by
        ext depth
        simp only [Finset.mem_Ici, Finset.mem_singleton]
        constructor
        · intro h
          exact Fin.le_antisymm (Fin.le_last depth) h
        · rintro rfl
          exact le_rfl]
  simp [project_activateNewPair_last]

theorem project_activateNewPair_last_pos {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (pulse : Current)
    (hpositive : 0 < lens.energy pulse) :
    0 < (silentExtendLens lens).project (activateNewPair (N := N) currents pulse)
      (Fin.last (N + 1)) := by
  rw [project_activateNewPair_last]
  exact hpositive

/-- Positive energy at the new pair changes the final receiver coordinate from the silent face. -/
theorem project_activateNewPair_ne_silentExtend {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (pulse : Current)
    (hpositive : 0 < lens.energy pulse) :
    (silentExtendLens lens).project (activateNewPair (N := N) currents pulse) ≠
      (silentExtendLens lens).project (silentExtendCurrents (N := N) currents) := by
  intro heq
  have hlast := congrFun heq (Fin.last (N + 1))
  rw [project_activateNewPair_last, project_silentExtend_last] at hlast
  exact hpositive.ne' hlast

/-- Positive energy changes the final suffix-energy face from zero. -/
theorem tailEnergy_project_activateNewPair_last_ne_silent {N : ℕ}
    (lens : CausalTailLens Site Current (Fin (N + 1)))
    (currents : AddressedPairSection Site Current) (pulse : Current)
    (hpositive : 0 < lens.energy pulse) :
    tailEnergy ((silentExtendLens lens).project (activateNewPair (N := N) currents pulse))
        (Fin.last (N + 1)) ≠
      tailEnergy ((silentExtendLens lens).project (silentExtendCurrents (N := N) currents))
        (Fin.last (N + 1)) := by
  rw [tailEnergy_project_activateNewPair_last, tailEnergy_project_silentExtend_last]
  exact pow_ne_zero 2 hpositive.ne'

end Soma.Holonics.Computation.HolonicCausalTailLens.HNA1

section Audit
open Soma.Holonics.Computation.HolonicCausalTailLens
open Soma.Holonics.Computation.HolonicCausalTailLens.HNA1
#print axioms project_silentExtend
#print axioms silentExtendPopulationPreimage
#print axioms silentExtend_addressedPair_source_target_receive
#print axioms tailEnergy_project_silentExtend_castSucc
#print axioms tailRadius_project_silentExtend_castSucc
#print axioms mass_project_silentExtend
#print axioms tailSurface_project_silentExtend
#print axioms finiteSharpCoefficient_padding_mono
#print axioms project_activateNewPair_ne_silentExtend
#print axioms tailEnergy_project_activateNewPair_last_ne_silent
end Audit
