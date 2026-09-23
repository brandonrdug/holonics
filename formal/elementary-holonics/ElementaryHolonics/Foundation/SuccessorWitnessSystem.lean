import Mathlib.Data.Nat.Basic
import Mathlib.Logic.IsEmpty.Basic

/-!
# Coherent sections from surjective successor restrictions

Generic local-to-global passage for a sequence of witness fibres.  The declarations retain
their historical namespace until the Lean path and namespace migration (M2).
-/

universe u

namespace Soma.Holonics.Millennium.HolonicDirectedPassage

/-- [definition] A sequential local-witness system retains the witness type at every depth and
the exact fine-to-coarse restriction. `restrict_surjective` is the constitutive extension law:
every admitted occurrence at one depth has an admitted successor at the next depth. -/
structure SuccessorWitnessSystem where
  Fibre : ℕ → Type u
  restrict : ∀ depth, Fibre (depth + 1) → Fibre depth
  baseNonempty : Nonempty (Fibre 0)
  restrict_surjective : ∀ depth, Function.Surjective (restrict depth)

/-- [definition] A coherent section is a complete oriented history, not a population of unrelated
local witnesses: every successor restricts to the witness that actually preceded it. -/
structure SuccessorWitnessSystem.CoherentSection
    (system : SuccessorWitnessSystem) where
  witness : ∀ depth, system.Fibre depth
  compatible : ∀ depth,
    system.restrict depth (witness (depth + 1)) = witness depth

namespace SuccessorWitnessSystem

/-- [proved-derived; formal-checked] Recursively choose one successor of the already chosen local
occurrence. The construction therefore retains one lineage through every scale rather than
choosing each inhabited fibre independently. -/
noncomputable def coherentWitness (system : SuccessorWitnessSystem) :
    (depth : ℕ) → system.Fibre depth
  | 0 => Classical.choice system.baseNonempty
  | depth + 1 => Classical.choose
      (system.restrict_surjective depth (coherentWitness system depth))

/-- [proved-derived; formal-checked] Every recursive successor returns exactly to its chosen
predecessor. -/
theorem coherentWitness_compatible (system : SuccessorWitnessSystem) (depth : ℕ) :
    system.restrict depth (system.coherentWitness (depth + 1)) =
      system.coherentWitness depth := by
  exact Classical.choose_spec
    (system.restrict_surjective depth (system.coherentWitness depth))

/-- [proved-derived; formal-checked] A base occurrence plus surjective successor restriction
constructs a complete coherent history through all natural-number depths. -/
noncomputable def coherentSection (system : SuccessorWitnessSystem) :
    system.CoherentSection where
  witness := system.coherentWitness
  compatible := system.coherentWitness_compatible

/-- [proved-derived; formal-checked] The exact sequential local-to-global passage. This theorem is
restricted to the acyclic successor course; cyclic or multiply-related index geometries owe their
own holonomy/equalization law. -/
theorem nonempty_coherentSection (system : SuccessorWitnessSystem) :
    Nonempty system.CoherentSection :=
  ⟨system.coherentSection⟩

end SuccessorWitnessSystem

/-- [definition] The smallest nontrivial orientation reversal on a two-state fibre. -/
def boolFlip (value : Bool) : Bool := !value

/-- [proved-derived; formal-checked] Local orientation reversal is itself a bijective transport. -/
theorem boolFlip_surjective : Function.Surjective boolFlip := by
  intro value
  exact ⟨!value, by cases value <;> rfl⟩

/-- [definition] A section around the one-step reversal loop would have to be fixed by its loop
return. -/
structure BoolFlipCoherent where
  witness : Bool
  compatible : boolFlip witness = witness

/-- [counterexample; formal-checked] Bijective local transport and inhabited local fibres do not
produce a global section around a loop: nonzero holonomy has no fixed occurrence here. Thus the
acyclic theorem above cannot be promoted to arbitrary index geometry without an exact loop-return
condition. -/
theorem boolFlipCoherent_isEmpty : IsEmpty BoolFlipCoherent := by
  constructor
  rintro ⟨witness, compatible⟩
  cases witness <;> simp [boolFlip] at compatible

section Audit

#print axioms SuccessorWitnessSystem.nonempty_coherentSection
#print axioms boolFlipCoherent_isEmpty

end Audit

end Soma.Holonics.Millennium.HolonicDirectedPassage
