import ElementaryHolonics.Computation.IntrinsicHolonProfile
import Mathlib.Tactic

/-!
# Exact foreign-weight passages

A finite foreign codeword is not identified with a unique departed richer value.  The passage
retains its exact stored value, residual, and complete encoding preimage.  Modular and quantized
charts are consequently exact only relative to the receiver family that factors through them.
-/

namespace Soma.Holonics.Computation.HolonicIntelligence

universe uSource uCode uNative

/-- An exact codeword crossing into one additive native carrier. -/
structure ExactForeignWeightPassage
    (Source : Type uSource) (Code : Type uCode) (Native : Type uNative)
    [AddCommGroup Native] where
  encode : Source → Code
  sourceValue : Source → Native
  storedValue : Code → Native
  residual : Source → Native
  reconstructs : ∀ source,
    sourceValue source = storedValue (encode source) + residual source

namespace ExactForeignWeightPassage

variable
    {Source : Type uSource} {Code : Type uCode} {Native : Type uNative}
    [AddCommGroup Native]
    (passage : ExactForeignWeightPassage Source Code Native)

/-- Every richer source occurrence retained behind one stored codeword. -/
def preimageFibre (code : Code) : Set Source :=
  {source | passage.encode source = code}

/-- The source occurrence is always retained in the fibre of its own codeword. -/
theorem source_mem_preimageFibre (source : Source) :
    source ∈ passage.preimageFibre (passage.encode source) := by
  rfl

/-- Two collapsed source occurrences remain together in the complete preimage fibre. -/
theorem collapsed_pair_retained {left right : Source}
    (collapsed : passage.encode left = passage.encode right) :
    left ∈ passage.preimageFibre (passage.encode left) ∧
      right ∈ passage.preimageFibre (passage.encode left) := by
  exact ⟨rfl, collapsed.symm⟩

/-- The stored value plus retained residual reconstructs the exact admitted source value. -/
theorem exact_reconstruction (source : Source) :
    passage.storedValue (passage.encode source) + passage.residual source =
      passage.sourceValue source := by
  exact (passage.reconstructs source).symm

end ExactForeignWeightPassage

namespace Control

/-- Integer reduction modulo a radix as an exact stored-value-plus-residual passage. -/
def integralModulo (modulus : ℤ) : ExactForeignWeightPassage ℤ ℤ ℤ where
  encode source := source % modulus
  sourceValue := _root_.id
  storedValue := _root_.id
  residual source := source - source % modulus
  reconstructs source := by
    change source = source % modulus + (source - source % modulus)
    ring

/-- Zero and two collapse under the binary stored face while remaining plural in its preimage. -/
theorem binaryModulo_retains_plural_preimage :
    (0 : ℤ) ∈ (integralModulo 2).preimageFibre 0 ∧
      (2 : ℤ) ∈ (integralModulo 2).preimageFibre 0 := by
  norm_num [ExactForeignWeightPassage.preimageFibre, integralModulo]

/-- The richer value two is recovered exactly as stored zero plus residual two. -/
theorem binaryModulo_two_reconstructs :
    (integralModulo 2).storedValue ((integralModulo 2).encode 2) +
        (integralModulo 2).residual 2 =
      (integralModulo 2).sourceValue 2 := by
  norm_num [integralModulo]

end Control

section Audit

#print axioms ExactForeignWeightPassage.source_mem_preimageFibre
#print axioms ExactForeignWeightPassage.collapsed_pair_retained
#print axioms ExactForeignWeightPassage.exact_reconstruction
#print axioms Control.binaryModulo_retains_plural_preimage
#print axioms Control.binaryModulo_two_reconstructs

end Audit

end Soma.Holonics.Computation.HolonicIntelligence
