import Mathlib.Order.Defs.PartialOrder

/-! Refs #62. The existing Tower carrier, moved unchanged to its narrow owner. -/
namespace Holonics.Foundation.ContinuingTower
universe u v w

/-- [definition] A **tower**: a family of faces over a refinement preorder together with the
restriction that carries a finer face to the coarser one it presents.

`Index` is the index of apertures, grains, charts, precisions and environments; `Face i` is what is
actually presented at index `i`; `restrict` is the only transport, and it is directed from finer to
coarser. `restrict_refl` and `restrict_trans` are the two laws — no face is the object, and the
object is exactly this family plus these laws.

Rust counterpart: `crates/holonics/src/holon/restriction/tower.rs::Tower`. -/
structure Tower (Index : Type u) [Preorder Index] where
  /-- The face actually presented at one index. -/
  Face : Index → Type v
  /-- Carry a finer face to the coarser index it refines. -/
  restrict : ∀ {i j : Index}, i ≤ j → Face j → Face i
  /-- Restricting to the same index changes nothing. -/
  restrict_refl : ∀ (i : Index) (x : Face i), restrict (le_refl i) x = x
  /-- Restricting twice is restricting once along the composite refinement. -/
  restrict_trans : ∀ {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) (x : Face k),
    restrict hij (restrict hjk x) = restrict (le_trans hij hjk) x

end Holonics.Foundation.ContinuingTower
