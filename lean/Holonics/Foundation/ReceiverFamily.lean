import Mathlib.Data.Set.Defs

/-!
# Receiver families and their collapse

The receiver-family carrier and its induced agreement relation are elementary: they require no
algebraic, analytic, or research hypotheses.  Their declarations live
under `Holonics.Foundation.Separation`.
-/

universe uX uY

namespace Holonics.Foundation.Separation

variable {X : Type uX} {Y : Type uY}

/-- A receiver family is a set of readings of `X`. -/
abbrev ReceiverFamily (X : Type uX) (Y : Type uY) := Set (X → Y)

/-- The collapse a receiver family induces: pairs it cannot distinguish. -/
def collapseOf (F : ReceiverFamily X Y) (a b : X) : Prop := ∀ f ∈ F, f a = f b

end Holonics.Foundation.Separation
