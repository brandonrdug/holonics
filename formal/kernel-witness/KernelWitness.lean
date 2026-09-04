/-!
# The kernel-in-the-loop witness

This library carries no dependency beyond Lean core. That is its entire point: it is the one
formal project in this repository that an exterior Lean kernel can check **offline**, so a driver
can submit proof terms to `lake env lean` and receive a real verdict without materializing the
Mathlib package cache that `elementary-holonics` and `rh-source-transport` require.

The declarations here are the carrier the driver's problems talk about. They are deliberately
small; the evidence this project exists to produce is the *verdict*, not the mathematics.
-/

namespace Soma

/-- The exact carrier: a receiver that transports a proposition and returns it unchanged. -/
def exactCarrier (P : Prop) : Prop := P

/-- Transport through the exact carrier is definitionally the identity chart. -/
theorem exact_chart_carry (P : Prop) : exactCarrier P = P := rfl

/-- A hypothesis crosses the carrier without a chart change. -/
theorem formal_carry {P : Prop} (h : P) : exactCarrier P := h

end Soma
