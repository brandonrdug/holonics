import ElementaryHolonics.Millennium.Swing

/-!
# Ellipse: the Einstein constant is an inverse force, and the orbit is a swing

**No cosmology here** — the symbols and the geometric intentions only.

`κ = 8πG/c⁴` has dimension `N⁻¹`.  So `G_μν = κ T_μν` reads *curvature equals source
divided by a fixed force*, per area, and what crosses the equality is a **dimensionless
ratio of forces** rather than a magnitude.  The `8π` factors as `2·(4π)`: the sphere's
full solid angle, doubled by the inverse of the trace-reversal's `½` — the same half
this corpus carries as the half-density a double cover resolves.

And the ellipse Newton read the inverse square off is a **swing orbit**.  The focal sum
law `r₁ + r₂ = 2a` is exactly `r₂ = swing a r₁`, the half-turn about the semi-major axis
with the board frozen at infinity — the same shape as `r + r' = n` for a modulus, with
`a` where the anchor sits.  The circle is the swing's fixed point, the residue is the
focal difference, and the eccentricity is the residue over the modulus: a ratio, which
is what crosses.

```text
  modulus    r + r'  = n      anchor n/2    fixed class n/2, no hand
  ellipse    r₁ + r₂ = 2a     anchor a      fixed point: the circle, r₁ = r₂ = a
```

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.Ellipse

/-- A physical dimension as exponents of (length, mass, time). -/
abbrev Dim := ℤ × ℤ × ℤ

def dimG : Dim := (3, -1, -2)          -- m³ kg⁻¹ s⁻²
def dimC : Dim := (1, 0, -1)           -- m s⁻¹
def dimForce : Dim := (1, 1, -2)       -- kg m s⁻²

def dsub (a b : Dim) : Dim := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def dsmul (k : ℤ) (a : Dim) : Dim := (k * a.1, k * a.2.1, k * a.2.2)
def dneg (a : Dim) : Dim := (-a.1, -a.2.1, -a.2.2)

/-- **THE EINSTEIN CONSTANT IS AN INVERSE FORCE.**  `[G/c⁴] = [N]⁻¹` exactly, so the
field equation reads *curvature = source divided by a fixed force*, per area.  What
crosses the equality is a dimensionless **ratio of forces**, not a magnitude. -/
theorem theEinsteinConstantIsAnInverseForce :
    dsub dimG (dsmul 4 dimC) = dneg dimForce := by decide

/-- **THE `8π` FACTORS AS HALF-DENSITY TIMES SOLID ANGLE.**  `8π = 2·(4π)`: the sphere's
full solid angle, doubled by the inverse of the trace-reversal's `½` — the same half
this corpus carries as the half-density a double cover resolves. -/
theorem theEightPiFactors : (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) := by ring

/-! ## The ellipse as a swing orbit -/

/-- **THE FOCAL SUM LAW IS THE SWING.**  `r₁ + r₂ = 2a` is exactly `r₂ = swing a r₁`:
the half-turn about the semi-major axis, with the board frozen at infinity.  The same
shape as `r + r' = n` for a modulus, with `a` in the anchor's place. -/
theorem theFocalSumLawIsTheSwing (a r₁ r₂ : ℝ) :
    r₁ + r₂ = 2 * a ↔ r₂ = Swing.swing a r₁ := by
  unfold Swing.swing
  constructor <;> intro h <;> linarith

/-- **THE CIRCLE IS THE FIXED POINT OF THE ORBIT.**  A focal radius equal to its own
swing is the degenerate orbit — the anchor itself, where the two foci coincide and the
residue vanishes.  Exactly the handless class of a modulus. -/
theorem theCircleIsTheFixedPointOfTheOrbit (a r : ℝ) :
    Swing.swing a r = r ↔ r = a := by
  unfold Swing.swing
  constructor <;> intro h <;> linarith

/-- **THE ECCENTRICITY IS THE RESIDUE OVER THE MODULUS.**  With apsides `a(1±e)` the
sum is the invariant `2a` and the difference is the varying part; their ratio is `e`.
The conserved quantity is the sum, the observable is the difference, and what crosses
between frames is the ratio. -/
theorem theEccentricityIsTheResidueOverTheModulus (a e : ℝ) (ha : a ≠ 0) :
    (a * (1 + e) - a * (1 - e)) / (a * (1 + e) + a * (1 - e)) = e := by
  field_simp
  ring

end Soma.Holonics.Millennium.Ellipse
