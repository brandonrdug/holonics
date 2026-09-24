import ElementaryHolonics.Millennium.FamilyTunnellHeckeIntertwining

/-!
# The Tunnell lattice Hecke correspondence carrier

The remaining source law is not left as a sentence saying that a theta form is an
eigenform.  This file expands it into one finite signed occurrence population at
every `(p,n)`.

The four source species are retained separately:

* the thick ternary population with weight `+2`;
* the thin population with weight `-1`;
* the level-four thick correction with weight `-2`;
* the level-four thin correction with weight `+1`.

Their total is the complete integral Tunnell coefficient.  The `T(p²)` source
layers, the quadratic middle layer, the exact quotient layer, and the product with
the weighted Gaussian norm-`p` shell are then joined into one signed carrier.  Its
total is proved to be the integral Hecke defect.  A fixed-point-free involutive swing
which reverses the weight therefore proves the source eigenlaw.  This is the exact
geometric construction target for the lattice correspondence: no theorem-name or
external-library placeholder remains in the interface.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHeckeCorrespondence

open NumberTheorySymbols
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier
open Soma.Holonics.Millennium.FamilyTunnellShimuraLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeIntertwining
open Soma.Holonics.Millennium.HeckeTheta

/-! ## 1. One complete signed Tunnell layer -/

/-- The four tagged ternary species. -/
abbrev TunnellLayerOccurrence :=
  (TernaryOccurrence ⊕ TernaryOccurrence) ⊕
    (TernaryOccurrence ⊕ TernaryOccurrence)

noncomputable local instance : DecidableEq TunnellLayerOccurrence := Classical.decEq _

/-- The complete source population at one coefficient index. -/
def tunnellLayerPopulation (n : ℕ) : Finset TunnellLayerOccurrence :=
  (canonicalThickPopulation n).disjSum (canonicalThinPopulation n) |>.disjSum
    ((levelThickPopulation n).disjSum (levelThinPopulation n))

/-- The orientation/multiplicity of each tagged source species. -/
def tunnellLayerWeight : TunnellLayerOccurrence → ℤ
  | .inl (.inl _) => 2
  | .inl (.inr _) => -1
  | .inr (.inl _) => -2
  | .inr (.inr _) => 1

private theorem sum_disjSum
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α ⊕ β → ℤ) :
    (∑ x ∈ s.disjSum t, f x) =
      (∑ a ∈ s, f (.inl a)) + ∑ b ∈ t, f (.inr b) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [ha]

/-- The signed total of one retained layer is exactly the complete integral Tunnell
coefficient, including the level-four correction. -/
theorem tunnellLayerTotalWeight (n : ℕ) :
    (∑ x ∈ tunnellLayerPopulation n, tunnellLayerWeight x) =
      fullTunnellThetaCoefficient n := by
  unfold tunnellLayerPopulation
  rw [sum_disjSum, sum_disjSum, sum_disjSum]
  simp only [tunnellLayerWeight, Finset.sum_const, nsmul_eq_mul]
  unfold fullTunnellThetaCoefficient tunnellThetaCoefficient
    thickThetaCoefficient thinThetaCoefficient levelThickCoefficient levelThinCoefficient
  push_cast
  ring

/-- Multiplying every occurrence weight commutes with returning the complete layer. -/
theorem weightedTunnellLayerTotal (c : ℤ) (n : ℕ) :
    (∑ x ∈ tunnellLayerPopulation n, c * tunnellLayerWeight x) =
      c * fullTunnellThetaCoefficient n := by
  rw [← Finset.mul_sum, tunnellLayerTotalWeight]

/-! ## 2. The complete signed Hecke plate -/

/-- Upper source layer, middle character layer, exact quotient layer, and Gaussian
target product, kept as distinct occurrence species. -/
abbrev TunnellHeckeOccurrence :=
  ((TunnellLayerOccurrence ⊕ TunnellLayerOccurrence) ⊕ TunnellLayerOccurrence) ⊕
    ((ℤ × ℤ) × TunnellLayerOccurrence)

noncomputable local instance : DecidableEq TunnellHeckeOccurrence := Classical.decEq _

/-- The quotient layer exists only when its predecessor really maps to `n`. -/
def quotientTunnellLayerPopulation (p n : ℕ) : Finset TunnellLayerOccurrence :=
  if p ^ 2 ∣ n then tunnellLayerPopulation (n / p ^ 2) else ∅

/-- The complete finite occurrence population of the source-specific `T(p²)`
correspondence. -/
def tunnellHeckePopulation (p n : ℕ) : Finset TunnellHeckeOccurrence :=
  ((tunnellLayerPopulation (p ^ 2 * n)).disjSum (tunnellLayerPopulation n) |>.disjSum
      (quotientTunnellLayerPopulation p n)) |>.disjSum
    ((heckeShell p) ×ˢ (tunnellLayerPopulation n))

/-- The signed action carried by each occurrence in the Hecke plate. -/
def tunnellHeckeWeight (p n : ℕ) : TunnellHeckeOccurrence → ℤ
  | .inl (.inl (.inl x)) => tunnellLayerWeight x
  | .inl (.inl (.inr x)) => jacobiSym (-(n : ℤ)) p * tunnellLayerWeight x
  | .inl (.inr x) => (p : ℤ) * tunnellLayerWeight x
  | .inr (q, x) => -q.1 * tunnellLayerWeight x

/-- The integral source eigen-defect.  It is twice the rational normalized defect
and has no denominator. -/
def integralTunnellHeckeDefect (p n : ℕ) : ℤ :=
  fullTunnellThetaCoefficient (p ^ 2 * n) +
    jacobiSym (-(n : ℤ)) p * fullTunnellThetaCoefficient n +
    (p : ℤ) *
      (if p ^ 2 ∣ n then fullTunnellThetaCoefficient (n / p ^ 2) else 0) -
    heckeCoeff p * fullTunnellThetaCoefficient n

/-- The complete signed occurrence population returns exactly the integral Hecke
defect. -/
theorem tunnellHeckePopulation_totalWeight (p n : ℕ) :
    (∑ x ∈ tunnellHeckePopulation p n, tunnellHeckeWeight p n x) =
      integralTunnellHeckeDefect p n := by
  classical
  unfold tunnellHeckePopulation
  rw [sum_disjSum, sum_disjSum, sum_disjSum]
  simp only [tunnellHeckeWeight]
  rw [tunnellLayerTotalWeight,
    weightedTunnellLayerTotal (jacobiSym (-(n : ℤ)) p) n]
  have htarget :
      (∑ q ∈ heckeShell p ×ˢ tunnellLayerPopulation n,
          -q.1.1 * tunnellLayerWeight q.2) =
        -heckeCoeff p * fullTunnellThetaCoefficient n := by
    rw [Finset.sum_product]
    simp_rw [weightedTunnellLayerTotal]
    rw [← Finset.sum_mul]
    rw [Finset.sum_neg_distrib]
    unfold heckeCoeff
    ring
  rw [htarget]
  by_cases hdiv : p ^ 2 ∣ n
  · rw [quotientTunnellLayerPopulation, if_pos hdiv,
      weightedTunnellLayerTotal, integralTunnellHeckeDefect, if_pos hdiv]
    ring
  · rw [quotientTunnellLayerPopulation, if_neg hdiv, integralTunnellHeckeDefect,
      if_neg hdiv]
    simp
    ring

/-- The rational normalized defect is precisely one half of the signed population
return. -/
theorem two_mul_tunnellHalfIntegralHeckeDefect (p n : ℕ) :
    (2 : ℚ) * tunnellHalfIntegralHeckeDefect p n =
      (integralTunnellHeckeDefect p n : ℚ) := by
  unfold tunnellHalfIntegralHeckeDefect halfIntegralHeckeCoefficient
    normalizedTunnellCoefficient integralTunnellHeckeDefect
  by_cases hdiv : p ^ 2 ∣ n
  · rw [exactQuotientCoefficient, if_pos hdiv, if_pos hdiv]
    push_cast
    ring
  · rw [exactQuotientCoefficient, if_neg hdiv, if_neg hdiv]
    push_cast
    ring

/-! ## 3. The swing criterion for the missing lattice correspondence -/

/-- A finite signed carrier, with no collapse of its occurrences into its total. -/
structure SignedFiniteCarrier (α : Type) [DecidableEq α] where
  occurrences : Finset α
  weight : α → ℤ

def SignedFiniteCarrier.total {α : Type} [DecidableEq α]
    (carrier : SignedFiniteCarrier α) : ℤ :=
  ∑ x ∈ carrier.occurrences, carrier.weight x

/-- The exact cancellation structure sought from the lattice Hecke correspondence:
the swing stays in the carrier, returns after two turns, and reverses orientation. -/
structure CancellingSwing {α : Type} [DecidableEq α]
    (carrier : SignedFiniteCarrier α) where
  swing : (x : α) → x ∈ carrier.occurrences → α
  weight_reverses : ∀ x hx,
    carrier.weight x + carrier.weight (swing x hx) = 0
  nonfixed_of_nonzero : ∀ x hx,
    carrier.weight x ≠ 0 → swing x hx ≠ x
  stays_inside : ∀ x hx, swing x hx ∈ carrier.occurrences
  returns : ∀ x hx, swing (swing x hx) (stays_inside x hx) = x

/-- A cancelling swing forces the complete signed return to vanish. -/
theorem CancellingSwing.total_eq_zero
    {α : Type} [DecidableEq α] {carrier : SignedFiniteCarrier α}
    (swing : CancellingSwing carrier) : carrier.total = 0 := by
  exact Finset.sum_involution swing.swing swing.weight_reverses
    swing.nonfixed_of_nonzero swing.stays_inside swing.returns

/-- The concrete Hecke plate as a signed finite carrier. -/
def tunnellHeckeCarrier (p n : ℕ) : SignedFiniteCarrier TunnellHeckeOccurrence where
  occurrences := tunnellHeckePopulation p n
  weight := tunnellHeckeWeight p n

theorem tunnellHeckeCarrier_total (p n : ℕ) :
    (tunnellHeckeCarrier p n).total = integralTunnellHeckeDefect p n :=
  tunnellHeckePopulation_totalWeight p n

/-- A cancelling lattice swing on every coefficient plate proves the complete
Tunnell `T(p²)` eigen-current law at that prime. -/
theorem tunnellEigen_of_cancellingSwings (p : ℕ)
    (swings : ∀ n : ℕ,
      CancellingSwing (α := TunnellHeckeOccurrence) (tunnellHeckeCarrier p n)) :
    IsHalfIntegralHeckeEigenAt normalizedTunnellCoefficient p
      (heckeCoeff p : ℚ) := by
  intro n
  have hzero : integralTunnellHeckeDefect p n = 0 := by
    rw [← tunnellHeckeCarrier_total]
    exact (swings n).total_eq_zero
  have htwo := two_mul_tunnellHalfIntegralHeckeDefect p n
  rw [hzero, Int.cast_zero] at htwo
  unfold tunnellHalfIntegralHeckeDefect at htwo
  linarith

#print axioms tunnellLayerTotalWeight
#print axioms tunnellHeckePopulation_totalWeight
#print axioms two_mul_tunnellHalfIntegralHeckeDefect
#print axioms CancellingSwing.total_eq_zero
#print axioms tunnellEigen_of_cancellingSwings

end Soma.Holonics.Millennium.FamilyTunnellHeckeCorrespondence
