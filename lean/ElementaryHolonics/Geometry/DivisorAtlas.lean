import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic

/-!
# Signed divisor ledgers and Cartier chart transport

This file separates algebraic-geometric divisors from arithmetic division.

* A `WeilDivisorLedger` is a finite signed population of declared irreducible codimension-one
  loci.  The locus type carries that geometric declaration; the integer coefficient carries
  orientation and multiplicity.
* A `PrincipalDivisorSystem` transports multiplication of nonzero local functions to addition of
  signed ledgers.  Inversion negates the ledger and a ratio returns a difference.
* A `CartierAtlas` carries local equations and admitted unit transitions on chart overlaps.
  A `CartierDivisorAtlas` additionally states that admitted transitions have zero principal
  ledger, from which the local ledgers glue exactly.

Nothing here divides an arbitrary holon, constructs a scheme, or claims that an untyped locus is a
prime divisor.  Those geometric hypotheses must be supplied by each specialization.
-/

namespace Soma.Holonics.Geometry.DivisorAtlas

universe u v w x

/-- [definition] A finite signed ledger over declared irreducible codimension-one loci. -/
abbrev WeilDivisorLedger (PrimeLocus : Type u) := PrimeLocus →₀ ℤ

/-- [definition] An effective ledger has no negatively oriented coefficient. -/
def Effective {PrimeLocus : Type u} (ledger : WeilDivisorLedger PrimeLocus) : Prop :=
  ∀ locus, 0 ≤ ledger locus

/-- The empty codimension-one population is effective. -/
theorem zero_effective {PrimeLocus : Type u} :
    Effective (0 : WeilDivisorLedger PrimeLocus) := by
  intro locus
  simp

/-- Addition of effective ledgers preserves effectiveness. -/
theorem Effective.add {PrimeLocus : Type u}
    {left right : WeilDivisorLedger PrimeLocus}
    (hleft : Effective left) (hright : Effective right) :
    Effective (left + right) := by
  intro locus
  simp only [Finsupp.add_apply]
  exact add_nonneg (hleft locus) (hright locus)

/-- [definition] A principal-divisor system turns multiplicative composition of nonzero local
functions into additive composition of signed codimension-one ledgers. -/
structure PrincipalDivisorSystem (Function : Type v) (PrimeLocus : Type u)
    [CommGroup Function] where
  divisor : Function → WeilDivisorLedger PrimeLocus
  divisor_one : divisor 1 = 0
  divisor_mul : ∀ left right, divisor (left * right) = divisor left + divisor right

namespace PrincipalDivisorSystem

variable {Function : Type v} {PrimeLocus : Type u} [CommGroup Function]

/-- [proved-derived; formal-checked] Inversion reverses every oriented divisor coefficient. -/
theorem divisor_inv (system : PrincipalDivisorSystem Function PrimeLocus) (function : Function) :
    system.divisor function⁻¹ = -system.divisor function := by
  apply Finsupp.ext
  intro locus
  have h := congrArg (fun ledger : WeilDivisorLedger PrimeLocus ↦ ledger locus)
    (system.divisor_mul function function⁻¹)
  simp only [mul_inv_cancel, system.divisor_one, Finsupp.zero_apply, Finsupp.add_apply] at h
  have : system.divisor function locus + system.divisor function⁻¹ locus = 0 := h.symm
  simp only [Finsupp.neg_apply]
  omega

/-- [proved-derived; formal-checked] A quotient of local functions returns subtraction of their
signed divisor ledgers.  The sign comes from orientation reversal under inversion. -/
theorem divisor_div (system : PrincipalDivisorSystem Function PrimeLocus)
    (numerator denominator : Function) :
    system.divisor (numerator / denominator) =
      system.divisor numerator - system.divisor denominator := by
  rw [div_eq_mul_inv, system.divisor_mul, system.divisor_inv, sub_eq_add_neg]

end PrincipalDivisorSystem

/-- [definition] Local equations and admitted unit transitions over an exact chart cover. -/
structure CartierAtlas (Point : Type w) (Chart : Type x) (Function : Type v)
    [CommGroup Function] where
  active : Chart → Point → Prop
  cover : ∀ point, ∃ chart, active chart point
  localEquation : Chart → Function
  transition : Chart → Chart → Function
  IsAdmittedUnit : Function → Prop
  transition_is_unit : ∀ left right, IsAdmittedUnit (transition left right)
  transition_refl : ∀ chart, transition chart chart = 1
  local_change : ∀ {point left right}, active left point → active right point →
    localEquation left = transition left right * localEquation right
  transition_cocycle : ∀ {point left middle right},
    active left point → active middle point → active right point →
      transition left middle * transition middle right = transition left right

namespace CartierAtlas

variable {Point : Type w} {Chart : Type x} {Function : Type v} [CommGroup Function]

/-- [proved-derived; formal-checked] Opposite overlap transports compose to the identity. -/
theorem transition_reverse (atlas : CartierAtlas Point Chart Function)
    {point : Point} {left right : Chart}
    (hleft : atlas.active left point) (hright : atlas.active right point) :
    atlas.transition left right * atlas.transition right left = 1 := by
  calc
    atlas.transition left right * atlas.transition right left =
        atlas.transition left left := atlas.transition_cocycle hleft hright hleft
    _ = 1 := atlas.transition_refl left

/-- [proved-derived; formal-checked] An overlap equation is reconstructed by its typed transition. -/
theorem localEquation_reconstructs (atlas : CartierAtlas Point Chart Function)
    {point : Point} {left right : Chart}
    (hleft : atlas.active left point) (hright : atlas.active right point) :
    atlas.transition left right * atlas.localEquation right = atlas.localEquation left :=
  (atlas.local_change hleft hright).symm

end CartierAtlas

/-- [definition] A Cartier atlas whose admitted overlap units carry no principal divisor. -/
structure CartierDivisorAtlas (Point : Type w) (Chart : Type x)
    (Function : Type v) (PrimeLocus : Type u) [CommGroup Function] where
  atlas : CartierAtlas Point Chart Function
  principal : PrincipalDivisorSystem Function PrimeLocus
  admittedUnit_has_zero_divisor : ∀ function,
    atlas.IsAdmittedUnit function → principal.divisor function = 0

namespace CartierDivisorAtlas

variable {Point : Type w} {Chart : Type x} {Function : Type v} {PrimeLocus : Type u}
  [CommGroup Function]

/-- [proved-derived; formal-checked] Local principal ledgers agree on every occupied overlap.
The apparent quotient of local equations is therefore a unit-valued chart transition, not an
untyped division of the geometric body. -/
theorem localLedgersAgree (atlas : CartierDivisorAtlas Point Chart Function PrimeLocus)
    {point : Point} {left right : Chart}
    (hleft : atlas.atlas.active left point) (hright : atlas.atlas.active right point) :
    atlas.principal.divisor (atlas.atlas.localEquation left) =
      atlas.principal.divisor (atlas.atlas.localEquation right) := by
  rw [atlas.atlas.local_change hleft hright, atlas.principal.divisor_mul,
    atlas.admittedUnit_has_zero_divisor _ (atlas.atlas.transition_is_unit left right), zero_add]

end CartierDivisorAtlas

section Audit

#print axioms Effective.add
#print axioms PrincipalDivisorSystem.divisor_inv
#print axioms PrincipalDivisorSystem.divisor_div
#print axioms CartierAtlas.transition_reverse
#print axioms CartierDivisorAtlas.localLedgersAgree

end Audit

end Soma.Holonics.Geometry.DivisorAtlas
