import ElementaryHolonics.Foundation.Holon
import Mathlib.Tactic

/-!
# The twelve polarized Mestre lines are algebraic surface sections

For six rational centres `aᵢ`, put

`p_T(x) = ∏ᵢ ((x - aᵢ)² - T²)`.

If `g(x,T)` is the monic completed-square polynomial and `r = g² - p_T`, Mestre's surface is
`y² = r(x,T)`.  The elementary source incidence does not depend on how `g` was constructed:
on each polarized line `x = aᵢ ± T`, one factor of `p_T` vanishes, hence

`r(aᵢ ± T,T) = g(aᵢ ± T,T)²`.

This file proves that identity in the actual polynomial rings `ℚ[T]` and `ℚ[T][x]`, then retains
the twelve section graphs as occurrences of a `Holon`.  It is the source geometry underneath the
eleven forced-section directions in `MestreHeightLattice`; the twelfth independent direction in
that file is the non-forced section `L0+` and remains a separate obligation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.MestreForcedSectionIncidence

open Soma.Holonics

/-- [definition] The parameter chart `ℚ[T]`. -/
abbrev ParameterPolynomial := Polynomial ℚ

/-- [definition] The family chart `ℚ[T][x]`; the inner indeterminate is `T`, the outer one `x`. -/
abbrev FamilyPolynomial := Polynomial ParameterPolynomial

/-- [definition] The two orientations of a forced section line.  `true` carries `+T` and `false`
carries `-T`; the Boolean is the exact two-state carrier rather than duplicated left/right code. -/
abbrev Polarity := Bool

/-- [definition] The oriented coefficient carried by a section polarity. -/
def Polarity.sign : Polarity → ℚ
  | true => 1
  | false => -1

/-- [definition] One of the twelve source labels, retaining both its centre and polarity. -/
abbrev ForcedSectionLabel := Fin 6 × Polarity

/-- [definition] The first elementary-symmetric face on the six addressed centres. -/
def mestreE1 (centres : Fin 6 → ℚ) : ℚ :=
  centres 0 + centres 1 + centres 2 + centres 3 + centres 4 + centres 5

/-- [definition] The second elementary-symmetric face on the six addressed centres. -/
def mestreE2 (a : Fin 6 → ℚ) : ℚ :=
  a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 0 * a 4 + a 0 * a 5 +
  a 1 * a 2 + a 1 * a 3 + a 1 * a 4 + a 1 * a 5 +
  a 2 * a 3 + a 2 * a 4 + a 2 * a 5 +
  a 3 * a 4 + a 3 * a 5 + a 4 * a 5

/-- [definition] The third elementary-symmetric face on the six addressed centres. -/
def mestreE3 (a : Fin 6 → ℚ) : ℚ :=
  a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 1 * a 4 + a 0 * a 1 * a 5 +
  a 0 * a 2 * a 3 + a 0 * a 2 * a 4 + a 0 * a 2 * a 5 +
  a 0 * a 3 * a 4 + a 0 * a 3 * a 5 + a 0 * a 4 * a 5 +
  a 1 * a 2 * a 3 + a 1 * a 2 * a 4 + a 1 * a 2 * a 5 +
  a 1 * a 3 * a 4 + a 1 * a 3 * a 5 + a 1 * a 4 * a 5 +
  a 2 * a 3 * a 4 + a 2 * a 3 * a 5 + a 2 * a 4 * a 5 + a 3 * a 4 * a 5

/-- [definition] The fifth elementary-symmetric face on the six addressed centres. -/
def mestreE5 (a : Fin 6 → ℚ) : ℚ :=
  a 1 * a 2 * a 3 * a 4 * a 5 + a 0 * a 2 * a 3 * a 4 * a 5 +
  a 0 * a 1 * a 3 * a 4 * a 5 + a 0 * a 1 * a 2 * a 4 * a 5 +
  a 0 * a 1 * a 2 * a 3 * a 5 + a 0 * a 1 * a 2 * a 3 * a 4

/-- [definition] The exact conditions under which the paired-root completed-square remainder
drops from degree at most five to the elliptic quartic case used by Mestre. -/
structure EllipticMestreSextuple where
  centres : Fin 6 → ℚ
  distinct : Function.Injective centres
  traceZero : mestreE1 centres = 0
  quarticCondition :
    2 * mestreE5 centres = mestreE2 centres * mestreE3 centres

/-- [definition] The published rank-17 family numbered 159 in the ICARM table, retained exactly
and without a floating-point chart. -/
def mestre159Centres : Fin 6 → ℚ :=
  ![-1146, -2304, -654, 3054, 2880, -1830]

@[simp] theorem mestre159Centres_zero : mestre159Centres 0 = -1146 := rfl
@[simp] theorem mestre159Centres_one : mestre159Centres 1 = -2304 := rfl
@[simp] theorem mestre159Centres_two : mestre159Centres 2 = -654 := rfl
@[simp] theorem mestre159Centres_three : mestre159Centres 3 = 3054 := rfl
@[simp] theorem mestre159Centres_four : mestre159Centres 4 = 2880 := rfl
@[simp] theorem mestre159Centres_five : mestre159Centres 5 = -1830 := rfl

/-- [proved-derived; formal-checked] The published six centres are pairwise distinct. -/
theorem mestre159Centres_injective : Function.Injective mestre159Centres := by
  decide

/-- [proved-derived; formal-checked] The published six centres have exactly zero trace. -/
theorem mestre159_traceZero : mestreE1 mestre159Centres = 0 := by
  norm_num [mestreE1]

/-- [proved-derived; formal-checked] The published six centres satisfy the exact symmetric
condition which removes the degree-five remainder term. -/
theorem mestre159_quarticCondition :
    2 * mestreE5 mestre159Centres =
      mestreE2 mestre159Centres * mestreE3 mestre159Centres := by
  norm_num [mestreE2, mestreE3, mestreE5]

/-- [proved-derived; formal-checked] The published family is admitted as an exact elliptic Mestre
sextuple, rather than only entering through an exterior report. -/
def mestre159 : EllipticMestreSextuple where
  centres := mestre159Centres
  distinct := mestre159Centres_injective
  traceZero := mestre159_traceZero
  quarticCondition := mestre159_quarticCondition

/-- [definition] The polynomial line `x(T) = aᵢ ± T`. -/
def forcedLine (centres : Fin 6 → ℚ) (label : ForcedSectionLabel) : ParameterPolynomial :=
  Polynomial.C (centres label.1) + Polynomial.C label.2.sign * Polynomial.X

/-- [definition] Evaluation of the outer `x` chart along a polynomial line in `T`. -/
def along (line : ParameterPolynomial) : FamilyPolynomial →+* ParameterPolynomial :=
  Polynomial.eval₂RingHom (RingHom.id ParameterPolynomial) line

/-- [definition] The factor `((x-aᵢ)²-T²)` carried by one centre. -/
def pairedFactor (centres : Fin 6 → ℚ) (index : Fin 6) : FamilyPolynomial :=
  (Polynomial.X - Polynomial.C (Polynomial.C (centres index))) ^ 2 -
    Polynomial.C Polynomial.X ^ 2

/-- [definition] Mestre's paired-root polynomial `p_T(x)`. -/
def familyProduct (centres : Fin 6 → ℚ) : FamilyPolynomial :=
  ∏ index : Fin 6, pairedFactor centres index

/-- [proved-derived; formal-checked] A polarized line kills its own paired factor exactly. -/
theorem pairedFactor_vanishes_on_own_line
    (centres : Fin 6 → ℚ) (label : ForcedSectionLabel) :
    along (forcedLine centres label) (pairedFactor centres label.1) = 0 := by
  rcases label with ⟨index, polarity⟩
  cases polarity <;> simp [along, forcedLine, Polarity.sign, pairedFactor]

/-- [proved-derived; formal-checked] The complete twelve-root product vanishes on every forced
line.  The proof retains the exact factor responsible for the zero. -/
theorem familyProduct_vanishes_on_forced_line
    (centres : Fin 6 → ℚ) (label : ForcedSectionLabel) :
    along (forcedLine centres label) (familyProduct centres) = 0 := by
  classical
  rw [familyProduct, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ label.1)
  exact pairedFactor_vanishes_on_own_line centres label

/-- [definition] The completed-square remainder `r = g²-p_T`. -/
def remainder (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial) :
    FamilyPolynomial :=
  completedSquare ^ 2 - familyProduct centres

/-- [definition] A polynomial section of the affine surface `y² = r(x,T)`. -/
structure SurfaceSection (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial) where
  x : ParameterPolynomial
  y : ParameterPolynomial
  liesOnSurface : y ^ 2 = along x (remainder centres completedSquare)

/-- [definition] The forced section graph carried by one centre and one polarity. -/
def forcedSection (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial)
    (label : ForcedSectionLabel) : SurfaceSection centres completedSquare where
  x := forcedLine centres label
  y := along (forcedLine centres label) completedSquare
  liesOnSurface := by
    rw [remainder, map_sub, map_pow, familyProduct_vanishes_on_forced_line, sub_zero]

/-- [proved-derived; formal-checked] The forced section equation, exposed without the structure
projection: each oriented source line is an exact algebraic graph on the family surface. -/
theorem forced_section_incidence
    (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial)
    (label : ForcedSectionLabel) :
    (along (forcedLine centres label) completedSquare) ^ 2 =
      along (forcedLine centres label) (remainder centres completedSquare) :=
  (forcedSection centres completedSquare label).liesOnSurface

/-- [definition] The source-bearing holon of the twelve forced algebraic sections.  Its occurrence
is the polarized label, its target is the complete polynomial graph, and its receiver returns that
same graph without deleting the source incidence. -/
def forcedSectionHolon (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial) :
    Holon ForcedSectionLabel (SurfaceSection centres completedSquare)
      (SurfaceSection centres completedSquare) where
  Occurrence := ForcedSectionLabel
  source label := label
  target label := forcedSection centres completedSquare label
  receive label := forcedSection centres completedSquare label

/-- [proved-derived; formal-checked] Every forced graph has an occupied preimage fibre whose
witness retains the centre and the sign which produced it. -/
theorem forcedSectionHolon_fibre_occupied
    (centres : Fin 6 → ℚ) (completedSquare : FamilyPolynomial)
    (label : ForcedSectionLabel) :
    Nonempty ((forcedSectionHolon centres completedSquare).PreimageFibre
      (forcedSection centres completedSquare label)) :=
  ⟨⟨label, rfl⟩⟩

/-- [proved-derived; formal-checked] The source population has exactly twelve polarized section
labels; this is a count of retained occurrences, not an independence claim. -/
theorem forcedSectionLabel_card : Fintype.card ForcedSectionLabel = 12 := by
  simp [ForcedSectionLabel]

section Audit

#print axioms pairedFactor_vanishes_on_own_line
#print axioms familyProduct_vanishes_on_forced_line
#print axioms forced_section_incidence
#print axioms forcedSectionHolon_fibre_occupied
#print axioms forcedSectionLabel_card
#print axioms mestre159Centres_injective
#print axioms mestre159_traceZero
#print axioms mestre159_quarticCondition

end Audit

end Soma.Holonics.Millennium.MestreForcedSectionIncidence
