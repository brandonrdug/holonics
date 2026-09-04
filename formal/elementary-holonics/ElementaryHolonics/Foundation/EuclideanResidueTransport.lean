import ElementaryHolonics.Foundation.ExactPartition
import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Foundation.ReceiverQuotient
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Euclidean residue transport as a lossless holonic chart

This file separates four objects which the overloaded word `modulus` can otherwise collapse:

* a lossless Euclidean chart, carrying both a residue face and a quotient/winding coordinate;
* the residue receiver quotient, whose complete preimage fibre retains that winding;
* equality in `ZMod modulus`, which is equality after the residue receiver; and
* scalar divisibility, which is the zero-residue fibre and hence a specialized multiplication
  lift rather than division of an arbitrary holon, matrix, tensor, or geometric body.

For natural sources Mathlib already supplies the exact equivalence
`Nat.residueClassesEquiv modulus : ℕ ≃ ZMod modulus × ℕ`.  The integer lift below supplies its
oriented counterpart `ℤ ≃ ZMod modulus × ℤ`.  The sign of the integer winding coordinate is the
polarity lost by the residue receiver: advancing or reversing one winding changes the source by
`+modulus` or `-modulus` while returning the same residue face.

Analytic absolute value, geometric moduli spaces, and signed codimension-one divisor ledgers are
not identified with this construction.  They may meet it only through an additional typed
passage.
-/

namespace Soma.Holonics.Foundation.EuclideanResidueTransport

open Soma.Holonics
open Soma.Holonics.Foundation.ExactPartition
open Soma.Holonics.Foundation.ReceiverCompression

universe u v w

/-! ## Any lossless residue/winding chart returns a holon and a quotient fibre -/

/-- [definition] A lossless residue chart regarded as one occurrence-bearing holon.  Its target
retains both coordinates while its receiver exposes only the residue face. -/
def chartHolon {Source : Type u} {Residue : Type v} {Winding : Type w}
    (chart : Source ≃ Residue × Winding) :
    Holon Source (Residue × Winding) Residue where
  Occurrence := Source
  source := id
  target := chart
  receive source := (chart source).1

/-- [definition] Projection of a lossless residue/winding chart to its residue receiver. -/
def firstProjectionQuotient {Source : Type u} {Residue : Type v} {Winding : Type w}
    (chart : Source ≃ Residue × Winding) :
    ReceiverQuotient Unit Source Residue Residue where
  quotient source := (chart source).1
  receiver _ source := (chart source).1
  factor _ := id
  exact _ _ := rfl

/-- [proved-derived; formal-checked] The complete predecessor fibre of the projected residue is
equivalent to the winding carrier.  The quotient did not destroy the coordinate; it moved it into
the preimage fibre. -/
def firstProjectionPreimageFibreEquiv
    {Source : Type u} {Residue : Type v} {Winding : Type w}
    (chart : Source ≃ Residue × Winding) (residue : Residue) :
    preimageFibre (firstProjectionQuotient chart) residue ≃ Winding where
  toFun source := (chart source.1).2
  invFun winding :=
    ⟨chart.symm (residue, winding),
      congrArg Prod.fst (chart.apply_symm_apply (residue, winding))⟩
  left_inv source := by
    apply Subtype.ext
    change chart.symm (residue, (chart source.1).2) = source.1
    apply chart.injective
    rw [chart.apply_symm_apply]
    exact Prod.ext source.2.symm rfl
  right_inv winding := by
    exact congrArg Prod.snd (chart.apply_symm_apply (residue, winding))

/-! ## Natural Euclidean residues -/

/-- [definition] Mathlib's exact natural quotient/remainder chart, retained under its holonic
role.  No floor approximation occurs: the equivalence reconstructs the source exactly. -/
abbrev natEuclideanChart (modulus : ℕ) [NeZero modulus] :
    ℕ ≃ ZMod modulus × ℕ :=
  Nat.residueClassesEquiv modulus

/-- [definition] The natural Euclidean residue holon. -/
def natEuclideanHolon (modulus : ℕ) [NeZero modulus] :
    Holon ℕ (ZMod modulus × ℕ) (ZMod modulus) :=
  chartHolon (natEuclideanChart modulus)

/-- [definition] The natural residue receiver quotient. -/
def natResidueQuotient (modulus : ℕ) [NeZero modulus] :
    ReceiverQuotient Unit ℕ (ZMod modulus) (ZMod modulus) :=
  firstProjectionQuotient (natEuclideanChart modulus)

/-- [proved-derived; formal-checked] One natural residue fibre reconstructs exactly as the
nonnegative quotient/winding coordinate. -/
def natResiduePreimageFibreEquiv (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) :
    preimageFibre (natResidueQuotient modulus) residue ≃ ℕ :=
  firstProjectionPreimageFibreEquiv (natEuclideanChart modulus) residue

/-- [proved-derived; formal-checked] Equality at the residue receiver is precisely natural
congruence modulo the declared scalar face. -/
theorem natResidue_eq_iff_modEq (modulus left right : ℕ) [NeZero modulus] :
    (natResidueQuotient modulus).quotient left =
        (natResidueQuotient modulus).quotient right ↔
      left ≡ right [MOD modulus] := by
  exact ZMod.natCast_eq_natCast_iff left right modulus

/-- [proved-derived; formal-checked] Scalar divisibility is exactly occupancy of the zero-residue
fibre, and exactly existence of the established multiplication lift.  This does not define
division of the source holon. -/
theorem natZeroResidue_iff_factorWitness (modulus source : ℕ) [NeZero modulus] :
    (natResidueQuotient modulus).quotient source = 0 ↔
      Nonempty (NatFactorWitness modulus source) := by
  rw [show (natResidueQuotient modulus).quotient source = (source : ZMod modulus) by rfl]
  rw [ZMod.natCast_eq_zero_iff]
  exact (NatFactorWitness.nonempty_iff_dvd modulus source).symm

/-! ## Integer residues retain polarized winding -/

/-- [proved-derived; formal-checked] The oriented Euclidean chart.  The finite residue is a
cross-section; the signed quotient is the complete winding coordinate through that section. -/
def intEuclideanChart (modulus : ℕ) [NeZero modulus] :
    ℤ ≃ ZMod modulus × ℤ where
  toFun source := ((source : ZMod modulus), source / (modulus : ℤ))
  invFun face := (face.1.val : ℤ) + (modulus : ℤ) * face.2
  left_inv source := by
    change ((source : ZMod modulus).val : ℤ) +
      (modulus : ℤ) * (source / (modulus : ℤ)) = source
    rw [ZMod.val_intCast]
    exact Int.emod_add_mul_ediv source (modulus : ℤ)
  right_inv face := by
    have modulusPositive : (0 : ℤ) < (modulus : ℤ) := by
      exact_mod_cast NeZero.pos modulus
    have unique :
        (((face.1.val : ℤ) + (modulus : ℤ) * face.2) / (modulus : ℤ) = face.2 ∧
          ((face.1.val : ℤ) + (modulus : ℤ) * face.2) % (modulus : ℤ) =
            face.1.val) :=
      (Int.ediv_emod_unique modulusPositive).mpr
        ⟨rfl, Int.natCast_nonneg _, by exact_mod_cast face.1.val_lt⟩
    apply Prod.ext
    · change ((((face.1.val : ℤ) + (modulus : ℤ) * face.2 : ℤ) :
          ZMod modulus)) = face.1
      simpa only [Int.cast_add, Int.cast_natCast, Int.cast_mul,
        ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero]
    · exact unique.1

/-- [definition] The oriented integer residue holon. -/
def intEuclideanHolon (modulus : ℕ) [NeZero modulus] :
    Holon ℤ (ZMod modulus × ℤ) (ZMod modulus) :=
  chartHolon (intEuclideanChart modulus)

/-- [definition] The oriented integer residue receiver quotient. -/
def intResidueQuotient (modulus : ℕ) [NeZero modulus] :
    ReceiverQuotient Unit ℤ (ZMod modulus) (ZMod modulus) :=
  firstProjectionQuotient (intEuclideanChart modulus)

/-- [proved-derived; formal-checked] One integer residue fibre reconstructs exactly as a signed
winding axis. -/
def intResiduePreimageFibreEquiv (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) :
    preimageFibre (intResidueQuotient modulus) residue ≃ ℤ :=
  firstProjectionPreimageFibreEquiv (intEuclideanChart modulus) residue

/-- [proved-derived; formal-checked] Equality at the oriented residue receiver is exactly the
statement that the returned difference is a whole signed winding of the modulus. -/
theorem intResidue_eq_iff_dvd_difference (modulus : ℕ) [NeZero modulus]
    (left right : ℤ) :
    (intResidueQuotient modulus).quotient left =
        (intResidueQuotient modulus).quotient right ↔
      (modulus : ℤ) ∣ right - left := by
  exact ZMod.intCast_eq_intCast_iff_dvd_sub left right modulus

/-- [definition] Reconstruct the source occurrence at one residue and signed winding. -/
def orientedSource (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) (winding : ℤ) : ℤ :=
  (intEuclideanChart modulus).symm (residue, winding)

/-- [proved-derived; formal-checked] One positive winding step advances the source by the declared
modulus while preserving the residue cross-section. -/
theorem orientedSource_forward (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) (winding : ℤ) :
    orientedSource modulus residue (winding + 1) =
      orientedSource modulus residue winding + modulus := by
  simp only [orientedSource, intEuclideanChart, Equiv.coe_fn_symm_mk]
  ring

/-- [proved-derived; formal-checked] One negative winding step reverses the same axis. -/
theorem orientedSource_reverse (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) (winding : ℤ) :
    orientedSource modulus residue (winding - 1) =
      orientedSource modulus residue winding - modulus := by
  simp only [orientedSource, intEuclideanChart, Equiv.coe_fn_symm_mk]
  ring

/-- [proved-derived; formal-checked] Every signed winding reconstructs inside the requested
residue fibre. -/
theorem orientedSource_returns_residue (modulus : ℕ) [NeZero modulus]
    (residue : ZMod modulus) (winding : ℤ) :
    (intResidueQuotient modulus).quotient
        (orientedSource modulus residue winding) = residue := by
  exact congrArg Prod.fst
    ((intEuclideanChart modulus).apply_symm_apply (residue, winding))

/-! ## Signed quotient conventions are cross-section choices

Lean also exposes truncated (`tdiv`/`tmod`) and floor (`fdiv`/`fmod`) signed division.  Their
coordinate pairs reconstruct the same source exactly.  Floor division at a positive modulus is
the Euclidean product chart above.  Truncated division agrees on the nonnegative half-axis but,
across the sign seam, selects a different representative and compensating winding.  Its admissible
coordinate population is therefore retained as an image subtype rather than incorrectly declared
to be the whole product `ℤ × ℤ`.
-/

/-- [definition] Remainder and quotient coordinates selected by truncation toward zero. -/
def intTruncatedCoordinates (modulus : ℕ) (source : ℤ) : ℤ × ℤ :=
  (source.tmod (modulus : ℤ), source.tdiv (modulus : ℤ))

/-- [definition] Remainder and quotient coordinates selected by floor division. -/
def intFloorCoordinates (modulus : ℕ) (source : ℤ) : ℤ × ℤ :=
  (source.fmod (modulus : ℤ), source.fdiv (modulus : ℤ))

/-- [proved-derived; formal-checked] Truncated coordinates reconstruct the source exactly. -/
theorem intTruncatedCoordinates_reconstruct (modulus : ℕ) (source : ℤ) :
    (intTruncatedCoordinates modulus source).1 +
        (modulus : ℤ) * (intTruncatedCoordinates modulus source).2 = source := by
  exact Int.tmod_add_mul_tdiv source (modulus : ℤ)

/-- [proved-derived; formal-checked] Floor coordinates reconstruct the source exactly. -/
theorem intFloorCoordinates_reconstruct (modulus : ℕ) (source : ℤ) :
    (intFloorCoordinates modulus source).1 +
        (modulus : ℤ) * (intFloorCoordinates modulus source).2 = source := by
  exact Int.fmod_add_mul_fdiv source (modulus : ℤ)

/-- [proved-derived; formal-checked] Exact reconstruction makes the truncated chart injective. -/
theorem intTruncatedCoordinates_injective (modulus : ℕ) :
    Function.Injective (intTruncatedCoordinates modulus) := by
  intro left right hequal
  rw [← intTruncatedCoordinates_reconstruct modulus left,
    ← intTruncatedCoordinates_reconstruct modulus right, hequal]

/-- [proved-derived; formal-checked] Exact reconstruction makes the floor chart injective. -/
theorem intFloorCoordinates_injective (modulus : ℕ) :
    Function.Injective (intFloorCoordinates modulus) := by
  intro left right hequal
  rw [← intFloorCoordinates_reconstruct modulus left,
    ← intFloorCoordinates_reconstruct modulus right, hequal]

/-- [proved-derived; formal-checked] The truncated convention is a lossless chart onto its actual
admissible coordinate population. -/
noncomputable def intTruncatedImageChart (modulus : ℕ) :
    ℤ ≃ Set.range (intTruncatedCoordinates modulus) :=
  Equiv.ofInjective _ (intTruncatedCoordinates_injective modulus)

/-- [proved-derived; formal-checked] The floor convention is a lossless chart onto its actual
admissible coordinate population. -/
noncomputable def intFloorImageChart (modulus : ℕ) :
    ℤ ≃ Set.range (intFloorCoordinates modulus) :=
  Equiv.ofInjective _ (intFloorCoordinates_injective modulus)

/-- [definition] The truncated coordinate convention as a source-retaining Holon.  Its target is
the admissible image, while its receiver is the common arithmetic quotient. -/
noncomputable def intTruncatedImageHolon (modulus : ℕ) [NeZero modulus] :
    Holon ℤ (Set.range (intTruncatedCoordinates modulus)) (ZMod modulus) where
  Occurrence := ℤ
  source := id
  target := intTruncatedImageChart modulus
  receive source := (source : ZMod modulus)

/-- [definition] The floor coordinate convention as a source-retaining Holon. -/
noncomputable def intFloorImageHolon (modulus : ℕ) [NeZero modulus] :
    Holon ℤ (Set.range (intFloorCoordinates modulus)) (ZMod modulus) where
  Occurrence := ℤ
  source := id
  target := intFloorImageChart modulus
  receive source := (source : ZMod modulus)

/-- [proved-derived; formal-checked] At a positive modulus, floor coordinates are exactly the
Euclidean representative and signed winding already carried by `intEuclideanChart`. -/
theorem intFloorCoordinates_eq_euclidean (modulus : ℕ) [NeZero modulus]
    (source : ℤ) :
    intFloorCoordinates modulus source =
      (((source : ZMod modulus).val : ℤ), source / (modulus : ℤ)) := by
  have modulusPositive : (0 : ℤ) < (modulus : ℤ) := by
    exact_mod_cast NeZero.pos modulus
  have euclidean :=
    (Int.ediv_emod_unique modulusPositive).mp
      (show source / (modulus : ℤ) = source / (modulus : ℤ) ∧
        source % (modulus : ℤ) = source % (modulus : ℤ) from ⟨rfl, rfl⟩)
  have floorCoordinates :=
    (Int.fdiv_fmod_unique modulusPositive).mpr euclidean
  apply Prod.ext
  · change source.fmod (modulus : ℤ) = ((source : ZMod modulus).val : ℤ)
    rw [floorCoordinates.2, ZMod.val_intCast]
  · exact floorCoordinates.1

/-- [proved-derived; formal-checked] On the nonnegative half-axis, truncated coordinates select
the same Euclidean cross-section and winding. -/
theorem intTruncatedCoordinates_eq_euclidean_of_nonnegative
    (modulus : ℕ) [NeZero modulus] (source : ℤ) (hsource : 0 ≤ source) :
    intTruncatedCoordinates modulus source =
      (((source : ZMod modulus).val : ℤ), source / (modulus : ℤ)) := by
  have modulusPositive : (0 : ℤ) < (modulus : ℤ) := by
    exact_mod_cast NeZero.pos modulus
  have euclidean :=
    (Int.ediv_emod_unique modulusPositive).mp
      (show source / (modulus : ℤ) = source / (modulus : ℤ) ∧
        source % (modulus : ℤ) = source % (modulus : ℤ) from ⟨rfl, rfl⟩)
  have truncated :=
    (Int.tdiv_tmod_unique hsource (ne_of_gt modulusPositive)).mpr euclidean
  apply Prod.ext
  · change source.tmod (modulus : ℤ) = ((source : ZMod modulus).val : ℤ)
    rw [truncated.2, ZMod.val_intCast]
  · exact truncated.1

/-- [proved-derived; formal-checked] Crossing the sign seam rebases the representative and the
winding together: Euclidean/floor coordinates use `(5,-1)` for `-3` modulo eight, while truncation
uses `(-3,0)`.  Both pairs reconstruct the same source occurrence. -/
theorem negativeThree_modEight_crossSection_rebase :
    intEuclideanChart 8 (-3) = ((5 : ZMod 8), -1) ∧
      intTruncatedCoordinates 8 (-3) = (-3, 0) := by
  decide

section Audit

#print axioms firstProjectionPreimageFibreEquiv
#print axioms natResiduePreimageFibreEquiv
#print axioms natResidue_eq_iff_modEq
#print axioms natZeroResidue_iff_factorWitness
#print axioms intEuclideanChart
#print axioms intResiduePreimageFibreEquiv
#print axioms intResidue_eq_iff_dvd_difference
#print axioms orientedSource_forward
#print axioms orientedSource_reverse
#print axioms orientedSource_returns_residue
#print axioms intTruncatedCoordinates_reconstruct
#print axioms intFloorCoordinates_reconstruct
#print axioms intTruncatedImageChart
#print axioms intFloorImageChart
#print axioms intFloorCoordinates_eq_euclidean
#print axioms intTruncatedCoordinates_eq_euclidean_of_nonnegative
#print axioms negativeThree_modEight_crossSection_rebase

end Audit

end Soma.Holonics.Foundation.EuclideanResidueTransport
