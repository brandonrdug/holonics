import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import ElementaryHolonics.Millennium.Lines

/-!
# Border: the degeneration reaches the padded permanent, and the remainder carries both hands

The smallest instance in which the **border** of a determinant reaches something a limit-free
substitution does not: `n = 3`, `m = 2`, the padded two-by-two permanent `x₀₀ · perm₂` sitting at
the `e → 0` end of a *declared* one-parameter substitution of the generic three-by-three
determinant.  Everything is exact over `ℚ`, inside `MvPolynomial (Fin 3 × Fin 3) ℚ`.  Nothing
floats, nothing is approximated, and no limit is asserted without its path.

## What is proved

1. **The degeneration, with its family declared and its remainder exhibited.**  For every `e`,
   `det M(e) = x₀₀ · perm₂ + e² · R`, where `M(e)` is the generic matrix with the four off-block
   entries scaled by `e` and one sign flipped.  There is no `e¹` term: the expansion goes from the
   padded permanent straight to the square.  `R` is not a residue that got swept up — it is
   written out, and it splits into **one summand of each hand**: a two-by-two *permanent*
   (mathlib's `Matrix.permanent`) against `x₀₁`, and a two-by-two *determinant* against `x₀₂`.
   The two hands are not one reading; they separate at an exhibited rational probe, `+1` against
   `−1`.  Netting them would delete the difference, which is what reporting a remainder as a
   magnitude does.

2. **The family is an invertible substitution, singular exactly at the limit.**  The substitution
   is the diagonal matrix `diag(1, e, e, e, 1, −1, e, 1, 1)` acting on the nine variables;
   `theSubstitutionIsTheScalingMatrixActing` says the substitution *is* that matrix acting, and
   the matrix's determinant is `−e⁴`.  So the family is invertible at every `e ≠ 0` and singular
   at `e = 0` — which is what makes *border* the load-bearing word rather than *orbit*.  A limit
   whose path is discarded is a quotient with no exhibited fibre, and that is a collapse theorem
   rather than a slogan: over `ℂ` every homogeneous form lies in the border of a depth-three
   top-fan-in-two circuit while some quadratics require top fan-in `Ω(n)` exactly (Kumar, ACM
   Trans. Comput. Theory 2020).  The path is not discarded here.

3. **The two objects have different blind directions.**  A *direction* is a vector on the nine
   variables; it *annihilates* `f` when `∑ vₛ · ∂ₛ f = 0`.  The padded permanent is annihilated by
   every direction supported on the four slots it does not mention.  The generic determinant is
   annihilated by **no** nonzero direction whatsoever: its nine first partials are the nine
   complementary two-by-two minors, whose monomial supports are pairwise disjoint, and nine
   exhibited rational probes read the nine coefficients off one at a time.  The control is
   `theDeterminantIsNotBlindAlongTheAbsentSlot` — the very direction that blinds the padded
   permanent does not blind the determinant.

4. **A reading that vanishes along the punctured family vanishes at the limit.**  Two rational
   parameters suffice: a linear functional killed at `e = 1` and at `e = 2` is killed at `e = 0`.
   Instantiated into `Lines.ReceiverFamily`, this makes the family of linear readings annihilating
   the punctured curve **blind** to membership on the curve, and
   `Lines.blindFamilyCarriesNoVerdict` then says no function whatsoever of those readings decides
   it.

## What is refused

**The orbit separation is not proved and is named open.**
`TheOrbitDoesNotCarryThePaddedPermanent` — no invertible linear substitution carries the generic
determinant to the padded permanent — is a `Prop`, not a theorem.  What *is* proved is the
reduction: granted `BlindnessTransportsAlongTheSubstitution`, the two annihilator computations
close it, because the transported direction is the `(0,1)`-column of the substituting matrix and a
zero column kills its determinant.  The transport hypothesis is the chain rule for a linear
substitution together with the injectivity an invertible substitution supplies; it is classical and
elementary and it is simply not carried here.  Stating it as a hypothesis is what keeps the
reduction honest about what it assumes, and it is the one thing a successor deed owes.

**Nothing here is an insight about geometric complexity theory, and the fourth item least of all.**
That the vanishing ideal of a set equals that of its closure is exactly *why* the Mulmuley–Sohoni
programme is posed on orbit **closures**; re-deriving Zariski closure in receiver vocabulary would
be a restatement dressed as a discovery.  What the fourth item buys is a **Lean** deed and not a
mathematical one: `Lines.blindFamilyCarriesNoVerdict` had exactly one witness — the
residue-modulo-two reading against the hand — and now has one on a real algebraic object, with a
nonzero reading in the declared family exhibited by name
(`theConstantReadingIsADeclaredNonzeroReading`) so the family cannot be blind by being empty.

**No obstruction is exhibited, because at `n = 3, m = 2` there is none to exhibit.**  The padded
permanent *is* in the border, and the first two items are the exhibit.  This file is therefore the
**control** for any later obstruction machinery: a candidate obstruction functional that fires here
is refuted on the spot.  At `n = 2` the determinant and the permanent share an orbit outright,
through the sign flip on one entry, so three is the first size at which anything happens at all.

**Two of the checks below cannot fail, and are stated as checks.**  The expansion identity and the
scaling determinant are decidable computations; a check whose material cannot vary the property
under test carries no evidence, however exact the apparatus around it.  What *can* fail — and what
makes this more than bookkeeping — is `theTwoHandsAreNotOneReading` and
`theDeterminantIsNotBlindAlongTheAbsentSlot`: both are separations at exhibited witnesses, and both
would go red if the remainder's two hands were netted or if the determinant had an
essential-variable deficiency.

**Two readings are carried as speculation, not as findings.**  That the padding `x₀₀^{n−m}` is a
receiver coordinate promoted into the object, and that this is *why* occurrence obstructions fail,
is unverified causal attribution; the cited fact is only that a padding-free reformulation exists,
replacing the determinant by the trace of a matrix power (Gesmundo–Ikenmeyer–Panova).  And the
reading that occurrence → multiplicity → object is a three-step may be a two-step read as three:
multiplicity obstructions are still counts, and a symmetry-derived object is how an obstruction gets
*constructed*, while what gets *compared* remains a multiplicity.

## Imported and not proved here

Cited so the instance is read at its true height; none of these is stated or used below.  The
determinant-versus-permanent programme and the completeness of the permanent (Valiant 1979); the
orbit-closure formulation of the separation and the obstruction proposal (Mulmuley–Sohoni, SIAM J.
Comput. 2001); that occurrence obstructions cannot separate these two orbit closures
(Bürgisser–Ikenmeyer–Panova, FOCS 2016, J. Amer. Math. Soc. 2019) — which explicitly does *not* rule
out multiplicity obstructions; that multiplicity obstructions are strictly stronger than occurrence
obstructions (Dörfler–Ikenmeyer–Panova, ICALP 2019); the first implemented separation of two orbit
closures by an obstruction built from the symmetry groups of *both* polynomials
(Ikenmeyer–Kandasamy, STOC 2020); `dc(perm₂) = 2` and `dc(perm₃) = 7` (Alper–Bogart–Velasco, Found.
Comput. Math. 2017), which is the general reason a size-two permanent lands inside the size-three
border while a size-three one does not land inside the size-four border — the degeneration below is
the direct exhibit for the first of those and cites nothing; and the border determinantal lower
bound `m²/2` for the `m × m` permanent (Landsberg–Manivel–Ressayre), which is what would make the
same construction one size up a falsifier with teeth rather than a check.

## Measured, 2026-08-21

Over the vendored mathlib at `v4.27.0`, run from `soma/formal/elementary-holonics`:
`grep -rli "schurPoly\|SchurPolynomial\|kroneckerCoeff\|plethysm" .lake/packages/mathlib/Mathlib
--include='*.lean'` → 0 files; the same command for `highestWeight` → 1 file,
`Mathlib/Combinatorics/Young/SemistandardTableau.lean`;
`ls .lake/packages/mathlib/Mathlib/Data/Matrix/Kronecker.lean` → no such file.  Those commands
measure those names over that scope and are not a claim that no related content exists under
another name.  A deed on multiplicities is out of reach in that library today; a deed on the border
geometry is not.  `Matrix.permanent` **is** present, at
`Mathlib/LinearAlgebra/Matrix/Permanent.lean`, and is used below rather than re-declared; that file
carries no two-by-two closed form, so one is proved here by enumerating the two permutations of a
two-element type.

`theRemainderCarriesBothHands`, `theFamilyIsTheScaledDeterminant` and
`theLimitOfTheFamilyIsThePaddedPermanent` are definitional unfoldings — stated so the docstring
says so.

Every `theorem` is discharged and none depends on `sorryAx`.

Nothing here formalizes P versus NP, Valiant's conjecture, or any statement about determinantal
complexity at any size other than the exhibited three-by-three and two-by-two carriers; no
multiplicity, no highest weight and no representation appears, and nothing in this file may be
cited as movement on any named question.
-/

namespace Soma.Holonics.Millennium.Border

open MvPolynomial

/-! ## 0. The carriers -/

/-- One matrix position: the index type of the nine variables. -/
abbrev Slot : Type := Fin 3 × Fin 3

/-- The exact carrier: rational polynomials in the nine matrix entries. -/
abbrev R : Type := MvPolynomial Slot ℚ

/-- The variable at one slot. -/
noncomputable def x (i j : Fin 3) : R := MvPolynomial.X (i, j)

/-- The generic three-by-three matrix. -/
noncomputable def gen : Matrix (Fin 3) (Fin 3) R :=
  !![x 0 0, x 0 1, x 0 2; x 1 0, x 1 1, x 1 2; x 2 0, x 2 1, x 2 2]

/-- The generic determinant — the object whose border is at issue. -/
noncomputable def det3 : R := gen.det

/-- The lower-right two-by-two block. -/
noncomputable def blockPadded : Matrix (Fin 2) (Fin 2) R := !![x 1 1, x 1 2; x 2 1, x 2 2]

/-- The two-by-two permanent, taken with mathlib's `Matrix.permanent`. -/
noncomputable def perm2 : R := blockPadded.permanent

/-- The padded permanent `x₀₀ · perm₂`: degree three, so that it is comparable with the generic
determinant at all.  The padding factor carries no complexity content; it homogenises degree two
into degree three, and it is a receiver coordinate rather than a feature of the permanent. -/
noncomputable def padded : R := x 0 0 * perm2

/-- The scaled matrix: the four off-block entries carry `e`, and one entry carries the sign. -/
noncomputable def M (e : R) : Matrix (Fin 3) (Fin 3) R :=
  !![x 0 0, e * x 0 1, e * x 0 2; e * x 1 0, x 1 1, -(x 1 2); e * x 2 0, x 2 1, x 2 2]

/-- The block whose **permanent** is the remainder's first summand: rows one and two, columns zero
and two. -/
noncomputable def blockPermanentHand : Matrix (Fin 2) (Fin 2) R := !![x 1 0, x 1 2; x 2 0, x 2 2]

/-- The block whose **determinant** is the remainder's second summand: rows one and two, columns
zero and one. -/
noncomputable def blockDeterminantHand : Matrix (Fin 2) (Fin 2) R := !![x 1 0, x 1 1; x 2 0, x 2 1]

/-- **The exhibited remainder**, retained as a population of two summands with their hands rather
than netted into one magnitude: an unsigned pairing against `x₀₁`, an alternating pairing against
`x₀₂`. -/
noncomputable def remainder : R :=
  -(x 0 1) * blockPermanentHand.permanent + x 0 2 * blockDeterminantHand.det

/-- **The two-by-two permanent is the unsigned pairing.**  mathlib defines `Matrix.permanent` as a
sum over permutations and carries no two-by-two closed form, so one is proved here by enumerating
the two permutations of a two-element type. -/
theorem theTwoByTwoPermanentIsTheUnsignedPairing (m : Matrix (Fin 2) (Fin 2) R) :
    m.permanent = m 0 0 * m 1 1 + m 0 1 * m 1 0 := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Matrix.permanent, hu, Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-! ## 1. The degeneration, its declared family, and the remainder's two hands -/

/-- **The degeneration.**  `det M(e) = x₀₀ · perm₂ + e² · R`, exactly, over the polynomial ring —
so `e` may be any ring element, an indeterminate included.  Two things are visible in the shape of
the right-hand side and are the point of stating it this way: the `e⁰` term is *exactly* the padded
permanent, and there is **no `e¹` term** — the expansion jumps to the square.

This is a decidable computation and cannot fail; it carries no evidential weight and is stated as a
check.  Its content is that the border point is reached along a written-down path. -/
theorem theScaledDeterminantIsThePaddedPermanentPlusASquaredRemainder (e : R) :
    (M e).det = padded + e ^ 2 * remainder := by
  simp [M, Matrix.det_fin_three, padded, perm2, blockPadded, remainder,
    theTwoByTwoPermanentIsTheUnsignedPairing, blockPermanentHand, blockDeterminantHand,
    Matrix.det_fin_two]
  ring

/-- The weights of the declared one-parameter subgroup, read off the slot:
`(1, e, e, e, 1, −1, e, 1, 1)`. -/
noncomputable def weight (e : ℚ) (s : Slot) : ℚ :=
  !![(1 : ℚ), e, e; e, 1, -1; e, 1, 1] s.1 s.2

/-- The declared scaling family as a nine-by-nine matrix on the variables. -/
noncomputable def scalingMatrix (e : ℚ) : Matrix Slot Slot ℚ := Matrix.diagonal (weight e)

/-- The declared scaling family as a substitution of the variables. -/
noncomputable def scaling (e : ℚ) : R →ₐ[ℚ] R := aeval (fun s => C (weight e s) * X s)

/-- **The substitution is that matrix acting.**  Without this the scaled matrix is an ad-hoc
expression; with it, the degeneration is a genuine linear change of variables and the determinant
below is a statement about that change of variables. -/
theorem theSubstitutionIsTheScalingMatrixActing (e : ℚ) (s : Slot) :
    ∑ t : Slot, C (scalingMatrix e s t) * X t = C (weight e s) * X s := by
  rw [Finset.sum_eq_single s]
  · simp [scalingMatrix]
  · intro t _ hts
    simp [scalingMatrix, Ne.symm hts]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- **The scaling family's determinant is `−e⁴`.**  Four variables carry `e`, one carries the sign,
four stand.  A decidable computation, stated as a check. -/
theorem theScalingMatrixDeterminantIsTheNegatedFourthPower (e : ℚ) :
    (scalingMatrix e).det = -e ^ 4 := by
  simp [scalingMatrix, Matrix.det_diagonal, Fintype.prod_prod_type, Fin.prod_univ_three, weight]
  ring

/-- **Away from the limit the family is invertible** — so every point of the curve except the
endpoint is in the orbit, by an exhibited substitution rather than by assertion. -/
theorem theScalingFamilyIsInvertibleAwayFromTheLimit (e : ℚ) (he : e ≠ 0) :
    IsUnit (scalingMatrix e).det := by
  rw [theScalingMatrixDeterminantIsTheNegatedFourthPower]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (pow_ne_zero 4 he))

/-- **At the limit the family is singular** — which is precisely why the endpoint is a *border*
point and not an orbit point.  The word `border` is load-bearing and this is the line that carries
the load. -/
theorem theScalingFamilyIsSingularAtTheLimit : (scalingMatrix 0).det = 0 := by
  rw [theScalingMatrixDeterminantIsTheNegatedFourthPower]
  norm_num

/-- **The scaled determinant is the substituted determinant** — the bridge from the substitution to
the matrix, so that the degeneration above reads as the determinant composed with the family. -/
theorem theScaledDeterminantIsTheSubstitutedDeterminant (e : ℚ) :
    scaling e det3 = (M (C e)).det := by
  simp [scaling, det3, gen, M, Matrix.det_fin_three, x, weight]

/-- **The remainder carries both hands, written out.**  A definitional unfolding; it names the two
summands rather than proving anything about them. -/
theorem theRemainderCarriesBothHands :
    remainder = -(x 0 1) * (x 1 0 * x 2 2 + x 1 2 * x 2 0)
      + x 0 2 * (x 1 0 * x 2 1 - x 1 1 * x 2 0) := by
  simp [remainder, theTwoByTwoPermanentIsTheUnsignedPairing, blockPermanentHand,
    blockDeterminantHand, Matrix.det_fin_two]

/-- The probe that separates the two hands: the two anti-diagonal entries of the block, and nothing
else. -/
noncomputable def handProbe : Slot → ℚ := fun t => !![0, 0, 0; 0, 0, 1; 1, 0, 0] t.1 t.2

/-- **The two hands separate at the probe**, `+1` against `−1`, on one and the same block. -/
theorem theTwoHandsSeparateAtTheProbe :
    eval handProbe blockPermanentHand.permanent = 1 ∧
      eval handProbe blockPermanentHand.det = -1 := by
  constructor <;>
    simp [handProbe, theTwoByTwoPermanentIsTheUnsignedPairing, blockPermanentHand,
      Matrix.det_fin_two, x]

/-- **The two hands are not one reading.**  This can fail and does not: netting the remainder's
permanent-hand summand against its determinant-hand summand would delete a difference a rational
probe already sees. -/
theorem theTwoHandsAreNotOneReading :
    blockPermanentHand.permanent ≠ blockPermanentHand.det := by
  intro h
  have hp := congrArg (eval handProbe) h
  rw [theTwoHandsSeparateAtTheProbe.1, theTwoHandsSeparateAtTheProbe.2] at hp
  norm_num at hp

/-! ## 2. The annihilator, and the separation it would give -/

/-- A direction in the nine variables. -/
abbrev Direction : Type := Slot → ℚ

/-- `v` **annihilates** `f` when the directional derivative of `f` along `v` vanishes: the
essential-variable reading, stated as a first-order condition rather than as a count of names. -/
noncomputable def Annihilates (v : Direction) (f : R) : Prop :=
  ∑ s : Slot, C (v s) * pderiv s f = 0

/-- The nine complementary two-by-two minors, signed. -/
noncomputable def cofactorMatrix : Matrix (Fin 3) (Fin 3) R :=
  !![x 1 1 * x 2 2 - x 1 2 * x 2 1, x 1 2 * x 2 0 - x 1 0 * x 2 2, x 1 0 * x 2 1 - x 1 1 * x 2 0;
     x 0 2 * x 2 1 - x 0 1 * x 2 2, x 0 0 * x 2 2 - x 0 2 * x 2 0, x 0 1 * x 2 0 - x 0 0 * x 2 1;
     x 0 1 * x 1 2 - x 0 2 * x 1 1, x 0 2 * x 1 0 - x 0 0 * x 1 2, x 0 0 * x 1 1 - x 0 1 * x 1 0]

/-- **The nine first partials of the determinant are the nine complementary minors.**  A
degree-two monomial in the minor at `(i,j)` uses exactly the two rows other than `i` and the two
columns other than `j`, so it determines `i` and `j`: the nine supports are pairwise disjoint, and
that disjointness is what the next theorem spends. -/
theorem theDerivativesOfTheDeterminantAreTheComplementaryMinors (s : Slot) :
    pderiv s det3 = cofactorMatrix s.1 s.2 := by
  obtain ⟨i, j⟩ := s
  fin_cases i <;> fin_cases j <;>
    simp [det3, gen, Matrix.det_fin_three, x, cofactorMatrix, Prod.ext_iff] <;>
    ring

/-- **The padded permanent is annihilated by every direction on the four slots it never mentions.**
`x₀₁, x₀₂, x₁₀, x₂₀` do not occur in `x₀₀ · perm₂`, so their partials vanish outright — a
four-dimensional space of blind directions. -/
theorem thePaddedPermanentIsAnnihilatedByTheFourAbsentSlots (v : Direction)
    (h : ∀ s, v s ≠ 0 → s = (0, 1) ∨ s = (0, 2) ∨ s = (1, 0) ∨ s = (2, 0)) :
    Annihilates v padded := by
  refine Finset.sum_eq_zero fun s _ => ?_
  rcases eq_or_ne (v s) 0 with hv | hv
  · simp [hv]
  · rcases h s hv with rfl | rfl | rfl | rfl <;>
      simp [padded, perm2, blockPadded, theTwoByTwoPermanentIsTheUnsignedPairing, x, Prod.ext_iff]

/-- **The determinant is annihilated only by the zero direction.**  Nine exhibited rational probes,
one per slot, each the partial identity on the complementary two-by-two block: at the probe for
`(i,j)` every minor but the `(i,j)`-th evaluates to zero, so the equation reads off that one
coefficient alone.  No linear algebra is invoked; the disjointness of the nine supports does the
work. -/
theorem theDeterminantIsAnnihilatedOnlyByTheZeroDirection (v : Direction)
    (h : Annihilates v det3) : v = 0 := by
  have key : ∀ p : Slot → ℚ, ∑ s : Slot, v s * eval p (cofactorMatrix s.1 s.2) = 0 := by
    intro p
    have hp := congrArg (eval p) h
    simpa [Annihilates, theDerivativesOfTheDeterminantAreTheComplementaryMinors] using hp
  funext s
  simp only [Pi.zero_apply]
  obtain ⟨i, j⟩ := s
  fin_cases i <;> fin_cases j
  · have hk := key (fun t => !![0, 0, 0; 0, 1, 0; 0, 0, 1] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![0, 0, 0; 1, 0, 0; 0, 0, 1] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![0, 0, 0; 1, 0, 0; 0, 1, 0] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![0, 1, 0; 0, 0, 0; 0, 0, 1] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![1, 0, 0; 0, 0, 0; 0, 0, 1] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![1, 0, 0; 0, 0, 0; 0, 1, 0] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![0, 1, 0; 0, 0, 1; 0, 0, 0] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![1, 0, 0; 0, 0, 1; 0, 0, 0] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk
  · have hk := key (fun t => !![1, 0, 0; 0, 1, 0; 0, 0, 0] t.1 t.2)
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, cofactorMatrix, x] at hk
    simpa using hk

/-- One coordinate direction: the slot `x₀₁`, which the padded permanent does not mention. -/
noncomputable def absentSlot : Direction :=
  fun t => if t = ((0 : Fin 3), (1 : Fin 3)) then 1 else 0

/-- **The padded permanent is blind along that direction.** -/
theorem thePaddedPermanentIsBlindAlongTheAbsentSlot : Annihilates absentSlot padded := by
  refine thePaddedPermanentIsAnnihilatedByTheFourAbsentSlots _ fun s hs => ?_
  by_cases hc : s = ((0 : Fin 3), (1 : Fin 3))
  · exact Or.inl hc
  · simp [absentSlot, hc] at hs

/-- **The determinant is not.**  This is the control that makes the pair of annihilator statements
a separation rather than a bookkeeping exercise: one nonzero direction, blind for one object and
not for the other, both facts proved and neither declared. -/
theorem theDeterminantIsNotBlindAlongTheAbsentSlot : ¬ Annihilates absentSlot det3 := by
  intro h
  have hz := congrFun (theDeterminantIsAnnihilatedOnlyByTheZeroDirection _ h)
    ((0 : Fin 3), (1 : Fin 3))
  simp [absentSlot] at hz

/-- A linear change of variables, as a substitution. -/
noncomputable def substitute (A : Matrix Slot Slot ℚ) : R →ₐ[ℚ] R :=
  aeval (fun s => ∑ t : Slot, C (A s t) * X t)

/-- **Named open.**  No invertible linear substitution carries the generic determinant to the
padded permanent — the orbit half of "the border strictly exceeds the orbit here".  Classically
true and elementary; it is not proved in this file, and the reduction below says exactly what is
missing. -/
def TheOrbitDoesNotCarryThePaddedPermanent : Prop :=
  ∀ A : Matrix Slot Slot ℚ, IsUnit A.det → substitute A det3 ≠ padded

/-- **Named open, and it is the only gap.**  Blindness transports along an invertible substitution:
if `w` annihilates the substituted form then the transported direction annihilates the original.
This is the chain rule for a linear substitution together with the injectivity an invertible
substitution supplies.  Classical and elementary; stated as a hypothesis because it is not carried
here. -/
def BlindnessTransportsAlongTheSubstitution : Prop :=
  ∀ A : Matrix Slot Slot ℚ, IsUnit A.det → ∀ (w : Direction) (f : R),
    Annihilates w (substitute A f) → Annihilates (fun s => ∑ t : Slot, A s t * w t) f

/-- **The separation follows from blindness transport.**  Granted the transport, the two
annihilator computations close the orbit question: the direction that blinds the padded permanent
transports to a direction that blinds the determinant, hence to the zero direction, hence the
substituting matrix's `(0,1)`-column vanishes, hence so does its determinant — contradicting
invertibility.

This is the load the two annihilator theorems carry, and it is stated as an implication so the open
half is visible rather than hidden inside a proof. -/
theorem theSeparationFollowsFromBlindnessTransport
    (htrans : BlindnessTransportsAlongTheSubstitution) :
    TheOrbitDoesNotCarryThePaddedPermanent := by
  intro A hA hEq
  have hpad : Annihilates absentSlot (substitute A det3) := by
    rw [hEq]; exact thePaddedPermanentIsBlindAlongTheAbsentSlot
  have hdet := theDeterminantIsAnnihilatedOnlyByTheZeroDirection _
    (htrans A hA absentSlot det3 hpad)
  have hcol : ∀ s : Slot, A s ((0 : Fin 3), (1 : Fin 3)) = 0 := by
    intro s
    have hs := congrFun hdet s
    simpa [absentSlot] using hs
  exact (isUnit_iff_ne_zero.mp hA) (Matrix.det_eq_zero_of_column_eq_zero _ hcol)

/-! ## 3. The blind reading, as a witness for the aperture theorem -/

/-- What the declared family reaches at parameter `e`. -/
noncomputable def alongTheFamily (e : ℚ) : R := padded + (e ^ 2) • remainder

/-- **The family is the scaled determinant.**  A definitional bridge between the substitution and
the affine line the degeneration traces. -/
theorem theFamilyIsTheScaledDeterminant (e : ℚ) : scaling e det3 = alongTheFamily e := by
  rw [theScaledDeterminantIsTheSubstitutedDeterminant,
    theScaledDeterminantIsThePaddedPermanentPlusASquaredRemainder, alongTheFamily,
    ← C_pow, C_mul']

/-- **The limit of the family is the padded permanent** — the endpoint, reached by the substitution
that `theScalingFamilyIsSingularAtTheLimit` shows is not invertible.  A definitional consequence of
the two theorems above. -/
theorem theLimitOfTheFamilyIsThePaddedPermanent : scaling 0 det3 = padded := by
  rw [theFamilyIsTheScaledDeterminant]
  simp [alongTheFamily]

/-- Membership on the punctured family: reached at some nonzero parameter. -/
def OnTheFamily (f : R) : Prop := ∃ e : ℚ, e ≠ 0 ∧ f = alongTheFamily e

/-- The probe at which the remainder is nonzero: `x₀₁, x₁₀, x₂₂` at one, everything else at
zero. -/
noncomputable def familyProbe : Slot → ℚ := fun t => !![0, 1, 0; 1, 0, 0; 0, 0, 1] t.1 t.2

/-- **The remainder is not zero** — exhibited at a rational probe, where it evaluates to `−1`.
Without this the family below would be a point and the blindness would be vacuous. -/
theorem theRemainderIsNotZero : remainder ≠ 0 := by
  intro h
  have hp := congrArg (eval familyProbe) h
  simp [familyProbe, remainder, theTwoByTwoPermanentIsTheUnsignedPairing, blockPermanentHand,
    blockDeterminantHand, Matrix.det_fin_two, x] at hp

/-- **The limit point is not on the punctured family.**  So the property `OnTheFamily` genuinely
distinguishes the pair that the readings below cannot separate. -/
theorem thePaddedPermanentIsNotOnTheFamily : ¬ OnTheFamily padded := by
  rintro ⟨e, he, hEq⟩
  rw [alongTheFamily] at hEq
  have hz : (e ^ 2) • remainder = (0 : R) := by
    refine add_left_cancel (a := padded) ?_
    rw [add_zero]
    exact hEq.symm
  rcases smul_eq_zero.mp hz with h | h
  · exact pow_ne_zero 2 he h
  · exact theRemainderIsNotZero h

/-- The declared receiver family: the linear readings of a form that vanish along the punctured
family.  This is the degree-one part of the coordinate ring, restricted to the ideal of the curve —
narrower than the full polynomial family, and stated at that width rather than at the width the
argument would prefer. -/
noncomputable def familyAnnihilatingReadings : Lines.ReceiverFamily R ℚ where
  Index := { ρ : R →ₗ[ℚ] ℚ // ∀ f, OnTheFamily f → ρ f = 0 }
  read := fun ρ f => ρ.1 f

/-- **A linear reading that vanishes along the punctured family vanishes at the limit.**  Two
rational parameters do it: the reading is affine in `e²`, so killing it at `e = 1` and `e = 2` kills
both coefficients.  No limit, no topology and no infinite-root argument — two evaluations over
`ℚ`. -/
theorem theVanishingLinearReadingVanishesAtTheLimit (ρ : R →ₗ[ℚ] ℚ)
    (h : ∀ e : ℚ, e ≠ 0 → ρ (alongTheFamily e) = 0) : ρ padded = 0 := by
  have h1 := h 1 one_ne_zero
  have h2 := h 2 two_ne_zero
  simp only [alongTheFamily, map_add, map_smul, smul_eq_mul] at h1 h2
  norm_num at h1 h2
  linarith

/-- **The declared family is blind to membership on the family.**  The pair is the curve at
parameter one against the limit point; every reading in the family kills both, and the property
separates them.  This is the Lean content of the fourth item: `Lines.ReceiverFamily.Blind` on a real
algebraic object rather than on the residue-modulo-two toy. -/
theorem theFamilyAnnihilatingReadingsAreBlindToTheFamily :
    familyAnnihilatingReadings.Blind OnTheFamily := by
  refine ⟨alongTheFamily 1, padded, ⟨1, one_ne_zero, rfl⟩, thePaddedPermanentIsNotOnTheFamily,
    fun ρ => ?_⟩
  have hA : ρ.1 (alongTheFamily 1) = 0 := ρ.2 _ ⟨1, one_ne_zero, rfl⟩
  have hB : ρ.1 padded = 0 :=
    theVanishingLinearReadingVanishesAtTheLimit ρ.1 fun e he => ρ.2 _ ⟨e, he, rfl⟩
  simp [familyAnnihilatingReadings, hA, hB]

/-- **Therefore those readings carry no verdict about the family.**
`Lines.blindFamilyCarriesNoVerdict` applied verbatim: no function whatsoever of the vanishing linear
readings decides membership.  This is not a difficulty result and it is not news about geometric
complexity theory — it is the reason that programme is posed on closures, arriving here as a
discharged Lean statement. -/
theorem theFamilyAnnihilatingReadingsCarryNoVerdictAboutTheFamily :
    ¬ ∃ verdict : (familyAnnihilatingReadings.Index → ℚ) → Prop,
        ∀ f : R, OnTheFamily f ↔ verdict (fun i => familyAnnihilatingReadings.read i f) :=
  familyAnnihilatingReadings.blindFamilyCarriesNoVerdict _
    theFamilyAnnihilatingReadingsAreBlindToTheFamily

/-- One reading, exhibited by name: evaluation at the origin, which reads off the constant
coefficient of a form. -/
noncomputable def constantReading : R →ₗ[ℚ] ℚ :=
  (aeval (fun _ : Slot => (0 : ℚ)) : R →ₐ[ℚ] ℚ).toLinearMap

/-- **The declared family is not blind by being empty.**  The origin reading vanishes on the whole
punctured family and is not the zero functional — it returns one at one.  A blind family with no
readings in it would prove nothing at all, so the witness is required rather than decorative. -/
theorem theConstantReadingIsADeclaredNonzeroReading :
    (∀ f, OnTheFamily f → constantReading f = 0) ∧ constantReading ≠ 0 := by
  constructor
  · rintro f ⟨e, -, rfl⟩
    simp [constantReading, alongTheFamily, padded, perm2, blockPadded, remainder,
      theTwoByTwoPermanentIsTheUnsignedPairing, blockPermanentHand, blockDeterminantHand,
      Matrix.det_fin_two, x]
  · intro h
    have h1 : constantReading (1 : R) = 0 := by rw [h]; rfl
    simp [constantReading] at h1

end Soma.Holonics.Millennium.Border
