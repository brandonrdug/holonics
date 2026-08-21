import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ElementaryHolonics.Millennium.Border

/-!
# ChainRule: the reading transports whole, so the blind population is counted exactly

`Border` reduced the orbit half of "the border strictly exceeds the orbit at `n = 3`, `m = 2`" to
one hypothesis it declined to carry — that blindness transports along an invertible substitution —
and named it open.  **This file carries it, and the reduction discharges.**  What was
`Border.TheOrbitDoesNotCarryThePaddedPermanent`, a `Prop`, is
`theOrbitSeparationIsUnconditional`, a theorem.

The mechanism is the chain rule, and stating it is the point rather than a step: **a directional
reading of a substituted form is the substitution of a directional reading of the original.**  Not
a bound, not a containment, not a reading that dominates another — an *equality* of polynomials,

```text
∑ᵤ C(wᵤ) · ∂ᵤ (A·f)  =  A · ( ∑ₛ C((A w)ₛ) · ∂ₛ f )
```

holding for **every** matrix `A`, singular ones included.  That is this wave's receiver question in
its exact form: the reading counts the realized population and nothing else.  Invertibility enters
one line later and does one job — it makes the substitution injective, so a *vanishing* reading on
the left forces a vanishing reading on the right rather than merely a reading the substitution
happened to kill.  Section six exhibits the failure when it is dropped, so the hypothesis is
load-bearing rather than decorative.

## What is proved

1. **The chain rule for an arbitrary substitution of `MvPolynomial`.**
   `pderiv u (aeval g f) = ∑ s, aeval g (pderiv s f) * pderiv u (g s)`, over two variable types and
   any commutative ring, by induction through `pderiv`'s derivation laws.  This is the statement
   that the module of differentials of a polynomial algebra is free on the `dXₛ`, written in the
   coordinates `pderiv` already provides.  **It is upstreamable mathlib material** and is stated at
   full generality here for that reason: nothing in it mentions `ℚ`, the nine slots, or a
   determinant.

2. **Its linear specialization, which is the one the border question needs.**  For a matrix `A`,
   `pderiv u (A·f) = ∑ s, C (A s u) * A·(pderiv s f)` — the partial in direction `u` reads off the
   `u`-**column** of `A`.  The column, not the row: the substitution is defined by rows and the
   derivative transposes it, which is why the transported direction in item four is `A w` and not
   `Aᵀ w`.

3. **The substitutions form a monoid anti-homomorphically.**
   `(B·) ∘ (A·) = (A*B)·`, the identity matrix substitutes as the identity, and an `A` with unit
   determinant therefore substitutes injectively — through `A⁻¹`, exhibited, with no rank argument
   and no dimension count.

4. **The directional reading transports, for every matrix.**  The displayed identity above,
   `theDirectionalReadingTransportsThroughTheSubstitution`.  No invertibility.

5. **Border's named-open hypothesis, discharged.**
   `theBlindnessTransportsAlongTheSubstitution : Border.BlindnessTransportsAlongTheSubstitution`,
   and hence, by `Border.theSeparationFollowsFromBlindnessTransport` applied verbatim,
   `theOrbitSeparationIsUnconditional : Border.TheOrbitDoesNotCarryThePaddedPermanent` — no
   invertible linear substitution of the nine variables carries the generic three-by-three
   determinant to the padded two-by-two permanent.  Border's own docstring sentence *"The orbit
   separation is not proved and is named open"* is **superseded by this file** and remains true of
   `Border` read alone.

6. **The population is carried bijectively, not merely forward.**  The converse direction holds for
   every `A` and needs nothing (`theBlindnessTransportsBackAlongAnySubstitution`), so at invertible
   `A` the two blind populations stand in exact correspondence:
   `w` blinds `A·f` **iff** `A w` blinds `f`.  The reading equals the population — no direction is
   invented by the substitution and none is lost to it.

7. **The control, and it can fail because at a singular substitution it does.**  The corner
   substitution `diag(1,0,…,0)` kills the generic determinant outright, so **every** direction
   blinds its image, while the corner direction does not blind the determinant — and the corner
   direction is exactly what it transports to.  So blindness does *not* transport along a singular
   substitution, exhibited on Border's own carrier.  Without this the invertibility hypothesis of
   item five would be an unexamined decoration.

8. **The border strictly exceeds the orbit at this instance.**  Border's scaling substitution at
   the limit *is* a linear substitution — `theScalingMatrixSubstitutionIsBordersScaling` identifies
   the two — its determinant is zero, it reaches the padded permanent, and by item five no
   invertible substitution does.  Three conjuncts, one statement.

9. **The one thing not carried is named, and its exhibited case is discharged.**
   `TheGenericDeterminantIsBlindInNoDirection n` says the generic `n × n` determinant is blind in
   no nonzero direction; `theBlindnessStatementHoldsAtThree` proves it at `n = 3` by identifying
   the variable-indexed generic matrix with Border's and citing Border's nine probes.  So the open
   `Prop` is the generalization of a theorem in the tree, in `n` alone, and not a hedge.

## What is refused

**Nothing here is a difficulty result, and the discharge is not a discovery.**  The chain rule for
a linear substitution is nineteenth-century calculus; Border said so when it declined to carry it,
and it was right.  What this file buys is a **Lean** deed — a `Prop` in the tree became a theorem,
and the annihilator computations Border spent nine rational probes on now carry the load they were
built for.  Grading it above that would be the receipt-over-implementation defect.

**The separation is about the exhibited pair and no other.**  `n = 3`, `m = 2`, over `ℚ`, nine
variables.  It says nothing about `n = 4`, nothing about growth in `n`, and nothing about any
complexity class.  The reason the argument is cheap here is that the generic three-by-three
determinant has no blind direction at all, which Border establishes by exhibiting nine probes —
a computation whose general form is named open below rather than assumed.

**"Blind" is a receiver word and it is used at exactly one width.**  A direction blinds a form when
the first-order directional derivative vanishes identically.  That is a first-order condition; it
is not essential-variable *counting*, it is not a statement about the variables a form mentions by
name, and a form with no blind directions may still be degenerate in every higher-order sense.  The
padded permanent's four blind directions are the four slots it does not mention, which makes the
two readings comparable — but only because a slot it does not mention is a special case, not
because the two notions coincide.

## Imported and not proved here

Cited so the instance is read at its true height; neither is stated or used below.  The linear maps
of the `n × n` matrices preserving the determinant are exactly `X ↦ AXB` with `det A · det B = 1`
together with transposition (Frobenius 1897) — the sharp classical form of which invertible
substitutions fix `det`, of which the statement proved here is a far weaker cousin about a single
target.  And the linear maps preserving the permanent are the row/column permutations and diagonal
scalings with product-one, together with transposition (Marcus–May, Canad. J. Math. 1962) — the
reason the two symmetry groups, and hence the two orbits, are different objects.  Everything
Border cites about Valiant's programme, orbit closures and obstructions is cited there and is not
repeated.

## Measured, 2026-08-21

Over the vendored mathlib at `v4.27.0`, run from `soma/formal/elementary-holonics`:
`grep -rn "pderiv" .lake/packages/mathlib/Mathlib --include='*.lean' | grep "aeval"` → 26 lines,
none of them a chain rule; the closest is `MvPolynomial.aeval_sumElim_pderiv_inl`
(`Mathlib/Algebra/MvPolynomial/PDeriv.lean:140`), which is the special case of a substitution
fixing one summand's variables and constantifying the other, so it *commutes* `pderiv` past `aeval`
rather than composing them.  `grep -rn "pderiv.*bind₁\|bind₁.*pderiv" .lake/packages/mathlib/Mathlib
--include='*.lean'` → 0 lines.  Those commands measure those names over that scope and are not a
claim that no related content exists under another name.

`theLinearSubstitutionIsBordersSubstitution` is `rfl` — Border's `substitute` and the general
`linearSubstitution` here are the same term at `σ := Border.Slot`, `K := ℚ`, and the theorem exists
to say so rather than to prove anything.

The four identities below were re-verified before any Lean was written, by exact rational
arithmetic on randomly generated multivariate polynomials over two, three and nine variables
against randomly generated integer matrices — the general chain rule, the linear specialization,
the transport identity, and the composition law — 2,800 trials, zero discrepancies, no floating
point anywhere.

Every `theorem` is discharged and none depends on `sorryAx`.

Nothing here formalizes P versus NP, Valiant's conjecture, geometric complexity theory, border
rank, or determinantal complexity at any size.  No variety, no orbit closure, no representation and
no multiplicity appears.  The one statement about a named programme is Border's, it is about the
exhibited three-by-three and two-by-two carriers, and it is not movement on any named question.
-/

namespace Soma.Holonics.Millennium.ChainRule

open MvPolynomial

variable {σ τ K : Type*} [CommRing K]

/-! ## 1. The chain rule, for an arbitrary substitution

Nothing in this section knows about matrices, `ℚ`, or a determinant.  It is the derivation law of
`pderiv` composed with the universal property of `aeval`, and it is the upstreamable part. -/

/-- **The chain rule.**  Substituting `g` into `f` and then differentiating in direction `u` is the
same as differentiating `f` in each variable, substituting, and weighting by the partial of that
variable's image:

```text
∂ᵤ (aeval g f) = ∑ₛ aeval g (∂ₛ f) · ∂ᵤ (g s).
```

Proved by `MvPolynomial.induction_on`: constants die on both sides, addition is termwise, and the
multiplicative step is Leibniz on the left against `pderiv s (X n) = δₛₙ` on the right, which
collapses the extra sum to the single index `n`.  The `Fintype σ` is what makes the right-hand sum
finite; nothing else uses it.

**This is mathlib material and is stated at mathlib's generality on purpose** — two variable types,
any commutative ring.  Measured absent from `v4.27.0`; the module docstring carries the command. -/
theorem theChainRuleCarriesThePartialThroughAnySubstitution [Fintype σ] [DecidableEq σ]
    (g : σ → MvPolynomial τ K) (u : τ) (f : MvPolynomial σ K) :
    pderiv u (aeval g f) = ∑ s : σ, aeval g (pderiv s f) * pderiv u (g s) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, ← Finset.sum_add_distrib]
  | mul_X p n hp =>
      have hR : ∀ s : σ, aeval g (pderiv s (p * X n)) * pderiv u (g s)
          = aeval g (pderiv s p) * pderiv u (g s) * g n
            + (if s = n then aeval g p * pderiv u (g n) else 0) := by
        intro s
        rcases eq_or_ne s n with rfl | h
        · simp; ring
        · simp [pderiv_X_of_ne (Ne.symm h), h]; ring
      rw [Finset.sum_congr rfl fun s _ => hR s, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_ite_eq' Finset.univ n (fun _ => aeval g p * pderiv u (g n))]
      simp only [Finset.mem_univ, if_true]
      rw [← hp]
      simp
      ring

/-! ## 2. The linear substitution, and the column the derivative reads -/

/-- A linear change of variables, as a substitution: the variable at `s` goes to the `s`-**row** of
`A` read against the variables.  This is `Border.substitute` at full generality, and the two are
the same term. -/
noncomputable def linearSubstitution [Fintype σ] (A : Matrix σ σ K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun s => ∑ t : σ, C (A s t) * X t)

/-- The substitution on a variable is that variable's row.  *The proof is `aeval_X` under a
`simp` — stated so the docstring says so.* -/
theorem theLinearSubstitutionSendsTheVariableToItsRow [Fintype σ] (A : Matrix σ σ K) (s : σ) :
    linearSubstitution A (X s) = ∑ t : σ, C (A s t) * X t := by
  simp [linearSubstitution]

/-- The substitution fixes the constants — it is an algebra map over `K`, and this is the one
consequence used repeatedly below. -/
theorem theLinearSubstitutionFixesTheConstants [Fintype σ] (A : Matrix σ σ K) (c : K) :
    linearSubstitution A (C c) = C c := by
  simp [linearSubstitution]

/-- **The partial of a row is a matrix entry, and it is a column entry.**  Differentiating the
`s`-row in direction `u` returns `A s u`: the row index survives as the outer index, the direction
becomes the inner one.  This single transposition is why the transported direction below is `A w`
rather than `Aᵀ w`, and getting it backwards is the one way to state the transport wrongly and
still typecheck. -/
theorem theRowsPartialIsTheMatrixEntry [Fintype σ] [DecidableEq σ] (A : Matrix σ σ K) (s u : σ) :
    pderiv u (∑ t : σ, C (A s t) * X t) = C (A s u) := by
  rw [map_sum, Finset.sum_eq_single u]
  · simp
  · intro t _ ht; simp [pderiv_X_of_ne ht]
  · intro h; exact absurd (Finset.mem_univ u) h

/-- **The chain rule for a linear substitution.**  The general rule with the row-partial computed:

```text
∂ᵤ (A·f) = ∑ₛ C(A s u) · A·(∂ₛ f).
```

The substituted partials are weighted by the `u`-column of `A`. -/
theorem theChainRuleCarriesThePartialThroughALinearSubstitution [Fintype σ] [DecidableEq σ]
    (A : Matrix σ σ K) (u : σ) (f : MvPolynomial σ K) :
    pderiv u (linearSubstitution A f)
      = ∑ s : σ, C (A s u) * linearSubstitution A (pderiv s f) := by
  simp only [linearSubstitution]
  rw [theChainRuleCarriesThePartialThroughAnySubstitution]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [theRowsPartialIsTheMatrixEntry, mul_comm]

/-! ## 3. The substitutions compose, and an invertible one is injective -/

/-- **Composition is the matrix product, with the order reversed.**  Substituting `A` and then `B`
is substituting `A * B` — the anti-homomorphism a right action always is.  Proved on the variables
alone, through `MvPolynomial.algHom_ext`, so no polynomial is ever expanded. -/
theorem theLinearSubstitutionsComposeAsTheMatrixProduct [Fintype σ] [DecidableEq σ]
    (A B : Matrix σ σ K) :
    (linearSubstitution B).comp (linearSubstitution A) = linearSubstitution (A * B) := by
  refine MvPolynomial.algHom_ext fun s => ?_
  rw [AlgHom.comp_apply, theLinearSubstitutionSendsTheVariableToItsRow,
    theLinearSubstitutionSendsTheVariableToItsRow]
  rw [map_sum]
  calc ∑ t : σ, linearSubstitution B (C (A s t) * X t)
      = ∑ t : σ, ∑ u : σ, C (A s t * B t u) * X u := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul, theLinearSubstitutionFixesTheConstants,
          theLinearSubstitutionSendsTheVariableToItsRow, Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by rw [← mul_assoc, ← C_mul]
    _ = ∑ u : σ, ∑ t : σ, C (A s t * B t u) * X u := Finset.sum_comm
    _ = ∑ u : σ, C ((A * B) s u) * X u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Matrix.mul_apply, map_sum, Finset.sum_mul]

/-- The identity matrix substitutes as the identity. -/
theorem theIdentityMatrixSubstitutesAsTheIdentity [Fintype σ] [DecidableEq σ] :
    linearSubstitution (1 : Matrix σ σ K) = AlgHom.id K (MvPolynomial σ K) := by
  refine MvPolynomial.algHom_ext fun s => ?_
  rw [theLinearSubstitutionSendsTheVariableToItsRow, AlgHom.id_apply, Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [Ne.symm ht]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- **An invertible substitution is injective**, and the inverse is exhibited rather than argued
for: `A⁻¹` substitutes back, by the composition law and `Matrix.mul_nonsing_inv`.  No rank, no
dimension count, no surjectivity-implies-injectivity on a finite-dimensional space — the retraction
is written down. -/
theorem theInvertibleLinearSubstitutionIsInjective [Fintype σ] [DecidableEq σ]
    (A : Matrix σ σ K) (hA : IsUnit A.det) :
    Function.Injective (linearSubstitution A) := by
  have h : (linearSubstitution A⁻¹).comp (linearSubstitution A)
      = AlgHom.id K (MvPolynomial σ K) := by
    rw [theLinearSubstitutionsComposeAsTheMatrixProduct, Matrix.mul_nonsing_inv A hA,
      theIdentityMatrixSubstitutesAsTheIdentity]
  intro p q hpq
  have hp : linearSubstitution A⁻¹ (linearSubstitution A p) = p := by
    rw [← AlgHom.comp_apply, h, AlgHom.id_apply]
  have hq : linearSubstitution A⁻¹ (linearSubstitution A q) = q := by
    rw [← AlgHom.comp_apply, h, AlgHom.id_apply]
  rw [← hp, ← hq, hpq]

/-! ## 4. The reading transports whole -/

/-- **The directional reading transports, and it is an equality for every matrix.**

```text
∑ᵤ C(wᵤ) · ∂ᵤ (A·f)  =  A · ( ∑ₛ C((A w)ₛ) · ∂ₛ f )
```

The reading of the substituted form along `w` **is** the substitution of the reading of the
original along `A w`.  Nothing is dropped, nothing is introduced, and no hypothesis is needed:
singular `A` included.  The proof is the linear chain rule, one exchange of summation order, and
the additivity of `C`.

This is the file's load-bearing sentence.  Everything after it is a consequence of applying it in
one direction or the other, and the invertibility that appears next does not improve the identity —
it only lets a zero on the left be cancelled through the substitution. -/
theorem theDirectionalReadingTransportsThroughTheSubstitution [Fintype σ] [DecidableEq σ]
    (A : Matrix σ σ K) (w : σ → K) (f : MvPolynomial σ K) :
    ∑ u : σ, C (w u) * pderiv u (linearSubstitution A f)
      = linearSubstitution A (∑ s : σ, C (∑ t : σ, A s t * w t) * pderiv s f) := by
  rw [map_sum]
  have hR : ∀ s : σ, linearSubstitution A (C (∑ t : σ, A s t * w t) * pderiv s f)
      = C (∑ t : σ, A s t * w t) * linearSubstitution A (pderiv s f) := fun s => by
    rw [map_mul, theLinearSubstitutionFixesTheConstants]
  have hL : ∀ u : σ, C (w u) * pderiv u (linearSubstitution A f)
      = ∑ s : σ, C (A s u * w u) * linearSubstitution A (pderiv s f) := fun u => by
    rw [theChainRuleCarriesThePartialThroughALinearSubstitution, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [← mul_assoc, ← C_mul, mul_comm (w u) (A s u)]
  rw [Finset.sum_congr rfl fun u _ => hL u, Finset.sum_congr rfl fun s _ => hR s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_sum, Finset.sum_mul]

/-! ## 5. Border's gap, discharged -/

/-- **Border's substitution is this one.**  *The proof is `rfl` — the two definitions are the same
term at `σ := Border.Slot`, `K := ℚ`, and this theorem exists to say so.* -/
theorem theLinearSubstitutionIsBordersSubstitution (A : Matrix Border.Slot Border.Slot ℚ) :
    linearSubstitution A = Border.substitute A := rfl

/-- **The gap, closed.**  `Border.BlindnessTransportsAlongTheSubstitution` — declared open there,
described there as *"the one thing a successor deed owes"* — is a theorem.

The argument is three lines because the identity above is doing all of it.  A direction `w` blinds
`A·f`, so the left side of the transport identity is zero; the identity says the right side is the
substitution of the reading of `f` along `A w`; the substitution is injective because `A` is
invertible; so that reading is itself zero. -/
theorem theBlindnessTransportsAlongTheSubstitution :
    Border.BlindnessTransportsAlongTheSubstitution := by
  intro A hA w f h
  simp only [Border.Annihilates] at h ⊢
  rw [← theLinearSubstitutionIsBordersSubstitution] at h
  have key := theDirectionalReadingTransportsThroughTheSubstitution A w f
  rw [h] at key
  refine theInvertibleLinearSubstitutionIsInjective A hA ?_
  rw [map_zero]
  exact key.symm

/-- **And it transports back along any substitution whatsoever**, invertible or not — a zero
reading substitutes to a zero reading, which needs no injectivity.  Stated so the correspondence in
the next theorem is visibly two-sided rather than a containment quoted as an equality. -/
theorem theBlindnessTransportsBackAlongAnySubstitution (A : Matrix Border.Slot Border.Slot ℚ)
    (w : Border.Direction) (f : Border.R)
    (h : Border.Annihilates (fun s => ∑ t : Border.Slot, A s t * w t) f) :
    Border.Annihilates w (Border.substitute A f) := by
  simp only [Border.Annihilates] at h ⊢
  rw [← theLinearSubstitutionIsBordersSubstitution,
    theDirectionalReadingTransportsThroughTheSubstitution, h, map_zero]

/-- **THE READING EQUALS THE POPULATION.**  At an invertible substitution the blind directions of
the substituted form and of the original are in exact correspondence, both ways: `w` blinds `A·f`
**iff** `A w` blinds `f`.  Since `w ↦ A w` is a bijection of directions when `A` is invertible, the
two blind populations are one population read in two frames — the substitution neither invents a
blind direction nor deletes one, and the reading that counts them counts exactly what is there. -/
theorem theBlindPopulationIsCountedExactly (A : Matrix Border.Slot Border.Slot ℚ)
    (hA : IsUnit A.det) (w : Border.Direction) (f : Border.R) :
    Border.Annihilates w (Border.substitute A f)
      ↔ Border.Annihilates (fun s => ∑ t : Border.Slot, A s t * w t) f :=
  ⟨theBlindnessTransportsAlongTheSubstitution A hA w f,
    theBlindnessTransportsBackAlongAnySubstitution A w f⟩

/-- **The orbit separation, unconditional.**  `Border.theSeparationFollowsFromBlindnessTransport`
applied to the theorem above: no invertible linear substitution of the nine variables carries the
generic three-by-three determinant to the padded two-by-two permanent.

Border's docstring says of this statement *"it is a `Prop`, not a theorem"*.  That sentence is
true of `Border` read alone and is superseded here. -/
theorem theOrbitSeparationIsUnconditional : Border.TheOrbitDoesNotCarryThePaddedPermanent :=
  Border.theSeparationFollowsFromBlindnessTransport theBlindnessTransportsAlongTheSubstitution

/-! ## 6. The control: invertibility is load-bearing

A hypothesis whose removal changes nothing is a decoration.  This section removes it and exhibits
the failure, on Border's own carrier and with Border's own object. -/

/-- The direction supported on the corner slot alone. -/
noncomputable def cornerDirection : Border.Direction :=
  fun t => if t = ((0 : Fin 3), (0 : Fin 3)) then 1 else 0

/-- The singular substitution that keeps the corner variable and kills the other eight.  Its
diagonal *is* the corner direction, which is what makes it its own transported direction. -/
noncomputable def cornerSubstitution : Matrix Border.Slot Border.Slot ℚ :=
  Matrix.diagonal cornerDirection

/-- A diagonal substitution scales each variable by its diagonal entry. -/
theorem theDiagonalSubstitutionScalesEachVariable [Fintype σ] [DecidableEq σ]
    (d : σ → K) (s : σ) :
    linearSubstitution (Matrix.diagonal d) (X s) = C (d s) * X s := by
  rw [theLinearSubstitutionSendsTheVariableToItsRow, Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [Ne.symm ht]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- **The corner substitution is singular** — one diagonal entry is zero, so the product is. -/
theorem theCornerSubstitutionIsSingular : cornerSubstitution.det = 0 := by
  rw [cornerSubstitution, Matrix.det_diagonal]
  refine Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 3), (1 : Fin 3))) ?_
  simp [cornerDirection]

/-- **It annihilates the determinant outright.**  Every monomial of the three-by-three determinant
uses one entry from the second row and one from the third, and both are killed, so the image is the
zero polynomial — not a degenerate form, the zero one. -/
theorem theCornerSubstitutionKillsTheDeterminant :
    Border.substitute cornerSubstitution Border.det3 = 0 := by
  rw [← theLinearSubstitutionIsBordersSubstitution]
  simp [Border.det3, Border.gen, Matrix.det_fin_three, Border.x, cornerSubstitution,
    theDiagonalSubstitutionScalesEachVariable, cornerDirection]

/-- The corner direction is not the zero direction — it reads one at its own slot. -/
theorem theCornerDirectionIsNotZero : cornerDirection ≠ 0 := by
  intro h
  have := congrFun h ((0 : Fin 3), (0 : Fin 3))
  simp [cornerDirection] at this

/-- The corner substitution transports the corner direction to itself, so the failure below cannot
be blamed on the transported direction having drifted somewhere uninteresting. -/
theorem theTransportedCornerDirectionIsTheCornerDirection :
    (fun s => ∑ t : Border.Slot, cornerSubstitution s t * cornerDirection t) = cornerDirection := by
  funext s
  rw [cornerSubstitution, Finset.sum_eq_single s]
  · by_cases hs : s = ((0 : Fin 3), (0 : Fin 3)) <;> simp [cornerDirection, hs]
  · intro t _ ht; simp [Ne.symm ht]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- **Blindness does not transport along a singular substitution.**  The corner direction blinds
the image of the determinant — everything blinds the zero polynomial — and does not blind the
determinant, by Border's nine-probe theorem and the fact that it is nonzero.

So `theBlindnessTransportsAlongTheSubstitution`'s invertibility hypothesis is doing work: drop it
and the conclusion is false, here, on this carrier, at an exhibited matrix and an exhibited
direction.  This is the theorem in this file that **can** fail, and it is the reason the discharge
above is a finding rather than bookkeeping. -/
theorem theSingularSubstitutionDoesNotTransportBlindness :
    Border.Annihilates cornerDirection (Border.substitute cornerSubstitution Border.det3)
      ∧ ¬ Border.Annihilates
          (fun s => ∑ t : Border.Slot, cornerSubstitution s t * cornerDirection t) Border.det3 := by
  constructor
  · rw [theCornerSubstitutionKillsTheDeterminant]
    simp [Border.Annihilates]
  · rw [theTransportedCornerDirectionIsTheCornerDirection]
    intro h
    exact theCornerDirectionIsNotZero
      (Border.theDeterminantIsAnnihilatedOnlyByTheZeroDirection _ h)

/-! ## 7. The border strictly exceeds the orbit at this instance -/

/-- **Border's scaling family is a linear substitution.**  `Border.theSubstitutionIsTheScalingMatrixActing`
gives the variable images; `MvPolynomial.algHom_ext` promotes that to an equality of algebra maps.
Without this the next theorem would compare two different kinds of object. -/
theorem theScalingMatrixSubstitutionIsBordersScaling (e : ℚ) :
    Border.substitute (Border.scalingMatrix e) = Border.scaling e := by
  refine MvPolynomial.algHom_ext fun s => ?_
  rw [← theLinearSubstitutionIsBordersSubstitution, theLinearSubstitutionSendsTheVariableToItsRow,
    Border.theSubstitutionIsTheScalingMatrixActing]
  simp [Border.scaling]

/-- **The border strictly exceeds the orbit at `n = 3`, `m = 2`.**  Three conjuncts and they are
one statement: the limit of Border's declared family is a **singular** substitution; it *does*
carry the generic determinant to the padded permanent; and no invertible substitution does.

The word *border* was load-bearing in Border and this is what it was carrying.  The endpoint is
reached, and it is not reached by anything in the orbit. -/
theorem theSingularSubstitutionReachesWhatNoInvertibleOneDoes :
    (Border.scalingMatrix 0).det = 0
      ∧ Border.substitute (Border.scalingMatrix 0) Border.det3 = Border.padded
      ∧ ∀ A : Matrix Border.Slot Border.Slot ℚ, IsUnit A.det →
          Border.substitute A Border.det3 ≠ Border.padded := by
  refine ⟨Border.theScalingFamilyIsSingularAtTheLimit, ?_, theOrbitSeparationIsUnconditional⟩
  rw [theScalingMatrixSubstitutionIsBordersScaling]
  exact Border.theLimitOfTheFamilyIsThePaddedPermanent

/-! ## 8. What is not carried -/

/-- **Named open in this tree, and a real statement rather than a hedge.**  The generic `n × n`
determinant is annihilated by no nonzero direction, for every `n`.

Border proves the case `n = 3` by exhibiting nine rational probes, one per slot, and reading the
nine coefficients off one at a time.  The general case is the same argument — the `n²`
complementary minors have pairwise disjoint monomial supports, because a degree-`(n−1)` monomial in
the `(i,j)` minor uses exactly the rows other than `i` and the columns other than `j` — but as a
statement about `n` it needs that disjointness proved rather than enumerated, and that is not
carried here.  It is classically elementary; nothing below depends on it.

It is stated so the scope of `theOrbitSeparationIsUnconditional` is visible in the tree rather than
only in prose: that theorem is about the exhibited three-by-three carrier and no other size, and
this `Prop` is the input a version at another size would need. -/
def TheGenericDeterminantIsBlindInNoDirection (n : ℕ) : Prop :=
  ∀ v : Fin n × Fin n → ℚ,
    ∑ s : Fin n × Fin n,
        C (v s) * pderiv s (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin n × Fin n) ℚ)).det
      = 0 → v = 0

/-- The variable-indexed generic matrix is Border's `gen`, entry by entry. -/
theorem theGenericMatrixIsBordersGenericMatrix :
    (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℚ)) = Border.gen := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Border.gen, Border.x]

/-- **The named-open statement is discharged at three**, by Border's nine probes — which is what
makes it the generalization of a theorem rather than a hedge dressed as one.  What is open is the
statement as a function of `n`, and only that. -/
theorem theBlindnessStatementHoldsAtThree : TheGenericDeterminantIsBlindInNoDirection 3 := by
  intro v h
  refine Border.theDeterminantIsAnnihilatedOnlyByTheZeroDirection v ?_
  rw [theGenericMatrixIsBordersGenericMatrix] at h
  exact h

end Soma.Holonics.Millennium.ChainRule
