import Mathlib.FieldTheory.KummerExtension
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The norm relation: one product identity, two arithmetic cases, and the Euler factor

The Euler-system axiom for cyclotomic units is usually written as two lines.  With `K_m = Q(ζ_m)`
and `c_m = 1 − ζ_m`, for a prime `l`:

* `l ∤ m` — `N_{K_{ml}/K_m}(c_{ml}) = (1 − ζ_m^l)/(1 − ζ_m) = c_m^{σ_l − 1}`, the Euler factor
  `σ_l − 1` present;
* `l ∣ m` — `N_{K_{ml}/K_m}(c_{ml}) = 1 − ζ_m = c_m`, the Euler factor absent.

**This file proves that those two lines are two sub-products of one identity in an integral
domain**, and that the split between them is arithmetic — it is a fact about which set of
exponents is the relative Galois orbit — and never algebraic.  The identity itself is

```
∏_{j = 0}^{l-1} (1 − ξ · η^j) = 1 − ξ^l          for η a primitive l-th root of unity
```

and every hypothesis it needs is `0 < l` and `IsPrimitiveRoot η l` in a `CommRing` that is an
`IsDomain`.  Reading the unramified case takes `ξ = ζ_m` and drops the `j = 0` factor, which is
`c_m` itself, leaving the orbit `{1, …, l−1} = (Z/l)^×` for `l` prime.  Reading the ramified case
takes `ξ = ζ_{ml}` with `ξ^l = ζ_m` and keeps the whole range, because there the orbit **is** the
whole level.  Same identity; different orbit; the Euler factor is the difference between them.

## What is proved

* `theWholeOrbitProductIsOneMinusTheLevelPower` — the identity above, over any integral domain.
* `theHigherUnitDescendsThroughTheEulerFactor` — the unramified reading, product over `Ico 1 l`
  against `1 − ξ^l`, which is `N(c_{ml}) · c_m = σ_l(c_m)`.
* `theRamifiedLayerCarriesNoEulerFactor` — the ramified reading, product over `range l` against
  `1 − ξ^l`, which is `N(c_{ml}) = c_m` once `ξ^l = ζ_m`.
* `theTwoLayerDescentComposesToOneLevel` — two coprime levels descend to their product level.
  This is the transport chain: adjacent layers compose, and the composite is the relation at the
  composed level, with no extra hypothesis beyond coprimality of the two levels.
* `theRamifiedCaseIsNotTheUnramifiedOne` — the partition falsifier, **run** rather than asserted.
  In `𝔽₁₉` with `ζ₉ ↦ 4` and `ζ₃ ↦ 7` (so `4³ = 7`, modelling `m = l = 3`), the ramified norm is
  `1 − ζ₃`, while the unramified relation would force `N · c_m = 1 − ζ₃³ = 0`; the measured value
  is `17 ≠ 0`.  A relation that fails after a ring homomorphism `ℤ[ζ₉] → 𝔽₁₉` failed before it,
  so the model refutes and does not merely illustrate.
* `theEvenLevelNeedsNoOddnessHypothesis` — a level-2 instance, present because a proof of the main
  identity that needed `Odd l` or `IsUnit ξ` would have divided by `ξ^l` instead of taking the
  polynomial route.  The absence of those hypotheses is the receipt that it did not.
* `theMailletDeterminantAtFive`, `theMailletDeterminantAtSeven` — an arithmetic control on the
  **other** side of the theory, and it is here to carry a correction rather than a corroboration
  (see the boundary below).

## What is named open, honestly

* `TheRelativeOrbitFillsTheCoprimeLevel` — that every exponent `1 ≤ a < l` is realized by a
  `ℚ`-automorphism fixing `ζ_m` and sending `ζ_l ↦ ζ_l^a`.  Classically this is the linear
  disjointness of `Q(ζ_m)` and `Q(ζ_l)` over `Q` for `gcd(m, l) = 1`, and it is exactly the step
  that converts the product proved here into a *relative norm*.  Without it the theorems above are
  a polynomial identity wearing arithmetic clothes.

  **Where the gap actually sits, measured 2026-08-21 over the vendored mathlib at `v4.27.0`, from
  the package root.**  `IsCyclotomicExtension.autEquivPow`
  (`.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/Gal.lean:90`) is already general in its
  base field — it returns `(L ≃ₐ[K] L) ≃* (ZMod n)ˣ` for any `K`, so with `K = Q(ζ_m)` and
  `n = l` it *is* the relative statement.  Its hypothesis is `Irreducible (cyclotomic n K)`, and
  that hypothesis is never discharged over anything but `ℚ`:
  `grep -rn "theorem cyclotomic.irreducible" .lake/packages/mathlib/Mathlib --include='*.lean'`
  finds `cyclotomic.irreducible_rat` and nothing over a general base.  So the missing object is
  not an equivalence but one irreducibility, and
  `grep -rn "LinearDisjoint\|linearDisjoint" .lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/`
  → 0 lines.  Name searches over stated scopes, not content-absence proofs.

## Classical sources, cited and not proved here

Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (GTM 83, 1997), Ch. 8, for the two-case
norm relation and for Kummer–Sinnott `[E : C] = h⁺` (Thm 8.2).  Rubin, *Euler Systems* (Annals of
Math. Studies 147, 2000), §3.2, for the cyclotomic-unit system and its axioms.  Thaine,
*On the ideal class groups of real abelian number fields*, Ann. of Math. 128 (1988) 1–18, for what
the system bounds — the **even** eigenspaces.  Carlitz and Olson, *Maillet's determinant*, Proc.
AMS 6 (1955) 265–269, for `D_p = (−p)^{(p−3)/2} h⁻`.  Schoof, *Class numbers of real cyclotomic
fields of prime conductor*, Math. Comp. 72 (2003) 913–937, and Miller, arXiv:1407.2373, for the
fact that `h⁺` is *determined* only up to conductor 67 and is **probable** beyond it.

## Boundary

Every `theorem` here is discharged and none depends on `sorryAx`.  Nothing in this file claims any
movement on the Birch–Swinnerton-Dyer conjecture, the Riemann hypothesis, or any Iwasawa main
conjecture; no L-function, no `Λ`-module, no class group, no Selmer group and no class number
appears in any statement.  In particular the Maillet determinants below are integer determinants
and nothing more: their reading as `(−p)^{(p−3)/2} h⁻` is imported from Carlitz–Olson, and it is
recorded here precisely because it names a crossing — **the exactly computable side is the minus
side, and the cyclotomic-unit Euler system controls the plus side.**  Anyone quoting
"index of cyclotomic units `=` `h⁺`, exactly computable" has crossed the two halves; the index
theorem is real and the computability is not, past conductor 67.

The determinant values `−5` and `49` were recomputed by fraction-free (Bareiss) integer
elimination before being written here, together with all nineteen odd primes `p ≤ 71` against the
standard `h⁻` table; nineteen of nineteen matched `(−p)^{(p−3)/2} h⁻`.  Only the two that a
`Matrix.det_fin_two_of` / `Matrix.det_fin_three` proof can carry are stated as theorems; mathlib
has no `det_fin_four`, so `p = 11` and beyond are cut rather than carried by a hand expansion.
-/

namespace Soma.Holonics.Millennium.NormRelation

open Finset

/-! ## 1. The identity — one product, no oddness, no invertibility

`X_pow_sub_C_eq_prod` (mathlib, `Mathlib/FieldTheory/KummerExtension.lean`) splits `X^l − C a`
over an integral domain carrying a primitive `l`-th root of unity, once `a` is an `l`-th power.
Taking `a = ξ^l` and **evaluating the split at `X = 1`** is the whole proof: it needs no division,
hence no hypothesis on `ξ`, and no parity hypothesis on `l`. -/

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **The whole-orbit product.**  For `η` a primitive `l`-th root of unity in an integral domain
and any `ξ` whatever, the product of `1 − ξ η^j` over the full level is `1 − ξ^l`.

Read arithmetically with `ξ = ζ_m` and `η = ζ_l`: the `j = 0` factor is the cyclotomic unit `c_m`
and the remaining `l − 1` factors are the conjugates of `c_{ml}`. -/
theorem theWholeOrbitProductIsOneMinusTheLevelPower {l : ℕ} (hl : 0 < l) {eta : R}
    (heta : IsPrimitiveRoot eta l) (xi : R) :
    ∏ j ∈ range l, (1 - xi * eta ^ j) = 1 - xi ^ l := by
  have hsplit := X_pow_sub_C_eq_prod heta hl (α := xi) (a := xi ^ l) rfl
  have hev := congrArg (Polynomial.eval (1 : R)) hsplit
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow] at hev
  rw [hev]
  exact prod_congr rfl fun j _ => by rw [mul_comm]

/-- **The unramified layer: the norm carries the Euler factor.**  With `ξ = ζ_m`, `η = ζ_l` and
`l` prime, the product over `Ico 1 l` is the relative norm `N_{K_{ml}/K_m}(1 − ζ_{ml})`, the
detached factor `1 − ξ` is `c_m`, and the right side `1 − ξ^l` is `σ_l(c_m)`.  So the statement
is `N(c_{ml}) · c_m = σ_l(c_m)`, which is `N(c_{ml}) = c_m^{σ_l − 1}`.

No `Odd l` and no `IsUnit xi`: see the docstring of the file. -/
theorem theHigherUnitDescendsThroughTheEulerFactor {l : ℕ} (hl : 0 < l) {eta : R}
    (heta : IsPrimitiveRoot eta l) (xi : R) :
    (1 - xi) * ∏ j ∈ Ico 1 l, (1 - xi * eta ^ j) = 1 - xi ^ l := by
  have hbot : ∏ j ∈ range l, (1 - xi * eta ^ j)
      = (1 - xi * eta ^ 0) * ∏ j ∈ Ico 1 l, (1 - xi * eta ^ j) := by
    rw [range_eq_Ico]
    exact prod_eq_prod_Ico_succ_bot hl _
  rw [← theWholeOrbitProductIsOneMinusTheLevelPower hl heta xi, hbot]
  simp

/-- **The ramified layer: the norm carries no Euler factor.**  With `ξ = ζ_{ml}` and `l ∣ m`, the
relative Galois orbit of `ζ_{ml}` over `K_m` is the *whole* level `{η^j : j < l}`, and `ξ^l` is
`ζ_m`.  So the product over `range l` is the relative norm outright and equals `1 − ζ_m = c_m`.

Algebraically this is the same identity as the unramified case.  **The partition between the two
is arithmetic — which exponents form the orbit — and nothing in the algebra decides it.**  Stating
one of the two and calling it "the norm relation" authors the partition; both are stated. -/
theorem theRamifiedLayerCarriesNoEulerFactor {l : ℕ} (hl : 0 < l) {eta : R}
    (heta : IsPrimitiveRoot eta l) (xi : R) :
    ∏ j ∈ range l, (1 - xi * eta ^ j) = 1 - xi ^ l :=
  theWholeOrbitProductIsOneMinusTheLevelPower hl heta xi

/-! ## 2. The chain — two coprime layers compose to their product layer

The Euler system is not one relation but an indexed compatible family, and the content of the
family is that adjacent transitions commute.  Here that is proved outright: descending through
level `l₂` and then through level `l₁` returns the relation at level `l₁ l₂`, and the only
hypothesis beyond primitivity is that the two levels are coprime — which is the same coprimality
that makes `η₁ η₂` primitive at the composed level. -/

/-- **Two coprime layers compose to one level.**  The double product over the two levels is the
single relation at their product.  Proof: the inner product is the identity at level `l₂` with
`ξ η₁^i` in place of `ξ`; the outer product is then the identity at level `l₁` with `ξ^{l₂}` in
place of `ξ` and `η₁^{l₂}` — primitive at level `l₁` by coprimality — in place of `η₁`. -/
theorem theTwoLayerDescentComposesToOneLevel {l₁ l₂ : ℕ} (h₁ : 0 < l₁) (h₂ : 0 < l₂)
    (hco : Nat.Coprime l₁ l₂) {e₁ e₂ : R} (he₁ : IsPrimitiveRoot e₁ l₁)
    (he₂ : IsPrimitiveRoot e₂ l₂) (xi : R) :
    ∏ i ∈ range l₁, ∏ j ∈ range l₂, (1 - xi * e₁ ^ i * e₂ ^ j) = 1 - xi ^ (l₁ * l₂) := by
  have hinner : ∀ i ∈ range l₁,
      (∏ j ∈ range l₂, (1 - xi * e₁ ^ i * e₂ ^ j)) = 1 - xi ^ l₂ * (e₁ ^ l₂) ^ i := by
    intro i _
    rw [theWholeOrbitProductIsOneMinusTheLevelPower h₂ he₂ (xi * e₁ ^ i)]
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm i l₂]
  have hprim : IsPrimitiveRoot (e₁ ^ l₂) l₁ := he₁.pow_of_coprime l₂ (Nat.Coprime.symm hco)
  rw [prod_congr rfl hinner,
    theWholeOrbitProductIsOneMinusTheLevelPower h₁ hprim (xi ^ l₂), ← pow_mul,
    Nat.mul_comm l₂ l₁]

/-! ## 3. The partition falsifier, run in a finite model

`ℤ[ζ₉] → 𝔽₁₉` sending `ζ₉ ↦ 4` is a ring homomorphism: `4` has order `9` in `𝔽₁₉ˣ` and
`4³ = 7`, which has order `3`.  So the pair `(ζ₉, ζ₃) ↦ (4, 7)` carries every multiplicative
relation forward, and a relation that fails in the image failed in the source.  This models
`m = l = 3`, the smallest ramified case, which is the instance the partition falsifier names. -/

/-- `7` is a primitive cube root of unity in `𝔽₁₉`.  By `orderOf_eq_prime`, on two `decide`s. -/
theorem theCubeRootIsPrimitiveInTheModel : IsPrimitiveRoot (7 : ZMod 19) 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : orderOf (7 : ZMod 19) = 3 := orderOf_eq_prime (by decide) (by decide)
  exact ⟨by decide, fun m hm => h3 ▸ orderOf_dvd_of_pow_eq_one hm⟩

/-- The model's ninth root cubes to its cube root: `4³ = 7` in `𝔽₁₉`.  By `decide`. -/
theorem theNinthRootCubesToTheCubeRootInTheModel : (4 : ZMod 19) ^ 3 = 7 := by decide

/-- **The ramified norm, computed in the model.**  `N(1 − ζ₉) = 1 − ζ₉³ = 1 − ζ₃`, the ramified
law, obtained by applying the general theorem — not by evaluating a product by hand. -/
theorem theRamifiedNormInTheModelIsTheLowerUnit :
    ∏ j ∈ range 3, (1 - (4 : ZMod 19) * 7 ^ j) = 1 - (7 : ZMod 19) := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  rw [theRamifiedLayerCarriesNoEulerFactor (by norm_num) theCubeRootIsPrimitiveInTheModel
    (4 : ZMod 19), theNinthRootCubesToTheCubeRootInTheModel]

/-- **The partition falsifier, run.**  If the unramified relation held at `m = l = 3` it would
force `N(c_{ml}) · c_m = σ_l(c_m) = 1 − ζ₃³ = 0`.  The measured left side is `13 · 13 = 17` in
`𝔽₁₉`, which is not `0`.  So the two cases are genuinely two, and a file stating only the
unramified identity would be refuted by this instance.  The left side comes from the general
theorem; only the final inequality is `decide`. -/
theorem theRamifiedCaseIsNotTheUnramifiedOne :
    (∏ j ∈ range 3, (1 - (4 : ZMod 19) * 7 ^ j)) * (1 - (7 : ZMod 19))
      ≠ 1 - (7 : ZMod 19) ^ 3 := by
  rw [theRamifiedNormInTheModelIsTheLowerUnit]
  decide

/-- `4` is `−1` in `𝔽₅` and is a primitive square root of unity there.  By `orderOf_eq_prime`. -/
theorem theEvenLevelRootIsPrimitiveInTheModel : IsPrimitiveRoot (4 : ZMod 5) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h2 : orderOf (4 : ZMod 5) = 2 := orderOf_eq_prime (by decide) (by decide)
  exact ⟨by decide, fun m hm => h2 ▸ orderOf_dvd_of_pow_eq_one hm⟩

/-- **The hypothesis falsifier, run at an even level**, by instantiating the unramified theorem
rather than by evaluating anything.  A proof of the main identity requiring `Odd l` would have
taken the divide-by-`ξ^l` route and could not be instantiated here at all; that it can be is the
receipt that it did not. -/
theorem theEvenLevelNeedsNoOddnessHypothesis :
    (1 - (2 : ZMod 5)) * ∏ j ∈ Ico 1 2, (1 - (2 : ZMod 5) * 4 ^ j) = 1 - (2 : ZMod 5) ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact theHigherUnitDescendsThroughTheEulerFactor (by norm_num)
    theEvenLevelRootIsPrimitiveInTheModel 2

/-- **The identity at a non-unit.**  `ξ = 0` is not invertible in any ring, and the identity holds
there by the general theorem with no side condition — the degenerate check that no division was
performed. -/
theorem theIdentityHoldsAtANonUnit {l : ℕ} (hl : 0 < l) {eta : R} (heta : IsPrimitiveRoot eta l) :
    ∏ j ∈ range l, (1 - (0 : R) * eta ^ j) = 1 - (0 : R) ^ l :=
  theWholeOrbitProductIsOneMinusTheLevelPower hl heta 0

/-! ## 4. What is not proved here, stated as a proposition rather than assumed -/

/-- **Named open in this file.**  The relative Galois orbit at a coprime prime level: for a field
`L` generated over `ℚ` by a primitive `m`-th root and a primitive `l`-th root of unity, with `l`
prime and `l ∤ m`, every exponent `1 ≤ a < l` is realized by a `ℚ`-automorphism of `L` that fixes
the `m`-th root and sends the `l`-th root to its `a`-th power.

Classically true — it is the linear disjointness of `Q(ζ_m)` and `Q(ζ_l)` over `Q`, equivalently
`Gal(Q(ζ_{ml})/Q(ζ_m)) ≅ (Z/l)^×` — and it is the whole distance between the product proved above
and a *relative norm*.  Its mathlib-native form is `IsCyclotomicExtension.autEquivPow` at
`K = Q(ζ_m)`, whose one undischarged input is `Irreducible (cyclotomic l K)` over that base.

It is stated and not used: no theorem in this file assumes it, and nothing below it depends on
it. -/
def TheRelativeOrbitFillsTheCoprimeLevel : Prop :=
  ∀ (L : Type) [Field L] [Algebra ℚ L] (m l : ℕ) (zm zl : L),
    0 < m → Nat.Prime l → ¬ l ∣ m →
    IsPrimitiveRoot zm m → IsPrimitiveRoot zl l →
    Algebra.adjoin ℚ ({zm, zl} : Set L) = ⊤ →
    ∀ a : ℕ, 1 ≤ a → a < l → ∃ σ : L ≃ₐ[ℚ] L, σ zm = zm ∧ σ zl = zl ^ a

/-! ## 5. The arithmetic control, on the other side of the theory

Maillet's matrix at an odd prime `p` has entry `R(r · s⁻¹ mod p)` at `(r, s)` for
`1 ≤ r, s ≤ (p−1)/2`, where `R` is the least positive residue.  Carlitz and Olson (1955) prove its
determinant is `(−p)^{(p−3)/2} h⁻`, refuting Malo's 1914 conjecture that it is `(−p)^{(p−3)/2}`.
The determinant is computed here from `ZMod` arithmetic, not from a transcribed table: the entries
are produced by inversion in `ZMod p` and only then read as integers.

`h⁻` has no owner in mathlib and none is invented here — the theorems are integer determinants and
the class-number reading is the imported half. -/

/-- Maillet's matrix at level `m` for the prime `p`: the entry at `(r, s)` is the least positive
residue of `(r+1) · (s+1)⁻¹` modulo `p`, produced by inversion in `ZMod p`. -/
def maillet (p m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r s => ((((r.val + 1 : ℕ) : ZMod p) * ((s.val + 1 : ℕ) : ZMod p)⁻¹).val : ℤ)

/-- The entries at `p = 5`, computed by `decide` from `ZMod 5` inversion. -/
theorem theMailletMatrixAtFiveIsExplicit : maillet 5 2 = !![1, 3; 2, 1] := by
  native_decide

/-- The entries at `p = 7`, computed by `decide` from `ZMod 7` inversion. -/
theorem theMailletMatrixAtSevenIsExplicit : maillet 7 3 = !![1, 4, 5; 2, 1, 3; 3, 5, 1] := by
  native_decide

/-- **`D₅ = −5`.**  Carlitz–Olson read this as `(−5)^1 · h⁻(5)` with `h⁻(5) = 1`; the reading is
imported, the determinant is proved. -/
theorem theMailletDeterminantAtFive : (maillet 5 2).det = -5 := by
  rw [theMailletMatrixAtFiveIsExplicit, Matrix.det_fin_two_of]; norm_num

/-- **`D₇ = 49`.**  Carlitz–Olson read this as `(−7)² · h⁻(7)` with `h⁻(7) = 1`; the reading is
imported, the determinant is proved. -/
theorem theMailletDeterminantAtSeven : (maillet 7 3).det = 49 := by
  rw [theMailletMatrixAtSevenIsExplicit]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end Soma.Holonics.Millennium.NormRelation
