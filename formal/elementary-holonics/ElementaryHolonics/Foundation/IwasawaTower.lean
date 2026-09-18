import ElementaryHolonics.Foundation.ContinuingTower
import ElementaryHolonics.Millennium.NormRelation
import ElementaryHolonics.Millennium.SelmerCalculus
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The Iwasawa tower — item C8 of the shared carrier

[definition] This file discharges item **C8** of
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`.  It is the arithmetic instance of
`Foundation/ContinuingTower.lean`'s `Tower`: a continuing object whose charts are the layers of a
`ℤ_p`-tower, whose faces are finite specializations, and whose codimension-one receiver reading is
the characteristic ideal.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs::{IwasawaLevel, omega, IwasawaTower,
OmegaRestriction, FiniteLevelRing, LambdaPresentation, CharacteristicFace, FiniteSpecialization}`,
the finite computable shadow: exact `ℤ/p^n[T]/(ω_n)` arithmetic over `BigInt`/`BigUint`, the
`ω_n` chain by exact polynomial division, and the finite specializations of `Λ/(f)` modules read as
explicit finite abelian groups through `rebase_invariants`' Smith normal form.

## What is proved here

**1. The blocker named in the plan is discharged.**  `Millennium/NormRelation.lean` states
`TheRelativeOrbitFillsTheCoprimeLevel` as an unused `Prop` and locates the gap at
`Irreducible (cyclotomic n K)` over a base other than `ℚ`.  Both halves are now closed:

* `theCyclotomicPolynomialIsIrreducibleOverTheCoprimeLevel` — for coprime `m` and `n`,
  `cyclotomic n` **is** irreducible over `ℚ(ζ_m)`.  The route is the tower law, not a new
  irreducibility argument: `IsCyclotomicExtension.finrank` twice over `ℚ` and `Nat.totient_mul`
  give `[ℚ(ζ_mn) : ℚ(ζ_m)] = φ(n)`, the minimal polynomial of `ζ_n` over `ℚ(ζ_m)` divides
  `cyclotomic n` and already has that degree, and `eq_of_monic_of_dvd_of_natDegree_le` closes it.
  `theCoprimeIrreducibilityIsNotVacuous` instantiates it on `ℚ ⊆ ℚ(ζ_m) ⊆ ℚ(ζ_m)(ζ_n)`, so the
  hypotheses are inhabited and the statement is not vacuous.
* `theRelativeOrbitFillsTheCoprimeLevel` — `NormRelation.TheRelativeOrbitFillsTheCoprimeLevel`
  itself, proved.

**[open] A correction to the plan's own route, stated because it changes what C8 can use.**  The
plan says the Iwasawa tower needs that irreducibility.  It does not, and cannot: the layers of the
`ℤ_p`-tower are `ℚ(ζ_{p^{k+1}}) / ℚ(ζ_{p^k})`, which are **totally ramified of degree `p`**, and
`theRamifiedLayerCyclotomicIsReducible` proves that `cyclotomic (p^(k+1))` is *reducible* over
`ℚ(ζ_{p^k})` for every `(p, k) ≠ (2, 1)` with `k ≥ 1`.  The relative irreducibility is the
**coprime** statement and belongs to the Euler system's horizontal direction — the `NormRelation`
layer — not to the vertical tower.  The vertical layer degree is
`thePPowerLayerHasDegreeP`, which needs no coprimality and no irreducibility over the base.

**2. `Γ`, `T`, `Λ`.**  `Γ ≅ ℤ_p` is *not* rebuilt: it is `padicTower`'s section object and
`ContinuingTower.padicSectionEquiv` is cited.  `Λ` is `PowerSeries ℤ_[p]` in the difference
coordinate `T = γ − 1`, and `ωPoly p n = (1 + T)^(p^n) − 1` is built as a polynomial so that its
distinguished shape and the quotient's rank are theorems rather than descriptions:
`omegaPoly_monic`, `omegaPoly_natDegree` (`= p^n`), `omegaPoly_isDistinguished` (constant term `0`,
every strictly lower coefficient divisible by `p`, through `Nat.Prime.dvd_choose_pow`),
`omegaPoly_dvd_succ` (the divisibility chain, through `sub_dvd_pow_sub_pow` applied to
`Y = (1+T)^{p^n}`), and `omegaQuotient_finrank : Module.finrank ℤ_[p] (Λ_n) = p ^ n` through
`AdjoinRoot.powerBasis'`.  `omegaGroupRingEquiv` proves `ℤ_p[T]/(ω_n) ≅ ℤ_p[γ]/(γ^{p^n} − 1)` as
`ℤ_p`-algebras — the finite level **is** the group ring of `Γ/Γ_n ≅ ℤ/p^n` — through the
substitution `γ = 1 + T` and its inverse; the power-series form of that quotient is Weierstrass
division and is cited, not proved.

**3. An Iwasawa module is a `Tower`.**  `quotientTower` makes *any* antitone filtration of a module
a `Tower` in the sense of `ContinuingTower.lean`, `quotientTowerSection` sends each element of the
module to a compatible section, and `quotientTowerSection_injective_iff` proves that map is
injective **exactly** when the filtration is separated.  Surjectivity is completeness and is
carried as a hypothesis (`QuotientTowerComplete`), never asserted, and
`quotientTowerSection_not_injective_of_top` shows the criterion is not vacuous.  `omegaTower` is
the instance at `N n = ω_n • M`, whose antitonicity is `omega_dvd_of_le`.  `transitionOfHom`
presents any additive map of the tower as a C4 `Transition` whose retained residual is its kernel,
and `transitionOfHom_residual_subsingleton_iff` proves that residual is trivial exactly when
nothing was dropped; the control map of §4 is carried that way.

**4. `CharacteristicFace` is conditional, and blind.**  `StructureData` is a **hypothesis
structure** carrying the elementary module and the pseudo-isomorphism; there is no `axiom` and no
`sorry` anywhere in this file.  The two blindness statements are **unconditional**:

* `theCharacteristicFaceDoesNotDetermineTheModule` — `Λ/(T²)` and `Λ/(T) ⊕ Λ/(T)` carry the same
  codimension-one datum and are not isomorphic, proved by annihilator: `T` kills the second and
  not the first.  This is the same separation `ContinuingTower.theOrderFaceDoesNotDetermineTheModule`
  makes for `ℤ/4` against `ℤ/2 ⊕ ℤ/2`, now over `Λ`.
* `thePseudoNullResidueIsInvisibleToTheFace` — a nonzero finite `Λ`-module annihilated by both `p`
  and `T` whose characteristic ideal is the unit ideal.  The codimension-one face is blind above
  codimension one.

**5. `μ` and `λ` are growth exponents, not entropy.**  `WeierstrassData` carries a distinguished
factorization as data, with `omegaWeierstrassData` a constructed instance (`ω_n` itself, `μ = 0`,
`λ = p^n`) and `weierstrassData_isEmpty_at_zero` a constructed non-instance; `mu` and `lambda` are
read off it, and the growth law
`|M/ω_n M| = p^{μ p^n + λ n + ν}` is stated as `TheGrowthLaw`, a `Prop` **cited** to Iwasawa
(1959) and Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Thm 13.13, and **not proved
here**.  The Rust owner exhibits it numerically as exact integers at small `(p, n)`.

**6. The main conjecture is an open `Prop`.**  `TheMainConjecture` is receiver-exactness — equality
of two codimension-one faces — and explicitly not source identity.  No proof is claimed, and
`theMainConjectureIsNotSourceIdentity` proves that the equality of faces it asserts would *not*
establish equality of modules, by citing the counterexample above.

## Epistemic grades

Every `theorem` in this file is discharged; `#print axioms` on the named results returns only
`propext`, `Classical.choice`, `Quot.sound`.  `StructureData`, `WeierstrassData`, `TheGrowthLaw`
and `TheMainConjecture` are hypothesis carriers and open statements and are marked as such at each
declaration.  Nothing here claims progress on any Iwasawa main conjecture.
-/

noncomputable section

namespace Soma.Holonics.Foundation.IwasawaTower

open Polynomial IsCyclotomicExtension
open Soma.Holonics.Foundation.ContinuingTower

universe u v

/-! ## 1. The blocker: irreducibility of the cyclotomic polynomial over a coprime cyclotomic base -/

/-- [proved-derived; formal-checked] Primitive roots at coprime levels multiply to a primitive root
at the product level.  Mathlib carries the order statement
(`Commute.orderOf_mul_eq_mul_orderOf_of_coprime`) but not this corollary. -/
theorem isPrimitiveRoot_mul_of_coprime {R : Type u} [CommRing R] [IsDomain R] {m n : ℕ}
    {a b : R} (ha : IsPrimitiveRoot a m) (hb : IsPrimitiveRoot b n) (h : Nat.Coprime m n) :
    IsPrimitiveRoot (a * b) (m * n) := by
  have hm : m = orderOf a := ha.eq_orderOf
  have hn : n = orderOf b := hb.eq_orderOf
  have hord : orderOf (a * b) = orderOf a * orderOf b :=
    (Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [← hm, ← hn]; exact h)
  rw [hm, hn, ← hord]
  exact IsPrimitiveRoot.orderOf _

section CoprimeTower

variable {m n : ℕ} (F L : Type u) [Field F] [Field L]
variable [Algebra ℚ F] [Algebra ℚ L] [Algebra F L] [IsScalarTower ℚ F L]

/-- [proved-derived; formal-checked] A cyclotomic extension of level `m` over `ℚ` followed by one
of level `n` over it, with `m` and `n` coprime, is a cyclotomic extension of level `m * n`
over `ℚ`. -/
theorem isCyclotomicExtension_mul_of_coprime (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    [IsCyclotomicExtension {m} ℚ F] [IsCyclotomicExtension {n} F L] :
    IsCyclotomicExtension {m * n} ℚ L := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hunion : IsCyclotomicExtension ({m} ∪ {n}) ℚ L :=
    IsCyclotomicExtension.trans {m} {n} ℚ F L (algebraMap F L).injective
  have hzm : IsPrimitiveRoot (algebraMap F L (zeta m ℚ F)) m :=
    (zeta_spec m ℚ F).map_of_injective (algebraMap F L).injective
  have hprod := isPrimitiveRoot_mul_of_coprime hzm (zeta_spec n F L) hmn
  rw [IsCyclotomicExtension.iff_adjoin_eq_top]
  refine ⟨fun k hk _ => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hk
    subst hk
    exact ⟨_, hprod⟩
  · rw [eq_top_iff, ← ((IsCyclotomicExtension.iff_adjoin_eq_top ({m} ∪ {n}) ℚ L).1 hunion).2]
    refine Algebra.adjoin_mono ?_
    rintro x ⟨k, hk, hk0, hx⟩
    refine ⟨m * n, rfl, by positivity, ?_⟩
    have hdvd : k ∣ m * n := by
      rcases hk with hk | hk
      · exact (Set.mem_singleton_iff.1 hk) ▸ Dvd.intro n rfl
      · exact (Set.mem_singleton_iff.1 hk) ▸ Dvd.intro_left m rfl
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hx, one_pow]

/-- [proved-derived; formal-checked] **The relative degree is the totient of the upper level.**
`[ℚ(ζ_{mn}) : ℚ(ζ_m)] = φ(n)` for coprime `m` and `n`, by the tower law over `ℚ` and
`Nat.totient_mul`.  No irreducibility over `ℚ(ζ_m)` is used — this is what supplies it below. -/
theorem theRelativeCyclotomicDegreeIsTheTotient (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) [IsCyclotomicExtension {m} ℚ F] [IsCyclotomicExtension {n} F L] :
    Module.finrank F L = n.totient := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (m * n) := ⟨by positivity⟩
  have : IsCyclotomicExtension {m * n} ℚ L :=
    isCyclotomicExtension_mul_of_coprime F L hm hn hmn
  have : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {m} ℚ F
  have : FiniteDimensional F L := IsCyclotomicExtension.finiteDimensional {n} F L
  have h1 : Module.finrank ℚ F = m.totient :=
    IsCyclotomicExtension.finrank F (cyclotomic.irreducible_rat hm)
  have h2 : Module.finrank ℚ L = (m * n).totient :=
    IsCyclotomicExtension.finrank L (cyclotomic.irreducible_rat (by positivity))
  have h3 := Module.finrank_mul_finrank ℚ F L
  rw [h1, h2, Nat.totient_mul hmn] at h3
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 hm) h3

/-- [proved-derived; formal-checked] **The blocker named in `Millennium/NormRelation.lean`,
discharged.**  For coprime `m` and `n`, `cyclotomic n` is irreducible over `ℚ(ζ_m)`.

The proof does not repeat an irreducibility argument.  It is degree bookkeeping: the minimal
polynomial of `ζ_n` over `ℚ(ζ_m)` divides `cyclotomic n` because `ζ_n` is a root of it, its degree
is the relative degree `φ(n)` by `theRelativeCyclotomicDegreeIsTheTotient`, and `cyclotomic n` is
monic of exactly that degree, so the two coincide and `minpoly.irreducible` applies. -/
theorem theCyclotomicPolynomialIsIrreducibleOverTheCoprimeLevel [CharZero L] (hm : 0 < m)
    (hn : 0 < n)
    (hmn : Nat.Coprime m n) [IsCyclotomicExtension {m} ℚ F] [IsCyclotomicExtension {n} F L] :
    Irreducible (cyclotomic n F) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero ((n : ℕ) : L) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : FiniteDimensional F L := IsCyclotomicExtension.finiteDimensional {n} F L
  set ζ := zeta n F L with hζdef
  have hζ : IsPrimitiveRoot ζ n := zeta_spec n F L
  have hint : IsIntegral F ζ := IsIntegral.of_finite F ζ
  have hdeg : (minpoly F ζ).natDegree = n.totient := by
    have hpb := (hζ.powerBasis F).natDegree_minpoly
    rw [IsPrimitiveRoot.powerBasis_gen] at hpb
    rw [hpb, ← PowerBasis.finrank]
    exact theRelativeCyclotomicDegreeIsTheTotient F L hm hn hmn
  have haeval : (Polynomial.aeval ζ) (cyclotomic n F) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact hζ
  have heq : cyclotomic n F = minpoly F ζ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic n F)
      (minpoly.dvd F ζ haeval) (by rw [natDegree_cyclotomic, hdeg])
  rw [heq]
  exact minpoly.irreducible hint

/-- [proved-derived; formal-checked] **The hypotheses above are inhabited, so the theorem is not
vacuous.**  The concrete tower `ℚ ⊆ ℚ(ζ_m) ⊆ ℚ(ζ_m)(ζ_n)` satisfies every instance the previous
theorem takes, and the conclusion is irreducibility over a base that is genuinely larger than `ℚ`.
-/
theorem theCoprimeIrreducibilityIsNotVacuous {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) :
    Irreducible (cyclotomic n (CyclotomicField m ℚ)) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero ((m : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 hm.ne'⟩
  have hF : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  have htower : IsScalarTower ℚ (CyclotomicField m ℚ)
      (CyclotomicField n (CyclotomicField m ℚ)) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact theCyclotomicPolynomialIsIrreducibleOverTheCoprimeLevel (CyclotomicField m ℚ)
    (CyclotomicField n (CyclotomicField m ℚ)) hm hn hmn

end CoprimeTower

/-! ## 1b. The vertical layer: degree `p`, totally ramified, and *not* the coprime case -/

section PPowerLayer

variable {p k : ℕ} (F L : Type u) [Field F] [Field L]
variable [Algebra ℚ F] [Algebra ℚ L] [Algebra F L] [IsScalarTower ℚ F L]

/-- [proved-derived; formal-checked] **The `ℤ_p`-tower's own layer degree.**
`[ℚ(ζ_{p^{k+1}}) : ℚ(ζ_{p^k})] = p` for `k ≥ 1`.  This needs no coprimality and no irreducibility
over the lower level: it is `Nat.totient_prime_pow` on both sides of the tower law. -/
theorem thePPowerLayerHasDegreeP (hp : p.Prime) (hk : 0 < k)
    [IsCyclotomicExtension {p ^ k} ℚ F] [IsCyclotomicExtension {p ^ (k + 1)} ℚ L] :
    Module.finrank F L = p := by
  have hpne : p ≠ 0 := hp.pos.ne'
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hpne⟩
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hpne⟩
  have : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ F
  have : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} ℚ L
  have : FiniteDimensional F L := FiniteDimensional.right ℚ F L
  have h1 : Module.finrank ℚ F = p ^ (k - 1) * (p - 1) := by
    rw [IsCyclotomicExtension.finrank (n := p ^ k) F
      (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (pow_ne_zero k hpne))),
      Nat.totient_prime_pow hp hk]
  have h2 : Module.finrank ℚ L = p ^ k * (p - 1) := by
    rw [IsCyclotomicExtension.finrank (n := p ^ (k + 1)) L
      (cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (pow_ne_zero (k + 1) hpne))),
      Nat.totient_prime_pow hp (Nat.succ_pos k)]
    simp
  have h3 := Module.finrank_mul_finrank ℚ F L
  rw [h1, h2] at h3
  have hpow : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow] at h3
  have hA : 0 < p ^ (k - 1) * (p - 1) :=
    Nat.mul_pos (pow_pos hp.pos _) (by have := hp.two_le; omega)
  refine Nat.eq_of_mul_eq_mul_left hA ?_
  rw [h3]; ring

/-- [proved-derived; formal-checked] **The plan's route does not apply to the vertical tower.**
`cyclotomic (p^(k+1))` is *reducible* over `ℚ(ζ_{p^k})` for `k ≥ 1` except at `(p, k) = (2, 1)`.
Its degree there is `p^k (p−1)`, while every element of the upper field has degree at most
`p` over the lower one by `thePPowerLayerHasDegreeP`.  The relative irreducibility discharged
above is the **coprime** statement, and the `ℤ_p`-tower is totally ramified, which is the opposite
regime. -/
theorem theRamifiedLayerCyclotomicIsReducible [CharZero F] [CharZero L] (hp : p.Prime) (hk : 0 < k)
    (hpk : ¬ (p = 2 ∧ k = 1))
    [IsCyclotomicExtension {p ^ k} ℚ F] [IsCyclotomicExtension {p ^ (k + 1)} ℚ L] :
    ¬ Irreducible (cyclotomic (p ^ (k + 1)) F) := by
  have hpne : p ≠ 0 := hp.pos.ne'
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hpne⟩
  have : NeZero (((p ^ (k + 1) : ℕ) : L)) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero (k + 1) hpne)⟩
  have : NeZero (((p ^ (k + 1) : ℕ) : F)) := ⟨Nat.cast_ne_zero.2 (pow_ne_zero (k + 1) hpne)⟩
  have : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} ℚ L
  have : FiniteDimensional F L := FiniteDimensional.right ℚ F L
  intro hirr
  have hζ : IsPrimitiveRoot (zeta (p ^ (k + 1)) ℚ L) (p ^ (k + 1)) :=
    zeta_spec (p ^ (k + 1)) ℚ L
  have heq : cyclotomic (p ^ (k + 1)) F = minpoly F (zeta (p ^ (k + 1)) ℚ L) :=
    hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  have hle : (minpoly F (zeta (p ^ (k + 1)) ℚ L)).natDegree ≤ Module.finrank F L :=
    minpoly.natDegree_le _
  rw [← heq, natDegree_cyclotomic, Nat.totient_prime_pow hp (Nat.succ_pos k),
    thePPowerLayerHasDegreeP F L hp hk] at hle
  -- `p ^ k * (p - 1) ≤ p` forces `p = 2` and `k = 1`
  have hp2 : 2 ≤ p := hp.two_le
  have hpk1 : p ≤ p ^ k := Nat.le_self_pow hk.ne' p
  have h1 : p * (p - 1) ≤ p :=
    le_trans (Nat.mul_le_mul_right _ hpk1) hle
  have hd1 : p - 1 ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using h1) hp.pos
  have hpeq : p = 2 := by omega
  subst hpeq
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have hgrow : (2 : ℕ) ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hle' : (2 : ℕ) ^ k ≤ 2 := by simpa using hle
    omega
  exact hpk ⟨rfl, hk1⟩

end PPowerLayer

/-! ## 1c. `NormRelation.TheRelativeOrbitFillsTheCoprimeLevel`, discharged -/

open Soma.Holonics.Millennium.NormRelation in
/-- [proved-derived; formal-checked] **The relative-orbit step of `Millennium/NormRelation.lean`,
proved.**  `TheRelativeOrbitFillsTheCoprimeLevel` was deposited there as an unused `Prop` with the
Mathlib gap located; this is that `Prop`.

**[open] The route is not the one the plan predicted, and this narrows the plan's own wording.**
`NormRelation.lean:256` says the statement is "exactly" the relative irreducibility over `ℚ(ζ_m)`.
It is *implied* by it, but it does not need it: the whole level `ℚ(ζ_m, ζ_l)` is already a
cyclotomic extension of level `m l` over `ℚ`, where `cyclotomic.irreducible_rat` applies with no
relative statement at all, and the required automorphism is the unit of `(ℤ/ml)ˣ` that the Chinese
remainder theorem produces from `1 mod m` and `a mod l`.  The relative irreducibility is proved
above anyway, because it is the sharper object and the Euler system's horizontal composition wants
it; it is not what this `Prop` costs. -/
theorem theRelativeOrbitFillsTheCoprimeLevel : TheRelativeOrbitFillsTheCoprimeLevel := by
  intro L _ _ m l zm zl hm hl hlm hzm hzl htop a ha1 hal
  have hml : Nat.Coprime m l := ((hl.coprime_iff_not_dvd).2 hlm).symm
  have hmlpos : 0 < m * l := Nat.mul_pos hm hl.pos
  have : NeZero (m * l) := ⟨hmlpos.ne'⟩
  have hprod : IsPrimitiveRoot (zm * zl) (m * l) := isPrimitiveRoot_mul_of_coprime hzm hzl hml
  -- `L` is the cyclotomic field of level `m * l` over `ℚ`
  have hcyc : IsCyclotomicExtension {m * l} ℚ L := by
    rw [IsCyclotomicExtension.iff_adjoin_eq_top]
    refine ⟨fun k hk _ => ?_, ?_⟩
    · rw [Set.mem_singleton_iff] at hk; subst hk; exact ⟨_, hprod⟩
    · rw [eq_top_iff, ← htop]
      refine Algebra.adjoin_mono ?_
      rintro x (rfl | rfl)
      · exact ⟨m * l, rfl, hmlpos.ne', by rw [pow_mul, hzm.pow_eq_one, one_pow]⟩
      · exact ⟨m * l, rfl, hmlpos.ne', by rw [mul_comm, pow_mul, hzl.pow_eq_one, one_pow]⟩
  -- the exponent: `c ≡ 1 mod m` and `c ≡ a mod l`, supplied by the Chinese remainder theorem
  have hc1 : (Nat.chineseRemainder hml 1 a : ℕ) ≡ 1 [MOD m] := (Nat.chineseRemainder hml 1 a).2.1
  have hca : (Nat.chineseRemainder hml 1 a : ℕ) ≡ a [MOD l] := (Nat.chineseRemainder hml 1 a).2.2
  have hclt : (Nat.chineseRemainder hml 1 a : ℕ) < m * l :=
    Nat.chineseRemainder_lt_mul hml 1 a hm.ne' hl.pos.ne'
  set c : ℕ := (Nat.chineseRemainder hml 1 a : ℕ) with hcdef
  have hal' : Nat.Coprime a l := ((hl.coprime_iff_not_dvd).2 (fun hdvd =>
    absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))).symm
  have hcop : Nat.Coprime c (m * l) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · simpa [Nat.Coprime] using hc1.gcd_eq
    · simpa [Nat.Coprime, hca.gcd_eq] using hal'
  have hirr : Irreducible (cyclotomic (m * l) ℚ) := cyclotomic.irreducible_rat hmlpos
  set u : (ZMod (m * l))ˣ := ZMod.unitOfCoprime c hcop with hu
  set σ := (autEquivPow L hirr).symm u with hσ
  have hζ : IsPrimitiveRoot (zeta (m * l) ℚ L) (m * l) := zeta_spec (m * l) ℚ L
  have hval : ((u : ZMod (m * l))).val = c := by
    rw [hu, ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hclt]
  have hσζ : σ (zeta (m * l) ℚ L) = (zeta (m * l) ℚ L) ^ c := by
    have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζ σ
    have hmap : (autEquivPow L hirr) σ = u := (autEquivPow L hirr).apply_symm_apply u
    rw [autEquivPow_apply] at hmap
    rw [← hspec]
    congr 1
    rw [show (IsPrimitiveRoot.autToPow ℚ hζ) σ = u from hmap, hval]
  -- every root of unity in `L` whose order divides `m l` is a power of `ζ`, so `σ` raises it to `c`
  have key : ∀ x : L, x ^ (m * l) = 1 → σ x = x ^ c := by
    intro x hx
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
    rw [← hi, map_pow, hσζ, ← pow_mul, ← pow_mul, Nat.mul_comm c i]
  refine ⟨σ, ?_, ?_⟩
  · rw [key zm (by rw [pow_mul, hzm.pow_eq_one, one_pow])]
    rw [show zm ^ c = zm ^ 1 from pow_eq_pow_of_modEq hc1 hzm.pow_eq_one, pow_one]
  · rw [key zl (by rw [mul_comm, pow_mul, hzl.pow_eq_one, one_pow])]
    exact pow_eq_pow_of_modEq hca hzl.pow_eq_one

/-! ## 2. `Γ`, the difference coordinate `T`, and `Λ = ℤ_p[[T]]`

`Γ ≅ ℤ_p` is **not** rebuilt here.  It is already the compatible-section object of
`ContinuingTower.padicTower`, and `ContinuingTower.padicSectionEquiv` is both directions of that
identification.  `gammaSectionEquiv` is that citation and nothing more. -/

section Gamma

variable (p : ℕ) [Fact p.Prime]

/-- [proved-derived; formal-checked] **`Γ ≅ ℤ_p` is C2's section object, cited not rebuilt.**
The Galois group of the `ℤ_p`-tower is the inverse limit of the `ℤ/p^n`, which is exactly
`ContinuingTower.padicTower`'s `CompatibleSection`; `ContinuingTower.padicSectionEquiv` supplies
both directions. -/
def gammaSectionEquiv : ℤ_[p] ≃ (padicTower p).CompatibleSection :=
  padicSectionEquiv p

/-- [definition] The Iwasawa algebra in the difference coordinate `T = γ − 1`.  `Λ = ℤ_p[[T]]`. -/
abbrev Lambda : Type := PowerSeries ℤ_[p]

/-- [definition] `ω_n = (1 + T)^{p^n} − 1` as a **polynomial**, so that its distinguished shape and
the rank of its quotient are theorems rather than descriptions.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs::{omega, check_distinguished,
omega_divides_omega_succ}`. -/
def omegaPoly (n : ℕ) : Polynomial ℤ_[p] := (Polynomial.X + 1) ^ (p ^ n) - 1

/-- [definition] The same element inside `Λ`. -/
def omega (n : ℕ) : Lambda p := (PowerSeries.X + 1) ^ (p ^ n) - 1

variable {p}

theorem monic_X_add_one : ((Polynomial.X : Polynomial ℤ_[p]) + 1).Monic := by
  simpa using Polynomial.monic_X_add_C (1 : ℤ_[p])

theorem natDegree_X_add_one_pow (k : ℕ) :
    (((Polynomial.X : Polynomial ℤ_[p]) + 1) ^ k).natDegree = k := by
  rw [Polynomial.natDegree_pow,
    show ((Polynomial.X : Polynomial ℤ_[p]) + 1).natDegree = 1 by
      simpa using Polynomial.natDegree_X_add_C (1 : ℤ_[p]), mul_one]

/-- [proved-derived; formal-checked] `ω_n` is monic. -/
theorem omegaPoly_monic (p : ℕ) [Fact p.Prime] (n : ℕ) : (omegaPoly p n).Monic := by
  refine Polynomial.Monic.sub_of_left (monic_X_add_one.pow _) ?_
  have h0 : 0 < (((Polynomial.X : Polynomial ℤ_[p]) + 1) ^ (p ^ n)).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, natDegree_X_add_one_pow]
    exact pow_pos (Fact.out (p := p.Prime)).pos n
  exact lt_of_le_of_lt Polynomial.degree_one_le h0

/-- [proved-derived; formal-checked] `ω_n` has degree exactly `p ^ n`. -/
theorem omegaPoly_natDegree (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (omegaPoly p n).natDegree = p ^ n := by
  unfold omegaPoly
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_add_one_pow]
  rw [natDegree_X_add_one_pow]
  simpa using pow_pos (Fact.out (p := p.Prime)).pos n

/-- [proved-derived; formal-checked] The coefficients of `ω_n` are the binomial coefficients, with
the constant one cancelled. -/
theorem omegaPoly_coeff (p : ℕ) [Fact p.Prime] (n i : ℕ) (hi : i ≠ 0) :
    (omegaPoly p n).coeff i = (((p ^ n).choose i : ℕ) : ℤ_[p]) := by
  unfold omegaPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
  simp [hi]

/-- [proved-derived; formal-checked] **`ω_n` is a distinguished polynomial of degree `p^n`.**
Monic; constant term zero; and every coefficient strictly below the top is divisible by `p`,
through `Nat.Prime.dvd_choose_pow`. -/
theorem omegaPoly_isDistinguished (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (omegaPoly p n).Monic ∧ (omegaPoly p n).natDegree = p ^ n ∧
      (omegaPoly p n).coeff 0 = 0 ∧
      ∀ i, i < p ^ n → (p : ℤ_[p]) ∣ (omegaPoly p n).coeff i := by
  refine ⟨omegaPoly_monic p n, omegaPoly_natDegree p n, ?_, ?_⟩
  · unfold omegaPoly
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
    simp
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · unfold omegaPoly
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
      simp
    · rw [omegaPoly_coeff p n i hipos.ne']
      exact_mod_cast Nat.cast_dvd_cast (α := ℤ_[p])
        ((Fact.out (p := p.Prime)).dvd_choose_pow hipos.ne' hi.ne)

/-- [proved-derived; formal-checked] **The divisibility chain.**  `ω_n ∣ ω_{n+1}`, because
`ω_{n+1} = Y^p − 1` for `Y = (1 + T)^{p^n}` and `ω_n = Y − 1`. -/
theorem omegaPoly_dvd_succ (p : ℕ) [Fact p.Prime] (n : ℕ) :
    omegaPoly p n ∣ omegaPoly p (n + 1) := by
  have hY : (((Polynomial.X : Polynomial ℤ_[p]) + 1) ^ (p ^ (n + 1)))
      = (((Polynomial.X : Polynomial ℤ_[p]) + 1) ^ (p ^ n)) ^ p := by
    rw [← pow_mul, pow_succ]
  unfold omegaPoly
  rw [hY]
  simpa using sub_dvd_pow_sub_pow (((Polynomial.X : Polynomial ℤ_[p]) + 1) ^ (p ^ n)) 1 p

/-- [proved-derived; formal-checked] The chain at every gap, by induction on the gap. -/
theorem omegaPoly_dvd_of_le (p : ℕ) [Fact p.Prime] {i j : ℕ} (h : i ≤ j) :
    omegaPoly p i ∣ omegaPoly p j := by
  induction j with
  | zero => simpa using (Nat.le_zero.1 h) ▸ dvd_refl (omegaPoly p 0)
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · exact dvd_trans (ih (Nat.lt_succ_iff.1 hlt)) (omegaPoly_dvd_succ p k)
    · have : i = k + 1 := le_antisymm h hge
      exact this ▸ dvd_refl _

/-- [proved-derived; formal-checked] The same chain inside `Λ`, through the coefficient-wise
inclusion of polynomials into power series. -/
theorem omega_dvd_of_le (p : ℕ) [Fact p.Prime] {i j : ℕ} (h : i ≤ j) :
    omega p i ∣ omega p j := by
  obtain ⟨c, hc⟩ := omegaPoly_dvd_of_le p h
  refine ⟨(c : Lambda p), ?_⟩
  have := congrArg (fun q : Polynomial ℤ_[p] => (q : Lambda p)) hc
  simpa [omega, omegaPoly] using this

/-- [proved-derived; formal-checked] **`Λ/ω_n` is free of rank `p^n` over `ℤ_p`**, at the
polynomial level where the statement is a theorem: `ℤ_p[T]/(ω_n)` has a power basis of dimension
`natDegree ω_n = p^n`.

[established-bounded; cited-classical] The corresponding statement for the power-series quotient
`Λ/(ω_n)` is the Weierstrass division theorem for complete local rings (Washington,
*Introduction to Cyclotomic Fields*, 2nd ed., Thm 7.3 and its corollaries); it is **not** proved
here, and no declaration in this file asserts it. -/
theorem omegaQuotient_finrank (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank ℤ_[p] (AdjoinRoot (omegaPoly p n)) = p ^ n := by
  rw [(AdjoinRoot.powerBasis' (omegaPoly_monic p n)).finrank,
    AdjoinRoot.powerBasis'_dim, omegaPoly_natDegree]

/-- [definition] The group ring `ℤ_p[Γ/Γ_n] = ℤ_p[ℤ/p^n]` in its polynomial presentation
`ℤ_p[γ]/(γ^{p^n} − 1)`. -/
def groupRingPoly (p : ℕ) [Fact p.Prime] (n : ℕ) : Polynomial ℤ_[p] :=
  Polynomial.X ^ (p ^ n) - 1

theorem groupRingPoly_monic (p : ℕ) [Fact p.Prime] (n : ℕ) : (groupRingPoly p n).Monic := by
  refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
  have h0 : 0 < ((Polynomial.X : Polynomial ℤ_[p]) ^ (p ^ n)).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, Polynomial.natDegree_X_pow]
    exact pow_pos (Fact.out (p := p.Prime)).pos n
  exact lt_of_le_of_lt Polynomial.degree_one_le h0

theorem groupRingPoly_natDegree (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (groupRingPoly p n).natDegree = p ^ n := by
  unfold groupRingPoly
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
  rw [Polynomial.natDegree_X_pow]
  simpa using pow_pos (Fact.out (p := p.Prime)).pos n

/-- [proved-derived; formal-checked] The substitution `γ = 1 + T` carries `γ^{p^n} − 1` to `ω_n`,
as polynomials. -/
theorem omegaPoly_eq_groupRingPoly_comp (p : ℕ) [Fact p.Prime] (n : ℕ) :
    omegaPoly p n = (groupRingPoly p n).comp (Polynomial.X + 1) := by
  simp [omegaPoly, groupRingPoly]

/-- [proved-derived; formal-checked] And `T = γ − 1` carries it back. -/
theorem groupRingPoly_eq_omegaPoly_comp (p : ℕ) [Fact p.Prime] (n : ℕ) :
    groupRingPoly p n = (omegaPoly p n).comp (Polynomial.X - 1) := by
  simp [omegaPoly, groupRingPoly, sub_add_cancel]

/-- [proved-derived; formal-checked] **`Λ/ω_n ≅ ℤ_p[ℤ/p^n]`, at the level where it is a theorem.**
The two quotients are isomorphic as `ℤ_p`-algebras, through the substitution `γ = 1 + T` and its
inverse `T = γ − 1`; `ℤ_p[γ]/(γ^{p^n} − 1)` **is** the group ring of `Γ/Γ_n ≅ ℤ/p^n`, so this is
the finite level of the Iwasawa algebra with its group-ring meaning attached.

[established-bounded; cited-classical] The statement for the *power-series* quotient
`PowerSeries ℤ_[p] ⧸ (ω_n)` is Weierstrass division (Washington, *Introduction to Cyclotomic
Fields*, 2nd ed., Thm 7.3); it is **not** proved here and nothing in this file asserts it. -/
def omegaGroupRingEquiv (p : ℕ) [Fact p.Prime] (n : ℕ) :
    AdjoinRoot (omegaPoly p n) ≃ₐ[ℤ_[p]] AdjoinRoot (groupRingPoly p n) := by
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId ℤ_[p] (AdjoinRoot (groupRingPoly p n)))
      (AdjoinRoot.root (groupRingPoly p n) - 1) ?_)
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId ℤ_[p] (AdjoinRoot (omegaPoly p n)))
      (AdjoinRoot.root (omegaPoly p n) + 1) ?_) ?_ ?_
  · show (Polynomial.aeval (AdjoinRoot.root (groupRingPoly p n) - 1)) (omegaPoly p n) = 0
    rw [omegaPoly_eq_groupRingPoly_comp, Polynomial.aeval_comp]
    simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · show (Polynomial.aeval (AdjoinRoot.root (omegaPoly p n) + 1)) (groupRingPoly p n) = 0
    rw [groupRingPoly_eq_omegaPoly_comp, Polynomial.aeval_comp]
    simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · refine AdjoinRoot.algHom_ext ?_
    simp [AdjoinRoot.liftAlgHom_root]
  · refine AdjoinRoot.algHom_ext ?_
    simp [AdjoinRoot.liftAlgHom_root]

/-- [proved-derived; formal-checked] Consequently both presentations are free of rank `p^n` over
`ℤ_p`. -/
theorem groupRingQuotient_finrank_eq_omegaQuotient_finrank (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank ℤ_[p] (AdjoinRoot (groupRingPoly p n))
      = Module.finrank ℤ_[p] (AdjoinRoot (omegaPoly p n)) := by
  rw [(AdjoinRoot.powerBasis' (groupRingPoly_monic p n)).finrank, AdjoinRoot.powerBasis'_dim,
    groupRingPoly_natDegree, omegaQuotient_finrank]

end Gamma

/-! ## 3. An Iwasawa module **is** a `Tower`

The construction is not special to `Λ`: any antitone filtration of a module is a `Tower` in the
sense of `Foundation/ContinuingTower.lean`, its `CompatibleSection`s are the inverse limit, and the
section map from the module is injective **exactly** when the filtration is separated.  The
`ω`-filtration is the instance. -/

section QuotientTower

/-- [proved-derived; formal-checked] **Every additive homomorphism is a C4 `Transition` whose
retained residual is its kernel.**  `reopen` runs a chosen set-theoretic section of the map and
adds the retained kernel element back; `reopen_apply` then holds on every presented pair, which is
exactly the domain law `Transition` states.  This is what makes a lossy arithmetic restriction a
transition rather than a bare map. -/
def transitionOfHom {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    Transition A B where
  Residual := ↥f.ker
  apply := f
  residual := fun x => ⟨x - Function.invFun f (f x), by
    have : f (Function.invFun f (f x)) = f x := Function.invFun_eq ⟨x, rfl⟩
    simp [AddMonoidHom.mem_ker, this]⟩
  reopen := fun b r => Function.invFun f b + (r : A)
  reopen_apply := fun x => by simp

@[simp] theorem transitionOfHom_apply {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (x : A) : (transitionOfHom f).apply x = f x := rfl

/-- [proved-derived; formal-checked] The retained residual **is** the kernel, by `rfl`. -/
theorem transitionOfHom_residual {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) : (transitionOfHom f).Residual = ↥f.ker := rfl

/-- [proved-derived; formal-checked] The residual is trivial exactly when the map drops nothing. -/
theorem transitionOfHom_residual_subsingleton_iff {A : Type u} {B : Type v} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) :
    Subsingleton ↥f.ker ↔ Function.Injective f := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : (⟨a, ha⟩ : ↥f.ker) = ⟨0, f.map_zero⟩ := h.elim _ _
    exact congrArg Subtype.val this
  · intro h
    refine ⟨fun x y => ?_⟩
    have hker : ∀ z : ↥f.ker, (z : A) = 0 := fun z =>
      h (by rw [map_zero]; exact (AddMonoidHom.mem_ker).1 z.2)
    exact Subtype.ext ((hker x).trans (hker y).symm)

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- [definition] **The tower of an antitone filtration.**  `Face n = M ⧸ N n`; the restriction from
a finer chart to a coarser one is the quotient map that the inclusion `N j ≤ N i` supplies.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs::{IwasawaTower, OmegaRestriction,
FiniteSpecialization}`. -/
def quotientTower (N : ℕ → Submodule R M) (hN : Antitone N) : Tower.{0, v} ℕ where
  Face := fun n => M ⧸ N n
  restrict := fun {i j} h => Submodule.mapQ (N j) (N i) LinearMap.id (fun _ hy => hN h hy)
  restrict_refl := by
    intro i x
    refine Quotient.inductionOn' x fun y => ?_
    rfl
  restrict_trans := by
    intro i j k _ _ x
    refine Quotient.inductionOn' x fun y => ?_
    rfl

@[simp] theorem quotientTower_restrict_mk (N : ℕ → Submodule R M) (hN : Antitone N)
    {i j : ℕ} (h : i ≤ j) (y : M) :
    (quotientTower N hN).restrict h (Submodule.Quotient.mk y : M ⧸ N j)
      = (Submodule.Quotient.mk y : M ⧸ N i) := rfl

/-- [proved-derived; formal-checked] Every element of the module is a continuing object of the
tower: it presents one face at each level and the faces agree under every restriction. -/
def quotientTowerSection (N : ℕ → Submodule R M) (hN : Antitone N) (x : M) :
    (quotientTower N hN).CompatibleSection where
  witness := fun _ => Submodule.Quotient.mk x
  compatible := fun _ => rfl

/-- [proved-derived; formal-checked] **Separatedness is exactly injectivity of the section map.**
The module embeds in its own tower of finite specializations iff the filtration's intersection is
trivial; nothing is assumed about completeness. -/
theorem quotientTowerSection_injective_iff (N : ℕ → Submodule R M) (hN : Antitone N) :
    Function.Injective (quotientTowerSection N hN) ↔ (⨅ n, N n) = ⊥ := by
  constructor
  · intro hinj
    refine le_antisymm (fun x hx => ?_) bot_le
    have hmem : ∀ n, x ∈ N n := fun n => (Submodule.mem_iInf _).1 hx n
    have : quotientTowerSection N hN x = quotientTowerSection N hN 0 := by
      refine Tower.CompatibleSection.ext (fun n => ?_)
      show (Submodule.Quotient.mk x : M ⧸ N n) = Submodule.Quotient.mk 0
      rw [Submodule.Quotient.eq]
      simpa using hmem n
    simpa using hinj this
  · intro hbot x y hxy
    have hmem : ∀ n, x - y ∈ N n := by
      intro n
      have := congrArg (fun s : (quotientTower N hN).CompatibleSection => s.witness n) hxy
      exact (Submodule.Quotient.eq (N n)).1 this
    have : x - y ∈ (⨅ n, N n) := (Submodule.mem_iInf _).2 hmem
    rw [hbot] at this
    exact sub_eq_zero.1 (by simpa using this)

/-- [definition] **Completeness is a hypothesis, never asserted.**  A filtered module is complete
for its own tower when every continuing object of the tower is an element of the module.  Nothing
in this file proves this for `Λ`-modules; where it is needed it is carried. -/
def QuotientTowerComplete (N : ℕ → Submodule R M) (hN : Antitone N) : Prop :=
  Function.Surjective (quotientTowerSection N hN)

/-- [proved-derived; formal-checked] Separated and complete together is the bijection: the module
**is** the tower's continuing-object population, with neither half assumed. -/
theorem quotientTowerSection_bijective_of (N : ℕ → Submodule R M) (hN : Antitone N)
    (hsep : (⨅ n, N n) = ⊥) (hcom : QuotientTowerComplete N hN) :
    Function.Bijective (quotientTowerSection N hN) :=
  ⟨(quotientTowerSection_injective_iff N hN).2 hsep, hcom⟩

/-- [counterexample; formal-checked] Separatedness is not automatic.  For the constant filtration
`N n = ⊤` on a nontrivial module the section map is **not** injective, so
`quotientTowerSection_injective_iff` is not a vacuous criterion. -/
theorem quotientTowerSection_not_injective_of_top [Nontrivial M] :
    ¬ Function.Injective (quotientTowerSection (R := R) (M := M) (fun _ => ⊤)
      (show Antitone (fun _ : ℕ => (⊤ : Submodule R M)) from fun _ _ _ => le_refl _)) := by
  rw [quotientTowerSection_injective_iff]
  intro h
  rw [show (⨅ _ : ℕ, (⊤ : Submodule R M)) = ⊤ by simp] at h
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial M)
  exact hab (by
    have ha : a ∈ (⊥ : Submodule R M) := h ▸ Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule R M) := h ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb])

end QuotientTower

section OmegaTower

variable (p : ℕ) [Fact p.Prime] (M : Type v) [AddCommGroup M] [Module (Lambda p) M]

/-- [definition] The `ω_n`-step of the filtration: `ω_n M`. -/
def omegaSubmodule (n : ℕ) : Submodule (Lambda p) M :=
  (Ideal.span {omega p n}) • (⊤ : Submodule (Lambda p) M)

/-- [proved-derived; formal-checked] The filtration is antitone, by the divisibility chain
`omega_dvd_of_le`. -/
theorem omegaSubmodule_antitone : Antitone (omegaSubmodule p M) := by
  intro i j h
  refine Submodule.smul_mono_left ?_
  rw [Ideal.span_singleton_le_span_singleton]
  exact omega_dvd_of_le p h

/-- [definition] **The Iwasawa tower of a `Λ`-module**: `Face n = M / ω_n M`, restriction the
canonical quotient map.  This is `ContinuingTower.Tower`, not a parallel family.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs::{IwasawaTower,
LambdaPresentation::specialize, FiniteSpecialization}`. -/
def omegaTower : Tower.{0, v} ℕ :=
  quotientTower (omegaSubmodule p M) (omegaSubmodule_antitone p M)

/-- [proved-derived; formal-checked] Every element of an Iwasawa module is a continuing object of
its own `ω`-tower. -/
def omegaTowerSection (x : M) : (omegaTower p M).CompatibleSection :=
  quotientTowerSection (omegaSubmodule p M) (omegaSubmodule_antitone p M) x

/-- [proved-derived; formal-checked] **The precise form that holds.**  The elements of `M` are
exactly the compatible sections of its own `ω`-tower when `M` is `ω`-adically separated
(injectivity) and complete (surjectivity).  Separatedness is proved equivalent to injectivity
outright; completeness is carried as the hypothesis it is. -/
theorem omegaTowerSection_injective_iff :
    Function.Injective (omegaTowerSection p M) ↔ (⨅ n, omegaSubmodule p M n) = ⊥ :=
  quotientTowerSection_injective_iff _ _

end OmegaTower

/-! ## 4. Levelwise Selmer, with the control kernel and cokernel **retained**

`Millennium/SelmerCalculus.lean` owns `selmer = ⋂ᵢ rᵢ⁻¹(Lᵢ)` over abstract additive groups with an
abstract receiver family.  That is the level of abstraction used here, and it is stated plainly: no
Galois cohomology of an elliptic curve is constructed, and none is claimed.  What is added is the
tower direction — restriction up, corestriction down, `cores ∘ res = [degree]` — and the control
map to the limit, whose kernel and cokernel are **carried as data** rather than demanded to vanish.
That is C4's residual discipline applied arithmetically. -/

section LevelwiseSelmer

/-- [definition] A levelwise Selmer family.  At each layer `n` the abstract global module `A n`
carries the receiver family `r n` with its local conditions `cond n`; `res` is restriction up the
tower, `cores` corestriction down it, and `cores_res` is the degree law.  `cores` is what makes the
family a `Tower`. -/
structure SelmerTowerData (A : ℕ → Type v) [∀ n, AddCommGroup (A n)]
    (ι : Type) (T : ℕ → ι → Type v) [∀ n i, AddCommGroup (T n i)] where
  /-- the receiver family at each level -/
  r : ∀ n i, A n →+ T n i
  /-- what each receiver admits at each level -/
  cond : ∀ n i, AddSubgroup (T n i)
  /-- restriction up the tower -/
  res : ∀ {i j : ℕ}, i ≤ j → A i →+ A j
  /-- corestriction down the tower -/
  cores : ∀ {i j : ℕ}, i ≤ j → A j →+ A i
  /-- the layer degree -/
  degree : ℕ → ℕ → ℕ
  /-- restriction carries admitted classes to admitted classes -/
  res_admits : ∀ {i j : ℕ} (h : i ≤ j) {x : A i},
    x ∈ Soma.Holonics.Millennium.SelmerCalculus.selmer (r i) (cond i) →
      res h x ∈ Soma.Holonics.Millennium.SelmerCalculus.selmer (r j) (cond j)
  /-- and so does corestriction -/
  cores_admits : ∀ {i j : ℕ} (h : i ≤ j) {x : A j},
    x ∈ Soma.Holonics.Millennium.SelmerCalculus.selmer (r j) (cond j) →
      cores h x ∈ Soma.Holonics.Millennium.SelmerCalculus.selmer (r i) (cond i)
  /-- corestricting to the same level changes nothing -/
  cores_refl : ∀ (i : ℕ) (x : A i), cores (le_refl i) x = x
  /-- corestriction composes -/
  cores_trans : ∀ {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : A k),
    cores hij (cores hjk x) = cores (le_trans hij hjk) x
  /-- **the degree law**: `cores ∘ res` is multiplication by the layer degree -/
  cores_res : ∀ {i j : ℕ} (h : i ≤ j) (x : A i), cores h (res h x) = (degree i j) • x

namespace SelmerTowerData

variable {A : ℕ → Type v} [∀ n, AddCommGroup (A n)]
variable {ι : Type} {T : ℕ → ι → Type v} [∀ n i, AddCommGroup (T n i)]
variable (S : SelmerTowerData A ι T)

/-- [definition] The Selmer group at one layer, through `SelmerCalculus.selmer` — cited, not
rebuilt. -/
def level (n : ℕ) : AddSubgroup (A n) :=
  Soma.Holonics.Millennium.SelmerCalculus.selmer (S.r n) (S.cond n)

/-- [proved-derived; formal-checked] **The levelwise Selmer family is a `Tower`.**  Faces are the
layers' Selmer groups; the restriction from finer to coarser is corestriction. -/
def tower : Tower.{0, v} ℕ where
  Face := fun n => ↥(S.level n)
  restrict := fun {_ _} h x => ⟨S.cores h x.1, S.cores_admits h x.2⟩
  restrict_refl := fun i x => Subtype.ext (S.cores_refl i x.1)
  restrict_trans := fun hij hjk x => Subtype.ext (S.cores_trans hij hjk x.1)

/-- [proved-derived; formal-checked] The degree law read on the Selmer groups themselves: going up
and coming back down multiplies by the layer degree. -/
theorem tower_cores_res {i j : ℕ} (h : i ≤ j) (x : ↥(S.level i)) :
    S.cores h (S.res h x.1) = (S.degree i j) • x.1 :=
  S.cores_res h x.1

end SelmerTowerData

/-- [definition] **The control map, with both residuals retained.**  `ctrl n` sends the layer's
Selmer group into the declared `Γ_n`-invariants of the limit object.  Neither the kernel nor the
cokernel is required to vanish: both are readable from this data, and `ControlData.transition`
presents the kernel as a C4 `Transition` residual. -/
structure ControlData {A : ℕ → Type v} [∀ n, AddCommGroup (A n)]
    {ι : Type} {T : ℕ → ι → Type v} [∀ n i, AddCommGroup (T n i)]
    (S : SelmerTowerData A ι T) (Ainf : Type v) [AddCommGroup Ainf] where
  /-- the control map at each level -/
  ctrl : ∀ n, ↥(S.level n) →+ Ainf
  /-- the declared `Γ_n`-invariant subgroup of the limit -/
  invariants : ℕ → AddSubgroup Ainf
  /-- the control map lands in them -/
  lands : ∀ n x, ctrl n x ∈ invariants n

namespace ControlData

variable {A : ℕ → Type v} [∀ n, AddCommGroup (A n)]
variable {ι : Type} {T : ℕ → ι → Type v} [∀ n i, AddCommGroup (T n i)]
variable {S : SelmerTowerData A ι T} {Ainf : Type v} [AddCommGroup Ainf]
variable (C : ControlData S Ainf)

/-- [definition] The **retained control kernel** at one level. -/
def kernel (n : ℕ) : AddSubgroup ↥(S.level n) := (C.ctrl n).ker

/-- [definition] The image of the control map at one level. -/
def image (n : ℕ) : AddSubgroup Ainf := (C.ctrl n).range

/-- [definition] The **retained control cokernel** at one level: the declared invariants modulo
what the level actually reaches. -/
abbrev cokernel (n : ℕ) : Type v :=
  ↥(C.invariants n) ⧸ (C.image n).addSubgroupOf (C.invariants n)

/-- [proved-derived; formal-checked] The retained cokernel is trivial exactly when the level
reaches every declared invariant, so the second clause of `control_bijective_iff` below **is**
cokernel vanishing and the cokernel is not a decoration. -/
theorem cokernel_subsingleton_iff (n : ℕ) :
    Subsingleton (C.cokernel n) ↔ ∀ y ∈ C.invariants n, y ∈ C.image n := by
  constructor
  · intro h y hy
    have h0 : (QuotientAddGroup.mk (⟨y, hy⟩ : ↥(C.invariants n)) : C.cokernel n) = 0 :=
      h.elim _ _
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
    exact h0
  · intro h
    refine ⟨fun a b => ?_⟩
    refine QuotientAddGroup.induction_on a fun x => ?_
    refine QuotientAddGroup.induction_on b fun y => ?_
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
    exact h _ (x - y).2

/-- [definition] The control map as a C4 `Transition`, whose retained residual is exactly the
control kernel. -/
def transition (n : ℕ) : Transition ↥(S.level n) Ainf := transitionOfHom (C.ctrl n)

/-- [proved-derived; formal-checked] The transition's residual **is** the control kernel, by
`rfl`. -/
theorem transition_residual (n : ℕ) : (C.transition n).Residual = ↥(C.kernel n) := rfl

/-- [proved-derived; formal-checked] The control map at one level is injective exactly when its
retained kernel is trivial — the kernel is not a bound, it is the obstruction itself. -/
theorem control_injective_iff (n : ℕ) :
    Function.Injective (C.ctrl n) ↔ Subsingleton ↥(C.kernel n) :=
  (transitionOfHom_residual_subsingleton_iff (C.ctrl n)).symm

/-- [proved-derived; formal-checked] **The control map is an isomorphism onto the invariants
exactly when both retained residuals vanish.**  Neither half is assumed anywhere. -/
theorem control_bijective_iff (n : ℕ) :
    Function.Bijective (fun x : ↥(S.level n) => (⟨C.ctrl n x, C.lands n x⟩ : ↥(C.invariants n)))
      ↔ (Subsingleton ↥(C.kernel n) ∧ ∀ y ∈ C.invariants n, y ∈ C.image n) := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(C.control_injective_iff n).1 (fun a b hab => hinj (Subtype.ext hab)), ?_⟩
    intro y hy
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨hker, hcok⟩
    refine ⟨fun a b hab => (C.control_injective_iff n).2 hker (congrArg Subtype.val hab), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hcok y hy
    exact ⟨x, Subtype.ext hx⟩

/-- [proved-derived; formal-checked] **The control statement of C8, in the two retained residuals
themselves.**  The control map is an isomorphism onto the declared invariants exactly when its
kernel and its cokernel both vanish — and `theControlKernelAndCokernelAreBothRetained` below shows
neither vanishing is automatic. -/
theorem control_bijective_iff_residuals (n : ℕ) :
    Function.Bijective (fun x : ↥(S.level n) => (⟨C.ctrl n x, C.lands n x⟩ : ↥(C.invariants n)))
      ↔ (Subsingleton ↥(C.kernel n) ∧ Subsingleton (C.cokernel n)) := by
  rw [C.control_bijective_iff n, C.cokernel_subsingleton_iff n]

end ControlData

/-! ### A family in which both control residuals are genuinely nonzero -/

/-- [definition] The flattest possible levelwise family: one abstract group at every level, one
receiver that admits everything, identity restriction and corestriction, layer degree `1`.  It
exists only to carry the control counterexample, and it is a real `SelmerTowerData`. -/
def flatSelmerTower :
    SelmerTowerData (fun _ => ZMod 2 × ZMod 2) PUnit (fun _ _ => PUnit) where
  r := fun _ _ => 0
  cond := fun _ _ => ⊤
  res := fun _ => AddMonoidHom.id _
  cores := fun _ => AddMonoidHom.id _
  degree := fun _ _ => 1
  res_admits := by
    intro i j h x _
    rw [Soma.Holonics.Millennium.SelmerCalculus.mem_selmer]
    intro _
    exact AddSubgroup.mem_top _
  cores_admits := by
    intro i j h x _
    rw [Soma.Holonics.Millennium.SelmerCalculus.mem_selmer]
    intro _
    exact AddSubgroup.mem_top _
  cores_refl := fun _ _ => rfl
  cores_trans := fun _ _ _ => rfl
  cores_res := fun _ x => by simp

/-- [proved-derived; formal-checked] Every class is admitted at every level of the flat family, so
its Selmer group is the whole group. -/
theorem flatSelmerTower_level (n : ℕ) : flatSelmerTower.level n = ⊤ := by
  refine eq_top_iff.2 (fun x _ => ?_)
  rw [SelmerTowerData.level, Soma.Holonics.Millennium.SelmerCalculus.mem_selmer]
  intro _
  exact AddSubgroup.mem_top _

/-- [definition] A control map on that family which is neither injective nor surjective onto its
declared invariants: it forgets the second coordinate. -/
def flatControl : ControlData flatSelmerTower (ZMod 2 × ZMod 2) where
  ctrl := fun _ => ((AddMonoidHom.fst (ZMod 2) (ZMod 2)).prod 0).comp
    (AddSubgroup.subtype _)
  invariants := fun _ => ⊤
  lands := fun _ _ => AddSubgroup.mem_top _

/-- [counterexample; formal-checked] **Both control residuals are retained and both are nonzero.**
The control map's kernel contains a nonzero class, and its declared invariants contain a class the
level does not reach.  C8's control statement is therefore *not* "the control map is an
isomorphism"; it is "the two residuals are carried". -/
theorem theControlKernelAndCokernelAreBothRetained (n : ℕ) :
    (¬ Subsingleton ↥(flatControl.kernel n)) ∧
      ∃ y ∈ flatControl.invariants n, y ∉ flatControl.image n := by
  have hmem : ∀ z : ZMod 2 × ZMod 2, z ∈ flatSelmerTower.level n := by
    rw [flatSelmerTower_level]
    exact fun _ => AddSubgroup.mem_top _
  constructor
  · intro hsub
    have hinj : Function.Injective (flatControl.ctrl n) :=
      (flatControl.control_injective_iff n).2 hsub
    have hval : (⟨((0 : ZMod 2), (1 : ZMod 2)), hmem _⟩ : ↥(flatSelmerTower.level n))
        = ⟨((0 : ZMod 2), (0 : ZMod 2)), hmem _⟩ := hinj rfl
    have hcoe : ((0 : ZMod 2), (1 : ZMod 2)) = ((0 : ZMod 2), (0 : ZMod 2)) :=
      congrArg Subtype.val hval
    exact absurd hcoe (by decide)
  · refine ⟨((0 : ZMod 2), (1 : ZMod 2)), AddSubgroup.mem_top _, ?_⟩
    rintro ⟨x, hx⟩
    have h2 : ((0 : ZMod 2), (1 : ZMod 2)).2 = (0 : ZMod 2) := by rw [← hx]; rfl
    exact absurd h2 (by decide)

end LevelwiseSelmer

/-! ## 5. The characteristic face: conditional on structure data, and blind above codimension one -/

section CharacteristicFace

variable (p : ℕ) [Fact p.Prime]

/-- [hypothesis] **The structure theorem, supplied as data and never assumed.**  `StructureData`
carries an elementary module `⨁ Λ/(f_i)` together with the pseudo-isomorphism into it, presented by
its two finite residuals.  There is no `axiom` here: a caller who has no such datum has no
characteristic face, and the counterexamples below are *unconditional* because they construct the
datum rather than assume it. -/
structure StructureData (M : Type v) [AddCommGroup M] [Module (Lambda p) M] where
  /-- how many elementary summands -/
  rank : ℕ
  /-- the elementary divisors -/
  divisor : Fin rank → Lambda p
  /-- each is nonzero, so the face is a genuine codimension-one datum -/
  divisor_ne_zero : ∀ i, divisor i ≠ 0
  /-- the pseudo-isomorphism into the elementary module -/
  toElementary : M →ₗ[Lambda p]
    ((i : Fin rank) → (Lambda p ⧸ (Ideal.span {divisor i} : Ideal (Lambda p))))
  /-- its kernel is finite -/
  kernelFinite : Finite ↥(LinearMap.ker toElementary)
  /-- and so is its cokernel -/
  cokernelFinite :
    Finite (((i : Fin rank) → (Lambda p ⧸ (Ideal.span {divisor i} : Ideal (Lambda p))))
      ⧸ LinearMap.range toElementary)

/-- [definition] **The characteristic face** of a module *through* supplied structure data: the
ideal generated by the product of the elementary divisors.  It is a receiver reading of the module
and never its identity — which is what the next two theorems prove. -/
def StructureData.characteristicFace {M : Type v} [AddCommGroup M] [Module (Lambda p) M]
    (D : StructureData p M) : Ideal (Lambda p) :=
  Ideal.span {∏ i, D.divisor i}

/-! ### Counterexample one: `Λ/(T²)` against `Λ/(T) ⊕ Λ/(T)` -/

/-- [definition] `Λ/(T²)`, presented as its own elementary module. -/
abbrev SquareModule : Type :=
  (_ : Fin 1) → (Lambda p ⧸ (Ideal.span {(PowerSeries.X : Lambda p) ^ 2} : Ideal (Lambda p)))

/-- [definition] `Λ/(T) ⊕ Λ/(T)`, presented as its own elementary module. -/
abbrev SplitModule : Type :=
  (_ : Fin 2) → (Lambda p ⧸ (Ideal.span {(PowerSeries.X : Lambda p)} : Ideal (Lambda p)))

theorem powerSeriesX_ne_zero : (PowerSeries.X : Lambda p) ≠ 0 := PowerSeries.X_ne_zero

/-- [definition] Structure data for `Λ/(T²)`: it *is* its elementary module, so the
pseudo-isomorphism is the identity and both residuals are trivial. -/
def squareStructure : StructureData p (SquareModule p) where
  rank := 1
  divisor := fun _ => (PowerSeries.X : Lambda p) ^ 2
  divisor_ne_zero := fun _ => pow_ne_zero 2 (powerSeriesX_ne_zero p)
  toElementary := LinearMap.id
  kernelFinite := by
    rw [LinearMap.ker_id]
    exact Finite.of_subsingleton
  cokernelFinite := by
    rw [LinearMap.range_id]
    refine @Finite.of_subsingleton _ ⟨fun a b => ?_⟩
    refine Quotient.inductionOn₂' a b fun x y => ?_
    exact (Submodule.Quotient.eq _).2 Submodule.mem_top

/-- [definition] Structure data for `Λ/(T) ⊕ Λ/(T)`, the same way. -/
def splitStructure : StructureData p (SplitModule p) where
  rank := 2
  divisor := fun _ => (PowerSeries.X : Lambda p)
  divisor_ne_zero := fun _ => powerSeriesX_ne_zero p
  toElementary := LinearMap.id
  kernelFinite := by
    rw [LinearMap.ker_id]
    exact Finite.of_subsingleton
  cokernelFinite := by
    rw [LinearMap.range_id]
    refine @Finite.of_subsingleton _ ⟨fun a b => ?_⟩
    refine Quotient.inductionOn₂' a b fun x y => ?_
    exact (Submodule.Quotient.eq _).2 Submodule.mem_top

/-- [proved-derived; formal-checked] The characteristic face of `Λ/(T²)` is `(T²)`. -/
theorem squareStructure_characteristicFace :
    (squareStructure p).characteristicFace = Ideal.span {(PowerSeries.X : Lambda p) ^ 2} := by
  show Ideal.span {∏ _ : Fin 1, (PowerSeries.X : Lambda p) ^ 2} = _
  simp

/-- [proved-derived; formal-checked] The characteristic face of `Λ/(T) ⊕ Λ/(T)` is also `(T²)`. -/
theorem splitStructure_characteristicFace :
    (splitStructure p).characteristicFace = Ideal.span {(PowerSeries.X : Lambda p) ^ 2} := by
  show Ideal.span {∏ _ : Fin 2, (PowerSeries.X : Lambda p)} = _
  simp

/-- [proved-derived; formal-checked] `T` annihilates `Λ/(T) ⊕ Λ/(T)` outright. -/
theorem splitModule_annihilated (y : SplitModule p) : (PowerSeries.X : Lambda p) • y = 0 := by
  funext i
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    (Ideal.span {(PowerSeries.X : Lambda p)} : Ideal (Lambda p)) (y i)
  show (PowerSeries.X : Lambda p) • y i = 0
  rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mem_span_singleton.2 ⟨a, rfl⟩

/-- [proved-derived; formal-checked] `T` does **not** annihilate `Λ/(T²)`: the class of `T` there is
nonzero because `T² ∤ T`, read off the coefficient of degree one. -/
theorem squareModule_not_annihilated :
    (PowerSeries.X : Lambda p) •
      (fun _ => Submodule.Quotient.mk 1 : SquareModule p) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, Pi.zero_apply] at h0
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_span_singleton] at h0
  rw [PowerSeries.X_pow_dvd_iff] at h0
  have h1 := h0 1 (by norm_num)
  simp [PowerSeries.coeff_X] at h1

/-- [counterexample; formal-checked] **The characteristic face does not determine the module.**
`Λ/(T²)` and `Λ/(T) ⊕ Λ/(T)` carry the *same* characteristic face `(T²)` and are not isomorphic:
`T` kills the second and not the first.  This is
`ContinuingTower.theOrderFaceDoesNotDetermineTheModule`'s separation — `ℤ/4` against `ℤ/2 ⊕ ℤ/2` —
now over `Λ`, and it is unconditional: both structure data are constructed, not assumed.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs` verifies the same separation
numerically — equal orders at every level, different Smith invariants. -/
theorem theCharacteristicFaceDoesNotDetermineTheModule :
    (squareStructure p).characteristicFace = (splitStructure p).characteristicFace ∧
      IsEmpty (SquareModule p ≃ₗ[Lambda p] SplitModule p) := by
  constructor
  · rw [squareStructure_characteristicFace, splitStructure_characteristicFace]
  · refine ⟨fun e => ?_⟩
    have hmap : e ((PowerSeries.X : Lambda p) •
        (fun _ => Submodule.Quotient.mk 1 : SquareModule p))
        = (PowerSeries.X : Lambda p) • e (fun _ => Submodule.Quotient.mk 1) := map_smul e _ _
    rw [splitModule_annihilated] at hmap
    exact squareModule_not_annihilated p (e.injective (hmap.trans (map_zero e).symm))

/-! ### Counterexample two: a pseudo-null residue the face cannot see -/

/-- [definition] The ring map `Λ → 𝔽_p` that reduces the constant term. -/
def lambdaToZMod : Lambda p →+* ZMod p :=
  (PadicInt.toZMod).comp (PowerSeries.constantCoeff (R := ℤ_[p]))

/-- [definition] `𝔽_p = Λ/(p, T)` as a `Λ`-module, through that map.  It is nonzero, finite, and
annihilated by both `p` and `T`: a pseudo-null module. -/
def PseudoNull : Type := ZMod p

namespace PseudoNull

instance : CommRing (PseudoNull p) := inferInstanceAs (CommRing (ZMod p))

instance : Module (ZMod p) (PseudoNull p) := inferInstanceAs (Module (ZMod p) (ZMod p))

instance : Module (Lambda p) (PseudoNull p) := Module.compHom (PseudoNull p) (lambdaToZMod p)

instance : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩

instance : Finite (PseudoNull p) := inferInstanceAs (Finite (ZMod p))

instance : Nontrivial (PseudoNull p) := by
  have : Fact (1 < p) := ⟨(Fact.out (p := p.Prime)).one_lt⟩
  exact inferInstanceAs (Nontrivial (ZMod p))

end PseudoNull

/-- [proved-derived; formal-checked] `p` and `T` both annihilate the pseudo-null module: its
support has codimension two. -/
theorem pseudoNull_annihilated (x : PseudoNull p) :
    ((p : Lambda p)) • x = 0 ∧ (PowerSeries.X : Lambda p) • x = 0 := by
  constructor
  · show (lambdaToZMod p (p : Lambda p)) • x = 0
    have hz : lambdaToZMod p (p : Lambda p) = 0 := by
      simp [lambdaToZMod, map_natCast]
    rw [hz, zero_smul]
  · show (lambdaToZMod p (PowerSeries.X : Lambda p)) • x = 0
    have hz : lambdaToZMod p (PowerSeries.X : Lambda p) = 0 := by
      simp [lambdaToZMod]
    rw [hz, zero_smul]

/-- [definition] Structure data for the pseudo-null module: its elementary module is **zero**, the
pseudo-isomorphism is the zero map, and both residuals are finite because the module itself is. -/
def pseudoNullStructure : StructureData p (PseudoNull p) where
  rank := 0
  divisor := Fin.elim0
  divisor_ne_zero := fun i => i.elim0
  toElementary := 0
  kernelFinite := by
    have hsub : Finite (PseudoNull p) := inferInstance
    exact Subtype.finite
  cokernelFinite := by
    refine @Finite.of_subsingleton _ ⟨fun a b => ?_⟩
    refine Quotient.inductionOn₂' a b fun x y => ?_
    exact congrArg _ (funext fun i => i.elim0)

/-- [counterexample; formal-checked] **The codimension-one face is blind above codimension one.**
A nonzero finite `Λ`-module, annihilated by both `p` and `T`, whose characteristic face is the unit
ideal.  No characteristic ideal distinguishes it from the zero module, and the module is not zero.

Rust counterpart: `crates/holonic-engine/src/iwasawa_tower.rs` exhibits `Λ/(p, T)` with constant
order `p` at every level and trivial characteristic datum. -/
theorem thePseudoNullResidueIsInvisibleToTheFace :
    (pseudoNullStructure p).characteristicFace = ⊤ ∧
      Nontrivial (PseudoNull p) ∧ Finite (PseudoNull p) := by
  refine ⟨?_, inferInstance, inferInstance⟩
  simp [StructureData.characteristicFace, pseudoNullStructure]

end CharacteristicFace

/-! ## 6. `μ` and `λ` as growth exponents, never entropy -/

section Growth

variable (p : ℕ) [Fact p.Prime]

/-- [hypothesis] **Weierstrass data** for an element of `Λ`: the factorization
`f = p^μ · g · u` with `g` distinguished of degree `λ` and `u` a unit, carried as data.
Whether such a factorization exists for every nonzero `f` is the Weierstrass preparation theorem
for `ℤ_p[[T]]`; it is **not** proved here and nothing in this file asserts it. -/
structure WeierstrassData (f : Lambda p) where
  /-- the `μ`-invariant: the power of `p` split off -/
  mu : ℕ
  /-- the `λ`-invariant: the degree of the distinguished factor -/
  lambda : ℕ
  /-- the distinguished factor -/
  distinguished : Polynomial ℤ_[p]
  /-- the unit factor -/
  unit : Lambda p
  distinguished_monic : distinguished.Monic
  distinguished_degree : distinguished.natDegree = lambda
  distinguished_coeffs : ∀ i, i < lambda → (p : ℤ_[p]) ∣ distinguished.coeff i
  unit_isUnit : IsUnit unit
  factorization : f = (p : Lambda p) ^ mu * (distinguished : Lambda p) * unit

/-- [proved-derived; formal-checked] `ω_n` carries Weierstrass data with `μ = 0` and `λ = p^n`, so
`WeierstrassData` is inhabited by a real object and is not a vacuous carrier. -/
def omegaWeierstrassData (n : ℕ) : WeierstrassData p (omega p n) where
  mu := 0
  lambda := p ^ n
  distinguished := omegaPoly p n
  unit := 1
  distinguished_monic := omegaPoly_monic p n
  distinguished_degree := omegaPoly_natDegree p n
  distinguished_coeffs := fun i hi => (omegaPoly_isDistinguished p n).2.2.2 i hi
  unit_isUnit := isUnit_one
  factorization := by
    simp only [pow_zero, one_mul, mul_one]
    simp [omega, omegaPoly]

/-- [counterexample; formal-checked] **`WeierstrassData` is a real condition, not a decoration.**
No element of `Λ` that is zero carries it: the right-hand side of the factorization is a product of
nonzero factors in a domain.  Together with `omegaWeierstrassData` this gives the carrier both a
constructed instance and a constructed non-instance.

[established-bounded; cited-classical] That *every* nonzero element carries it is the Weierstrass
preparation theorem for `ℤ_p[[T]]` (Washington, *Introduction to Cyclotomic Fields*, 2nd ed.,
Thm 7.3); it is **not** proved here. -/
theorem weierstrassData_isEmpty_at_zero : IsEmpty (WeierstrassData p 0) := by
  refine ⟨fun W => ?_⟩
  have hu : W.unit ≠ 0 := W.unit_isUnit.ne_zero
  have hg : (W.distinguished : Lambda p) ≠ 0 := by
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact W.distinguished_monic.ne_zero
  have hp : ((p : Lambda p)) ≠ 0 := by
    intro h
    have h2 := congrArg (PowerSeries.constantCoeff (R := ℤ_[p])) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero (R := ℤ_[p])).2 (Fact.out (p := p.Prime)).pos.ne' h2
  have := W.factorization
  rw [eq_comm, mul_eq_zero, mul_eq_zero, pow_eq_zero_iff'] at this
  rcases this with (⟨h0, _⟩ | h0) | h0
  · exact hp h0
  · exact hg h0
  · exact hu h0

/-- [established-bounded; cited-classical] **Iwasawa's growth theorem, stated and not proved.**
For a finitely generated torsion `Λ`-module the finite quotients grow as
`|M/ω_n M| = p^{μ p^n + λ n + ν}` for all large `n`.  Source: K. Iwasawa, *On Γ-extensions of
algebraic number fields*, Bull. AMS 65 (1959) 183–226; L. Washington, *Introduction to Cyclotomic
Fields*, 2nd ed. (GTM 83, 1997), Thm 13.13.  `μ` and `λ` are **growth exponents** read off a
distinguished factorization; they are not an entropy, not a rate and not a score.  This file proves
no instance of this `Prop`; the Rust owner exhibits it numerically at small `(p, n)` as exact
integers. -/
def TheGrowthLaw (M : Type v) [AddCommGroup M] [Module (Lambda p) M] (mu lambda nu : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card (M ⧸ omegaSubmodule p M n) = p ^ (mu * p ^ n + lambda * n + nu)

end Growth

/-! ## 7. The main conjecture as an open `Prop` over these carriers -/

section MainConjecture

variable (p : ℕ) [Fact p.Prime]

/-- [open] **The main conjecture, as receiver-exactness.**  Two codimension-one faces are asserted
equal: the characteristic face of the Selmer-side module `X` read through its supplied structure
data, and the ideal cut by the `p`-adic `L`-function.  It is an equality of *faces*, explicitly not
an identity of sources — `theMainConjectureIsNotSourceIdentity` proves the difference is real.
**No proof is claimed here, in any case.** -/
def TheMainConjecture {X : Type v} [AddCommGroup X] [Module (Lambda p) X]
    (D : StructureData p X) (Lp : Lambda p) : Prop :=
  D.characteristicFace = Ideal.span {Lp}

/-- [proved-derived; formal-checked] **Receiver-exactness is not source identity.**  One and the
same `L`-element satisfies `TheMainConjecture` for two non-isomorphic modules.  An equality of
codimension-one faces therefore establishes nothing about the modules beyond that face — which is
exactly this carrier's standing rule that a face is a receiver reading and never the identity of
its source. -/
theorem theMainConjectureIsNotSourceIdentity :
    ∃ Lp : Lambda p,
      TheMainConjecture p (squareStructure p) Lp ∧
        TheMainConjecture p (splitStructure p) Lp ∧
        IsEmpty (SquareModule p ≃ₗ[Lambda p] SplitModule p) := by
  refine ⟨(PowerSeries.X : Lambda p) ^ 2, ?_, ?_, (theCharacteristicFaceDoesNotDetermineTheModule p).2⟩
  · exact squareStructure_characteristicFace p
  · exact splitStructure_characteristicFace p

end MainConjecture

end Soma.Holonics.Foundation.IwasawaTower
