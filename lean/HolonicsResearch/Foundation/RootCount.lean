import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic
import HolonicsResearch.Mathematics.Sturm

/-! # Root counting: the gauge a sign-variation reading is blind to, and the squarefree part

[definition] This owner states the two laws the Rust module
`crates/holonic-engine/src/exact_value.rs::SturmChain` rests on, and closes the boundary
`HolonicsResearch.Mathematics.Sturm` names open.

That module carries the classical instrument: a chart is a coefficient list, `remainderChain` is the
negated-remainder chain, `readingAt` is its sign-variation count at a rational point, and
`theReadingIsInvariantUnderPositiveRescaling` proves the reading blind to **one common positive**
factor. Its docstring then says, in as many words, that the **per-entry** gauge — rescaling each
chain entry by *its own* positive constant, which is what clearing denominators does — is not
proved there.

That per-entry gauge is exactly the licence the Rust owner needs and nothing else would do. The
Rust chain is not the Euclidean sequence over `ℚ`; it is the **pseudo-remainder sequence over `ℤ`**,
whose `i`-th entry is `lc(S_i)^(δ+1) / content` times the classical one — a different positive
factor at every entry. So:

1. `theContinuingCountIsInvariantUnderPerEntryPositiveRescaling` and
   `theReadingIsInvariantUnderPerEntryPositiveRescaling` prove the reading blind to a per-entry
   positive rescaling. This is the correctness of the sign rule in
   `exact_value.rs::SturmChain::build`, and its negative counterpart is live: a *negative* factor at
   one entry is visible, which is why that routine tracks the sign of `lc(S_i)^(δ+1)` rather than
   taking absolute values.
2. `theContinuingCountIsInvariantUnderCommonNonzeroRescaling` and
   `theReadingIsInvariantUnderCommonNonzeroRescaling` strengthen the existing common-factor law from
   *positive* to *nonzero*. A common factor enters squared into every adjacent product, so its sign
   cannot matter; only a per-entry factor's sign can. This is why a chain built from a polynomial
   that is **not** squarefree still counts *distinct* roots: at any point the whole chain is the
   squarefree part's chain times the one value `gcd(f, f')(x)`, whose sign is common to every entry
   and therefore gauge.
3. `theSquarefreePartSharesItsRoots` is the squarefree half: **assuming** `p = g * q` with
   `g = gcd(p, p')`, the polynomial `q` has **exactly** the roots of `p`. Over `ℚ` — characteristic
   zero — a root of multiplicity `m` in `p` has multiplicity `m - 1` in `p'`, hence `m - 1` in `g`,
   hence `1` in `q`. The factorization is a *hypothesis*, and the theorem is therefore conditional
   on it; what discharges it is the Rust, which computes `g` and then takes an **exact** division
   that refuses a nonzero remainder by name. This is the law under
   `crates/holonic-engine/src/rational_polynomial.rs`'s `squarefree_part` and under every consumer
   that counts distinct roots by counting the radical's.

**Not proved here, and said so.** *Sturm's theorem itself* — that the reading's drop across an
interval is the number of distinct real roots in it — is a **cited classical fact**
[established-classical; not-formalized-here]: C. Sturm, *Mémoire sur la résolution des équations
numériques*, Bull. des Sciences de Férussac **11** (1829); see also Basu–Pollack–Roy,
*Algorithms in Real Algebraic Geometry*, 2nd ed., Theorem 2.61. It is stated in this repository as
the named-open proposition `Holonics.Mathematics.Sturm.TheReadingEqualsThePopulation` and is not
assumed anywhere below: every theorem in this file is about the *reading*, which is a finite
combinatorial object, and none of them needs the theorem that interprets it. Mathlib has no Sturm
theory (its `Polynomial.signVariations` serves Descartes' rule of signs, which is a bound and not a
count).

Rust owner: `crates/holonic-engine/src/exact_value.rs::SturmChain` ↔
`theReadingIsInvariantUnderPerEntryPositiveRescaling`;
`crates/holonic-engine/src/exact_value.rs::SturmChain::of` on a non-squarefree polynomial ↔
`theReadingIsInvariantUnderCommonNonzeroRescaling`;
`crates/holonic-engine/src/rational_polynomial.rs::RationalPolynomial::squarefree_part` ↔
`theSquarefreePartSharesItsRoots`.
Plan: `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`, **R1** and **R3**.
-/

namespace Holonics.Foundation.RootCount

open Holonics.Mathematics.Sturm

/-! ## 1. The per-entry positive gauge -/

/-- **One list is a per-entry positive rescaling of another.**

Entry `i` of the rescaled list is `c_i` times entry `i` of the original, with each `c_i > 0` and
each chosen independently. This is precisely the relation between the Rust owner's
pseudo-remainder chain, evaluated at a point, and the classical Euclidean chain evaluated there. -/
inductive PositivelyRescaled : List ℚ → List ℚ → Prop
  | nil : PositivelyRescaled [] []
  | cons {c u : ℚ} {l m : List ℚ} :
      0 < c → PositivelyRescaled l m → PositivelyRescaled (u :: l) (c * u :: m)

/-- A per-entry positive rescaling preserves length. -/
theorem thePerEntryRescalingPreservesLength :
    ∀ {l m : List ℚ}, PositivelyRescaled l m → m.length = l.length := by
  intro l m h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-- **The continuing count is invariant under a per-entry positive rescaling**, including a
positive rescaling of the declared predecessor. -/
theorem theContinuingCountIsInvariantUnderPerEntryPositiveRescaling :
    ∀ {l m : List ℚ}, PositivelyRescaled l m →
      ∀ {d u : ℚ}, 0 < d → variationFrom (d * u) m = variationFrom u l := by
  intro l m h
  induction h with
  | nil => intro d u _; simp [variationFrom]
  | @cons c u l m hc hrec ih =>
    intro d w hd
    simp only [variationFrom]
    by_cases hu : u = 0
    · have hcu : c * u = 0 := by rw [hu, mul_zero]
      rw [if_pos hcu, if_pos hu]
      exact ih hd
    · have hcu : c * u ≠ 0 := mul_ne_zero (ne_of_gt hc) hu
      have hdc : (0 : ℚ) < d * c := mul_pos hd hc
      have hprod : (d * w) * (c * u) = (d * c) * (w * u) := by ring
      have hsign : (d * w) * (c * u) < 0 ↔ w * u < 0 := by
        rw [hprod]
        constructor
        · intro hlt
          by_contra hcon
          push_neg at hcon
          exact absurd hlt (not_lt.mpr (mul_nonneg (le_of_lt hdc) hcon))
        · intro hlt
          exact mul_neg_of_pos_of_neg hdc hlt
      rw [if_neg hu, if_neg hcu, ih hc]
      by_cases hs : w * u < 0
      · rw [if_pos (hsign.mpr hs), if_pos hs]
      · rw [if_neg (fun hx => hs (hsign.mp hx)), if_neg hs]

/-- **The reading is invariant under a per-entry positive rescaling.**

[proved-derived; formal-checked] This is the boundary `Mathematics/Sturm.lean` named open, closed.
It is the whole licence for the Rust owner's pseudo-remainder chain: its `i`-th entry is a
*different* positive multiple of the classical `i`-th entry, and the reading cannot see that. The
positivity is not decoration — the per-entry statement is false for a negative factor, which is why
`exact_value.rs::SturmChain` carries `−sign(lc(S_i)^(δ+1))` explicitly instead of normalizing signs
away. -/
theorem theReadingIsInvariantUnderPerEntryPositiveRescaling :
    ∀ {l m : List ℚ}, PositivelyRescaled l m → variationCount m = variationCount l := by
  intro l m h
  induction h with
  | nil => simp only [variationCount]
  | @cons c u l m hc hrec ih =>
    simp only [variationCount]
    by_cases hu : u = 0
    · have hcu : c * u = 0 := by rw [hu, mul_zero]
      rw [if_pos hcu, if_pos hu]
      exact ih
    · have hcu : c * u ≠ 0 := mul_ne_zero (ne_of_gt hc) hu
      rw [if_neg hcu, if_neg hu]
      exact theContinuingCountIsInvariantUnderPerEntryPositiveRescaling hrec hc

/-- A **negative** entry is not gauge: the two-entry reading `[1, -1]` counts one variation and
flipping only the second entry counts none. The per-entry law above is therefore sharp at its
positivity hypothesis, and this is the executable reason the Rust owner tracks a sign. -/
theorem thePerEntryGaugeIsSharpAtItsPositivity :
    variationCount [(1 : ℚ), -1] ≠ variationCount [(1 : ℚ), 1] := by
  norm_num [variationCount, variationFrom]

/-! ## 2. The common factor, strengthened from positive to nonzero -/

/-- **The continuing count is invariant under a common nonzero rescaling.**

`Mathematics/Sturm.lean` proves this for `0 < c`. A common factor enters every adjacent product
squared — `(c u)(c v) = c² (u v)` — so its *sign* cannot matter, and the hypothesis weakens to
`c ≠ 0`. -/
theorem theContinuingCountIsInvariantUnderCommonNonzeroRescaling {c : ℚ} (hc : c ≠ 0) :
    ∀ (u : ℚ) (l : List ℚ),
      variationFrom (c * u) (l.map (fun v => c * v)) = variationFrom u l := by
  have hc2 : (0 : ℚ) < c * c := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  intro u l
  induction l generalizing u with
  | nil => simp [variationFrom]
  | cons v l ih =>
    simp only [List.map_cons, variationFrom]
    by_cases hv : v = 0
    · have hcv : c * v = 0 := by rw [hv, mul_zero]
      rw [if_pos hcv, if_pos hv]
      exact ih u
    · have hcv : c * v ≠ 0 := mul_ne_zero hc hv
      have hprod : (c * u) * (c * v) = (c * c) * (u * v) := by ring
      have hsign : (c * u) * (c * v) < 0 ↔ u * v < 0 := by
        rw [hprod]
        constructor
        · intro hlt
          by_contra hcon
          push_neg at hcon
          exact absurd hlt (not_lt.mpr (mul_nonneg (le_of_lt hc2) hcon))
        · intro hlt
          exact mul_neg_of_pos_of_neg hc2 hlt
      rw [if_neg hv, if_neg hcv, ih v]
      by_cases hs : u * v < 0
      · rw [if_pos (hsign.mpr hs), if_pos hs]
      · rw [if_neg (fun hx => hs (hsign.mp hx)), if_neg hs]

/-- **The reading is invariant under a common nonzero rescaling.**

[proved-derived; formal-checked] This is why a chain built from a polynomial that is *not*
squarefree still counts **distinct** roots. At any point `x`, every entry of the chain of `f` is the
corresponding entry of the chain of `f / gcd(f, f')` times the single value `gcd(f, f')(x)`. That
value is one common factor, its sign is whatever it is, and the reading cannot see it. -/
theorem theReadingIsInvariantUnderCommonNonzeroRescaling {c : ℚ} (hc : c ≠ 0) :
    ∀ l : List ℚ, variationCount (l.map (fun v => c * v)) = variationCount l := by
  intro l
  induction l with
  | nil => simp only [List.map_nil]
  | cons v l ih =>
    simp only [List.map_cons, variationCount]
    by_cases hv : v = 0
    · have hcv : c * v = 0 := by rw [hv, mul_zero]
      rw [if_pos hcv, if_pos hv]
      exact ih
    · have hcv : c * v ≠ 0 := mul_ne_zero hc hv
      rw [if_neg hcv, if_neg hv]
      exact theContinuingCountIsInvariantUnderCommonNonzeroRescaling hc v l

/-- A common rescaling is one instance of a per-entry rescaling, so the positive case of the law
above is also a corollary of §1. Stated to record that the two families agree where they overlap. -/
theorem theCommonPositiveRescalingIsAPerEntryOne {c : ℚ} (hc : 0 < c) :
    ∀ l : List ℚ, PositivelyRescaled l (l.map (fun v => c * v)) := by
  intro l
  induction l with
  | nil => exact PositivelyRescaled.nil
  | cons v l ih => exact PositivelyRescaled.cons hc ih

/-! ## 3. The squarefree part -/

open Polynomial

/-- **The squarefree part has exactly the roots of the polynomial — given the factorization.**

[proved-derived; formal-checked] `p = g * q` with `g = gcd(p, p')` is a **hypothesis of this
theorem, not a conclusion of it**: `hq` is assumed, and nothing here proves that the `q` a caller
supplies is the quotient, or that the quotient is exact. What is proved, from that hypothesis, is
that `q` is a root of `p` exactly where `p` is. Forwards: over a field of characteristic zero a root
of multiplicity `m ≥ 1` in `p` has multiplicity `m - 1` in `p'`, hence at least `m - 1` and at most
`m - 1` in `g`, so exactly `1` remains in `q`. Backwards: `q ∣ p`.

**Where the hypothesis is discharged.** It is discharged *computationally, at each use*, on the
Rust side: `crates/holonic-engine/src/rational_polynomial.rs::RationalPolynomial::squarefree_part`
forms `g = monic_gcd(p, p')` and then takes `p.divided_exactly_by(&g)`, which returns
`NonExactPolynomialDivision` — a typed refusal, in the library and not only in a test — unless the
remainder is exactly the zero polynomial. A returned radical therefore *is* a `q` with `p = g * q`,
and `rational_polynomial::tests::the_squarefree_factorization_the_lean_theorem_assumes_is_checked`
holds that identity on the corpus as well. The radical is additionally made monic; scaling by a
nonzero constant is a unit and moves no root, so the conclusion transfers to it unchanged.

This is the law every distinct-root count in the Rust rests on: counting the roots of the radical is
counting the *distinct* roots of the original. -/
theorem theSquarefreePartSharesItsRoots {p q : ℚ[X]} (hp : p ≠ 0)
    (hq : p = EuclideanDomain.gcd p (derivative p) * q) :
    ∀ a : ℚ, p.IsRoot a ↔ q.IsRoot a := by
  set g := EuclideanDomain.gcd p (derivative p) with hgdef
  have hg0 : g ≠ 0 := fun h => hp (by rw [hq, h, zero_mul])
  have hq0 : q ≠ 0 := fun h => hp (by rw [hq, h, mul_zero])
  intro a
  constructor
  · intro ha
    have hm : 0 < p.rootMultiplicity a := (rootMultiplicity_pos hp).mpr ha
    have hd0 : derivative p ≠ 0 := by
      intro h
      have hdeg : p.natDegree = 0 := derivative_eq_zero.mp h
      have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hzero : p.coeff 0 = 0 := by
        have := ha
        rw [hC] at this
        simpa using this
      exact hp (by rw [hC, hzero, map_zero])
    -- the derivative loses exactly one from the multiplicity, in characteristic zero
    have hderiv : (derivative p).rootMultiplicity a = p.rootMultiplicity a - 1 :=
      derivative_rootMultiplicity_of_root ha
    -- `(X - C a) ^ (m - 1)` divides both, so it divides the gcd
    have hdvd_p : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ p :=
      dvd_trans (pow_dvd_pow _ (Nat.sub_le _ 1)) (pow_rootMultiplicity_dvd p a)
    have hdvd_d : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ derivative p := by
      rw [← hderiv]
      exact pow_rootMultiplicity_dvd (derivative p) a
    have hdvd_g : (X - C a) ^ (p.rootMultiplicity a - 1) ∣ g :=
      EuclideanDomain.dvd_gcd hdvd_p hdvd_d
    -- and no more than that divides it, because no more divides the derivative
    have hle : g.rootMultiplicity a ≤ p.rootMultiplicity a - 1 := by
      by_contra hcon
      push_neg at hcon
      have hstep : p.rootMultiplicity a ≤ g.rootMultiplicity a := by omega
      have hdvd : (X - C a) ^ p.rootMultiplicity a ∣ g :=
        (le_rootMultiplicity_iff hg0).mp hstep
      have hdvd2 : (X - C a) ^ p.rootMultiplicity a ∣ derivative p :=
        hdvd.trans (EuclideanDomain.gcd_dvd_right _ _)
      have hback : p.rootMultiplicity a ≤ (derivative p).rootMultiplicity a :=
        (le_rootMultiplicity_iff hd0).mpr hdvd2
      rw [hderiv] at hback
      omega
    have hsplit : p.rootMultiplicity a = g.rootMultiplicity a + q.rootMultiplicity a := by
      conv_lhs => rw [hq]
      exact rootMultiplicity_mul (by rw [← hq]; exact hp)
    have : 0 < q.rootMultiplicity a := by omega
    exact (rootMultiplicity_pos hq0).mp this
  · intro ha
    exact ha.dvd ⟨g, by rw [hq]; ring⟩

/-- The backwards direction on its own, which needs nothing about characteristic or gcds: the
squarefree part divides the polynomial, so it cannot acquire a root the polynomial does not have. -/
theorem theSquarefreePartAcquiresNoRoot {p q g : ℚ[X]} (hq : p = g * q) :
    ∀ a : ℚ, q.IsRoot a → p.IsRoot a := by
  intro a ha
  exact ha.dvd ⟨g, by rw [hq]; ring⟩

/-! ## Kernel receipts

Only `propext`, `Classical.choice` and `Quot.sound` are admissible. -/

end Holonics.Foundation.RootCount

#print axioms Holonics.Foundation.RootCount.thePerEntryRescalingPreservesLength
#print axioms
  Holonics.Foundation.RootCount.theContinuingCountIsInvariantUnderPerEntryPositiveRescaling
#print axioms Holonics.Foundation.RootCount.theReadingIsInvariantUnderPerEntryPositiveRescaling
#print axioms Holonics.Foundation.RootCount.thePerEntryGaugeIsSharpAtItsPositivity
#print axioms
  Holonics.Foundation.RootCount.theContinuingCountIsInvariantUnderCommonNonzeroRescaling
#print axioms Holonics.Foundation.RootCount.theReadingIsInvariantUnderCommonNonzeroRescaling
#print axioms Holonics.Foundation.RootCount.theCommonPositiveRescalingIsAPerEntryOne
#print axioms Holonics.Foundation.RootCount.theSquarefreePartSharesItsRoots
#print axioms Holonics.Foundation.RootCount.theSquarefreePartAcquiresNoRoot
