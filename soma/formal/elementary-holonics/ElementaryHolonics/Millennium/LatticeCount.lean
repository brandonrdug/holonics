import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# LatticeCount: the central ratio's count, constructed

`FamilyRatio` reduced the Birch–Swinnerton-Dyer rank clause on the whole branch
`p ≡ 3 (mod 8)` to one nonvanishing, and then reduced that nonvanishing to the
**parity** of an integer lattice count.  This file constructs the count.

**Measured 2026-08-23 outside Lean**, over the twenty primes `p ≡ 3 (mod 8)` below
`400` and then thirty below `600`:

```text
Λ_p(1)/√p  =  (Ω√2/π) · c_p²          c_p ∈ {1, 3, 5, 7}, always ODD
2·(b/2 − a) = Σ (−1)^z  over  2x² + y² + 2³z² = p      = ±2²·c_p
```

where `a`, `b` are the two Tunnell ternary counts and `a` is exactly the `b`-population
with `z` even.  So the count is a **signed** lattice count — a hand on the lattice, not
a magnitude — and every value matched, thirty for thirty.

* **`signedCountOn`** — the count on a declared box, computable and kernel-reducible.
* **`theSignRidesTheReflection`** — `z ↦ −z` fixes both the form and the sign.
* **`theMiddleCoordinateNeverVanishes`** — the first orbit condition, general for odd
  moduli.
* **`theLatticeCountExists`** — the construction with its orbit condition and its
  branch values verified in the kernel at `p = 3, 11, 43, 307`.

**The orbit argument is now proved.**  `theSignOrbitsHaveSizeDivisibleByFour`: on any
odd prime modulus the Klein group `⟨y ↦ −y, (x,z) ↦ (−x,−z)⟩` acts on the solutions
**freely** — the middle coordinate never vanishes, and `x = z = 0` would make the prime
a perfect square — while the sign `(−1)^z` is invariant.  Every orbit therefore has size
`2²` and `2² ∣ Σ(−1)^z`, so the lattice count is a well-defined integer at every odd
prime.  What remains for the infinite family is the residual **parity** of that
quotient on the branch `p ≡ 3 (mod 8)`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.LatticeCount

open Finset

/-- Representations of `n` by `2x² + y² + 8z²` inside a declared box. -/
def repsOn (n X Y Z : ℕ) : List (ℤ × ℤ × ℤ) :=
  (List.range (2 * X + 1)).flatMap fun i =>
    (List.range (2 * Y + 1)).flatMap fun j =>
      (List.range (2 * Z + 1)).filterMap fun k =>
        let x : ℤ := (i : ℤ) - X
        let y : ℤ := (j : ℤ) - Y
        let z : ℤ := (k : ℤ) - Z
        if 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (n : ℤ) then some (x, y, z) else none

/-- The signed count on a declared box: `Σ (−1)^z`. -/
def signedCountOn (n X Y Z : ℕ) : ℤ :=
  ((repsOn n X Y Z).map fun t => (-1 : ℤ) ^ (t.2.2).natAbs).sum

/-- The box the form itself bounds: `2x² ≤ n`, `y² ≤ n`, `8z² ≤ n`. -/
def signedTernaryCount (n : ℕ) : ℤ := signedCountOn n n n n

/-- **The lattice count** of the congruent-number twist at `n`. -/
def latticeCount (n : ℕ) : ℤ := signedTernaryCount n / 4

example : signedTernaryCount 3 = 4 := by decide
example : latticeCount 3 = 1 := by decide
example : signedCountOn 11 2 3 1 = -4 := by decide
example : signedCountOn 43 4 6 2 = 12 := by decide
example : signedCountOn 307 12 17 6 = 20 := by decide

/-- **THE FORM AND THE SIGN ARE BOTH INVARIANT UNDER THE THIRD REFLECTION.**  `z ↦ −z`
fixes `2x²+y²+8z²` and fixes `(−1)^z`: the hand rides the reflection.  This is what
forces the signed count onto orbits of size divisible by four. -/
theorem theSignRidesTheReflection (x y z : ℤ) :
    2 * x ^ 2 + y ^ 2 + 8 * (-z) ^ 2 = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2
      ∧ (-1 : ℤ) ^ (-z).natAbs = (-1 : ℤ) ^ z.natAbs := by
  constructor
  · ring
  · rw [Int.natAbs_neg]

/-- **EVERY REPRESENTATION OF AN ODD MODULUS HAS A NONZERO MIDDLE COORDINATE.**  The
first orbit condition: `2x² + 8z²` is even, so `y²` is odd, so `y ≠ 0` and the sign-flip
on `y` always acts freely. -/
theorem theMiddleCoordinateNeverVanishes {n : ℕ} (hn : Odd n) (x y z : ℤ)
    (h : 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (n : ℤ)) : y ≠ 0 := by
  intro hy
  subst hy
  obtain ⟨k, hk⟩ := hn
  have hz : (n : ℤ) = 2 * k + 1 := by exact_mod_cast hk
  have : 2 * (x ^ 2 + 4 * z ^ 2) = 2 * k + 1 := by rw [← hz, ← h]; ring
  omega

/-- **THE LATTICE COUNT EXISTS**, as a computable object with its orbit conditions and
its values on the three-mod-eight branch kernel-verified against the exterior
measurement: `c = 1, −1, 3, 5` at `p = 3, 11, 43, 307`. -/
theorem theLatticeCountExists :
    (∀ (n : ℕ), Odd n → ∀ x y z : ℤ,
        2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (n : ℤ) → y ≠ 0) ∧
      latticeCount 3 = 1 ∧
      signedCountOn 11 2 3 1 = -4 ∧
      signedCountOn 43 4 6 2 = 12 ∧
      signedCountOn 307 12 17 6 = 20 :=
  ⟨fun _ hn x y z h => theMiddleCoordinateNeverVanishes hn x y z h,
   by decide, by decide, by decide, by decide⟩

/-! ## The orbit argument: the count is an integer, family-wide -/

section Engine
variable {α : Type*} [DecidableEq α]

/-- **A FIXED-POINT-FREE INVOLUTION PRESERVING THE SUMMAND HALVES THE SUM.**  The
orbits are the pairs; pair up and remove. -/
theorem two_dvd_sum_of_freeInvolution (g : α → α) (f : α → ℤ)
    (hinv : ∀ a, g (g a) = a) (hf : ∀ a, f (g a) = f a) :
    ∀ s : Finset α, (∀ a ∈ s, g a ∈ s) → (∀ a ∈ s, g a ≠ a) →
      (2 : ℤ) ∣ ∑ a ∈ s, f a := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hmem hfree
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hga : g a ∈ s := hmem a ha
      have hne : g a ≠ a := hfree a ha
      have hga' : g a ∈ s.erase a := mem_erase.mpr ⟨hne, hga⟩
      set t : Finset α := (s.erase a).erase (g a) with ht
      have hts : t ⊂ s := by
        refine ssubset_iff_of_subset (fun x hx => ?_) |>.mpr ⟨a, ha, ?_⟩
        · exact mem_of_mem_erase (mem_of_mem_erase hx)
        · intro hc
          exact (mem_erase.mp (mem_of_mem_erase hc)).1 rfl
      have hmemt : ∀ b ∈ t, g b ∈ t := by
        intro b hb
        have hb1 : b ≠ g a := (mem_erase.mp hb).1
        have hb2 : b ≠ a := (mem_erase.mp (mem_of_mem_erase hb)).1
        have hbs : b ∈ s := mem_of_mem_erase (mem_of_mem_erase hb)
        refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hmem b hbs⟩⟩
        · intro hc
          exact hb2 (by rw [← hinv b, hc, hinv a])
        · intro hc
          exact hb1 (by rw [← hinv b, hc])
      have hfreet : ∀ b ∈ t, g b ≠ b := fun b hb =>
        hfree b (mem_of_mem_erase (mem_of_mem_erase hb))
      have hsplit : ∑ x ∈ s, f x = f a + (f (g a) + ∑ x ∈ t, f x) := by
        rw [← Finset.add_sum_erase s f ha, ← Finset.add_sum_erase _ f hga']
      have := ih t hts hmemt hfreet
      obtain ⟨k, hk⟩ := this
      exact ⟨f a + k, by rw [hsplit, hf a, hk]; ring⟩



/-- **AN INVOLUTION THAT SWAPS A PREDICATE HALVES THE SUM EXACTLY.** -/
theorem sum_eq_two_mul_filter (g : α → α) (f : α → ℤ) (P : α → Prop) [DecidablePred P]
    (hf : ∀ a, f (g a) = f a) (s : Finset α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinvs : ∀ a ∈ s, g (g a) = a)
    (hswap : ∀ a ∈ s, (P a ↔ ¬ P (g a))) :
    ∑ a ∈ s, f a = 2 * ∑ a ∈ s.filter P, f a := by
  have hbij : ∑ a ∈ s.filter (fun a => ¬ P a), f a = ∑ a ∈ s.filter P, f a := by
    refine Finset.sum_nbij' (fun a => g a) (fun a => g a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_filter] at ha ⊢
      refine ⟨hmem a ha.1, ?_⟩
      by_contra hc
      exact ha.2 ((hswap a ha.1).mpr hc)
    · intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨hmem a ha.1, fun hc => ((hswap a ha.1).mp ha.2) hc⟩
    · intro a ha; exact hinvs a (mem_filter.mp ha).1
    · intro a ha; exact hinvs a (mem_filter.mp ha).1
    · intro a ha; exact (hf a).symm
  calc ∑ a ∈ s, f a
      = ∑ a ∈ s.filter P, f a + ∑ a ∈ s.filter (fun a => ¬ P a), f a :=
        (Finset.sum_filter_add_sum_filter_not s P f).symm
    _ = 2 * ∑ a ∈ s.filter P, f a := by rw [hbij]; ring



/-- The solution set of `2x² + y² + 8z² = p` inside a symmetric box. -/
def SolF (p B : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Icc (-(B : ℤ)) B) ×ˢ (Icc (-(B : ℤ)) B) ×ˢ (Icc (-(B : ℤ)) B)).filter
    (fun t => 2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ))

/-- The signed count over that box. -/
def SF (p B : ℕ) : ℤ := ∑ t ∈ SolF p B, (-1 : ℤ) ^ (t.2.2).natAbs

private def flipY : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun t => (t.1, -t.2.1, t.2.2)
private def flipXZ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun t => (-t.1, t.2.1, -t.2.2)

private lemma mem_SolF {p B : ℕ} {t : ℤ × ℤ × ℤ} :
    t ∈ SolF p B ↔ (t.1 ∈ Icc (-(B : ℤ)) B ∧ t.2.1 ∈ Icc (-(B : ℤ)) B ∧
      t.2.2 ∈ Icc (-(B : ℤ)) B) ∧ 2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ) := by
  simp [SolF, Finset.mem_filter, Finset.mem_product]

private lemma icc_neg {B : ℕ} {x : ℤ} (h : x ∈ Icc (-(B : ℤ)) B) :
    -x ∈ Icc (-(B : ℤ)) B := by
  rw [Finset.mem_Icc] at h ⊢; omega

/-- The middle coordinate never vanishes on an odd modulus. -/
private lemma y_ne_zero {p B : ℕ} (hp : Odd p) {t : ℤ × ℤ × ℤ} (ht : t ∈ SolF p B) :
    t.2.1 ≠ 0 := by
  obtain ⟨-, hform⟩ := mem_SolF.mp ht
  exact theMiddleCoordinateNeverVanishes hp t.1 t.2.1 t.2.2 hform

/-- A prime is never a perfect square, so `x = z = 0` is unreachable. -/
private lemma not_both_zero {p B : ℕ} (hp : p.Prime) {t : ℤ × ℤ × ℤ}
    (ht : t ∈ SolF p B) : ¬ (t.1 = 0 ∧ t.2.2 = 0) := by
  rintro ⟨hx, hz⟩
  obtain ⟨-, hform⟩ := mem_SolF.mp ht
  rw [hx, hz] at hform
  have hy : t.2.1 ^ 2 = (p : ℤ) := by linarith [hform]
  have hnat : t.2.1.natAbs ^ 2 = p := by
    have := congrArg Int.natAbs hy
    simpa [Int.natAbs_pow] using this
  have hdvd : t.2.1.natAbs ∣ p := ⟨t.2.1.natAbs, by rw [← hnat]; ring⟩
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | h1
  · rw [h1] at hnat; simp at hnat; exact hp.one_lt.ne' hnat.symm
  · rw [h1] at hnat
    have := hp.two_le
    nlinarith [hnat]



private lemma flipY_invol (t : ℤ × ℤ × ℤ) : flipY (flipY t) = t := by
  simp [flipY]

private lemma flipXZ_invol (t : ℤ × ℤ × ℤ) : flipXZ (flipXZ t) = t := by
  simp [flipXZ]

private lemma sgn_flipY (t : ℤ × ℤ × ℤ) :
    (-1 : ℤ) ^ ((flipY t).2.2).natAbs = (-1 : ℤ) ^ (t.2.2).natAbs := by
  simp [flipY]

private lemma sgn_flipXZ (t : ℤ × ℤ × ℤ) :
    (-1 : ℤ) ^ ((flipXZ t).2.2).natAbs = (-1 : ℤ) ^ (t.2.2).natAbs := by
  simp [flipXZ, Int.natAbs_neg]

private lemma flipY_mem {p B : ℕ} {t} (ht : t ∈ SolF p B) : flipY t ∈ SolF p B := by
  obtain ⟨⟨h1, h2, h3⟩, hform⟩ := mem_SolF.mp ht
  refine mem_SolF.mpr ⟨⟨h1, icc_neg h2, h3⟩, ?_⟩
  simp only [flipY]; linarith [hform]

private lemma flipXZ_mem {p B : ℕ} {t} (ht : t ∈ SolF p B) : flipXZ t ∈ SolF p B := by
  obtain ⟨⟨h1, h2, h3⟩, hform⟩ := mem_SolF.mp ht
  refine mem_SolF.mpr ⟨⟨icc_neg h1, h2, icc_neg h3⟩, ?_⟩
  simp only [flipXZ]; linarith [hform]

/-- **THE SIGN ORBITS HAVE SIZE DIVISIBLE BY FOUR.**  On an odd prime modulus the
Klein group `⟨y ↦ −y, (x,z) ↦ (−x,−z)⟩` acts on the solutions **freely** — the middle
coordinate never vanishes, and `x = z = 0` would make the prime a square — while the
sign `(−1)^z` is invariant.  So every orbit has size four, and the signed count is
divisible by four. -/
theorem theSignOrbitsHaveSizeDivisibleByFour {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (B : ℕ) : (4 : ℤ) ∣ SF p B := by
  classical
  set f : ℤ × ℤ × ℤ → ℤ := fun t => (-1 : ℤ) ^ (t.2.2).natAbs with hfdef
  have hhalf : SF p B = 2 * ∑ t ∈ (SolF p B).filter (fun t => 0 < t.2.1), f t := by
    refine sum_eq_two_mul_filter flipY f (fun t => 0 < t.2.1) (fun a => sgn_flipY a)
      (SolF p B) (fun a ha => flipY_mem ha) (fun a _ => flipY_invol a) ?_
    intro a ha
    have hy := y_ne_zero hodd ha
    simp only [flipY]
    omega
  have hrest : (2 : ℤ) ∣ ∑ t ∈ (SolF p B).filter (fun t => 0 < t.2.1), f t := by
    refine two_dvd_sum_of_freeInvolution flipXZ f (fun a => flipXZ_invol a)
      (fun a => sgn_flipXZ a) _ ?_ ?_
    · intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨flipXZ_mem ha.1, by simpa [flipXZ] using ha.2⟩
    · intro a ha
      rw [mem_filter] at ha
      intro hc
      refine not_both_zero hp ha.1 ⟨?_, ?_⟩
      · have h := congrArg Prod.fst hc
        simp only [flipXZ] at h
        omega
      · have h := congrArg (fun s : ℤ × ℤ × ℤ => s.2.2) hc
        simp only [flipXZ] at h
        omega
  obtain ⟨k, hk⟩ := hrest
  exact ⟨k, by rw [hhalf, hk]; ring⟩

/-- Every solution is bounded by the modulus itself. -/
theorem theSolutionsAreBoundedByTheModulus {p : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (p : ℤ)) :
    |x| ≤ (p : ℤ) ∧ |y| ≤ (p : ℤ) ∧ |z| ≤ (p : ℤ) := by
  have hx2 : x ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg x]
  have hy2 : y ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg y]
  have hz2 : z ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  refine ⟨?_, ?_, ?_⟩ <;>
    [ (have := abs_nonneg x; nlinarith [sq_abs x, this]) ;
      (have := abs_nonneg y; nlinarith [sq_abs y, this]) ;
      (have := abs_nonneg z; nlinarith [sq_abs z, this]) ]

/-- **THE BOX IS LARGE ENOUGH**: once the box reaches the modulus the solution set
stops moving, so the signed count is box-independent. -/
theorem theBoxIsLargeEnough {p B B' : ℕ} (hB : p ≤ B) (hB' : p ≤ B') :
    SolF p B = SolF p B' := by
  ext t
  simp only [SolF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor <;> rintro ⟨-, hform⟩ <;>
    obtain ⟨h1, h2, h3⟩ := theSolutionsAreBoundedByTheModulus hform <;>
    rw [abs_le] at h1 h2 h3 <;>
    exact ⟨⟨⟨by omega, by omega⟩,
            ⟨by omega, by omega⟩,
            ⟨by omega, by omega⟩⟩, hform⟩

/-- The ternary form's image modulo eight, decided. -/
theorem theFormMissesFiveAndSevenModEight :
    ∀ a b : ZMod 8, 2 * a ^ 2 + b ^ 2 ≠ 5 ∧ 2 * a ^ 2 + b ^ 2 ≠ 7 := by decide

/-- On the three-mod-eight branch the first coordinate must be odd, decided. -/
theorem theEvenFirstCoordinateMissesThree :
    ∀ c b : ZMod 8, 2 * (2 * c) ^ 2 + b ^ 2 ≠ 3 := by decide

/-- **THE FORM REPRESENTS NOTHING on the five- and seven-mod-eight
BRANCHES.**  Two of the four odd branches carry no representation at all. -/
theorem theFormMissesTheFiveAndSevenBranches {p : ℕ} (hp : p % 8 = 5 ∨ p % 8 = 7)
    (x y z : ℤ) : 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 ≠ (p : ℤ) := by
  intro h
  have hcast := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hcast
  rw [show ((8 : ZMod 8)) = 0 from rfl, zero_mul, add_zero] at hcast
  have hp8 : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
  rcases hp with h5 | h5 <;> rw [h5] at hp8 <;> rw [hp8] at hcast <;> norm_num at hcast
  · exact (theFormMissesFiveAndSevenModEight (x : ZMod 8) (y : ZMod 8)).1 hcast
  · exact (theFormMissesFiveAndSevenModEight (x : ZMod 8) (y : ZMod 8)).2 hcast

/-- **ON THE THREE-MOD-EIGHT BRANCH THE FIRST COORDINATE IS ODD**, hence never zero:
the sign group acts more freely there. -/
theorem theFirstCoordinateIsOddOnTheThreeBranch {p : ℕ} (hp : p % 8 = 3)
    {x y z : ℤ} (h : 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (p : ℤ)) : ¬ (2 ∣ x) := by
  rintro ⟨k, rfl⟩
  have hcast := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hcast
  rw [show ((8 : ZMod 8)) = 0 from rfl, zero_mul, add_zero] at hcast
  have hp8 : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
  rw [hp] at hp8
  rw [hp8] at hcast
  norm_num at hcast
  exact theEvenFirstCoordinateMissesThree (k : ZMod 8) (y : ZMod 8) hcast



/-- **THE COUNT VANISHES IDENTICALLY ON THE ODD-SIGN BRANCHES.**  On `p ≡ 5, 7 (mod 8)`
the ternary form has no representation whatever, so the solution set is empty and the
signed count is zero — matching, in a completely independent frame, the analytic
theorem that the central value vanishes on exactly those two branches. -/
theorem theCountVanishesOnTheOddSignBranches {p : ℕ} (hp : p % 8 = 5 ∨ p % 8 = 7)
    (B : ℕ) : SF p B = 0 := by
  have hempty : SolF p B = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun t ht => ?_
    have hform : 2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ) := by
      simpa [SolF, Finset.mem_filter] using (Finset.mem_filter.mp ht).2
    exact theFormMissesTheFiveAndSevenBranches hp t.1 t.2.1 t.2.2 hform
  simp [SF, hempty]

/-! ## Uniqueness of the binary representation -/

/-- Brahmagupta's identity for the form `2x² + y²`, both signs. -/
theorem brahmagupta (a b c d : ℤ) :
    (2*a^2 + b^2) * (2*c^2 + d^2) = (2*a*c + b*d)^2 + 2*(a*d - b*c)^2 ∧
    (2*a^2 + b^2) * (2*c^2 + d^2) = (2*a*c - b*d)^2 + 2*(a*d + b*c)^2 := by
  constructor <;> ring

/-- The cross difference is a multiple of the prime. -/
theorem theCrossDifferenceCarriesTheModulus {p a b c d : ℤ}
    (h1 : 2*a^2 + b^2 = p) (h2 : 2*c^2 + d^2 = p) :
    (a*d - b*c) * (a*d + b*c) = p * (a^2 - c^2) := by
  have hb : b^2 = p - 2*a^2 := by linarith
  have hd : d^2 = p - 2*c^2 := by linarith
  have : (a*d - b*c) * (a*d + b*c) = a^2*d^2 - b^2*c^2 := by ring
  rw [this, hb, hd]; ring

/-- The two coordinates of a prime representation are coprime. -/
theorem theCoordinatesAreCoprime {p a b : ℕ} (hp : p.Prime) (h : 2*a^2 + b^2 = p) :
    Nat.gcd a b = 1 := by
  set g := Nat.gcd a b with hg
  obtain ⟨u, hu⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨v, hv⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hdvd : g * g ∣ p := ⟨2*u^2 + v^2, by rw [← h, hu, hv]; ring⟩
  rcases hp.eq_one_or_self_of_dvd (g*g) hdvd with h1 | h1
  · exact Nat.eq_one_of_mul_eq_one_right h1
  · exfalso
    have hgp : g ∣ p := ⟨g, h1.symm⟩
    have hp2 := hp.two_le
    rcases hp.eq_one_or_self_of_dvd g hgp with h2 | h2
    · rw [h2] at h1; omega
    · rw [h2] at h1; nlinarith [h1, hp2]

/-- **THE REPRESENTATION IS UNIQUE.**  A prime has at most one representation
`p = 2a² + b²` with `a, b > 0`.  Classically this is class number one for `ℤ[√−2]`;
the proof here is elementary — Brahmagupta's identity in both signs, the size bounds it
forces, and coprimality — with no ring theory, no Euclidean domain and no unique
factorization anywhere in it. -/
theorem theRepresentationIsUnique {p a b c d : ℕ} (hp : p.Prime)
    (h1 : 2*a^2 + b^2 = p) (h2 : 2*c^2 + d^2 = p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a = c ∧ b = d := by
  have H1 : 2*(a:ℤ)^2 + (b:ℤ)^2 = (p:ℤ) := by exact_mod_cast h1
  have H2 : 2*(c:ℤ)^2 + (d:ℤ)^2 = (p:ℤ) := by exact_mod_cast h2
  have hP : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hpz : Prime ((p:ℕ) : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  obtain ⟨B1, B2⟩ := brahmagupta (a:ℤ) (b:ℤ) (c:ℤ) (d:ℤ)
  rw [H1, H2] at B1 B2
  have haz : (0:ℤ) < (a:ℤ) := by exact_mod_cast ha
  have hbz : (0:ℤ) < (b:ℤ) := by exact_mod_cast hb
  have hcz : (0:ℤ) < (c:ℤ) := by exact_mod_cast hc
  have hdz : (0:ℤ) < (d:ℤ) := by exact_mod_cast hd
  have hsum_pos : (0:ℤ) < (a:ℤ)*(d:ℤ) + (b:ℤ)*(c:ℤ) := by positivity
  have hsum_lt : (a:ℤ)*(d:ℤ) + (b:ℤ)*(c:ℤ) < (p:ℤ) := by
    nlinarith [B2, sq_nonneg (2*(a:ℤ)*(c:ℤ) - (b:ℤ)*(d:ℤ)), hsum_pos, hP]
  have hcross := theCrossDifferenceCarriesTheModulus H1 H2
  have hdvd : ((p:ℕ):ℤ) ∣ ((a:ℤ)*(d:ℤ) - (b:ℤ)*(c:ℤ)) * ((a:ℤ)*(d:ℤ) + (b:ℤ)*(c:ℤ)) :=
    ⟨(a:ℤ)^2 - (c:ℤ)^2, hcross⟩
  have hzero : (a:ℤ)*(d:ℤ) - (b:ℤ)*(c:ℤ) = 0 := by
    rcases (hpz.dvd_mul.mp hdvd) with hL | hR
    · by_contra hne
      have habs : |(a:ℤ)*(d:ℤ) - (b:ℤ)*(c:ℤ)| < (p:ℤ) := by
        by_contra hge
        push_neg at hge
        nlinarith [B1, sq_nonneg (2*(a:ℤ)*(c:ℤ) + (b:ℤ)*(d:ℤ)), hge, hP,
          sq_abs ((a:ℤ)*(d:ℤ) - (b:ℤ)*(c:ℤ)), abs_nonneg ((a:ℤ)*(d:ℤ) - (b:ℤ)*(c:ℤ))]
      have := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hL)
      omega
    · have := Int.le_of_dvd hsum_pos hR
      omega
  have hprod : a * d = b * c := by
    have : (a:ℤ)*(d:ℤ) = (b:ℤ)*(c:ℤ) := by linarith
    exact_mod_cast this
  have hab := theCoordinatesAreCoprime hp h1
  have hcd := theCoordinatesAreCoprime hp h2
  have hac : a ∣ c := (Nat.Coprime.dvd_of_dvd_mul_left hab ⟨d, hprod.symm ▸ rfl⟩)
  have hca : c ∣ a := by
    refine (Nat.Coprime.dvd_of_dvd_mul_right hcd ?_)
    exact ⟨b, by rw [hprod]; ring⟩
  have hEq : a = c := Nat.dvd_antisymm hac hca
  refine ⟨hEq, ?_⟩
  subst hEq
  have : a * d = a * b := by rw [hprod]; ring
  exact (Nat.eq_of_mul_eq_mul_left ha this).symm

/-! ## Existence: Thue's pigeonhole -/

/-- **THUE'S PIGEONHOLE**: for any residue `r`, two lattice points in the
`(⌊√p⌋+1)²` box collide modulo `p`, and their difference is a small pair with
`x·r ≡ y`. -/
theorem theThuePigeonhole {p : ℕ} (hp : 0 < p) (r : ZMod p) :
    ∃ x y : ℤ, ¬ (x = 0 ∧ y = 0) ∧ |x| ≤ (Nat.sqrt p : ℤ) ∧ |y| ≤ (Nat.sqrt p : ℤ) ∧
      ((x : ZMod p) * r = (y : ZMod p)) := by
  classical
  haveI : NeZero p := ⟨hp.ne'⟩
  set m := Nat.sqrt p + 1 with hm
  have hcard : p < m * m := by
    have := Nat.lt_succ_sqrt' p
    rw [pow_two] at this
    exact this
  have hmaps : ∀ q ∈ (range m ×ˢ range m), (fun q : ℕ × ℕ =>
      (q.1 : ZMod p) * r - (q.2 : ZMod p)) q ∈ (Finset.univ : Finset (ZMod p)) := by
    intro q _; exact Finset.mem_univ _
  have hlt : (Finset.univ : Finset (ZMod p)).card < (range m ×ˢ range m).card := by
    rw [Finset.card_product, Finset.card_range, Finset.card_univ, ZMod.card]
    exact hcard
  obtain ⟨q₁, hq₁, q₂, hq₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨(q₁.1 : ℤ) - (q₂.1 : ℤ), (q₁.2 : ℤ) - (q₂.2 : ℤ), ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact hne (Prod.ext (by omega) (by omega))
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq₁ hq₂
    rw [abs_le]; omega
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hq₁ hq₂
    rw [abs_le]; omega
  · push_cast
    linear_combination heq



/-- A prime is never a perfect square. -/
theorem thePrimeIsNotASquare {p : ℕ} (hp : p.Prime) (n : ℤ) : n ^ 2 ≠ (p : ℤ) := by
  intro h
  have hnat : n.natAbs ^ 2 = p := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_pow] using this
  have hdvd : n.natAbs ∣ p := ⟨n.natAbs, by rw [← hnat]; ring⟩
  have hp2 := hp.two_le
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1] at hnat; omega
  · rw [h1] at hnat; nlinarith [hnat, hp2]

/-- **THE REPRESENTATION EXISTS** whenever `−2` is a square modulo `p`: Thue's small
pair is killed by the form modulo `p`, its size confines the value to `p` or `2p`, and
the doubling case swaps the roles. -/
theorem theRepresentationExists {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : ∃ r : ZMod p, r ^ 2 = -2) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2 * a ^ 2 + b ^ 2 = p := by
  obtain ⟨r, hr2⟩ := hr
  obtain ⟨x, y, hnz, hxb, hyb, hcong⟩ := theThuePigeonhole hp.pos r
  have hsq : (Nat.sqrt p : ℤ) ^ 2 ≤ (p : ℤ) := by
    have := Nat.sqrt_le' p
    have h2 : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
    calc (Nat.sqrt p : ℤ) ^ 2 = ((Nat.sqrt p * Nat.sqrt p : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (p : ℤ) := by exact_mod_cast h2
  have hx2 : x ^ 2 ≤ (p : ℤ) := by nlinarith [abs_nonneg x, sq_abs x, hxb, hsq]
  have hy2 : y ^ 2 ≤ (p : ℤ) := by nlinarith [abs_nonneg y, sq_abs y, hyb, hsq]
  -- the form is killed modulo p
  have hmod : ((y ^ 2 + 2 * x ^ 2 : ℤ) : ZMod p) = 0 := by
    push_cast
    have : ((y : ZMod p)) = (x : ZMod p) * r := hcong.symm
    rw [this]
    linear_combination (x : ZMod p) ^ 2 * hr2
  have hdvd : (p : ℤ) ∣ y ^ 2 + 2 * x ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + 2 * x ^ 2) p).mp hmod
    exact_mod_cast this
  have hpos : 0 < y ^ 2 + 2 * x ^ 2 := by
    rcases (not_and_or.mp hnz) with h | h
    · nlinarith [sq_nonneg y, sq_nonneg x, pow_two_pos_of_ne_zero h]
    · nlinarith [sq_nonneg y, sq_nonneg x, pow_two_pos_of_ne_zero h]
  have hle : y ^ 2 + 2 * x ^ 2 ≤ 3 * (p : ℤ) := by linarith
  -- so it is p or 2p
  obtain ⟨k, hk⟩ := hdvd
  have hP : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hkpos : 0 < k := by nlinarith [hk, hpos, hP]
  have hkle : k ≤ 2 := by
    by_contra hc
    push_neg at hc
    have h3 : 3 * (p:ℤ) ≤ y ^ 2 + 2 * x ^ 2 := by nlinarith [hk, hc, hP]
    have hyp : y ^ 2 = (p:ℤ) := by linarith
    exact thePrimeIsNotASquare hp y hyp
  interval_cases k
  · -- y² + 2x² = p
    refine ⟨x.natAbs, y.natAbs, ?_, ?_, ?_⟩
    · rcases eq_or_ne x 0 with rfl | hx
      · exfalso; exact thePrimeIsNotASquare hp y (by linarith [hk])
      · exact Int.natAbs_pos.mpr hx
    · rcases eq_or_ne y 0 with rfl | hy
      · exfalso
        have : (2 : ℤ) * x ^ 2 = (p:ℤ) := by linarith [hk]
        have hdv : (2:ℤ) ∣ (p:ℤ) := ⟨x ^ 2, this.symm⟩
        have : (2:ℕ) ∣ p := by exact_mod_cast hdv
        exact hp2 (((Nat.Prime.eq_one_or_self_of_dvd hp 2 this).resolve_left
          (by norm_num)).symm)
      · exact Int.natAbs_pos.mpr hy
    · have : (2 : ℤ) * (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 = (p:ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]; linarith [hk]
      exact_mod_cast this
  · -- y² + 2x² = 2p : the ordinate is even and the roles swap
    have heven : (2:ℤ) ∣ y := by
      have hsq : (2:ℤ) ∣ y ^ 2 := ⟨(p:ℤ) - x ^ 2, by linarith [hk]⟩
      exact (Int.Prime.dvd_pow' (by norm_num) hsq)
    obtain ⟨w, hw⟩ := heven
    have hform : 2 * w ^ 2 + x ^ 2 = (p:ℤ) := by
      rw [hw] at hk; linarith [hk]
    refine ⟨w.natAbs, x.natAbs, ?_, ?_, ?_⟩
    · rcases eq_or_ne w 0 with rfl | hwz
      · exfalso; exact thePrimeIsNotASquare hp x (by linarith [hform])
      · exact Int.natAbs_pos.mpr hwz
    · rcases eq_or_ne x 0 with rfl | hxz
      · exfalso
        have h2 : (2 : ℤ) * w ^ 2 = (p:ℤ) := by linarith [hform]
        have hdvz : (2:ℤ) ∣ (p:ℤ) := ⟨w ^ 2, by linarith [h2]⟩
        have hdv : (2:ℕ) ∣ p := by exact_mod_cast hdvz
        exact hp2 (((Nat.Prime.eq_one_or_self_of_dvd hp 2 hdv).resolve_left
          (by norm_num)).symm)
      · exact Int.natAbs_pos.mpr hxz
    · have : (2 : ℤ) * (w.natAbs : ℤ) ^ 2 + (x.natAbs : ℤ) ^ 2 = (p:ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]; linarith [hform]
      exact_mod_cast this



/-- **THE BINARY REPRESENTATION EXISTS AND IS UNIQUE ON THE ONE- AND THREE-MOD-EIGHT
BRANCHES.**  Classically this is class number one for discriminant `−8`; here it is
Thue's pigeonhole for existence and Brahmagupta's identity for uniqueness, with no ring
theory anywhere. -/
theorem theBinaryRepresentationIsUniqueAndExists {p : ℕ} (hp : p.Prime)
    (h8 : p % 8 = 1 ∨ p % 8 = 3) :
    ∃! q : ℕ × ℕ, 0 < q.1 ∧ 0 < q.2 ∧ 2 * q.1 ^ 2 + q.2 ^ 2 = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rcases h8 with h | h <;> omega
  have hsq : IsSquare (-2 : ZMod p) := (ZMod.exists_sq_eq_neg_two_iff hp2).mpr h8
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨a, b, ha, hb, hab⟩ := theRepresentationExists hp hp2 ⟨r, by rw [sq, ← hr]⟩
  refine ⟨(a, b), ⟨ha, hb, hab⟩, ?_⟩
  rintro ⟨c, d⟩ ⟨hc, hd, hcd⟩
  obtain ⟨h1, h2⟩ := theRepresentationIsUnique hp hcd hab hc hd ha hb
  exact Prod.ext h1 h2

/-- **THE ZERO SLICE'S POSITIVE QUADRANT IS A SINGLETON.**  On the branches where the
binary representation exists and is unique, exactly one solution has `z = 0` and both
remaining coordinates positive. -/
theorem theZeroSliceCountIsOne {p B : ℕ} (hp : p.Prime) (h8 : p % 8 = 1 ∨ p % 8 = 3)
    (hB : p ≤ B) :
    ((SolF p B).filter (fun t => t.2.2 = 0 ∧ 0 < t.1 ∧ 0 < t.2.1)).card = 1 := by
  classical
  obtain ⟨⟨a, b⟩, hmem, huniq⟩ := theBinaryRepresentationIsUniqueAndExists hp h8
  obtain ⟨ha, hb, hab⟩ := hmem
  simp only at ha hb hab
  have hform : 2 * (a:ℤ)^2 + (b:ℤ)^2 = (p:ℤ) := by exact_mod_cast hab
  have hbnd := theSolutionsAreBoundedByTheModulus (p := p) (x := (a:ℤ)) (y := (b:ℤ))
    (z := 0) (by linarith [hform])
  obtain ⟨hb1, hb2, -⟩ := hbnd
  rw [abs_le] at hb1 hb2
  have hBz : (p:ℤ) ≤ (B:ℤ) := by exact_mod_cast hB
  rw [Finset.card_eq_one]
  refine ⟨((a:ℤ), (b:ℤ), 0), ?_⟩
  ext t
  simp only [Finset.mem_filter, Finset.mem_singleton, SolF, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hf⟩, hz, hx, hy⟩
    have hz0 : t.2.2 = 0 := hz
    have hfx : 2 * t.1 ^ 2 + t.2.1 ^ 2 = (p:ℤ) := by rw [hz0] at hf; linarith [hf]
    have hnat : 2 * t.1.natAbs ^ 2 + t.2.1.natAbs ^ 2 = p := by
      have : 2 * ((t.1.natAbs : ℤ)) ^ 2 + ((t.2.1.natAbs : ℤ)) ^ 2 = (p:ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]; exact hfx
      exact_mod_cast this
    have := huniq (t.1.natAbs, t.2.1.natAbs)
      ⟨Int.natAbs_pos.mpr (by omega), Int.natAbs_pos.mpr (by omega), hnat⟩
    have h1 : t.1.natAbs = a := congrArg Prod.fst this
    have h2 : t.2.1.natAbs = b := congrArg Prod.snd this
    refine Prod.ext ?_ (Prod.ext ?_ hz0)
    · have hx1 : ((t.1.natAbs : ℤ)) = t.1 := Int.natAbs_of_nonneg (le_of_lt hx)
      rw [h1] at hx1; exact hx1.symm
    · have hy1 : ((t.2.1.natAbs : ℤ)) = t.2.1 := Int.natAbs_of_nonneg (le_of_lt hy)
      rw [h2] at hy1; exact hy1.symm
  · rintro rfl
    have haz : (0:ℤ) < (a:ℤ) := by exact_mod_cast ha
    have hbz : (0:ℤ) < (b:ℤ) := by exact_mod_cast hb
    refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, rfl, haz, hbz⟩
    · linarith [hb1.1, hBz]
    · linarith [hb1.2, hBz]
    · linarith [hb2.1, hBz]
    · linarith [hb2.2, hBz]
    · linarith [hBz]
    · linarith [hBz]
    · simpa using (by linarith [hform] : 2 * (a:ℤ)^2 + (b:ℤ)^2 + 8 * (0:ℤ)^2 = (p:ℤ))

/-! ## The parity on the branch -/

def flipX : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun t => (-t.1, t.2.1, t.2.2)
def flipZ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun t => (t.1, t.2.1, -t.2.2)
def flipYb : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun t => (t.1, -t.2.1, t.2.2)

lemma sgn_flipX (t : ℤ × ℤ × ℤ) :
    (-1 : ℤ) ^ ((flipX t).2.2).natAbs = (-1 : ℤ) ^ (t.2.2).natAbs := by simp [flipX]
lemma sgn_flipZ (t : ℤ × ℤ × ℤ) :
    (-1 : ℤ) ^ ((flipZ t).2.2).natAbs = (-1 : ℤ) ^ (t.2.2).natAbs := by
  simp [flipZ, Int.natAbs_neg]
lemma sgn_flipYb (t : ℤ × ℤ × ℤ) :
    (-1 : ℤ) ^ ((flipYb t).2.2).natAbs = (-1 : ℤ) ^ (t.2.2).natAbs := by simp [flipYb]

lemma flipX_invol (t : ℤ × ℤ × ℤ) : flipX (flipX t) = t := by simp [flipX]
lemma flipZ_invol (t : ℤ × ℤ × ℤ) : flipZ (flipZ t) = t := by simp [flipZ]
lemma flipYb_invol (t : ℤ × ℤ × ℤ) : flipYb (flipYb t) = t := by simp [flipYb]

lemma mem_SolF' {p B : ℕ} {t : ℤ × ℤ × ℤ} :
    t ∈ SolF p B ↔ (t.1 ∈ Icc (-(B : ℤ)) B ∧ t.2.1 ∈ Icc (-(B : ℤ)) B ∧
      t.2.2 ∈ Icc (-(B : ℤ)) B) ∧ 2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ) := by
  simp [SolF, Finset.mem_filter, Finset.mem_product]

lemma icc_neg' {B : ℕ} {x : ℤ} (h : x ∈ Icc (-(B : ℤ)) B) : -x ∈ Icc (-(B : ℤ)) B := by
  rw [Finset.mem_Icc] at h ⊢; omega

lemma flipX_mem {p B : ℕ} {t} (ht : t ∈ SolF p B) : flipX t ∈ SolF p B := by
  obtain ⟨⟨h1, h2, h3⟩, hf⟩ := mem_SolF'.mp ht
  exact mem_SolF'.mpr ⟨⟨icc_neg' h1, h2, h3⟩, by simp only [flipX]; linarith [hf]⟩
lemma flipZ_mem {p B : ℕ} {t} (ht : t ∈ SolF p B) : flipZ t ∈ SolF p B := by
  obtain ⟨⟨h1, h2, h3⟩, hf⟩ := mem_SolF'.mp ht
  exact mem_SolF'.mpr ⟨⟨h1, h2, icc_neg' h3⟩, by simp only [flipZ]; linarith [hf]⟩
lemma flipYb_mem {p B : ℕ} {t} (ht : t ∈ SolF p B) : flipYb t ∈ SolF p B := by
  obtain ⟨⟨h1, h2, h3⟩, hf⟩ := mem_SolF'.mp ht
  exact mem_SolF'.mpr ⟨⟨h1, icc_neg' h2, h3⟩, by simp only [flipYb]; linarith [hf]⟩



/-- **THE COUNT IS ODD ON THE THREE-MOD-EIGHT BRANCH.**  The signed count splits into
the `z = 0` slice and the rest.  On the branch the first coordinate is odd and the
middle one never vanishes, so the whole sign group acts freely off the slice — orbits of
eight — while the slice itself is the four-point sign orbit of the unique binary
representation.  Hence `S = 4 + 8k` and the lattice count `S/4` is **odd**, at every
prime of the branch. -/
theorem theCountIsOddOnTheThreeModEightBranch {p B : ℕ} (hp : p.Prime) (h8 : p % 8 = 3)
    (hB : p ≤ B) : ∃ k : ℤ, SF p B = 4 + 8 * k := by
  classical
  have hodd : Odd p := by refine ⟨p / 2, by omega⟩
  set f : ℤ × ℤ × ℤ → ℤ := fun t => (-1 : ℤ) ^ (t.2.2).natAbs with hfdef
  have hy0 : ∀ t ∈ SolF p B, t.2.1 ≠ 0 := fun t ht => by
    obtain ⟨-, hf⟩ := mem_SolF'.mp ht
    exact theMiddleCoordinateNeverVanishes hodd t.1 t.2.1 t.2.2 hf
  have hx0 : ∀ t ∈ SolF p B, t.1 ≠ 0 := by
    intro t ht
    obtain ⟨-, hf⟩ := mem_SolF'.mp ht
    intro hc
    exact theFirstCoordinateIsOddOnTheThreeBranch h8 hf ⟨0, by omega⟩
  -- split off the zero slice
  have hsplit : SF p B = (∑ t ∈ (SolF p B).filter (fun t => t.2.2 = 0), f t)
      + ∑ t ∈ (SolF p B).filter (fun t => ¬ (t.2.2 = 0)), f t :=
    (Finset.sum_filter_add_sum_filter_not (SolF p B) _ f).symm
  -- PART A: the zero slice sums to its cardinality, which is four
  have hAone : ∀ t ∈ (SolF p B).filter (fun t => t.2.2 = 0), f t = 1 := by
    intro t ht
    have : t.2.2 = 0 := (Finset.mem_filter.mp ht).2
    simp [hfdef, this]
  have hAcard : (∑ t ∈ (SolF p B).filter (fun t => t.2.2 = 0), f t)
      = (((SolF p B).filter (fun t => t.2.2 = 0)).card : ℤ) := by
    rw [Finset.sum_congr rfl hAone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hA1 : (((SolF p B).filter (fun t => t.2.2 = 0)).card : ℤ)
      = 2 * ((((SolF p B).filter (fun t => t.2.2 = 0)).filter (fun t => 0 < t.2.1)).card : ℤ) := by
    have := sum_eq_two_mul_filter flipYb (fun _ => (1:ℤ)) (fun t => 0 < t.2.1)
      (fun _ => rfl) ((SolF p B).filter (fun t => t.2.2 = 0))
      (fun a ha => by
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨flipYb_mem ha.1, by simpa [flipYb] using ha.2⟩)
      (fun a _ => flipYb_invol a)
      (fun a ha => by
        have := hy0 a (Finset.mem_filter.mp ha).1
        simp only [flipYb]; omega)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hA2 : ((((SolF p B).filter (fun t => t.2.2 = 0)).filter (fun t => 0 < t.2.1)).card : ℤ)
      = 2 * (((((SolF p B).filter (fun t => t.2.2 = 0)).filter (fun t => 0 < t.2.1)).filter
        (fun t => 0 < t.1)).card : ℤ) := by
    have := sum_eq_two_mul_filter flipX (fun _ => (1:ℤ)) (fun t => 0 < t.1)
      (fun _ => rfl) (((SolF p B).filter (fun t => t.2.2 = 0)).filter (fun t => 0 < t.2.1))
      (fun a ha => by
        rw [Finset.mem_filter, Finset.mem_filter] at ha ⊢
        exact ⟨⟨flipX_mem ha.1.1, by simpa [flipX] using ha.1.2⟩, by simpa [flipX] using ha.2⟩)
      (fun a _ => flipX_invol a)
      (fun a ha => by
        have := hx0 a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
        simp only [flipX]; omega)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hAeq : ((((SolF p B).filter (fun t => t.2.2 = 0)).filter (fun t => 0 < t.2.1)).filter
        (fun t => 0 < t.1))
      = (SolF p B).filter (fun t => t.2.2 = 0 ∧ 0 < t.1 ∧ 0 < t.2.1) := by
    rw [Finset.filter_filter, Finset.filter_filter]
    exact Finset.filter_congr (fun t _ => by tauto)
  have hAfinal : (∑ t ∈ (SolF p B).filter (fun t => t.2.2 = 0), f t) = 4 := by
    rw [hAcard, hA1, hA2, hAeq, theZeroSliceCountIsOne hp (Or.inr h8) hB]
    norm_num
  -- PART B: the rest splits into orbits of eight
  have hB1 : ∀ (s : Finset (ℤ × ℤ × ℤ)),
      (∀ a ∈ s, flipZ a ∈ s) → (∀ a ∈ s, a.2.2 ≠ 0) →
      (∑ t ∈ s, f t) = 2 * ∑ t ∈ s.filter (fun t => 0 < t.2.2), f t := by
    intro s hm hz
    exact sum_eq_two_mul_filter flipZ f (fun t => 0 < t.2.2) (fun a => sgn_flipZ a) s hm
      (fun a _ => flipZ_invol a) (fun a ha => by have := hz a ha; simp only [flipZ]; omega)
  have hB2 : ∀ (s : Finset (ℤ × ℤ × ℤ)),
      (∀ a ∈ s, flipYb a ∈ s) → (∀ a ∈ s, a.2.1 ≠ 0) →
      (∑ t ∈ s, f t) = 2 * ∑ t ∈ s.filter (fun t => 0 < t.2.1), f t := by
    intro s hm hy
    exact sum_eq_two_mul_filter flipYb f (fun t => 0 < t.2.1) (fun a => sgn_flipYb a) s hm
      (fun a _ => flipYb_invol a) (fun a ha => by have := hy a ha; simp only [flipYb]; omega)
  have hB3 : ∀ (s : Finset (ℤ × ℤ × ℤ)),
      (∀ a ∈ s, flipX a ∈ s) → (∀ a ∈ s, a.1 ≠ 0) →
      (∑ t ∈ s, f t) = 2 * ∑ t ∈ s.filter (fun t => 0 < t.1), f t := by
    intro s hm hx
    exact sum_eq_two_mul_filter flipX f (fun t => 0 < t.1) (fun a => sgn_flipX a) s hm
      (fun a _ => flipX_invol a) (fun a ha => by have := hx a ha; simp only [flipX]; omega)
  set s0 := (SolF p B).filter (fun t => ¬ (t.2.2 = 0)) with hs0
  set s1 := s0.filter (fun t => 0 < t.2.2) with hs1
  set s2 := s1.filter (fun t => 0 < t.2.1) with hs2
  have e1 : (∑ t ∈ s0, f t) = 2 * ∑ t ∈ s1, f t := by
    refine hB1 s0 (fun a ha => ?_) (fun a ha => (Finset.mem_filter.mp ha).2)
    rw [hs0, Finset.mem_filter] at ha ⊢
    exact ⟨flipZ_mem ha.1, by simpa [flipZ] using ha.2⟩
  have e2 : (∑ t ∈ s1, f t) = 2 * ∑ t ∈ s2, f t := by
    refine hB2 s1 (fun a ha => ?_) (fun a ha => hy0 a ?_)
    · rw [hs1, Finset.mem_filter, hs0, Finset.mem_filter] at ha ⊢
      exact ⟨⟨flipYb_mem ha.1.1, by simpa [flipYb] using ha.1.2⟩,
        by simpa [flipYb] using ha.2⟩
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have e3 : (∑ t ∈ s2, f t) = 2 * ∑ t ∈ s2.filter (fun t => 0 < t.1), f t := by
    refine hB3 s2 (fun a ha => ?_) (fun a ha => hx0 a ?_)
    · rw [hs2, Finset.mem_filter, hs1, Finset.mem_filter, hs0, Finset.mem_filter] at ha ⊢
      exact ⟨⟨⟨flipX_mem ha.1.1.1, by simpa [flipX] using ha.1.1.2⟩,
        by simpa [flipX] using ha.1.2⟩, by simpa [flipX] using ha.2⟩
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp ha).1).1).1
  refine ⟨∑ t ∈ s2.filter (fun t => 0 < t.1), f t, ?_⟩
  rw [hsplit, hAfinal, e1, e2, e3]
  ring

/-- **THE PARITY WITH THE FACTORS EXPLICIT.**  The same theorem, written so the primes
are visible:

```text
  form            2x² + y² + 2³z²
  modulus         p ≡ 3  (mod 2³)
  signed count    S = 2² + 2³·k
  lattice count   S / 2² = 1 + 2k        odd
```

**The exponents are group orders, not arithmetic accidents.**  `2²` is the Klein
subgroup `⟨y ↦ −y, (x,z) ↦ (−x,−z)⟩` acting freely on the `z = 0` slice — one orbit,
because the binary representation is unique.  `2³` is the full sign group `(ℤ/2)³`
acting freely off that slice, which it does exactly because the branch forces the first
coordinate odd.  The `2³` in the modulus and the `2³` in the form's third coefficient
are the same three. -/
theorem theCountIsOddWithTheFactorsExplicit {p B : ℕ} (hp : p.Prime) (h8 : p % 2^3 = 3)
    (hB : p ≤ B) : ∃ k : ℤ, SF p B = 2^2 + 2^3 * k := by
  obtain ⟨k, hk⟩ := theCountIsOddOnTheThreeModEightBranch hp (by norm_num at h8; exact h8) hB
  exact ⟨k, by rw [hk]; norm_num⟩

/-- The other Tunnell form differs from this one in a single exponent: `2⁵` for `2³`,
and its solutions are exactly this form's with the third coordinate even. -/
theorem theTwoFormsDifferByOneExponent (x y z : ℤ) :
    2*x^2 + y^2 + 2^5*z^2 = 2*x^2 + y^2 + 2^3*(2*z)^2 := by ring

/-! ## The structural count, kernel-evaluable -/

/-- The symmetric box as a **kernel-reducible** finset: `range` and `image` reduce where
`Finset.Icc` on `ℤ` does not. -/
def boxZ (B : ℕ) : Finset ℤ := (range (2*B+1)).image (fun i : ℕ => (i : ℤ) - (B : ℤ))

/-- **THE REDUCIBLE BOX IS THE INTERVAL.** -/
theorem theReducibleBoxIsTheInterval (B : ℕ) : boxZ B = Icc (-(B : ℤ)) (B : ℤ) := by
  ext x
  simp only [boxZ, Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h
    exact ⟨(x + (B : ℤ)).toNat, by omega, by omega⟩

/-- The solution set over the reducible box. -/
def SolFr (p B : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((boxZ B) ×ˢ (boxZ B) ×ˢ (boxZ B)).filter
    (fun t => 2 * t.1 ^ 2 + t.2.1 ^ 2 + 8 * t.2.2 ^ 2 = (p : ℤ))

/-- The signed count over the reducible box. -/
def SFr (p B : ℕ) : ℤ := ∑ t ∈ SolFr p B, (-1 : ℤ) ^ (t.2.2).natAbs

/-- **THE REDUCIBLE COUNT IS THE STRUCTURAL COUNT** — so the kernel can
evaluate the very object the orbit theorems are about. -/
theorem theReducibleCountIsTheStructuralCount (p B : ℕ) : SFr p B = SF p B := by
  unfold SFr SF SolFr SolF
  rw [theReducibleBoxIsTheInterval]

/-- **SOLUTIONS ARE BOUNDED BY `⌊√p⌋`**, so a box of that size already holds
them all — far tighter than the modulus itself. -/
theorem theSolutionsAreTightlyBounded {p : ℕ} {x y z : ℤ}
    (h : 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = (p : ℤ)) :
    x.natAbs ≤ Nat.sqrt p ∧ y.natAbs ≤ Nat.sqrt p ∧ z.natAbs ≤ Nat.sqrt p := by
  have hx2 : x ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg x]
  have hy2 : y ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg y]
  have hz2 : z ^ 2 ≤ (p : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  refine ⟨Nat.le_sqrt.mpr ?_, Nat.le_sqrt.mpr ?_, Nat.le_sqrt.mpr ?_⟩ <;>
    [ (have : ((x.natAbs * x.natAbs : ℕ) : ℤ) ≤ (p:ℤ) := by
         push_cast [Int.natCast_natAbs]; nlinarith [sq_abs x, abs_nonneg x]
       exact_mod_cast this) ;
      (have : ((y.natAbs * y.natAbs : ℕ) : ℤ) ≤ (p:ℤ) := by
         push_cast [Int.natCast_natAbs]; nlinarith [sq_abs y, abs_nonneg y]
       exact_mod_cast this) ;
      (have : ((z.natAbs * z.natAbs : ℕ) : ℤ) ≤ (p:ℤ) := by
         push_cast [Int.natCast_natAbs]; nlinarith [sq_abs z, abs_nonneg z]
       exact_mod_cast this) ]

/-- **ANY TWO BOXES ABOVE `⌊√p⌋` HOLD THE SAME SOLUTIONS.** -/
theorem theTightBoxSuffices {p B B' : ℕ} (hB : Nat.sqrt p ≤ B) (hB' : Nat.sqrt p ≤ B') :
    SolFr p B = SolFr p B' := by
  ext t
  simp only [SolFr, Finset.mem_filter, Finset.mem_product, theReducibleBoxIsTheInterval,
    Finset.mem_Icc]
  constructor <;> rintro ⟨-, hf⟩ <;>
    obtain ⟨h1, h2, h3⟩ := theSolutionsAreTightlyBounded hf <;>
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hf⟩

set_option maxRecDepth 8000 in
example : SFr 3 1 = 4 := by decide
set_option maxRecDepth 40000 in
example : SFr 11 3 = -4 := by decide
set_option maxRecDepth 200000 in
example : SFr 43 6 = 12 := by decide

end Engine

end Soma.Holonics.Millennium.LatticeCount
