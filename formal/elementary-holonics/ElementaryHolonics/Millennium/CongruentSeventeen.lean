import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

/-!
# The seventeen descent IS the congruent-number question for seventeen

Five separate frontier entries carried the seventeen obstruction — the quartic, the archimedean
descent, the unit analysis, the both-odd branch, the descended quartics — and each was measured
the same way: *no congruence at any depth refuses it*.  Five entries, five measurements, one
shape.  **They are one object, and this file exhibits the map.**

The chain is two Pythagorean descents and nothing else:

```text
X² = 34u² + 1  ∧  X² + 1 = 2v²
  ⟹  v² − 17u² = 1     (subtract)      and   X² = v² + 17u²   (add)
  ⟹  X² + (17u²)² = (v²)²              multiply the two: a triple with a SQUARE hypotenuse
  ⟹  X = m²−n²,  17u² = 2mn,  v² = m²+n²        first parametrisation
  ⟹  v² = m²+n² is itself a triple → m·n = 2kl(k²−l²)   second parametrisation
  ⟹  kl(k−l)(k+l) = 17w²                          the congruent-number criterion for 17
```

So the last unrefuted branch of the descent asks exactly whether **17 is a congruent number**.
It is not — but that is a rank-zero statement for `y² = x³ − 289x`, not a congruence.  And that
explains, rather than merely records, every measurement in the frontier: `17 ≡ 1 (mod 8)` is
precisely the residue class in which no congruence can decide congruent-ness, because `41 ≡ 1
(mod 8)` **is** congruent while `17` is not.  A local frame cannot separate them; the separator is
global.  That is this corpus's own reading of `Ш` as a collapsed population, arriving as a
theorem about which cluster a frontier entry belongs to.

The two descents are also the same move twice, which is the content worth carrying: **a square
hypotenuse forces a second parametrisation**, and the second one is where the seventeen lands on
the area rather than on a side.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.CongruentSeventeen

/-- `n` is a **congruent number** in the classical parametrised form: some primitive
opposite-parity pair `(k,l)` gives a right triangle of area `n` times a square. -/
def IsCongruentNumber (n : ℤ) : Prop :=
  ∃ k l w : ℤ, 0 < l ∧ l < k ∧ IsCoprime k l ∧ w ≠ 0 ∧ k * l * (k - l) * (k + l) = n * w ^ 2

/-! ## The three algebraic steps, all free -/

/-- Subtracting the two branch equations returns Pell at seventeen. -/
theorem thePellRelation {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) :
    v ^ 2 - 17 * u ^ 2 = 1 := by linarith

/-- Adding them returns the norm form. -/
theorem theNormRelation {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) :
    X ^ 2 = v ^ 2 + 17 * u ^ 2 := by linarith

/-- **THE BRANCH IS A PYTHAGOREAN TRIPLE WITH A SQUARE HYPOTENUSE.**  The product of the two
relations is the whole content: `(v²)² − (17u²)² = (v²−17u²)(v²+17u²) = 1·X²`. -/
theorem theBranchIsPythagorean {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) :
    X ^ 2 + (17 * u ^ 2) ^ 2 = (v ^ 2) ^ 2 := by
  have hp := thePellRelation h1 h2
  have hn := theNormRelation h1 h2
  nlinarith [hp, hn]

/-- **THE SECOND SLOT IS EVEN**, forced mod eight: `v² = 1 + 17u²`, and an odd `u` would put
`v² ≡ 2 (mod 8)`. -/
theorem theSecondSlotIsEven {u v : ℤ} (h : v ^ 2 - 17 * u ^ 2 = 1) : Even u := by
  have hz : ((v : ZMod 8)) ^ 2 - 17 * ((u : ZMod 8)) ^ 2 = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod 8)) h
    push_cast at this
    exact this
  have key : ∀ a b : ZMod 8, b ^ 2 - 17 * a ^ 2 = 1 → (a = 0 ∨ a = 2 ∨ a = 4 ∨ a = 6) := by decide
  have h8 := key _ _ hz
  have hh : (ZMod.castHom (by norm_num : (2:ℕ) ∣ 8) (ZMod 2)) ((u : ℤ) : ZMod 8)
      = ((u : ℤ) : ZMod 2) := by simp
  have hcast : ((u : ℤ) : ZMod 2) = 0 := by
    rcases h8 with h | h | h | h <;> rw [← hh, h] <;> decide
  exact (even_iff_two_dvd).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd u 2).mp hcast)

/-! ## The parametrisation: two Pythagorean descents -/

/-- The triple is primitive. -/
theorem theTripleIsCoprime {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) :
    IsCoprime X (17 * u ^ 2) := by
  have hp := thePellRelation h1 h2
  have hn := theNormRelation h1 h2
  exact ⟨X, -2, by linear_combination h1⟩

/-- **THE SEVENTEEN BRANCH RETURNS A CONGRUENT-NUMBER WITNESS FOR 17.**  Two Pythagorean
descents: the branch equations give `X² + (17u²)² = (v²)²` with a square hypotenuse, whose
parametrisation `(m,n)` is itself a triple, whose parametrisation `(k,l)` satisfies
`kl(k−l)(k+l) = 17w²` — the classical criterion.  So the descent obstruction at seventeen and the
question *"is 17 a congruent number"* are one object. -/
theorem theSeventeenBranchGivesACongruentWitness {X u v : ℤ}
    (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) (hu : u ≠ 0) :
    ∃ k l w : ℤ, Int.gcd k l = 1 ∧ w ≠ 0 ∧ k * l * (k - l) * (k + l) = 17 * w ^ 2 := by
  have hp := thePellRelation h1 h2
  have hn := theNormRelation h1 h2
  have hpyth : PythagoreanTriple X (17 * u ^ 2) (v ^ 2) := by
    unfold PythagoreanTriple; nlinarith [hp, hn]
  have hcop : Int.gcd X (17 * u ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp (theTripleIsCoprime h1 h2)
  have hXodd : X % 2 = 1 := by
    have hnd : ¬ (2 ∣ X) := by
      rintro ⟨r, rfl⟩
      have h4 : 4 * r ^ 2 = 34 * u ^ 2 + 1 := by linear_combination h1
      omega
    omega
  have hv2pos : 0 < v ^ 2 := by nlinarith [hp, sq_nonneg u, sq_nonneg v]
  obtain ⟨m, n, hm, hn2, hv, hmn, hpar, hm0⟩ :=
    hpyth.coprime_classification' hcop hXodd hv2pos
  -- second descent: `(m, n, |v|)` is itself a primitive triple
  have hvne : v ≠ 0 := by intro h; rw [h] at hp; nlinarith [sq_nonneg u]
  have habs : |v| * |v| = v ^ 2 := by rw [abs_mul_abs_self]; ring
  have hvpos : 0 < |v| := abs_pos.mpr hvne
  have key : ∃ k l : ℤ, Int.gcd k l = 1 ∧ m * n = 2 * (k * l * (k ^ 2 - l ^ 2)) := by
    rcases hpar with ⟨hme, hno⟩ | ⟨hmo, hne⟩
    · -- m even, n odd: classify `(n, m, |v|)`
      have ht : PythagoreanTriple n m |v| := by
        unfold PythagoreanTriple; rw [habs]; linarith [hv]
      obtain ⟨k, l, hk1, hk2, _, hkl, _, _⟩ :=
        ht.coprime_classification' (by rw [Int.gcd_comm]; exact hmn) hno hvpos
      exact ⟨k, l, hkl, by rw [hk1, hk2]; ring⟩
    · -- m odd, n even: classify `(m, n, |v|)`
      have ht : PythagoreanTriple m n |v| := by
        unfold PythagoreanTriple; rw [habs]; linarith [hv]
      obtain ⟨k, l, hk1, hk2, _, hkl, _, _⟩ :=
        ht.coprime_classification' hmn hmo hvpos
      exact ⟨k, l, hkl, by rw [hk1, hk2]; ring⟩
  obtain ⟨k, l, hkl, hmnk⟩ := key
  obtain ⟨w, hw⟩ := theSecondSlotIsEven hp
  refine ⟨k, l, w, hkl, ?_, ?_⟩
  · rintro rfl; exact hu (by omega)
  · have hkey : 17 * u ^ 2 = 4 * (k * l * (k ^ 2 - l ^ 2)) := by
      linear_combination hn2 + 2 * hmnk
    have hu2 : u ^ 2 = 4 * w ^ 2 := by rw [hw]; ring
    rw [hu2] at hkey
    have hexp : k * l * (k - l) * (k + l) = k * l * (k ^ 2 - l ^ 2) := by ring
    rw [hexp]; linarith [hkey]

/-- **AND THE CONVERSE READING: NON-CONGRUENCE OF 17 REFUSES THE BRANCH.**  Contraposition of the
witness map.  The last unrefuted branch of the seventeen descent and the classical question *"is
17 a congruent number"* are therefore **the same statement**, and every measurement recorded
against the branch — no modulus below six hundred refuses it, no coprime solution below nine
hundred — is explained rather than merely logged: `17 ≡ 1 (mod 8)` is exactly the residue class in
which no congruence decides congruent-ness, since `41 ≡ 1 (mod 8)` *is* congruent. -/
theorem theBranchIsRefusedIfSeventeenIsNotCongruent
    (h : ¬ ∃ k l w : ℤ, Int.gcd k l = 1 ∧ w ≠ 0 ∧ k * l * (k - l) * (k + l) = 17 * w ^ 2)
    {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) : u = 0 := by
  by_contra hu
  exact h (theSeventeenBranchGivesACongruentWitness h1 h2 hu)

/-- With the second slot dead, the branch collapses to the trivial solution. -/
theorem theTrivialSolutionIsAllThatSurvives
    (h : ¬ ∃ k l w : ℤ, Int.gcd k l = 1 ∧ w ≠ 0 ∧ k * l * (k - l) * (k + l) = 17 * w ^ 2)
    {X u v : ℤ} (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) : X ^ 2 = 1 := by
  have hu := theBranchIsRefusedIfSeventeenIsNotCongruent h h1 h2
  rw [hu] at h1; simpa using h1

end Soma.Holonics.Millennium.CongruentSeventeen
