import ElementaryHolonics.Millennium.FamilyFace
import ElementaryHolonics.Millennium.ReflectionCensus
import ElementaryHolonics.Millennium.TateLedger
import ElementaryHolonics.Millennium.DistantWindings
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# BirchSwinnertonDyer: the conjecture, posed directly on the congruent-number family

**The pose.**  Everything before this file approached the conjecture through its
two-adic shadow; this file states the object itself, for the twists `y² = x³ − n²x`:

* **the arithmetic coefficients** are literal point counts: `a_p = p − #E^aff(𝔽_p)`
  (`traceOfFrobenius`), computed over `ZMod p` — no modular input, no declared table;
* **the analytic side** is a declared receiver: `LDatum n` carries an entire function
  `L : ℂ → ℂ`, its agreement with the Dirichlet series `LSeries` of the coefficients on
  the half-plane of convergence, the completed function
  `Λ(s) = (√N/2π)^s Γ(s) L(s)`, and the functional equation `Λ(2−s) = w·Λ(s)` with sign
  `w = ±1`.  For this family the witness exists classically through complex
  multiplication by the Gaussian integers (Hecke), and **constructing it in this tree —
  theta and Poisson summation, integration by reflection — is the named next deed**;
  the pose is honest about being conditional until then;
* **the analytic rank** is `analyticOrderAt L 1` — mathlib's vanishing order at the
  center;
* **the algebraic rank** is the independence predicate this corpus already uses:
  `AlgebraicRankAtLeast n r` demands `r` points no nonzero integer combination of which
  is torsion; no Mordell–Weil theorem is consumed by the definition;
* **the conjecture** (`TheBirchSwinnertonDyerConjecture`) is the conjunction of the
  rank clause — the vanishing order equals the algebraic rank — and the rank-zero
  ledger clause: the central value equals `|Ш| · ∏c / |T|²` times the real period, with
  the obstruction order carried as the **square** positive integer that the alternating
  pairing forces it to be (the parity theorem of this tree is why the square is honest).
  The higher-rank leading-coefficient clause needs the Néron–Tate height pairing, which
  no library owns; it is the named successor pose.

**What is already a theorem about the posed object, this same file:**

* `theCoefficientVanishesOnTheBlindFrames` — for every prime `p ≡ 3 (mod 4)` not
  dividing `2n`, every admissible datum has `coeff p = 0`: the reflection census
  (`a_p = 0` by the odd-function fold) becomes the first analytic-side law of the posed
  L-function, family-wise;
* `theAlgebraicRankAtFiveIsAtLeastOne` — the posed rank predicate is genuinely met at
  five, through the kernel-checked infinite-order point and the torsion classification;
* `theLedgerClauseHoldsAtOneGivenTheCentralValue` — granted the classical central value
  `L(1) = Ω/8`, the rank-zero ledger closes at one with `Ш` trivial and the Tamagawa
  and torsion numbers this tree computed in the Tate ledger.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the
existence of an `LDatum` witness is not claimed here (it is the theta/Poisson
construction, next); Tamagawa numbers enter the ledger clause as explicit parameters
whose values the Tate ledger computed per instance, not as a general definition (a
general definition needs minimal models); nothing about the conjecture is claimed as
proved.
-/

namespace Soma.Holonics.Millennium.BirchSwinnertonDyer

open WeierstrassCurve.Affine Finset

/-! ## 1. The arithmetic coefficients: literal point counts -/

/-- The affine point count of `y² = x³ − n²x` over `ZMod p`, as the sum of the fibre
counts the reflection census integrates. -/
def affineCount (n p : ℕ) [NeZero p] : ℕ :=
  ∑ x : ZMod p, (univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x).card

/-- The trace of Frobenius: `a_p = p + 1 − #E(𝔽_p) = p − #E^aff(𝔽_p)`. -/
def traceOfFrobenius (n p : ℕ) [NeZero p] : ℤ :=
  (p : ℤ) - affineCount n p

/-! ## 2. The analytic receiver: the declared continuation -/

open Complex in
/-- The completed L-function shape `Λ(s) = (√N / 2π)^s · Γ(s) · L(s)`. -/
noncomputable def completed (N : ℕ) (L : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((Real.sqrt N : ℂ) / (2 * Real.pi)) ^ s * Complex.Gamma s * L s

/-- **The declared analytic datum** for the twist at `n`: an entire function agreeing
with the Dirichlet series of the point-count coefficients on the convergence
half-plane, with the completed functional equation and a sign.  Classically such a
witness exists through the Gaussian complex multiplication (Hecke); constructing one is
the theta/Poisson deed this pose names. -/
structure LDatum (n : ℕ) where
  /-- The Dirichlet coefficients. -/
  coeff : ℕ → ℂ
  /-- Normalization. -/
  coeff_one : coeff 1 = 1
  /-- The coefficients are the point counts at the good primes. -/
  coeff_prime : ∀ p : ℕ, ∀ hp : p.Prime, ¬ p ∣ 2 * n →
    coeff p = ((@traceOfFrobenius n p ⟨hp.pos.ne'⟩ : ℤ) : ℂ)
  /-- Multiplicativity across coprime indices. -/
  coeff_mul : ∀ a b : ℕ, Nat.Coprime a b → coeff (a * b) = coeff a * coeff b
  /-- The Euler recursion at good prime powers. -/
  coeff_prime_pow : ∀ p k : ℕ, p.Prime → ¬ p ∣ 2 * n →
    coeff (p ^ (k + 2)) = coeff p * coeff (p ^ (k + 1)) - (p : ℂ) * coeff (p ^ k)
  /-- Bad prime powers carry the degenerate Euler factor. -/
  coeff_bad : ∀ p k : ℕ, p.Prime → p ∣ 2 * n → coeff (p ^ (k + 1)) = coeff p ^ (k + 1)
  /-- The analytic continuation. -/
  L : ℂ → ℂ
  /-- Entirety. -/
  analytic : Differentiable ℂ L
  /-- Agreement with the Dirichlet series where it converges. -/
  agrees : ∀ s : ℂ, 3 / 2 < s.re → L s = LSeries coeff s
  /-- The conductor. -/
  conductor : ℕ
  conductor_pos : 0 < conductor
  /-- The sign of the functional equation. -/
  sign : ℤ
  sign_pm : sign = 1 ∨ sign = -1
  /-- The completed functional equation. -/
  functional_equation : ∀ s : ℂ,
    completed conductor L (2 - s) = (sign : ℂ) * completed conductor L s

/-- **The analytic rank**: the order of vanishing of the continued L-function at the
center of the functional equation. -/
noncomputable def analyticRank {n : ℕ} (W : LDatum n) : ℕ∞ :=
  analyticOrderAt W.L 1

/-! ## 3. The algebraic rank, with no Mordell–Weil input -/

/-- A point of finite order. -/
def IsTorsion (n : ℕ) (P : (FamilyFace.E n).Point) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k • P = 0

/-- A family of points is independent modulo torsion when no nonzero integer
combination is torsion. -/
def IndependentModTorsion (n : ℕ) {r : ℕ} (Pts : Fin r → (FamilyFace.E n).Point) :
    Prop :=
  ∀ c : Fin r → ℤ, IsTorsion n (∑ i, c i • Pts i) → ∀ i, c i = 0

/-- The algebraic rank is at least `r`. -/
def AlgebraicRankAtLeast (n r : ℕ) : Prop :=
  ∃ Pts : Fin r → (FamilyFace.E n).Point, IndependentModTorsion n Pts

/-- The algebraic rank is exactly `r`. -/
def AlgebraicRankIs (n r : ℕ) : Prop :=
  AlgebraicRankAtLeast n r ∧ ¬ AlgebraicRankAtLeast n (r + 1)

/-! ## 4. The real period and the conjecture -/

open MeasureTheory in
/-- The real period of the twist: twice the integral of `dx/y` over the unbounded real
branch. -/
noncomputable def realPeriod (n : ℕ) : ℝ :=
  2 * ∫ x in Set.Ioi (n : ℝ), 1 / Real.sqrt (x ^ 3 - (n : ℝ) ^ 2 * x)

/-- **The rank clause of the conjecture**: the order of vanishing at the center equals
the algebraic rank. -/
def TheRankClause (n : ℕ) (W : LDatum n) : Prop :=
  ∀ r : ℕ, analyticRank W = (r : ℕ∞) ↔ AlgebraicRankIs n r

/-- **The rank-zero ledger clause**: at algebraic rank zero the central value is the
real period times `|Ш| · ∏c / |T|²`, with the obstruction order a positive **square**
integer — the square is forced by the alternating Cassels pairing, whose parity theorem
this tree carries.  The Tamagawa product and torsion order enter as parameters; the
Tate ledger computes them per instance. -/
def TheLedgerClause (n : ℕ) (W : LDatum n) (tamagawa torsion : ℕ) : Prop :=
  AlgebraicRankIs n 0 →
    ∃ sha : ℕ, 0 < sha ∧ IsSquare sha ∧
      W.L 1 = (((sha * tamagawa : ℕ) : ℂ) / ((torsion : ℂ) ^ 2)) * (realPeriod n : ℂ)

/-- **THE BIRCH–SWINNERTON-DYER CONJECTURE**, posed for the congruent-number twist at
`n` with declared analytic datum and arithmetic parameters: the rank clause together
with the rank-zero ledger clause.  The higher-rank leading-coefficient clause requires
the Néron–Tate height pairing and is the named successor pose. -/
def TheBirchSwinnertonDyerConjecture (n : ℕ) (W : LDatum n)
    (tamagawa torsion : ℕ) : Prop :=
  TheRankClause n W ∧ TheLedgerClause n W tamagawa torsion

/-! ## 5. The first theorems about the posed object -/

/-- **THE COEFFICIENT VANISHES ON THE BLIND FRAMES**: for every odd prime
`p ≡ 3 (mod 4)`, the affine count is exactly `p` — the reflection census — so the
trace of Frobenius vanishes.  The first analytic-side law of the posed L-function,
family-wise over both `n` and `p`. -/
theorem theCoefficientVanishesOnTheBlindFrames (n p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) :
    traceOfFrobenius n p = 0 := by
  have hcount : affineCount n p = p := by
    unfold affineCount
    have := ReflectionCensus.theReflectionIntegratesTheCensus (p := p) hp3
      (-(n : ZMod p) ^ 2)
    have hconv : ∀ x : ZMod p,
        (univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x) =
        (univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 + (-(n : ZMod p) ^ 2) * x) := by
      intro x
      congr 1
      ext y
      constructor
      · intro h
        rw [h]
        ring
      · intro h
        rw [h]
        ring
    have hsum : (∑ x : ZMod p,
        ((univ.filter fun y : ZMod p =>
          y ^ 2 = x ^ 3 + (-(n : ZMod p) ^ 2) * x).card : ℤ)) = p := this
    have : (∑ x : ZMod p,
        ((univ.filter fun y : ZMod p =>
          y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x).card : ℤ)) = p := by
      rw [show (∑ x : ZMod p,
          ((univ.filter fun y : ZMod p =>
            y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x).card : ℤ)) =
          (∑ x : ZMod p,
          ((univ.filter fun y : ZMod p =>
            y ^ 2 = x ^ 3 + (-(n : ZMod p) ^ 2) * x).card : ℤ)) from by
        congr 1
        ext x
        rw [hconv x]]
      exact hsum
    exact_mod_cast this
  unfold traceOfFrobenius
  rw [hcount]
  ring

/-- **The posed algebraic rank is at least one at five**: the kernel-checked
infinite-order point meets the pose's own independence predicate — no nonzero multiple
of `(−4, 6)` is torsion, by the torsion classification and infinite order. -/
theorem theAlgebraicRankAtFiveIsAtLeastOne : AlgebraicRankAtLeast 5 1 := by
  have hEq : FamilyFace.E ((5 : ℕ) : ℚ) = RankOne.E5 := by
    unfold FamilyFace.E RankOne.E5
    norm_num
  unfold AlgebraicRankAtLeast IndependentModTorsion IsTorsion
  rw [hEq]
  refine ⟨fun _ => RankOne.P, ?_⟩
  intro c htor i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  by_contra hc0
  obtain ⟨k, hk, hkP⟩ := htor
  have hsum : (∑ j : Fin 1, c j • (fun _ => RankOne.P) j) = c 0 • RankOne.P := by
    simp
  rw [hsum] at hkP
  have hcomb : (k * c 0 : ℤ) • RankOne.P = 0 := by
    rw [mul_smul]
    rw [natCast_zsmul]
    exact hkP
  have hkc : (k * c 0 : ℤ) ≠ 0 := by
    refine mul_ne_zero ?_ hc0
    exact_mod_cast hk.ne'
  have hnat : (k * c 0 : ℤ).natAbs • RankOne.P = 0 := by
    rcases Int.natAbs_eq (k * c 0 : ℤ) with h | h
    · rw [← natCast_zsmul, ← h]
      exact hcomb
    · rw [← natCast_zsmul, ← neg_neg ((↑(k * c 0).natAbs : ℤ)), ← h, neg_zsmul, hcomb,
        neg_zero]
  exact DistantWindings.thePointHasInfiniteOrderHolds (k * c 0 : ℤ).natAbs
    (Int.natAbs_pos.mpr hkc) hnat

/-- **The ledger clause closes at one, granted the classical central value**
`L(1) = Ω/8`: with the Tate ledger's Tamagawa product two and torsion order four, the
obstruction order is one — a positive square — and `(1·2)/4² = 1/8`. -/
theorem theLedgerClauseHoldsAtOneGivenTheCentralValue (W : LDatum 1)
    (hL : W.L 1 = (1 / 8 : ℂ) * (realPeriod 1 : ℂ)) :
    TheLedgerClause 1 W 2 4 := by
  intro _
  refine ⟨1, one_pos, ⟨1, rfl⟩, ?_⟩
  rw [hL]
  norm_num

/-- **THE ODD SIGN FORCES CENTRAL VANISHING**: any admissible analytic datum with sign
`−1` has `L(1) = 0` — the functional equation at its own center, so the analytic rank
is at least one whenever the sign is odd.  A theorem of the pose itself, before any
continuation is constructed: once the theta/Poisson deed returns the sign law
(`w = −1` exactly on the residue classes five and seven mod eight), the analytic side
of every odd-parity instance vanishes for free. -/
theorem theOddSignForcesCentralVanishing {n : ℕ} (W : LDatum n) (hw : W.sign = -1) :
    W.L 1 = 0 := by
  have h := W.functional_equation 1
  rw [hw] at h
  have h2 : (2 : ℂ) * completed W.conductor W.L 1 = 0 := by
    push_cast at h
    have hsub : (2 : ℂ) - 1 = 1 := by norm_num
    rw [hsub] at h
    linear_combination h
  have h1 : completed W.conductor W.L 1 = 0 := by
    have h20 : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h2).resolve_left h20
  unfold completed at h1
  rw [Complex.cpow_one, Complex.Gamma_one, mul_one] at h1
  rcases mul_eq_zero.mp h1 with hfac | hL
  · exfalso
    rcases div_eq_zero_iff.mp hfac with hnum | hden
    · have hs : Real.sqrt W.conductor = 0 := by exact_mod_cast hnum
      have hpos : (0 : ℝ) < Real.sqrt W.conductor :=
        Real.sqrt_pos.mpr (by exact_mod_cast W.conductor_pos)
      linarith
    · have hpi : (2 * Real.pi : ℝ) = 0 := by exact_mod_cast hden
      have := Real.pi_pos
      linarith
  · exact hL

end Soma.Holonics.Millennium.BirchSwinnertonDyer
