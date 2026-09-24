import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

/-!
# MinusFourth: Fermat's own descent — `x⁴ − y⁴ = z²` has no nontrivial solution

The sharpening deed of the BSD route.  The route's named-open proposition — *the four half-turns
are the whole population* of the congruent-number curve — is classically Fermat's theorem that
**one is not a congruent number**, and its proof is the first infinite descent in mathematics
(Fermat, c. 1640, the right-triangle theorem).  The carrying equation is the minus form
`x⁴ − y⁴ = z²`, which is **absent from mathlib** (measured 2026-08-21:
`grep -rn "4 - b ^ 4" Mathlib --include='*.lean'` → 0 hits; mathlib's `not_fermat_42` covers only
the plus form, and the minus form does not reduce to it — it descends within itself).  This file
climbs it.

The descent, in the dialect: a solution is a realizer; two Pythagorean classifications strip it
to a strictly smaller realizer of the same equation; the terrain (`ℕ` under `<`) is well-founded,
so the realizer population is empty.  **The descent preserves coprimality** — the classification
hands `gcd(m, n) = 1` down, and coprime squares force coprime roots — so the strong induction
carries coprimality as a hypothesis and the gcd-reduction happens once, in the outer wrapper.
Navigation's FOUND stroke with well-foundedness as its termination, exactly as the route records
posed it.

The skeleton: **the even lead fails** (the odd-square residue `1 mod 8`); **branch one**
(`b` odd) — one classification of `b⁴ + c² = (a²)²` returns `(ab)² = m⁴ − n⁴` with `|m| < |a|`;
**branch two** (`b` even) — two nested classifications and the four-fold coprime factorization
`(b/2)² = r·s·(r−s)·(r+s)` force `r = j², s = k², r−s = u², r+s = v²`, whence
`j⁴ − k⁴ = (uv)²` with `|j| < |a|`; the strong induction closes, and the wrapper removes the
sign and gcd normalizations.

Classical citations: Fermat's right-triangle theorem (c. 1640); the treatment follows the shape
of Mordell, *Diophantine Equations* (1969), transported onto mathlib's
`PythagoreanTriple.coprime_classification'` and `Int.sq_of_gcd_eq_one` exactly as mathlib's own
plus-form proof (`Mathlib.NumberTheory.FLT.Four`) uses them.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: this file proves the
integer equation empty; the bridge from the congruent-number curve's points to this equation, and
the discharge of the route's named-open proposition, are the companion file's deed, not this
one's.  Nothing here claims movement on the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.MinusFourth

/-! ## 1. Small arithmetic instruments -/

/-- An odd square is `1 mod 8` — the residue instrument of the parity step. -/
theorem theOddSquareIsOneModEight {b : ℤ} (hb : b % 2 = 1) : b ^ 2 % 8 = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, b = 2 * t + 1 := ⟨b / 2, by omega⟩
  obtain ⟨u, hu⟩ := Int.even_mul_succ_self t
  have h : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
  omega

/-- An even fourth power is divisible by eight. -/
theorem theEvenFourthPowerVanishesModEight {a : ℤ} (ha : a % 2 = 0) : a ^ 4 % 8 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 2 * t := ⟨a / 2, by omega⟩
  have h : (2 * t) ^ 4 = 8 * (2 * t ^ 4) := by ring
  omega

/-- An odd fourth power is `1 mod 8`. -/
theorem theOddFourthPowerIsOneModEight {b : ℤ} (hb : b % 2 = 1) : b ^ 4 % 8 = 1 := by
  have h1 := theOddSquareIsOneModEight hb
  obtain ⟨u, hu⟩ : ∃ u, b ^ 2 = 8 * u + 1 := ⟨b ^ 2 / 8, by omega⟩
  have h : b ^ 4 = (8 * u + 1) ^ 2 := by rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, hu]
  have h2 : (8 * u + 1) ^ 2 = 8 * (8 * u ^ 2 + 2 * u) + 1 := by ring
  omega

/-- The square-comparison face of the descent measure: a strictly smaller square means a
strictly smaller absolute value. -/
theorem theSmallerSquareHasTheSmallerAbsolute {m a : ℤ} (h : m ^ 2 < a ^ 2) :
    m.natAbs < a.natAbs := by
  have h1 : (m ^ 2).natAbs < (a ^ 2).natAbs :=
    Int.natAbs_lt_natAbs_of_nonneg_of_lt (sq_nonneg m) h
  rw [Int.natAbs_pow, Int.natAbs_pow] at h1
  exact lt_of_pow_lt_pow_left' 2 h1

/-! ## 2. The even lead fails -/

/-- **The even lead fails**: in a coprime solution the lead is odd — an even `a` would read
`0 − 1 ≡ 1 mod 8`. -/
theorem theEvenLeadFails {a b c : ℤ} (heq : a ^ 4 - b ^ 4 = c ^ 2)
    (hcop : IsCoprime a b) (ha : a % 2 = 0) : False := by
  have hb : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h | h
    · exact absurd (hcop.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero ha)
        (Int.dvd_of_emod_eq_zero h)) (by rw [Int.isUnit_iff]; norm_num)
    · exact h
  have hc : c % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one c with h | h
    · exfalso
      have hA : a ^ 4 % 8 = 0 := theEvenFourthPowerVanishesModEight ha
      have hB : b ^ 4 % 8 = 1 := theOddFourthPowerIsOneModEight hb
      obtain ⟨t, rfl⟩ : ∃ t, c = 2 * t := ⟨c / 2, by omega⟩
      have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      omega
    · exact h
  have hA := theEvenFourthPowerVanishesModEight ha
  have hB := theOddFourthPowerIsOneModEight hb
  have hC := theOddSquareIsOneModEight hc
  omega

/-! ## 3. The four-squares core -/

/-- Positivity resolves the sign a square extraction leaves open. -/
theorem thePositiveResolvesTheSquareSign {x i : ℤ} (hx : 0 < x)
    (h : x = i ^ 2 ∨ x = -i ^ 2) : x = i ^ 2 := by
  rcases h with h | h
  · exact h
  · exfalso; nlinarith [sq_nonneg i]

/-- **The four-fold coprime factorization forces four squares and returns the smaller
realizer**: for coprime `r > s > 0` of opposite parity with `r·s·(r−s)·(r+s)` a nonzero square,
the two bands and both factors are squares, and `j⁴ − k⁴ = (uv)²` returns with `j⁴ = r²` — the
strictly smaller realizer both parity sub-cases of the even branch hand to the induction. -/
theorem theFourSquaresCore {r s e : ℤ} (hr : 0 < r) (hs : 0 < s)
    (hcop : Int.gcd r s = 1)
    (hpar : r % 2 = 0 ∧ s % 2 = 1 ∨ r % 2 = 1 ∧ s % 2 = 0)
    (heq : r * s * ((r - s) * (r + s)) = e ^ 2) :
    ∃ j k w : ℤ, j ^ 4 - k ^ 4 = w ^ 2 ∧ j ≠ 0 ∧ k ≠ 0 ∧ w ≠ 0 ∧
      Int.gcd j k = 1 ∧ j ^ 4 = r ^ 2 := by
  have hC : IsCoprime r s := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hrs : r ≠ s := by rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hgt : s < r := by
    by_contra hle
    push_neg at hle
    have hlt : r < s := lt_of_le_of_ne hle hrs
    have hband : (r - s) * (r + s) < 0 :=
      mul_neg_of_neg_of_pos (by omega) (by omega)
    have hneg : r * s * ((r - s) * (r + s)) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hr hs) hband
    rw [heq] at hneg
    exact absurd hneg (not_lt.mpr (sq_nonneg e))
  -- the two factors are coprime to both bands
  have hC_rm : IsCoprime r (r - s) := by
    have h := hC.neg_right.add_mul_left_right 1
    rw [mul_one] at h
    rwa [show -s + r = r - s by ring] at h
  have hC_rp : IsCoprime r (r + s) := by
    have h := hC.add_mul_left_right 1
    rw [mul_one] at h
    rwa [show s + r = r + s by ring] at h
  have hC_sm : IsCoprime s (r - s) := by
    have h := hC.symm.add_mul_left_right (-1)
    rwa [show r + s * -1 = r - s by ring] at h
  have hC_sp : IsCoprime s (r + s) := by
    have h := hC.symm.add_mul_left_right 1
    rw [mul_one] at h
    rwa [show r + s = r + s by ring] at h
  -- the two bands are coprime to each other: both odd, and any common divisor divides two
  have hodd_m : (r - s) % 2 = 1 := by rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hg_band : Int.gcd (r - s) (r + s) = 1 := by
    have hd1 : (↑(Int.gcd (r - s) (r + s)) : ℤ) ∣ r - s := Int.gcd_dvd_left _ _
    have hd2 : (↑(Int.gcd (r - s) (r + s)) : ℤ) ∣ r + s := Int.gcd_dvd_right _ _
    have hd2r : (↑(Int.gcd (r - s) (r + s)) : ℤ) ∣ 2 * r := by
      have h := dvd_add hd1 hd2
      rwa [show r - s + (r + s) = 2 * r by ring] at h
    have hd2s : (↑(Int.gcd (r - s) (r + s)) : ℤ) ∣ 2 * s := by
      have h := dvd_sub hd2 hd1
      rwa [show r + s - (r - s) = 2 * s by ring] at h
    have hdg : Int.gcd (r - s) (r + s) ∣ Int.gcd (2 * r) (2 * s) :=
      Int.dvd_gcd hd2r hd2s
    rw [Int.gcd_mul_left, hcop] at hdg
    norm_num at hdg
    rcases (Nat.dvd_prime Nat.prime_two).mp hdg with h | h
    · exact h
    · exfalso
      have h2 : (2 : ℤ) ∣ r - s := by
        have := Int.gcd_dvd_left (a := r - s) (b := r + s)
        rw [h] at this
        exact_mod_cast this
      omega
  have hC_band : IsCoprime (r - s) (r + s) := Int.isCoprime_iff_gcd_eq_one.mpr hg_band
  -- extract the two squares at the top split
  have hC_top : IsCoprime (r * s) ((r - s) * (r + s)) :=
    ((hC_rm.mul_right hC_rp).mul_left (hC_sm.mul_right hC_sp))
  obtain ⟨e1, he1⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hC_top) heq
  have hrs_pos : 0 < r * s := mul_pos hr hs
  have hrs_sq : r * s = e1 ^ 2 := thePositiveResolvesTheSquareSign hrs_pos he1
  have heq' : (r - s) * (r + s) * (r * s) = e ^ 2 := by linear_combination heq
  obtain ⟨f, hf⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp hC_top.symm) heq'
  have hband_pos : 0 < (r - s) * (r + s) := mul_pos (by omega) (by omega)
  have hband_sq : (r - s) * (r + s) = f ^ 2 := thePositiveResolvesTheSquareSign hband_pos hf
  -- split the factor square
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one hcop hrs_sq
  have hjr : r = j ^ 2 := thePositiveResolvesTheSquareSign hr hj
  have hsr_sq : s * r = e1 ^ 2 := by linear_combination hrs_sq
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one (by rwa [Int.gcd_comm] at hcop) hsr_sq
  have hks : s = k ^ 2 := thePositiveResolvesTheSquareSign hs hk
  -- split the band square
  obtain ⟨u, hu⟩ := Int.sq_of_gcd_eq_one hg_band hband_sq
  have hum : r - s = u ^ 2 := thePositiveResolvesTheSquareSign (by omega) hu
  have hband_sq' : (r + s) * (r - s) = f ^ 2 := by linear_combination hband_sq
  obtain ⟨v, hv⟩ := Int.sq_of_gcd_eq_one (by rwa [Int.gcd_comm] at hg_band) hband_sq'
  have hvp : r + s = v ^ 2 := thePositiveResolvesTheSquareSign (by omega) hv
  -- assemble
  refine ⟨j, k, u * v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show j ^ 4 = (j ^ 2) ^ 2 by ring, show k ^ 4 = (k ^ 2) ^ 2 by ring, ← hjr, ← hks]
    rw [show r ^ 2 - s ^ 2 = (r - s) * (r + s) by ring, hum, hvp]
    ring
  · intro h0; rw [h0] at hjr; simp at hjr; omega
  · intro h0; rw [h0] at hks; simp at hks; omega
  · intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [h] at hum; simp at hum; omega
    · rw [h] at hvp; simp at hvp; omega
  · have hCjk2 : IsCoprime (j ^ 2) (k ^ 2) := by rwa [← hjr, ← hks]
    have hCj : IsCoprime j (k ^ 2) :=
      IsCoprime.of_isCoprime_of_dvd_left hCjk2 (dvd_pow_self j (by norm_num))
    have hCjk : IsCoprime j k :=
      IsCoprime.of_isCoprime_of_dvd_right hCj (dvd_pow_self k (by norm_num))
    exact Int.isCoprime_iff_gcd_eq_one.mp hCjk
  · rw [hjr]; ring

/-! ## 4. The two branches -/

/-- The receiver-side coprimality the classifications need: with `a` coprime to `b` and the
equation standing, `b²` is coprime to `c`. -/
theorem theFlankIsCoprimeToTheHypotenuse {a b c : ℤ} (hcop : IsCoprime a b)
    (heq : a ^ 4 - b ^ 4 = c ^ 2) : IsCoprime (b ^ 2) c := by
  have h1 : IsCoprime (b ^ 2) (a ^ 4) := (hcop.symm.pow : IsCoprime (b ^ 2) (a ^ 4))
  have h2 : IsCoprime (b ^ 2) (a ^ 4 + b ^ 2 * (-(b ^ 2))) := h1.add_mul_left_right (-(b ^ 2))
  have h3 : IsCoprime (b ^ 2) (c ^ 2) := by
    rwa [show a ^ 4 + b ^ 2 * (-(b ^ 2)) = a ^ 4 - b ^ 4 by ring, heq] at h2
  exact IsCoprime.of_isCoprime_of_dvd_right h3 (dvd_pow_self c (by norm_num))

/-- **Branch one** (`b` odd): a single Pythagorean classification of `b⁴ + c² = (a²)²` returns
the immediate smaller realizer `m⁴ − n⁴ = (ab)²`. -/
theorem theOddBranchDescends {a b c : ℤ} (ha : 0 < a) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcop : IsCoprime a b) (hbodd : b % 2 = 1)
    (heq : a ^ 4 - b ^ 4 = c ^ 2) :
    ∃ a' b' c' : ℤ, a' ^ 4 - b' ^ 4 = c' ^ 2 ∧ 0 < a' ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
      IsCoprime a' b' ∧ a'.natAbs < a.natAbs := by
  have ht : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
    delta PythagoreanTriple
    linear_combination -heq
  have hgcd : Int.gcd (b ^ 2) c = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (theFlankIsCoprimeToTheHypotenuse hcop heq)
  have hb2odd : b ^ 2 % 2 = 1 := by
    obtain ⟨t, rfl⟩ : ∃ t, b = 2 * t + 1 := ⟨b / 2, by omega⟩
    have h : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring
    omega
  obtain ⟨m, n, ht1, ht2, ht3, ht4, _ht5, ht6⟩ :=
    ht.coprime_classification' hgcd hb2odd (by positivity)
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ht2
    exact hc ht2
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h : b ^ 2 = -n ^ 2 := by linarith [ht1]
    nlinarith [sq_nonneg b, sq_nonneg n, sq_pos_of_ne_zero hb]
  have hmpos : 0 < m := lt_of_le_of_ne ht6 (Ne.symm hm0)
  refine ⟨m, n, a * b, ?_, hmpos, hn0, mul_ne_zero (ne_of_gt ha) hb,
    Int.isCoprime_iff_gcd_eq_one.mpr ht4, ?_⟩
  · linear_combination (-(m ^ 2 + n ^ 2)) * ht1 - b ^ 2 * ht3
  · apply theSmallerSquareHasTheSmallerAbsolute
    nlinarith [sq_pos_of_ne_zero hn0, ht3]

/-- **Branch two** (`b` even): two nested classifications and the four-squares core return the
smaller realizer with its fourth power strictly below `a`. -/
theorem theEvenBranchDescends {a b c : ℤ} (ha : 0 < a) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcop : IsCoprime a b) (haodd : a % 2 = 1) (hbev : b % 2 = 0)
    (heq : a ^ 4 - b ^ 4 = c ^ 2) :
    ∃ j k w : ℤ, j ^ 4 - k ^ 4 = w ^ 2 ∧ j ≠ 0 ∧ k ≠ 0 ∧ w ≠ 0 ∧
      Int.gcd j k = 1 ∧ j ^ 4 < a := by
  -- the hypotenuse-side flank is odd here
  have hcodd : c % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one c with h | h
    · exfalso
      have hA : a ^ 4 % 8 = 1 := theOddFourthPowerIsOneModEight haodd
      have hB : b ^ 4 % 8 = 0 := theEvenFourthPowerVanishesModEight hbev
      obtain ⟨t, rfl⟩ : ∃ t, c = 2 * t := ⟨c / 2, by omega⟩
      have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      omega
    · exact h
  have ht : PythagoreanTriple c (b ^ 2) (a ^ 2) := by
    delta PythagoreanTriple
    linear_combination -heq
  have hgcd : Int.gcd c (b ^ 2) = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.mp (theFlankIsCoprimeToTheHypotenuse hcop heq)
  obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
    ht.coprime_classification' hgcd hcodd (by positivity)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at ht2
    exact hb ht2
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ht2
    exact hb ht2
  have hmpos : 0 < m := lt_of_le_of_ne ht6 (Ne.symm hm0)
  -- the second triple
  have htt : PythagoreanTriple m n a := by
    delta PythagoreanTriple
    linear_combination -ht3
  obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    simp at hb
  rcases ht5 with ⟨hme, hno⟩ | ⟨hmo, hne⟩
  · -- `n` odd: classify `(n, m, a)`
    obtain ⟨r, s, hr1, hr2, hr3, hr4, hr5, hr6⟩ :=
      (htt.symm).coprime_classification'
        (by rwa [Int.gcd_comm] at ht4) hno ha
    -- the four-band square
    have hsq4 : (4 : ℤ) * b' ^ 2 = 4 * (r * s * ((r - s) * (r + s))) := by
      have h := ht2
      rw [hr1, hr2] at h
      linear_combination h
    have hb'sq : b' ^ 2 = r * s * ((r - s) * (r + s)) := by linarith
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr2
      exact hm0 (by omega)
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hr2
      exact hm0 (by omega)
    have hrpos : 0 < r := lt_of_le_of_ne hr6 (Ne.symm hr0)
    rcases lt_or_gt_of_ne hs0 with hsneg | hspos
    · -- `s < 0`: the roles reflect
      have hb'sq' : (-s) * r * (((-s) - r) * ((-s) + r)) = b' ^ 2 := by
        linear_combination -hb'sq
      obtain ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, hj4⟩ :=
        theFourSquaresCore (by omega) hrpos
          (by rw [Int.neg_gcd, Int.gcd_comm]; exact hr4)
          (by rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · right; omega
              · left; omega)
          hb'sq'
      refine ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, ?_⟩
      have hs2 : j ^ 4 = s ^ 2 := by rw [hj4]; ring
      linarith [hs2, hr3, sq_pos_of_ne_zero hr0]
    · -- `s > 0`
      obtain ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, hj4⟩ :=
        theFourSquaresCore hrpos hspos hr4
          (by rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left; exact ⟨h1, h2⟩
              · right; exact ⟨h1, h2⟩)
          hb'sq.symm
      refine ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, ?_⟩
      linarith [hj4, hr3, sq_pos_of_ne_zero hs0]
  · -- `m` odd: classify `(m, n, a)`
    obtain ⟨r, s, hr1, hr2, hr3, hr4, hr5, hr6⟩ :=
      htt.coprime_classification' ht4 hmo ha
    have hsq4 : (4 : ℤ) * b' ^ 2 = 4 * (r * s * ((r - s) * (r + s))) := by
      have h := ht2
      rw [hr1, hr2] at h
      linear_combination h
    have hb'sq : b' ^ 2 = r * s * ((r - s) * (r + s)) := by linarith
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr1
      have : m = -s ^ 2 := by linarith
      nlinarith [sq_nonneg s]
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hr2
      exact hn0 hr2
    have hrpos : 0 < r := lt_of_le_of_ne hr6 (Ne.symm hr0)
    rcases lt_or_gt_of_ne hs0 with hsneg | hspos
    · have hb'sq' : (-s) * r * (((-s) - r) * ((-s) + r)) = b' ^ 2 := by
        linear_combination -hb'sq
      obtain ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, hj4⟩ :=
        theFourSquaresCore (by omega) hrpos
          (by rw [Int.neg_gcd, Int.gcd_comm]; exact hr4)
          (by rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · right; omega
              · left; omega)
          hb'sq'
      refine ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, ?_⟩
      have hs2 : j ^ 4 = s ^ 2 := by rw [hj4]; ring
      linarith [hs2, hr3, sq_pos_of_ne_zero hr0]
    · obtain ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, hj4⟩ :=
        theFourSquaresCore hrpos hspos hr4
          (by rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left; exact ⟨h1, h2⟩
              · right; exact ⟨h1, h2⟩)
          hb'sq.symm
      refine ⟨j, k, w, hjkw, hj0, hk0, hw0, hg, ?_⟩
      linarith [hj4, hr3, sq_pos_of_ne_zero hs0]

/-! ## 5. The descent closes, and the wrapper removes the normalizations -/

/-- The absolute value keeps the gcd — the sign wrap the even branch's recursion needs. -/
theorem theAbsoluteKeepsTheGcd (j k : ℤ) : Int.gcd |j| k = Int.gcd j k := by
  unfold Int.gcd
  rw [Int.natAbs_abs]

/-- **The descent closes on coprime solutions**: strong induction on the lead's absolute value,
each branch handing the induction a strictly smaller coprime realizer. -/
theorem theDescentClosesOnCoprimeSolutions :
    ∀ N : ℕ, ∀ a b c : ℤ, a.natAbs = N → 0 < a → b ≠ 0 → c ≠ 0 → IsCoprime a b →
      a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b c hN ha hb hc hcop heq
    have haodd : a % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one a with h | h
      · exact (theEvenLeadFails heq hcop h).elim
      · exact h
    rcases Int.emod_two_eq_zero_or_one b with hbev | hbodd
    · -- the even branch returns `(j, k, w)` with `j⁴ < a`; wrap the sign of `j`
      obtain ⟨j, k, w, heq', hj0, hk0, hw0, hg, hlt⟩ :=
        theEvenBranchDescends ha hb hc hcop haodd hbev heq
      have habs : |j| ^ 4 = j ^ 4 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by positivity)
      have hja : (|j|).natAbs < a.natAbs := by
        have h1 : (1 : ℤ) ≤ |j| := abs_pos.mpr hj0
        have h2 : |j| ≤ |j| ^ 4 := le_self_pow₀ h1 (by norm_num)
        have h3 : |j| < a := by rw [habs] at h2; linarith
        have h4 : (0 : ℤ) ≤ |j| := abs_nonneg j
        omega
      exact ih (|j|).natAbs (hN ▸ hja) (|j|) k w rfl (abs_pos.mpr hj0) hk0 hw0
        (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [theAbsoluteKeepsTheGcd]; exact hg))
        (by rw [habs]; exact heq')
    · -- the odd branch returns the smaller solution directly
      obtain ⟨a', b', c', heq', ha', hb', hc', hcop', hlt⟩ :=
        theOddBranchDescends ha hb hc hcop hbodd heq
      exact ih a'.natAbs (hN ▸ hlt) a' b' c' rfl ha' hb' hc' hcop' heq'

/-- **Fermat's theorem, the minus form**: `a⁴ − b⁴ = c²` has no integer solution with `b` and
`c` nonzero.  The first infinite descent in mathematics, kernel-checked; equivalently, no
rational right triangle has area one, and one is not a congruent number — the bridge to the
curve is the companion file's deed. -/
theorem theMinusFourthHasNoSolution {a b c : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro heq
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : (0 : ℤ) < b ^ 4 := by positivity
    have h2 : (0 : ℤ) ≤ c ^ 2 := sq_nonneg c
    norm_num at heq
    linarith [heq]
  -- the gcd normalization
  set d : ℤ := (Int.gcd a b : ℤ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]
    intro h
    exact ha0 (Int.gcd_eq_zero_iff.mp (by exact_mod_cast h)).1
  have hda : d ∣ a := by rw [hd]; exact Int.gcd_dvd_left a b
  have hdb : d ∣ b := by rw [hd]; exact Int.gcd_dvd_right a b
  obtain ⟨a1, ha1⟩ := hda
  obtain ⟨b1, hb1⟩ := hdb
  have ha10 : a1 ≠ 0 := by rintro rfl; rw [mul_zero] at ha1; exact ha0 ha1
  have hb10 : b1 ≠ 0 := by rintro rfl; rw [mul_zero] at hb1; exact hb hb1
  have hgpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b ha0
  have hcop1 : Int.gcd a1 b1 = 1 := by
    have h := Int.gcd_div_gcd_div_gcd hgpos
    rwa [show a / ↑(Int.gcd a b) = a1 by rw [← hd, ha1, Int.mul_ediv_cancel_left a1 hd0],
      show b / ↑(Int.gcd a b) = b1 by rw [← hd, hb1, Int.mul_ediv_cancel_left b1 hd0]] at h
  -- the square factor of `c`
  have hd4c : (d ^ 2) ^ 2 ∣ c ^ 2 := by
    refine ⟨a1 ^ 4 - b1 ^ 4, ?_⟩
    rw [← heq, ha1, hb1]
    ring
  have hd2c : d ^ 2 ∣ c := by
    have h1 : ((d ^ 2) ^ 2).natAbs ∣ (c ^ 2).natAbs := Int.natAbs_dvd_natAbs.mpr hd4c
    simp only [Int.natAbs_pow] at h1
    have h2 : d.natAbs ^ 2 ∣ c.natAbs :=
      (Nat.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
    have h3 : (d ^ 2).natAbs ∣ c.natAbs := by rwa [Int.natAbs_pow]
    exact Int.natAbs_dvd_natAbs.mp h3
  obtain ⟨c1, hc1⟩ := hd2c
  have hc10 : c1 ≠ 0 := by rintro rfl; rw [mul_zero] at hc1; exact hc hc1
  have heq1 : a1 ^ 4 - b1 ^ 4 = c1 ^ 2 := by
    have h := heq
    rw [ha1, hb1, hc1] at h
    have h2 : d ^ 4 * (a1 ^ 4 - b1 ^ 4) = d ^ 4 * c1 ^ 2 := by linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 4 hd0) h2
  -- the sign normalization, then the descent
  have habs : |a1| ^ 4 = a1 ^ 4 := by
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  exact theDescentClosesOnCoprimeSolutions (|a1|).natAbs (|a1|) b1 c1 rfl
    (abs_pos.mpr ha10) hb10 hc10
    (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [theAbsoluteKeepsTheGcd]; exact hcop1))
    (by rw [habs]; exact heq1)

end Soma.Holonics.Millennium.MinusFourth
