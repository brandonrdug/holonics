import ElementaryHolonics.Millennium.MinusFourth
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Congruum: the half-turn primes are never congruent — an infinite twist family in one descent

The second frame opens.  A number `n` is congruent exactly when three rational squares stand
in arithmetic progression with common difference `n` — the classical *congruum* — because
`((a ± b)/2)² = (c/2)² ± n` converts the right triangle to the progression and back.  This
file proves, for **every** prime `p ≡ 3 (mod 8)` at once: **no congruum `p·e²` exists**, so
no such prime is a congruent number (Genocchi's theorem, 1855) — infinitely many quadratic
twists `y² = x³ − p²x` of the congruent-number family with their realized triangles refused
by a single kernel-checked infinite descent.

The descent (`theCongruumNeverForms`), in the route's vocabulary: an odd scale dies at the
frame of eight, where `3·(odd)²` cannot separate two squares twice
(`theOddScaleDiesAtEight`, a sixteen-line kernel enumeration).  An even scale walks the same
staircase as Fermat's descent: the progression folds to a primitive Pythagorean triple
(`r² + s² = u₁²` with `rs = 2pe′²`), the classification hands down `m, n`, and the four
pairwise-coprime factors satisfy `m·n·(m−n)·(m+n) = p·e′²`.  The prime sits in exactly one
factor, and the frame at `p` refuses three of the four placements — the quarter-turn is
invisible (`p ≡ 3 mod 4`: sums of two squares descend, `theSumOfSquaresDescendsToTheFrame`)
and two is invisible (`p ≡ 3 mod 8`: doubled squares descend,
`theDoubledSquareDescendsToTheFrame`) — while the fourth placement (`p ∣ n`) reproduces the
progression at scale `b` with `4·|b| ≤ |e|`: a strictly descending chain on well-founded
terrain.  **The same two invisibility facts that made the reflection census vanish at the
blind frames here refuse three of four descent branches: the analytic side's phase law and
the realized side's descent law are one mechanism.**

Summits: `theCongruumNeverForms` (the descent), `theHalfTurnPrimesAreNotCongruent`
(no rational right triangle has area `p`, for every prime `p ≡ 3 mod 8`), and the instances
at three, eleven, and nineteen.  Every `theorem` is discharged and none depends on
`sorryAx`.  **Boundary**: primes `p ≡ 5 (mod 8)` (also classically non-congruent) need the
minus-two character and a different branch pattern, not carried here; nothing about ranks,
Selmer structure, or the Birch–Swinnerton-Dyer conjecture is claimed — this is the realized
side of infinitely many twists, closed.
-/

set_option maxHeartbeats 1600000

namespace Soma.Holonics.Millennium.Congruum

variable {p : ℕ}

/-! ## 1. The two invisibility facts and their integer faces -/

/-- At a half-turn-of-the-half-turn prime, the quarter-turn is invisible. -/
theorem theQuarterTurnIsInvisibleAtEight [Fact p.Prime] (h8 : p % 8 = 3) :
    ¬ IsSquare (-1 : ZMod p) := by
  rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
  omega

/-- At such a prime, two is invisible as well. -/
theorem theTwoIsInvisible [Fact p.Prime] (h8 : p % 8 = 3) : ¬ IsSquare (2 : ZMod p) := by
  rw [ZMod.exists_sq_eq_two_iff (by omega : p ≠ 2)]
  omega

/-- A vanishing sum of two squares in the frame forces both to vanish. -/
theorem theSumOfSquaresForcesBothZero [Fact p.Prime] (h8 : p % 8 = 3) {c d : ZMod p}
    (h : c ^ 2 + d ^ 2 = 0) : c = 0 ∧ d = 0 := by
  by_cases hd : d = 0
  · subst hd
    refine ⟨?_, rfl⟩
    have hc : c ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hc
  · exfalso
    apply theQuarterTurnIsInvisibleAtEight h8
    refine ⟨c / d, ?_⟩
    field_simp
    linear_combination -h

/-- **The integer face**: `p ∣ c² + d²` forces `p ∣ c` and `p ∣ d`. -/
theorem theSumOfSquaresDescendsToTheFrame [Fact p.Prime] (h8 : p % 8 = 3) {c d : ℤ}
    (h : (p : ℤ) ∣ c ^ 2 + d ^ 2) : (p : ℤ) ∣ c ∧ (p : ℤ) ∣ d := by
  have hcast : (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 = 0 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at h0
    linear_combination h0
  obtain ⟨hc, hd⟩ := theSumOfSquaresForcesBothZero h8 hcast
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc,
    (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd⟩

/-- **The doubled face**: `p ∣ d² − 2a²` forces `p ∣ a` and `p ∣ d`. -/
theorem theDoubledSquareDescendsToTheFrame [Fact p.Prime] (h8 : p % 8 = 3) {a d : ℤ}
    (h : (p : ℤ) ∣ d ^ 2 - 2 * a ^ 2) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ d := by
  have hcast : (d : ZMod p) ^ 2 - 2 * (a : ZMod p) ^ 2 = 0 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at h0
    linear_combination h0
  by_cases ha : (a : ZMod p) = 0
  · have hd : (d : ZMod p) = 0 := by
      have hd2 : (d : ZMod p) ^ 2 = 0 := by
        rw [ha] at hcast
        linear_combination hcast
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hd2
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
      (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hd⟩
  · exfalso
    apply theTwoIsInvisible h8
    refine ⟨d / a, ?_⟩
    field_simp
    linear_combination -hcast

/-- A prime is never a rational square: `u² = p·e²` with `e ≠ 0` is refused. -/
theorem thePrimeIsNotARationalSquare (hp : p.Prime) {u e : ℤ} (he : e ≠ 0)
    (h : u ^ 2 = (p : ℤ) * e ^ 2) : False := by
  have he' : (e : ℚ) ≠ 0 := Int.cast_ne_zero.mpr he
  have hq : ((u : ℚ) / (e : ℚ)) ^ 2 = (p : ℚ) := by
    field_simp
    exact_mod_cast (by linear_combination h : u ^ 2 = e ^ 2 * ((p : ℕ) : ℤ))
  have hsq : IsSquare ((p : ℕ) : ℚ) := ⟨(u : ℚ) / e, by rw [← hq]; ring⟩
  rw [Rat.isSquare_natCast_iff] at hsq
  exact hp.not_isSquare hsq

/-! ## 2. The frame of eight refuses the odd scale -/

/-- Over the frame of eight, `3·(odd)²` cannot separate squares twice in progression. -/
private lemma theOddScaleDiesAtEight :
    ∀ u₁ u₂ u₃ f : ZMod 8, ¬ (u₁ ^ 2 - u₂ ^ 2 = 3 * (2 * f + 1) ^ 2 ∧
      u₃ ^ 2 - u₁ ^ 2 = 3 * (2 * f + 1) ^ 2) := by
  decide

private lemma pcast8 (h8 : p % 8 = 3) : ((p : ℕ) : ZMod 8) = 3 := by
  rw [← ZMod.natCast_mod, h8]
  rfl

/-! ## 3. Small instruments -/

private lemma gcd_eq_one_of_no_common_prime {a b : ℤ}
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ a → (q : ℤ) ∣ b → False) : Int.gcd a b = 1 := by
  by_contra hg
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
  exact h q hq
    (dvd_trans (Int.natCast_dvd_natCast.mpr hqd) (Int.gcd_dvd_left _ _))
    (dvd_trans (Int.natCast_dvd_natCast.mpr hqd) (Int.gcd_dvd_right _ _))

private lemma unit_prime_refuted {q : ℕ} (hq : q.Prime) (h : IsUnit ((q : ℕ) : ℤ)) :
    False := by
  rw [Int.isUnit_iff] at h
  have h2 := hq.two_le
  rcases h with h | h <;> omega

/-- Four pairwise-coprime positive factors of a square are each squares. -/
private lemma four_coprime_split {A B C D w : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAB : IsCoprime A B) (hAC : IsCoprime A C) (hAD : IsCoprime A D)
    (hBC : IsCoprime B C) (hBD : IsCoprime B D) (hCD : IsCoprime C D)
    (h : A * B * C * D = w ^ 2) :
    ∃ a b c d : ℤ, A = a ^ 2 ∧ B = b ^ 2 ∧ C = c ^ 2 ∧ D = d ^ 2 ∧
      w ^ 2 = (a * b * c * d) ^ 2 := by
  have hCtop : IsCoprime (A * B) (C * D) := (hAC.mul_right hAD).mul_left (hBC.mul_right hBD)
  have htop : (A * B) * (C * D) = w ^ 2 := by linear_combination h
  obtain ⟨α, hα⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hCtop) htop
  have hαsq : A * B = α ^ 2 :=
    MinusFourth.thePositiveResolvesTheSquareSign (mul_pos hA hB) hα
  have htop' : (C * D) * (A * B) = w ^ 2 := by linear_combination h
  obtain ⟨β, hβ⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hCtop.symm) htop'
  have hβsq : C * D = β ^ 2 :=
    MinusFourth.thePositiveResolvesTheSquareSign (mul_pos hC hD) hβ
  obtain ⟨a, ha⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hAB) hαsq
  have hasq : A = a ^ 2 := MinusFourth.thePositiveResolvesTheSquareSign hA ha
  have hαsq' : B * A = α ^ 2 := by linear_combination hαsq
  obtain ⟨b, hb⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hAB.symm) hαsq'
  have hbsq : B = b ^ 2 := MinusFourth.thePositiveResolvesTheSquareSign hB hb
  obtain ⟨c, hc⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hCD) hβsq
  have hcsq : C = c ^ 2 := MinusFourth.thePositiveResolvesTheSquareSign hC hc
  have hβsq' : D * C = β ^ 2 := by linear_combination hβsq
  obtain ⟨d, hd⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hCD.symm) hβsq'
  have hdsq : D = d ^ 2 := MinusFourth.thePositiveResolvesTheSquareSign hD hd
  exact ⟨a, b, c, d, hasq, hbsq, hcsq, hdsq, by
    rw [← h, hasq, hbsq, hcsq, hdsq]; ring⟩

private lemma natAbs_ge_two_of_sq_ge_two {a : ℤ} {m : ℤ} (h : a ^ 2 = m) (hm : 2 ≤ m) :
    2 ≤ a.natAbs := by
  by_contra hcon
  push_neg at hcon
  interval_cases h1 : a.natAbs
  · have : a = 0 := Int.natAbs_eq_zero.mp h1
    subst this
    simp at h
    omega
  · have : a = 1 ∨ a = -1 := by
      rcases Int.natAbs_eq a with h2 | h2 <;> rw [h1] at h2 <;> omega
    rcases this with rfl | rfl <;> simp at h <;> omega

/-! ## 4. The four-factor core: three refusals and one descent -/

private lemma theFourFactorsRefuseOrDescend [Fact p.Prime] (hp : p.Prime)
    (h8 : p % 8 = 3) {m n e' : ℤ} {E : ℕ}
    (hmn : Int.gcd m n = 1) (hn : 0 < n) (hnm : n < m)
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
    (he' : e' ≠ 0) (hE : 2 * e'.natAbs = E)
    (hprod : m * n * (m - n) * (m + n) = (p : ℤ) * e' ^ 2)
    (ihE : ∀ b : ℤ, b ≠ 0 → 4 * b.natAbs ≤ E →
      ∀ x y z : ℤ, x ^ 2 - y ^ 2 = (p : ℤ) * b ^ 2 →
        z ^ 2 - x ^ 2 = (p : ℤ) * b ^ 2 → False) :
    False := by
  have hm : 0 < m := lt_trans hn hnm
  have hm2 : 2 ≤ m := by omega
  have hsub : 0 < m - n := by omega
  have hadd : 0 < m + n := by omega
  have hpodd : p ≠ 2 := by omega
  have hpprime : Prime ((p : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hp)
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by
    have := hp.two_le
    omega
  -- the coprimality kit
  have hCmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hCm_sub : IsCoprime m (m - n) := by
    have h := hCmn.neg_right.add_mul_left_right 1
    have heq : -n + m * 1 = m - n := by ring
    rwa [heq] at h
  have hCm_add : IsCoprime m (m + n) := by
    have h := hCmn.add_mul_left_right 1
    have heq : n + m * 1 = m + n := by ring
    rwa [heq] at h
  have hCn_sub : IsCoprime n (m - n) := by
    have h := hCmn.symm.add_mul_left_right (-1)
    have heq : m + n * (-1) = m - n := by ring
    rwa [heq] at h
  have hCn_add : IsCoprime n (m + n) := by
    have h := hCmn.symm.add_mul_left_right 1
    have heq : m + n * 1 = m + n := by ring
    rwa [heq] at h
  have hsubodd : (m - n) % 2 = 1 := by omega
  have haddodd : (m + n) % 2 = 1 := by omega
  have hCband : IsCoprime (m - n) (m + n) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    apply gcd_eq_one_of_no_common_prime
    intro q hq hq1 hq2
    have hqZ : Prime ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq)
    have hq2m : ((q : ℕ) : ℤ) ∣ 2 * m := by
      have := dvd_add hq1 hq2
      have heq : m - n + (m + n) = 2 * m := by ring
      rwa [heq] at this
    have hq2n : ((q : ℕ) : ℤ) ∣ 2 * n := by
      have := dvd_sub hq2 hq1
      have heq : m + n - (m - n) = 2 * n := by ring
      rwa [heq] at this
    have hqne2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hq1
      omega
    have hqm : ((q : ℕ) : ℤ) ∣ m := by
      rcases hqZ.dvd_mul.mp hq2m with h2 | hqm
      · exfalso
        have : (q : ℕ) ∣ 2 := by exact_mod_cast h2
        have := Nat.le_of_dvd (by norm_num) this
        have := hq.two_le
        omega
      · exact hqm
    have hqn : ((q : ℕ) : ℤ) ∣ n := by
      rcases hqZ.dvd_mul.mp hq2n with h2 | hqn
      · exfalso
        have : (q : ℕ) ∣ 2 := by exact_mod_cast h2
        have := Nat.le_of_dvd (by norm_num) this
        have := hq.two_le
        omega
      · exact hqn
    exact unit_prime_refuted hq (hCmn.isUnit_of_dvd' hqm hqn)
  -- the prime sits in exactly one factor
  have hpd : ((p : ℕ) : ℤ) ∣ m * n * (m - n) * (m + n) := ⟨e' ^ 2, hprod⟩
  have hp_cases : ((p : ℕ) : ℤ) ∣ m ∨ ((p : ℕ) : ℤ) ∣ n ∨
      ((p : ℕ) : ℤ) ∣ (m - n) ∨ ((p : ℕ) : ℤ) ∣ (m + n) := by
    rcases hpprime.dvd_mul.mp hpd with h1 | h1
    · rcases hpprime.dvd_mul.mp h1 with h2 | h2
      · rcases hpprime.dvd_mul.mp h2 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h1))
  -- the common endgame for the three refusals: a shared prime divisor of m and n
  have hkill : ((p : ℕ) : ℤ) ∣ m → ((p : ℕ) : ℤ) ∣ n → False := fun h1 h2 =>
    unit_prime_refuted hp (hCmn.isUnit_of_dvd' h1 h2)
  have hppos : (0 : ℤ) < ((p : ℕ) : ℤ) := by exact_mod_cast hp.pos
  rcases hp_cases with hpm | hpn | hpsub | hpadd
  · -- p ∣ m : the sum of two squares refuses this placement
    obtain ⟨t, rfl⟩ := hpm
    have ht : 0 < t := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hm, mul_nonneg hppos.le (neg_nonneg.mpr hcon)]
    have htm : t ∣ ((p : ℕ) : ℤ) * t := ⟨(p : ℕ), by ring⟩
    have hCt_n : IsCoprime t n := hCmn.of_isCoprime_of_dvd_left htm
    have hCt_sub : IsCoprime t (((p : ℕ) : ℤ) * t - n) := hCm_sub.of_isCoprime_of_dvd_left htm
    have hCt_add : IsCoprime t (((p : ℕ) : ℤ) * t + n) := hCm_add.of_isCoprime_of_dvd_left htm
    have hcan : t * n * (((p : ℕ) : ℤ) * t - n) * (((p : ℕ) : ℤ) * t + n) = e' ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hprod
    obtain ⟨a, b, c, d, hasq, hbsq, hcsq, hdsq, hwsq⟩ :=
      four_coprime_split ht hn hsub hadd hCt_n hCt_sub hCt_add hCn_sub hCn_add hCband hcan
    have hsumcd : c ^ 2 + d ^ 2 = ((p : ℕ) : ℤ) * (2 * t) := by
      linear_combination -hcsq - hdsq
    obtain ⟨hpc, hpd2⟩ := theSumOfSquaresDescendsToTheFrame h8 ⟨2 * t, hsumcd⟩
    have hpsub' : ((p : ℕ) : ℤ) ∣ ((p : ℕ) : ℤ) * t - n := by
      rw [hcsq]
      exact dvd_pow hpc (by norm_num)
    have hpn' : ((p : ℕ) : ℤ) ∣ n := by
      have h := dvd_sub (Dvd.intro t rfl) hpsub'
      have heq : ((p : ℕ) : ℤ) * t - (((p : ℕ) : ℤ) * t - n) = n := by ring
      rwa [heq] at h
    exact hkill (Dvd.intro t rfl) hpn'
  · -- p ∣ n : THE DESCENT
    obtain ⟨t, rfl⟩ := hpn
    have ht : 0 < t := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hn, mul_nonneg hppos.le (neg_nonneg.mpr hcon)]
    have htn : t ∣ ((p : ℕ) : ℤ) * t := ⟨(p : ℕ), by ring⟩
    have hCm_t : IsCoprime m t := hCmn.of_isCoprime_of_dvd_right htn
    have hCt_sub : IsCoprime t (m - ((p : ℕ) : ℤ) * t) := hCn_sub.of_isCoprime_of_dvd_left htn
    have hCt_add : IsCoprime t (m + ((p : ℕ) : ℤ) * t) := hCn_add.of_isCoprime_of_dvd_left htn
    have hcan : m * t * (m - ((p : ℕ) : ℤ) * t) * (m + ((p : ℕ) : ℤ) * t) = e' ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hprod
    obtain ⟨a, b, c, d, hasq, hbsq, hcsq, hdsq, hwsq⟩ :=
      four_coprime_split hm ht hsub hadd hCm_t hCm_sub hCm_add hCt_sub hCt_add hCband hcan
    have heq1 : a ^ 2 - c ^ 2 = ((p : ℕ) : ℤ) * b ^ 2 := by
      linear_combination -hasq + hcsq + ((p : ℕ) : ℤ) * hbsq
    have heq2 : d ^ 2 - a ^ 2 = ((p : ℕ) : ℤ) * b ^ 2 := by
      linear_combination -hdsq + hasq + ((p : ℕ) : ℤ) * hbsq
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hbsq
      omega
    -- the measure descends: 4|b| ≤ E
    have habs : e'.natAbs = (a * b * c * d).natAbs := by
      have h1 := congrArg Int.natAbs hwsq
      rw [Int.natAbs_pow, Int.natAbs_pow] at h1
      exact Nat.pow_left_injective (by norm_num) h1
    have ha2 : 2 ≤ a.natAbs := natAbs_ge_two_of_sq_ge_two hasq.symm (by omega)
    have hc1 : 1 ≤ c.natAbs := by
      rw [Nat.one_le_iff_ne_zero, Ne, Int.natAbs_eq_zero]
      rintro rfl
      simp at hcsq
      omega
    have hd1 : 1 ≤ d.natAbs := by
      rw [Nat.one_le_iff_ne_zero, Ne, Int.natAbs_eq_zero]
      rintro rfl
      simp at hdsq
      nlinarith [hadd]
    have hb1 : 1 ≤ b.natAbs := by
      rw [Nat.one_le_iff_ne_zero, Ne, Int.natAbs_eq_zero]
      exact hb0
    have hmeasure : 4 * b.natAbs ≤ E := by
      have hprodabs : e'.natAbs = a.natAbs * b.natAbs * c.natAbs * d.natAbs := by
        rw [habs, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
      have h1 : 2 * b.natAbs ≤ a.natAbs * b.natAbs :=
        Nat.mul_le_mul_right _ ha2
      have h2 : a.natAbs * b.natAbs ≤ a.natAbs * b.natAbs * c.natAbs :=
        Nat.le_mul_of_pos_right _ hc1
      have h3 : a.natAbs * b.natAbs * c.natAbs ≤ a.natAbs * b.natAbs * c.natAbs * d.natAbs :=
        Nat.le_mul_of_pos_right _ hd1
      omega
    exact ihE b hb0 hmeasure a c d heq1 heq2
  · -- p ∣ m − n : the doubled square refuses this placement
    obtain ⟨t, ht_eq⟩ := hpsub
    have ht : 0 < t := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hsub, ht_eq, mul_nonneg hppos.le (neg_nonneg.mpr hcon)]
    have htd : t ∣ m - n := ⟨(p : ℕ), by rw [ht_eq]; ring⟩
    have hCm_t : IsCoprime m t := hCm_sub.of_isCoprime_of_dvd_right htd
    have hCn_t : IsCoprime n t := hCn_sub.of_isCoprime_of_dvd_right htd
    have hCt_add : IsCoprime t (m + n) := hCband.of_isCoprime_of_dvd_left htd
    have hcan : m * n * t * (m + n) = e' ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hprod - m * n * (m + n) * ht_eq
    obtain ⟨a, b, c, d, hasq, hbsq, hcsq, hdsq, hwsq⟩ :=
      four_coprime_split hm hn ht hadd hCmn hCm_t hCm_add hCn_t hCn_add hCt_add hcan
    have hdvd : ((p : ℕ) : ℤ) ∣ d ^ 2 - 2 * a ^ 2 := by
      refine ⟨-c ^ 2, ?_⟩
      linear_combination -hdsq + 2 * hasq - ht_eq - ((p : ℕ) : ℤ) * hcsq
    obtain ⟨hpa, hpd2⟩ := theDoubledSquareDescendsToTheFrame h8 hdvd
    have hpm' : ((p : ℕ) : ℤ) ∣ m := by
      rw [hasq]
      exact dvd_pow hpa (by norm_num)
    have hpn' : ((p : ℕ) : ℤ) ∣ n := by
      have hpd3 : ((p : ℕ) : ℤ) ∣ m + n := by
        rw [hdsq]
        exact dvd_pow hpd2 (by norm_num)
      have h := dvd_sub hpd3 hpm'
      have heq : m + n - m = n := by ring
      rwa [heq] at h
    exact hkill hpm' hpn'
  · -- p ∣ m + n : the sum of two squares refuses this placement
    obtain ⟨t, ht_eq⟩ := hpadd
    have ht : 0 < t := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hadd, ht_eq, mul_nonneg hppos.le (neg_nonneg.mpr hcon)]
    have htd : t ∣ m + n := ⟨(p : ℕ), by rw [ht_eq]; ring⟩
    have hCm_t : IsCoprime m t := hCm_add.of_isCoprime_of_dvd_right htd
    have hCn_t : IsCoprime n t := hCn_add.of_isCoprime_of_dvd_right htd
    have hCsub_t : IsCoprime (m - n) t := hCband.of_isCoprime_of_dvd_right htd
    have hcan : m * n * (m - n) * t = e' ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hprod - m * n * (m - n) * ht_eq
    obtain ⟨a, b, c, d, hasq, hbsq, hcsq, hdsq, hwsq⟩ :=
      four_coprime_split hm hn hsub ht hCmn hCm_sub hCm_t hCn_sub hCn_t hCsub_t hcan
    have hdvd : ((p : ℕ) : ℤ) ∣ a ^ 2 + b ^ 2 := by
      refine ⟨t, ?_⟩
      linear_combination -hasq - hbsq + ht_eq
    obtain ⟨hpa, hpb⟩ := theSumOfSquaresDescendsToTheFrame h8 hdvd
    have hpm' : ((p : ℕ) : ℤ) ∣ m := by
      rw [hasq]
      exact dvd_pow hpa (by norm_num)
    have hpn' : ((p : ℕ) : ℤ) ∣ n := by
      rw [hbsq]
      exact dvd_pow hpb (by norm_num)
    exact hkill hpm' hpn'

/-! ## 5. The descent -/

/-- **THE CONGRUUM NEVER FORMS**: over any prime `p ≡ 3 (mod 8)`, three integer squares in
arithmetic progression with common difference `p·e²`, `e ≠ 0`, do not exist. -/
theorem theCongruumNeverForms (hp : p.Prime) (h8 : p % 8 = 3) :
    ∀ (E : ℕ) (u₁ u₂ u₃ e : ℤ), e.natAbs = E → e ≠ 0 →
      u₁ ^ 2 - u₂ ^ 2 = (p : ℤ) * e ^ 2 → u₃ ^ 2 - u₁ ^ 2 = (p : ℤ) * e ^ 2 → False := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro u₁ u₂ u₃ e hE he h₁ h₂
    have hpe : (0 : ℤ) < (p : ℤ) * e ^ 2 := by
      have h1 : (0 : ℤ) < e ^ 2 := by positivity
      have h2 : (0 : ℤ) < ((p : ℕ) : ℤ) := by exact_mod_cast hp.pos
      positivity
    by_cases hg : Int.gcd u₁ u₂ = 1
    case neg =>
      -- strip a common prime from the middle pair and descend
      have hg0 : Int.gcd u₁ u₂ ≠ 0 := by
        intro h0
        obtain ⟨hu₁, hu₂⟩ := Int.gcd_eq_zero_iff.mp h0
        rw [hu₁, hu₂] at h₁
        have h0' : (p : ℤ) * e ^ 2 = 0 := by linear_combination -h₁
        nlinarith [hpe, h0']
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hg
      have hqZ : Prime ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq)
      have hq1 : ((q : ℕ) : ℤ) ∣ u₁ :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hqd) (Int.gcd_dvd_left _ _)
      have hq2 : ((q : ℕ) : ℤ) ∣ u₂ :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hqd) (Int.gcd_dvd_right _ _)
      have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by
        have := hq.two_le
        omega
      have hqsq : ((q : ℕ) : ℤ) ^ 2 ∣ (p : ℤ) * e ^ 2 := by
        rw [← h₁]
        exact dvd_sub (pow_dvd_pow_of_dvd hq1 2) (pow_dvd_pow_of_dvd hq2 2)
      have hqe : ((q : ℕ) : ℤ) ∣ e := by
        have hqpe : ((q : ℕ) : ℤ) ∣ (p : ℤ) * e ^ 2 :=
          dvd_trans (dvd_pow_self _ (by norm_num)) hqsq
        rcases hqZ.dvd_mul.mp hqpe with hqp | hqe2
        · have hqp' : q ∣ p := by exact_mod_cast hqp
          have hqep : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp'
          subst hqep
          have hqq : ((q : ℕ) : ℤ) * ((q : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) * e ^ 2 := by
            have h := hqsq
            rwa [pow_two] at h
          have he2 : ((q : ℕ) : ℤ) ∣ e ^ 2 := (mul_dvd_mul_iff_left hq0).mp hqq
          exact hqZ.dvd_of_dvd_pow he2
        · exact hqZ.dvd_of_dvd_pow hqe2
      have hq3 : ((q : ℕ) : ℤ) ∣ u₃ := by
        apply hqZ.dvd_of_dvd_pow (n := 2)
        have hu3 : u₃ ^ 2 = u₁ ^ 2 + (p : ℤ) * e ^ 2 := by linear_combination h₂
        rw [hu3]
        refine dvd_add ?_ (Dvd.dvd.mul_left ?_ _)
        · exact dvd_trans (dvd_pow_self _ (by norm_num)) (pow_dvd_pow_of_dvd hq1 2)
        · exact dvd_trans (dvd_pow_self _ (by norm_num)) (pow_dvd_pow_of_dvd hqe 2)
      obtain ⟨v₁, rfl⟩ := hq1
      obtain ⟨v₂, rfl⟩ := hq2
      obtain ⟨v₃, rfl⟩ := hq3
      obtain ⟨f, rfl⟩ := hqe
      have hq2' : (2 : ℕ) ≤ q := hq.two_le
      have hf : f ≠ 0 := by
        rintro rfl
        simp at he
      have hE' : f.natAbs < E := by
        rw [← hE, Int.natAbs_mul, Int.natAbs_natCast]
        have hf1 : 1 ≤ f.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hf)
        nlinarith [hq2', hf1]
      refine ih f.natAbs hE' v₁ v₂ v₃ f rfl hf ?_ ?_
      · have hcancel : ((q : ℕ) : ℤ) ^ 2 * (v₁ ^ 2 - v₂ ^ 2)
            = ((q : ℕ) : ℤ) ^ 2 * ((p : ℤ) * f ^ 2) := by
          linear_combination h₁
        exact mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      · have hcancel : ((q : ℕ) : ℤ) ^ 2 * (v₃ ^ 2 - v₁ ^ 2)
            = ((q : ℕ) : ℤ) ^ 2 * ((p : ℤ) * f ^ 2) := by
          linear_combination h₂
        exact mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
    case pos =>
    have hu₂ : u₂ ≠ 0 := by
      rintro rfl
      have h : u₁ ^ 2 = (p : ℤ) * e ^ 2 := by linear_combination h₁
      exact thePrimeIsNotARationalSquare hp he h
    have hu₁ : u₁ ≠ 0 := by
      rintro rfl
      simp at h₁
      nlinarith [hpe, h₁, sq_nonneg u₂]
    rcases Int.even_or_odd e with ⟨e', rfl⟩ | ⟨k, rfl⟩
    case inr =>
      -- odd scale dies at the frame of eight
      have hz₁ := congrArg (fun t : ℤ => (t : ZMod 8)) h₁
      have hz₂ := congrArg (fun t : ℤ => (t : ZMod 8)) h₂
      push_cast at hz₁ hz₂
      rw [pcast8 h8] at hz₁ hz₂
      refine theOddScaleDiesAtEight (u₁ : ZMod 8) (u₂ : ZMod 8) (u₃ : ZMod 8) (k : ZMod 8)
        ⟨by linear_combination hz₁, by linear_combination hz₂⟩
    case inl =>
    have he' : e' ≠ 0 := by
      rintro rfl
      simp at he
    have h₁' : u₁ ^ 2 - u₂ ^ 2 = (p : ℤ) * (4 * e' ^ 2) := by linear_combination h₁
    have h₂' : u₃ ^ 2 - u₁ ^ 2 = (p : ℤ) * (4 * e' ^ 2) := by linear_combination h₂
    -- all three middle terms are odd
    have hodd₁ : u₁ % 2 = 1 := by
      rcases Int.even_or_odd u₁ with ⟨v, hv⟩ | ⟨v, hv⟩
      · exfalso
        have hu₂odd : ∃ w, u₂ = 2 * w + 1 := by
          rcases Int.even_or_odd u₂ with ⟨w, hw⟩ | ⟨w, hw⟩
          · exfalso
            have h2 : (2 : ℤ) ∣ u₁ := ⟨v, by omega⟩
            have h2' : (2 : ℤ) ∣ u₂ := ⟨w, by omega⟩
            have hcm := Int.dvd_gcd h2 h2'
            rw [hg] at hcm
            norm_num at hcm
          · exact ⟨w, hw⟩
        obtain ⟨w, hw⟩ := hu₂odd
        rw [hv, hw] at h₁'
        have hdvd41 : (4 : ℤ) ∣ 1 := by
          refine ⟨v * v - (p : ℤ) * e' ^ 2 - w ^ 2 - w, ?_⟩
          linear_combination -h₁'
        norm_num at hdvd41
      · omega
    have hodd₂ : u₂ % 2 = 1 := by
      rcases Int.even_or_odd u₂ with ⟨w, hw⟩ | ⟨w, hw⟩
      · exfalso
        obtain ⟨v, hv⟩ : ∃ v, u₁ = 2 * v + 1 := ⟨(u₁ - 1) / 2, by omega⟩
        rw [hv, hw] at h₁'
        have hdvd41 : (4 : ℤ) ∣ 1 := by
          refine ⟨w * w + (p : ℤ) * e' ^ 2 - v ^ 2 - v, ?_⟩
          linear_combination h₁'
        norm_num at hdvd41
      · omega
    have hodd₃ : u₃ % 2 = 1 := by
      rcases Int.even_or_odd u₃ with ⟨w, hw⟩ | ⟨w, hw⟩
      · exfalso
        obtain ⟨v, hv⟩ : ∃ v, u₁ = 2 * v + 1 := ⟨(u₁ - 1) / 2, by omega⟩
        rw [hv, hw] at h₂'
        have hdvd41 : (4 : ℤ) ∣ 1 := by
          refine ⟨w * w - (p : ℤ) * e' ^ 2 - v ^ 2 - v, ?_⟩
          linear_combination -h₂'
        norm_num at hdvd41
      · omega
    -- pass to absolute values
    have hA₁ : |u₁| ^ 2 = u₁ ^ 2 := sq_abs u₁
    have hA₂ : |u₂| ^ 2 = u₂ ^ 2 := sq_abs u₂
    have hA₃ : |u₃| ^ 2 = u₃ ^ 2 := sq_abs u₃
    have hh₁ : |u₁| ^ 2 - |u₂| ^ 2 = (p : ℤ) * (4 * e' ^ 2) := by
      rw [hA₁, hA₂]; exact h₁'
    have hh₂ : |u₃| ^ 2 - |u₁| ^ 2 = (p : ℤ) * (4 * e' ^ 2) := by
      rw [hA₃, hA₁]; exact h₂'
    have hgU : Int.gcd |u₁| |u₂| = 1 := by
      simpa [Int.gcd, Int.natAbs_abs] using hg
    have hUodd₂ : Odd |u₂| := odd_abs.mpr (Int.odd_iff.mpr hodd₂)
    have hUodd₃ : Odd |u₃| := odd_abs.mpr (Int.odd_iff.mpr hodd₃)
    have hU₁pos : 0 < |u₁| := abs_pos.mpr hu₁
    have hU₂pos : 0 < |u₂| := abs_pos.mpr hu₂
    have hpe4 : (0 : ℤ) < (p : ℤ) * (4 * e' ^ 2) := by
      have h1 : (0 : ℤ) < e' ^ 2 := by positivity
      have h2 : (0 : ℤ) < ((p : ℕ) : ℤ) := by exact_mod_cast hp.pos
      positivity
    have hU₃₂ : |u₂| < |u₃| := by
      have hsq : |u₂| ^ 2 < |u₃| ^ 2 := by nlinarith [hh₁, hh₂, hpe4]
      nlinarith [hsq, abs_nonneg u₂, abs_nonneg u₃]
    -- fold to the Pythagorean pair
    obtain ⟨r, hr⟩ := (hUodd₃.add_odd hUodd₂ : Even (|u₃| + |u₂|))
    obtain ⟨s, hs⟩ := (hUodd₃.sub_odd hUodd₂ : Even (|u₃| - |u₂|))
    have hU3 : |u₃| = r + s := by omega
    have hU2 : |u₂| = r - s := by omega
    have hrpos : 0 < r := by omega
    have hspos : 0 < s := by omega
    rw [hU2] at hh₁
    rw [hU3] at hh₂
    have hrs_sum : r ^ 2 + s ^ 2 = |u₁| ^ 2 := by
      have h4 : 2 * (r ^ 2 + s ^ 2) = 2 * |u₁| ^ 2 := by linear_combination hh₂ - hh₁
      linarith [h4]
    have hrs_prod : r * s = 2 * ((p : ℤ) * e' ^ 2) := by
      have h4 : 4 * (r * s) = 4 * (2 * ((p : ℤ) * e' ^ 2)) := by
        linear_combination hh₁ + hh₂
      linarith [h4]
    have hgrs : Int.gcd r s = 1 := by
      apply gcd_eq_one_of_no_common_prime
      intro q hq hq1 hq2
      have hqZ : Prime ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq)
      have hq3 : ((q : ℕ) : ℤ) ∣ |u₂| := by
        rw [hU2]
        exact dvd_sub hq1 hq2
      have hq5 : ((q : ℕ) : ℤ) ∣ |u₁| := by
        apply hqZ.dvd_of_dvd_pow (n := 2)
        rw [← hrs_sum]
        refine dvd_add ?_ ?_
        · exact dvd_trans (dvd_pow_self _ (by norm_num)) (pow_dvd_pow_of_dvd hq1 2)
        · exact dvd_trans (dvd_pow_self _ (by norm_num)) (pow_dvd_pow_of_dvd hq2 2)
      have hCU : IsCoprime |u₁| |u₂| := Int.isCoprime_iff_gcd_eq_one.mpr hgU
      exact unit_prime_refuted hq (hCU.isUnit_of_dvd' hq5 hq3)
    have hE2 : 2 * e'.natAbs = E := by
      rw [← hE]
      have h2 : e' + e' = 2 * e' := by ring
      rw [h2, Int.natAbs_mul]
      norm_num
    have hIH : ∀ b : ℤ, b ≠ 0 → 4 * b.natAbs ≤ E →
        ∀ x y z : ℤ, x ^ 2 - y ^ 2 = (p : ℤ) * b ^ 2 →
          z ^ 2 - x ^ 2 = (p : ℤ) * b ^ 2 → False := by
      intro b hb hble x y z hx hz
      have hbpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
      exact ih b.natAbs (by omega) x y z b rfl hb hx hz
    rcases Int.even_or_odd r with hreven | ⟨w0, hw0⟩
    · -- s is odd: classify (s, r, |u₁|)
      have hsodd : s % 2 = 1 := by
        obtain ⟨v0, hv0⟩ := hreven
        rcases Int.even_or_odd s with ⟨w1, hw1⟩ | ⟨w1, hw1⟩
        · exfalso
          have h2 : (2 : ℤ) ∣ r := ⟨v0, by omega⟩
          have h2' : (2 : ℤ) ∣ s := ⟨w1, by omega⟩
          have hcm := Int.dvd_gcd h2 h2'
          rw [hgrs] at hcm
          norm_num at hcm
        · omega
      have ht : PythagoreanTriple s r |u₁| := by
        delta PythagoreanTriple
        linear_combination hrs_sum
      obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
        ht.coprime_classification' (by rwa [Int.gcd_comm] at hgrs) hsodd hU₁pos
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at ht2
        omega
      have hm0 : 0 < m := by
        rcases eq_or_lt_of_le ht6 with hz | hz
        · exfalso
          rw [← hz] at ht2
          simp at ht2
          omega
        · exact hz
      have hnpos : 0 < n := by
        by_contra hcon
        push_neg at hcon
        have hneg : n < 0 := lt_of_le_of_ne hcon hn0
        nlinarith [ht2, hrpos, mul_pos hm0 (neg_pos.mpr hneg)]
      have hnm : n < m := by
        by_contra hcon
        push_neg at hcon
        have h1 : m * m ≤ n * n := mul_le_mul hcon hcon hm0.le hnpos.le
        nlinarith [ht1, hspos, h1]
      rw [ht1, ht2] at hrs_prod
      have hprodmn : m * n * (m - n) * (m + n) = (p : ℤ) * e' ^ 2 := by
        have h2 : 2 * (m * n * (m - n) * (m + n)) = 2 * ((p : ℤ) * e' ^ 2) := by
          linear_combination hrs_prod
        linarith [h2]
      exact theFourFactorsRefuseOrDescend hp h8 ht4 hnpos hnm ht5 he' hE2 hprodmn hIH
    · -- r is odd: classify (r, s, |u₁|)
      have hrodd : r % 2 = 1 := by omega
      have ht : PythagoreanTriple r s |u₁| := by
        delta PythagoreanTriple
        linear_combination hrs_sum
      obtain ⟨m, n, ht1, ht2, ht3, ht4, ht5, ht6⟩ :=
        ht.coprime_classification' hgrs hrodd hU₁pos
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at ht2
        omega
      have hm0 : 0 < m := by
        rcases eq_or_lt_of_le ht6 with hz | hz
        · exfalso
          rw [← hz] at ht2
          simp at ht2
          omega
        · exact hz
      have hnpos : 0 < n := by
        by_contra hcon
        push_neg at hcon
        have hneg : n < 0 := lt_of_le_of_ne hcon hn0
        nlinarith [ht2, hspos, mul_pos hm0 (neg_pos.mpr hneg)]
      have hnm : n < m := by
        by_contra hcon
        push_neg at hcon
        have h1 : m * m ≤ n * n := mul_le_mul hcon hcon hm0.le hnpos.le
        nlinarith [ht1, hrpos, h1]
      rw [ht1, ht2] at hrs_prod
      have hprodmn : m * n * (m - n) * (m + n) = (p : ℤ) * e' ^ 2 := by
        have h2 : 2 * (m * n * (m - n) * (m + n)) = 2 * ((p : ℤ) * e' ^ 2) := by
          linear_combination hrs_prod
        linarith [h2]
      exact theFourFactorsRefuseOrDescend hp h8 ht4 hnpos hnm ht5 he' hE2 hprodmn hIH

/-! ## 6. The triangle refused: Genocchi's theorem -/

/-- **THE HALF-TURN PRIMES ARE NOT CONGRUENT** (Genocchi): no prime `p ≡ 3 (mod 8)` is the
area of a rational right triangle.  The triangle folds to three rational squares in
progression with common difference `p`, the denominators clear, and the congruum descent
refuses.  Infinitely many quadratic twists of the congruent-number family, their realized
triangles refused by one kernel-checked theorem. -/
theorem theHalfTurnPrimesAreNotCongruent (hp : p.Prime) (h8 : p % 8 = 3) :
    ∀ a b c : ℚ, a * b = 2 * p → a ^ 2 + b ^ 2 = c ^ 2 → False := by
  intro a b c hab hpyth
  obtain ⟨x₁, hx₁⟩ : ∃ x : ℚ, x = (a - b) / 2 := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x : ℚ, x = c / 2 := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ x : ℚ, x = (a + b) / 2 := ⟨_, rfl⟩
  have hq₁ : x₂ ^ 2 - x₁ ^ 2 = ((p : ℕ) : ℚ) := by
    rw [hx₁, hx₂]
    linear_combination (-(1 : ℚ) / 4) * hpyth + (1 / 2) * hab
  have hq₂ : x₃ ^ 2 - x₂ ^ 2 = ((p : ℕ) : ℚ) := by
    rw [hx₂, hx₃]
    linear_combination ((1 : ℚ) / 4) * hpyth + (1 / 2) * hab
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = (x₁.den : ℤ) * (x₂.den : ℤ) * (x₃.den : ℤ) := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast x₁.den_nz) (by exact_mod_cast x₂.den_nz))
      (by exact_mod_cast x₃.den_nz)
  obtain ⟨w₁, hw₁⟩ : ∃ w : ℤ, w = x₁.num * (x₂.den : ℤ) * (x₃.den : ℤ) := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w : ℤ, w = x₂.num * (x₁.den : ℤ) * (x₃.den : ℤ) := ⟨_, rfl⟩
  obtain ⟨w₃, hw₃⟩ : ∃ w : ℤ, w = x₃.num * (x₁.den : ℤ) * (x₂.den : ℤ) := ⟨_, rfl⟩
  have hc₁ : ((w₁ : ℤ) : ℚ) = x₁ * ((D : ℤ) : ℚ) := by
    rw [hw₁, hD]
    push_cast
    rw [← Rat.mul_den_eq_num x₁]
    ring
  have hc₂ : ((w₂ : ℤ) : ℚ) = x₂ * ((D : ℤ) : ℚ) := by
    rw [hw₂, hD]
    push_cast
    rw [← Rat.mul_den_eq_num x₂]
    ring
  have hc₃ : ((w₃ : ℤ) : ℚ) = x₃ * ((D : ℤ) : ℚ) := by
    rw [hw₃, hD]
    push_cast
    rw [← Rat.mul_den_eq_num x₃]
    ring
  have hint₁ : w₂ ^ 2 - w₁ ^ 2 = ((p : ℕ) : ℤ) * D ^ 2 := by
    have hQ : ((w₂ : ℤ) : ℚ) ^ 2 - ((w₁ : ℤ) : ℚ) ^ 2 = ((p : ℕ) : ℚ) * ((D : ℤ) : ℚ) ^ 2 := by
      rw [hc₂, hc₁]
      linear_combination ((D : ℤ) : ℚ) ^ 2 * hq₁
    exact_mod_cast hQ
  have hint₂ : w₃ ^ 2 - w₂ ^ 2 = ((p : ℕ) : ℤ) * D ^ 2 := by
    have hQ : ((w₃ : ℤ) : ℚ) ^ 2 - ((w₂ : ℤ) : ℚ) ^ 2 = ((p : ℕ) : ℚ) * ((D : ℤ) : ℚ) ^ 2 := by
      rw [hc₃, hc₂]
      linear_combination ((D : ℤ) : ℚ) ^ 2 * hq₂
    exact_mod_cast hQ
  exact theCongruumNeverForms hp h8 D.natAbs w₂ w₁ w₃ D rfl hD0 hint₁ hint₂

/-- The first three members of the infinite family: three, eleven, and nineteen are not
congruent numbers. -/
theorem theFirstThreeMembers :
    (∀ a b c : ℚ, a * b = 2 * 3 → a ^ 2 + b ^ 2 = c ^ 2 → False) ∧
    (∀ a b c : ℚ, a * b = 2 * 11 → a ^ 2 + b ^ 2 = c ^ 2 → False) ∧
    (∀ a b c : ℚ, a * b = 2 * 19 → a ^ 2 + b ^ 2 = c ^ 2 → False) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := theHalfTurnPrimesAreNotCongruent (p := 3) (by norm_num) (by norm_num)
    intro a b c hab hpyth
    exact h a b c (by exact_mod_cast hab) hpyth
  · have h := theHalfTurnPrimesAreNotCongruent (p := 11) (by norm_num) (by norm_num)
    intro a b c hab hpyth
    exact h a b c (by exact_mod_cast hab) hpyth
  · have h := theHalfTurnPrimesAreNotCongruent (p := 19) (by norm_num) (by norm_num)
    intro a b c hab hpyth
    exact h a b c (by exact_mod_cast hab) hpyth

end Soma.Holonics.Millennium.Congruum
