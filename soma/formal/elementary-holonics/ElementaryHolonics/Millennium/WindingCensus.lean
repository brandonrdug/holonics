import ElementaryHolonics.Millennium.RankOne
import ElementaryHolonics.Millennium.Descent
import Mathlib.Tactic

/-!
# WindingCensus: the closed windings of the rank-one curve, counted receiver by receiver

The torsion classification, framed as what it is: **a census of closed windings**.  A rational
point of `y² = x³ − 25x` is a route; `n • Q` is its repeated traversal, and repetition explores
only the cyclic subgroup the route generates.  A winding is *closed* when the traversal returns
to rest — `n • Q = 0` — and the torsion subgroup is the population of routes whose windings
close, against the free part whose windings never do.

The census is read one receiver at a time, and each receiver sees a band of winding numbers:

* **The square-class face** — the `ℤ/2` double cover `ℚ*/ℚ*²`, the parity face of winding —
  reads the *second* and *fourth* windings.  The second winding closes exactly on the Klein
  table (`theSecondWindingClosesExactlyOnTheTable`), and no route halves a half-turn
  (`theDoubledRouteAvoidsTheTable`), so the fourth winding closes only where the second already
  did (`theFourthWindingIsAlreadyTheSecond`).  The three refusing square classes are `−1`, `2`,
  `2` — cousins of the separators `−1`, `2`, `−2` that carried `Descent.lean`'s injectivity on
  the rank-zero curve.
* **The tangent-return reading** — the third winding closes only where the tangent construction
  returns to its own abscissa, which is the third division polynomial
  `3x⁴ − 150x² − 625` here; its vanishing forces `(3x² − 75)² = 7500`, and three is not a
  rational square (`theThirdWindingNeverCloses`).
* Every further winding number would need its own polynomial receiver, and the family never
  covers the population — infinitely many primes remain.  **The complete census therefore
  reduces to one statement** (`theCensusReducesToTheDistantPrimeWindings`): if no route closes
  at a prime winding of five or more, `RankOne.TheTorsionIsTheKleinGroup` holds.  That residual
  statement is carried as the named-open `TheDistantPrimeWindingsNeverClose`; its classical
  proof is a transport to a compact frame — reduction to a finite field, where *every* route
  closes and the whole census is one reading (this curve mod three has four points, so no prime
  winding of five or more survives the transport), with the injectivity of that transport on
  closed windings itself a well-founded descent through the p-adic filtration, the same
  mechanism as `MinusFourth.lean`.  Neither the transport nor its injectivity has a mathlib
  owner (measured 2026-08-21: `Reduction.lean` reduces the curve, not its points;
  `DivisionPolynomial/` has no torsion link; no Lutz–Nagell, no Mazur), so the compact frame is
  the owed instrument, not an import.

What this file advances, measured against `RankOne.lean`'s named-open proposition: the torsion
classification previously needed the classical machinery wholesale; it now needs exactly the
distant prime windings, with every winding number below five read off by rational receivers.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the census below
the fifth winding is complete and unconditional; nothing is claimed about prime windings of
five or more; nothing about other curves, ranks, or the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.WindingCensus

open WeierstrassCurve.Affine
open RankOne (E5 T0 T5 Tm5)

/-! ## 1. The arithmetic separators -/

/-- Three is not a rational square — the separator behind the third winding's refusal. -/
theorem theThreeIsNotASquare : ¬ IsSquare (3 : ℚ) := by
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  exact (by norm_num : Nat.Prime 3).not_isSquare

/-! ## 2. The coordinate instruments -/

/-- The abscissa face of a point; the identity reads zero.  Used only forward, to transport a
point equality onto its `x`-coordinate. -/
private def abscissa : E5.Point → ℚ
  | .zero => 0
  | .some (x := x) _ => x

private lemma some_eq_some {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : E5.Nonsingular x₁ y₁} {h₂ : E5.Nonsingular x₂ y₂} :
    (Point.some h₁ : E5.Point) = Point.some h₂ := by
  subst hx; subst hy; rfl

/-- On this curve the negation face is the plain sign flip: `negY x y = −y`. -/
private lemma negY_eq (x y : ℚ) : E5.negY x y = -y := by
  simp [negY, RankOne.E5]

/-- The curve equation, extracted from nonsingularity. -/
private lemma curve_eq {x y : ℚ} (h : E5.Nonsingular x y) : y ^ 2 = x ^ 3 - 25 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [RankOne.E5] at h1
  linarith [h1]

/-- **The tangent return in coordinates**: mathlib's `addX` at the tangent slope is
`((3x² − 25) / (2y))² − 2x`. -/
private lemma addX_tangent {x y : ℚ} (hy : y ≠ E5.negY x y) :
    E5.addX x x (E5.slope x x y y) = ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 - 2 * x := by
  rw [slope_of_Y_ne rfl hy, negY_eq]
  simp only [addX, RankOne.E5]
  ring

/-- **The doubled abscissa clears to one square**: on the curve,
`(3x² − 25)² − 8xy² = (x² + 25)²`. -/
theorem theClearedDoubleIsTheSquare {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) :
    (3 * x ^ 2 - 25) ^ 2 - 8 * x * y ^ 2 = (x ^ 2 + 25) ^ 2 := by
  linear_combination (-8 * x) * h

/-! ## 3. The four refusals, in coordinates -/

/-- **Nothing halves the half-turn at zero**: the tangent return cannot land on abscissa `0`,
for that would force `(x² + 25)² = 0`. -/
theorem theZeroTurnRefusesHalving {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 - 2 * x ≠ 0 := by
  intro h0
  have h2y : (2 * y) ≠ 0 := mul_ne_zero two_ne_zero hy
  have h1 : ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 = 2 * x := by linarith
  have h2 : (3 * x ^ 2 - 25) ^ 2 = 2 * x * (2 * y) ^ 2 := by
    rw [← h1]; field_simp
  have h3 : (x ^ 2 + 25) ^ 2 = 0 := by
    rw [← theClearedDoubleIsTheSquare h]; linear_combination h2
  have h4 : x ^ 2 + 25 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h3
  nlinarith [sq_nonneg x]

/-- **Nothing halves the half-turn at five**: landing on abscissa `5` would force
`(x − 5)² = 50`, and two is not a rational square. -/
theorem theFiveTurnRefusesHalving {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 - 2 * x ≠ 5 := by
  intro h0
  have h2y : (2 * y) ≠ 0 := mul_ne_zero two_ne_zero hy
  have h1 : ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 = 5 + 2 * x := by linarith
  have h2 : (3 * x ^ 2 - 25) ^ 2 = (5 + 2 * x) * (2 * y) ^ 2 := by
    rw [← h1]; field_simp
  have h3 : (x ^ 2 - 10 * x - 25) ^ 2 = 0 := by
    linear_combination h2 - theClearedDoubleIsTheSquare h + 20 * h
  have h4 : x ^ 2 - 10 * x - 25 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h3
  refine Descent.notSquareTwo ⟨(x - 5) / 5, ?_⟩
  field_simp
  linear_combination -h4

/-- **Nothing halves the half-turn at negative five**: landing on abscissa `−5` would force
`(x + 5)² = 50`. -/
theorem theNegativeFiveTurnRefusesHalving {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 - 2 * x ≠ -5 := by
  intro h0
  have h2y : (2 * y) ≠ 0 := mul_ne_zero two_ne_zero hy
  have h1 : ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 = -5 + 2 * x := by linarith
  have h2 : (3 * x ^ 2 - 25) ^ 2 = (-5 + 2 * x) * (2 * y) ^ 2 := by
    rw [← h1]; field_simp
  have h3 : (x ^ 2 + 10 * x - 25) ^ 2 = 0 := by
    linear_combination h2 - theClearedDoubleIsTheSquare h - 20 * h
  have h4 : x ^ 2 + 10 * x - 25 = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h3
  refine Descent.notSquareTwo ⟨(x + 5) / 5, ?_⟩
  field_simp
  linear_combination -h4

/-- **The tangent return cannot rest on its own abscissa**: `x(2Q) = x(Q)` is the third
division polynomial `3x⁴ − 150x² − 625 = 0`, which forces `(3x² − 75)² = 7500`, and three is
not a rational square. -/
theorem theThirdWindingRefusesTheReturn {x y : ℚ} (h : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 - 2 * x ≠ x := by
  intro h0
  have h2y : (2 * y) ≠ 0 := mul_ne_zero two_ne_zero hy
  have h1 : ((3 * x ^ 2 - 25) / (2 * y)) ^ 2 = 3 * x := by linarith
  have h2 : (3 * x ^ 2 - 25) ^ 2 = 3 * x * (2 * y) ^ 2 := by
    rw [← h1]; field_simp
  have h3 : 3 * x ^ 4 - 150 * x ^ 2 - 625 = 0 := by
    linear_combination theClearedDoubleIsTheSquare h - h2 - 4 * x * h
  refine theThreeIsNotASquare ⟨(3 * x ^ 2 - 75) / 50, ?_⟩
  field_simp
  linear_combination -3 * h3

/-! ## 4. The census, winding by winding -/

/-- **The census at the second winding**: a route closes in two turns exactly on the Klein
table. -/
theorem theSecondWindingClosesExactlyOnTheTable (Q : E5.Point) :
    Q + Q = 0 ↔ (Q = 0 ∨ Q = T0 ∨ Q = T5 ∨ Q = Tm5) := by
  constructor
  · intro hQQ
    cases Q with
    | zero => exact Or.inl rfl
    | @some x y h =>
      by_cases hy : y = E5.negY x y
      · have hy0 : y = 0 := by rw [negY_eq] at hy; linarith
        subst hy0
        have heq := curve_eq h
        have hx : x = 0 ∨ x = 5 ∨ x = -5 := by
          have hcube : x * ((x - 5) * (x + 5)) = 0 := by linear_combination -heq
          rcases mul_eq_zero.mp hcube with h1 | h1
          · exact Or.inl h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact Or.inr (Or.inl (by linarith))
            · exact Or.inr (Or.inr (by linarith))
        rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inl (some_eq_some rfl rfl))
        · exact Or.inr (Or.inr (Or.inl (some_eq_some rfl rfl)))
        · exact Or.inr (Or.inr (Or.inr (some_eq_some rfl rfl)))
      · rw [Point.add_self_of_Y_ne hy] at hQQ
        exact absurd hQQ (Point.some_ne_zero _)
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · exact RankOne.theThreePointsAreHalfTurns.1
    · exact RankOne.theThreePointsAreHalfTurns.2.1
    · exact RankOne.theThreePointsAreHalfTurns.2.2

/-- **No route halves a half-turn**: the doubled population avoids the three half-turns
entirely — the square classes `−1`, `2`, `2` refuse, one per half-turn. -/
theorem theDoubledRouteAvoidsTheTable (Q : E5.Point) :
    Q + Q ≠ T0 ∧ Q + Q ≠ T5 ∧ Q + Q ≠ Tm5 := by
  cases Q with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      · intro hcontra
        rw [← Point.zero_def, add_zero] at hcontra
        exact Point.some_ne_zero _ hcontra.symm
  | @some x y h =>
    have heq := curve_eq h
    by_cases hy : y = E5.negY x y
    · rw [Point.add_self_of_Y_eq hy]
      exact ⟨fun hc => Point.some_ne_zero _ hc.symm, fun hc => Point.some_ne_zero _ hc.symm,
        fun hc => Point.some_ne_zero _ hc.symm⟩
    · have hy0 : y ≠ 0 := fun h0 => hy (by rw [negY_eq, h0, neg_zero])
      rw [Point.add_self_of_Y_ne hy]
      refine ⟨?_, ?_, ?_⟩ <;> intro hcontra
      · have habs := congrArg abscissa hcontra
        simp only [RankOne.T0, abscissa] at habs
        rw [addX_tangent hy] at habs
        exact theZeroTurnRefusesHalving heq hy0 habs
      · have habs := congrArg abscissa hcontra
        simp only [RankOne.T5, abscissa] at habs
        rw [addX_tangent hy] at habs
        exact theFiveTurnRefusesHalving heq hy0 habs
      · have habs := congrArg abscissa hcontra
        simp only [RankOne.Tm5, abscissa] at habs
        rw [addX_tangent hy] at habs
        exact theNegativeFiveTurnRefusesHalving heq hy0 habs

/-- **The fourth winding is already the second**: a route killed by four is killed by two. -/
theorem theFourthWindingIsAlreadyTheSecond (Q : E5.Point) (h4 : 4 • Q = 0) : 2 • Q = 0 := by
  by_contra h2
  have hRR : 2 • Q + 2 • Q = 0 := by
    have hcast : (4 : ℕ) • Q = (2 * 2 : ℕ) • Q := by norm_num
    rw [hcast, ← smul_smul, two_smul] at h4
    exact h4
  rcases (theSecondWindingClosesExactlyOnTheTable (2 • Q)).mp hRR with h | h | h | h
  · exact h2 h
  · exact (theDoubledRouteAvoidsTheTable Q).1 (by rwa [two_smul] at h)
  · exact (theDoubledRouteAvoidsTheTable Q).2.1 (by rwa [two_smul] at h)
  · exact (theDoubledRouteAvoidsTheTable Q).2.2 (by rwa [two_smul] at h)

/-- **The third winding never closes off the identity**: the tangent return would have to rest
on its own abscissa, and three is not a rational square. -/
theorem theThirdWindingNeverCloses (Q : E5.Point) (hQ : Q ≠ 0) : 3 • Q ≠ 0 := by
  intro h3
  cases Q with
  | zero => exact hQ rfl
  | @some x y h =>
    have heq := curve_eq h
    rw [show (3 : ℕ) = 2 + 1 by rfl, add_smul, one_smul, two_smul] at h3
    by_cases hy : y = E5.negY x y
    · rw [Point.add_self_of_Y_eq hy, zero_add] at h3
      exact Point.some_ne_zero h h3
    · have hy0 : y ≠ 0 := fun h0 => hy (by rw [negY_eq, h0, neg_zero])
      have h2Q := eq_neg_of_add_eq_zero_left h3
      rw [Point.add_self_of_Y_ne hy, Point.neg_some] at h2Q
      have habs := congrArg abscissa h2Q
      simp only [abscissa] at habs
      rw [addX_tangent hy] at habs
      exact theThirdWindingRefusesTheReturn heq hy0 habs

/-- **The census below the fifth winding is complete**: every route closed by a winding number
below five is on the Klein table. -/
theorem theCensusBelowTheFifthWinding (Q : E5.Point) (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4)
    (h : n • Q = 0) : Q = 0 ∨ Q = T0 ∨ Q = T5 ∨ Q = Tm5 := by
  interval_cases n
  · left; rwa [one_smul] at h
  · exact (theSecondWindingClosesExactlyOnTheTable Q).mp (by rwa [two_smul] at h)
  · rcases eq_or_ne Q 0 with rfl | hQ
    · exact Or.inl rfl
    · exact absurd h (theThirdWindingNeverCloses Q hQ)
  · have h2 := theFourthWindingIsAlreadyTheSecond Q h
    exact (theSecondWindingClosesExactlyOnTheTable Q).mp (by rwa [two_smul] at h2)

/-! ## 5. The reduction of the whole census -/

/-- **The distant prime windings never close** — the one statement standing between the
receiver-by-receiver census and the full torsion classification.  Classically true: this curve
reduced mod three has four points, and reduction injects closed windings, so no prime winding
of five or more survives the transport.  The transport and its injectivity have no mathlib
owner; open here. -/
def TheDistantPrimeWindingsNeverClose : Prop :=
  ∀ (p : ℕ) (R : E5.Point), Nat.Prime p → 5 ≤ p → p • R = 0 → R = 0

/-- **THE REDUCTION: the whole census hangs on the distant prime windings.**  Granting
`TheDistantPrimeWindingsNeverClose`, the torsion of `y² = x³ − 25x` is exactly the Klein table
— `RankOne.TheTorsionIsTheKleinGroup` follows.  The square-class receiver reads the second and
fourth windings, the tangent-return receiver the third, and every remaining winding number
factors through a prime the rational face cannot see. -/
theorem theCensusReducesToTheDistantPrimeWindings
    (hdistant : TheDistantPrimeWindingsNeverClose) : RankOne.TheTorsionIsTheKleinGroup := by
  intro Q
  constructor
  · rintro ⟨n, hn, hQ⟩
    have hfin : IsOfFinAddOrder Q := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hQ⟩
    have hdpos : 0 < addOrderOf Q := hfin.addOrderOf_pos
    have hprime2 : ∀ p : ℕ, Nat.Prime p → p ∣ addOrderOf Q → p = 2 := by
      intro p hp hpd
      by_contra hp2
      have hR : addOrderOf ((addOrderOf Q / p) • Q) = p :=
        addOrderOf_nsmul_addOrderOf_sub (by omega) hpd
      have hRp : p • ((addOrderOf Q / p) • Q) = 0 := by
        have hclose := addOrderOf_nsmul_eq_zero ((addOrderOf Q / p) • Q)
        rwa [hR] at hclose
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      rcases Nat.lt_or_ge p 5 with h5 | h5
      · have hp3' : p = 3 := by
          interval_cases p
          · rfl
          · exact absurd hp (by norm_num)
        subst hp3'
        have hR0 : (addOrderOf Q / 3) • Q ≠ 0 := by
          intro h0
          rw [h0, addOrderOf_zero] at hR
          omega
        exact theThirdWindingNeverCloses _ hR0 hRp
      · have hzero := hdistant p _ hp h5 hRp
        rw [hzero, addOrderOf_zero] at hR
        omega
    have hno4 : ¬ (4 ∣ addOrderOf Q) := by
      intro h4d
      have hR : addOrderOf ((addOrderOf Q / 4) • Q) = 4 :=
        addOrderOf_nsmul_addOrderOf_sub (by omega) h4d
      have hR4 : 4 • ((addOrderOf Q / 4) • Q) = 0 := by
        have hclose := addOrderOf_nsmul_eq_zero ((addOrderOf Q / 4) • Q)
        rwa [hR] at hclose
      have hR2 := theFourthWindingIsAlreadyTheSecond _ hR4
      have hdvd : addOrderOf ((addOrderOf Q / 4) • Q) ∣ 2 :=
        addOrderOf_dvd_of_nsmul_eq_zero hR2
      rw [hR] at hdvd
      norm_num at hdvd
    have hd2 : addOrderOf Q ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hgt with h4 | ⟨p, hp, hpd, hodd⟩
      · exact hno4 h4
      · have hp2 := hprime2 p hp hpd
        rw [hp2] at hodd
        simp [Nat.odd_iff] at hodd
    rcases (by omega : addOrderOf Q = 1 ∨ addOrderOf Q = 2) with h1 | h2
    · exact Or.inl (AddMonoid.addOrderOf_eq_one_iff.mp h1)
    · have h2Q : 2 • Q = 0 := by
        have hclose := addOrderOf_nsmul_eq_zero Q
        rwa [h2] at hclose
      exact (theSecondWindingClosesExactlyOnTheTable Q).mp (by rwa [two_smul] at h2Q)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_pos, by simp⟩
    · exact ⟨2, by norm_num, by rw [two_smul]; exact RankOne.theThreePointsAreHalfTurns.1⟩
    · exact ⟨2, by norm_num, by rw [two_smul]; exact RankOne.theThreePointsAreHalfTurns.2.1⟩
    · exact ⟨2, by norm_num, by rw [two_smul]; exact RankOne.theThreePointsAreHalfTurns.2.2⟩

end Soma.Holonics.Millennium.WindingCensus
