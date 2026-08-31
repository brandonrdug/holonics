import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# FrameDescent: the depth calculus and chart identities for the compact frame's kernel

The ℚ-layer of the compact-frame instrument.  The winding-census record reduced the torsion
classification of `y² = x³ − 25x` to one statement — no route closes at a prime winding of
five or more — and the classical proof transports the census to the frame at three, where the
kernel of the transport refuses closed windings by a strictly descending chain of 3-adic
depths.  This file builds everything that argument needs **below** the level of curve points:

* **the depth calculus** — `Deep j q` (depth at least `j`) and `Sharp j q` (depth exactly
  `j`), a thin wrapper over `padicValRat 3` whose one load-bearing law is that a sharp
  summand carries the sum past any strictly deeper one;
* **the entry classification** — a curve point with a three in its abscissa's denominator
  sits at an exact level: `Sharp (−2k) x` and `Sharp (−3k) y` for one `k ≥ 1`;
* **the integral forcing** — a three-integral point has ordinate depth at least one (the
  Fermat cube `x³ − x` is deep): the frame at three is pure half-turns, which is what forces
  any odd winding below the surface;
* **the transport chart** — `t = x/y`, `s = 1/y`, in which the identity is the origin and
  the curve reads `s = t³ − 25ts²`; the chord slope is carried by a unit denominator
  (`theChordSlopeIsCarriedByAUnit`, whose whole proof is one subtraction of chart
  equations); the tangent line has a double root at its point of tangency
  (`theTangentLineHasADoubleRoot`, pure algebra from the slope's defining equation); and the
  cubic a line cuts from the chart yields the sum formula
  `(1 − 25α²)(t₁ + t₂ + u) = 50αβ` whenever the third root is distinct from the others
  (`theChordCutsTheSumFormula`, `theTangentCutsTheSumFormula`).

Every identity here was verified in exact modular arithmetic on random points of the curve
over two large prime fields before encoding.  Every `theorem` is discharged and none depends
on `sorryAx`.  **Boundary**: this file mentions no elliptic-curve point type; the point-level
induction that spends these instruments lives in `DistantWindings.lean`.
-/

namespace Soma.Holonics.Millennium.FrameDescent

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-! ## 1. The depth calculus -/

/-- Depth at least `j`: the value vanishes or its 3-adic valuation is at least `j`. -/
def Deep (j : ℤ) (q : ℚ) : Prop := q = 0 ∨ j ≤ padicValRat 3 q

/-- Depth exactly `j`: nonzero, with 3-adic valuation exactly `j`. -/
def Sharp (j : ℤ) (q : ℚ) : Prop := q ≠ 0 ∧ padicValRat 3 q = j

theorem Sharp.deep {j : ℤ} {q : ℚ} (h : Sharp j q) : Deep j q := Or.inr h.2.ge

theorem Deep.mono {i j : ℤ} {q : ℚ} (hij : i ≤ j) (h : Deep j q) : Deep i q :=
  h.imp id fun hj => hij.trans hj

theorem deep_zero (j : ℤ) : Deep j 0 := Or.inl rfl

theorem Deep.neg {j : ℤ} {q : ℚ} (h : Deep j q) : Deep j (-q) := by
  rcases h with h | h
  · exact Or.inl (by rw [h, neg_zero])
  · exact Or.inr (by rwa [padicValRat.neg])

theorem Deep.add {j : ℤ} {q r : ℚ} (hq : Deep j q) (hr : Deep j r) : Deep j (q + r) := by
  rcases hq with hq | hq
  · rwa [hq, zero_add]
  rcases hr with hr | hr
  · rw [hr, add_zero]
    exact Or.inr hq
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  · exact Or.inr (le_trans (le_min hq hr) (padicValRat.min_le_padicValRat_add hqr))

theorem Deep.mul {i j : ℤ} {q r : ℚ} (hq : Deep i q) (hr : Deep j r) :
    Deep (i + j) (q * r) := by
  by_cases hq0 : q = 0
  · exact Or.inl (by rw [hq0, zero_mul])
  by_cases hr0 : r = 0
  · exact Or.inl (by rw [hr0, mul_zero])
  rcases hq with hq | hq
  · exact absurd hq hq0
  rcases hr with hr | hr
  · exact absurd hr hr0
  exact Or.inr (by rw [padicValRat.mul hq0 hr0]; exact add_le_add hq hr)

theorem Sharp.mul {i j : ℤ} {q r : ℚ} (hq : Sharp i q) (hr : Sharp j r) :
    Sharp (i + j) (q * r) :=
  ⟨mul_ne_zero hq.1 hr.1, by rw [padicValRat.mul hq.1 hr.1, hq.2, hr.2]⟩

theorem Sharp.inv {j : ℤ} {q : ℚ} (h : Sharp j q) : Sharp (-j) q⁻¹ :=
  ⟨inv_ne_zero h.1, by rw [padicValRat.inv, h.2]⟩

/-- **The sharp summand carries the sum** past any strictly deeper one. -/
theorem Sharp.add_deep {i j : ℤ} {q r : ℚ} (hq : Sharp i q) (hr : Deep j r) (hij : i < j) :
    Sharp i (q + r) := by
  rcases hr with hr0 | hr
  · rwa [hr0, add_zero]
  by_cases hr0 : r = 0
  · rwa [hr0, add_zero]
  have hqr : q + r ≠ 0 := by
    intro h0
    have hqe : q = -r := eq_neg_of_add_eq_zero_left h0
    have hveq : padicValRat 3 r = i := by
      have hv := hq.2
      rw [hqe, padicValRat.neg] at hv
      exact hv
    omega
  refine ⟨hqr, ?_⟩
  have hlow : padicValRat 3 q ≤ padicValRat 3 (q + r) :=
    padicValRat.le_padicValRat_add_of_le hqr (by rw [hq.2]; exact le_trans hij.le hr)
  have hhigh : padicValRat 3 (q + r) ≤ i := by
    have h1 : min (padicValRat 3 (q + r)) (padicValRat 3 (-r))
        ≤ padicValRat 3 ((q + r) + -r) :=
      padicValRat.min_le_padicValRat_add (by rw [add_neg_cancel_right]; exact hq.1)
    rw [add_neg_cancel_right, hq.2, padicValRat.neg] at h1
    rcases min_le_iff.mp h1 with h2 | h2
    · exact h2
    · omega
  have hlow' := hq.2 ▸ hlow
  omega

/-- A sharp value refuses any strictly greater depth. -/
theorem Sharp.not_deep {j : ℤ} {q : ℚ} (h : Sharp j q) : ¬ Deep (j + 1) q := by
  rintro (h0 | hd)
  · exact h.1 h0
  · have := h.2
    omega

theorem Deep.div_sharp {j : ℤ} {q u : ℚ} (hq : Deep j q) (hu : Sharp 0 u) :
    Deep j (q / u) := by
  rw [div_eq_mul_inv]
  have h := hq.mul hu.inv.deep
  simpa using h

/-- An integer with no factor of three is sharp at depth zero. -/
theorem sharp_int {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) : Sharp 0 ((n : ℚ)) := by
  have hn : n ≠ 0 := by rintro rfl; exact h ⟨0, by ring⟩
  refine ⟨Int.cast_ne_zero.mpr hn, ?_⟩
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (by exact_mod_cast h)]
  rfl

/-- One plus anything of depth one is sharp at depth zero. -/
theorem one_add_deep {q : ℚ} (h : Deep 1 q) : Sharp 0 (1 + q) := by
  have h1 : Sharp 0 (1 : ℚ) := by
    have := sharp_int (n := 1) (by norm_num)
    simpa using this
  exact h1.add_deep h (by norm_num)

/-- An integer divisible by three is deep. -/
theorem deep_int_of_dvd {n : ℤ} (h : (3 : ℤ) ∣ n) : Deep 1 ((n : ℚ)) := by
  by_cases hn : n = 0
  · rw [hn]
    exact_mod_cast deep_zero 1
  refine Or.inr ?_
  rw [padicValRat.of_int]
  have h1 := (padicValInt_dvd_iff (p := 3) 1 n).mp (by simpa using h)
  rcases h1 with h0 | h1
  · exact absurd h0 hn
  · exact_mod_cast h1

/-! ## 2. The entry classification and the integral forcing -/

/-- A nonzero rational with nonnegative depth has a three-free denominator. -/
theorem den_not_dvd_of_deep {x : ℚ} (_hx : x ≠ 0) (h : 0 ≤ padicValRat 3 x) :
    ¬ (3 : ℤ) ∣ (x.den : ℤ) := by
  intro hdvd
  have hnum : ¬ (3 : ℤ) ∣ x.num := by
    intro hnd
    have hcop := x.reduced
    have h3 : (3 : ℕ) ∣ Nat.gcd x.num.natAbs x.den := by
      refine Nat.dvd_gcd ?_ ?_
      · have := Int.natAbs_dvd_natAbs.mpr hnd
        simpa using this
      · exact_mod_cast hdvd
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    norm_num at h3
  have hv : padicValRat 3 x = padicValInt 3 x.num - padicValNat 3 x.den :=
    padicValRat_def 3 x
  rw [padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hnum)] at hv
  have hden : 1 ≤ padicValNat 3 x.den := by
    have h3d : (3 : ℕ) ∣ x.den := by exact_mod_cast hdvd
    exact one_le_padicValNat_of_dvd x.den_nz h3d
  omega

/-- **The Fermat cube is deep**: for a three-integral rational, `x³ − x` has depth one. -/
theorem theFermatCubeIsDeep {x : ℚ} (hx : x ≠ 0) (h : 0 ≤ padicValRat 3 x) :
    Deep 1 (x ^ 3 - x) := by
  by_cases h0 : x ^ 3 - x = 0
  · rw [h0]; exact deep_zero 1
  have hden := den_not_dvd_of_deep hx h
  set a : ℤ := x.num with ha
  set b : ℤ := (x.den : ℤ) with hb
  have hb0 : b ≠ 0 := by
    rw [hb]
    exact_mod_cast x.den_nz
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hxab : x = (a : ℚ) / (b : ℚ) := by
    rw [ha, hb]
    push_cast
    exact (Rat.num_div_den x).symm
  have hform : x ^ 3 - x = ((a ^ 3 - a * b ^ 2 : ℤ) : ℚ) / ((b ^ 3 : ℤ) : ℚ) := by
    rw [hxab]
    push_cast
    field_simp
  have hdvd : (3 : ℤ) ∣ (a ^ 3 - a * b ^ 2) := by
    have hbz : ((b : ZMod 3)) ≠ 0 := by
      intro hz
      exact hden ((ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hz)
    have hbsq : (b : ZMod 3) ^ 2 = 1 := by
      have hall : ∀ c : ZMod 3, c ≠ 0 → c ^ 2 = 1 := by decide
      exact hall _ hbz
    have hacube : (a : ZMod 3) ^ 3 = (a : ZMod 3) := by
      have hall : ∀ c : ZMod 3, c ^ 3 = c := by decide
      exact hall _
    have hcast : ((a ^ 3 - a * b ^ 2 : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [hbsq, hacube]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hcast
  rw [hform]
  have hnum : Deep 1 ((a ^ 3 - a * b ^ 2 : ℤ) : ℚ) := deep_int_of_dvd hdvd
  have hden3 : Sharp 0 ((b ^ 3 : ℤ) : ℚ) := by
    refine sharp_int ?_
    intro hd
    exact hden ((by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow hd)
  exact hnum.div_sharp hden3

/-- **The integral ordinate is divisible**: on the curve, a three-integral abscissa forces
ordinate depth at least one — the frame at three is pure half-turns. -/
theorem theIntegralOrdinateIsDivisible {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) (hx : x ≠ 0) (hxv : 0 ≤ padicValRat 3 x) : 1 ≤ padicValRat 3 y := by
  have hsplit : y ^ 2 = (x ^ 3 - x) + (-24 : ℚ) * x := by linarith [hcurve]
  have h24 : Deep 1 ((-24 : ℚ) * x) := by
    have h24' : Deep 1 (((-24 : ℤ) : ℚ)) := deep_int_of_dvd (by norm_num)
    have hx0 : Deep 0 x := Or.inr hxv
    have hmul := h24'.mul hx0
    have hcast : ((-24 : ℤ) : ℚ) = (-24 : ℚ) := by norm_num
    rw [hcast] at hmul
    simpa using hmul
  have hdeep : Deep 1 (y ^ 2) := by
    rw [hsplit]
    exact (theFermatCubeIsDeep hx hxv).add h24
  rcases hdeep with h0 | hd
  · exact absurd (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0) hy
  · rw [padicValRat.pow] at hd
    omega

/-- **The kernel level is classified**: negative abscissa depth on the curve comes in exact
levels — `Sharp (−2k) x` and `Sharp (−3k) y` for one `k ≥ 1`. -/
theorem theKernelLevelIsClassified {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 25 * x)
    (hy : y ≠ 0) (hx : x ≠ 0) (hneg : padicValRat 3 x < 0) :
    ∃ k : ℕ, 1 ≤ k ∧ Sharp (-(2 * (k : ℤ))) x ∧ Sharp (-(3 * (k : ℤ))) y := by
  set w : ℤ := padicValRat 3 x with hw
  have hx3 : Sharp (3 * w) (x ^ 3) := by
    refine ⟨pow_ne_zero 3 hx, ?_⟩
    rw [padicValRat.pow, ← hw]
    push_cast
    ring
  have h25x : Sharp w ((-25 : ℚ) * x) := by
    have h25 : Sharp 0 (((-25 : ℤ) : ℚ)) := sharp_int (by norm_num)
    have hxs : Sharp w x := ⟨hx, hw.symm⟩
    have hmul := h25.mul hxs
    have hcast : ((-25 : ℤ) : ℚ) = (-25 : ℚ) := by norm_num
    rw [hcast] at hmul
    simpa using hmul
  have hrhs : Sharp (3 * w) (x ^ 3 - 25 * x) := by
    have h1 := hx3.add_deep h25x.deep (by omega)
    have heq : x ^ 3 + (-25 : ℚ) * x = x ^ 3 - 25 * x := by ring
    rwa [heq] at h1
  have hy2 : 2 * padicValRat 3 y = 3 * w := by
    have hyv : padicValRat 3 (y ^ 2) = 3 * w := by
      rw [hcurve]
      exact hrhs.2
    rw [padicValRat.pow] at hyv
    push_cast at hyv
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w = 2 * m := ⟨padicValRat 3 y - w, by omega⟩
  have hyv : padicValRat 3 y = 3 * m := by omega
  have hmneg : m < 0 := by omega
  refine ⟨(-m).toNat, by omega, ⟨hx, ?_⟩, ⟨hy, ?_⟩⟩
  · rw [← hw]
    omega
  · rw [hyv]
    omega

/-! ## 3. The transport chart and its identities -/

/-- **The chart equation**: on the curve, `s = t³ − 25ts²` for `t = x/y`, `s = 1/y` — the
identity is the origin of this chart. -/
theorem theChartEquation {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - 25 * x) (hy : y ≠ 0) :
    (1 : ℚ) / y = (x / y) ^ 3 - 25 * (x / y) * (1 / y) ^ 2 := by
  field_simp
  linear_combination hcurve

/-- **The chord slope is carried by a unit**: subtracting the two chart equations places the
slope over the denominator `1 + 25t₁(s₁ + s₂)`, which the depth calculus makes a unit. -/
theorem theChordSlopeIsCarriedByAUnit {t₁ s₁ t₂ s₂ : ℚ}
    (h₁ : s₁ = t₁ ^ 3 - 25 * t₁ * s₁ ^ 2) (h₂ : s₂ = t₂ ^ 3 - 25 * t₂ * s₂ ^ 2) :
    (s₂ - s₁) * (1 + 25 * t₁ * (s₁ + s₂))
      = (t₂ - t₁) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 25 * s₂ ^ 2) := by
  linear_combination h₂ - h₁

/-- **The tangent line has a double root** at its point of tangency: pure algebra from the
tangent slope's defining equation. -/
theorem theTangentLineHasADoubleRoot {t₁ s₁ α : ℚ}
    (hα : α * (1 + 50 * t₁ * s₁) = 3 * t₁ ^ 2 - 25 * s₁ ^ 2) :
    3 * (1 - 25 * α ^ 2) * t₁ ^ 2 - 100 * α * (s₁ - α * t₁) * t₁
      - 25 * (s₁ - α * t₁) ^ 2 - α = 0 := by
  linear_combination -hα

/-- A chart point on a line satisfies the cubic that line cuts from the chart. -/
theorem theLineCutsTheCubic {t s α β : ℚ}
    (hchart : s = t ^ 3 - 25 * t * s ^ 2) (hline : s = α * t + β) :
    (1 - 25 * α ^ 2) * t ^ 3 - 50 * α * β * t ^ 2 - (25 * β ^ 2 + α) * t - β = 0 := by
  rw [hline] at hchart
  linear_combination -hchart

/-- The cubic's difference quotient, as pure algebra. -/
theorem theCubicDifferenceFactors (α β a b : ℚ) :
    ((1 - 25 * α ^ 2) * a ^ 3 - 50 * α * β * a ^ 2 - (25 * β ^ 2 + α) * a - β)
      - ((1 - 25 * α ^ 2) * b ^ 3 - 50 * α * β * b ^ 2 - (25 * β ^ 2 + α) * b - β)
      = (a - b) * ((1 - 25 * α ^ 2) * (a ^ 2 + a * b + b ^ 2) - 50 * α * β * (a + b)
          - (25 * β ^ 2 + α)) := by
  ring

/-- The difference quotient's own difference, as pure algebra. -/
theorem theQuotientDifferenceFactors (α β a b c : ℚ) :
    ((1 - 25 * α ^ 2) * (a ^ 2 + a * b + b ^ 2) - 50 * α * β * (a + b) - (25 * β ^ 2 + α))
      - ((1 - 25 * α ^ 2) * (a ^ 2 + a * c + c ^ 2) - 50 * α * β * (a + c)
          - (25 * β ^ 2 + α))
      = (b - c) * ((1 - 25 * α ^ 2) * (a + b + c) - 50 * α * β) := by
  ring

/-- **The chord cuts the sum formula**: three distinct roots of the line's cubic satisfy
`(1 − 25α²)(t₁ + t₂ + u) = 50αβ`. -/
theorem theChordCutsTheSumFormula {α β t₁ t₂ u : ℚ}
    (hP₁ : (1 - 25 * α ^ 2) * t₁ ^ 3 - 50 * α * β * t₁ ^ 2 - (25 * β ^ 2 + α) * t₁ - β = 0)
    (hP₂ : (1 - 25 * α ^ 2) * t₂ ^ 3 - 50 * α * β * t₂ ^ 2 - (25 * β ^ 2 + α) * t₂ - β = 0)
    (hPu : (1 - 25 * α ^ 2) * u ^ 3 - 50 * α * β * u ^ 2 - (25 * β ^ 2 + α) * u - β = 0)
    (h12 : t₁ ≠ t₂) (hu1 : u ≠ t₁) (hu2 : u ≠ t₂) :
    (1 - 25 * α ^ 2) * (t₁ + t₂ + u) = 50 * α * β := by
  have hQ1 : (1 - 25 * α ^ 2) * (u ^ 2 + u * t₁ + t₁ ^ 2) - 50 * α * β * (u + t₁)
      - (25 * β ^ 2 + α) = 0 := by
    have hfac := theCubicDifferenceFactors α β u t₁
    rw [hPu, hP₁, sub_zero] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left (sub_ne_zero.mpr hu1)
  have hQ2 : (1 - 25 * α ^ 2) * (u ^ 2 + u * t₂ + t₂ ^ 2) - 50 * α * β * (u + t₂)
      - (25 * β ^ 2 + α) = 0 := by
    have hfac := theCubicDifferenceFactors α β u t₂
    rw [hPu, hP₂, sub_zero] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left (sub_ne_zero.mpr hu2)
  have hfin := theQuotientDifferenceFactors α β u t₁ t₂
  rw [hQ1, hQ2, sub_zero] at hfin
  have hz := (mul_eq_zero.mp hfin.symm).resolve_left (sub_ne_zero.mpr h12)
  linear_combination hz

/-- **The tangent cuts the sum formula**: with the double root at the tangency, a distinct
third root satisfies `(1 − 25α²)(2t₁ + u) = 50αβ`. -/
theorem theTangentCutsTheSumFormula {α β t₁ s₁ u : ℚ}
    (hβ : β = s₁ - α * t₁)
    (hα : α * (1 + 50 * t₁ * s₁) = 3 * t₁ ^ 2 - 25 * s₁ ^ 2)
    (hP₁ : (1 - 25 * α ^ 2) * t₁ ^ 3 - 50 * α * β * t₁ ^ 2 - (25 * β ^ 2 + α) * t₁ - β = 0)
    (hPu : (1 - 25 * α ^ 2) * u ^ 3 - 50 * α * β * u ^ 2 - (25 * β ^ 2 + α) * u - β = 0)
    (hu1 : u ≠ t₁) :
    (1 - 25 * α ^ 2) * (2 * t₁ + u) = 50 * α * β := by
  have hQ1 : (1 - 25 * α ^ 2) * (t₁ ^ 2 + t₁ * u + u ^ 2) - 50 * α * β * (t₁ + u)
      - (25 * β ^ 2 + α) = 0 := by
    have hfac := theCubicDifferenceFactors α β u t₁
    rw [hPu, hP₁, sub_zero] at hfac
    have hz := (mul_eq_zero.mp hfac.symm).resolve_left (sub_ne_zero.mpr hu1)
    linear_combination hz
  have hdr := theTangentLineHasADoubleRoot hα
  rw [← hβ] at hdr
  have hQ11 : (1 - 25 * α ^ 2) * (t₁ ^ 2 + t₁ * t₁ + t₁ ^ 2) - 50 * α * β * (t₁ + t₁)
      - (25 * β ^ 2 + α) = 0 := by
    linear_combination hdr
  have hfin := theQuotientDifferenceFactors α β t₁ u t₁
  rw [hQ1, hQ11, sub_zero] at hfin
  have hz := (mul_eq_zero.mp hfin.symm).resolve_left (sub_ne_zero.mpr hu1)
  linear_combination hz

end Soma.Holonics.Millennium.FrameDescent
