import ElementaryHolonics.Millennium.FrameDescent
import ElementaryHolonics.Millennium.WindingCensus
import Mathlib.Tactic

/-!
# DistantWindings: the kernel refuses the distant prime windings, and the census closes

The point layer of the compact-frame instrument, spending `FrameDescent.lean`'s depth calculus
and chart identities on mathlib's actual group law for `y² = x³ − 25x`.

The argument, per point of prime order `p ≥ 5`: its odd order keeps every multiple affine with
nonzero ordinate; if the point is three-integral the frame at three is pure half-turns, so its
ordinate is deep and its double sinks into the kernel; so some multiple sits at an exact kernel
level `K ≥ 1`.  Walking the cyclic subgroup, each addition either returns a transport
coordinate one level deeper than the sum of its addends' — the first-order law of the kernel —
or lands on a negation of an addend, a coincidence the group order converts into a doubling
whose estimate contradicts the exact level.  At the last step the walk closes,
`(p−1)•R = −R`, and the accumulated congruence `t((p−1)•R) ≡ (p−1)·t(R)` forces
`p·t(R)` a level deeper than the exact level the entry classification gave it.  No such point
exists (`theDistantPrimeWindingsNeverCloseHolds`), so `WindingCensus`'s reduction discharges
`RankOne.TheTorsionIsTheKleinGroup` (`theTorsionIsTheKleinGroupHolds`), and with the chain
already proved off the torsion table, `RankOne.ThePointHasInfiniteOrder`
(`thePointHasInfiniteOrderHolds`): **the torsion of `y² = x³ − 25x` is exactly the Klein
four-group, and the point `(−4, 6)` has infinite order — the census closed and the chain
certified.**  (The splitting `E(ℚ) ≅ T ⊕ ℤʳ` needs finite generation — the Mordell–Weil
theorem, which has no mathlib owner and is not claimed here.)

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: one curve, one
prime frame; nothing about general curves, nothing about ranks beyond the certified chain, and
nothing about the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.DistantWindings

open WeierstrassCurve.Affine
open RankOne (E5)
open FrameDescent

/-! A small explicit constructor for the 4.33 point API.  Keeping the
coordinate and nonsingularity proof together makes the carrier equality
independent of proof-term elaboration. -/
private abbrev pointOf {x y : ℚ} (h : E5.Nonsingular x y) : E5.Point :=
  Point.some x y h

/-! ## 1. Coordinate faces and small instruments -/

private def abscissa : E5.Point → ℚ
  | .zero => 0
  | .some x _ _ => x

private def ordinate : E5.Point → ℚ
  | .zero => 0
  | .some _ y _ => y

private lemma some_eq_some {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : E5.Nonsingular x₁ y₁} {h₂ : E5.Nonsingular x₂ y₂} :
    (Point.some x₁ y₁ h₁ : E5.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

private lemma negY_eq (x y : ℚ) : E5.negY x y = -y := by
  simp [negY, RankOne.E5]

private lemma curve_eq {x y : ℚ} (h : E5.Nonsingular x y) : y ^ 2 = x ^ 3 - 25 * x := by
  have h1 := ((nonsingular_iff x y).mp h).1
  rw [equation_iff] at h1
  simp only [RankOne.E5] at h1
  linarith [h1]

/-- A nonzero ordinate keeps the abscissa off zero: `(0, y)` is on the curve only at `y = 0`. -/
private lemma x_ne_zero {x y : ℚ} (h : E5.Nonsingular x y) (hy : y ≠ 0) : x ≠ 0 := by
  intro hx0
  have hc := curve_eq h
  rw [hx0] at hc
  norm_num at hc
  exact hy hc

/-! ## 2. The chord estimate -/

/-- **The chord estimate.**  Adding two kernel-deep points along a chord either lands on the
negation of an addend — the coincidence the group order will refuse — or returns a transport
coordinate one level deeper than the sum of the addends', with the new point still deep. -/
private lemma chord_estimate {K : ℕ} (hK : 1 ≤ K)
    {x₁ y₁ x₂ y₂ x₃ y₃ : ℚ}
    {h₁ : E5.Nonsingular x₁ y₁} {h₂ : E5.Nonsingular x₂ y₂} {h₃ : E5.Nonsingular x₃ y₃}
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (hx : x₁ ≠ x₂)
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃)
    (ht₁ : Deep (K : ℤ) (x₁ / y₁)) (hs₁ : Deep (3 * (K : ℤ)) (1 / y₁))
    (ht₂ : Deep (K : ℤ) (x₂ / y₂)) (hs₂ : Deep (3 * (K : ℤ)) (1 / y₂)) :
    Point.some x₃ y₃ h₃ = -Point.some x₁ y₁ h₁ ∨ Point.some x₃ y₃ h₃ = -Point.some x₂ y₂ h₂ ∨
      (Deep ((K : ℤ) + 1) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) ∧
        Deep (K : ℤ) (x₃ / y₃) ∧ Deep (3 * (K : ℤ)) (1 / y₃)) := by
  have hK1 : (1 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
  -- the concrete sum coordinates
  have hslopedef : E5.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := slope_of_X_ne hx
  rw [Point.add_of_X_ne hx] at hsum
  have habs := congrArg abscissa hsum
  have hordi := congrArg ordinate hsum
  simp only [abscissa, ordinate] at habs hordi
  set lam : ℚ := (y₁ - y₂) / (x₁ - x₂) with hlam
  have hx₃ : x₃ = lam ^ 2 - x₁ - x₂ := by
    rw [← habs, hslopedef]
    simp [addX, RankOne.E5]
  have hy₃c : y₃ = -(lam * (x₃ - x₁) + y₁) := by
    have hxx : E5.addX x₁ x₂ lam = x₃ := by rw [← hslopedef]; exact habs
    rw [← hordi, addY, negAddY, negY_eq, hslopedef, hxx]
  -- the transport chart
  set t₁ : ℚ := x₁ / y₁ with htd₁
  set s₁ : ℚ := 1 / y₁ with hsd₁
  set t₂ : ℚ := x₂ / y₂ with htd₂
  set s₂ : ℚ := 1 / y₂ with hsd₂
  have hc₁ := curve_eq h₁
  have hc₂ := curve_eq h₂
  have hc₃ := curve_eq h₃
  have hF₁ : s₁ = t₁ ^ 3 - 25 * t₁ * s₁ ^ 2 := theChartEquation hc₁ hy₁
  have hF₂ : s₂ = t₂ ^ 3 - 25 * t₂ * s₂ ^ 2 := theChartEquation hc₂ hy₂
  -- the transport-line slope over its unit denominator
  set D : ℚ := 1 + 25 * t₁ * (s₁ + s₂) with hDdef
  have hDsharp : Sharp 0 D := by
    apply one_add_deep
    have h25 : Deep 0 (25 : ℚ) := (sharp_int (n := 25) (by norm_num)).deep |>.mono le_rfl
      |>.mono (by norm_num)
    have hss : Deep (3 * (K : ℤ)) (s₁ + s₂) := hs₁.add hs₂
    have := (h25.mul ht₁).mul hss
    exact this.mono (by omega)
  set α : ℚ := (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 25 * s₂ ^ 2) / D with hαdef
  set β : ℚ := s₁ - α * t₁ with hβdef
  have hαD : α * D = t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 25 * s₂ ^ 2 :=
    div_mul_cancel₀ _ hDsharp.1
  have hslope := theChordSlopeIsCarriedByAUnit hF₁ hF₂
  have hαslope : α * (t₂ - t₁) = s₂ - s₁ := by
    have h1 : α * (t₂ - t₁) * D = (s₂ - s₁) * D := by
      calc α * (t₂ - t₁) * D = (t₂ - t₁) * (α * D) := by ring
      _ = (t₂ - t₁) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 25 * s₂ ^ 2) := by rw [hαD]
      _ = (s₂ - s₁) * (1 + 25 * t₁ * (s₁ + s₂)) := hslope.symm
      _ = (s₂ - s₁) * D := by rw [hDdef]
    exact mul_right_cancel₀ hDsharp.1 h1
  have hline₁ : s₁ = α * t₁ + β := by rw [hβdef]; ring
  have hline₂ : s₂ = α * t₂ + β := by
    have := hαslope
    rw [hβdef]
    linarith [this]
  -- transport-line membership in cleared xy-form
  have hl₁ : α * x₁ + β * y₁ = 1 := by
    have h := hline₁
    rw [htd₁, hsd₁] at h
    field_simp at h
    linarith [h]
  have hl₂ : α * x₂ + β * y₂ = 1 := by
    have h := hline₂
    rw [htd₂, hsd₂] at h
    field_simp at h
    linarith [h]
  -- the third intersection (x₃, −y₃) is on the transport line
  have hthird : α * x₃ - β * y₃ = 1 := by
    have hy3 : -y₃ = lam * (x₃ - x₁) + y₁ := by rw [hy₃c]; ring
    have hxne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hlamc : lam * (x₁ - x₂) = y₁ - y₂ := by
      rw [hlam]
      field_simp
    have : α * x₃ + β * (lam * (x₃ - x₁) + y₁) = 1 := by
      have h1 : (α * x₃ + β * (lam * (x₃ - x₁) + y₁)) * (x₁ - x₂) = 1 * (x₁ - x₂) := by
        linear_combination (x₃ - x₂) * hl₁ - (x₃ - x₁) * hl₂ + β * (x₃ - x₁) * hlamc
      exact mul_right_cancel₀ hxne h1
    calc α * x₃ - β * y₃ = α * x₃ + β * (-y₃) := by ring
    _ = α * x₃ + β * (lam * (x₃ - x₁) + y₁) := by rw [hy3]
    _ = 1 := this
  -- chart membership of the third intersection
  set u : ℚ := x₃ / -y₃ with hudef
  set su : ℚ := 1 / -y₃ with hsudef
  have hy₃n : (-y₃ : ℚ) ≠ 0 := neg_ne_zero.mpr hy₃
  have hFu : su = u ^ 3 - 25 * u * su ^ 2 := by
    have hcneg : (-y₃) ^ 2 = x₃ ^ 3 - 25 * x₃ := by rw [neg_pow]; simpa using hc₃
    exact theChartEquation hcneg hy₃n
  have hlineu : su = α * u + β := by
    have hu' : u * (-y₃) = x₃ := by rw [hudef]; field_simp
    have hsu' : su * (-y₃) = 1 := by rw [hsudef]; field_simp
    have h1 : su * (-y₃) = (α * u + β) * (-y₃) := by
      rw [hsu']
      calc (1 : ℚ) = α * x₃ - β * y₃ := hthird.symm
      _ = (α * u + β) * (-y₃) := by rw [← hu']; ring
    exact mul_right_cancel₀ hy₃n h1
  -- the cubic facts
  have hP₁ := theLineCutsTheCubic hF₁ hline₁
  have hP₂ := theLineCutsTheCubic hF₂ hline₂
  have hPu := theLineCutsTheCubic hFu hlineu
  -- the addends' transports are separated
  have ht₁₂ : t₁ ≠ t₂ := by
    intro he
    have h0 : s₂ - s₁ = 0 := by
      have := hαslope
      rw [he] at this
      simpa using this.symm
    have hy12 : y₁ = y₂ := by
      have hs : s₁ = s₂ := by linarith [h0]
      rw [hsd₁, hsd₂] at hs
      field_simp at hs
      linarith [hs]
    have hx12 : x₁ = x₂ := by
      have ht : t₁ = t₂ := he
      rw [htd₁, htd₂, hy12] at ht
      field_simp at ht
      linarith [ht]
    exact hx hx12
  -- the case split on the third root
  by_cases hu₁ : u = t₁
  · -- the third intersection is the first addend: the sum is its negation
    left
    have hsu₁ : su = s₁ := by rw [hlineu, hu₁, ← hline₁]
    have hyy : -y₃ = y₁ := by
      have h := hsu₁
      rw [hsudef, hsd₁] at h
      field_simp at h
      linarith [h]
    have hxx : x₃ = x₁ := by
      have h := hu₁
      rw [hudef, htd₁, hyy] at h
      field_simp at h
      linarith [h]
    rw [Point.neg_some]
    exact some_eq_some hxx (by rw [negY_eq]; linarith [hyy])
  by_cases hu₂ : u = t₂
  · right; left
    have hsu₂ : su = s₂ := by rw [hlineu, hu₂, ← hline₂]
    have hyy : -y₃ = y₂ := by
      have h := hsu₂
      rw [hsudef, hsd₂] at h
      field_simp at h
      linarith [h]
    have hxx : x₃ = x₂ := by
      have h := hu₂
      rw [hudef, htd₂, hyy] at h
      field_simp at h
      linarith [h]
    rw [Point.neg_some]
    exact some_eq_some hxx (by rw [negY_eq]; linarith [hyy])
  -- the generic case: the sum formula and the depth propagation
  right; right
  have hsumf := theChordCutsTheSumFormula hP₁ hP₂ hPu ht₁₂ hu₁ hu₂
  have hαdeep : Deep (2 * (K : ℤ)) α := by
    have hN : Deep (2 * (K : ℤ)) (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 - 25 * s₂ ^ 2) := by
      have h11 : Deep (2 * (K : ℤ)) (t₁ ^ 2) := by
        have := ht₁.mul ht₁
        rw [← pow_two] at this
        convert this using 1
        ring
      have h12 : Deep (2 * (K : ℤ)) (t₁ * t₂) := by
        have := ht₁.mul ht₂
        convert this using 1
        ring
      have h22 : Deep (2 * (K : ℤ)) (t₂ ^ 2) := by
        have := ht₂.mul ht₂
        rw [← pow_two] at this
        convert this using 1
        ring
      have h25 : Deep (2 * (K : ℤ)) (-(25 * s₂ ^ 2)) := by
        have hd25 : Deep 0 (25 : ℚ) := (sharp_int (n := 25) (by norm_num)).deep
        have hss : Deep (6 * (K : ℤ)) (s₂ ^ 2) := by
          have := hs₂.mul hs₂
          rw [← pow_two] at this
          convert this using 1
          ring
        have := (hd25.mul hss).neg
        exact this.mono (by omega)
      have hsum4 := ((h11.add h12).add h22).add h25
      convert hsum4 using 1
      ring
    exact hN.div_sharp hDsharp
  have hβdeep : Deep (3 * (K : ℤ)) β := by
    rw [hβdef]
    have hαt : Deep (3 * (K : ℤ)) (-(α * t₁)) := by
      have := (hαdeep.mul ht₁).neg
      exact this.mono (by omega)
    have := hs₁.add hαt
    convert this using 1
    ring
  have hunit : Sharp 0 (1 - 25 * α ^ 2) := by
    have h25 : Deep 0 (-25 : ℚ) := (sharp_int (n := -25) (by norm_num)).deep
    have hαα : Deep (4 * (K : ℤ)) (α ^ 2) := by
      have := hαdeep.mul hαdeep
      rw [← pow_two] at this
      convert this using 1
      ring
    have hq : Deep 1 (-25 * α ^ 2) := (h25.mul hαα).mono (by omega)
    have := one_add_deep hq
    convert this using 1
    ring
  have hrhs : Deep (5 * (K : ℤ)) (50 * α * β) := by
    have h50 : Deep 0 (50 : ℚ) := (sharp_int (n := 50) (by norm_num)).deep
    have := (h50.mul hαdeep).mul hβdeep
    exact this.mono (by omega)
  have hsumdeep : Deep (5 * (K : ℤ)) (t₁ + t₂ + u) := by
    have hdiv : t₁ + t₂ + u = 50 * α * β / (1 - 25 * α ^ 2) := by
      rw [eq_div_iff hunit.1]
      linear_combination hsumf
    rw [hdiv]
    exact hrhs.div_sharp hunit
  have hudeep : Deep (K : ℤ) u := by
    have h1 : u = (t₁ + t₂ + u) + (-t₁) + (-t₂) := by ring
    rw [h1]
    exact ((hsumdeep.mono (by omega)).add ht₁.neg).add ht₂.neg
  have ht₃ : x₃ / y₃ = -u := by
    rw [hudef]
    field_simp
  have hs₃ : 1 / y₃ = -su := by
    rw [hsudef]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · have hdd : Deep ((K : ℤ) + 1) (-(t₁ + t₂ + u)) := (hsumdeep.mono (by omega)).neg
    rw [ht₃]
    convert hdd using 1
    ring
  · rw [ht₃]
    exact hudeep.neg
  · rw [hs₃]
    have hsu' : Deep (3 * (K : ℤ)) su := by
      rw [hlineu]
      have hαu : Deep (3 * (K : ℤ)) (α * u) := (hαdeep.mul hudeep).mono (by omega)
      exact hαu.add hβdeep
    exact hsu'.neg

/-! ## 3. The tangent estimate -/

/-- **The tangent estimate.**  Doubling a kernel-deep point either lands on its own negation —
the coincidence the group order refuses through the third winding — or returns a transport
coordinate one level deeper than twice the point's, with the double still deep. -/
private lemma tangent_estimate {K : ℕ} (hK : 1 ≤ K)
    {x₁ y₁ x₃ y₃ : ℚ}
    {h₁ : E5.Nonsingular x₁ y₁} {h₃ : E5.Nonsingular x₃ y₃}
    (hy₁ : y₁ ≠ 0) (hy₃ : y₃ ≠ 0)
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = Point.some x₃ y₃ h₃)
    (ht₁ : Deep (K : ℤ) (x₁ / y₁)) (hs₁ : Deep (3 * (K : ℤ)) (1 / y₁)) :
    Point.some x₃ y₃ h₃ = -Point.some x₁ y₁ h₁ ∨
      (Deep ((K : ℤ) + 1) (x₃ / y₃ - 2 * (x₁ / y₁)) ∧
        Deep (K : ℤ) (x₃ / y₃) ∧ Deep (3 * (K : ℤ)) (1 / y₃)) := by
  have hK1 : (1 : ℤ) ≤ (K : ℤ) := by exact_mod_cast hK
  have hyneg : y₁ ≠ E5.negY x₁ y₁ := by
    rw [negY_eq]
    intro h
    exact hy₁ (by linarith)
  set lam : ℚ := (3 * x₁ ^ 2 - 25) / (2 * y₁) with hlam
  have hslopedef : E5.slope x₁ x₁ y₁ y₁ = lam := by
    rw [slope_of_Y_ne rfl hyneg, negY_eq, hlam]
    simp only [RankOne.E5]
    ring_nf
  rw [Point.add_self_of_Y_ne hyneg] at hsum
  have habs := congrArg abscissa hsum
  have hordi := congrArg ordinate hsum
  simp only [abscissa, ordinate] at habs hordi
  have hx₃ : x₃ = lam ^ 2 - x₁ - x₁ := by
    rw [← habs, hslopedef]
    simp [addX, RankOne.E5]
  have hy₃c : y₃ = -(lam * (x₃ - x₁) + y₁) := by
    have hxx : E5.addX x₁ x₁ lam = x₃ := by rw [← hslopedef]; exact habs
    rw [← hordi, addY, negAddY, negY_eq, hslopedef, hxx]
  -- the transport chart
  set t₁ : ℚ := x₁ / y₁ with htd₁
  set s₁ : ℚ := 1 / y₁ with hsd₁
  have hc₁ := curve_eq h₁
  have hc₃ := curve_eq h₃
  have hF₁ : s₁ = t₁ ^ 3 - 25 * t₁ * s₁ ^ 2 := theChartEquation hc₁ hy₁
  -- the tangent slope over its unit denominator
  set D : ℚ := 1 + 50 * t₁ * s₁ with hDdef
  have hDsharp : Sharp 0 D := by
    apply one_add_deep
    have h50 : Deep 0 (50 : ℚ) := (sharp_int (n := 50) (by norm_num)).deep
    have := (h50.mul ht₁).mul hs₁
    exact this.mono (by omega)
  set α : ℚ := (3 * t₁ ^ 2 - 25 * s₁ ^ 2) / D with hαdef
  set β : ℚ := s₁ - α * t₁ with hβdef
  have hαD : α * D = 3 * t₁ ^ 2 - 25 * s₁ ^ 2 := div_mul_cancel₀ _ hDsharp.1
  have hαt : α * (1 + 50 * t₁ * s₁) = 3 * t₁ ^ 2 - 25 * s₁ ^ 2 := by
    rw [← hDdef]; exact hαD
  have hline₁ : s₁ = α * t₁ + β := by rw [hβdef]; ring
  have hl₁ : α * x₁ + β * y₁ = 1 := by
    have h := hline₁
    rw [htd₁, hsd₁] at h
    field_simp at h
    linarith [h]
  -- the transport slope annihilates the coordinate slope
  have hkey : (3 * t₁ ^ 2 - 25 * s₁ ^ 2) * (1 - t₁ * lam) + s₁ * lam * (1 + 50 * t₁ * s₁)
      = 0 := by
    rw [htd₁, hsd₁, hlam]
    field_simp
    linear_combination (9 * x₁ ^ 2 - 75) * hc₁
  have hαβlam : α + β * lam = 0 := by
    have h1 : (α + β * lam) * D = 0 := by
      have hexp : (α + β * lam) * D = (α * D) * (1 - t₁ * lam) + s₁ * lam * D := by
        rw [hβdef]; ring
      rw [hexp, hαD, hDdef]
      linear_combination hkey
    exact (mul_eq_zero.mp h1).resolve_right hDsharp.1
  -- the third intersection (x₃, −y₃) is on the transport line
  have hthird : α * x₃ - β * y₃ = 1 := by
    have hy3 : -y₃ = lam * (x₃ - x₁) + y₁ := by rw [hy₃c]; ring
    calc α * x₃ - β * y₃ = α * x₃ + β * (-y₃) := by ring
    _ = α * x₃ + β * (lam * (x₃ - x₁) + y₁) := by rw [hy3]
    _ = (α * x₁ + β * y₁) + (x₃ - x₁) * (α + β * lam) := by ring
    _ = 1 + (x₃ - x₁) * 0 := by rw [hl₁, hαβlam]
    _ = 1 := by ring
  -- chart membership of the third intersection
  set u : ℚ := x₃ / -y₃ with hudef
  set su : ℚ := 1 / -y₃ with hsudef
  have hy₃n : (-y₃ : ℚ) ≠ 0 := neg_ne_zero.mpr hy₃
  have hFu : su = u ^ 3 - 25 * u * su ^ 2 := by
    have hcneg : (-y₃) ^ 2 = x₃ ^ 3 - 25 * x₃ := by rw [neg_pow]; simpa using hc₃
    exact theChartEquation hcneg hy₃n
  have hlineu : su = α * u + β := by
    have hu' : u * (-y₃) = x₃ := by rw [hudef]; field_simp
    have hsu' : su * (-y₃) = 1 := by rw [hsudef]; field_simp
    have h1 : su * (-y₃) = (α * u + β) * (-y₃) := by
      rw [hsu']
      calc (1 : ℚ) = α * x₃ - β * y₃ := hthird.symm
      _ = (α * u + β) * (-y₃) := by rw [← hu']; ring
    exact mul_right_cancel₀ hy₃n h1
  -- the cubic facts
  have hP₁ := theLineCutsTheCubic hF₁ hline₁
  have hPu := theLineCutsTheCubic hFu hlineu
  -- the case split on the third root
  by_cases hu₁ : u = t₁
  · left
    have hsu₁ : su = s₁ := by rw [hlineu, hu₁, ← hline₁]
    have hyy : -y₃ = y₁ := by
      have h := hsu₁
      rw [hsudef, hsd₁] at h
      field_simp at h
      linarith [h]
    have hxx : x₃ = x₁ := by
      have h := hu₁
      rw [hudef, htd₁, hyy] at h
      field_simp at h
      linarith [h]
    rw [Point.neg_some]
    exact some_eq_some hxx (by rw [negY_eq]; linarith [hyy])
  right
  have hsumf := theTangentCutsTheSumFormula hβdef hαt hP₁ hPu hu₁
  have hαdeep : Deep (2 * (K : ℤ)) α := by
    have hN : Deep (2 * (K : ℤ)) (3 * t₁ ^ 2 - 25 * s₁ ^ 2) := by
      have h3t : Deep (2 * (K : ℤ)) (3 * t₁ ^ 2) := by
        have h3 : Deep 1 ((3 : ℚ)) := by
          have := deep_int_of_dvd (n := 3) (by norm_num)
          simpa using this
        have htt : Deep (2 * (K : ℤ)) (t₁ ^ 2) := by
          have := ht₁.mul ht₁
          rw [← pow_two] at this
          convert this using 1
          ring
        have := h3.mul htt
        exact this.mono (by omega)
      have h25 : Deep (2 * (K : ℤ)) (-(25 * s₁ ^ 2)) := by
        have hd25 : Deep 0 (25 : ℚ) := (sharp_int (n := 25) (by norm_num)).deep
        have hss : Deep (6 * (K : ℤ)) (s₁ ^ 2) := by
          have := hs₁.mul hs₁
          rw [← pow_two] at this
          convert this using 1
          ring
        have := (hd25.mul hss).neg
        exact this.mono (by omega)
      have := h3t.add h25
      convert this using 1
      ring
    exact hN.div_sharp hDsharp
  have hβdeep : Deep (3 * (K : ℤ)) β := by
    rw [hβdef]
    have hαt' : Deep (3 * (K : ℤ)) (-(α * t₁)) := by
      have := (hαdeep.mul ht₁).neg
      exact this.mono (by omega)
    have := hs₁.add hαt'
    convert this using 1
    ring
  have hunit : Sharp 0 (1 - 25 * α ^ 2) := by
    have h25 : Deep 0 (-25 : ℚ) := (sharp_int (n := -25) (by norm_num)).deep
    have hαα : Deep (4 * (K : ℤ)) (α ^ 2) := by
      have := hαdeep.mul hαdeep
      rw [← pow_two] at this
      convert this using 1
      ring
    have hq : Deep 1 (-25 * α ^ 2) := (h25.mul hαα).mono (by omega)
    have := one_add_deep hq
    convert this using 1
    ring
  have hrhs : Deep (5 * (K : ℤ)) (50 * α * β) := by
    have h50 : Deep 0 (50 : ℚ) := (sharp_int (n := 50) (by norm_num)).deep
    have := (h50.mul hαdeep).mul hβdeep
    exact this.mono (by omega)
  have hsumdeep : Deep (5 * (K : ℤ)) (2 * t₁ + u) := by
    have hdiv : 2 * t₁ + u = 50 * α * β / (1 - 25 * α ^ 2) := by
      rw [eq_div_iff hunit.1]
      linear_combination hsumf
    rw [hdiv]
    exact hrhs.div_sharp hunit
  have hudeep : Deep (K : ℤ) u := by
    have h1 : u = (2 * t₁ + u) + (-t₁) + (-t₁) := by ring
    rw [h1]
    exact ((hsumdeep.mono (by omega)).add ht₁.neg).add ht₁.neg
  have ht₃ : x₃ / y₃ = -u := by
    rw [hudef]
    field_simp
  have hs₃ : 1 / y₃ = -su := by
    rw [hsudef]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · have hdd : Deep ((K : ℤ) + 1) (-(2 * t₁ + u)) := (hsumdeep.mono (by omega)).neg
    rw [ht₃]
    convert hdd using 1
    ring
  · rw [ht₃]
    exact hudeep.neg
  · rw [hs₃]
    have hsu' : Deep (3 * (K : ℤ)) su := by
      rw [hlineu]
      have hαu : Deep (3 * (K : ℤ)) (α * u) := (hαdeep.mul hudeep).mono (by omega)
      exact hαu.add hβdeep
    exact hsu'.neg

/-! ## 4. The multiples stay affine, and the entry into the kernel -/

/-- Every multiple below the prime order is affine with nonzero ordinate: the odd order
refuses both the identity and the half-turns. -/
private lemma multiple_affine {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {R : E5.Point}
    (hord : addOrderOf R = p) {m : ℕ} (hm0 : 0 < m) (hmp : m < p) :
    ∃ (x y : ℚ) (h : E5.Nonsingular x y), m • R = Point.some x y h ∧ y ≠ 0 := by
  have hne : m • R ≠ 0 := by
    intro h0
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hord] at hdvd
    have := Nat.le_of_dvd hm0 hdvd
    omega
  cases hQ : m • R with
  | zero => exact absurd hQ hne
  | @some x y h =>
    refine ⟨x, y, h, rfl, ?_⟩
    intro hy0
    subst hy0
    have hhalf : pointOf h + pointOf h = 0 :=
      Point.add_self_of_Y_eq (by rw [negY_eq]; norm_num)
    have h2m : (2 * m) • R = 0 := by
      rw [Nat.mul_comm 2 m, mul_nsmul, two_nsmul, hQ]
      exact hhalf
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h2m
    rw [hord] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | hm
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd hm0 hm
      omega

/-- **Some multiple enters the kernel**: a point of prime order at least five is at an exact
kernel level, or its double is — the integral forcing of the frame at three. -/
private lemma exists_kernel_multiple {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {R : E5.Point}
    (hord : addOrderOf R = p) :
    ∃ (n : ℕ) (x y : ℚ) (h : E5.Nonsingular x y) (K : ℕ),
      0 < n ∧ n < p ∧ n • R = pointOf h ∧ 1 ≤ K ∧
      Sharp (-(2 * (K : ℤ))) x ∧ Sharp (-(3 * (K : ℤ))) y := by
  obtain ⟨x, y, h, hQ, hy⟩ := multiple_affine hp hp5 hord (m := 1) one_pos (by omega)
  have hx : x ≠ 0 := x_ne_zero h hy
  have hc := curve_eq h
  by_cases hneg : padicValRat 3 x < 0
  · obtain ⟨K, hK1, hxs, hys⟩ := theKernelLevelIsClassified hc hy hx hneg
    exact ⟨1, x, y, h, K, one_pos, by omega, hQ, hK1, hxs, hys⟩
  · push_neg at hneg
    have hyv : 1 ≤ padicValRat 3 y := theIntegralOrdinateIsDivisible hc hy hx hneg
    -- the double sinks into the kernel
    obtain ⟨x₂, y₂, h₂, hQ₂, hy₂⟩ := multiple_affine hp hp5 hord (m := 2) two_pos (by omega)
    have hyneg : y ≠ E5.negY x y := by
      rw [negY_eq]
      intro heq
      exact hy (by linarith)
    have hR1 : R = pointOf h := by
      simpa [pointOf] using (show R = Point.some x y h by rw [← hQ, one_smul])
    have hsum : pointOf h + pointOf h = pointOf h₂ := by
      simpa [pointOf] using
        (show Point.some x y h + Point.some x y h = Point.some x₂ y₂ h₂ by
          rw [← hQ₂, two_nsmul, hR1])
    set lam : ℚ := (3 * x ^ 2 - 25) / (2 * y) with hlam
    have hslopedef : E5.slope x x y y = lam := by
      rw [slope_of_Y_ne rfl hyneg, negY_eq, hlam]
      simp only [RankOne.E5]
      ring_nf
    rw [Point.add_self_of_Y_ne hyneg] at hsum
    have habs := congrArg abscissa hsum
    simp only [abscissa] at habs
    have hx₂ : x₂ = lam ^ 2 - x - x := by
      rw [← habs, hslopedef]
      simp [addX, RankOne.E5]
    -- exact depths
    set w : ℤ := padicValRat 3 y with hw
    have hys : Sharp w y := ⟨hy, hw.symm⟩
    have hnum : Sharp 0 (3 * x ^ 2 - 25) := by
      have h25 : Sharp 0 ((-25 : ℚ)) := by
        have := sharp_int (n := -25) (by norm_num)
        simpa using this
      have h3x : Deep 1 (3 * x ^ 2) := by
        have h3 : Deep 1 ((3 : ℚ)) := by
          have := deep_int_of_dvd (n := 3) (by norm_num)
          simpa using this
        have hxx : Deep 0 (x ^ 2) := by
          have hx0 : Deep 0 x := Or.inr hneg
          have := hx0.mul hx0
          rw [← pow_two] at this
          simpa using this
        have := h3.mul hxx
        simpa using this
      have := h25.add_deep h3x (by norm_num)
      have heq : (-25 : ℚ) + 3 * x ^ 2 = 3 * x ^ 2 - 25 := by ring
      rwa [heq] at this
    have h2y : Sharp w (2 * y) := by
      have h2 : Sharp 0 ((2 : ℚ)) := by
        have := sharp_int (n := 2) (by norm_num)
        simpa using this
      have := h2.mul hys
      simpa using this
    have hlamS : Sharp (-w) lam := by
      rw [hlam]
      have := hnum.mul h2y.inv
      have heq : (0 : ℤ) + -w = -w := by ring
      rw [heq] at this
      rwa [div_eq_mul_inv]
    have hlam2 : Sharp (-(2 * w)) (lam ^ 2) := by
      have := hlamS.mul hlamS
      rw [← pow_two] at this
      have heq : -w + -w = -(2 * w) := by ring
      rwa [heq] at this
    have hx₂S : Sharp (-(2 * w)) x₂ := by
      rw [hx₂]
      have hdx : Deep 0 (-x + -x) := by
        have hx0' : Deep 0 x := Or.inr hneg
        have hx0 : Deep 0 (-x) := hx0'.neg
        exact hx0.add hx0
      have := hlam2.add_deep hdx (by omega)
      have heq : lam ^ 2 + (-x + -x) = lam ^ 2 - x - x := by ring
      rwa [heq] at this
    have hx₂0 : x₂ ≠ 0 := hx₂S.1
    have hx₂neg : padicValRat 3 x₂ < 0 := by
      have := hx₂S.2
      omega
    obtain ⟨K, hK1, hxs, hys'⟩ := theKernelLevelIsClassified (curve_eq h₂) hy₂ hx₂0 hx₂neg
    exact ⟨2, x₂, y₂, h₂, K, two_pos, by omega, hQ₂, hK1, hxs, hys'⟩

/-! ## 5. The kernel refuses the closed winding -/

/-- **A kernel point of distant prime order is refused**: walking its cyclic subgroup, the
transport coordinate accumulates `t(m•R) ≡ m·t(R)` one level deep, and the closing of the
walk forces `p·t(R)` deeper than its exact level. -/
private lemma kernel_point_refuses {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {xR yR : ℚ} {hRns : E5.Nonsingular xR yR}
    (hord : addOrderOf (pointOf hRns : E5.Point) = p)
    {K : ℕ} (hK : 1 ≤ K)
    (hxR : Sharp (-(2 * (K : ℤ))) xR) (hyRs : Sharp (-(3 * (K : ℤ))) yR) : False := by
  set R : E5.Point := pointOf hRns with hRdef
  have hyR : yR ≠ 0 := hyRs.1
  have htR : Sharp ((K : ℤ)) (xR / yR) := by
    have h := hxR.mul hyRs.inv
    have heq : (-(2 * (K : ℤ))) + -(-(3 * (K : ℤ))) = (K : ℤ) := by ring
    rw [heq] at h
    rwa [div_eq_mul_inv]
  have hsR : Sharp (3 * (K : ℤ)) (1 / yR) := by
    have h := hyRs.inv
    rw [one_div]
    simpa using h
  have hp3 : ¬ (3 : ℤ) ∣ (p : ℤ) := by
    intro hdvd
    have h3p : (3 : ℕ) ∣ p := by exact_mod_cast hdvd
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h3p
    omega
  have hpS : Sharp 0 ((p : ℚ)) := by
    have := sharp_int (n := (p : ℤ)) hp3
    simpa using this
  have hptR : Sharp ((K : ℤ)) ((p : ℚ) * (xR / yR)) := by
    have := hpS.mul htR
    simpa using this
  -- the contradiction engine: a multiple of `t(R)` by `p` cannot be deep
  have hcontra : ¬ Deep ((K : ℤ) + 1) ((p : ℚ) * (xR / yR)) := hptR.not_deep
  -- the walk
  have main : ∀ m : ℕ, 1 ≤ m → m ≤ p - 1 →
      ∃ (x y : ℚ) (h : E5.Nonsingular x y),
        m • R = pointOf h ∧ y ≠ 0 ∧
        Deep ((K : ℤ)) (x / y) ∧ Deep (3 * (K : ℤ)) (1 / y) ∧
        Deep ((K : ℤ) + 1) (x / y - (m : ℚ) * (xR / yR)) := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨xR, yR, hRns, ?_, hyR, htR.deep, hsR.deep, ?_⟩
      · rw [one_smul]
      · have hz : xR / yR - ((1 : ℕ) : ℚ) * (xR / yR) = 0 := by push_cast; ring
        rw [hz]
        exact deep_zero _
    | succ m hm ih =>
      intro hb
      obtain ⟨xm, ym, hm', hQm, hym, htm, hsm, hCm⟩ := ih (by omega)
      obtain ⟨x₃, y₃, h₃, hQ₃, hy₃⟩ :=
        multiple_affine hp hp5 hord (m := m + 1) (by omega) (by omega)
      have hsum : pointOf hm' + R = pointOf h₃ := by
        simpa [pointOf] using
          (show pointOf hm' + R = Point.some x₃ y₃ h₃ by
            rw [← hQm, ← hQ₃, succ_nsmul])
      -- exclusions from the order
      have hmR_ne : ∀ j : ℕ, 0 < j → j < p → j • R ≠ 0 := by
        intro j hj0 hjp hj
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hj
        rw [hord] at hdvd
        have := Nat.le_of_dvd hj0 hdvd
        omega
      by_cases hxeq : xm = xR
      · -- same abscissa: the multiple is the point itself, and the step is a doubling
        have hy2 : ym = yR ∨ ym = -yR := by
          have hcm := curve_eq hm'
          have hcR := curve_eq hRns
          rw [hxeq] at hcm
          have : (ym - yR) * (ym + yR) = 0 := by linear_combination hcm - hcR
          rcases mul_eq_zero.mp this with h | h
          · exact Or.inl (by linarith)
          · exact Or.inr (by linarith)
        rcases hy2 with hyy | hyy
        · -- the multiple is the point: m = 1, tangent step
          have hmeq : pointOf hm' = R := by
            rw [hRdef]
            exact some_eq_some hxeq hyy
          have hm1' : m = 1 := by
            by_contra hne1
            have hmR : m • R = R := by rw [hQm, hmeq]
            have hsub : (m - 1) • R + 1 • R = m • R := by
              rw [← add_nsmul]
              congr 1
              omega
            rw [one_smul, hmR] at hsub
            have h1 : (m - 1) • R = 0 :=
              add_right_cancel (b := R) (c := 0) (by rw [hsub, zero_add])
            exact hmR_ne (m - 1) (by omega) (by omega) h1
          subst hm1'
          have hsum' : pointOf hRns + pointOf hRns = pointOf h₃ := by
            rw [← hsum, hmeq, hRdef]
          rcases tangent_estimate hK hyR hy₃ hsum' htR.deep hsR.deep with hco | ⟨hd1, hd2, hd3⟩
          · -- 2R = −R would close the third winding
            exfalso
            have h3R : (3 : ℕ) • R = 0 := by
              have h2R : (2 : ℕ) • R = -R := by
                rw [two_nsmul, hRdef]
                rw [hsum']
                exact hco
              have hs3 : (3 : ℕ) • R = (2 : ℕ) • R + R := by
                rw [← succ_nsmul]
              rw [hs3, h2R, neg_add_cancel]
            have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h3R
            rw [hord] at hdvd
            have := Nat.le_of_dvd (by norm_num) hdvd
            omega
          · refine ⟨x₃, y₃, h₃, hQ₃, hy₃, hd2, hd3, ?_⟩
            have hcast : ((1 + 1 : ℕ) : ℚ) = 2 := by norm_num
            rw [hcast]
            exact hd1
        · -- the multiple is the negation: the next multiple would vanish
          exfalso
          have hmeq : pointOf hm' = -R := by
            rw [hRdef, Point.neg_some]
            exact some_eq_some hxeq (by rw [negY_eq]; linarith [hyy])
          have : (m + 1) • R = 0 := by
            rw [succ_nsmul, hQm, hmeq, neg_add_cancel]
          exact hmR_ne (m + 1) (by omega) (by omega) this
      · -- distinct abscissae: chord step
        rcases chord_estimate hK hym hyR hy₃ hxeq hsum htm hsm htR.deep hsR.deep with
          hco | hco | ⟨hd1, hd2, hd3⟩
        · -- the sum is the negation of the multiple: `2m + 1 = p`, refused by doubling
          exfalso
          have h2m1 : (2 * m + 1) • R = 0 := by
            have hstep : (m + 1) • R = -(m • R) := by rw [hQ₃, hco, hQm]
            have hsplit : (2 * m + 1) • R = (m + 1) • R + m • R := by
              rw [← add_nsmul]
              congr 1
              omega
            rw [hsplit, hstep, neg_add_cancel]
          have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h2m1
          rw [hord] at hdvd
          obtain ⟨c, hc⟩ := hdvd
          have hpm : 2 * m + 1 = p := by
            rcases Nat.lt_or_ge c 2 with hc2 | hc2
            · interval_cases c <;> omega
            · exfalso
              have hbig : 2 * p ≤ p * c := by
                calc 2 * p = p * 2 := by ring
                _ ≤ p * c := Nat.mul_le_mul_left p hc2
              have h2 : 2 * p ≤ 2 * m + 1 := by rw [hc]; exact hbig
              omega
          -- the doubling of the multiple lands on `−R`
          have h2mR : (2 * m) • R = -R := by
            have : (2 * m + 1) • R = (2 * m) • R + R := by rw [← succ_nsmul]
            have h0 := h2m1
            rw [this] at h0
            exact eq_neg_of_add_eq_zero_left h0
          have hsum2 : pointOf hm' + pointOf hm' =
              pointOf ((E5.nonsingular_neg ..).mpr hRns) := by
            have hh : pointOf hm' + pointOf hm' = (2 * m) • R := by
              rw [Nat.mul_comm 2 m, mul_nsmul, two_nsmul, hQm]
            rw [hh, h2mR, hRdef, Point.neg_some]
          have hyneg' : E5.negY xR yR ≠ 0 := by
            rw [negY_eq]
            exact neg_ne_zero.mpr hyR
          rcases tangent_estimate hK hym hyneg' hsum2 htm hsm with hco2 | ⟨he1, _, _⟩
          · -- `−R = −(m•R)` would force `m = 1` and `p = 3`
            have hco2' : -pointOf hRns = -pointOf hm' := by
              rw [Point.neg_some]
              exact hco2
            have hmeq : pointOf hm' = R := by
              have hneg := congrArg (fun P => -P) hco2'
              simp only [neg_neg] at hneg
              rw [hRdef]
              exact hneg.symm
            have hm1' : m • R = R := by rw [hQm, hmeq]
            have : (m - 1) • R = 0 := by
              have hsub : (m - 1) • R + 1 • R = m • R := by
                rw [← add_nsmul]
                congr 1
                omega
              rw [one_smul, hm1'] at hsub
              exact add_right_cancel (b := R) (by rw [hsub, zero_add])
            rcases Nat.eq_or_lt_of_le (by omega : 1 ≤ m) with h1 | h1
            · omega
            · exact hmR_ne (m - 1) (by omega) (by omega) this
          · -- the depth contradiction: `p·t(R)` a level deep
            apply hcontra
            -- t(−R) = −t(R)
            have htneg : xR / (E5.negY xR yR) = -(xR / yR) := by
              rw [negY_eq, div_neg]
            rw [htneg] at he1
            -- he1 : Deep (K+1) (−t(R) − 2·t(mR))
            have hcomb : (p : ℚ) * (xR / yR) =
                -(-(xR / yR) - 2 * (xm / ym)) - 2 * (xm / ym - (m : ℚ) * (xR / yR)) := by
              have hcast : ((2 * m + 1 : ℕ) : ℚ) = (p : ℚ) := by
                rw [hpm]
              push_cast at hcast
              linear_combination (xR / yR) * hcast.symm
            rw [hcomb]
            have hd2' : Deep ((K : ℤ) + 1) (-(2 * (xm / ym - (m : ℚ) * (xR / yR)))) := by
              have h2' : Deep 0 ((2 : ℚ)) := (sharp_int (n := 2) (by norm_num)).deep
              have := (h2'.mul hCm).neg
              simpa using this
            have := he1.neg.add hd2'
            have heq : -(-(xR / yR) - 2 * (xm / ym)) +
                -(2 * (xm / ym - (m : ℚ) * (xR / yR))) =
                -(-(xR / yR) - 2 * (xm / ym)) - 2 * (xm / ym - (m : ℚ) * (xR / yR)) := by
              ring
            rwa [heq] at this
        · -- the sum is the negation of the base: `m + 2 = p`, refused by doubling the base
          exfalso
          have hm2 : (m + 2) • R = 0 := by
            have hstep : (m + 1) • R = -R := by rw [hQ₃, hco, hRdef]
            have hsplit : (m + 2) • R = (m + 1) • R + 1 • R := by
              rw [← add_nsmul]
            rw [hsplit, hstep, one_smul, neg_add_cancel]
          have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hm2
          rw [hord] at hdvd
          have hpm : m + 2 = p := by
            have hle := Nat.le_of_dvd (by omega) hdvd
            omega
          -- the doubling of the base lands on `−(m•R)`
          have h2R : (2 : ℕ) • R = -(m • R) := by
            have hsplit : (m + 2) • R = (2 : ℕ) • R + m • R := by
              rw [← add_nsmul]
              congr 1
              omega
            have h0 := hm2
            rw [hsplit] at h0
            exact eq_neg_of_add_eq_zero_left h0
          have hsum2 : pointOf hRns + pointOf hRns =
              pointOf ((E5.nonsingular_neg ..).mpr hm') := by
            have hh : pointOf hRns + pointOf hRns = (2 : ℕ) • R := by
              rw [two_nsmul, hRdef]
            rw [hh, h2R, hQm, Point.neg_some]
          have hyneg' : E5.negY xm ym ≠ 0 := by
            rw [negY_eq]
            exact neg_ne_zero.mpr hym
          rcases tangent_estimate hK hyR hyneg' hsum2 htR.deep hsR.deep with hco2 | ⟨he1, _, _⟩
          · have hco2' : -pointOf hm' = -pointOf hRns := by
              rw [Point.neg_some]
              exact hco2
            have hmeq : pointOf hm' = R := by
              have hneg := congrArg (fun P => -P) hco2'
              simp only [neg_neg] at hneg
              rw [hRdef]
              exact hneg
            have hm1' : m • R = R := by rw [hQm, hmeq]
            have : (m - 1) • R = 0 := by
              have hsub : (m - 1) • R + 1 • R = m • R := by
                rw [← add_nsmul]
                congr 1
                omega
              rw [one_smul, hm1'] at hsub
              exact add_right_cancel (b := R) (by rw [hsub, zero_add])
            rcases Nat.eq_or_lt_of_le (by omega : 1 ≤ m) with h1 | h1
            · omega
            · exact hmR_ne (m - 1) (by omega) (by omega) this
          · apply hcontra
            have htneg : xm / (E5.negY xm ym) = -(xm / ym) := by
              rw [negY_eq, div_neg]
            rw [htneg] at he1
            -- he1 : Deep (K+1) (−t(mR) − 2·t(R))
            have hcomb : (p : ℚ) * (xR / yR) =
                -(-(xm / ym) - 2 * (xR / yR)) - (xm / ym - (m : ℚ) * (xR / yR)) := by
              have hcast : ((m + 2 : ℕ) : ℚ) = (p : ℚ) := by rw [hpm]
              push_cast at hcast
              linear_combination (xR / yR) * hcast.symm
            rw [hcomb]
            have hsum3 := he1.neg.add hCm.neg
            have heq : -(-(xm / ym) - 2 * (xR / yR)) + -(xm / ym - (m : ℚ) * (xR / yR)) =
                -(-(xm / ym) - 2 * (xR / yR)) - (xm / ym - (m : ℚ) * (xR / yR)) := by ring
            rwa [heq] at hsum3
        · -- the generic chord step
          refine ⟨x₃, y₃, h₃, hQ₃, hy₃, hd2, hd3, ?_⟩
          have hcomb : x₃ / y₃ - ((m + 1 : ℕ) : ℚ) * (xR / yR) =
              (x₃ / y₃ - xm / ym - xR / yR) + (xm / ym - (m : ℚ) * (xR / yR)) := by
            push_cast
            ring
          rw [hcomb]
          exact hd1.add hCm
  -- the walk closes
  obtain ⟨xf, yf, hf, hQf, hyf, _, _, hCf⟩ := main (p - 1) (by omega) le_rfl
  have hpR : p • R = 0 := by
    rw [← hord]
    exact addOrderOf_nsmul_eq_zero R
  have hfin : (p - 1) • R = -R := by
    have hsplit : p • R = (p - 1) • R + 1 • R := by
      rw [← add_nsmul]
      congr 1
      omega
    rw [hsplit, one_smul] at hpR
    exact eq_neg_of_add_eq_zero_left hpR
  have hfeq : pointOf hf = pointOf ((E5.nonsingular_neg ..).mpr hRns) := by
    rw [← hQf, hfin, hRdef, Point.neg_some]
  have hxf : xf = xR := congrArg abscissa hfeq
  have hyf' : yf = E5.negY xR yR := congrArg ordinate hfeq
  apply hcontra
  have htf : xf / yf = -(xR / yR) := by
    rw [hxf, hyf', negY_eq, div_neg]
  rw [htf] at hCf
  have hcomb : (p : ℚ) * (xR / yR) =
      -(-(xR / yR) - ((p - 1 : ℕ) : ℚ) * (xR / yR)) := by
    have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      have : (1 : ℕ) ≤ p := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]
    ring
  rw [hcomb]
  exact hCf.neg

/-! ## 6. The discharges -/

/-- **THE INSTRUMENT: the distant prime windings never close.**  No rational route of
`y² = x³ − 25x` closes at a prime winding of five or more — `WindingCensus.lean`'s named-open
statement, discharged by the kernel's descent on depth. -/
theorem theDistantPrimeWindingsNeverCloseHolds :
    WindingCensus.TheDistantPrimeWindingsNeverClose := by
  intro q Q hq hq5 hqQ
  by_contra hQ0
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hqQ
  rcases Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd with h1 | hord
  · exact hQ0 (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  · -- the order is the prime itself: find the kernel multiple and refuse it
    obtain ⟨n, x, y, h, K, hn0, hnp, hQn, hK1, hxs, hys⟩ :=
      exists_kernel_multiple hq hq5 hord
    have hcop : Nat.gcd q n = 1 :=
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hq).mpr
        (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega))
    have hordn : addOrderOf (pointOf h : E5.Point) = q := by
      rw [← hQn, addOrderOf_nsmul' _ (by omega : n ≠ 0), hord, hcop, Nat.div_one]
    exact kernel_point_refuses hq hq5 hordn hK1 hxs hys

/-- **THE DISCHARGE: the torsion of `y² = x³ − 25x` is the Klein four-group.**
`RankOne.lean`'s named-open proposition, now a theorem: the census below the fifth winding
was read by rational receivers, and the kernel's descent refuses everything beyond. -/
theorem theTorsionIsTheKleinGroupHolds : RankOne.TheTorsionIsTheKleinGroup :=
  WindingCensus.theCensusReducesToTheDistantPrimeWindings theDistantPrimeWindingsNeverCloseHolds

/-- **The chain is infinite**: the point `(−4, 6)` has infinite order — `RankOne.lean`'s other
named-open proposition, now a theorem, since the chain provably leaves the torsion table. -/
theorem thePointHasInfiniteOrderHolds : RankOne.ThePointHasInfiniteOrder := by
  intro n hn hnP
  have hmem := (theTorsionIsTheKleinGroupHolds RankOne.P).mp ⟨n, hn, hnP⟩
  rcases hmem with h | h | h | h
  · exact RankOne.theChainLeavesTheTorsionTable.1.1 h
  · exact RankOne.theChainLeavesTheTorsionTable.1.2.1 h
  · exact RankOne.theChainLeavesTheTorsionTable.1.2.2.1 h
  · exact RankOne.theChainLeavesTheTorsionTable.1.2.2.2 h

end Soma.Holonics.Millennium.DistantWindings
