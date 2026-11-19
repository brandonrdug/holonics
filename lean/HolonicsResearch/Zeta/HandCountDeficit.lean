import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import HolonicsResearch.Zeta.Hand

/-!
# A code length's equation of state, and the count lens's saving on the primes' hand

The record of October 23
(`research/records/2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md`,
§1 and §5, owed in §7; atlas `code.equation-of-state`, `rh.hand-count-deficit`) reads a region's code length `L` on
its own clock `V` through the equation of state `w = −d ln L/d ln V`, and reads the hand `λ(n) = (−1)^Ω(n)` through the
count lens, whose maximum-likelihood saving over the floor of one bit a cell is
`D(N) = N(1 − h₂((N + L)/(2N)))` bits, `L(N) = Σ_(n ≤ N) λ(n)`.

[proved-derived; formal-checked] What is proved.

1. **The equation of state is the logarithmic rate** (`eos`, `hasDerivAt_log_log`, `eos_eq_neg_deriv_log_log`): for
   `V > 0` and `L(V) > 0`, `w = −V L′(V)/L(V)` is `−d ln L/d ln V`, the derivative of `u ↦ ln L(eᵘ)` at `ln V`.
2. **A learning region cannot expand** (`eos_ge_neg_one`): if `L = hV + C(V)` with the excess `C` concave on
   `[0, ∞)`, `C(0) = 0` and `L(V) > 0`, then `V C′(V) ≤ C(V)`, so `V L′ ≤ L` and `w ≥ −1`. Expansion (`w < −1`) needs
   an excess that is not concave.
3. **The deficit's series** (`gap`, `gap_eq`, `hasSum_gap`): in nats, `ln 2 − H((1 + y)/2)`, `H = Real.binEntropy`, is
   `((1 + y)/2) ln(1 + y) + ((1 − y)/2) ln(1 − y) = Σ_(k ≥ 1) y^(2k)/(2k(2k − 1))` for `|y| < 1`.
4. **The sandwich** (`gap_bounds`, `one_sub_h₂_bounds`, `deficit_sandwich`): for `|y| ≤ 1`,
   `y²/2 ≤ ln 2 − H((1 + y)/2) ≤ y² ln 2`; in bits, `h₂ = H / ln 2`, `y²/(2 ln 2) ≤ 1 − h₂((1 + y)/2) ≤ y²`; so for
   `N > 0` and `|L| ≤ N`, `L²/(2N ln 2) ≤ D(N) ≤ L²/N`. The lower side is the first term of the series (Pinsker's
   inequality); the upper side holds because the series over `y²` divided by `y²` increases in `|y|` and its value at
   `|y| = 1` is `ln 2`, read here by continuity at the edge.
5. **The hand's saving** (`abs_runningHandSum_le`, `handDeficit_sandwich`): `|L(N)| ≤ N`, so the sandwich holds on the
   hand's running sum at every `N ≥ 1`.
6. **The growth law on the saving** (`hand_iff_deficit`): `Hand.TheHandCancelsToSquareRoot` holds exactly when for
   every `ε > 0` there is `C > 0` with `D(N) ≤ C N^ε` at every `N ≥ 1`, with no hypothesis: the count lens's saving on
   the primes' hand grows slower than every power exactly when the hand cancels to square-root order.

The computational object is the helical pair interaction read as a count: the hand is a word of half-turns, its running
sum is the walk's winding, and the count lens's saving is the code a learned bias recovers from that winding. Of the
winding guide's six general objects this touches the helix (the hand's half-turns and their running winding) and faces
and placement (the code length read on its clock, in bits and in nats); the pair, the cell holonomy, the tube and the
tower thread stay attached.

Consumers: the atlas rows `code.equation-of-state` and `rh.hand-count-deficit`, `Zeta/Hand.TheHandCancelsToSquareRoot`,
and the record's §1 and §5.

What stands beside it: the classical equivalence of `TheHandCancelsToSquareRoot` with the Riemann hypothesis (named by
`Zeta/Seam` and not formalized), so the RH reading of item 6 passes through that bridge; the Stirling form
`KT(N) = N + ½ log₂ N + ½ log₂(π/2) − D(N) + o(1)`, the octave form `w = −log₂(L(2V)/L(V))` and the record's measured
readings.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Zeta.HandCountDeficit

open Real Filter Topology Finset

/-! ## 1. The equation of state -/

/-- The equation of state of a code length `L` on its clock `V`, `w = −V L′(V)/L(V)`. -/
noncomputable def eos (L : ℝ → ℝ) (V : ℝ) : ℝ := -(V * deriv L V) / L V

/-- [proved-standard; formal-checked] On positive values, `V L′(V)/L(V)` is the derivative of `u ↦ ln L(eᵘ)` at
`ln V`: the logarithmic rate `d ln L/d ln V`. -/
theorem hasDerivAt_log_log {L : ℝ → ℝ} {V : ℝ} (hV : 0 < V) (hL : 0 < L V) (hd : DifferentiableAt ℝ L V) :
    HasDerivAt (fun u => Real.log (L (Real.exp u))) (V * deriv L V / L V) (Real.log V) := by
  have h1 : HasDerivAt Real.exp V (Real.log V) := by
    simpa [Real.exp_log hV] using Real.hasDerivAt_exp (Real.log V)
  have h2 : HasDerivAt L (deriv L V) (Real.exp (Real.log V)) := by
    rw [Real.exp_log hV]; exact hd.hasDerivAt
  have h3 := h2.comp (Real.log V) h1
  have h5 : (L ∘ Real.exp) (Real.log V) = L V := by simp [Real.exp_log hV]
  have h4 := h3.log (by rw [h5]; exact hL.ne')
  rw [h5, mul_comm] at h4
  exact h4

/-- [proved-standard; formal-checked] **The equation of state is `−d ln L/d ln V`.** -/
theorem eos_eq_neg_deriv_log_log {L : ℝ → ℝ} {V : ℝ} (hV : 0 < V) (hL : 0 < L V)
    (hd : DifferentiableAt ℝ L V) :
    eos L V = -deriv (fun u => Real.log (L (Real.exp u))) (Real.log V) := by
  rw [(hasDerivAt_log_log hV hL hd).deriv, eos, neg_div]

/-- [proved-derived; formal-checked] **A learning region cannot expand.** A code length `L = hV + C(V)` whose excess
`C` is concave on `[0, ∞)` with `C(0) = 0` has `w ≥ −1` wherever it is positive: concavity gives `V C′(V) ≤ C(V)`. -/
theorem eos_ge_neg_one {C : ℝ → ℝ} {h V : ℝ} (hC : ConcaveOn ℝ (Set.Ici 0) C) (hC0 : C 0 = 0)
    (hV : 0 < V) (hd : DifferentiableAt ℝ C V) (hL : 0 < h * V + C V) :
    -1 ≤ eos (fun v => h * v + C v) V := by
  have hs := hC.deriv_le_slope (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hV.le) hV hd
  rw [slope_def_field, hC0, sub_zero, sub_zero, le_div_iff₀ hV] at hs
  have hD : HasDerivAt (fun v => h * v + C v) (h * 1 + deriv C V) V :=
    ((hasDerivAt_id' V).const_mul h).add hd.hasDerivAt
  rw [eos, hD.deriv, mul_one, le_div_iff₀ hL]
  nlinarith

/-! ## 2. The deficit's series and its sandwich -/

/-- The binary entropy in bits. -/
noncomputable def h₂ (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- The count lens's saving a cell, in nats, at the bias `(1 + y)/2`: `ln 2 − H((1 + y)/2)`. -/
noncomputable def gap (y : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 + y) / 2)

/-- [proved-standard; formal-checked] The saving a cell is continuous, the edge `|y| = 1` included. -/
@[fun_prop] theorem continuous_gap : Continuous gap := by
  unfold gap
  fun_prop

/-- [proved-standard; formal-checked] Inside the edge, `ln 2 − H((1 + y)/2)` is
`((1 + y)/2) ln(1 + y) + ((1 − y)/2) ln(1 − y)`. -/
theorem gap_eq {y : ℝ} (hy : |y| < 1) :
    gap y = (1 + y) / 2 * Real.log (1 + y) + (1 - y) / 2 * Real.log (1 - y) := by
  have h1 : 0 < 1 + y := by linarith [(abs_lt.mp hy).1]
  have h2 : 0 < 1 - y := by linarith [(abs_lt.mp hy).2]
  unfold gap Real.binEntropy
  rw [show 1 - (1 + y) / 2 = (1 - y) / 2 by ring, Real.log_inv, Real.log_inv,
    Real.log_div h1.ne' two_ne_zero, Real.log_div h2.ne' two_ne_zero]
  ring

/-- [proved-standard; formal-checked] **The deficit's series**: `ln 2 − H((1 + y)/2) = Σ_(n ≥ 0)
y^(2n+2)/((2n + 1)(2n + 2))` for `|y| < 1`. -/
theorem hasSum_gap {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => y ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) (gap y) := by
  have h1 : 0 < 1 + y := by linarith [(abs_lt.mp hy).1]
  have h2 : 0 < 1 - y := by linarith [(abs_lt.mp hy).2]
  have hy2 : |y ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg y) hy two_ne_zero
  have hA := Real.hasSum_log_sub_log_of_abs_lt_one hy
  have hB := Real.hasSum_pow_div_log_of_abs_lt_one hy2
  have hlog : Real.log (1 - y ^ 2) = Real.log (1 + y) + Real.log (1 - y) := by
    rw [← Real.log_mul h1.ne' h2.ne']
    congr 1
    ring
  have hS := (hA.mul_left (y / 2)).add (hB.mul_left (-1 / 2))
  have hval : gap y = y / 2 * (Real.log (1 + y) - Real.log (1 - y)) + -1 / 2 * -Real.log (1 - y ^ 2) := by
    rw [gap_eq hy, hlog]
    ring
  have hf : (fun n : ℕ => y ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) =
      fun n : ℕ => y / 2 * (2 * (1 / (2 * (n : ℝ) + 1)) * y ^ (2 * n + 1)) +
        -1 / 2 * ((y ^ 2) ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    have hn1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hn2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn3 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (n + 1) = 2 * n + 2 by ring, show y ^ (2 * n + 2) = y * y ^ (2 * n + 1) by ring]
    field_simp
    ring
  rw [hval, hf]
  exact hS

/-- [proved-standard; formal-checked] Every term of the deficit's series is nonnegative. -/
theorem gap_term_nonneg (y : ℝ) (n : ℕ) :
    0 ≤ y ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul]
  positivity

/-- [proved-derived; formal-checked] The series over `y²` divided by `y²` increases in `|y|`: for `|y| ≤ z < 1`,
`z² (ln 2 − H((1 + y)/2)) ≤ y² (ln 2 − H((1 + z)/2))`. -/
theorem gap_mono {y z : ℝ} (hyz : |y| ≤ z) (hz : z < 1) : z ^ 2 * gap y ≤ y ^ 2 * gap z := by
  have hy : |y| < 1 := lt_of_le_of_lt hyz hz
  have hz' : |z| < 1 := by rw [abs_of_nonneg ((abs_nonneg y).trans hyz)]; exact hz
  refine hasSum_le (fun n => ?_) ((hasSum_gap hy).mul_left (z ^ 2)) ((hasSum_gap hz').mul_left (y ^ 2))
  have hsq : y ^ 2 ≤ z ^ 2 := by
    rw [← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg y) hyz 2
  have hp : (y ^ 2) ^ n ≤ (z ^ 2) ^ n := pow_le_pow_left₀ (sq_nonneg y) hsq n
  have hD : 0 < (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) := by positivity
  have e1 : z ^ 2 * (y ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) =
      y ^ 2 * z ^ 2 * ((y ^ 2) ^ n / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) := by
    rw [← pow_mul]; ring
  have e2 : y ^ 2 * (z ^ 2 * 0 + z ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) =
      y ^ 2 * z ^ 2 * ((z ^ 2) ^ n / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) := by
    rw [← pow_mul]; ring
  rw [e1, show y ^ 2 * (z ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) =
      y ^ 2 * (z ^ 2 * 0 + z ^ (2 * n + 2) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) by ring, e2]
  gcongr

/-- [proved-standard; formal-checked] At the edge `y = 1` the saving is `ln 2`. -/
@[simp] theorem gap_one : gap 1 = Real.log 2 := by simp [gap]

/-- [proved-standard; formal-checked] At the edge `y = −1` the saving is `ln 2`. -/
@[simp] theorem gap_neg_one : gap (-1) = Real.log 2 := by simp [gap]

/-- [proved-derived; formal-checked] **The sandwich in nats**: for `|y| ≤ 1`,
`y²/2 ≤ ln 2 − H((1 + y)/2) ≤ y² ln 2`. -/
theorem gap_bounds {y : ℝ} (hy : |y| ≤ 1) : y ^ 2 / 2 ≤ gap y ∧ gap y ≤ y ^ 2 * Real.log 2 := by
  rcases hy.lt_or_eq with hy | hy
  · constructor
    · have := le_hasSum (hasSum_gap hy) 0 (fun j _ => gap_term_nonneg y j)
      norm_num at this
      linarith
    · -- `z ↦ y² gap z − z² gap y` is continuous and nonnegative on `[|y|, 1)`, so at `1`
      have hc : Continuous (fun z => y ^ 2 * gap z - z ^ 2 * gap y) := by fun_prop
      have hT : Tendsto (fun z => y ^ 2 * gap z - z ^ 2 * gap y) (𝓝[<] 1)
          (𝓝 (y ^ 2 * gap 1 - 1 ^ 2 * gap y)) :=
        (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ z in 𝓝[<] (1 : ℝ), 0 ≤ y ^ 2 * gap z - z ^ 2 * gap y := by
        filter_upwards [Ioo_mem_nhdsLT hy] with z hz
        linarith [gap_mono hz.1.le hz.2]
      have := ge_of_tendsto hT hev
      rw [gap_one, one_pow, one_mul] at this
      linarith
  · have h2 : Real.log 2 ≥ 1 / 2 := by
      have := Real.one_sub_inv_le_log_of_pos (x := 2) two_pos
      norm_num at this ⊢
      linarith
    rcases abs_eq (zero_le_one) |>.mp hy with rfl | rfl
    · simp only [gap_one]; norm_num; linarith
    · simp only [gap_neg_one]; norm_num; linarith

/-- [proved-derived; formal-checked] **The sandwich in bits**: for `|y| ≤ 1`,
`y²/(2 ln 2) ≤ 1 − h₂((1 + y)/2) ≤ y²`, with `h₂ = H / ln 2`. -/
theorem one_sub_h₂_bounds {y : ℝ} (hy : |y| ≤ 1) :
    y ^ 2 / (2 * Real.log 2) ≤ 1 - h₂ ((1 + y) / 2) ∧ 1 - h₂ ((1 + y) / 2) ≤ y ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e : 1 - h₂ ((1 + y) / 2) = gap y / Real.log 2 := by
    unfold h₂ gap
    field_simp
  obtain ⟨b1, b2⟩ := gap_bounds hy
  rw [e]
  constructor
  · rw [div_le_div_iff₀ (by positivity) hl]
    nlinarith
  · rw [div_le_iff₀ hl]
    linarith

/-- The count lens's saving over the floor, in bits, for `N` cells whose signs sum to `L`. -/
noncomputable def deficit (N L : ℝ) : ℝ := N * (1 - h₂ ((N + L) / (2 * N)))

/-- [proved-derived; formal-checked] **The deficit sandwich**: for `N > 0` and `|L| ≤ N`,
`L²/(2N ln 2) ≤ D ≤ L²/N`. -/
theorem deficit_sandwich {N L : ℝ} (hN : 0 < N) (hL : |L| ≤ N) :
    L ^ 2 / (2 * N * Real.log 2) ≤ deficit N L ∧ deficit N L ≤ L ^ 2 / N := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hy : |L / N| ≤ 1 := by
    rw [abs_div, abs_of_pos hN, div_le_one hN]
    exact hL
  have e : (N + L) / (2 * N) = (1 + L / N) / 2 := by field_simp
  obtain ⟨b1, b2⟩ := one_sub_h₂_bounds hy
  unfold deficit
  rw [e]
  constructor
  · calc L ^ 2 / (2 * N * Real.log 2) = N * ((L / N) ^ 2 / (2 * Real.log 2)) := by field_simp
      _ ≤ N * (1 - h₂ ((1 + L / N) / 2)) := by gcongr
  · calc N * (1 - h₂ ((1 + L / N) / 2)) ≤ N * (L / N) ^ 2 := by gcongr
      _ = L ^ 2 / N := by field_simp

/-! ## 3. The primes' hand -/

open Holonics.Zeta.Hand in
/-- [proved-standard; formal-checked] The hand's running sum is a walk of half-turns: `|L(N)| ≤ N`. -/
theorem abs_runningHandSum_le (N : ℕ) : |(Hand.runningHandSum N : ℝ)| ≤ N := by
  have h : |Hand.runningHandSum N| ≤ N := by
    unfold Hand.runningHandSum
    calc |∑ n ∈ Icc 1 N, hand n| ≤ ∑ n ∈ Icc 1 N, |hand n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _n ∈ Icc 1 N, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro n _
        rcases theHandIsOnlyEverAHalfTurn n with h | h <;> simp [h]
      _ = N := by simp
  exact_mod_cast h

/-- The count lens's saving on the hand's first `N` signs, in bits. -/
noncomputable def handDeficit (N : ℕ) : ℝ := deficit N (Hand.runningHandSum N)

/-- [proved-derived; formal-checked] The sandwich on the hand: `L(N)²/(2N ln 2) ≤ D(N) ≤ L(N)²/N` for `N ≥ 1`. -/
theorem handDeficit_sandwich {N : ℕ} (hN : 1 ≤ N) :
    (Hand.runningHandSum N : ℝ) ^ 2 / (2 * N * Real.log 2) ≤ handDeficit N ∧
      handDeficit N ≤ (Hand.runningHandSum N : ℝ) ^ 2 / N :=
  deficit_sandwich (by exact_mod_cast hN) (abs_runningHandSum_le N)

/-- [proved-derived; formal-checked] **The growth law on the saving.** The hand cancels to square-root order exactly
when the count lens's saving grows slower than every power, with no hypothesis. -/
theorem hand_iff_deficit :
    Hand.TheHandCancelsToSquareRoot ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → handDeficit N ≤ C * (N : ℝ) ^ ε := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro hH ε hε
    obtain ⟨C, hC, hb⟩ := hH (ε / 2) (by positivity)
    refine ⟨C ^ 2, by positivity, fun N hN => ?_⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (Hand.runningHandSum N : ℝ) ^ 2 ≤ C ^ 2 * (N : ℝ) ^ (1 + ε) := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (hb N hN) 2
      rw [sq_abs, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + ε / 2)) 2,
        ← Real.rpow_mul hNpos.le] at hsq
      rw [show (1 / 2 + ε / 2) * ((2 : ℕ) : ℝ) = 1 + ε by push_cast; ring] at hsq
      exact hsq
    calc handDeficit N ≤ (Hand.runningHandSum N : ℝ) ^ 2 / N := (handDeficit_sandwich hN).2
      _ ≤ C ^ 2 * (N : ℝ) ^ (1 + ε) / N := by gcongr
      _ = C ^ 2 * (N : ℝ) ^ ε := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
        field_simp
  · intro hD ε hε
    obtain ⟨C, hC, hb⟩ := hD (2 * ε) (by positivity)
    have hK : 0 < 2 * Real.log 2 * C := by positivity
    refine ⟨Real.sqrt (2 * Real.log 2 * C), Real.sqrt_pos.mpr hK, fun N hN => ?_⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hB : 0 ≤ Real.sqrt (2 * Real.log 2 * C) * (N : ℝ) ^ (1 / 2 + ε) := by positivity
    rw [← pow_le_pow_iff_left₀ (abs_nonneg _) hB two_ne_zero, sq_abs, mul_pow, Real.sq_sqrt hK.le,
      ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + ε)) 2, ← Real.rpow_mul hNpos.le,
      show (1 / 2 + ε) * ((2 : ℕ) : ℝ) = 1 + 2 * ε by push_cast; ring, Real.rpow_add hNpos, Real.rpow_one]
    have hs := (handDeficit_sandwich hN).1
    rw [div_le_iff₀ (by positivity)] at hs
    calc (Hand.runningHandSum N : ℝ) ^ 2 ≤ handDeficit N * (2 * N * Real.log 2) := hs
      _ ≤ C * (N : ℝ) ^ (2 * ε) * (2 * N * Real.log 2) := by gcongr; exact hb N hN
      _ = 2 * Real.log 2 * C * ((N : ℝ) * (N : ℝ) ^ (2 * ε)) := by ring

end Holonics.Zeta.HandCountDeficit
