import Mathlib

/-!
# Information spectroscopy: the clock gauge, the basin's Doppler delay and the reading's mass

Source: #410's box "Information spectroscopy (#404)" and the record
`research/records/2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md`,
§2 to §4 and §6 (its §9 lists the owed Lean). A mode of a constitution is one line `s` of its pencil
`s²C + sD + K`; a receiver's clock moves every line by one factor; in the multiplier disk a basin is a point and
the clock a boost; and a receiver has a mass along each reading, the inverse of its leverage.

[proved-derived; formal-checked] What is proved.

1. **The clock gauge** (record §2, `clock_gauge`): over any field, for `λ ≠ 0`,
   `det(s²C + sλD + λ²K) = λ^(2n) det((s/λ)²C + (s/λ)D + K)`, so the constitution `(C, λD, λ²K)` read on the clock
   `t = λτ` has every line at `λs`.
2. **A lossless proportional mass is a clock** (record §2, `proportionalMass_is_clock`, `proportionalMass_moves_lines`,
   `clock_of_mass`): with `D = 0` and `λ²μ = 1`, `det(s²(μC) + K) = μ^n det(s²C + λ²K)` (the record's "`μ²` times
   that of the clock `3/2`" at `n = 2`, `μ = 4/9`), and `det(s²(μC) + K) = det((s/λ)²C + K)`; over `ℝ` with `μ > 0`
   the loaded pencil at `s` is the unloaded one at `s√μ`, so every line moves by `μ^(−1/2)`.
3. **The Cayley chart** (record §3, `cayley_conjugates_clock`, `cayley_normSq_lt_one`, `halfRapidity_ratio`,
   `halfRapidity_velocity`): `z = (1 + s)/(1 − s)` sends the clock `s ↦ ks` to the boost
   `φ_a(z) = (z − a)/(1 − az)`, `a = (k − 1)/(k + 1)`, with `(1 + a)/(1 − a) = k` and
   `2a/(1 + a²) = (k² − 1)/(k² + 1)`; it takes the open left half plane into the open unit disk.
4. **Disk motions** (record §4, `one_sub_normSq_diskMotion`, `pseudoHyperbolicSq_diskMotion`,
   `pseudoHyperbolicSq_eq_normSq_motion`): for `φ(z) = u(z − c)/(1 − c̄z)` with `|u| = 1`,
   `1 − |φ(a)|² = (1 − |a|²)(1 − |c|²)/|1 − c̄a|²`, and `δ(a, b)² = |a − b|²/|1 − āb|²` is unchanged by every motion
   with `|c| ≠ 1`; `δ(a, b)² = |φ_a(b)|²`.
5. **The basin's group delay** (record §3, `hasDerivAt_basinResponse`, `groupDelay_basin`): `H_a(z) = (1 − āz)/(z − a)`
   has `H_a′(z) = (|a|² − 1)/(z − a)²`, and on the unit circle `−Re(z H_a′/H_a) = (1 − |a|²)/|z − a|²`.
6. **Its Doppler form** (record §3, `normSq_exp_sub_ofReal`, `poisson_doppler`, `groupDelay_basin_doppler`,
   `doppler_peak_trough`): for real `|a| < 1` and `β = 2a/(1 + a²)`, at `z = e^(iω)` the delay is
   `√(1 − β²)/(1 − β cos ω)`, with peak `(1 + a)/(1 − a) = k` at `ω = 0`, trough `1/k` at `ω = π`, and
   `(k + 1/k)/2 = 1/√(1 − β²)`.
7. **The ring sum** (record §3, `sum_range_pow_primitive`, `sum_inv_sub_roots`, `poisson_eq_re`, `ring_sum_range`,
   `sum_nthRootsFinset_eq_sum_range`, `ring_sum`, `ring_sum_of_normSq_lt_one`): over the `N`-th roots of unity,
   `Σ_(ζ^N = 1) (1 − |a|²)/|ζ − a|² = N·Re((1 + a^N)/(1 − a^N))` whenever `a^N ≠ 1`, in particular for `|a| < 1`. The
   proof is finite: `1/(a − ζ) = (Σ_i a^i ζ^(N−1−i))/(a^N − 1)` and the power sums of the roots vanish below `N`.
8. **The reading's mass** (record §6, `leverage_add_reading`, `inv_leverage_add_reading`, `leverage_add_reading_eq`,
   `reading_share`, `reading_share_witness`): with leverage `h = vᵀG⁻¹v` and `G′ = G + vvᵀ` (both invertible),
   `h′(1 + h) = h`, so `1/h′ = 1/h + 1` and `h′ = h/(1 + h) = m/(M + m)` with `m = 1`, `M = 1/h`; and the
   prediction along `v` of the solution of `G′w′ = b + yv` moves from that of `Gw = b` by `h′` of the residual,
   `vᵀw′ − vᵀw = h′(y − vᵀw)`. No symmetry of `G` is used. The record's witness `h = 215/209` gives `h′ = 215/424`.

Limits. The first-order line shift `δs = −vᵀ(s²ΔC + sΔD + ΔK)v / vᵀ(2sC + D)v` at a simple line (record §1) is not proved
here; it needs the derivative of a simple root of `det P_ε` in `ε`. Neither is the inner–outer factorization of record §5
(for a rational causal stable `H`, `H = H_min B` with `|H| = |H_min|` on the circle and `B` a finite Blaschke product
whose degree is the winding deficit), nor the count of basins as a winding (record §4, the argument principle). The viscous
clause of record §2 (with `D` held, a mass load multiplies each loss invariant by `1/μ`) and the first-order ratio shift
`δ log(s₁/s₂)` are not stated. The off-range reading (record §6, share one where `v ∉ range G`) is outside these theorems,
which take `G` invertible. The ring sum is stated over Mathlib's `Polynomial.nthRootsFinset N 1` and, through any
primitive root, over `range N`; the receipts' exact checks in `ℚ(ζ_M)` are not reproduced.

The computational object is the helical pair interaction: a line is a pair's move per tick, its ratio's logarithmic
derivative is boost rate plus `i` times turn rate, and a basin's delay on the receiver's ring is the face that pair
leaves on the circle. Of the winding guide's six general objects this touches faces and placement (the Poisson face
of a basin on the circle, the ring of `N` channels, the leverage of a reading) and the pair (the clock as one
boost of the multiplier disk); the helix, cell holonomy, the tube and the tower thread stay attached.

Consumers: atlas `spectro.clock-gauge`, `spectro.basin-doppler`, `spectro.basin-shape` and `spectro.reading-mass`,
whose statements these theorems carry; the record's §9 box in #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Transport.InformationSpectroscopy

open Matrix Finset
open scoped ComplexConjugate

/-! ## 1. The clock gauge of the pencil -/

section Pencil

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **The clock gauge.** Read on the clock `t = λτ`, the constitution
`(C, λD, λ²K)` has every line at `λs`: its pencil's determinant at `s` is `λ^(2n)` times the original pencil's at
`s/λ`. -/
theorem clock_gauge (C D K : Matrix n n 𝕜) (s l : 𝕜) (hl : l ≠ 0) :
    (s ^ 2 • C + (s * l) • D + l ^ 2 • K).det =
      l ^ (2 * Fintype.card n) * ((s / l) ^ 2 • C + (s / l) • D + K).det := by
  have h : s ^ 2 • C + (s * l) • D + l ^ 2 • K = l ^ 2 • ((s / l) ^ 2 • C + (s / l) • D + K) := by
    simp only [smul_add, smul_smul]
    congr 2
    · congr 1; field_simp
    · congr 1; field_simp
  rw [h, det_smul, ← pow_mul]

/-- [proved-derived; formal-checked] **A lossless proportional mass is a clock.** With no viscosity, the mass load
`C ↦ μC` has `μ^n` times the characteristic polynomial of the clock `λ`, `λ²μ = 1`. -/
theorem proportionalMass_is_clock (C K : Matrix n n 𝕜) (μ l s : 𝕜) (h : l ^ 2 * μ = 1) :
    (s ^ 2 • (μ • C) + K).det = μ ^ Fintype.card n * (s ^ 2 • C + l ^ 2 • K).det := by
  have e : s ^ 2 • (μ • C) + K = μ • (s ^ 2 • C + l ^ 2 • K) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm μ (l ^ 2), h, one_smul, mul_comm]
  rw [e, det_smul]

/-- [proved-derived; formal-checked] The mass load's pencil at `s` is the unloaded pencil at `s/λ`: every line moves
by `λ`. -/
theorem proportionalMass_moves_lines (C K : Matrix n n 𝕜) (μ l s : 𝕜) (h : l ^ 2 * μ = 1) :
    (s ^ 2 • (μ • C) + K).det = ((s / l) ^ 2 • C + K).det := by
  have hl : l ≠ 0 := by rintro rfl; simp at h
  have hg := clock_gauge C 0 K s l hl
  simp only [smul_zero, add_zero] at hg
  rw [proportionalMass_is_clock C K μ l s h, hg, ← mul_assoc, pow_mul, ← mul_pow, mul_comm μ, h,
    one_pow, one_mul]

end Pencil

/-- [proved-derived; formal-checked] **The clock `μ^(−1/2)`.** Over `ℝ` with `μ > 0`, the loaded pencil at `s` is the
unloaded one at `s√μ`, so a line `s₀` of `(C, 0, K)` becomes the line `s₀/√μ` of `(μC, 0, K)`. -/
theorem clock_of_mass {n : Type*} [Fintype n] [DecidableEq n]
    (C K : Matrix n n ℝ) {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    (s ^ 2 • (μ • C) + K).det = ((s * Real.sqrt μ) ^ 2 • C + K).det := by
  have h : (Real.sqrt μ)⁻¹ ^ 2 * μ = 1 := by
    rw [inv_pow, Real.sq_sqrt hμ.le, inv_mul_cancel₀ hμ.ne']
  rw [proportionalMass_moves_lines C K μ _ s h, div_inv_eq_mul]

/-! ## 2. The Cayley chart conjugates a clock to a boost -/

section Cayley

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- [definition] The Cayley chart from the line plane to the multiplier disk, `z = (1 + s)/(1 − s)`. -/
def cayley (s : 𝕜) : 𝕜 := (1 + s) / (1 - s)

/-- [definition] The boost of the disk along the real axis, `φ_a(z) = (z − a)/(1 − az)`. -/
def boost (a z : 𝕜) : 𝕜 := (z - a) / (1 - a * z)

/-- [definition] The boost that a clock `k` becomes in the chart, `a = (k − 1)/(k + 1)`. -/
def halfRapidity (k : 𝕜) : 𝕜 := (k - 1) / (k + 1)

/-- [proved-derived; formal-checked] **The Cayley chart conjugates the clock `s ↦ ks` to the boost `φ_a`.** -/
theorem cayley_conjugates_clock (k s : 𝕜) (hs : s ≠ 1) (hks : k * s ≠ 1) (hk : k + 1 ≠ 0) :
    cayley (k * s) = boost (halfRapidity k) (cayley s) := by
  unfold cayley boost halfRapidity
  have h1 : (1 : 𝕜) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have h2 : (1 : 𝕜) - k * s ≠ 0 := sub_ne_zero.mpr (Ne.symm hks)
  have hden : 1 - (k - 1) / (k + 1) * ((1 + s) / (1 - s)) =
      2 * (1 - k * s) / ((k + 1) * (1 - s)) := by
    field_simp; ring
  rw [hden]
  have h2' : (2 : 𝕜) * (1 - k * s) ≠ 0 := mul_ne_zero two_ne_zero h2
  field_simp
  ring

/-- [proved-derived; formal-checked] The boost's velocity reads the clock back: `(1 + a)/(1 − a) = k`. -/
theorem halfRapidity_ratio (k : 𝕜) (hk : k + 1 ≠ 0) :
    (1 + halfRapidity k) / (1 - halfRapidity k) = k := by
  unfold halfRapidity
  have h2 : (1 : 𝕜) - (k - 1) / (k + 1) = 2 / (k + 1) := by field_simp; ring
  rw [h2]
  field_simp
  ring

/-- [proved-derived; formal-checked] The relativistic velocity of the boost: `2a/(1 + a²) = (k² − 1)/(k² + 1)`. -/
theorem halfRapidity_velocity (k : 𝕜) (hk : k + 1 ≠ 0) (hk2 : k ^ 2 + 1 ≠ 0) :
    2 * halfRapidity k / (1 + halfRapidity k ^ 2) = (k ^ 2 - 1) / (k ^ 2 + 1) := by
  unfold halfRapidity
  have h1 : (1 : 𝕜) + ((k - 1) / (k + 1)) ^ 2 = 2 * (k ^ 2 + 1) / (k + 1) ^ 2 := by field_simp; ring
  rw [h1]
  field_simp
  ring

end Cayley

/-- [proved-standard; formal-checked] The Cayley chart takes the open left half plane into the open unit disk:
a decaying line is a stable multiplier. -/
theorem cayley_normSq_lt_one {s : ℂ} (hs : s.re < 0) : Complex.normSq (cayley s) < 1 := by
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hpos : 0 < Complex.normSq (1 - s) := Complex.normSq_pos.mpr hne
  rw [cayley, Complex.normSq_div, div_lt_one hpos]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  nlinarith

/-! ## 3. Disk motions keep the horizon and the shape -/

/-- [definition] A motion of the unit disk, `φ(z) = u (z − c)/(1 − c̄ z)`. -/
noncomputable def diskMotion (u c z : ℂ) : ℂ := u * (z - c) / (1 - conj c * z)

/-- [definition] The squared pseudo-hyperbolic distance `δ(a, b)² = |a − b|²/|1 − āb|²`. -/
noncomputable def pseudoHyperbolicSq (a b : ℂ) : ℝ :=
  Complex.normSq (a - b) / Complex.normSq (1 - conj a * b)

/-- [proved-standard; formal-checked] The numerator identity `|1 − c̄a|² − |a − c|² = (1 − |a|²)(1 − |c|²)`. -/
theorem normSq_one_sub_conj_mul_sub (a c : ℂ) :
    Complex.normSq (1 - conj c * a) - Complex.normSq (a - c) =
      (1 - Complex.normSq a) * (1 - Complex.normSq c) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- [proved-standard; formal-checked] **No basin crosses the horizon.**
`1 − |φ(a)|² = (1 − |a|²)(1 − |c|²)/|1 − c̄a|²` for every disk motion `φ`. -/
theorem one_sub_normSq_diskMotion (u c a : ℂ) (hu : Complex.normSq u = 1)
    (hca : 1 - conj c * a ≠ 0) :
    1 - Complex.normSq (diskMotion u c a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq c) / Complex.normSq (1 - conj c * a) := by
  have hpos : Complex.normSq (1 - conj c * a) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [diskMotion, Complex.normSq_div, Complex.normSq_mul, hu, one_mul,
    ← normSq_one_sub_conj_mul_sub, eq_div_iff hpos, sub_mul, div_mul_cancel₀ _ hpos, one_mul]

/-- [proved-standard; formal-checked] The difference of two moved basins. -/
theorem diskMotion_sub (u c a b : ℂ) (ha : 1 - conj c * a ≠ 0) (hb : 1 - conj c * b ≠ 0) :
    diskMotion u c a - diskMotion u c b =
      u * (1 - c * conj c) * (a - b) / ((1 - conj c * a) * (1 - conj c * b)) := by
  unfold diskMotion
  rw [div_sub_div _ _ ha hb]
  congr 1
  ring

/-- [proved-standard; formal-checked] The pairing of two moved basins. -/
theorem conj_diskMotion_mul (u c a b : ℂ) :
    conj (diskMotion u c a) * diskMotion u c b =
      (u * conj u) * ((conj a - conj c) * (b - c)) / ((1 - c * conj a) * (1 - conj c * b)) := by
  unfold diskMotion
  rw [map_div₀, div_mul_div_comm]
  congr 1
  · simp only [map_mul, map_sub]
    ring
  · simp only [map_sub, map_mul, map_one, Complex.conj_conj]

/-- [proved-standard; formal-checked] `1 − conj(φa)·φb = (1 − |c|²)(1 − āb)/((1 − cā)(1 − c̄b))`. -/
theorem one_sub_conj_diskMotion_mul (u c a b : ℂ) (hu : Complex.normSq u = 1)
    (ha : 1 - conj c * a ≠ 0) (hb : 1 - conj c * b ≠ 0) :
    1 - conj (diskMotion u c a) * diskMotion u c b =
      (1 - c * conj c) * (1 - conj a * b) / ((1 - c * conj a) * (1 - conj c * b)) := by
  have huu : u * conj u = 1 := by rw [Complex.mul_conj, hu, Complex.ofReal_one]
  have ha' : 1 - c * conj a ≠ 0 := by
    intro h
    apply ha
    have := congrArg conj h
    simpa [mul_comm] using this
  rw [conj_diskMotion_mul, huu, one_mul, one_sub_div (mul_ne_zero ha' hb)]
  congr 1
  ring

/-- [proved-standard; formal-checked] **The shape is invariant.** Every motion of the disk with `|c| ≠ 1` keeps
`δ(a, b)² = |a − b|²/|1 − āb|²`. -/
theorem pseudoHyperbolicSq_diskMotion (u c a b : ℂ) (hu : Complex.normSq u = 1)
    (hc : Complex.normSq c ≠ 1) (ha : 1 - conj c * a ≠ 0) (hb : 1 - conj c * b ≠ 0) :
    pseudoHyperbolicSq (diskMotion u c a) (diskMotion u c b) = pseudoHyperbolicSq a b := by
  unfold pseudoHyperbolicSq
  rw [diskMotion_sub u c a b ha hb, one_sub_conj_diskMotion_mul u c a b hu ha hb]
  have hconj : 1 - c * conj a = conj (1 - conj c * a) := by simp [mul_comm]
  rw [hconj]
  simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_conj, hu, one_mul]
  have hN : Complex.normSq (1 - c * conj c) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero, Complex.mul_conj, sub_eq_zero]
    intro h
    apply hc
    exact_mod_cast h.symm
  have hA : Complex.normSq (1 - conj c * a) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hB : Complex.normSq (1 - conj c * b) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  by_cases hY : Complex.normSq (1 - conj a * b) = 0
  · simp [hY]
  · field_simp

/-- [proved-standard; formal-checked] Moving `a` to the centre puts `b` at distance `δ(a, b)`:
`δ(a, b)² = |φ_a(b)|²`. -/
theorem pseudoHyperbolicSq_eq_normSq_motion (a b : ℂ) :
    pseudoHyperbolicSq a b = Complex.normSq (diskMotion 1 a b) := by
  rw [pseudoHyperbolicSq, diskMotion, one_mul, Complex.normSq_div, ← Complex.normSq_neg (a - b),
    neg_sub]

/-! ## 4. The basin's residence is a Doppler factor -/

/-- [definition] The lossless response of a basin at `a`, `H_a(z) = (1 − āz)/(z − a)`. -/
noncomputable def basinResponse (a z : ℂ) : ℂ := (1 - conj a * z) / (z - a)

/-- [proved-standard; formal-checked] `H_a′(z) = (|a|² − 1)/(z − a)²` away from the basin. -/
theorem hasDerivAt_basinResponse (a z : ℂ) (hz : z ≠ a) :
    HasDerivAt (basinResponse a) ((a * conj a - 1) / (z - a) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-(conj a)) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_sub 1
  have h2 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  have h3 := h1.div h2 hza
  have e : (a * conj a - 1) / (z - a) ^ 2 =
      (-(conj a) * (z - a) - (1 - conj a * z) * 1) / (z - a) ^ 2 := by
    rw [div_left_inj' (pow_ne_zero 2 hza)]
    ring
  rw [e]
  exact h3

/-- [proved-derived; formal-checked] **The basin's group delay is the Poisson kernel.** On the unit circle,
`−Re(z H_a′/H_a) = (1 − |a|²)/|z − a|²`. -/
theorem groupDelay_basin (a z : ℂ) (hz : Complex.normSq z = 1) (hza : z ≠ a) :
    -(z * deriv (basinResponse a) z / basinResponse a z).re =
      (1 - Complex.normSq a) / Complex.normSq (z - a) := by
  rw [(hasDerivAt_basinResponse a z hza).deriv]
  have hzc : z * conj z = 1 := by rw [Complex.mul_conj, hz, Complex.ofReal_one]
  have key : 1 - conj a * z = z * conj (z - a) := by
    rw [map_sub, mul_sub, hzc]
    ring
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hc : conj (z - a) ≠ 0 := (map_ne_zero _).mpr hza'
  have e : z * ((a * conj a - 1) / (z - a) ^ 2) / basinResponse a z =
      (((Complex.normSq a - 1) / Complex.normSq (z - a) : ℝ) : ℂ) := by
    unfold basinResponse
    rw [key]
    push_cast
    rw [← Complex.mul_conj a, ← Complex.mul_conj (z - a)]
    field_simp
  rw [e, Complex.ofReal_re]
  ring

/-- [proved-standard; formal-checked] `|e^(iω) − a|² = 1 − 2a cos ω + a²` for real `a`. -/
theorem normSq_exp_sub_ofReal (a ω : ℝ) :
    Complex.normSq (Complex.exp (ω * Complex.I) - a) = 1 - 2 * a * Real.cos ω + a ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  linear_combination Real.sin_sq_add_cos_sq ω

/-- [proved-standard; formal-checked] The real basin's circle never meets it: `1 − 2a cos ω + a² > 0` for `|a| < 1`. -/
theorem one_sub_two_mul_cos_add_sq_pos {a : ℝ} (ha : |a| < 1) (ω : ℝ) :
    0 < 1 - 2 * a * Real.cos ω + a ^ 2 := by
  have hc : a * Real.cos ω ≤ |a| := by
    calc a * Real.cos ω ≤ |a * Real.cos ω| := le_abs_self _
      _ = |a| * |Real.cos ω| := abs_mul _ _
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ω) (abs_nonneg a)
      _ = |a| := mul_one _
  have h0 : 0 ≤ |a| := abs_nonneg a
  have hsq : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  nlinarith

/-- [definition] The relativistic velocity of a real basin, `β = 2a/(1 + a²)`. -/
noncomputable def basinVelocity (a : ℝ) : ℝ := 2 * a / (1 + a ^ 2)

/-- [proved-derived; formal-checked] `√(1 − β²) = (1 − a²)/(1 + a²)` for `|a| ≤ 1`. -/
theorem sqrt_one_sub_basinVelocity_sq {a : ℝ} (ha : |a| ≤ 1) :
    Real.sqrt (1 - basinVelocity a ^ 2) = (1 - a ^ 2) / (1 + a ^ 2) := by
  have hpos : 0 < 1 + a ^ 2 := by positivity
  have hnn : 0 ≤ (1 - a ^ 2) / (1 + a ^ 2) := by
    apply div_nonneg _ hpos.le
    have : a ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg a]
    linarith
  rw [← Real.sqrt_sq hnn]
  congr 1
  unfold basinVelocity
  field_simp
  ring

/-- [proved-derived; formal-checked] **The Doppler form.** For real `|a| < 1`, the Poisson face
`(1 − a²)/|e^(iω) − a|²` is `√(1 − β²)/(1 − β cos ω)`, `β = 2a/(1 + a²)`. -/
theorem poisson_doppler {a : ℝ} (ha : |a| < 1) (ω : ℝ) :
    (1 - a ^ 2) / Complex.normSq (Complex.exp (ω * Complex.I) - a) =
      Real.sqrt (1 - basinVelocity a ^ 2) / (1 - basinVelocity a * Real.cos ω) := by
  rw [normSq_exp_sub_ofReal, sqrt_one_sub_basinVelocity_sq ha.le]
  have hpos : 0 < 1 + a ^ 2 := by positivity
  have hd := one_sub_two_mul_cos_add_sq_pos ha ω
  have hd' : 1 - basinVelocity a * Real.cos ω = (1 - 2 * a * Real.cos ω + a ^ 2) / (1 + a ^ 2) := by
    unfold basinVelocity
    field_simp
    ring
  rw [hd', div_div_div_cancel_right₀ hpos.ne']

/-- [proved-derived; formal-checked] **The basin's delay at angle `ω` is the Doppler factor of the boost `β`.** -/
theorem groupDelay_basin_doppler {a : ℝ} (ha : |a| < 1) (ω : ℝ) :
    -(Complex.exp (ω * Complex.I) * deriv (basinResponse a) (Complex.exp (ω * Complex.I)) /
        basinResponse a (Complex.exp (ω * Complex.I))).re =
      Real.sqrt (1 - basinVelocity a ^ 2) / (1 - basinVelocity a * Real.cos ω) := by
  have hz : Complex.normSq (Complex.exp (ω * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hza : Complex.exp (ω * Complex.I) ≠ a := by
    intro h
    have h2 := hz
    rw [h, Complex.normSq_ofReal] at h2
    have : |a| * |a| = 1 := by rw [← abs_mul, h2, abs_one]
    nlinarith [abs_nonneg a]
  rw [groupDelay_basin _ _ hz hza, Complex.normSq_ofReal, ← sq, poisson_doppler ha]

/-- [proved-derived; formal-checked] **Peak, trough and the Lorentz factor.** For real `|a| < 1` with
`k = (1 + a)/(1 − a)`: the delay is `k` at the basin's own line (`ω = 0`), `1/k` opposite (`ω = π`), and
`(k + 1/k)/2 = 1/√(1 − β²)`. -/
theorem doppler_peak_trough {a : ℝ} (ha : |a| < 1) :
    (1 - a ^ 2) / (1 - 2 * a + a ^ 2) = (1 + a) / (1 - a) ∧
    (1 - a ^ 2) / (1 + 2 * a + a ^ 2) = 1 / ((1 + a) / (1 - a)) ∧
    ((1 + a) / (1 - a) + 1 / ((1 + a) / (1 - a))) / 2 = 1 / Real.sqrt (1 - basinVelocity a ^ 2) := by
  have h1 : 0 < 1 - a := by linarith [neg_abs_le a, le_abs_self a]
  have h2 : 0 < 1 + a := by linarith [neg_abs_le a, le_abs_self a]
  rw [sqrt_one_sub_basinVelocity_sq ha.le]
  refine ⟨?_, ?_, ?_⟩
  · have : 1 - 2 * a + a ^ 2 = (1 - a) ^ 2 := by ring
    rw [this]
    field_simp
    ring
  · have : 1 + 2 * a + a ^ 2 = (1 + a) ^ 2 := by ring
    rw [this]
    field_simp
    ring
  · have h3 : (1 - a ^ 2) ≠ 0 := by nlinarith
    field_simp
    ring

/-! ## 5. A ring of `N` channels -/

/-- [proved-standard; formal-checked] The power sums of the `N`-th roots of unity vanish strictly between `0` and
`N`. -/
theorem sum_range_pow_primitive {N m : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω N) (hm0 : m ≠ 0)
    (hm : m < N) : ∑ k ∈ range N, (ω ^ k) ^ m = 0 := by
  have hne : ω ^ m ≠ 1 := hω.pow_ne_one_of_pos_of_lt hm0 hm
  have e : ∀ k, (ω ^ k) ^ m = (ω ^ m) ^ k := fun k => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [e]
  rw [geom_sum_eq hne, ← pow_mul, mul_comm m N, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]

/-- [proved-derived; formal-checked] **The logarithmic derivative of `z^N − 1` at a point off the ring:**
`Σ_k 1/(a − ω^k) = N a^(N−1)/(a^N − 1)`, read without calculus through `a^N − ζ^N = (a − ζ) Σ_i a^i ζ^(N−1−i)`. -/
theorem sum_inv_sub_roots {N : ℕ} (hN : 0 < N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) {a : ℂ}
    (ha : a ^ N ≠ 1) :
    ∑ k ∈ range N, 1 / (a - ω ^ k) = N * a ^ (N - 1) / (a ^ N - 1) := by
  have hden : a ^ N - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hterm : ∀ k ∈ range N, 1 / (a - ω ^ k) =
      (∑ i ∈ range N, a ^ i * (ω ^ k) ^ (N - 1 - i)) / (a ^ N - 1) := by
    intro k _
    have hζN : (ω ^ k) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hg := geom_sum₂_mul a (ω ^ k) N
    rw [hζN] at hg
    have hne : a - ω ^ k ≠ 0 := by
      intro h
      apply ha
      rw [sub_eq_zero.mp h, hζN]
    have hS : ∑ i ∈ range N, a ^ i * (ω ^ k) ^ (N - 1 - i) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hg
      exact hden hg.symm
    rw [← hg, div_mul_cancel_left₀ hS, one_div]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_comm]
  congr 1
  rw [Finset.sum_eq_single (N - 1)]
  · simp only [Nat.sub_self, pow_zero, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro i hi hne
    have hi' : i < N := Finset.mem_range.mp hi
    rw [← Finset.mul_sum, sum_range_pow_primitive hω (by omega) (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- [proved-standard; formal-checked] On the unit circle the Poisson face is the real part of `(ζ + a)/(ζ − a)`. -/
theorem poisson_eq_re (ζ a : ℂ) (hζ : Complex.normSq ζ = 1) :
    (1 - Complex.normSq a) / Complex.normSq (ζ - a) = ((ζ + a) / (ζ - a)).re := by
  rw [Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] at hζ ⊢
  linear_combination (-1 : ℝ) * hζ

/-- [proved-derived; formal-checked] **The ring sum over a primitive root's powers.** -/
theorem ring_sum_range {N : ℕ} (hN : 0 < N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) {a : ℂ}
    (ha : a ^ N ≠ 1) :
    ∑ k ∈ range N, (1 - Complex.normSq a) / Complex.normSq (ω ^ k - a) =
      N * ((1 + a ^ N) / (1 - a ^ N)).re := by
  have hrootN : ∀ k, (ω ^ k) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hroot : ∀ k, Complex.normSq (ω ^ k) = 1 := fun k => by
    have h := congrArg Complex.normSq (hrootN k)
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) hN.ne').mp h
  have hne : ∀ k, ω ^ k - a ≠ 0 := fun k h => ha (by rw [← sub_eq_zero.mp h, hrootN])
  have hne' : ∀ k, a - ω ^ k ≠ 0 := fun k h => ha (by rw [sub_eq_zero.mp h, hrootN])
  have h1N : (1 : ℂ) - a ^ N ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hN1 : a ^ N - 1 ≠ 0 := sub_ne_zero.mpr ha
  rw [Finset.sum_congr rfl (fun k _ => poisson_eq_re _ _ (hroot k)), ← Complex.re_sum]
  have hsplit : ∀ k ∈ range N, (ω ^ k + a) / (ω ^ k - a) = 1 - 2 * a * (1 / (a - ω ^ k)) := by
    intro k _
    have := hne k
    have := hne' k
    field_simp
    ring
  have hsum : ∑ k ∈ range N, (ω ^ k + a) / (ω ^ k - a) = N * ((1 + a ^ N) / (1 - a ^ N)) := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_inv_sub_roots hN hω ha, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hpow : a * a ^ (N - 1) = a ^ N := by
      rw [← pow_succ']
      congr 1
      omega
    have e1 : (N : ℂ) - 2 * a * (N * a ^ (N - 1) / (a ^ N - 1)) =
        N - 2 * N * (a * a ^ (N - 1)) / (a ^ N - 1) := by ring
    rw [e1, hpow]
    field_simp
    ring
  rw [hsum]
  simp [Complex.mul_re]

/-- [proved-standard; formal-checked] The `N`-th roots of unity are the powers of any primitive one. -/
theorem sum_nthRootsFinset_eq_sum_range {β : Type*} [AddCommMonoid β] {N : ℕ} (hN : 0 < N) {ω : ℂ}
    (hω : IsPrimitiveRoot ω N) (f : ℂ → β) :
    ∑ ζ ∈ Polynomial.nthRootsFinset N (1 : ℂ), f ζ = ∑ k ∈ range N, f (ω ^ k) := by
  have hinj : Set.InjOn (fun k => ω ^ k) (range N : Set ℕ) := by
    intro i hi j hj h
    exact hω.pow_inj (by simpa using hi) (by simpa using hj) h
  have himg : Polynomial.nthRootsFinset N (1 : ℂ) = (range N).image (fun k => ω ^ k) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset hN]
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [hω.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [himg, Finset.sum_image hinj]

/-- [proved-derived; formal-checked] **A ring of `N` channels reads a basin through `a^N`:**
`Σ_(ζ^N = 1) (1 − |a|²)/|ζ − a|² = N·Re((1 + a^N)/(1 − a^N))` whenever `a^N ≠ 1`. -/
theorem ring_sum {N : ℕ} (hN : 0 < N) {a : ℂ} (ha : a ^ N ≠ 1) :
    ∑ ζ ∈ Polynomial.nthRootsFinset N (1 : ℂ), (1 - Complex.normSq a) / Complex.normSq (ζ - a) =
      N * ((1 + a ^ N) / (1 - a ^ N)).re := by
  have hω := Complex.isPrimitiveRoot_exp N hN.ne'
  rw [sum_nthRootsFinset_eq_sum_range hN hω, ring_sum_range hN hω ha]

/-- [proved-derived; formal-checked] The ring sum for a basin inside the disk. -/
theorem ring_sum_of_normSq_lt_one {N : ℕ} (hN : 0 < N) {a : ℂ} (ha : Complex.normSq a < 1) :
    ∑ ζ ∈ Polynomial.nthRootsFinset N (1 : ℂ), (1 - Complex.normSq a) / Complex.normSq (ζ - a) =
      N * ((1 + a ^ N) / (1 - a ^ N)).re := by
  apply ring_sum hN
  intro h
  have h2 := congrArg Complex.normSq h
  rw [map_pow, map_one] at h2
  have := pow_lt_one₀ (Complex.normSq_nonneg a) ha hN.ne'
  linarith

/-! ## 6. The receiver's own mass along a reading -/

section Reading

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] The leverage of a reading `v` against a receiver's Gram `G`, `h = vᵀG⁻¹v`. -/
noncomputable def leverage (G : Matrix n n 𝕜) (v : n → 𝕜) : 𝕜 := v ⬝ᵥ (G⁻¹ *ᵥ v)

/-- [proved-derived; formal-checked] **One reading adds one unit of mass.** With `G′ = G + vvᵀ`, `h′(1 + h) = h`. -/
theorem leverage_add_reading (G : Matrix n n 𝕜) (v : n → 𝕜) (hG : IsUnit G.det)
    (hG' : IsUnit (G + vecMulVec v v).det) :
    leverage (G + vecMulVec v v) v * (1 + leverage G v) = leverage G v := by
  set w := (G + vecMulVec v v)⁻¹ *ᵥ v with hwdef
  have hw : (G + vecMulVec v v) *ᵥ w = v := by
    rw [hwdef, mulVec_mulVec, mul_nonsing_inv _ hG', one_mulVec]
  rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul] at hw
  have hGw : G *ᵥ w = (1 - v ⬝ᵥ w) • v := by
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq hw
  have hw' : w = (1 - v ⬝ᵥ w) • (G⁻¹ *ᵥ v) := by
    have := congrArg (fun x => G⁻¹ *ᵥ x) hGw
    simp only [mulVec_mulVec, nonsing_inv_mul _ hG, one_mulVec, mulVec_smul] at this
    exact this
  have e : v ⬝ᵥ w = (1 - v ⬝ᵥ w) * v ⬝ᵥ (G⁻¹ *ᵥ v) := by
    conv_lhs => rw [hw']
    rw [dotProduct_smul, smul_eq_mul]
  show v ⬝ᵥ w * (1 + v ⬝ᵥ (G⁻¹ *ᵥ v)) = v ⬝ᵥ (G⁻¹ *ᵥ v)
  linear_combination e

/-- [proved-derived; formal-checked] **The reading's mass:** `1/h′ = 1/h + 1`. -/
theorem inv_leverage_add_reading (G : Matrix n n 𝕜) (v : n → 𝕜) (hG : IsUnit G.det)
    (hG' : IsUnit (G + vecMulVec v v).det) (hh : leverage G v ≠ 0) :
    1 / leverage (G + vecMulVec v v) v = 1 / leverage G v + 1 := by
  have e := leverage_add_reading G v hG hG'
  have h1 : 1 + leverage G v ≠ 0 := by
    intro h
    rw [h, mul_zero] at e
    exact hh e.symm
  have h2 : leverage (G + vecMulVec v v) v ≠ 0 := by
    intro h
    rw [h, zero_mul] at e
    exact hh e.symm
  field_simp
  linear_combination (-1 : 𝕜) * e

/-- [proved-derived; formal-checked] **The barycentric share.** `h′ = h/(1 + h) = m/(M + m)` with `m = 1`,
`M = 1/h`. -/
theorem leverage_add_reading_eq (G : Matrix n n 𝕜) (v : n → 𝕜) (hG : IsUnit G.det)
    (hG' : IsUnit (G + vecMulVec v v).det) (hh : leverage G v ≠ 0) :
    leverage (G + vecMulVec v v) v = leverage G v / (1 + leverage G v) ∧
      leverage G v / (1 + leverage G v) = 1 / (1 / leverage G v + 1) := by
  have e := leverage_add_reading G v hG hG'
  have h1 : 1 + leverage G v ≠ 0 := by
    intro h
    rw [h, mul_zero] at e
    exact hh e.symm
  refine ⟨eq_div_of_mul_eq h1 e, ?_⟩
  field_simp

/-- [proved-derived; formal-checked] **The receiver moves by the share.** The solution `w′` of `G′w′ = b + yv`
predicts, along `v`, `h′` of the residual beyond the solution `w` of `Gw = b`: `vᵀw′ − vᵀw = h′(y − vᵀw)`. -/
theorem reading_share (G : Matrix n n 𝕜) (v b : n → 𝕜) (y : 𝕜) (hG : IsUnit G.det)
    (hG' : IsUnit (G + vecMulVec v v).det) :
    v ⬝ᵥ ((G + vecMulVec v v)⁻¹ *ᵥ (b + y • v)) - v ⬝ᵥ (G⁻¹ *ᵥ b) =
      leverage (G + vecMulVec v v) v * (y - v ⬝ᵥ (G⁻¹ *ᵥ b)) := by
  set u := v ᵥ* (G + vecMulVec v v)⁻¹ with hudef
  have hu : u ᵥ* (G + vecMulVec v v) = v := by
    rw [hudef, vecMul_vecMul, nonsing_inv_mul _ hG', vecMul_one]
  rw [vecMul_add, vecMul_vecMulVec] at hu
  have huG : u ᵥ* G = (1 - u ⬝ᵥ v) • v := by
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq hu
  have hu' : u = (1 - u ⬝ᵥ v) • (v ᵥ* G⁻¹) := by
    have := congrArg (fun x => x ᵥ* G⁻¹) huG
    simp only [vecMul_vecMul, mul_nonsing_inv _ hG, vecMul_one, smul_vecMul] at this
    exact this
  have hlev : leverage (G + vecMulVec v v) v = u ⬝ᵥ v := by
    rw [leverage, dotProduct_mulVec]
  have hb : v ⬝ᵥ ((G + vecMulVec v v)⁻¹ *ᵥ b) = (1 - u ⬝ᵥ v) * v ⬝ᵥ (G⁻¹ *ᵥ b) := by
    rw [dotProduct_mulVec, ← hudef]
    conv_lhs => rw [hu']
    rw [smul_dotProduct, smul_eq_mul, dotProduct_mulVec]
  rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hb, hlev,
    ← leverage, hlev]
  ring

/-- [proved-derived; formal-checked] The record's witness: leverage `215/209` becomes `215/424` after one reading. -/
theorem reading_share_witness : (215 / 209 : ℚ) / (1 + 215 / 209) = 215 / 424 ∧
    1 / (215 / 424 : ℚ) = 1 / (215 / 209) + 1 := by
  norm_num

end Reading

end Holonics.Transport.InformationSpectroscopy
