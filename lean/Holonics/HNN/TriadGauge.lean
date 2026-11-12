import Mathlib

/-!
# HNN.TriadGauge: a triad's legs and return share a gauge, and its legs exchange equal quanta

[definition] Triad `k` at a place `t` with both strand mates in the region
(`contact.triad-manley-rowe-gauge`; `Field`'s tick in `crates/holonics/src/hnn/tower/field.rs`; the
triad record `2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT…` §3 and §4) reads three
legs from the place's pair chart `r̂` and is returned through its own column `w_k` of `W_T`:

```text
α(t) = A r̂(t) + α_b,   β(t) = B r̂(t) + β_b,   γ(t) = G r̂(t) + γ_b
c^T_k(t) = α_k(t) β_k(t − 1) γ_k(t + 1),   x_t ← x_t + release(W c_t + W_T c^T_t + w_b 2^M, M)
```

(each product released at the face's grain). The return's term of triad `k` is `w_k α_k β_k γ_k`, so
scaling the three legs by `λ, μ, ν ∈ ℂˣ` and the column by `(λ μ ν)⁻¹` leaves it: six real directions
a triad that no receiver distinguishes. Differentiating that invariance at the identity, a loss read
through the return has `Re⟨α_k, ∇_α ℓ⟩ = Re⟨w_k, ∇_w ℓ⟩` (and the same for `β` and `γ`, and for each
leg's turn): the legs and the return are one family that no receiver tells apart, and their
covectors keep this scale identity at every state. Under a plain step at one rate it gives each leg
the same squared norm to first order: the Manley–Rowe relation of three-wave mixing, each wave
gaining or losing the same count of quanta. The field's learner divides each entry's step by its own
`⌊√v⌋ + 1` (`deposit_step` in `crates/holonics/src/hnn/tower.rs`): at fixed divisors `s` its step keeps
`Σ s_i |a_i|² − Σ s_j |w_j|²` to first order instead (`conserved_weighted_rows`), and its divisors
move with what reaches each entry, so equal gains of the legs are no prediction for it. The triad's
charts and return stay one part at one octave because an octave between the legs would be a rate set
by hand.

[proved-derived; formal-checked] What is proved.

1. **The gauge** (`triad_gauge`): `(λα)(μβ)(νγ)((λμν)⁻¹ w) = αβγw` for complex values and nonzero
   `λ, μ, ν`.
2. **The quarter-turn is exact on Gaussian integers** (`contact_mul_re`, `contact_mul_im`,
   `quarterTurn_re`, `quarterTurn_im`, `quarterBack_re`, `quarterBack_im`,
   `sqrtd_mul_neg_sqrtd`, `quarterTurn_mul`, `release_quarterTurn`): the plain contact's product on a
   complex pair's integer parts is the Gaussian integers' product; `i a` and `−i b` move the parts by a
   swap with a sign (a row permutation with a sign of the material, no release); and
   `(i a)(−i b) = a b`, so the release of the product is unchanged whatever the release.
3. **The scale identity** (`scale_identity`): a loss constant along `(s α, w / s)` for real `s ≠ 0`,
   whose derivative along that path at `s = 1` is the gradients' reading
   `Re(conj(g_α) α) − Re(conj(g_w) w)` (the chain rule through the path's velocity `(α, −w)`), has
   `Re(conj(g_α) α) = Re(conj(g_w) w)`. **The turn identity** (`turn_identity`): the same along
   `(e^(iθ) α, e^(−iθ) w)`, velocity `(iα, −iw)`, gives `Im(conj(g_α) α) = Im(conj(g_w) w)`.
4. **The conserved difference at one rate** (`normSq_step`, `step_change`, `conserved_at_one_rate`,
   `normSq_step_sum`, `conserved_rows`): one step `α − η g_α`, `w − η g_w` at one rate `η` changes
   `|α|² − |w|²` by `−2η (Re(conj(g_α) α) − Re(conj(g_w) w)) + η² (|g_α|² − |g_w|²)`, so under the
   scale identity by `η² (|g_α|² − |g_w|²)` with no first-order term; and the same for a leg's whole row
   and its return's column (finite families of entries, the identity summed over the row).
5. **The learner's form at fixed divisors** (`conserved_weighted_rows`): with a nonzero real divisor
   `s_i` on each entry, the step `a_i − (η / s_i) g_a,i`, `w_j − (η / s_j) g_w,j` changes
   `Σ s_i |a_i|² − Σ s_j |w_j|²` by `η² (Σ |g_a,i|² / s_i − Σ |g_w,j|² / s_j)` under the summed scale
   identity, with no first-order term. It is a form of the legs only while the divisors stand.

The host's tests read the realization's integers (the quarter-turn on `A`'s and `B`'s rows and biases
leaves every face bit for bit; the reverse against the code's change along a direction).
-/

namespace Holonics.HNN.TriadGauge

open Complex ComplexConjugate

/-! ## The gauge -/

/-- [proved-derived; formal-checked] **The gauge**: scaling a triad's three legs by `l, m, n ∈ ℂˣ` and
its return column by `(l m n)⁻¹` leaves the return's term, `(l a)(m b)(n c)((l m n)⁻¹ w) = a b c w`. -/
theorem triad_gauge (a b c w l m n : ℂ) (hl : l ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    l * a * (m * b) * (n * c) * ((l * m * n)⁻¹ * w) = a * b * c * w := by
  have h : l * m * n ≠ 0 := mul_ne_zero (mul_ne_zero hl hm) hn
  calc l * a * (m * b) * (n * c) * ((l * m * n)⁻¹ * w)
      = l * m * n * (l * m * n)⁻¹ * (a * b * c * w) := by ring
    _ = a * b * c * w := by rw [mul_inv_cancel₀ h, one_mul]

/-! ## The quarter-turn on Gaussian integers -/

/-- [proved-derived; formal-checked] **The plain contact's product is the Gaussian integers'**, real
part: `re = a_r b_r − a_i b_i`, as the realization forms it on a complex pair's integer parts. -/
theorem contact_mul_re (a b : GaussianInt) : (a * b).re = a.re * b.re - a.im * b.im := by
  first
    | (rw [Zsqrtd.re_mul]; ring)
    | (simp; ring)
    | simp [sub_eq_add_neg]

/-- [proved-derived; formal-checked] **The plain contact's product is the Gaussian integers'**,
imaginary part: `im = a_r b_i + a_i b_r`. -/
theorem contact_mul_im (a b : GaussianInt) : (a * b).im = a.re * b.im + a.im * b.re := by
  first
    | exact Zsqrtd.im_mul a b
    | simp

/-- [proved-derived; formal-checked] **The quarter-turn moves the parts exactly**: `i a` has real part
`−a_i`. -/
theorem quarterTurn_re (a : GaussianInt) : (Zsqrtd.sqrtd * a).re = -a.im := by
  first
    | (rw [Zsqrtd.re_mul, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]; ring)
    | simp

/-- [proved-derived; formal-checked] **The quarter-turn moves the parts exactly**: `i a` has imaginary
part `a_r`. -/
theorem quarterTurn_im (a : GaussianInt) : (Zsqrtd.sqrtd * a).im = a.re := by
  first
    | (rw [Zsqrtd.im_mul, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]; ring)
    | simp

/-- [proved-derived; formal-checked] **The back quarter-turn moves the parts exactly**: `−i b` has real
part `b_i`. -/
theorem quarterBack_re (b : GaussianInt) : ((-Zsqrtd.sqrtd) * b).re = b.im := by
  first
    | (rw [Zsqrtd.re_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]; ring)
    | simp

/-- [proved-derived; formal-checked] **The back quarter-turn moves the parts exactly**: `−i b` has
imaginary part `−b_r`. -/
theorem quarterBack_im (b : GaussianInt) : ((-Zsqrtd.sqrtd) * b).im = -b.re := by
  first
    | (rw [Zsqrtd.im_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]; ring)
    | simp

/-- [proved-derived; formal-checked] **The two quarter-turns compose to one**: `i · (−i) = 1` on the
Gaussian integers. -/
theorem sqrtd_mul_neg_sqrtd : (Zsqrtd.sqrtd : GaussianInt) * (-Zsqrtd.sqrtd) = 1 := by
  apply Zsqrtd.ext
  · first
      | (rw [Zsqrtd.re_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd, Zsqrtd.re_one]; ring)
      | simp
  · first
      | (rw [Zsqrtd.im_mul, Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd, Zsqrtd.im_one]; ring)
      | simp

/-- [proved-derived; formal-checked] **The quarter-turn gauge on Gaussian integers**:
`(i a)(−i b) = a b`. -/
theorem quarterTurn_mul (a b : GaussianInt) :
    Zsqrtd.sqrtd * a * ((-Zsqrtd.sqrtd) * b) = a * b := by
  first
    | (rw [mul_mul_mul_comm, sqrtd_mul_neg_sqrtd, one_mul]; done)
    | (apply Zsqrtd.ext <;> simp <;> ring)

/-- [proved-derived; formal-checked] **So the release of the product is unchanged**: whatever the
release (a function of the product's integer parts), the quarter-turned pair releases what the pair
does. -/
theorem release_quarterTurn {X : Type*} (release : GaussianInt → X) (a b : GaussianInt) :
    release (Zsqrtd.sqrtd * a * ((-Zsqrtd.sqrtd) * b)) = release (a * b) := by
  rw [quarterTurn_mul]

/-! ## The scale and turn identities -/

/-- [proved-derived; formal-checked] **The scale identity**: let `ℓ` be a loss of a leg's value `a`
and its return's column `w`, constant along the gauge's path `(s a, w / s)` for every real `s ≠ 0`,
and let its derivative along that path at `s = 1` be the gradients' reading
`Re(conj(g_a) a) − Re(conj(g_w) w)` (the chain rule with the path's velocity `(a, −w)`, a gradient `g`
reading a direction `δ` as `Re(conj(g) δ)`). Then `Re(conj(g_a) a) = Re(conj(g_w) w)`. -/
theorem scale_identity (ℓ : ℂ → ℂ → ℝ) (a w ga gw : ℂ)
    (hconst : ∀ s : ℝ, s ≠ 0 → ℓ ((s : ℂ) * a) (w / (s : ℂ)) = ℓ a w)
    (hderiv : HasDerivAt (fun s : ℝ => ℓ ((s : ℂ) * a) (w / (s : ℂ)))
      ((conj ga * a).re - (conj gw * w).re) 1) :
    (conj ga * a).re = (conj gw * w).re := by
  have hev : (fun s : ℝ => ℓ ((s : ℂ) * a) (w / (s : ℂ))) =ᶠ[nhds (1 : ℝ)] fun _ => ℓ a w :=
    (eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0)).mono fun s hs => hconst s hs
  have h0 : HasDerivAt (fun s : ℝ => ℓ ((s : ℂ) * a) (w / (s : ℂ))) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (ℓ a w)).congr_of_eventuallyEq hev
  have h := hderiv.unique h0
  linarith

/-- [proved-derived; formal-checked] **The turn identity**: let `ℓ` be constant along the gauge's
phase path `(e^(iθ) a, e^(−iθ) w)` for every real `θ`, with its derivative at `θ = 0` the gradients'
reading through the path's velocity `(i a, −i w)`, `Re(conj(g_a) i a) + Re(conj(g_w) (−i w)) =
Im(conj(g_w) w) − Im(conj(g_a) a)`. Then each leg's turn equals its return's:
`Im(conj(g_a) a) = Im(conj(g_w) w)`. -/
theorem turn_identity (ℓ : ℂ → ℂ → ℝ) (a w ga gw : ℂ)
    (hconst : ∀ θ : ℝ, ℓ (Complex.exp ((θ : ℂ) * I) * a) (Complex.exp (-((θ : ℂ) * I)) * w) = ℓ a w)
    (hderiv : HasDerivAt (fun θ : ℝ => ℓ (Complex.exp ((θ : ℂ) * I) * a) (Complex.exp (-((θ : ℂ) * I)) * w))
      ((conj gw * w).im - (conj ga * a).im) 0) :
    (conj ga * a).im = (conj gw * w).im := by
  have hev : (fun θ : ℝ => ℓ (Complex.exp ((θ : ℂ) * I) * a) (Complex.exp (-((θ : ℂ) * I)) * w))
      =ᶠ[nhds (0 : ℝ)] fun _ => ℓ a w :=
    Filter.Eventually.of_forall hconst
  have h0 : HasDerivAt (fun θ : ℝ => ℓ (Complex.exp ((θ : ℂ) * I) * a) (Complex.exp (-((θ : ℂ) * I)) * w))
      0 0 :=
    (hasDerivAt_const (0 : ℝ) (ℓ a w)).congr_of_eventuallyEq hev
  have h := hderiv.unique h0
  linarith

/-! ## The legs exchange equal quanta at one rate -/

/-- [proved-derived; formal-checked] **One step of a value**: `|x − η g|² = |x|² − 2η Re(conj(g) x) +
η² |g|²` for a real rate `η`. -/
theorem normSq_step (x g : ℂ) (η : ℝ) :
    Complex.normSq (x - η * g) = Complex.normSq x - 2 * η * (conj g * x).re + η ^ 2 * Complex.normSq g := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- [proved-derived; formal-checked] **One step at one rate moves the difference of a leg and its
return**: `(|a − η g_a|² − |w − η g_w|²) − (|a|² − |w|²) = −2η (Re(conj(g_a) a) − Re(conj(g_w) w)) +
η² (|g_a|² − |g_w|²)`. -/
theorem step_change (a w ga gw : ℂ) (η : ℝ) :
    Complex.normSq (a - η * ga) - Complex.normSq (w - η * gw) - (Complex.normSq a - Complex.normSq w)
      = -2 * η * ((conj ga * a).re - (conj gw * w).re)
        + η ^ 2 * (Complex.normSq ga - Complex.normSq gw) := by
  rw [normSq_step, normSq_step]
  ring

/-- [proved-derived; formal-checked] **The conserved difference at one rate, to first order**: under
the scale identity `Re(conj(g_a) a) = Re(conj(g_w) w)`, one step at one rate `η` changes
`|a|² − |w|²` by `η² (|g_a|² − |g_w|²)`, with no first-order term. -/
theorem conserved_at_one_rate (a w ga gw : ℂ) (η : ℝ) (h : (conj ga * a).re = (conj gw * w).re) :
    Complex.normSq (a - η * ga) - Complex.normSq (w - η * gw) - (Complex.normSq a - Complex.normSq w)
      = η ^ 2 * (Complex.normSq ga - Complex.normSq gw) := by
  rw [step_change, h]
  ring

/-- [proved-derived; formal-checked] **One step of a row**: over a finite family of entries,
`Σ|x_i − η g_i|² = Σ|x_i|² − 2η Σ Re(conj(g_i) x_i) + η² Σ|g_i|²`. -/
theorem normSq_step_sum {n : ℕ} (x g : Fin n → ℂ) (η : ℝ) :
    ∑ i, Complex.normSq (x i - η * g i)
      = (∑ i, Complex.normSq (x i)) - 2 * η * (∑ i, (conj (g i) * x i).re)
        + η ^ 2 * (∑ i, Complex.normSq (g i)) := by
  first
    | (rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => normSq_step (x i) (g i) η)
    | simp only [normSq_step, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- [proved-derived; formal-checked] **The conserved difference of a leg's row and its return's
column at one rate**: with the scale identity summed over the leg's entries `a` and the column's
entries `w`, `Σ Re(conj(g_a,i) a_i) = Σ Re(conj(g_w,j) w_j)`, one step at one rate `η` changes
`Σ|a_i|² − Σ|w_j|²` by `η² (Σ|g_a,i|² − Σ|g_w,j|²)`, with no first-order term: each leg gains the
squared norm its return gains, the three legs alike. -/
theorem conserved_rows {n m : ℕ} (a ga : Fin n → ℂ) (w gw : Fin m → ℂ) (η : ℝ)
    (h : ∑ i, (conj (ga i) * a i).re = ∑ j, (conj (gw j) * w j).re) :
    (∑ i, Complex.normSq (a i - η * ga i)) - (∑ j, Complex.normSq (w j - η * gw j))
        - ((∑ i, Complex.normSq (a i)) - (∑ j, Complex.normSq (w j)))
      = η ^ 2 * ((∑ i, Complex.normSq (ga i)) - (∑ j, Complex.normSq (gw j))) := by
  rw [normSq_step_sum, normSq_step_sum]
  linear_combination (-2 * η) * h

/-- [proved-derived; formal-checked] **The learner's own form at fixed divisors, to first order**: with a nonzero real
divisor `s_i` on each of a leg's entries `a_i` and `s_j` on each of its return's entries `w_j`, and the
scale identity summed over the leg's entries and the column's, `Σ Re(conj(g_a,i) a_i) =
Σ Re(conj(g_w,j) w_j)`, the learner's step `a_i − (η / s_i) g_a,i`, `w_j − (η / s_j) g_w,j` changes
`Σ s_i |a_i|² − Σ s_j |w_j|²` by `η² (Σ |g_a,i|² / s_i − Σ |g_w,j|² / s_j)`, with no first-order term.
Each entry's term is `s |x − (η / s) g|² = s |x|² − 2η Re(conj(g) x) + η² |g|² / s`, whose first-order
part carries no divisor, so the scale identity cancels it whatever the divisors. The form weighs each
entry by its own divisor: it is not the difference of plain squared norms, and it is a form of the
legs only while the divisors stand. -/
theorem conserved_weighted_rows {n m : ℕ} (a ga : Fin n → ℂ) (sa : Fin n → ℝ) (w gw : Fin m → ℂ)
    (sw : Fin m → ℝ) (η : ℝ) (hsa : ∀ i, sa i ≠ 0) (hsw : ∀ j, sw j ≠ 0)
    (h : ∑ i, (conj (ga i) * a i).re = ∑ j, (conj (gw j) * w j).re) :
    (∑ i, sa i * Complex.normSq (a i - ((η / sa i : ℝ) : ℂ) * ga i))
        - (∑ j, sw j * Complex.normSq (w j - ((η / sw j : ℝ) : ℂ) * gw j))
        - ((∑ i, sa i * Complex.normSq (a i)) - (∑ j, sw j * Complex.normSq (w j)))
      = η ^ 2 * ((∑ i, Complex.normSq (ga i) / sa i) - (∑ j, Complex.normSq (gw j) / sw j)) := by
  -- One entry: `s |x − (η / s) g|² = s |x|² − 2η Re(conj(g) x) + η² (|g|² / s)` for `s ≠ 0`.
  have hentry : ∀ (x g : ℂ) (c : ℝ), c ≠ 0 →
      c * Complex.normSq (x - ((η / c : ℝ) : ℂ) * g)
        = c * Complex.normSq x - 2 * η * (conj g * x).re + η ^ 2 * (Complex.normSq g / c) := by
    intro x g c hc
    rw [normSq_step]
    have hinv : c * c⁻¹ = 1 := by
      first
        | exact mul_inv_cancel₀ hc
        | field_simp
    first
      | linear_combination (-2 * η * (conj g * x).re + η ^ 2 * Complex.normSq g * c⁻¹) * hinv
      | (field_simp; ring)
  -- A row: the entries' terms summed over a finite family.
  have hrow : ∀ (k : ℕ) (x g : Fin k → ℂ) (c : Fin k → ℝ), (∀ i, c i ≠ 0) →
      ∑ i, c i * Complex.normSq (x i - ((η / c i : ℝ) : ℂ) * g i)
        = (∑ i, c i * Complex.normSq (x i)) - 2 * η * (∑ i, (conj (g i) * x i).re)
          + η ^ 2 * (∑ i, Complex.normSq (g i) / c i) := by
    intro k x g c hc
    first
      | (rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
         exact Finset.sum_congr rfl fun i _ => hentry (x i) (g i) (c i) (hc i))
      | (rw [Finset.sum_congr rfl fun i _ => hentry (x i) (g i) (c i) (hc i)]
         simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum])
  rw [hrow n a ga sa hsa, hrow m w gw sw hsw]
  linear_combination (-2 * η) * h

end Holonics.HNN.TriadGauge
