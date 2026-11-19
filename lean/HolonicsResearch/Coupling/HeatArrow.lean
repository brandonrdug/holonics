import Mathlib

/-!
# A translation kernel stays positive under Gaussian damping and an exchange kernel under Gaussian sharpening, and each fails the other way on two points

Sources.  Atlas rows `coupling.reflected-positivity`, `coupling.reflection-choice-sign`,
`rh.palette-damping-no-go`, `rh.scale-window-off-line` and `rh.finite-weil-criterion`
(`docs/atlas/targets.tsv`); the Lean owner `Coupling/ReflectedPositivity` (the round-trip form
`form (reflection a) b`); the record of this pass (November 19).

The occasion.  A reader proposed that Weil positivity is reflection positivity across the seam
`u = 0`, kept by the sharpening `e^{+τu²}` through the Schur product and broken by damping.  The
sentence joins two positivities.  A kernel on the line can be read through the difference of two
points, `k (u − v)` (positive type, Bochner's), or through their sum, `k (u + v)` (the round trip
of the difference form through the reflection `u ↦ −u`: reflection positivity, Hankel's).  The
Gaussian factors the two opposite ways,

```text
e^{−t(u−v)²} = e^{−tu²} · e^{+2tuv} · e^{−tv²}        e^{+τ(u+v)²} = e^{τu²} · e^{+2τuv} · e^{τv²}
```

and the cross kernel `e^{c·u·v}` is positive for `c ≥ 0`.  So the heat clock has two arrows.

**What is proved.**

1. `Pos` [definition]: a real kernel on finitely many sites pairs every test vector with itself
   to a nonnegative number.  Its closure steps: `Pos.congr_diag` (a diagonal rescaling),
   `pos_rankOne`, `Pos.add`; its two-point reading `Pos.two_point`, with `Pos.diag_nonneg` and the
   Cauchy–Schwarz bound `Pos.sq_le` for a symmetric kernel.
2. `Pos.exp_cross` [proved-standard]: the Schur step for the cross kernel.  For `c ≥ 0` the
   kernel `e^{c·u_i·u_j} · M i j` is positive when `M` is, by the exponential's series: the term
   of order `n` is `cⁿ/n!` times `M` paired with the test vector `u_iⁿ x_i`.  This is the one case
   of the Schur product theorem the module needs; the general theorem is not stated.
3. `seam_split`, `translation_split`: the two factorizations displayed above.
4. `exchange_sharpen`, `translation_damp` [proved-standard]: on any finite family of points,
   sharpening keeps exchange positivity and damping keeps translation positivity.
5. `exchange_damp_fails`, `translation_sharpen_fails` [counterexample]: each fails the other way
   on the two points `0, 1` with the constant kernel, for every positive time.
6. `ExchangePositive`, `TranslationPositive` [definition]: the two laws of a kernel on the line;
   `exchangePositive_sharpen`, `translationPositive_damp` (closure), `exchangePositive_const`,
   `translationPositive_const`, and `exchangePositive_not_dampingClosed`,
   `translationPositive_not_sharpenClosed` (no closure in the other direction).
7. `ExchangePositive.midpoint`, `ExchangePositive.nonneg`, `ExchangePositive.seam_le`
   [proved-standard]: an exchange-positive kernel satisfies `K (u + v)² ≤ K (2u) · K (2v)`, is
   nonnegative, and, when even, is least at the seam: `|K 0| ≤ K u`.
8. `exchangePositive_exp`, `translationPositive_cos`, `cos_not_exchangePositive`: a relaxing mode
   `e^{a·u}` is exchange positive; a turning mode `cos u` is translation positive and is not
   exchange positive.
9. `roundTrip_translation` [proved-derived]: on a finite family of points closed under a
   reflection `u ∘ σ = −u`, the translation form with the reflection in its first slot is the
   exchange form of `v ↦ k (−v)`.

**Limits.**  The kernels are real and the test vectors are real; the Hermitian case is not
stated.  A real test vector reads only the symmetric part of a kernel, so `TranslationPositive`
is positive type for an even kernel and is weaker for one that is not even (`sin` satisfies it
with every pairing zero); `cos`, the constant and their dampings here are even.  The points are finitely many; nothing is said of a measure or an integral form, of
Bochner's theorem or of the Hamburger and Stieltjes moment problems.  The Schur product theorem
is proved only for the cross kernel `e^{c·u_i·u_j}`.  Items 4 and 6 are closures in one direction
and item 5 gives one failing kernel in the other; no statement classifies which kernels survive
the other direction (a kernel that vanishes identically survives both).  Nothing here is a
statement about the zeros of any function.

Computational object: the helical pair interaction.  Of the winding guide's six general objects
this module touches the pair (`u`, `v` and the reflection that exchanges them) and faces and
placement (a positive form places a mode); the helix, the cell holonomy, the tube and the tower
thread stay attached.

**Consumers.**  `Zeta/PaletteReflection` (the palette of `ξ` against both laws); the atlas rows
above and the record of this pass; and, for the machine, a host ruler's reading of a region's
memory: a relaxing mode (a pure decay) is exchange positive and a turning mode is not (item 8).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Coupling.HeatArrow

variable {ι : Type*} [Fintype ι] {M N : ι → ι → ℝ} {K : ℝ → ℝ}

/-! ## 1. A positive kernel on finitely many sites -/

/-- [definition] A real kernel on finitely many sites pairs every test vector with itself to a
nonnegative number. -/
def Pos (M : ι → ι → ℝ) : Prop := ∀ x : ι → ℝ, 0 ≤ ∑ i, ∑ j, x i * M i j * x j

/-- [proved-standard; formal-checked] A diagonal rescaling of a positive kernel is positive: the
test vector `x` on `d i · M i j · d j` is the test vector `x · d` on `M`. -/
theorem Pos.congr_diag (hM : Pos M) (d : ι → ℝ) : Pos (fun i j => d i * M i j * d j) := by
  intro x
  have e : ∑ i, ∑ j, x i * (d i * M i j * d j) * x j
      = ∑ i, ∑ j, (x i * d i) * M i j * (x j * d j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  change 0 ≤ ∑ i, ∑ j, x i * (d i * M i j * d j) * x j
  rw [e]
  exact hM fun i => x i * d i

/-- [proved-standard; formal-checked] A rank-one kernel `w i · w j` is positive: its pairing is
the square of `∑ i, x i · w i`. -/
theorem pos_rankOne (w : ι → ℝ) : Pos (fun i j => w i * w j) := by
  intro x
  have e : ∑ i, ∑ j, x i * (w i * w j) * x j = (∑ i, x i * w i) * ∑ j, x j * w j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  change 0 ≤ ∑ i, ∑ j, x i * (w i * w j) * x j
  rw [e]
  exact mul_self_nonneg _

/-- [proved-standard; formal-checked] The sum of two positive kernels is positive. -/
theorem Pos.add (hM : Pos M) (hN : Pos N) : Pos (fun i j => M i j + N i j) := by
  intro x
  have e : ∑ i, ∑ j, x i * (M i j + N i j) * x j
      = (∑ i, ∑ j, x i * M i j * x j) + ∑ i, ∑ j, x i * N i j * x j := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  change 0 ≤ ∑ i, ∑ j, x i * (M i j + N i j) * x j
  rw [e]
  exact add_nonneg (hM x) (hN x)

/-- [proved-standard; formal-checked] A sum against a test vector carried by two sites reads the
two sites. -/
private theorem sum_twoSite [DecidableEq ι] (i j : ι) (a b : ℝ) (F : ι → ℝ) :
    ∑ k, (a * (if k = i then 1 else 0) + b * (if k = j then 1 else 0)) * F k
      = a * F i + b * F j := by
  simp [add_mul, Finset.sum_add_distrib]

/-- [proved-standard; formal-checked] The two-point reading of a positive kernel: the test vector
with `a` at site `i` and `b` at site `j` (the sites may coincide) pairs to the binary form of the
four entries. -/
theorem Pos.two_point [DecidableEq ι] (hM : Pos M) (i j : ι) (a b : ℝ) :
    0 ≤ a * (a * M i i + b * M i j) + b * (a * M j i + b * M j j) := by
  have h : 0 ≤ ∑ k, ∑ l, (a * (if k = i then 1 else 0) + b * (if k = j then 1 else 0)) * M k l
      * (a * (if l = i then 1 else 0) + b * (if l = j then 1 else 0)) :=
    hM fun k => a * (if k = i then 1 else 0) + b * (if k = j then 1 else 0)
  have inner : ∀ k : ι,
      ∑ l, (a * (if k = i then 1 else 0) + b * (if k = j then 1 else 0)) * M k l
          * (a * (if l = i then 1 else 0) + b * (if l = j then 1 else 0))
        = (a * (if k = i then 1 else 0) + b * (if k = j then 1 else 0))
          * (a * M k i + b * M k j) := by
    intro k
    rw [← sum_twoSite i j a b (fun l => M k l), Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => inner k,
    sum_twoSite i j a b (fun k => a * M k i + b * M k j)] at h
  exact h

/-- [proved-standard; formal-checked] A positive kernel has nonnegative diagonal entries. -/
theorem Pos.diag_nonneg [DecidableEq ι] (hM : Pos M) (i : ι) : 0 ≤ M i i := by
  have h := hM.two_point i i 1 0
  linarith

/-- [proved-standard; formal-checked] Cauchy–Schwarz for a symmetric positive kernel: an entry's
square is at most the product of its two diagonal entries. -/
theorem Pos.sq_le [DecidableEq ι] (hM : Pos M) (hsymm : ∀ i j, M i j = M j i) (i j : ι) :
    M i j ^ 2 ≤ M i i * M j j := by
  have h1 := hM.two_point i j (-M i j) (M i i)
  have h2 := hM.two_point i j (M j j) (-M i j)
  have h3 := hM.two_point i j 1 (-M i j)
  have hp := hM.diag_nonneg i
  have hr := hM.diag_nonneg j
  rw [hsymm j i] at h1 h2 h3
  have h1' : 0 ≤ M i i * (M i i * M j j - M i j ^ 2) := by linarith
  have h2' : 0 ≤ M j j * (M i i * M j j - M i j ^ 2) := by linarith
  rcases hp.eq_or_lt with hp0 | hp0
  · rcases hr.eq_or_lt with hr0 | hr0
    · rw [← hp0, ← hr0] at h3 ⊢
      nlinarith [sq_nonneg (M i j)]
    · have := nonneg_of_mul_nonneg_right h2' hr0
      linarith
  · have := nonneg_of_mul_nonneg_right h1' hp0
    linarith

/-! ## 2. The Schur step for the cross kernel -/

/-- [proved-standard; formal-checked] **The Schur step for the cross kernel.**  For `c ≥ 0` the
entrywise product of a positive kernel with `e^{c·u_i·u_j}` is positive.  The exponential is its
series, and the term of order `n` is `cⁿ/n!` times the pairing of `M` with the test vector
`u_iⁿ · x_i`, which is nonnegative. -/
theorem Pos.exp_cross (hM : Pos M) (u : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Pos (fun i j => Real.exp (c * u i * u j) * M i j) := by
  intro x
  change 0 ≤ ∑ i, ∑ j, x i * (Real.exp (c * u i * u j) * M i j) * x j
  have hterm : ∀ i j : ι,
      HasSum (fun n : ℕ => x i * ((c * u i * u j) ^ n / (n.factorial : ℝ) * M i j) * x j)
        (x i * (Real.exp (c * u i * u j) * M i j) * x j) := by
    intro i j
    have h := NormedSpace.expSeries_div_hasSum_exp (c * u i * u j)
    rw [← Real.exp_eq_exp_ℝ] at h
    exact ((h.mul_right (M i j)).mul_left (x i)).mul_right (x j)
  have hsum : HasSum
      (fun n : ℕ => ∑ i, ∑ j, x i * ((c * u i * u j) ^ n / (n.factorial : ℝ) * M i j) * x j)
      (∑ i, ∑ j, x i * (Real.exp (c * u i * u j) * M i j) * x j) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => hterm i j
  refine hsum.nonneg fun n => ?_
  have e : ∑ i, ∑ j, x i * ((c * u i * u j) ^ n / (n.factorial : ℝ) * M i j) * x j
      = c ^ n / (n.factorial : ℝ) * ∑ i, ∑ j, (u i ^ n * x i) * M i j * (u j ^ n * x j) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact mul_nonneg (div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _))
    (hM fun i => u i ^ n * x i)

/-! ## 3. The Gaussian factors two ways -/

/-- [proved-standard; formal-checked] The Gaussian of a sum factors through the cross kernel with
a positive coupling when it sharpens. -/
theorem seam_split (τ u v : ℝ) :
    Real.exp (τ * (u + v) ^ 2)
      = Real.exp (τ * u ^ 2) * Real.exp (2 * τ * u * v) * Real.exp (τ * v ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- [proved-standard; formal-checked] The Gaussian of a difference factors through the cross
kernel with a positive coupling when it damps. -/
theorem translation_split (t u v : ℝ) :
    Real.exp (-t * (u - v) ^ 2)
      = Real.exp (-t * u ^ 2) * Real.exp (2 * t * u * v) * Real.exp (-t * v ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- [proved-standard; formal-checked] **Sharpening keeps exchange positivity** on any finite
family of points: `e^{τ(u_i+u_j)²}` is a diagonal rescaling of the cross kernel `e^{2τ·u_i·u_j}`. -/
theorem exchange_sharpen (k : ℝ → ℝ) (u : ι → ℝ) (h : Pos (fun i j => k (u i + u j))) {τ : ℝ}
    (hτ : 0 ≤ τ) : Pos (fun i j => Real.exp (τ * (u i + u j) ^ 2) * k (u i + u j)) := by
  have h2 := (h.exp_cross u (c := 2 * τ) (by positivity)).congr_diag
    (fun i => Real.exp (τ * u i ^ 2))
  have e : (fun i j => Real.exp (τ * (u i + u j) ^ 2) * k (u i + u j))
      = fun i j => Real.exp (τ * u i ^ 2) * (Real.exp (2 * τ * u i * u j) * k (u i + u j))
        * Real.exp (τ * u j ^ 2) := by
    funext i j
    rw [seam_split]
    ring
  rw [e]
  exact h2

/-- [proved-standard; formal-checked] **Damping keeps translation positivity** on any finite
family of points: `e^{−t(u_i−u_j)²}` is a diagonal rescaling of the cross kernel
`e^{2t·u_i·u_j}`. -/
theorem translation_damp (k : ℝ → ℝ) (u : ι → ℝ) (h : Pos (fun i j => k (u i - u j))) {t : ℝ}
    (ht : 0 ≤ t) : Pos (fun i j => Real.exp (-t * (u i - u j) ^ 2) * k (u i - u j)) := by
  have h2 := (h.exp_cross u (c := 2 * t) (by positivity)).congr_diag
    (fun i => Real.exp (-t * u i ^ 2))
  have e : (fun i j => Real.exp (-t * (u i - u j) ^ 2) * k (u i - u j))
      = fun i j => Real.exp (-t * u i ^ 2) * (Real.exp (2 * t * u i * u j) * k (u i - u j))
        * Real.exp (-t * u j ^ 2) := by
    funext i j
    rw [translation_split]
    ring
  rw [e]
  exact h2

/-! ## 4. Each fails the other way, on two points -/

/-- [counterexample; formal-checked] **Damping breaks exchange positivity.**  On the points
`0, 1` the constant kernel damped for any time `t > 0` has the entries
`[[1, e^{−t}], [e^{−t}, e^{−4t}]]`, and the test vector `(e^{−t}, −1)` pairs to
`e^{−4t} − e^{−2t} < 0`. -/
theorem exchange_damp_fails {t : ℝ} (ht : 0 < t) :
    ¬ Pos (fun i j : Fin 2 =>
      Real.exp (-t * ((![0, 1] : Fin 2 → ℝ) i + ![0, 1] j) ^ 2) * 1) := by
  intro h
  have h' := h ![Real.exp (-t), -1]
  have e00 : Real.exp (-t * ((0 : ℝ) + 0) ^ 2) = 1 := by norm_num
  have e01 : Real.exp (-t * ((0 : ℝ) + 1) ^ 2) = Real.exp (-t) := by norm_num
  have e10 : Real.exp (-t * ((1 : ℝ) + 0) ^ 2) = Real.exp (-t) := by norm_num
  have e11 : Real.exp (-t * ((1 : ℝ) + 1) ^ 2) = Real.exp (-t) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e00, e01, e10,
    e11] at h'
  have hpos := Real.exp_pos (-t)
  have hlt : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : Real.exp (-t) ^ 2 < 1 := by nlinarith
  have h4 : Real.exp (-t) ^ 4 < Real.exp (-t) ^ 2 := by nlinarith [pow_pos hpos 2]
  linarith

/-- [counterexample; formal-checked] **Sharpening breaks translation positivity.**  On the points
`0, 1` the constant kernel sharpened for any time `τ > 0` has the entries
`[[1, e^{τ}], [e^{τ}, 1]]`, and the test vector `(1, −1)` pairs to `2 − 2e^{τ} < 0`. -/
theorem translation_sharpen_fails {τ : ℝ} (hτ : 0 < τ) :
    ¬ Pos (fun i j : Fin 2 =>
      Real.exp (τ * ((![0, 1] : Fin 2 → ℝ) i - ![0, 1] j) ^ 2) * 1) := by
  intro h
  have h' := h ![1, -1]
  have e00 : Real.exp (τ * ((0 : ℝ) - 0) ^ 2) = 1 := by norm_num
  have e01 : Real.exp (τ * ((0 : ℝ) - 1) ^ 2) = Real.exp τ := by norm_num
  have e10 : Real.exp (τ * ((1 : ℝ) - 0) ^ 2) = Real.exp τ := by norm_num
  have e11 : Real.exp (τ * ((1 : ℝ) - 1) ^ 2) = 1 := by norm_num
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e00, e01, e10,
    e11] at h'
  have hgt : 1 < Real.exp τ := by
    rw [Real.one_lt_exp_iff]
    exact hτ
  linarith

/-! ## 5. The two laws of a kernel on the line -/

/-- [definition] A kernel on the line is **exchange positive** when, on every finite family of
points, the kernel `K (u_i + u_j)` of their sums is positive (reflection positivity across the
seam `u = 0`; the Hankel form). -/
def ExchangePositive (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin n → ℝ), Pos (fun i j => K (u i + u j))

/-- [definition] A kernel on the line is **translation positive** when, on every finite family of
points, the kernel `K (u_i − u_j)` of their differences is positive (the Toeplitz form).  The
test vectors are real, so the pairing reads only the even part of `K`; for an even kernel this is
positive type. -/
def TranslationPositive (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (u : Fin n → ℝ), Pos (fun i j => K (u i - u j))

/-- [proved-standard; formal-checked] Exchange positivity is closed under Gaussian sharpening. -/
theorem exchangePositive_sharpen (h : ExchangePositive K) {τ : ℝ} (hτ : 0 ≤ τ) :
    ExchangePositive (fun u => Real.exp (τ * u ^ 2) * K u) :=
  fun n u => exchange_sharpen K u (h n u) hτ

/-- [proved-standard; formal-checked] Translation positivity is closed under Gaussian damping. -/
theorem translationPositive_damp (h : TranslationPositive K) {t : ℝ} (ht : 0 ≤ t) :
    TranslationPositive (fun u => Real.exp (-t * u ^ 2) * K u) :=
  fun n u => translation_damp K u (h n u) ht

/-- [proved-standard; formal-checked] The constant kernel `1` is exchange positive. -/
theorem exchangePositive_const : ExchangePositive (fun _ => 1) := by
  intro n u
  have h := pos_rankOne (fun _ : Fin n => (1 : ℝ))
  simpa using h

/-- [proved-standard; formal-checked] The constant kernel `1` is translation positive. -/
theorem translationPositive_const : TranslationPositive (fun _ => 1) := by
  intro n u
  have h := pos_rankOne (fun _ : Fin n => (1 : ℝ))
  simpa using h

/-- [counterexample; formal-checked] **Exchange positivity is not closed under damping**: the
constant kernel `1` is exchange positive and its damping for unit time is not
(`exchange_damp_fails`). -/
theorem exchangePositive_not_dampingClosed :
    ¬ ∀ K : ℝ → ℝ, ExchangePositive K → ∀ t : ℝ, 0 < t →
      ExchangePositive (fun u => Real.exp (-t * u ^ 2) * K u) := fun h =>
  exchange_damp_fails one_pos (h (fun _ => 1) exchangePositive_const 1 one_pos 2 ![0, 1])

/-- [counterexample; formal-checked] **Translation positivity is not closed under sharpening**:
the constant kernel `1` is translation positive and its sharpening for unit time is not
(`translation_sharpen_fails`). -/
theorem translationPositive_not_sharpenClosed :
    ¬ ∀ K : ℝ → ℝ, TranslationPositive K → ∀ τ : ℝ, 0 < τ →
      TranslationPositive (fun u => Real.exp (τ * u ^ 2) * K u) := fun h =>
  translation_sharpen_fails one_pos (h (fun _ => 1) translationPositive_const 1 one_pos 2 ![0, 1])

/-! ## 6. What exchange positivity forces: least at the seam -/

/-- [proved-standard; formal-checked] An exchange-positive kernel is midpoint log-convex in the
multiplicative form `K (u + v)² ≤ K (2u) · K (2v)`: Cauchy–Schwarz on the two points `u, v`. -/
theorem ExchangePositive.midpoint (h : ExchangePositive K) (u v : ℝ) :
    K (u + v) ^ 2 ≤ K (2 * u) * K (2 * v) := by
  have hs := (h 2 ![u, v]).sq_le (fun i j => congrArg K (add_comm _ _)) 0 1
  simpa [two_mul] using hs

/-- [proved-standard; formal-checked] An exchange-positive kernel is nonnegative: `K u` is the
diagonal entry at the single point `u / 2`. -/
theorem ExchangePositive.nonneg (h : ExchangePositive K) (u : ℝ) : 0 ≤ K u := by
  have hd : 0 ≤ K (u / 2 + u / 2) := (h 1 ![u / 2]).diag_nonneg 0
  rwa [add_halves] at hd

/-- [proved-standard; formal-checked] **An even exchange-positive kernel is least at the seam**:
`|K 0| ≤ K u` for every `u`, from the two points `u / 2, −u / 2`. -/
theorem ExchangePositive.seam_le (h : ExchangePositive K) (heven : ∀ u, K (-u) = K u) (u : ℝ) :
    |K 0| ≤ K u := by
  have hm := h.midpoint (u / 2) (-(u / 2))
  have e1 : u / 2 + -(u / 2) = 0 := by ring
  have e2 : 2 * (u / 2) = u := by ring
  have e3 : 2 * -(u / 2) = -u := by ring
  rw [e1, e2, e3, heven] at hm
  exact abs_le_of_sq_le_sq (by rw [sq (K u)]; exact hm) (h.nonneg u)

/-! ## 7. A relaxing mode and a turning mode -/

/-- [proved-standard; formal-checked] **A relaxing mode is exchange positive**:
`e^{a(u+v)} = e^{au} · e^{av}` is rank one. -/
theorem exchangePositive_exp (a : ℝ) : ExchangePositive (fun u => Real.exp (a * u)) := by
  intro n u
  have h := pos_rankOne (fun i => Real.exp (a * u i))
  have e : (fun i j : Fin n => Real.exp (a * (u i + u j)))
      = fun i j => Real.exp (a * u i) * Real.exp (a * u j) := by
    funext i j
    rw [mul_add, Real.exp_add]
  change Pos (fun i j : Fin n => Real.exp (a * (u i + u j)))
  rw [e]
  exact h

/-- [proved-standard; formal-checked] **A turning mode is translation positive**:
`cos (u − v) = cos u · cos v + sin u · sin v` is a sum of two rank-one kernels. -/
theorem translationPositive_cos : TranslationPositive Real.cos := by
  intro n u
  have h := (pos_rankOne (fun i => Real.cos (u i))).add (pos_rankOne (fun i => Real.sin (u i)))
  have e : (fun i j : Fin n => Real.cos (u i - u j))
      = fun i j => Real.cos (u i) * Real.cos (u j) + Real.sin (u i) * Real.sin (u j) := by
    funext i j
    exact Real.cos_sub _ _
  change Pos (fun i j : Fin n => Real.cos (u i - u j))
  rw [e]
  exact h

/-- [counterexample; formal-checked] **A turning mode is not exchange positive**: the single
point `π / 2` has the diagonal entry `cos π = −1`. -/
theorem cos_not_exchangePositive : ¬ ExchangePositive Real.cos := by
  intro h
  have hπ := h.nonneg Real.pi
  rw [Real.cos_pi] at hπ
  linarith

/-! ## 8. The round trip of a translation form is the exchange form -/

/-- [proved-derived; formal-checked] **The round trip of a translation form through the
reflection is the exchange form.**  On a finite family of points that a permutation `σ` reflects
(`u (σ i) = −u i`), the translation form of `k` with the reflection folded into its first slot
(`Coupling/ReflectedPositivity`'s `form (reflection a) b`) is the form of the sums' kernel
`v ↦ k (−v)`. -/
theorem roundTrip_translation (k : ℝ → ℝ) (u : ι → ℝ) (σ : Equiv.Perm ι)
    (hσ : ∀ i, u (σ i) = -u i) (f g : ι → ℝ) :
    ∑ i, ∑ j, f (σ i) * k (u i - u j) * g j = ∑ i, ∑ j, f i * k (-(u i + u j)) * g j := by
  rw [← Equiv.sum_comp σ (fun i => ∑ j, f i * k (-(u i + u j)) * g j)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : -(u (σ i) + u j) = u i - u j := by
    rw [hσ i]
    ring
  rw [e]

end Holonics.Coupling.HeatArrow

#print axioms Holonics.Coupling.HeatArrow.Pos.exp_cross
#print axioms Holonics.Coupling.HeatArrow.exchangePositive_not_dampingClosed
#print axioms Holonics.Coupling.HeatArrow.translationPositive_not_sharpenClosed
#print axioms Holonics.Coupling.HeatArrow.ExchangePositive.seam_le
#print axioms Holonics.Coupling.HeatArrow.roundTrip_translation
