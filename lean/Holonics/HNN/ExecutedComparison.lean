import Holonics.HNN.BankFace
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# HNN.ExecutedComparison: the release's own comparison, its exact pullback and its certified descent

[definition] The receiving bank's release (the Rust owner `hnn::prediction::bank_release`) decides
every station by the largest member's executed growth `a = max_m ρ(M_m)`, the spectral radius of
the member's monodromy through the executed ticks of its turn. The release's own comparison
(`hnn::executed`) compares exactly that, and its covector is the derivative of `log ρ` through the
executed tick and its solve (`hnn::ring::ReceivingBank::read_turn_covector`). This module states
the laws that covector and its certified step stand on (the diagnosis record,
`research/records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md`, §5).

1. **The monodromy's variation.** [proved-derived; formal-checked] A tick with its variation is
   the first-order polynomial `C T + X·C ΔT` over a (noncommutative) ring (`tick`); the passage's
   product (`passage`, later ticks on the left) has the monodromy as its constant coefficient
   (`passage_coeff_zero`), and its first-order coefficient composes forward, one tick at a time,
   `c₁′ = c₁ T + c₀ ΔT` (`passage_coeff_one`, the dual product of the Rust owner's forward route),
   and equals the reverse sum `Σ_t T_(>t) ΔT_t T_(<t)` over every tick (`product_deriv`, the Rust
   owner's prefix–suffix route): the two are one variation.
2. **The simple root's derivative.** [proved-derived; formal-checked] Along a differentiable path
   of roots `Φ(η, μ(η)) = 0` of a jointly differentiable `Φ` whose `λ`-derivative is nonzero at the
   root (a simple root), `μ′ = −∂_η Φ / ∂_λ Φ` (`simple_root_deriv`). With `Φ(η, λ) =
   det(λ − M − ηΔM)`, Jacobi's formula gives `∂_η Φ = −tr(adj(λ − M) ΔM)`, and at a simple root
   `adj(μ − M) = χ′(μ) r ℓᵀ / (ℓᵀ r)`, so `μ′ = ℓᵀ ΔM r / (ℓᵀ r)`: the Rust owner's eigen and trace
   routes. **The log-modulus.** Along a real parameter, `d log|μ| = Re(μ′/μ)` where `μ ≠ 0`
   (`log_modulus_deriv`): a conjugate pair moves its modulus together, so it is the one derivative
   of the pair.
3. **A max comparison descends where every active branch descends.** [proved-derived;
   formal-checked] For finitely many branches differentiable along a line, if every branch that
   attains the max at the start has slope at most `−a < 0`, the max is strictly lower for every small
   positive step (`max_descends`). **A sum of max comparisons descends where its active slopes sum
   below zero**: with every active branch of term `k` of slope at most `m_k` and `Σ_k m_k < 0`, the
   sum of the maxes is strictly lower for every small positive step (`sum_max_descends`, Danskin's
   bound for a finite max, summed; a hinge `(f)_+` is the max with the constant branch `0`). This
   is the first-order certificate the Rust owner reads on the active branches of the declared
   composition (`hnn::executed::executed_move`).
4. **A strict decrease certified by disjoint enclosures.** [proved-standard; formal-checked] With
   `F ∈ [L, U]` and `F′ ∈ [L′, U′]`, `U′ < L` gives `F′ < F` (`disjoint_enclosures_decrease`): the
   committed move's guard, read on the actual carried successor.
5. **The release's predicates release the section.** [proved-derived; formal-checked] At a
   refinement where every open station's top is its target, every station the lock takes (any
   subset of the open stations, the largest gap's ties together) is correct
   (`predicates_release_the_section`): class and threshold at every open station along the
   machine's own trajectory are sufficient for the order and the section.

[open] (#62) The existence of the differentiable root path (the implicit function theorem at a
simple root, from `Φ`'s strict differentiability), Jacobi's formula `∂_η det(λ − M − ηΔM) =
−tr(adj(λ − M) ΔM)` with the adjugate's rank-one form at a simple root, and the certificate's
enclosures (a Krawczyk disk holds exactly one simple root; the disk arithmetic is outward) are
hypotheses here or held by the Rust owner's tests; their Lean statements are owed.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.HNN.ExecutedComparison

open Polynomial Filter Topology
open scoped BigOperators

/-! ## 1. The monodromy's variation -/

section Variation

variable {A : Type*} [Ring A]

/-- [definition] **A tick with its variation** as the first-order polynomial `C T + X·C ΔT`. -/
def tick (T D : A) : A[X] := C T + X * C D

/-- [definition] **The passage**: the ticks in order, later ticks on the left. -/
def passage : List (A × A) → A[X]
  | [] => 1
  | p :: rest => passage rest * tick p.1 p.2

/-- [definition] **The monodromy**: the ticks' product, later ticks on the left. -/
def monodromy : List (A × A) → A
  | [] => 1
  | p :: rest => monodromy rest * p.1

theorem tick_coeff (T D : A) (n : ℕ) :
    (tick T D).coeff n = if n = 0 then T else if n = 1 then D else 0 := by
  rcases n with _ | _ | n <;> simp [tick, coeff_C]

/-- [proved-derived; formal-checked] **The passage's constant coefficient is the monodromy.** -/
theorem passage_coeff_zero (L : List (A × A)) : (passage L).coeff 0 = monodromy L := by
  induction L with
  | nil => simp [passage, monodromy]
  | cons p rest ih =>
    rw [passage, monodromy, coeff_mul]
    simp [tick_coeff, ih]

/-- [proved-derived; formal-checked] **One tick more, order one** (the forward route):
`c₁′ = c₁ T + c₀ ΔT`. -/
theorem passage_coeff_one (p : A × A) (rest : List (A × A)) :
    (passage (p :: rest)).coeff 1 = (passage rest).coeff 1 * p.1 + monodromy rest * p.2 := by
  rw [passage, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, tick_coeff, passage_coeff_zero]
  abel

/-- [definition] **The reverse sum** `Σ_t T_(>t) ΔT_t T_(<t)` over the ticks in order (`t` the
first tick at the head). -/
def reverseSum : List (A × A) → A
  | [] => 0
  | p :: rest => reverseSum rest * p.1 + monodromy rest * p.2

/-- [proved-derived; formal-checked] **The monodromy's variation, forward and in reverse, is one**:
the passage's first-order coefficient equals the reverse sum over every tick. -/
theorem product_deriv (L : List (A × A)) : (passage L).coeff 1 = reverseSum L := by
  induction L with
  | nil => simp [passage, reverseSum, coeff_one]
  | cons p rest ih => rw [passage_coeff_one, ih, reverseSum]

/-- [proved-derived; formal-checked] **The reverse sum, unfolded** at the head: the head tick's
variation reads the rest's monodromy on its left and nothing on its right, and every later tick's
term carries the head tick on its right. -/
theorem reverseSum_cons (p : A × A) (rest : List (A × A)) :
    reverseSum (p :: rest) = reverseSum rest * p.1 + monodromy rest * p.2 := rfl

end Variation

/-! ## 2. The simple root's derivative and the log-modulus -/

/-- [proved-derived; formal-checked] **The simple root's derivative.** Along a differentiable path
of roots `Φ(η, μ(η)) = 0` of a jointly differentiable `Φ` with `∂_λ Φ ≠ 0` at the root,
`μ′ = −∂_η Φ / ∂_λ Φ`. -/
theorem simple_root_deriv {Φ : ℂ × ℂ → ℂ} {Φ' : ℂ × ℂ →L[ℂ] ℂ} {μ : ℂ → ℂ} {μ' η₀ : ℂ}
    (hΦ : HasFDerivAt Φ Φ' (η₀, μ η₀)) (hμ : HasDerivAt μ μ' η₀)
    (hroot : ∀ η, Φ (η, μ η) = 0) (hsimple : Φ' (0, 1) ≠ 0) :
    μ' = -Φ' (1, 0) / Φ' (0, 1) := by
  have hpath : HasDerivAt (fun η => (η, μ η)) ((1 : ℂ), μ') η₀ := (hasDerivAt_id η₀).prodMk hμ
  have hcomp : HasDerivAt (fun η => Φ (η, μ η)) (Φ' ((1 : ℂ), μ')) η₀ :=
    hΦ.comp_hasDerivAt η₀ hpath
  have hconst : (fun η => Φ (η, μ η)) = fun _ => (0 : ℂ) := funext hroot
  have hzero : HasDerivAt (fun η => Φ (η, μ η)) 0 η₀ := by
    rw [hconst]
    exact hasDerivAt_const η₀ 0
  have h : Φ' ((1 : ℂ), μ') = 0 := hcomp.unique hzero
  have hsplit : ((1 : ℂ), μ') = ((1 : ℂ), (0 : ℂ)) + μ' • ((0 : ℂ), (1 : ℂ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at h
  field_simp
  linear_combination h

/-- [proved-derived; formal-checked] **The log-modulus's derivative** along a real parameter:
`d log|μ| = Re(μ′/μ)` where `μ ≠ 0`. -/
theorem log_modulus_deriv {μ : ℝ → ℂ} {μ' : ℂ} {η₀ : ℝ} (hμ : HasDerivAt μ μ' η₀)
    (h0 : μ η₀ ≠ 0) :
    HasDerivAt (fun η => Real.log ‖μ η‖) (μ' / μ η₀).re η₀ := by
  have hsq : HasDerivAt (fun η => ‖μ η‖ ^ 2) (2 * inner ℝ (μ η₀) μ') η₀ := hμ.norm_sq
  have hpos : ‖μ η₀‖ ^ 2 ≠ 0 := by positivity
  have hlog := (hsq.log hpos).div_const 2
  have hfun : (fun η => Real.log ‖μ η‖) = fun η => Real.log (‖μ η‖ ^ 2) / 2 := by
    funext η
    rw [Real.log_pow]
    push_cast
    ring
  have hn : Complex.normSq (μ η₀) ≠ 0 := by
    rwa [Complex.normSq_eq_norm_sq]
  have hval : 2 * inner ℝ (μ η₀) μ' / ‖μ η₀‖ ^ 2 / 2 = (μ' / μ η₀).re := by
    rw [Complex.inner, Complex.div_re, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hlog

/-! ## 3. A max comparison descends where every active branch descends -/

/-- A branch with a negative slope falls on the right. -/
theorem eventually_lt_of_deriv_neg {f : ℝ → ℝ} {D : ℝ} (hf : HasDerivAt f D 0) (hD : D < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), f η < f 0 := by
  have hslope : Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 D) :=
    hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
  have hneg : ∀ᶠ η in 𝓝[>] (0 : ℝ), slope f 0 η < 0 := hslope.eventually (gt_mem_nhds hD)
  filter_upwards [hneg, self_mem_nhdsWithin] with η hη hpos
  rw [slope_def_field, sub_zero] at hη
  have hp : (0 : ℝ) < η := hpos
  have := (div_neg_iff.mp hη)
  rcases this with ⟨_, hneg'⟩ | ⟨hpos', _⟩
  · exact absurd hneg' (not_lt.mpr hp.le)
  · linarith

/-- [proved-derived; formal-checked] **A max comparison descends where every active branch
descends.** For finitely many branches differentiable along a line at `0`, if every branch attaining
the max at `0` has slope at most `−a < 0`, the max is strictly lower for every small positive step. -/
theorem max_descends {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ → ℝ) (D : ι → ℝ)
    {a : ℝ} (ha : 0 < a) (hderiv : ∀ i ∈ s, HasDerivAt (f i) (D i) 0)
    (hactive : ∀ i ∈ s, f i 0 = s.sup' hs (fun j => f j 0) → D i ≤ -a) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), s.sup' hs (fun j => f j η) < s.sup' hs (fun j => f j 0) := by
  set top := s.sup' hs (fun j => f j 0)
  have each : ∀ i ∈ s, ∀ᶠ η in 𝓝[>] (0 : ℝ), f i η < top := by
    intro i hi
    by_cases hat : f i 0 = top
    · have hneg : D i < 0 := by linarith [hactive i hi hat]
      filter_upwards [eventually_lt_of_deriv_neg (hderiv i hi) hneg] with η hη
      rw [← hat]
      exact hη
    · have hle : f i 0 ≤ top := Finset.le_sup' (fun j => f j 0) hi
      have hlt : f i 0 < top := lt_of_le_of_ne hle hat
      have hcont : ContinuousAt (f i) 0 := (hderiv i hi).continuousAt
      have : ∀ᶠ η in 𝓝 (0 : ℝ), f i η < top := hcont.eventually (gt_mem_nhds hlt)
      exact nhdsWithin_le_nhds this
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i ∈ s, f i η < top :=
    (Filter.eventually_all_finset s).mpr each
  filter_upwards [hall] with η hη
  exact (Finset.sup'_lt_iff hs).mpr hη

/-- A branch's slope bound on the right: with `D < c`, `f η < f 0 + η c` for small `η > 0`. -/
theorem eventually_lt_of_deriv_lt {f : ℝ → ℝ} {D c : ℝ} (hf : HasDerivAt f D 0) (hD : D < c) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), f η < f 0 + η * c := by
  have hline : HasDerivAt (fun η : ℝ => η * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  have hg : HasDerivAt (fun η => f η - η * c) (D - c) 0 := hf.sub hline
  filter_upwards [eventually_lt_of_deriv_neg hg (by linarith)] with η hη
  simp at hη
  linarith

/-- [proved-derived; formal-checked] **A sum of max comparisons descends where its active slopes
sum below zero** (the composition's first-order certificate): for finitely many terms, each a max
over finitely many branches differentiable along a line at `0`, with every branch attaining its
term's max at `0` of slope at most `m_k`, and `Σ_k m_k < 0`, the sum of the maxes is strictly lower
for every small positive step (Danskin's bound for a finite max, summed). A hinge `(f)_+` is the max
with the constant branch `0`. -/
theorem sum_max_descends {κ ι : Type*} (K : Finset κ) (s : κ → Finset ι)
    (hs : ∀ k, (s k).Nonempty) (f : κ → ι → ℝ → ℝ) (D : κ → ι → ℝ) (m : κ → ℝ)
    (hderiv : ∀ k ∈ K, ∀ i ∈ s k, HasDerivAt (f k i) (D k i) 0)
    (hactive : ∀ k ∈ K, ∀ i ∈ s k,
      f k i 0 = (s k).sup' (hs k) (fun j => f k j 0) → D k i ≤ m k)
    (hsum : ∑ k ∈ K, m k < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ∑ k ∈ K, (s k).sup' (hs k) (fun j => f k j η) <
        ∑ k ∈ K, (s k).sup' (hs k) (fun j => f k j 0) := by
  set ε := -(∑ k ∈ K, m k) / (2 * (K.card + 1)) with hε
  have hcard : (0 : ℝ) < 2 * (K.card + 1) := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hcard
  -- Each term lies below its value at zero plus `η (m_k + ε)`.
  have term : ∀ k ∈ K, ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (s k).sup' (hs k) (fun j => f k j η) <
        (s k).sup' (hs k) (fun j => f k j 0) + η * (m k + ε) := by
    intro k hk
    set top := (s k).sup' (hs k) (fun j => f k j 0)
    have each : ∀ i ∈ s k, ∀ᶠ η in 𝓝[>] (0 : ℝ), f k i η < top + η * (m k + ε) := by
      intro i hi
      by_cases hat : f k i 0 = top
      · have hlt : D k i < m k + ε := by linarith [hactive k hk i hi hat]
        filter_upwards [eventually_lt_of_deriv_lt (hderiv k hk i hi) hlt] with η hη
        rw [← hat]
        exact hη
      · have hle : f k i 0 ≤ top := Finset.le_sup' (fun j => f k j 0) hi
        have hlt : f k i 0 < top := lt_of_le_of_ne hle hat
        set gap := top - f k i 0
        have hgap : 0 < gap := by simp [gap]; linarith
        have hcont : ContinuousAt (f k i) 0 := (hderiv k hk i hi).continuousAt
        have hnear : ∀ᶠ η in 𝓝 (0 : ℝ), f k i η < f k i 0 + gap / 2 :=
          hcont.eventually (gt_mem_nhds (by linarith))
        have hsmall : ∀ᶠ η in 𝓝 (0 : ℝ), -(gap / 2) < η * (m k + ε) := by
          have hc : ContinuousAt (fun η : ℝ => η * (m k + ε)) 0 :=
            (continuous_id.mul continuous_const).continuousAt
          have : ∀ᶠ η in 𝓝 (0 : ℝ), -(gap / 2) < (fun η : ℝ => η * (m k + ε)) η :=
            hc.eventually (lt_mem_nhds (by simp; linarith))
          exact this
        filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hsmall] with η h1 h2
        simp [gap] at h1
        linarith
    have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i ∈ s k, f k i η < top + η * (m k + ε) :=
      (Filter.eventually_all_finset (s k)).mpr each
    filter_upwards [hall] with η hη
    exact (Finset.sup'_lt_iff (hs k)).mpr hη
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ k ∈ K,
      (s k).sup' (hs k) (fun j => f k j η) <
        (s k).sup' (hs k) (fun j => f k j 0) + η * (m k + ε) :=
    (Filter.eventually_all_finset K).mpr term
  filter_upwards [hall, self_mem_nhdsWithin] with η hη hpos
  have hp : (0 : ℝ) < η := hpos
  by_cases hK : K = ∅
  · subst hK
    simp at hsum
  have hne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK
  have hlt : ∑ k ∈ K, (s k).sup' (hs k) (fun j => f k j η) <
      ∑ k ∈ K, ((s k).sup' (hs k) (fun j => f k j 0) + η * (m k + ε)) :=
    Finset.sum_lt_sum_of_nonempty hne hη
  have hrest : ∑ k ∈ K, η * (m k + ε) < 0 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hbound : ∑ k ∈ K, m k + (K.card : ℝ) * ε < 0 := by
      have hc : (K.card : ℝ) * ε ≤ -(∑ k ∈ K, m k) / 2 := by
        rw [hε, mul_div_assoc']
        rw [div_le_div_iff₀ hcard (by norm_num)]
        nlinarith [hsum]
      linarith
    exact mul_neg_of_pos_of_neg hp hbound
  rw [Finset.sum_add_distrib] at hlt
  linarith

/-! ## 4. A strict decrease certified by disjoint enclosures -/

/-- [proved-standard; formal-checked] **Disjoint enclosures certify a strict decrease**: with
`F ∈ [L, U]` and `F′ ∈ [L′, U′]`, `U′ < L` gives `F′ < F`. -/
theorem disjoint_enclosures_decrease {F F' L U' : ℝ} (hF : L ≤ F) (hF' : F' ≤ U')
    (hdisjoint : U' < L) : F' < F := by
  linarith

/-! ## 5. The release's predicates release the section -/

/-- [proved-derived; formal-checked] **Class and threshold at every open station make every lock
correct.** If every open station's top is its target, every station a refinement locks (any subset
of the open stations: the largest gap's ties together) is correct. -/
theorem predicates_release_the_section {σ κ : Type*} (open_ locked : Finset σ)
    (top target : σ → κ) (hsub : locked ⊆ open_) (hclass : ∀ j ∈ open_, top j = target j) :
    ∀ j ∈ locked, top j = target j := fun j hj => hclass j (hsub hj)

/-! ## 6. The modulus's least-squares step

[definition; agent-inferred, September 30] (`holonics::hnn::executed::executed_move`, the
modulus's record.) The port's normal law fits its storage moves `ΔE f` to the proposal's descent
covectors in least squares; the transport modulus has one feature, each contribution's storage
derivative `v_c = ∂z_c/∂ρ`, and its unit move is that fit: with the signed covectors `g_c`
(`sign_c ĝ_c`), `G = Σ ‖v_c‖²` and `γ = Σ ⟪g_c, v_c⟫`, the step `−γ/G` minimizes
`Σ ‖x v_c + g_c‖²` over every `x` (`modulus_least_squares`), and its first-order share `γ · (−γ/G)`
is `−γ²/G ≤ 0` (`modulus_least_squares_descends`): the move is proportional to the slope, never
inverse to it. -/

section LeastSquares

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {κ : Type*}

/-- The sum of squares along a ray, expanded: `Σ ‖x v + g‖² = x² G + 2 x γ + Σ ‖g‖²`. -/
theorem ray_sum_sq (K : Finset κ) (v g : κ → V) (x : ℝ) :
    ∑ c ∈ K, ‖x • v c + g c‖ ^ 2 =
      x ^ 2 * ∑ c ∈ K, ‖v c‖ ^ 2 + 2 * x * ∑ c ∈ K, inner ℝ (g c) (v c) +
        ∑ c ∈ K, ‖g c‖ ^ 2 := by
  have h : ∀ c ∈ K, ‖x • v c + g c‖ ^ 2 =
      x ^ 2 * ‖v c‖ ^ 2 + 2 * x * inner ℝ (g c) (v c) + ‖g c‖ ^ 2 := by
    intro c _
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_comm, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-- [proved-derived; formal-checked] **The modulus's least-squares step**: `−γ/G` minimizes the
fit of the storage moves to the descent covectors over every step. -/
theorem modulus_least_squares (K : Finset κ) (v g : κ → V) (hG : 0 < ∑ c ∈ K, ‖v c‖ ^ 2)
    (x : ℝ) :
    ∑ c ∈ K, ‖(-(∑ c ∈ K, inner ℝ (g c) (v c)) / ∑ c ∈ K, ‖v c‖ ^ 2) • v c + g c‖ ^ 2 ≤
      ∑ c ∈ K, ‖x • v c + g c‖ ^ 2 := by
  rw [ray_sum_sq, ray_sum_sq]
  set G := ∑ c ∈ K, ‖v c‖ ^ 2
  set γ := ∑ c ∈ K, inner ℝ (g c) (v c)
  have hsq : 0 ≤ G * (x + γ / G) ^ 2 := mul_nonneg hG.le (sq_nonneg _)
  have hG0 : G ≠ 0 := hG.ne'
  have key : G * (x + γ / G) ^ 2 = x ^ 2 * G + 2 * x * γ + γ ^ 2 / G := by
    field_simp
    ring
  have lhs : (-γ / G) ^ 2 * G + 2 * (-γ / G) * γ = -(γ ^ 2 / G) := by
    field_simp
    ring
  nlinarith [hsq, key, lhs]

/-- [proved-derived; formal-checked] **The least-squares step descends to first order**: its share
of the joint first order is `γ · (−γ/G) = −γ²/G ≤ 0`, zero only where `γ = 0`. -/
theorem modulus_least_squares_descends {γ G : ℝ} (hG : 0 < G) :
    γ * (-γ / G) = -(γ ^ 2 / G) ∧ γ * (-γ / G) ≤ 0 := by
  constructor
  · ring
  · have : γ * (-γ / G) = -(γ ^ 2 / G) := by ring
    rw [this, neg_nonpos]
    exact div_nonneg (sq_nonneg γ) hG.le

end LeastSquares

section Audit

#print axioms passage_coeff_zero
#print axioms passage_coeff_one
#print axioms product_deriv
#print axioms simple_root_deriv
#print axioms log_modulus_deriv
#print axioms eventually_lt_of_deriv_neg
#print axioms max_descends
#print axioms eventually_lt_of_deriv_lt
#print axioms sum_max_descends
#print axioms disjoint_enclosures_decrease
#print axioms predicates_release_the_section
#print axioms ray_sum_sq
#print axioms modulus_least_squares
#print axioms modulus_least_squares_descends

end Audit

end Holonics.HNN.ExecutedComparison
