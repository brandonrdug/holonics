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
7. **The lock-face comparison.** [proved-derived; formal-checked] The hinge composition's zero set
   is the closed predicate set, ties above threshold included (`hinge_zero_iff`,
   `hinge_zero_at_tie`). The lock face `ℓ = log((1 + a_t + r)/a_t)` has no zero and no minimizer,
   and its solved level `ℓ < log 2`, the lock's flip, certifies class and threshold on exact
   enclosures (`lockFace_enclosure_sublevel`); read at each station's decision refinement it releases
   the section whole (`decisions_release_the_section`); its covector is `θ − q` and its first-order
   certificate is Danskin's bound over the members (`lockFace_first_order`,
   `sum_upper_dini_descends`). Step 1b's candidate (§7).

[open] (#62) The existence of the differentiable root path (the implicit function theorem at a
simple root, from `Φ`'s strict differentiability), Jacobi's formula `∂_η det(λ − M − ηΔM) =
−tr(adj(λ − M) ΔM)` with the adjugate's rank-one form at a simple root, and the certificate's
enclosures (a Krawczyk disk holds exactly one simple root; the disk arithmetic is outward) are
hypotheses here or held by the Rust owner's tests; their Lean statements are owed. For §7: the
release's own lock rule (a nonempty set of the largest-gap eligible stations locks whenever one is
eligible) is the Rust owner's and is abstracted, not restated; and the first-order certificate
reads the chord of the carried move (the storage's exact change, the modulus's included), where
`lockFace_first_order` reads a differentiable line, the same scope as §3's.

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

/-! ## 7. The lock-face comparison: its solved level implies the release's predicates

[definition; agent-inferred, September 30] (Step 1b's candidate; the pin
`research/records/2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md`.) The
two counts measured the hinge composition `F = Σ (f)_+` of §5 descending every contrast toward ties
while its decisions stayed at a guess (its #62 item 4). Its zero set is the **closed** predicate set
(`hinge_zero_iff`): every tie above threshold is a zero where the class predicate fails
(`hinge_zero_at_tie`), and a right decision leaves the composition with no covector
(`hinge_right_leaves`), so `F = 0` does not supply `predicates_release_the_section`'s hypothesis.

The candidate reads each station's lock whole. Its candidates are biased sheets of weights `a_x`
(the executed growths) and its resting sheet has weight one (the lossless ring, at the
bifurcation): the exchange read at the resting sheet is `Π = 1 + a_t + r`, `r = Σ_(x ≠ t) a_x`,
and the comparison is the log of the ratio of the whole lock to the target sheet,
`ℓ = log(Π/a_t) = −log θ_t` (`lockFace`), the classical loss at the lock's face.
- It has **no zero and no minimizer** (`lockFace_pos`, `lockFace_strictAnti`): the target's pull
  never vanishes (`lockFace_share_lt_one`), and it rises with every rival (`lockFace_strictMono_rivals`).
- Its **solved level is the lock's flip**, `ℓ < log 2 ⇔ 1 + r < a_t` (`lockFace_lt_log_two_iff`),
  the target sheet outweighing the rest of the lock (`Objects/ParametronLock.lockFace_logistic`'s
  `θ > ½`). A tie, or any rival at or above the target, lies outside it
  (`lockFace_ge_log_two_of_rival`).
- On exact enclosures the rational test `1 + Σ_x U_x < L_t` certifies the class predicate
  (`U_x < L_t`), the threshold (`1 < L_t`) and the true term in the solved level
  (`lockFace_enclosure_sublevel`); the class predicate makes the target the release's top
  (`class_top_is_target`).
- Along the release, each station read once at its decision refinement while the earlier locks
  agree with the targets: when every such decision is at its target, every lock of every refinement
  is (`decisions_release_the_section`, by induction on the refinements).
- Its covector on the log-readings is `θ − q` with the resting sheet held (`lockFace_covector`,
  `HNN/BankFace.bank_face_covector` with one more sheet that does not move), and its first-order
  certificate over the members' active branches is Danskin's bound read through the term's
  monotonicity (`lockTerm_mono`, `lockTerm_line`, `sup_upper_dini`, `lockFace_first_order`); a sum
  of such terms descends where the bounds sum below zero (`sum_upper_dini_descends`).
-/

section LockFace

variable {ι : Type*}

/-! ### The hinge's zero set -/

/-- [definition] **The hinge term** of the executed comparison (§5's composition, the Rust owner's
`f = max(max_(x≠t) ln(a_x/a_t), −ln a_t)`): the rivals `s` against the target `t`. -/
def hingeTerm (s : Finset ι) (hs : s.Nonempty) (A : ι → ℝ) (t : ι) : ℝ :=
  max (s.sup' hs fun x => Real.log (A x / A t)) (-Real.log (A t))

/-- [proved-derived; formal-checked] **The hinge's zero set is the closed predicate set**: for
positive readings, `(f)_+ = 0` exactly when no rival exceeds the target and the target is at or
above the unit. Ties above threshold are in it. -/
theorem hinge_zero_iff (s : Finset ι) (hs : s.Nonempty) (A : ι → ℝ) (t : ι)
    (hA : ∀ x ∈ s, 0 < A x) (ht : 0 < A t) :
    max (hingeTerm s hs A t) 0 = 0 ↔ (∀ x ∈ s, A x ≤ A t) ∧ 1 ≤ A t := by
  rw [max_eq_right_iff, hingeTerm, max_le_iff, Finset.sup'_le_iff, neg_nonpos,
    Real.log_nonneg_iff ht]
  constructor
  · rintro ⟨hx, h1⟩
    refine ⟨fun x hxs => ?_, h1⟩
    have h := hx x hxs
    rw [Real.log_nonpos_iff (div_pos (hA x hxs) ht).le] at h
    exact (div_le_one ht).mp h
  · rintro ⟨hx, h1⟩
    refine ⟨fun x hxs => ?_, h1⟩
    rw [Real.log_nonpos_iff (div_pos (hA x hxs) ht).le]
    exact (div_le_one ht).mpr (hx x hxs)

/-- [proved-derived; formal-checked] **A tie above threshold zeroes the hinge while the class
predicate fails** (the two counts' #62 item 4): every candidate at the one reading `a ≥ 1` gives
`(f)_+ = 0`, and no rival is strictly below the target. `F = 0` does not imply the class
predicate. -/
theorem hinge_zero_at_tie (s : Finset ι) (hs : s.Nonempty) (t : ι) {a : ℝ} (ha : 1 ≤ a) :
    max (hingeTerm s hs (fun _ => a) t) 0 = 0 ∧ ¬ ∀ x ∈ s, (fun _ => a) x < a := by
  have hpos : 0 < a := lt_of_lt_of_le one_pos ha
  refine ⟨(hinge_zero_iff s hs (fun _ => a) t (fun _ _ => hpos) hpos).mpr
    ⟨fun _ _ => le_rfl, ha⟩, fun h => ?_⟩
  obtain ⟨x, hx⟩ := hs
  exact lt_irrefl a (h x hx)

/-- [proved-derived; formal-checked] **A right decision leaves the hinge**: where every rival is
strictly below the target and the target strictly past the unit, `(f)_+ = 0`, and it stays zero on
the open set of such readings, so no covector holds the decision's margin. -/
theorem hinge_right_leaves (s : Finset ι) (hs : s.Nonempty) (A : ι → ℝ) (t : ι)
    (hA : ∀ x ∈ s, 0 < A x) (hclass : ∀ x ∈ s, A x < A t) (hthreshold : 1 < A t) :
    max (hingeTerm s hs A t) 0 = 0 :=
  (hinge_zero_iff s hs A t hA (lt_trans one_pos hthreshold)).mpr
    ⟨fun x hx => (hclass x hx).le, hthreshold.le⟩

/-! ### The lock face: its sublevel, its sign, its ties -/

/-- [definition] **The lock-face comparison** of a target reading `a` against its rivals' total
`r`: `ℓ = log((1 + a + r)/a)`, the log of the lock's exchange read at its resting sheet (weight
one, the lossless ring at the bifurcation) over the target sheet: `−log θ_t`. -/
def lockFace (a r : ℝ) : ℝ := Real.log ((1 + a + r) / a)

/-- [proved-derived; formal-checked] **The lock face has no zero**: `ℓ > 0` for a positive target
and nonnegative rivals (the resting sheet always holds a share). -/
theorem lockFace_pos {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) : 0 < lockFace a r := by
  unfold lockFace
  apply Real.log_pos
  rw [one_lt_div ha]
  linarith

/-- [proved-derived; formal-checked] **The solved level is the lock's flip**: `ℓ < log 2` exactly
when the target sheet outweighs the resting sheet and every rival together, `1 + r < a`
(`θ_t > ½`; `Objects/ParametronLock.lockFace_logistic`'s flip with the rest of the lock as its
resting weight). -/
theorem lockFace_lt_log_two_iff {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    lockFace a r < Real.log 2 ↔ 1 + r < a := by
  unfold lockFace
  have hpos : 0 < (1 + a + r) / a := div_pos (by linarith) ha
  rw [Real.log_lt_log_iff hpos two_pos, div_lt_iff₀ ha]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The target raises the face strictly** (no minimizer): at
fixed rivals, a larger target reading has a strictly smaller comparison, so the covector's target
component never vanishes and a right decision keeps its margin's pull. -/
theorem lockFace_strictAnti {a b r : ℝ} (ha : 0 < a) (hab : a < b) (hr : 0 ≤ r) :
    lockFace b r < lockFace a r := by
  unfold lockFace
  have hb : 0 < b := lt_trans ha hab
  apply Real.log_lt_log (div_pos (by linarith) hb)
  rw [div_lt_div_iff₀ hb ha]
  nlinarith

/-- [proved-derived; formal-checked] **The rivals raise the face strictly.** -/
theorem lockFace_strictMono_rivals {a r r' : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hrr : r < r') :
    lockFace a r < lockFace a r' := by
  unfold lockFace
  apply Real.log_lt_log (div_pos (by linarith) ha)
  exact div_lt_div_of_pos_right (by linarith) ha

/-- [proved-derived; formal-checked] **A tie is outside the solved level**: if some rival reads at
least the target, `ℓ ≥ log 2`. In particular every tie of the candidates, where the hinge is zero
(`hinge_zero_at_tie`), is not a minimizer of the lock face. -/
theorem lockFace_ge_log_two_of_rival {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    Real.log 2 ≤ lockFace a r := by
  have hr0 : 0 ≤ r := le_trans ha.le hr
  by_contra h
  have := (lockFace_lt_log_two_iff ha hr0).mp (lt_of_not_ge h)
  linarith

/-- [proved-derived; formal-checked] **The solved level certifies the release's predicates on
exact enclosures.** With the target's reading enclosed below by `L`, every rival's above by
`U x ≥ 0`, and the exact rational test `1 + Σ_x U x < L`: every rival's upper end is below the
target's lower end (the class predicate, `hnn::ring::Growth::exceeds`), the target's lower end is
past the unit (the threshold, `Growth::is_locked`), and the true comparison is in the solved level. -/
theorem lockFace_enclosure_sublevel (s : Finset ι) (A U : ι → ℝ) (t : ι) {L : ℝ}
    (hL : L ≤ A t) (hU : ∀ x ∈ s, A x ≤ U x) (hA : ∀ x ∈ s, 0 ≤ A x) (hLpos : 0 < L)
    (htest : 1 + ∑ x ∈ s, U x < L) :
    (∀ x ∈ s, U x < L) ∧ 1 < L ∧ lockFace (A t) (∑ x ∈ s, A x) < Real.log 2 := by
  have hU0 : ∀ x ∈ s, 0 ≤ U x := fun x hx => le_trans (hA x hx) (hU x hx)
  have hsumU : 0 ≤ ∑ x ∈ s, U x := Finset.sum_nonneg hU0
  refine ⟨fun x hx => ?_, by linarith, ?_⟩
  · have : U x ≤ ∑ y ∈ s, U y := Finset.single_le_sum hU0 hx
    linarith
  · have hsumA : ∑ x ∈ s, A x ≤ ∑ x ∈ s, U x := Finset.sum_le_sum hU
    rw [lockFace_lt_log_two_iff (lt_of_lt_of_le hLpos hL) (Finset.sum_nonneg hA)]
    linarith

/-- [proved-derived; formal-checked] **The class predicate makes the target the release's top**:
with every rival's upper end below the target's lower end, every rival's lower end is below it too,
so the largest lower end (the release's top) is the target. -/
theorem class_top_is_target (s : Finset ι) (L U : ι → ℝ) (t : ι)
    (hLU : ∀ x ∈ s, L x ≤ U x) (hclass : ∀ x ∈ s, U x < L t) : ∀ x ∈ s, L x < L t :=
  fun x hx => lt_of_le_of_lt (hLU x hx) (hclass x hx)

/-! ### The covector -/

/-- [proved-derived; formal-checked] **The lock face's covector is `θ − q`** with the resting sheet
held (`HNN/BankFace.bank_face_covector` with one more sheet of weight one that does not move): along
a move `δ` of the candidates' log-readings, the derivative is `Σ_y θ_y δ_y − δ_t`,
`θ_y = A_y / (1 + Σ A)`. -/
theorem lockFace_covector (s : Finset ι) (A δ : ι → ℝ) (hA : ∀ y ∈ s, 0 < A y) (t : ι) :
    HasDerivAt
      (fun ε : ℝ => Real.log (1 + ∑ y ∈ s, A y * Real.exp (ε * δ y)) -
        (Real.log (A t) + ε * δ t))
      ((∑ y ∈ s, A y * δ y) / (1 + ∑ y ∈ s, A y) - δ t) 0 := by
  have hsum : HasDerivAt (fun ε : ℝ => 1 + ∑ y ∈ s, A y * Real.exp (ε * δ y))
      (∑ y ∈ s, A y * δ y) 0 := by
    have h := HasDerivAt.fun_sum (u := s) (A := fun y ε => A y * Real.exp (ε * δ y))
      (A' := fun y => A y * δ y) (x := (0 : ℝ)) fun y _ => by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ y)).exp.const_mul (A y)
    exact h.const_add 1
  have h0 : (1 + ∑ y ∈ s, A y * Real.exp ((0 : ℝ) * δ y)) = 1 + ∑ y ∈ s, A y := by simp
  have hpos : (1 + ∑ y ∈ s, A y * Real.exp ((0 : ℝ) * δ y)) ≠ 0 := by
    rw [h0]
    have : 0 ≤ ∑ y ∈ s, A y := Finset.sum_nonneg fun y hy => (hA y hy).le
    linarith
  have hlog := hsum.log hpos
  rw [h0] at hlog
  have hlin : HasDerivAt (fun ε : ℝ => Real.log (A t) + ε * δ t) (δ t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ t)).const_add (Real.log (A t))
  exact hlog.sub hlin

/-- [proved-derived; formal-checked] **The target's share is below one**: `θ_t < 1`, so the
covector's target component `θ_t − 1` is strictly negative at every constitution. -/
theorem lockFace_share_lt_one {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) : a / (1 + a + r) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-! ### The decisions along the release -/

/-- [proved-derived; formal-checked] **Decisions read along the key-consistent prefix release the
section whole.** Abstract the release's trajectory as the stations each refinement `r` locks and
every station's top there. If, at every refinement whose earlier locks all took their targets,
every station it locks has its top at its target (what the lock face's solved level gives at the
station's decision refinement, `lockFace_enclosure_sublevel` and `class_top_is_target`), then every
lock of every refinement takes its target. -/
theorem decisions_release_the_section {σ κ : Type*} (locks : ℕ → Finset σ) (top : ℕ → σ → κ)
    (target : σ → κ)
    (hdec : ∀ r, (∀ r' < r, ∀ j ∈ locks r', top r' j = target j) →
      ∀ j ∈ locks r, top r j = target j) :
    ∀ r, ∀ j ∈ locks r, top r j = target j := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih => exact hdec r fun r' hr' => ih r' hr'

end LockFace

section LockFaceFirstOrder

variable {ι μ : Type*} [DecidableEq ι]

/-- [definition] **The lock-face term on log-readings**: `log(1 + Σ_(y ∈ s) e^(S_y)) − S_t`. -/
def lockTerm (s : Finset ι) (t : ι) (S : ι → ℝ) : ℝ :=
  Real.log (1 + ∑ y ∈ s, Real.exp (S y)) - S t

/-- The term split at its target: `log((1 + Σ_(y ≠ t) e^(S_y)) e^(−S_t) + 1)`. -/
theorem lockTerm_eq (s : Finset ι) (t : ι) (ht : t ∈ s) (S : ι → ℝ) :
    lockTerm s t S =
      Real.log ((1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) + 1) := by
  unfold lockTerm
  rw [← Finset.add_sum_erase s _ ht]
  have hpos : 0 < 1 + (Real.exp (S t) + ∑ y ∈ s.erase t, Real.exp (S y)) := by
    have : 0 ≤ ∑ y ∈ s.erase t, Real.exp (S y) :=
      Finset.sum_nonneg fun y _ => (Real.exp_pos _).le
    have := Real.exp_pos (S t)
    linarith
  have he : Real.exp (S t) * Real.exp (-S t) = 1 := by rw [← Real.exp_add]; simp
  have key : (1 + (Real.exp (S t) + ∑ y ∈ s.erase t, Real.exp (S y))) * Real.exp (-S t) =
      (1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) + 1 := by
    calc (1 + (Real.exp (S t) + ∑ y ∈ s.erase t, Real.exp (S y))) * Real.exp (-S t)
        = (1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) +
            Real.exp (S t) * Real.exp (-S t) := by ring
      _ = (1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) + 1 := by rw [he]
  rw [← key, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- [proved-derived; formal-checked] **The lock-face term is monotone**: increasing in every rival's
log-reading, decreasing in the target's. -/
theorem lockTerm_mono (s : Finset ι) (t : ι) (ht : t ∈ s) (S V : ι → ℝ)
    (hr : ∀ y ∈ s, y ≠ t → S y ≤ V y) (htarget : V t ≤ S t) :
    lockTerm s t S ≤ lockTerm s t V := by
  rw [lockTerm_eq s t ht, lockTerm_eq s t ht]
  have hsum : ∑ y ∈ s.erase t, Real.exp (S y) ≤ ∑ y ∈ s.erase t, Real.exp (V y) :=
    Finset.sum_le_sum fun y hy =>
      Real.exp_le_exp.mpr (hr y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
  have h0 : 0 ≤ ∑ y ∈ s.erase t, Real.exp (S y) :=
    Finset.sum_nonneg fun y _ => (Real.exp_pos _).le
  have hexp : Real.exp (-S t) ≤ Real.exp (-V t) := Real.exp_le_exp.mpr (by linarith)
  have hprod : (1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) ≤
      (1 + ∑ y ∈ s.erase t, Real.exp (V y)) * Real.exp (-V t) :=
    mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by linarith)
  have hpos : 0 < (1 + ∑ y ∈ s.erase t, Real.exp (S y)) * Real.exp (-S t) + 1 := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ∑ y ∈ s.erase t, Real.exp (S y))
      (Real.exp_pos (-S t)).le
    linarith
  exact Real.log_le_log hpos (by linarith)

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The lock-face term along a line of log-readings** has the
derivative `Σ_y θ_y v_y − v_t`, `θ_y = e^(S_y)/(1 + Σ e^S)` (`lockFace_covector` at
`A = e^S`). -/
theorem lockTerm_line (s : Finset ι) (t : ι) (S v : ι → ℝ) :
    HasDerivAt (fun η : ℝ => lockTerm s t fun y => S y + η * v y)
      ((∑ y ∈ s, Real.exp (S y) * v y) / (1 + ∑ y ∈ s, Real.exp (S y)) - v t) 0 := by
  have h := lockFace_covector s (fun y => Real.exp (S y)) v (fun y _ => Real.exp_pos _) t
  have hfun : (fun η : ℝ => lockTerm s t fun y => S y + η * v y) =
      fun ε : ℝ => Real.log (1 + ∑ y ∈ s, Real.exp (S y) * Real.exp (ε * v y)) -
        (Real.log (Real.exp (S t)) + ε * v t) := by
    funext η
    unfold lockTerm
    simp only [Real.exp_add, Real.log_exp]
  rw [hfun]
  exact h

/-- [proved-derived; formal-checked] **A finite max of branches rises no faster than its active
branches' slopes**: for branches differentiable at `0` whose active branches have slope at most
`c`, every `ε > 0` leaves the max below `max(0) + η(c + ε)` for small `η > 0` (Danskin's upper
bound; the term bound inside `sum_max_descends`). -/
theorem sup_upper_dini (M : Finset μ) (hM : M.Nonempty) (σ : μ → ℝ → ℝ) (D : μ → ℝ) (c : ℝ)
    (hderiv : ∀ m ∈ M, HasDerivAt (σ m) (D m) 0)
    (hactive : ∀ m ∈ M, σ m 0 = M.sup' hM (fun k => σ k 0) → D m ≤ c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      M.sup' hM (fun m => σ m η) < M.sup' hM (fun m => σ m 0) + η * (c + ε) := by
  set top := M.sup' hM (fun k => σ k 0)
  have each : ∀ m ∈ M, ∀ᶠ η in 𝓝[>] (0 : ℝ), σ m η < top + η * (c + ε) := by
    intro m hm
    by_cases hat : σ m 0 = top
    · have hlt : D m < c + ε := by linarith [hactive m hm hat]
      filter_upwards [eventually_lt_of_deriv_lt (hderiv m hm) hlt] with η hη
      rw [← hat]
      exact hη
    · have hle : σ m 0 ≤ top := Finset.le_sup' (fun k => σ k 0) hm
      have hlt : σ m 0 < top := lt_of_le_of_ne hle hat
      set gap := top - σ m 0
      have hgap : 0 < gap := by simp [gap]; linarith
      have hcont : ContinuousAt (σ m) 0 := (hderiv m hm).continuousAt
      have hnear : ∀ᶠ η in 𝓝 (0 : ℝ), σ m η < σ m 0 + gap / 2 :=
        hcont.eventually (gt_mem_nhds (by linarith))
      have hsmall : ∀ᶠ η in 𝓝 (0 : ℝ), -(gap / 2) < η * (c + ε) := by
        have hc : ContinuousAt (fun η : ℝ => η * (c + ε)) 0 :=
          (continuous_id.mul continuous_const).continuousAt
        exact hc.eventually (lt_mem_nhds (by simp; linarith))
      filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds hsmall] with η h1 h2
      simp [gap] at h1
      linarith
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ m ∈ M, σ m η < top + η * (c + ε) :=
    (Filter.eventually_all_finset M).mpr each
  filter_upwards [hall] with η hη
  exact (Finset.sup'_lt_iff hM).mpr hη

/-- [proved-derived; formal-checked] **The lock face's first-order certificate over the members**
(the move's guard for the candidate comparison). Each candidate's log-reading is its members' max
(`S_y = max_m σ_(y,m)`, the joint's executed growth); along a line, with every active member of every
rival of slope at most `u_y`, and one active member of the target of slope at least `w`, the term
rises no faster than `Σ_(y ≠ t) θ_y u_y + (θ_t − 1) w`: for every `ε > 0`, eventually for small
`η > 0` it lies below its value plus `η` times that bound plus `ε`. -/
theorem lockFace_first_order (s : Finset ι) (t : ι) (ht : t ∈ s) (M : ι → Finset μ)
    (hM : ∀ y, (M y).Nonempty) (σ : ι → μ → ℝ → ℝ) (D : ι → μ → ℝ)
    (hderiv : ∀ y ∈ s, ∀ m ∈ M y, HasDerivAt (σ y m) (D y m) 0) (u : ι → ℝ)
    (hu : ∀ y ∈ s, y ≠ t → ∀ m ∈ M y,
      σ y m 0 = (M y).sup' (hM y) (fun k => σ y k 0) → D y m ≤ u y)
    {m₀ : μ} (hm₀ : m₀ ∈ M t) (hact : σ t m₀ 0 = (M t).sup' (hM t) (fun k => σ t k 0))
    {w : ℝ} (hw : w ≤ D t m₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      lockTerm s t (fun y => (M y).sup' (hM y) (fun m => σ y m η)) <
        lockTerm s t (fun y => (M y).sup' (hM y) (fun m => σ y m 0)) +
          η * (∑ y ∈ s.erase t,
                Real.exp ((M y).sup' (hM y) (fun m => σ y m 0)) /
                  (1 + ∑ z ∈ s, Real.exp ((M z).sup' (hM z) (fun m => σ z m 0))) * u y +
              (Real.exp ((M t).sup' (hM t) (fun m => σ t m 0)) /
                  (1 + ∑ z ∈ s, Real.exp ((M z).sup' (hM z) (fun m => σ z m 0))) - 1) * w +
              ε) := by
  set S0 : ι → ℝ := fun y => (M y).sup' (hM y) (fun m => σ y m 0) with hS0
  set Z := 1 + ∑ z ∈ s, Real.exp (S0 z) with hZ
  set θ : ι → ℝ := fun y => Real.exp (S0 y) / Z with hθ
  have hZpos : 0 < Z := by
    have : 0 ≤ ∑ z ∈ s, Real.exp (S0 z) := Finset.sum_nonneg fun z _ => (Real.exp_pos _).le
    simp only [hZ]
    linarith
  have hθ0 : ∀ y, 0 ≤ θ y := fun y => div_nonneg (Real.exp_pos _).le hZpos.le
  -- the shares sum below one
  have hθsum : ∑ y ∈ s, θ y < 1 := by
    simp only [hθ, ← Finset.sum_div]
    rw [div_lt_one hZpos]
    simp only [hZ]
    linarith
  have hθt : θ t ≤ 1 := by
    have : θ t ≤ ∑ y ∈ s, θ y := Finset.single_le_sum (fun y _ => hθ0 y) ht
    linarith
  have hθrest : ∑ y ∈ s.erase t, θ y ≤ 1 := by
    have : ∑ y ∈ s.erase t, θ y ≤ ∑ y ∈ s, θ y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset t s)
        (fun y _ _ => hθ0 y)
    linarith
  set e := ε / 4 with he
  have hepos : 0 < e := by simp [he]; linarith
  -- the comparison line: rivals raised to their slope bound, the target lowered to its
  set v : ι → ℝ := fun y => if y = t then w - e else u y + e with hv
  -- each rival's max below its line
  have hriv : ∀ y ∈ s, y ≠ t → ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (M y).sup' (hM y) (fun m => σ y m η) ≤ S0 y + η * v y := by
    intro y hy hyt
    filter_upwards [sup_upper_dini (M y) (hM y) (σ y) (D y) (u y) (hderiv y hy) (hu y hy hyt)
      hepos] with η hη
    simp only [hv, if_neg hyt]
    exact hη.le
  have hrivall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ y ∈ s, y ≠ t →
      (M y).sup' (hM y) (fun m => σ y m η) ≤ S0 y + η * v y := by
    have := (Filter.eventually_all_finset s).mpr fun y hy =>
      (show ∀ᶠ η in 𝓝[>] (0 : ℝ), y ≠ t →
          (M y).sup' (hM y) (fun m => σ y m η) ≤ S0 y + η * v y by
        by_cases hyt : y = t
        · exact Filter.Eventually.of_forall fun _ h => absurd hyt h
        · filter_upwards [hriv y hy hyt] with η hη _ using hη)
    exact this
  -- the target's max above its line, through its active member
  have htgt : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      S0 t + η * v t ≤ (M t).sup' (hM t) (fun m => σ t m η) := by
    have hneg : HasDerivAt (fun η => -σ t m₀ η) (-D t m₀) 0 := (hderiv t ht m₀ hm₀).neg
    have hlt : -D t m₀ < -(w - e) := by linarith
    filter_upwards [eventually_lt_of_deriv_lt hneg hlt] with η hη
    have hle : σ t m₀ η ≤ (M t).sup' (hM t) (fun m => σ t m η) :=
      Finset.le_sup' (fun m => σ t m η) hm₀
    simp only [hv, if_pos rfl]
    have : S0 t = σ t m₀ 0 := by simp only [hS0]; exact hact.symm
    rw [this]
    linarith
  -- the line's term rises at its derivative
  have hline := lockTerm_line s t S0 v
  set B := (∑ y ∈ s, Real.exp (S0 y) * v y) / Z - v t with hB
  have hlineB : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      lockTerm s t (fun y => S0 y + η * v y) < lockTerm s t (fun y => S0 y + 0 * v y) +
        η * (B + e) := by
    have := eventually_lt_of_deriv_lt hline (show B < B + e by linarith)
    simpa using this
  -- the derivative against the certificate's bound
  have hBle : B ≤ ∑ y ∈ s.erase t, θ y * u y + (θ t - 1) * w + 2 * e := by
    have hsplit : (∑ y ∈ s, Real.exp (S0 y) * v y) / Z = ∑ y ∈ s, θ y * v y := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun y _ => by simp only [hθ]; ring
    have herase : ∑ y ∈ s, θ y * v y = θ t * v t + ∑ y ∈ s.erase t, θ y * v y :=
      (Finset.add_sum_erase s _ ht).symm
    have hrest : ∑ y ∈ s.erase t, θ y * v y = ∑ y ∈ s.erase t, θ y * u y +
        e * ∑ y ∈ s.erase t, θ y := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y hy => by
        simp only [hv, if_neg (Finset.ne_of_mem_erase hy)]; ring
    have hvt : v t = w - e := by simp [hv]
    rw [hB, hsplit, herase, hrest, hvt]
    have h1 : e * ∑ y ∈ s.erase t, θ y ≤ e := by nlinarith
    have h2 : θ t * (w - e) + ∑ y ∈ s.erase t, θ y * u y + e * ∑ y ∈ s.erase t, θ y -
        (w - e) = ∑ y ∈ s.erase t, θ y * u y + (θ t - 1) * w + e * ∑ y ∈ s.erase t, θ y +
        (1 - θ t) * e := by ring
    have h3 : (1 - θ t) * e ≤ e := by nlinarith [hθ0 t]
    linarith [h1, h2, h3]
  filter_upwards [hrivall, htgt, hlineB, self_mem_nhdsWithin] with η hr htg hl hpos
  have hp : (0 : ℝ) < η := hpos
  have hmono := lockTerm_mono s t ht (fun y => (M y).sup' (hM y) (fun m => σ y m η))
    (fun y => S0 y + η * v y) hr htg
  have h0 : lockTerm s t (fun y => S0 y + 0 * v y) = lockTerm s t S0 := by simp
  rw [h0] at hl
  have hfinal : η * (B + e) ≤ η * (∑ y ∈ s.erase t, θ y * u y + (θ t - 1) * w + ε) := by
    apply mul_le_mul_of_nonneg_left _ hp.le
    have : 3 * e < ε := by simp [he]; linarith
    linarith
  have goal : lockTerm s t (fun y => (M y).sup' (hM y) (fun m => σ y m η)) <
      lockTerm s t S0 + η * (∑ y ∈ s.erase t, θ y * u y + (θ t - 1) * w + ε) := by
    linarith
  simpa [hθ, hZ, hS0] using goal

/-- [proved-derived; formal-checked] **A sum of terms descends where their upper slopes sum below
zero**: if every term, for every `ε > 0`, lies below its value plus `η(m_k + ε)` for small `η > 0`,
and `Σ_k m_k < 0`, the sum is strictly lower for every small positive step (the composition's
first-order certificate, for any terms with such bounds: `sum_max_descends`'s hinges and the lock
faces of `lockFace_first_order` alike). -/
theorem sum_upper_dini_descends {κ : Type*} (K : Finset κ) (T : κ → ℝ → ℝ) (m : κ → ℝ)
    (hterm : ∀ k ∈ K, ∀ ε > 0, ∀ᶠ η in 𝓝[>] (0 : ℝ), T k η < T k 0 + η * (m k + ε))
    (hsum : ∑ k ∈ K, m k < 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∑ k ∈ K, T k η < ∑ k ∈ K, T k 0 := by
  set ε := -(∑ k ∈ K, m k) / (2 * (K.card + 1)) with hε
  have hcard : (0 : ℝ) < 2 * (K.card + 1) := by positivity
  have hεpos : 0 < ε := div_pos (by linarith) hcard
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ k ∈ K, T k η < T k 0 + η * (m k + ε) :=
    (Filter.eventually_all_finset K).mpr fun k hk => hterm k hk ε hεpos
  filter_upwards [hall, self_mem_nhdsWithin] with η hη hpos
  have hp : (0 : ℝ) < η := hpos
  by_cases hK : K = ∅
  · subst hK
    simp at hsum
  have hne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hK
  have hlt : ∑ k ∈ K, T k η < ∑ k ∈ K, (T k 0 + η * (m k + ε)) :=
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

end LockFaceFirstOrder

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
#print axioms hinge_zero_iff
#print axioms hinge_zero_at_tie
#print axioms hinge_right_leaves
#print axioms lockFace_pos
#print axioms lockFace_lt_log_two_iff
#print axioms lockFace_strictAnti
#print axioms lockFace_strictMono_rivals
#print axioms lockFace_ge_log_two_of_rival
#print axioms lockFace_enclosure_sublevel
#print axioms class_top_is_target
#print axioms lockFace_covector
#print axioms lockFace_share_lt_one
#print axioms decisions_release_the_section
#print axioms lockTerm_eq
#print axioms lockTerm_mono
#print axioms lockTerm_line
#print axioms sup_upper_dini
#print axioms lockFace_first_order
#print axioms sum_upper_dini_descends

end Audit

end Holonics.HNN.ExecutedComparison
