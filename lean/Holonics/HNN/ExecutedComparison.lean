import Holonics.HNN.BankFace
import Holonics.Holon.Element
import Holonics.HNN.Ratio.Certificate
import Holonics.Foundation.Standing
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

9. **The move's fixed points and one step's reach.** [proved-derived; formal-checked] A positive
   definite metric's step `−P g` rests exactly where `g = 0` (`metric_step_zero_iff`) and descends
   elsewhere (`metric_step_descends`). A full metric reaches every descent direction
   (`posDef_reach`), and a per-coordinate one exactly the sign-consistent directions
   (`diagonal_reach_iff`). A native step `M⁻¹Aᵀμ` is horizontal, with no hidden part
   (`native_step_horizontal`, with `Holon/Element.KineticFace`): the baseline for U6 step 1's
   ingredient (§9).

10. **A scale in the readings' own coordinates.** [proved-derived; formal-checked] A metric keeps
   every step in the native span exactly when it acts through a form `D` on the readings
   (`keeps_span_iff`, `hidden_eq_zero_iff`); every positive definite `D` gives a positive definite
   metric `P_D` stepping to the least-energy lift of `−D c` (`readingMetric_posDef`,
   `readingMetric_step`, `readingMetric_reads`). The normal law is `D = AM⁻¹Aᵀ`
   (`readingStep_normal`). A per-reading scale `D = diag(p)` rests only where `∇L = 0`
   (`readingStep_zero_iff`), descends by `⟨c, D c⟩` (`readingStep_slope`), reaches the
   sign-consistent reading changes (`reading_diagonal_reach`; a full `D`, every descending one,
   `reading_posDef_reach`), and is certified in the Fisher form (`reading_scale_descends`) (§10).

11. **The port's mass and the hidden directions.** [proved-derived; formal-checked] A direction no
   reading sees is never native under any positive mass (`hidden_never_native`); some mass makes
   `δ` native exactly when `A δ ≠ 0` (`native_under_some_mass_iff`). The smallest additive change
   is rank one (`deposit_makes_native`); through the feature Gram it is `k = Zᵀ (Z Δᵀ)⁻¹ Z`, needing
   `(X − Δ H) Δᵀ ⪰ 0` (`feature_deposit_makes_native`, `feature_deposit_native_needs`). The reading
   change and its certificate are mass-free, and a deposit never lowers the step's kinetic energy
   (`deposit_raises_native_energy`) (§11).

12. **The release guard.** [proved-derived; formal-checked] A move's change in the own release is
   its fixed mask's change, continuous and certified at first order, plus the flip of the
   successor's own decisions read against the incumbent's (`own_telescopes`). Each step certifies
   the fixed mask's fall. The own release is guarded over a window from a checkpoint: below the
   checkpoint's plus a height `h` throughout, and closing at most `W` steps on below the checkpoint's
   less `σ ≥ 0`, which holds exactly when the window's fixed-mask decreases exceed its flips by `σ`
   (`window_closes_iff`). `W = 1`, `h = 0` is the monotone guard (`checkpoint_one_iff`). The
   checkpoints descend by the certified decreases (`checkpoint_descends`), nothing exceeds the
   opening by more than `h` (`excursion_le_start`), and the decreases are summable
   (`checkpoints_sum_le`, `large_windows_card`). A divergent step sum, which the lattice floor
   supplies (`floor_steps_diverge`), drives the windows' least slope below every `ε`
   (`schedule_frequently_small`, `floor_large_slopes_card`). The parameters follow from the laws:
   a bounded comparison supplies the height (`excursion_of_bounded`); a window of one answers no
   flip (`one_move_closes_iff`) and a closing window is at least its flips over the largest
   per-move decrease (`window_length_lower`); a grain's decrease per window ends the chain
   (`grain_windows_bounded`) (§12).

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

/-! ## 8. Loop 1c: the landing's paired factorial and the restore law

[definition; agent-inferred, October 1] Loop 1c's pin (§1.1, §2.3;
`research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md`).
A later lock landing on a solved station's section is two parts, its normalization and its entry
(`IndexedOpen.transported_weight_insert`), and the paired counterfactual reads the four cells. A
sequential telescoping attribution depends on the order of the parts by exactly their interaction
(`telescoping_orders_differ_by_interaction`), and on a binary criterion it can name either part
(`sequential_attribution_depends_on_order`): no order is reported as the cause. The exact replay of a
complete continuing state reproduces the native continuation on every admitted future when the
restore inverts the state on the admitted constitutions (`restoreStanding`,
`restored_continuation_agrees`, `equal_states_agree`); that inversion is the Rust owner's
(`hnn::constitution::{ContinuingState, Constitution::continued}`), held by its test
`a_restored_checkpoint_continues_exactly_over_successive_receptions` and measured by the loop's
replay. -/

section LoopOneC

/-- [proved-derived; formal-checked] **The two telescoping orders of a two-part landing differ by
its interaction**: with the cells `f00` (neither part: the decision's reading), `f10` (the
normalization alone), `f01` (the entry alone) and `f11` (both: the native landing), the
normalization's step read first (`f10 − f00`) and read second (`f11 − f01`) differ by the
interaction `f11 − f10 − f01 + f00`, the entry's likewise, and each order sums to the whole change.
A telescoping attribution is order-free exactly when the interaction is zero. -/
theorem telescoping_orders_differ_by_interaction (f00 f10 f01 f11 : ℝ) :
    (f11 - f01) - (f10 - f00) = f11 - f10 - f01 + f00 ∧
      (f11 - f10) - (f01 - f00) = f11 - f10 - f01 + f00 ∧
      (f10 - f00) + (f11 - f10) = f11 - f00 ∧
      (f01 - f00) + (f11 - f01) = f11 - f00 :=
  ⟨by ring, by ring, by ring, by ring⟩

/-- [counterexample; formal-checked] **On a binary criterion a sequential attribution names either
part, by its order**: a station solved with neither part, with the normalization alone and with the
entry alone, and not solved with both. Read the normalization first, the entry's step undoes it;
read the entry first, the normalization's step does. -/
theorem sequential_attribution_depends_on_order :
    (fun n e : Bool => !(n && e)) true false = true ∧
      (fun n e : Bool => !(n && e)) true true = false ∧
      (fun n e : Bool => !(n && e)) false true = true :=
  ⟨rfl, rfl, rfl⟩

/-- [definition] **The restore law as a standing law** (gate A's owed item 3, stated here): with
`retain` the complete continuing state of a constitution and `restore` its continuation onto the
declared opening, `restore (retain θ) = θ` on the admitted constitutions makes the state a
`Foundation/Standing.StandingLaw`: every admitted future observation, any receiver after any word
of receptions, is read off the state alone. -/
def restoreStanding {Generator Receiver Source Retained Face : Type*}
    (transport : Generator → Source → Source) (observe : Receiver → Source → Face)
    (retain : Source → Retained) (restore : Retained → Source)
    (hrestore : ∀ θ, restore (retain θ) = θ) :
    Holonics.Foundation.Standing.StandingLaw Generator Receiver Source Retained Face where
  transport := transport
  observe := observe
  retain := retain
  reopen receiver word state :=
    observe receiver (Holonics.Foundation.Chronology.transportWord transport word (restore state))
  sufficient receiver word θ := by rw [hrestore]

/-- [proved-derived; formal-checked] **The restored continuation is the native one**: under the
restore law, every admitted future observation from the restored constitution equals the native
continuation's. -/
theorem restored_continuation_agrees {Generator Receiver Source Retained Face : Type*}
    (transport : Generator → Source → Source) (observe : Receiver → Source → Face)
    (retain : Source → Retained) (restore : Retained → Source)
    (hrestore : ∀ θ, restore (retain θ) = θ) (θ : Source) (receiver : Receiver)
    (word : List Generator) :
    observe receiver
        (Holonics.Foundation.Chronology.transportWord transport word (restore (retain θ))) =
      observe receiver (Holonics.Foundation.Chronology.transportWord transport word θ) := by
  rw [hrestore]

/-- [proved-derived; formal-checked] **Equal continuing states agree on every admitted future**
(`StandingLaw.futureAgreement_of_retain_eq` on `restoreStanding`): two constitutions with one state
are indistinguishable by every admitted receiver after every word. -/
theorem equal_states_agree {Generator Receiver Source Retained Face : Type*}
    (transport : Generator → Source → Source) (observe : Receiver → Source → Face)
    (retain : Source → Retained) (restore : Retained → Source)
    (hrestore : ∀ θ, restore (retain θ) = θ) {θ θ' : Source} (h : retain θ = retain θ') :
    Holonics.Foundation.CausalRelevance.NonLinear.futureAgreement observe transport θ θ' :=
  (restoreStanding transport observe retain restore hrestore).futureAgreement_of_retain_eq h

end LoopOneC

/-! ## 9. The move's fixed points and one step's reach

[definition; agent-inferred, October 2] Rebuild step U6, step 1: a baseline for the native move at
`E` alone against an exterior optimizer's ingredient
(`research/records/2026-10-02_THE_NATIVE_MOVE_AT_E_ALONE_ITS_FIXED_POINTS_AND_ONE_STEPS_REACH.md`).
Every candidate move is a metric's step `−P ∇L`, so all share `L`'s stationary points
(`metric_step_zero_iff`); they differ in reach. A full metric reaches every descent direction
(`posDef_reach`), a per-coordinate one exactly the sign-consistent directions
(`diagonal_reach_iff`), and the native family, `M⁻¹Aᵀμ`, exactly the readings' horizontal space
(`native_step_horizontal`). -/

section MoveReach

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **`metric_step_zero_iff`: a metric's step rests only where the
comparison does.** For a positive definite metric `P`, `P g = 0` exactly when `g = 0`: every move
`−P ∇L` (the normal law, the witness's span, the kinetic solve's first iterate, and an exterior
`sgd` or `rms` step, or `adam`'s without momentum, whose `P` is diagonal) has the stationary points
of `L` as its fixed points, whatever `P`, step size or schedule. -/
theorem metric_step_zero_iff {P : Matrix n n ℝ} (hP : P.PosDef) (g : n → ℝ) :
    P *ᵥ g = 0 ↔ g = 0 := by
  constructor
  · intro h
    by_contra hg
    have := hP.dotProduct_mulVec_pos hg
    simp [h] at this
  · rintro rfl; exact mulVec_zero _

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **`metric_step_descends`**: at `g ≠ 0` the step `−P g` of a
positive definite metric is a first-order descent, `⟨g, −P g⟩ < 0`. -/
theorem metric_step_descends {P : Matrix n n ℝ} (hP : P.PosDef) {g : n → ℝ} (hg : g ≠ 0) :
    g ⬝ᵥ (-(P *ᵥ g)) < 0 := by
  have := hP.dotProduct_mulVec_pos hg
  simp only [star_trivial] at this
  rw [dotProduct_neg]; linarith

/-- [proved-derived; formal-checked] **`diagonal_reach_iff`: a per-coordinate scale reaches exactly the
sign-consistent directions.** `d = −diag(p) g` for some `p > 0` iff every entry of `d` is zero where
`g` is and of the opposite sign where `g` is not. An exterior `rms` step, and an `adam` step without
momentum, is of this form (`adam`'s first step is `−η g/(|g| + ε)`, which is `−η sign g` at `ε = 0`;
with momentum it steps along its running average, not along `g`), so its one-step reach from a state
is fixed by the signs of the comparison's covector there. -/
theorem diagonal_reach_iff (g d : n → ℝ) :
    (∃ p : n → ℝ, (∀ i, 0 < p i) ∧ d = -(diagonal p *ᵥ g)) ↔
      ∀ i, (g i = 0 → d i = 0) ∧ (g i ≠ 0 → d i * g i < 0) := by
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    simp only [Pi.neg_apply, mulVec_diagonal]
    refine ⟨fun h => by simp [h], fun h => ?_⟩
    have := mul_pos (hp i) (mul_self_pos.mpr h)
    nlinarith
  · intro h
    refine ⟨fun i => if g i = 0 then 1 else -(d i) / g i, fun i => ?_, ?_⟩
    · by_cases hi : g i = 0
      · simp [hi]
      · simp only [hi, if_false]
        have h2 := (h i).2 hi
        rcases lt_or_gt_of_ne hi with hlt | hgt
        · exact div_pos_of_neg_of_neg (by nlinarith) hlt
        · exact div_pos (by nlinarith) hgt
    · funext i
      simp only [Pi.neg_apply, mulVec_diagonal]
      by_cases hi : g i = 0
      · simp [hi, (h i).1 hi]
      · simp only [hi, if_false]; field_simp

omit [DecidableEq n] in
/-- `(a bᵀ) x = (b · x) a`. -/
theorem vecMulVec_mulVec_eq (a b x : n → ℝ) : vecMulVec a b *ᵥ x = (b ⬝ᵥ x) • a := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] **`posDef_reach`: a full metric reaches every descent direction.**
At `g ≠ 0`, every `d` with `⟨d, g⟩ < 0` is `−P g` for a positive definite `P`
(`P = I − g gᵀ/|g|² − d dᵀ/⟨d, g⟩`). So a metric alone can point a step anywhere in the open
descent half-space: whatever separates two moves' reach from one state is the class of metric each
admits, not descent. -/
theorem posDef_reach {g d : n → ℝ} (hg : g ≠ 0) (hdg : d ⬝ᵥ g < 0) :
    ∃ P : Matrix n n ℝ, P.PosDef ∧ -(P *ᵥ g) = d := by
  set s : ℝ := g ⬝ᵥ g with hs
  have hs0 : 0 < s := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (g i))
    fun h => hg (dotProduct_self_eq_zero.mp h.symm)
  set c : ℝ := -(d ⬝ᵥ g)⁻¹ with hc
  have hc0 : 0 < c := by rw [hc]; exact neg_pos.mpr (inv_lt_zero.mpr hdg)
  have hcd : c * (d ⬝ᵥ g) = -1 := by rw [hc, neg_mul, inv_mul_cancel₀ hdg.ne]
  let P : Matrix n n ℝ := 1 - s⁻¹ • vecMulVec g g + c • vecMulVec d d
  have hPx : ∀ x, P *ᵥ x = x - (s⁻¹ * (g ⬝ᵥ x)) • g + (c * (d ⬝ᵥ x)) • d := by
    intro x
    simp only [P, add_mulVec, sub_mulVec, one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_eq,
      smul_smul]
  refine ⟨P, ?_, ?_⟩
  · refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · simp only [P, IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_add,
        transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
    · simp only [star_trivial]
      set t : ℝ := s⁻¹ * (g ⬝ᵥ x) with ht
      have hq : x ⬝ᵥ (P *ᵥ x) = (x - t • g) ⬝ᵥ (x - t • g) + c * (d ⬝ᵥ x) ^ 2 := by
        rw [hPx]
        simp only [dotProduct_add, dotProduct_sub, sub_dotProduct, dotProduct_smul,
          smul_dotProduct, smul_eq_mul, dotProduct_comm x g, dotProduct_comm x d]
        have : t * (t * s) = t * (g ⬝ᵥ x) := by
          rw [ht, hs]; field_simp
        rw [← hs]
        nlinarith [this]
      rw [hq]
      by_cases hr : x - t • g = 0
      · have hx' : x = t • g := sub_eq_zero.mp hr
        have ht0 : t ≠ 0 := by rintro h0; apply hx; rw [hx', h0, zero_smul]
        have hdx : d ⬝ᵥ x ≠ 0 := by
          rw [hx', dotProduct_smul, smul_eq_mul]; exact mul_ne_zero ht0 hdg.ne
        rw [hr, zero_dotProduct, zero_add]
        exact mul_pos hc0 (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdx)))
      · have h1 : 0 < (x - t • g) ⬝ᵥ (x - t • g) :=
          lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
            fun h => hr (dotProduct_self_eq_zero.mp h.symm)
        have h2 : 0 ≤ c * (d ⬝ᵥ x) ^ 2 := mul_nonneg hc0.le (sq_nonneg _)
        linarith
  · rw [hPx, ← hs, inv_mul_cancel₀ hs0.ne', one_smul, sub_self, zero_add, hcd, neg_one_smul,
      neg_neg]

open Holonics.HolonCore.KineticFace in
/-- [proved-derived; formal-checked] **`native_step_horizontal`: every native step is horizontal.**
A move `v = M⁻¹Aᵀμ` (the normal law's deposition of the returns at reading weights `μ`, every
iterate of the kinetic solve) is the least-energy lift of its own reading change and has no hidden
part: `horizontal(A v) = v`, `hidden v = 0`. With `KineticFace.energy_split`, a target `δ` splits
into `horizontal(A δ)`, which a native step reaches, and `hidden δ`, which no native step from this
state moves and no reading sees at first order. -/
theorem native_step_horizontal (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (μ : m → ℝ) :
    horizontal M A (A *ᵥ (M⁻¹ *ᵥ (Aᵀ *ᵥ μ))) = M⁻¹ *ᵥ (Aᵀ *ᵥ μ) ∧
      hidden M A (M⁻¹ *ᵥ (Aᵀ *ᵥ μ)) = 0 := by
  have hG := cometric_posDef M A hM hA
  have hi := nonsing_inv_mul (cometric M A) ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)
  have hr : A *ᵥ (M⁻¹ *ᵥ (Aᵀ *ᵥ μ)) = cometric M A *ᵥ μ := by
    simp only [cometric, mulVec_mulVec, Matrix.mul_assoc]
  have hh : horizontal M A (A *ᵥ (M⁻¹ *ᵥ (Aᵀ *ᵥ μ))) = M⁻¹ *ᵥ (Aᵀ *ᵥ μ) := by
    have hμ : (cometric M A)⁻¹ *ᵥ (cometric M A *ᵥ μ) = μ := by
      rw [mulVec_mulVec, hi, one_mulVec]
    rw [hr, horizontal, faceMetric, hμ]
  exact ⟨hh, by rw [Holonics.HolonCore.KineticFace.hidden, hh, sub_self]⟩

end MoveReach

/-! ## 10. A scale in the readings' own coordinates

[definition; agent-inferred, October 2] Rebuild step U6, step 1: which metrics keep the move in the
native span, and the per-reading scale as the candidate native counterpart of an exterior `rms`
step (`research/records/2026-10-02_A_METRIC_KEEPS_THE_MOVE_NATIVE_EXACTLY_WHEN_IT_ACTS_THROUGH_THE_READINGS.md`).
A metric keeps every step horizontal exactly when it acts through a form `D` on the readings
(`keeps_span_iff`); every positive definite `D` is such a metric (`readingMetric_posDef`,
`readingMetric_step`); the normal law is `D = AM⁻¹Aᵀ` (`readingStep_normal`); a per-reading scale
`D = diag(p)` is a member, with `L`'s fixed points (`readingStep_zero_iff`), the sign-consistent
reach in the readings (`reading_diagonal_reach`) and its Fisher-form certificate
(`reading_scale_descends`). -/

section ReadingScale

open Matrix Holonics.HolonCore.KineticFace

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- [definition] **The least-energy lift as a matrix**, `H = M⁻¹Aᵀ(AM⁻¹Aᵀ)⁻¹`: `H w` is
`KineticFace.horizontal M A w`, the least-energy move of `E` whose readings change by `w`. -/
def liftMatrix (M : Matrix n n ℝ) (A : Matrix m n ℝ) : Matrix n m ℝ :=
  M⁻¹ * Aᵀ * faceMetric M A

/-- `H w` is the horizontal lift of `w`. -/
theorem liftMatrix_mulVec (M : Matrix n n ℝ) (A : Matrix m n ℝ) (w : m → ℝ) :
    liftMatrix M A *ᵥ w = horizontal M A w := by
  simp only [liftMatrix, horizontal, mulVec_mulVec, Matrix.mul_assoc]

/-- `A H = 1`: the lift reads back its own reading change. -/
theorem reads_liftMatrix (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) : A * liftMatrix M A = 1 := by
  have hG := cometric_posDef M A hM hA
  have hi := mul_nonsing_inv (cometric M A) ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)
  rw [liftMatrix, faceMetric, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact hi

/-- A horizontal lift has no hidden part. -/
theorem hidden_horizontal (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (w : m → ℝ) : hidden M A (horizontal M A w) = 0 := by
  rw [Holonics.HolonCore.KineticFace.hidden, horizontal_reads M A hM hA, sub_self]

/-- [proved-derived; formal-checked] **`hidden_eq_zero_iff`: the horizontal space is the
native span.** A move `v` has no hidden part exactly when its momentum `M v` is a combination of
the readings' covectors, `Aᵀμ`: the moves the normal law and the kinetic solve can deposit. -/
theorem hidden_eq_zero_iff (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (v : n → ℝ) :
    hidden M A v = 0 ↔ ∃ μ : m → ℝ, M *ᵥ v = Aᵀ *ᵥ μ := by
  constructor
  · intro h
    have hv : v = horizontal M A (A *ᵥ v) := sub_eq_zero.mp h
    exact ⟨faceMetric M A *ᵥ (A *ᵥ v), by rw [hv, metric_horizontal M A hM, ← hv]⟩
  · rintro ⟨μ, hμ⟩
    have hi := nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit)
    have hv : v = M⁻¹ *ᵥ (Aᵀ *ᵥ μ) := by rw [← hμ, mulVec_mulVec, hi, one_mulVec]
    rw [hv]
    exact (native_step_horizontal M A hM hA μ).2

/-- [proved-derived; formal-checked] **`keeps_span_iff`: a metric keeps the move native exactly
when it acts through the readings.** For any `P`, every step `P ∇L` with `∇L = Aᵀc` is horizontal
iff every such step is the least-energy lift of the reading change `(A P Aᵀ) c`. So a span-keeping
metric acts on the comparison only through `D = A P Aᵀ`, its form on the readings' covectors; the
rest of `P` never moves `E`. -/
theorem keeps_span_iff (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (P : Matrix n n ℝ) :
    (∀ c, hidden M A (P *ᵥ (Aᵀ *ᵥ c)) = 0) ↔
      ∀ c, P *ᵥ (Aᵀ *ᵥ c) = horizontal M A ((A * P * Aᵀ) *ᵥ c) := by
  constructor
  · intro h c
    have hv := sub_eq_zero.mp (h c)
    rw [hv, mulVec_mulVec, mulVec_mulVec]
  · intro h c
    rw [h c]
    exact hidden_horizontal M A hM hA _

/-- [definition; agent-inferred] **The metric of a reading form `D`** on `E`:
`P_D = H D Hᵀ + (1 − HA) M⁻¹ (1 − HA)ᵀ`. The first term acts on the readings' covectors; the
second is the port's own cometric on the hidden directions, where no comparison covector lies. -/
def readingMetric (M : Matrix n n ℝ) (A : Matrix m n ℝ) (D : Matrix m m ℝ) : Matrix n n ℝ :=
  liftMatrix M A * D * (liftMatrix M A)ᵀ +
    (1 - liftMatrix M A * A) * M⁻¹ * (1 - liftMatrix M A * A)ᵀ

/-- `P_D Aᵀ = H D`. -/
theorem readingMetric_mul_transpose (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (D : Matrix m m ℝ) :
    readingMetric M A D * Aᵀ = liftMatrix M A * D := by
  have h1 := reads_liftMatrix M A hM hA
  have hT : (liftMatrix M A)ᵀ * Aᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have hZ : (1 - liftMatrix M A * A)ᵀ * Aᵀ = 0 := by
    rw [← transpose_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      sub_self, transpose_zero]
  rw [readingMetric, Matrix.add_mul, Matrix.mul_assoc (liftMatrix M A * D), hT, Matrix.mul_one,
    Matrix.mul_assoc ((1 - liftMatrix M A * A) * M⁻¹), hZ, Matrix.mul_zero, add_zero]

/-- [proved-derived; formal-checked] **`readingMetric_step`**: `P_D` steps from `∇L = Aᵀc` to
the least-energy lift of the reading change `D c`. -/
theorem readingMetric_step (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (D : Matrix m m ℝ) (c : m → ℝ) :
    readingMetric M A D *ᵥ (Aᵀ *ᵥ c) = horizontal M A (D *ᵥ c) := by
  rw [mulVec_mulVec, readingMetric_mul_transpose M A hM hA, ← mulVec_mulVec, liftMatrix_mulVec]

/-- `A P_D Aᵀ = D`: `P_D` is the metric whose form on the readings is `D`. -/
theorem readingMetric_reads (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (D : Matrix m m ℝ) :
    A * readingMetric M A D * Aᵀ = D := by
  rw [Matrix.mul_assoc, readingMetric_mul_transpose M A hM hA, ← Matrix.mul_assoc,
    reads_liftMatrix M A hM hA, Matrix.one_mul]

/-- [proved-derived; formal-checked] **`readingMetric_posDef`**: for every positive definite
reading form `D`, `P_D` is a positive definite metric on `E`. With `readingMetric_step` and
`keeps_span_iff`, the span-keeping positive definite metrics act on the comparison exactly as the
family `P_D`, `D ≻ 0`. -/
theorem readingMetric_posDef (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    {D : Matrix m m ℝ} (hD : D.PosDef) :
    (readingMetric M A D).PosDef := by
  set H := liftMatrix M A with hH
  set Z : Matrix n n ℝ := 1 - H * A with hZdef
  have hDs : Dᵀ = D := by simpa only [conjTranspose_eq_transpose_of_trivial] using hD.1.eq
  have hMs : (M⁻¹)ᵀ = M⁻¹ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hM.inv.1.eq
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · simp only [readingMetric, ← hH, ← hZdef, IsHermitian, conjTranspose_eq_transpose_of_trivial,
      transpose_add, transpose_mul, transpose_transpose, hDs, hMs, Matrix.mul_assoc]
  · simp only [star_trivial]
    set u := Hᵀ *ᵥ x with hu
    set z := Zᵀ *ᵥ x with hz
    have hq : x ⬝ᵥ (readingMetric M A D *ᵥ x) = u ⬝ᵥ (D *ᵥ u) + z ⬝ᵥ (M⁻¹ *ᵥ z) := by
      simp only [readingMetric, ← hH, ← hZdef, add_mulVec, dotProduct_add, ← mulVec_mulVec]
      rw [← dotProduct_transpose_mulVec H, ← dotProduct_transpose_mulVec Z]
      simp only [hu, hz, dotProduct_comm]
    have hzx : z = x - Aᵀ *ᵥ u := by
      rw [hz, hu, hZdef, transpose_sub, transpose_one, transpose_mul, sub_mulVec, one_mulVec,
        mulVec_mulVec]
    rw [hq]
    by_cases hz0 : z = 0
    · have hx' : x = Aᵀ *ᵥ u := by rw [hz0] at hzx; exact (sub_eq_zero.mp hzx.symm)
      have hu0 : u ≠ 0 := by rintro h0; apply hx; rw [hx', h0, mulVec_zero]
      have h1 := hD.dotProduct_mulVec_pos hu0
      simp only [star_trivial, hz0, zero_dotProduct, add_zero] at h1 ⊢
      exact h1
    · have h2 := hM.inv.dotProduct_mulVec_pos hz0
      have h1 := hD.posSemidef.dotProduct_mulVec_nonneg u
      simp only [star_trivial] at h1 h2
      linarith

/-- [proved-derived; formal-checked] **`readingStep_normal`: the normal law is the member
`D = AM⁻¹Aᵀ`**, the readings' Gram in the port's cometric: its lift of `−D c` is `−M⁻¹Aᵀc`.
[agent-inferred] By its Rust owner's statement (`hnn::executed::KineticSolve`), the kinetic solve
is the member `D = F⁻¹` where the witness's Fisher form `F` is invertible on the readings. -/
theorem readingStep_normal (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (c : m → ℝ) :
    horizontal M A (cometric M A *ᵥ c) = M⁻¹ *ᵥ (Aᵀ *ᵥ c) := by
  have hG := cometric_posDef M A hM hA
  have hi := nonsing_inv_mul (cometric M A) ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)
  have hc : (cometric M A)⁻¹ *ᵥ (cometric M A *ᵥ c) = c := by rw [mulVec_mulVec, hi, one_mulVec]
  rw [horizontal, faceMetric, hc]

/-- [proved-derived; formal-checked] **`readingStep_zero_iff`: the fixed points.** For `D ≻ 0`
the step from `Aᵀc` rests exactly where `∇L = Aᵀc = 0`: no reading form changes where the move
can rest. -/
theorem readingStep_zero_iff (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) {D : Matrix m m ℝ} (hD : D.PosDef) (c : m → ℝ) :
    horizontal M A (-(D *ᵥ c)) = 0 ↔ Aᵀ *ᵥ c = 0 := by
  constructor
  · intro h
    have hr : D *ᵥ c = 0 := by
      have := horizontal_reads M A hM hA (-(D *ᵥ c))
      rw [h, mulVec_zero] at this
      exact neg_eq_zero.mp this.symm
    rw [(metric_step_zero_iff hD c).mp hr, mulVec_zero]
  · intro h
    have hc : c = 0 := transpose_injective A hA (by rw [h, mulVec_zero])
    simp [hc, horizontal]

/-- [proved-derived; formal-checked] **`readingStep_slope`**: the step's first-order change of
`L` is `−⟨c, D c⟩`, read in the readings alone. -/
theorem readingStep_slope (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (D : Matrix m m ℝ) (c : m → ℝ) :
    (Aᵀ *ᵥ c) ⬝ᵥ horizontal M A (-(D *ᵥ c)) = -(c ⬝ᵥ (D *ᵥ c)) := by
  rw [dotProduct_comm, dotProduct_transpose_mulVec, horizontal_reads M A hM hA, dotProduct_neg]

/-- [proved-derived; formal-checked] **`reading_diagonal_reach`: a per-reading scale's reach.**
The steps `−H diag(p) c`, `p > 0`, are exactly the horizontal moves whose reading change is zero
where `c` is and of the opposite sign where it is not: §9's sign-consistent reach, taken in the
readings' coordinates and lifted. -/
theorem reading_diagonal_reach (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (hA : Function.Surjective A.mulVec) (c : m → ℝ) (v : n → ℝ) :
    (∃ p : m → ℝ, (∀ k, 0 < p k) ∧ v = horizontal M A (-(diagonal p *ᵥ c))) ↔
      hidden M A v = 0 ∧
        ∀ k, (c k = 0 → (A *ᵥ v) k = 0) ∧ (c k ≠ 0 → (A *ᵥ v) k * c k < 0) := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hidden_horizontal M A hM hA _, (diagonal_reach_iff c _).mp ⟨p, hp, ?_⟩⟩
    rw [horizontal_reads M A hM hA]
  · rintro ⟨hv, hs⟩
    obtain ⟨p, hp, hr⟩ := (diagonal_reach_iff c (A *ᵥ v)).mpr hs
    exact ⟨p, hp, by rw [← hr]; exact sub_eq_zero.mp hv⟩

/-- [proved-derived; formal-checked] **`reading_posDef_reach`: a full reading form's reach.** At
`c ≠ 0`, every horizontal move whose reading change descends, `⟨A v, c⟩ < 0`, is `−H D c` for a
positive definite `D`. -/
theorem reading_posDef_reach (M : Matrix n n ℝ) (A : Matrix m n ℝ) {c : m → ℝ} (hc : c ≠ 0) {v : n → ℝ}
    (hv : hidden M A v = 0) (hd : (A *ᵥ v) ⬝ᵥ c < 0) :
    ∃ D : Matrix m m ℝ, D.PosDef ∧ v = horizontal M A (-(D *ᵥ c)) := by
  obtain ⟨D, hD, hr⟩ := posDef_reach hc hd
  exact ⟨D, hD, by rw [hr]; exact sub_eq_zero.mp hv⟩

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
open Holonics.HNN.Ratio.Certificate in
/-- [proved-derived; formal-checked] **`reading_scale_descends`: the per-reading step's
certificate in the Fisher form.** On one sheet of readings with face `p` and target `t`
(covector `c = p − e_t`), the reading change `−η (d ⊙ c)` of a per-reading scale `d` lowers the
code by at least `η Σ d_k c_k²/2` when `η · ln 2 · 2^ω · Var_p(d ⊙ c) ≤ Σ d_k c_k²` and the
change's spread is at most `ω`. `Var_p(d ⊙ c)` is the Fisher form `(d ⊙ c)ᵀ J_p (d ⊙ c)`
(`HNN/Ratio/Certificate.codeLength_step_descends`). It certifies the readings' first-order
change `A v`; where the readings are not linear in `E`, the move's guards certify the trial
whole. -/
theorem reading_scale_descends {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (f p d : ι → ℝ) (hp : ∀ k, p k = (2 : ℝ) ^ f k / ∑ l, (2 : ℝ) ^ f l) (t : ι) {η ω : ℝ}
    (hη : 0 ≤ η)
    (hosc : ∀ a b, η * (d b * (p b - (Pi.single t (1 : ℝ) : ι → ℝ) b) -
      d a * (p a - (Pi.single t (1 : ℝ) : ι → ℝ) a)) ≤ ω)
    (hstep : η * (Real.log 2 * (2 : ℝ) ^ ω *
        faceVariance p (fun k => d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k))) ≤
      ∑ k, d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k) ^ 2) :
    Holonics.HNN.Ratio.codeLength
        (fun k => f k - η * (d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k))) t ≤
      Holonics.HNN.Ratio.codeLength f t -
        η * (∑ k, d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k) ^ 2) / 2 := by
  have hsum : ∑ k, (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k) *
      (d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k)) =
      ∑ k, d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring
  have h := codeLength_step_descends f
    (fun k => d k * (p k - (Pi.single t (1 : ℝ) : ι → ℝ) k)) p hp hη hosc t (by rw [hsum]; exact hstep)
  rw [hsum] at h
  exact h

end ReadingScale

/-! ## 11. The port's mass and the hidden directions

[definition; agent-inferred, October 2] Rebuild step U6, step 1: if an exterior step's gain lies in
the directions no reading sees, what change of the port's mass `M = I ⊗ H′` carries it natively
(`research/records/2026-10-02_NO_MASS_MAKES_A_HIDDEN_DIRECTION_VISIBLE_THE_DEPOSIT_CAN_ONLY_TILT_A_VISIBLE_STEP.md`).
A direction no reading sees is never native under any mass (`hidden_never_native`); a mass change
can only tilt the lift of a visible reading change (`native_under_some_mass_iff`), by a rank-one
addition (`deposit_makes_native`) or, through the feature Gram, a deposit of rank at most the rows'
under a condition on every pair of rows (`feature_deposit_makes_native`,
`feature_deposit_native_needs`). The change leaves the step's reading change and its Fisher-form
certificate unchanged and never lowers its kinetic energy (`deposit_raises_native_energy`). -/

section PortMass

open Matrix Holonics.HolonCore.KineticFace

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- [proved-derived; formal-checked] **`hidden_never_native`: no mass makes a direction no
reading sees native.** If `A δ = 0` and `M δ = Aᵀμ` for a positive definite `M`, then `δ = 0`:
`⟨δ, M δ⟩ = ⟨A δ, μ⟩ = 0`. Visibility, `A δ ≠ 0`, is set by the readings alone, and a native step
is the least-energy lift of a reading change, so a purely hidden direction is the lift of zero under
every mass. -/
theorem hidden_never_native {M : Matrix n n ℝ} (hM : M.PosDef) (A : Matrix m n ℝ) {δ : n → ℝ}
    (hread : A *ᵥ δ = 0) {μ : m → ℝ} (hmom : M *ᵥ δ = Aᵀ *ᵥ μ) : δ = 0 := by
  by_contra hδ
  have hp := hM.dotProduct_mulVec_pos hδ
  simp only [star_trivial] at hp
  rw [hmom, dotProduct_transpose_mulVec, hread, dotProduct_zero] at hp
  exact lt_irrefl _ hp

omit [DecidableEq m] in
/-- [proved-derived; formal-checked] **`native_under_some_mass_iff`: some positive mass makes
`δ` native exactly when a reading sees it.** `M δ = Aᵀμ` for some `M ≻ 0` and `μ` iff `δ = 0` or
`A δ ≠ 0` (`M` from `posDef_reach` with `μ = A δ`). A mass change can only choose which lift of a
visible reading change the native step deposits; it can tilt that lift into hidden directions. -/
theorem native_under_some_mass_iff (A : Matrix m n ℝ) (δ : n → ℝ) :
    (∃ M : Matrix n n ℝ, M.PosDef ∧ ∃ μ : m → ℝ, M *ᵥ δ = Aᵀ *ᵥ μ) ↔
      (δ = 0 ∨ A *ᵥ δ ≠ 0) := by
  constructor
  · rintro ⟨M, hM, μ, hmom⟩
    by_cases hr : A *ᵥ δ = 0
    · exact Or.inl (hidden_never_native hM A hr hmom)
    · exact Or.inr hr
  · rintro (rfl | hr)
    · exact ⟨1, PosDef.one, 0, by simp⟩
    · have hδ : δ ≠ 0 := by rintro rfl; exact hr (mulVec_zero _)
      have hpos : 0 < (A *ᵥ δ) ⬝ᵥ (A *ᵥ δ) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
          fun h => hr (dotProduct_self_eq_zero.mp h.symm)
      have hd : (-(Aᵀ *ᵥ (A *ᵥ δ))) ⬝ᵥ δ < 0 := by
        rw [neg_dotProduct, dotProduct_comm, dotProduct_transpose_mulVec]
        linarith
      obtain ⟨P, hP, hPd⟩ := posDef_reach hδ hd
      exact ⟨P, hP, A *ᵥ δ, neg_injective hPd⟩

omit [DecidableEq n] [DecidableEq m] in
/-- [proved-derived; formal-checked] **`deposit_makes_native`: the smallest additive change.**
With `z = Aᵀμ − M δ` and `⟨δ, z⟩ > 0`, the rank-one positive semidefinite addition
`K = z zᵀ/⟨δ, z⟩` keeps the mass positive definite and makes `δ` native: `(M + K) δ = Aᵀμ`. A
`μ` with `⟨δ, z⟩ = ⟨A δ, μ⟩ − ⟨δ, M δ⟩ > 0` exists exactly when `A δ ≠ 0`. A deposit only adds,
so this is the least-rank change the deposit's sign admits. -/
theorem deposit_makes_native {M : Matrix n n ℝ} (hM : M.PosDef) (A : Matrix m n ℝ)
    (δ : n → ℝ) (μ : m → ℝ) (hz : 0 < δ ⬝ᵥ (Aᵀ *ᵥ μ - M *ᵥ δ)) :
    let z := Aᵀ *ᵥ μ - M *ᵥ δ
    let K := (δ ⬝ᵥ z)⁻¹ • vecMulVec z z
    K.PosSemidef ∧ (M + K).PosDef ∧ (M + K) *ᵥ δ = Aᵀ *ᵥ μ := by
  intro z K
  have hK : K.PosSemidef := by
    refine PosSemidef.smul ?_ (inv_nonneg.mpr hz.le)
    simpa using posSemidef_vecMulVec_self_star z
  refine ⟨hK, hM.add_posSemidef hK, ?_⟩
  rw [add_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_eq, smul_smul,
    dotProduct_comm z δ, inv_mul_cancel₀ hz.ne', one_smul]
  simp only [z]; abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- [proved-derived; formal-checked] **`feature_deposit_makes_native`: the same change through
the feature Gram.** The port's mass acts on `E`'s rows through one feature Gram, `V ↦ V H`
(`M = I ⊗ H′`), and the deposit changes only `H` (`ΔH = Σ w f fᵀ`). For a target `Δ` and a
momentum `X` (a combination of the readings' covectors in `E`'s shape), with `Z = X − Δ H`: if
`Z Δᵀ` is positive definite, the feature deposit `k = Zᵀ (Z Δᵀ)⁻¹ Z` is positive semidefinite, of
rank at most the rows', and `Δ (H + k) = X`. -/
theorem feature_deposit_makes_native {r : Type*} [Fintype r] [DecidableEq r]
    (Δ X : Matrix r n ℝ) (H : Matrix n n ℝ) (hY : ((X - Δ * H) * Δᵀ).PosDef) :
    let Z := X - Δ * H
    let k := Zᵀ * ((X - Δ * H) * Δᵀ)⁻¹ * Z
    k.PosSemidef ∧ Δ * (H + k) = X := by
  intro Z k
  have hYs : ((X - Δ * H) * Δᵀ)ᵀ = (X - Δ * H) * Δᵀ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hY.1.eq
  have hi := mul_nonsing_inv ((X - Δ * H) * Δᵀ) ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)
  refine ⟨?_, ?_⟩
  · simpa only [conjTranspose_eq_transpose_of_trivial] using
      hY.inv.posSemidef.conjTranspose_mul_mul_same Z
  · have hΔk : Δ * k = Z := by
      have hΔZ : Δ * Zᵀ = ((X - Δ * H) * Δᵀ)ᵀ := by
        rw [transpose_mul, transpose_transpose]
      simp only [k, ← Matrix.mul_assoc]
      rw [hΔZ, hYs, hi, Matrix.one_mul]
    rw [Matrix.mul_add, hΔk]
    simp only [Z]; abel

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- [proved-derived; formal-checked] **`feature_deposit_native_needs`: and it is needed.** If a
positive semidefinite feature deposit `k` gives `Δ (H + k) = X`, then `(X − Δ H) Δᵀ = Δ k Δᵀ` is
positive semidefinite. So a feature deposit can make `Δ` native toward `X` only where
`(X − Δ H) Δᵀ` is symmetric and positive semidefinite. Its entry `(i, j)` pairs row `i`'s needed
change `Z_i` with row `j`'s target `Δ_j`, so one Gram serving every row binds every pair of rows; a
target fails it wherever a row's needed change opposes its own target, `⟨Z_i, Δ_i⟩ < 0`. -/
theorem feature_deposit_native_needs {r : Type*} [Fintype r] [DecidableEq r]
    (Δ X : Matrix r n ℝ) (H k : Matrix n n ℝ) (hk : k.PosSemidef) (hX : Δ * (H + k) = X) :
    ((X - Δ * H) * Δᵀ).PosSemidef := by
  have : X - Δ * H = Δ * k := by rw [← hX, Matrix.mul_add]; abel
  rw [this]
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    hk.mul_mul_conjTranspose_same Δ

/-- [proved-derived; formal-checked] **`deposit_raises_native_energy`: the cost.** Every native
step's reading change is the same under any mass (`KineticFace.horizontal_reads`), so a mass change
leaves the step's first-order decrease and its Fisher-form certificate on the readings
(`reading_scale_descends`) unchanged. What it changes is the step's kinetic energy: after a
deposit `K ⪰ 0`, the least energy of a reading change `w`, `½⟨w, (A M⁻¹ Aᵀ)⁻¹ w⟩`, does not
fall. -/
theorem deposit_raises_native_energy {M K : Matrix n n ℝ} (hM : M.PosDef) (hK : K.PosSemidef)
    (A : Matrix m n ℝ) (hA : Function.Surjective A.mulVec) (w : m → ℝ) :
    Holonics.HolonCore.storageEnergy (faceMetric M A) w ≤
      Holonics.HolonCore.storageEnergy (faceMetric (M + K) A) w := by
  have hMK : (M + K).PosDef := hM.add_posSemidef hK
  set v := horizontal (M + K) A w
  have hread : A *ᵥ v = w := horizontal_reads (M + K) A hMK hA w
  have h1 := (unique_minimum_energy M A hM hA w v hread).1
  have h3 := ((unique_minimum_energy (M + K) A hMK hA w v hread).2).mpr rfl
  have h2 : Holonics.HolonCore.storageEnergy M v ≤ Holonics.HolonCore.storageEnergy (M + K) v := by
    unfold Holonics.HolonCore.storageEnergy
    have := hK.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at this
    rw [add_mulVec, dotProduct_add]
    nlinarith
  linarith

end PortMass

/-! ## 12. The release guard: a certified fixed-mask step and an excursion above a checkpoint

The release guard (`OwnNotBelow` in the Rust owner) adopted a successor only when its own release's
comparison fell strictly below the incumbent's (§4). The plain-gradient path that reaches the
sections does not: its own comparison rises above its opening before it falls. This section states
what the guard compares and the law that follows that path.

**What changes along a move.** Let `f k` be the own release's comparison at the `k`-th adopted
state and `m k` the incumbent's fixed mask read at the successor (the incumbent's decisions kept).
At the incumbent the two agree, so `f (k+1) − f k = (m k − f k) + (f (k+1) − m k)`. The first term
is the fixed mask's change, continuous along the move and the object of the first-order certificate
(§3, §4); the second is the **flip**, the successor's own decisions read against the incumbent's on
the same `E`, discontinuous where a decision changes (`own_telescopes`). The flip is re-read once,
at the next move, whose incumbent is the successor's own release.

**The law.** Each adopted step certifies the fixed mask's fall (unchanged). The own release is
guarded over a window: from a checkpoint `t n`, every comparison until the next checkpoint stays
below the checkpoint's plus a height `h`, and the next checkpoint, at most `W` steps on, lies below
the checkpoint's less a certified decrease `σ n ≥ 0`. A window that does not close returns to its
checkpoint. `W = 1` and `h = 0` is the monotone guard (`checkpoint_one_iff`). The window closes
exactly when the certified fixed-mask decreases exceed the window's net flips by `σ`
(`window_closes_iff`). -/

section ReleaseGuard

/-- [proved-derived; formal-checked] **A move's change is its fixed mask's change and its flip**:
`f n − f 0 = Σ_(k<n) (m k − f k) + Σ_(k<n) (f (k+1) − m k)`. -/
theorem own_telescopes (f m : ℕ → ℝ) (n : ℕ) :
    f n - f 0 = ∑ k ∈ Finset.range n, (m k - f k) + ∑ k ∈ Finset.range n, (f (k + 1) - m k) := by
  rw [← Finset.sum_add_distrib]
  simp only [sub_add_sub_cancel']
  exact (Finset.sum_range_sub f n).symm

/-- [proved-derived; formal-checked] **A window closes exactly when its fixed-mask decreases exceed
its flips**: from `a` to `b ≥ a`, `f b ≤ f a − σ` iff
`Σ_(a≤k<b) (f (k+1) − m k) ≤ Σ_(a≤k<b) (f k − m k) − σ`. -/
theorem window_closes_iff (f m : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) (σ : ℝ) :
    f b ≤ f a - σ ↔
      ∑ k ∈ Finset.Ico a b, (f (k + 1) - m k) ≤ ∑ k ∈ Finset.Ico a b, (f k - m k) - σ := by
  have htel : ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) = f b - f a :=
    Finset.sum_Ico_sub f hab
  have hsplit : ∑ k ∈ Finset.Ico a b, (f (k + 1) - f k) =
      ∑ k ∈ Finset.Ico a b, (f (k + 1) - m k) - ∑ k ∈ Finset.Ico a b, (f k - m k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  constructor <;> intro h <;> linarith

/-- The checkpoint guard on a chain of comparisons `f` with checkpoints `t` (`t 0 = 0`): every
comparison of the `n`-th window lies below its checkpoint's plus `h`, and the window closes at most
`W` steps on, below its checkpoint's less `σ n`. -/
structure CheckpointGuard (f : ℕ → ℝ) (t : ℕ → ℕ) (W : ℕ) (h : ℝ) (σ : ℕ → ℝ) : Prop where
  start : t 0 = 0
  advances : ∀ n, t n < t (n + 1)
  length : ∀ n, t (n + 1) ≤ t n + W
  excursion : ∀ n j, t n ≤ j → j ≤ t (n + 1) → f j ≤ f (t n) + h
  closes : ∀ n, f (t (n + 1)) ≤ f (t n) - σ n

/-- [proved-derived; formal-checked] **The guard of one step and no height is the monotone
guard**: checkpoints at every step with `h = 0` hold exactly when `f (n+1) ≤ f n − σ n` for every
`n`, with `σ ≥ 0`. -/
theorem checkpoint_one_iff (f σ : ℕ → ℝ) (hσ : ∀ n, 0 ≤ σ n) :
    CheckpointGuard f id 1 0 σ ↔ ∀ n, f (n + 1) ≤ f n - σ n := by
  constructor
  · intro g n
    simpa using g.closes n
  · intro hf
    refine ⟨rfl, fun n => Nat.lt_succ_self n, fun n => le_rfl, fun n j hlo hhi => ?_,
      fun n => by simpa using hf n⟩
    simp only [id, add_zero] at hlo hhi ⊢
    rcases Nat.eq_or_lt_of_le hhi with rfl | hlt
    · linarith [hf n, hσ n]
    · rw [le_antisymm (Nat.lt_succ_iff.mp hlt) hlo]

/-- [proved-derived; formal-checked] **The checkpoints descend by the certified decreases**:
`f (t n) ≤ f 0 − Σ_(b<n) σ b`. -/
theorem checkpoint_descends {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) (n : ℕ) :
    f (t n) ≤ f 0 - ∑ b ∈ Finset.range n, σ b := by
  induction n with
  | zero => simp [g.start]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [g.closes n]

/-- [proved-derived; formal-checked] **No comparison exceeds the opening's by more than the
height**: in the `n`-th window, `f j ≤ f 0 + h` (with `σ ≥ 0`). -/
theorem excursion_le_start {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) (hσ : ∀ n, 0 ≤ σ n) {n j : ℕ} (hlo : t n ≤ j)
    (hhi : j ≤ t (n + 1)) : f j ≤ f 0 + h := by
  have h1 := g.excursion n j hlo hhi
  have h2 := checkpoint_descends g n
  have h3 : 0 ≤ ∑ b ∈ Finset.range n, σ b := Finset.sum_nonneg fun b _ => hσ b
  linarith

/-- [proved-derived; formal-checked] **The excursion check on enclosures is sound**: with the
checkpoint's comparison at least `L` and the successor's at most `U`, `U ≤ L + h` gives
`f ≤ f_checkpoint + h`; at `h = 0` with strict `<` it is §4's disjoint enclosures. -/
theorem excursion_enclosure {F F' L U h : ℝ} (hF : L ≤ F) (hF' : F' ≤ U) (hcheck : U ≤ L + h) :
    F' ≤ F + h := by
  linarith

/-- [proved-derived; formal-checked] **The certified decreases are summable**: below a floor
`m ≤ f`, `Σ_(b<n) σ b ≤ f 0 − m`. -/
theorem checkpoints_sum_le {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) {m : ℝ} (hm : ∀ k, m ≤ f k) (n : ℕ) :
    ∑ b ∈ Finset.range n, σ b ≤ f 0 - m := by
  linarith [checkpoint_descends g n, hm (t n)]

/-- [proved-derived; formal-checked] **Few windows certify much**: with `σ ≥ 0`, at most
`(f 0 − m)/ε` of the first `n` windows certify `ε` or more. -/
theorem large_windows_card {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) (hσ : ∀ n, 0 ≤ σ n) {m : ℝ} (hm : ∀ k, m ≤ f k) {ε : ℝ}
    (n : ℕ) : (((Finset.range n).filter fun b => ε ≤ σ b).card : ℝ) * ε ≤ f 0 - m := by
  have hsum := checkpoints_sum_le g hm n
  have hfilter : ∑ b ∈ (Finset.range n).filter (fun b => ε ≤ σ b), σ b ≤
      ∑ b ∈ Finset.range n, σ b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ => hσ b
  have hcard : (((Finset.range n).filter fun b => ε ≤ σ b).card : ℝ) * ε ≤
      ∑ b ∈ (Finset.range n).filter (fun b => ε ≤ σ b), σ b := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2
  linarith

/-- [proved-derived; formal-checked] **The schedule's condition**: let each window's certified
decrease be `s b = η b · q b` with steps `η b ≥ 0` whose sum diverges (every bound is passed by some
partial sum). If the decreases sum below `C`, then `q` falls below every `ε > 0` in windows beyond
every `N`. With `q b` the window's least certified slope this is the guarded path reaching the
neighbourhood of `L`'s fixed points; with a summable `η` nothing is certified. -/
theorem schedule_frequently_small (η q : ℕ → ℝ) (hη : ∀ b, 0 ≤ η b)
    (hdiv : ∀ C, ∃ n, C < ∑ b ∈ Finset.range n, η b) {C : ℝ}
    (hsum : ∀ n, ∑ b ∈ Finset.range n, η b * q b ≤ C) (hq : ∀ b, 0 ≤ q b) {ε : ℝ} (hε : 0 < ε)
    (N : ℕ) : ∃ b, N ≤ b ∧ q b < ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := hdiv ((C + ε * ∑ b ∈ Finset.range N, η b) / ε)
  have hNn : N ≤ n ∨ n < N := le_or_gt N n
  have hhead : ∑ b ∈ Finset.range N, η b * q b ≥ 0 :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hη b) (hq b)
  rcases hNn with hNn | hNn
  · have hsplit := Finset.sum_range_add_sum_Ico (fun b => η b * q b) hNn
    have hsplitη := Finset.sum_range_add_sum_Ico η hNn
    have htail : ε * ∑ b ∈ Finset.Ico N n, η b ≤ ∑ b ∈ Finset.Ico N n, η b * q b := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun b hb =>
        by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hcon b (Finset.mem_Ico.mp hb).1) (hη b)
    have hlt : C + ε * ∑ b ∈ Finset.range N, η b < ε * ∑ b ∈ Finset.range n, η b := by
      rw [div_lt_iff₀ hε] at hn; linarith
    have := hsum n
    nlinarith
  · have hsub : ∑ b ∈ Finset.range n, η b ≤ ∑ b ∈ Finset.range N, η b :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNn.le) fun b _ _ => hη b
    have hC : 0 ≤ C := (hsum 0).trans' (by simp)
    rw [div_lt_iff₀ hε] at hn
    nlinarith

/-- [proved-derived; formal-checked] **A step floor makes the step sum diverge**: every adopted move
of the ladder moves at least one lattice coordinate, so its step is at least `c > 0` (with the unit
move's largest entry bounded); then every bound is passed by some partial sum. -/
theorem floor_steps_diverge (η : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hη : ∀ k, c ≤ η k) (C : ℝ) :
    ∃ n, C < ∑ k ∈ Finset.range n, η k := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / c)
  refine ⟨n, ?_⟩
  have hsum : (n : ℝ) * c ≤ ∑ k ∈ Finset.range n, η k := by
    have := Finset.sum_le_sum fun k (_ : k ∈ Finset.range n) => hη k
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  rw [div_lt_iff₀ hc] at hn
  linarith

/-- [proved-derived; formal-checked] **Under a step floor the slopes themselves are summable**: if
each window's certified decrease is at least `c · q n` with `c > 0` (a positive margin times the floor
step), at most `(f 0 − m)/(c ε)` of the first `n` windows have least slope `q ≥ ε`: the slope falls
below every `ε` in all but finitely many windows. -/
theorem floor_large_slopes_card {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ q : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) {c : ℝ} (hc : 0 < c) (hs : ∀ n, c * q n ≤ σ n)
    (hq0 : ∀ n, 0 ≤ q n) {m : ℝ} (hm : ∀ k, m ≤ f k) {ε : ℝ} (n : ℕ) :
    (((Finset.range n).filter fun b => ε ≤ q b).card : ℝ) * (c * ε) ≤ f 0 - m := by
  have hσ : ∀ n, 0 ≤ σ n := fun n => (mul_nonneg hc.le (hq0 n)).trans (hs n)
  have hsum := checkpoints_sum_le g hm n
  have hfilter : ∑ b ∈ (Finset.range n).filter (fun b => ε ≤ q b), c * q b ≤
      ∑ b ∈ Finset.range n, σ b :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b _ _ =>
      mul_nonneg hc.le (hq0 b)).trans (Finset.sum_le_sum fun b _ => hs b)
  have hcard : (((Finset.range n).filter fun b => ε ≤ q b).card : ℝ) * (c * ε) ≤
      ∑ b ∈ (Finset.range n).filter (fun b => ε ≤ q b), c * q b := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun b hb =>
      mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hb).2 hc.le
  linarith

/-- [proved-derived; formal-checked] **A window of one move must pay its flip from the same move**:
`f (a+1) ≤ f a − σ` iff the move's flip is at most its fixed-mask decrease less `σ`. The decrease
was certified before the flip was read, so this window answers no flip. -/
theorem one_move_closes_iff (f m : ℕ → ℝ) (a : ℕ) (σ : ℝ) :
    f (a + 1) ≤ f a - σ ↔ f (a + 1) - m a ≤ (f a - m a) - σ := by
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **A window's length is at least its flips over the largest
per-move decrease**: if a window from `a` to `b` closes, every move's certified fixed-mask decrease
is at most `d`, and its flips sum to `F`, then `F + σ ≤ (b − a) d`. -/
theorem window_length_lower (f m : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) {σ d : ℝ}
    (hclose : f b ≤ f a - σ) (hd : ∀ k ∈ Finset.Ico a b, f k - m k ≤ d) :
    ∑ k ∈ Finset.Ico a b, (f (k + 1) - m k) + σ ≤ ((b - a : ℕ) : ℝ) * d := by
  have h := (window_closes_iff f m hab σ).mp hclose
  have hsum : ∑ k ∈ Finset.Ico a b, (f k - m k) ≤ ∑ _k ∈ Finset.Ico a b, d :=
    Finset.sum_le_sum hd
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum
  linarith

/-- [proved-derived; formal-checked] **A bounded comparison supplies the height**: if every adopted
comparison lies in `[m, B]`, every window's excursion holds with `h = B − m`, so the height is not a
free parameter once the comparison is bounded (the entry bound bounds it). -/
theorem excursion_of_bounded (f : ℕ → ℝ) (t : ℕ → ℕ) {m B : ℝ} (hm : ∀ k, m ≤ f k)
    (hB : ∀ k, f k ≤ B) (n j : ℕ) : f j ≤ f (t n) + (B - m) := by
  linarith [hm (t n), hB j]

/-- [proved-derived; formal-checked] **A decrease of one grain per window ends the chain**: with
every `σ n ≥ g > 0`, `n` closed windows need `n g ≤ f 0 − m`, so at most `(f 0 − m)/g` windows
close: the chain releases at the receiver's grain. -/
theorem grain_windows_bounded {f : ℕ → ℝ} {t : ℕ → ℕ} {W : ℕ} {h : ℝ} {σ : ℕ → ℝ}
    (g : CheckpointGuard f t W h σ) {γ : ℝ} (hγ : ∀ n, γ ≤ σ n) {m : ℝ} (hm : ∀ k, m ≤ f k)
    (n : ℕ) : (n : ℝ) * γ ≤ f 0 - m := by
  have hsum := checkpoints_sum_le g hm n
  have : ∑ _b ∈ Finset.range n, γ ≤ ∑ b ∈ Finset.range n, σ b := Finset.sum_le_sum fun b _ => hγ b
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  linarith

end ReleaseGuard

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
#print axioms telescoping_orders_differ_by_interaction
#print axioms sequential_attribution_depends_on_order
#print axioms restored_continuation_agrees
#print axioms equal_states_agree
#print axioms metric_step_zero_iff
#print axioms metric_step_descends
#print axioms diagonal_reach_iff
#print axioms vecMulVec_mulVec_eq
#print axioms posDef_reach
#print axioms native_step_horizontal
#print axioms reads_liftMatrix
#print axioms hidden_horizontal
#print axioms hidden_eq_zero_iff
#print axioms keeps_span_iff
#print axioms readingMetric_mul_transpose
#print axioms readingMetric_step
#print axioms readingMetric_reads
#print axioms readingMetric_posDef
#print axioms readingStep_normal
#print axioms readingStep_zero_iff
#print axioms readingStep_slope
#print axioms reading_diagonal_reach
#print axioms reading_posDef_reach
#print axioms reading_scale_descends
#print axioms hidden_never_native
#print axioms native_under_some_mass_iff
#print axioms deposit_makes_native
#print axioms feature_deposit_makes_native
#print axioms feature_deposit_native_needs
#print axioms deposit_raises_native_energy
#print axioms own_telescopes
#print axioms window_closes_iff
#print axioms checkpoint_one_iff
#print axioms checkpoint_descends
#print axioms excursion_le_start
#print axioms excursion_enclosure
#print axioms checkpoints_sum_le
#print axioms large_windows_card
#print axioms schedule_frequently_small
#print axioms floor_steps_diverge
#print axioms floor_large_slopes_card
#print axioms one_move_closes_iff
#print axioms window_length_lower
#print axioms excursion_of_bounded
#print axioms grain_windows_bounded

end Audit

end Holonics.HNN.ExecutedComparison
