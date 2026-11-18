import Holonics.Aeon.Production.Kac
import Mathlib

/-!
# Recurrence is the first-return ledger of a kept measure, with a deadline

Source: aeon record A4 and `Aeon/Production/Kac` (the finite Markov ledger), and the box of #410 that asks for
Mathlib's Poincaré recurrence joined to that owner and to the near-return owners
(`Aeon/Clock/Lock`, `HolonicsResearch/Aeon/Clock/NearReturn`), so that approximate recurrence is a theorem of the
objects.

A motion `T` keeps a measure `μ` (`MeasurePreserving T μ μ`); a **section** `A` is a measurable set, a coarser
receiver whose ticks are the returns of the motion to `A`. `surv T A n` is the set of states that have not crossed the
section at the fine epochs `1, …, n`, the set form of `Kac.survival`.

[proved-derived; formal-checked] What is proved.

1. **The ledger at every truncation** (`ledger`): `Σ_(n<N) μ(A ∩ surv n) + μ(surv N) = μ(X)`. Only the keeping of the
   measure is used, as only stationarity is in `Kac.kac_ledger`; the measure may be infinite. It is the telescoping of
   one step, `μ(surv (n+1)) + μ(A ∩ surv n) = μ(surv n)` (`measure_surv_succ`).
2. **Recurrence with a deadline** (`rate`, `measure_not_returned_le`): the part of the section that has not returned by
   the fine epoch `n` has measure at most `μ(X)/(n + 1)`. So where `μ(X) < (n + 1) μ(A)` some state of `A` is back in
   `A` within `n` epochs (`exists_return_le`), with no ergodicity and no topology.
3. **Poincaré recurrence** from the ledger alone (`measure_never_return`, `ae_returns`): in a finite measure almost
   every state of `A` returns. Mathlib's form, infinitely many returns, is `ae_returns_frequently`
   (`MeasurePreserving.conservative`).
4. **Kac's lemma for a kept measure** (`kac`, `kac_entering`): the first-return time is the tail sum
   `returnTime = Σ_n 1[surv n]` (`returnTime_eq_of_first`, `returnTime_eq_top`), its integral over the section is
   `Σ_n μ(A ∩ surv n)` (`lintegral_returnTime`), and `∫_A τ_A dμ + μ(never entering) = μ(X)`: the mean first return
   from the section, weighed by the section, is the measure of the states that ever enter it. For an ergodic motion
   and a section of nonzero measure it is `μ(X)` (`kac_ergodic`): fine epochs per coarse epoch are the undivided pair
   `(μ(X) : μ(A))`, atlas `aeon.kac-grain-ratio` with no finiteness of the state space.
5. **The finite Markov owner is the same ledger** (`avoid_detKernel`, `survival_detKernel`,
   `stationary_detKernel_iff`, `kac_ledger_deterministic`): a map `σ` of a finite set is the chain
   `P x y = [σ x = y]`, `Kac.survival` of that chain is the indicator of `surv σ A n`, a weight is stationary exactly
   when each state's weight is the sum over its preimages, and `Kac.kac_ledger` reads
   `Σ_(y∈A) π_y #{n < N : y ∈ surv n} = Σ π − Σ_(y ∈ surv N) π_y`.
6. **Near-return of a clock is recurrence with its deadline** (`near_return_of_lt`, `dirichlet`, `dirichlet_real`,
   `rotation_recurrent`): the rotation by `a` of the circle keeps length, and the ledger's deadline on a closed arc of
   length `ε` gives `‖k a‖ ≤ ε` for some `1 ≤ k ≤ n` as soon as `(n + 1) ε > 1`. Taking the least of the finitely many
   candidates gives Dirichlet's bound `‖k a‖ ≤ 1/(N + 1)` with `1 ≤ k ≤ N`, and every state of the circle returns
   within any `ε` of itself. The convergents of `NearReturn` are the ticks that realize these returns
   (`near_return_le_all` there bounds the miss at each); here the return is a statement of the kept measure.

Limits. The deadline is the pigeonhole of the ledger; it is not the convergents' bound `1/q_(n+1)` and does not say
which `k` returns. Kac's lemma is stated with the extended integral and the tail-sum time; the induced map on the
section and Abramov's formula for a general ergodic motion stay with `Kac`'s closing paragraph. The rotation is on
the circle of circumference one; a torus of several clocks has the same ledger with the product of arcs and is not
stated. No rate of mixing is claimed.

Computational object: the helical pair interaction read at a section, on the winding guide's helix (a clock's
return to a face) and tube (the span between two crossings of a section); pair, placement, cell holonomy and tower
thread are not touched.

Consumers: `Aeon/Production/Kac` (its ledger and series are the finite Markov case), the near-return owners, and
atlas `aeon.kac-ledger`, `aeon.kac-observable`, `aeon.kac-grain-ratio`, `aeon.two-clocks-lock`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.Recurrence

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

variable {X : Type*}

/-! ## 1. The survival sets -/

/-- [definition] `surv T A n`: the states that have not crossed the section `A` at the fine epochs `1, …, n`. -/
def surv (T : X → X) (A : Set X) : ℕ → Set X
  | 0 => univ
  | n + 1 => T ⁻¹' (Aᶜ ∩ surv T A n)

/-- [definition] Before the first epoch every state survives. -/
theorem surv_zero (T : X → X) (A : Set X) : surv T A 0 = univ := rfl

/-- [definition] One more epoch: the next state is off the section and survives the rest. -/
theorem surv_succ (T : X → X) (A : Set X) (n : ℕ) : surv T A (n + 1) = T ⁻¹' (Aᶜ ∩ surv T A n) := rfl

/-- [proved-derived] Membership: no iterate from the first to the `n`-th is in the section. -/
theorem mem_surv_iff {T : X → X} {A : Set X} {n : ℕ} {x : X} :
    x ∈ surv T A n ↔ ∀ k, 1 ≤ k → k ≤ n → T^[k] x ∉ A := by
  induction n generalizing x with
  | zero =>
    simp only [surv_zero, mem_univ, true_iff]
    intro k hk1 hk0
    omega
  | succ n ih =>
    rw [surv_succ, mem_preimage, mem_inter_iff, mem_compl_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk1 hk2
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using h1
      · exact h2 j hj (by omega)
    · intro h
      refine ⟨by simpa using h 1 le_rfl (by omega), fun k hk1 hk2 => ?_⟩
      have := h (k + 1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this

/-- [proved-derived] A state that survives one more epoch survived the epochs before. -/
theorem surv_succ_subset (T : X → X) (A : Set X) (n : ℕ) : surv T A (n + 1) ⊆ surv T A n := by
  intro x hx
  rw [mem_surv_iff] at hx ⊢
  exact fun k hk1 hk2 => hx k hk1 (by omega)

/-- [proved-derived] The survival sets decrease. -/
theorem surv_antitone (T : X → X) (A : Set X) : Antitone (surv T A) :=
  antitone_nat_of_succ_le (surv_succ_subset T A)

/-- [proved-derived] The states that never enter the section. -/
theorem iInter_surv (T : X → X) (A : Set X) : ⋂ n, surv T A n = {x | ∀ k, 1 ≤ k → T^[k] x ∉ A} := by
  ext x
  simp only [mem_iInter, mem_surv_iff, mem_ofPred_eq]
  exact ⟨fun h k hk => h k k hk le_rfl, fun h _ k hk _ => h k hk⟩

variable [MeasurableSpace X] {μ : Measure X} {T : X → X} {A : Set X}

/-- [proved-derived] The survival sets of a measurable motion and a measurable section are measurable. -/
theorem measurableSet_surv (hT : Measurable T) (hA : MeasurableSet A) (n : ℕ) : MeasurableSet (surv T A n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact hT (hA.compl.inter ih)

/-! ## 2. The ledger and its deadline -/

/-- [proved-derived] **One step of the ledger**: the survivors of `n` epochs are those that survive one more and
those of the section. -/
theorem measure_surv_succ (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) (n : ℕ) :
    μ (surv T A (n + 1)) + μ (A ∩ surv T A n) = μ (surv T A n) := by
  have hS := measurableSet_surv hT.measurable hA n
  rw [surv_succ, hT.measure_preimage (hA.compl.inter hS).nullMeasurableSet]
  have h := measure_inter_add_sdiff (μ := μ) (surv T A n) hA
  rw [show Aᶜ ∩ surv T A n = surv T A n \ A by rw [sdiff_eq, inter_comm], inter_comm A, add_comm]
  exact h

/-- [proved-derived] **The ledger at every truncation**: the mass of the section that has not returned, summed over
the first `N` epochs, with the mass still avoiding the section, is the whole. Only the keeping of the measure is
used. -/
theorem ledger (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) (N : ℕ) :
    ∑ n ∈ Finset.range N, μ (A ∩ surv T A n) + μ (surv T A N) = μ univ := by
  induction N with
  | zero => simp [surv_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, add_comm (μ (A ∩ surv T A N)), measure_surv_succ hT hA N, ih]

/-- [proved-derived] **Recurrence with a deadline**: `(n + 1)` times the mass of the section not yet returned at
epoch `n` is at most the whole. -/
theorem rate (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) * μ (A ∩ surv T A n) ≤ μ univ := by
  have h := ledger hT hA (n + 1)
  have hle : ∑ _k ∈ Finset.range (n + 1), μ (A ∩ surv T A n) ≤ ∑ k ∈ Finset.range (n + 1), μ (A ∩ surv T A k) := by
    refine Finset.sum_le_sum fun k hk => ?_
    exact measure_mono (inter_subset_inter_right A
      (surv_antitone T A (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
  calc ((n : ℝ≥0∞) + 1) * μ (A ∩ surv T A n)
      = ∑ _k ∈ Finset.range (n + 1), μ (A ∩ surv T A n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ (A ∩ surv T A k) := hle
    _ ≤ μ univ := by
        rw [← h]
        exact le_self_add

/-- [proved-derived] The mass of the section that has not returned by epoch `n` is at most `μ(X)/(n + 1)`. -/
theorem measure_not_returned_le (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) (n : ℕ) :
    μ (A ∩ surv T A n) ≤ μ univ / ((n : ℝ≥0∞) + 1) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), mul_comm]
  exact rate hT hA n

/-- [proved-derived] **A return inside the deadline**: where the whole is less than `(n + 1)` sections, some state
of the section is back in it within `n` epochs. -/
theorem exists_return_le (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) {n : ℕ}
    (h : μ univ < ((n : ℝ≥0∞) + 1) * μ A) : ∃ x ∈ A, ∃ k, 1 ≤ k ∧ k ≤ n ∧ T^[k] x ∈ A := by
  by_contra hno
  push Not at hno
  have hsub : A ⊆ surv T A n := fun x hx => mem_surv_iff.mpr fun k hk1 hk2 => hno x hx k hk1 hk2
  have hr := rate hT hA n
  rw [inter_eq_left.mpr hsub] at hr
  exact absurd hr (not_le.mpr h)

/-! ## 3. Poincaré recurrence -/

/-- [proved-standard] **Poincaré recurrence from the ledger**: in a finite measure the states of the section that
never return have measure zero. -/
theorem measure_never_return [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) :
    μ (A ∩ ⋂ n, surv T A n) = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne (measure_ne_top μ univ)
  have h1 : (n : ℝ≥0∞) * μ (A ∩ ⋂ m, surv T A m) ≤ ((n : ℝ≥0∞) + 1) * μ (A ∩ surv T A n) :=
    mul_le_mul' le_self_add (measure_mono (inter_subset_inter_right A (iInter_subset _ n)))
  exact absurd (h1.trans (rate hT hA n)) (not_le.mpr hn)

/-- [proved-standard] Almost every state of the section returns to it. -/
theorem ae_returns [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ k, 1 ≤ k ∧ T^[k] x ∈ A := by
  have h0 := measure_never_return hT hA
  rw [ae_iff]
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [mem_ofPred_eq, Classical.not_imp, not_exists, not_and] at hx
  exact ⟨hx.1, mem_iInter.mpr fun n => mem_surv_iff.mpr fun k hk _ => hx.2 k hk⟩

/-- [proved-standard] Mathlib's form: almost every state of the section returns infinitely often. -/
theorem ae_returns_frequently [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ n in atTop, T^[n] x ∈ A :=
  hT.conservative.ae_mem_imp_frequently_image_mem hA.nullMeasurableSet

/-! ## 4. Kac's lemma for a kept measure -/

/-- [definition] **The first-return time as a tail sum**: `τ_A(x) = Σ_n 1[x ∈ surv n]`, with value `∞` on a state
that never enters. -/
def returnTime (T : X → X) (A : Set X) (x : X) : ℝ≥0∞ := ∑' n, (surv T A n).indicator 1 x

omit [MeasurableSpace X] in
/-- [proved-derived] The tail sum is the first-return time. -/
theorem returnTime_eq_of_first {x : X} {k : ℕ} (hk : 1 ≤ k) (hlt : ∀ j, 1 ≤ j → j < k → T^[j] x ∉ A)
    (hk' : T^[k] x ∈ A) : returnTime T A x = k := by
  have hmem : ∀ n, x ∈ surv T A n ↔ n < k := by
    intro n
    rw [mem_surv_iff]
    constructor
    · intro h
      by_contra hn
      exact h k hk (not_lt.mp hn) hk'
    · intro hn j hj1 hj2
      exact hlt j hj1 (lt_of_le_of_lt hj2 hn)
  unfold returnTime
  rw [tsum_eq_sum (s := Finset.range k)]
  · rw [Finset.sum_congr rfl fun n hn => indicator_of_mem ((hmem n).mpr (Finset.mem_range.mp hn)) _]
    simp
  · intro n hn
    exact indicator_of_notMem (fun h => hn (Finset.mem_range.mpr ((hmem n).mp h))) _

omit [MeasurableSpace X] in
/-- [proved-derived] A state that never enters the section has no finite return time. -/
theorem returnTime_eq_top {x : X} (h : ∀ k, 1 ≤ k → T^[k] x ∉ A) : returnTime T A x = ∞ := by
  have h1 : ∀ n, (surv T A n).indicator (1 : X → ℝ≥0∞) x = 1 := fun n =>
    indicator_of_mem (mem_surv_iff.mpr fun k hk _ => h k hk) _
  simp only [returnTime, h1]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- [proved-derived] The integral of the return time over the section is the tail sum of the ledger. -/
theorem lintegral_returnTime (hT : Measurable T) (hA : MeasurableSet A) :
    ∫⁻ x in A, returnTime T A x ∂μ = ∑' n, μ (A ∩ surv T A n) := by
  unfold returnTime
  rw [lintegral_tsum fun n => (measurable_one.indicator (measurableSet_surv hT hA n)).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_indicator (measurableSet_surv hT hA n)]
  simp only [Pi.one_apply, setLIntegral_one]
  rw [Measure.restrict_apply (measurableSet_surv hT hA n), inter_comm]

/-- [proved-standard] **Kac's lemma for a kept measure**: the return time integrated over the section, with the mass
that never enters, is the whole. -/
theorem kac [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) :
    ∫⁻ x in A, returnTime T A x ∂μ + μ (⋂ n, surv T A n) = μ univ := by
  rw [lintegral_returnTime hT.measurable hA]
  have h1 : Tendsto (fun N => ∑ n ∈ Finset.range N, μ (A ∩ surv T A n)) atTop
      (𝓝 (∑' n, μ (A ∩ surv T A n))) := ENNReal.tendsto_nat_tsum _
  have h2 : Tendsto (fun N => μ (surv T A N)) atTop (𝓝 (μ (⋂ n, surv T A n))) :=
    tendsto_measure_iInter_atTop (fun n => (measurableSet_surv hT.measurable hA n).nullMeasurableSet)
      (surv_antitone T A) ⟨0, measure_ne_top μ _⟩
  have h3 := h1.add h2
  simp only [ledger hT hA] at h3
  exact tendsto_nhds_unique tendsto_const_nhds h3 |>.symm

/-- [proved-standard] The mean first return, weighed by the section, is the measure of the states that ever enter
it. -/
theorem kac_entering [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A) :
    ∫⁻ x in A, returnTime T A x ∂μ = μ {x | ∃ k, 1 ≤ k ∧ T^[k] x ∈ A} := by
  have hk := kac hT hA
  have hS : MeasurableSet (⋂ n, surv T A n) := MeasurableSet.iInter fun n => measurableSet_surv hT.measurable hA n
  have hc := measure_add_measure_compl (μ := μ) hS
  have hset : (⋂ n, surv T A n)ᶜ = {x | ∃ k, 1 ≤ k ∧ T^[k] x ∈ A} := by
    rw [iInter_surv]
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_not, exists_prop]
  rw [← hset]
  have : ∫⁻ x in A, returnTime T A x ∂μ + μ (⋂ n, surv T A n) = μ (⋂ n, surv T A n)ᶜ + μ (⋂ n, surv T A n) := by
    rw [hk, add_comm, hc]
  exact (ENNReal.add_left_inj (measure_ne_top μ _)).mp this

/-- [proved-standard] **Kac's lemma for an ergodic motion**: over a section of nonzero measure the return time
integrates to the whole, so fine epochs per coarse epoch are the pair `(μ(X) : μ(A))`. -/
theorem kac_ergodic [IsFiniteMeasure μ] (hT : Ergodic T μ) (hA : MeasurableSet A) (h0 : μ A ≠ 0) :
    ∫⁻ x in A, returnTime T A x ∂μ = μ univ := by
  have hk := kac hT.toMeasurePreserving hA
  suffices h : μ (⋂ n, surv T A n) = 0 by rwa [h, add_zero] at hk
  have hEm : MeasurableSet (⋂ n, surv T A n)ᶜ :=
    (MeasurableSet.iInter fun n => measurableSet_surv hT.measurable hA n).compl
  have hsub : T ⁻¹' (⋂ n, surv T A n)ᶜ ⊆ (⋂ n, surv T A n)ᶜ := by
    intro x hx
    simp only [mem_preimage, mem_compl_iff, mem_iInter, not_forall] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨n + 1, fun h => hn ?_⟩
    rw [surv_succ] at h
    exact h.2
  rcases hT.ae_empty_or_univ_of_preimage_ae_le hEm.nullMeasurableSet (LE.le.eventuallyLE hsub)
    with h | h
  · exfalso
    have hAE : T ⁻¹' A ⊆ (⋂ n, surv T A n)ᶜ := by
      intro x hx
      simp only [mem_compl_iff, mem_iInter, not_forall]
      refine ⟨1, fun h => ?_⟩
      exact mem_surv_iff.mp h 1 le_rfl le_rfl (by simpa using hx)
    have hE0 : μ (⋂ n, surv T A n)ᶜ = 0 := by rw [measure_congr h, measure_empty]
    exact h0 (by
      rw [← hT.toMeasurePreserving.measure_preimage hA.nullMeasurableSet]
      exact measure_mono_null hAE hE0)
  · have := ae_eq_univ.mp h
    rwa [compl_compl] at this

end Holonics.Aeon.Production.Recurrence

/-! ## 5. The finite Markov owner is the same ledger -/

namespace Holonics.Aeon.Production.Recurrence

open Set Function
open Holonics.Aeon.Production

section Deterministic

variable {S : Type*} [Fintype S] [DecidableEq S] {R : Type*} [CommRing R]

/-- [definition] The chain of a map: one step from `x` lands on `σ x`. -/
def detKernel (σ : S → S) : S → S → R := fun x y => if σ x = y then 1 else 0

/-- [proved-derived] One fine epoch of the chain of a map that has not crossed the section. -/
theorem avoid_detKernel (σ : S → S) (A : Finset S) (g : S → R) (y : S) :
    Kac.avoid (detKernel σ) A g y = if σ y ∈ A then 0 else g (σ y) := by
  unfold Kac.avoid detKernel
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  by_cases h : σ y ∈ A <;> simp [h]

open Classical in
/-- [proved-derived] **The Markov survival of a map's chain is the indicator of the survival set.** -/
theorem survival_detKernel (σ : S → S) (A : Finset S) (n : ℕ) (y : S) :
    Kac.survival (detKernel σ) A n y = if y ∈ surv σ (A : Set S) n then (1 : R) else 0 := by
  induction n generalizing y with
  | zero => simp [Kac.survival, surv_zero]
  | succ n ih =>
    have hstep : Kac.survival (detKernel (R := R) σ) A (n + 1) y
        = Kac.avoid (detKernel σ) A (Kac.survival (detKernel σ) A n) y := by
      unfold Kac.survival
      rw [Function.iterate_succ_apply']
    rw [hstep, avoid_detKernel, ih, surv_succ]
    by_cases h1 : σ y ∈ A <;> by_cases h2 : σ y ∈ surv σ (A : Set S) n <;> simp [h1, h2]

/-- [proved-derived] A weight is stationary for a map's chain exactly when each state's weight is the sum over its
preimages. -/
theorem stationary_detKernel_iff (σ : S → S) (π : S → R) :
    Kac.Stationary (detKernel σ) π ↔ ∀ y, ∑ x ∈ Finset.univ.filter (fun x => σ x = y), π x = π y := by
  unfold Kac.Stationary detKernel
  refine forall_congr' fun y => ?_
  rw [Finset.sum_filter]
  simp only [mul_ite, mul_one, mul_zero]

open Classical in
/-- [proved-derived] **Kac's ledger of a map**: for a stationary weight, the section's weight counted once for each
epoch it has not returned by `N`, is the whole less the weight still avoiding the section. -/
theorem kac_ledger_deterministic {σ : S → S} {π : S → R} (hπ : Kac.Stationary (detKernel σ) π) (A : Finset S)
    (N : ℕ) :
    ∑ y ∈ A, π y * ∑ n ∈ Finset.range N, (if y ∈ surv σ (A : Set S) n then (1 : R) else 0)
      = ∑ y, π y - ∑ y, π y * (if y ∈ surv σ (A : Set S) N then (1 : R) else 0) := by
  have h := Kac.kac_ledger hπ A N
  simp only [Kac.truncatedReturn, survival_detKernel] at h
  exact h

end Deterministic

/-! ## 6. Near-return of a clock is recurrence with its deadline -/

section Rotation

open MeasureTheory
open scoped ENNReal

/-- [proved-derived] The iterates of a rotation of the circle. -/
theorem rotation_iterate (a x : AddCircle (1 : ℝ)) (k : ℕ) : (a + ·)^[k] x = k • a + x := by
  rw [add_left_iterate]

/-- [proved-derived] **A clock's near-return inside the deadline**: where `(n + 1) ε > 1`, some `1 ≤ k ≤ n` has
`‖k a‖ ≤ ε`, by the ledger of the rotation on a closed arc of length `ε`. -/
theorem near_return_of_lt (a : AddCircle (1 : ℝ)) {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : 1 < ((n : ℝ) + 1) * ε) : ∃ k, 1 ≤ k ∧ k ≤ n ∧ ‖k • a‖ ≤ ε := by
  have hT : MeasurePreserving (a + ·) (volume : Measure (AddCircle (1 : ℝ))) volume :=
    measurePreserving_add_left volume a
  have hA : MeasurableSet (Metric.closedBall (0 : AddCircle (1 : ℝ)) (ε / 2)) := measurableSet_closedBall
  have hvol : volume (Metric.closedBall (0 : AddCircle (1 : ℝ)) (ε / 2)) = ENNReal.ofReal ε := by
    rw [AddCircle.volume_closedBall, show 2 * (ε / 2) = ε by ring, min_eq_right hε1]
  have hcast : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hlt : volume (univ : Set (AddCircle (1 : ℝ)))
      < ((n : ℝ≥0∞) + 1) * volume (Metric.closedBall (0 : AddCircle (1 : ℝ)) (ε / 2)) := by
    rw [hvol, AddCircle.measure_univ, hcast, ← ENNReal.ofReal_mul (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h
  obtain ⟨x, hx, k, hk1, hkn, hk⟩ := exists_return_le hT hA hlt
  refine ⟨k, hk1, hkn, ?_⟩
  rw [rotation_iterate] at hk
  rw [mem_closedBall_zero_iff] at hx hk
  calc ‖k • a‖ = ‖(k • a + x) - x‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖k • a + x‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hk hx
    _ = ε := by ring

/-- [proved-standard] **Dirichlet's bound from the ledger**: for `N ≥ 1` some `1 ≤ k ≤ N` has
`‖k a‖ ≤ 1/(N + 1)`. -/
theorem dirichlet (a : AddCircle (1 : ℝ)) {N : ℕ} (hN : 1 ≤ N) :
    ∃ k, 1 ≤ k ∧ k ≤ N ∧ ‖k • a‖ ≤ 1 / ((N : ℝ) + 1) := by
  by_contra hno
  push Not at hno
  have hne : (Finset.Icc 1 N).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩
  obtain ⟨k₀, hk₀, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 N) (fun k : ℕ => ‖k • a‖) hne
  have hk₀' := Finset.mem_Icc.mp hk₀
  have hgt := hno k₀ hk₀'.1 hk₀'.2
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : 1 / ((N : ℝ) + 1) < min ‖k₀ • a‖ 1 :=
    lt_min hgt (by rw [div_lt_one hN0]; linarith)
  obtain ⟨ε, hεlo, hεhi⟩ := exists_between h1
  have hεpos : 0 < ε := lt_trans (by positivity) hεlo
  have hdead : 1 < ((N : ℝ) + 1) * ε := by
    have := mul_lt_mul_of_pos_left hεlo hN0
    rwa [mul_one_div_cancel hN0.ne'] at this
  obtain ⟨k, hk1, hkN, hk⟩ :=
    near_return_of_lt a hεpos (le_of_lt (lt_of_lt_of_le hεhi (min_le_right _ _))) hdead
  have hm := hmin k (Finset.mem_Icc.mpr ⟨hk1, hkN⟩)
  have hl := min_le_left ‖k₀ • a‖ 1
  linarith

/-- [proved-standard] Dirichlet's bound for a real clock ratio: some `1 ≤ k ≤ N` and an integer `j` have
`|k α − j| ≤ 1/(N + 1)`. -/
theorem dirichlet_real (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ ∃ j : ℤ, |(k : ℝ) * α - j| ≤ 1 / ((N : ℝ) + 1) := by
  obtain ⟨k, hk1, hkN, hk⟩ := dirichlet (α : AddCircle (1 : ℝ)) hN
  refine ⟨k, hk1, hkN, round ((k : ℝ) * α), ?_⟩
  rw [← AddCircle.coe_nsmul, AddCircle.norm_eq] at hk
  simpa [nsmul_eq_mul] using hk

/-- [proved-derived] **Every state of a clock returns within any `ε`**: the rotation is recurrent at every point,
not only almost every one, because it commutes with itself. -/
theorem rotation_recurrent (a x : AddCircle (1 : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, 1 ≤ k ∧ dist ((a + ·)^[k] x) x ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hk1, -, hk⟩ := dirichlet a (N := n + 1) (by omega)
  refine ⟨k, hk1, ?_⟩
  rw [rotation_iterate, dist_eq_norm, add_sub_cancel_right]
  have h2 : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  linarith

end Rotation

end Holonics.Aeon.Production.Recurrence
