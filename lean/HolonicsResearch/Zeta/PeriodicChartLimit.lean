import HolonicsResearch.Coupling.MeanFieldHeatClock
import Holonics.Aeon.Clock.Lock
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# A chart of one fixed period reaches no function that is not periodic, and two primes' clocks never close together

The record of November 20 on the integer failure of the Hodge relation carries a second reader's
point on the tree's heat clock (atlas `rh.periodic-chart-no-limit`,
`prime.log-clocks-incommensurate`): every finite sum of locks is `2π`-periodic on the seam at
every clock time, a limit at each point of functions of one period has that period, and the
function the zeta lane wants on the seam decays and is not zero at the origin. So the join of
`Coupling/MeanFieldHeatClock` to `Zeta/HeatFlowEntire` cannot be completed by letting the count of
locks or the clock time run with the seam's variable held fixed. The construction it asks for is a
chart whose period grows (the variable divided by a scale that runs with the count), with
convergence uniform on compact sets, which is what Hurwitz's theorem reads.

What is proved.

1. **A limit keeps the period** (`periodic_of_tendsto`): a limit at each point of functions of
   period `T` has period `T`. A function of period `T` whose values at the multiples of `T` tend to
   zero is zero at the origin (`periodic_limit_keeps_origin`), so no family of period `T` reaches a
   function that decays along those multiples and is not zero at the origin
   (`no_periodic_chart_reaches`). An operation that commutes with the shift by `T` keeps the period
   (`periodic_of_commutes_shift`): the heat flow is one.
2. **Finite sums of locks.** A finite sum of turns with integer rates is `2π`-periodic whatever its
   coefficients (`lockSum_periodic`), in particular after the modes are reweighted by a clock
   (`heated_lockSum_periodic`). The tree's heat-clock flow is such a sum on the seam
   (`mag_int`, `flow_axis_periodic`), and no sequence of flows, at any counts of locks, any clock
   times and any normalizations, reaches such a function with the seam's variable held fixed
   (`no_heat_clock_sequence_reaches`).
3. **Two primes' clocks never close together.** Powers of two distinct primes are equal only at
   exponent zero (`prime_pow_eq_prime_pow`), so `a · log p = b · log q` forces `a = b = 0`
   (`log_prime_clocks_incommensurate`), the ratio of the logarithms is irrational
   (`irrational_log_ratio`), and no aeon of a nonzero number of ticks is a cycle of the two clocks
   (`prime_clocks_never_cycle`, on `Aeon/Clock/Lock.no_cycle_of_irrational`).

Sources, `from training`: the uniqueness of a limit; unique factorization. That the function of
the zeta lane on the seam is not zero at the origin and decays is not proved here: statement 1
takes both as hypotheses on `f`. The reading (a ring that closes at a least common multiple against
a winding that never closes) is `agent-inferred` and stands in the record.

Not proved here: any convergence to the zeta lane's function, on any chart.
-/

namespace Holonics.Zeta.PeriodicChartLimit

open Filter Topology

/-! ## 1. A limit keeps the period -/

section Limit

variable {E : Type*} [TopologicalSpace E]

/-- [proved-standard; formal-checked] **A limit at each point of functions of period `T` has
period `T`.** -/
theorem periodic_of_tendsto [T2Space E] {g : ℕ → ℝ → E} {f : ℝ → E} {T : ℝ}
    (hg : ∀ n, Function.Periodic (g n) T)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))) : Function.Periodic f T := by
  intro x
  have h1 : Tendsto (fun n => g n (x + T)) atTop (𝓝 (f (x + T))) := hlim (x + T)
  have e : (fun n => g n (x + T)) = fun n => g n x := funext fun n => hg n x
  rw [e] at h1
  exact tendsto_nhds_unique h1 (hlim x)

/-- [proved-standard; formal-checked] A function of period `T` whose values at the multiples of `T`
tend to zero is zero at the origin. -/
theorem periodic_limit_keeps_origin [T2Space E] [Zero E] {f : ℝ → E} {T : ℝ}
    (hf : Function.Periodic f T)
    (hdecay : Tendsto (fun k : ℕ => f (k * T)) atTop (𝓝 0)) : f 0 = 0 := by
  have hconst : (fun k : ℕ => f (k * T)) = fun _ => f 0 := by
    funext k
    have h := (hf.nat_mul k) 0
    simpa using h
  rw [hconst] at hdecay
  exact tendsto_nhds_unique tendsto_const_nhds hdecay

/-- [counterexample; formal-checked] **No family of one period reaches a function that decays along
the multiples of that period and is not zero at the origin.** -/
theorem no_periodic_chart_reaches [T2Space E] [Zero E] {f : ℝ → E} {T : ℝ} (h0 : f 0 ≠ 0)
    (hdecay : Tendsto (fun k : ℕ => f (k * T)) atTop (𝓝 0)) (g : ℕ → ℝ → E)
    (hg : ∀ n, Function.Periodic (g n) T) :
    ¬ ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := fun hlim =>
  h0 (periodic_limit_keeps_origin (periodic_of_tendsto hg hlim) hdecay)

omit [TopologicalSpace E] in
/-- [proved-standard; formal-checked] An operation that commutes with the shift by `T` keeps the
period `T`. -/
theorem periodic_of_commutes_shift {T : ℝ} (H : (ℝ → E) → ℝ → E)
    (hH : ∀ u : ℝ → E, H (fun x => u (x + T)) = fun x => H u (x + T)) {u : ℝ → E}
    (hu : Function.Periodic u T) : Function.Periodic (H u) T := by
  intro x
  have e : (fun x => u (x + T)) = u := funext hu
  have h := congrFun (hH u) x
  rw [e] at h
  exact h.symm

end Limit

/-! ## 2. Finite sums of locks -/

/-- [proved-standard; formal-checked] **A finite sum of turns with integer rates is `2π`-periodic
whatever its coefficients.** -/
theorem lockSum_periodic (s : Finset ℤ) (c : ℤ → ℂ) :
    Function.Periodic
      (fun x : ℝ => ∑ M ∈ s, c M * Complex.exp ((M : ℂ) * (x : ℂ) * Complex.I))
      (2 * Real.pi) := by
  intro x
  show ∑ M ∈ s, c M * Complex.exp ((M : ℂ) * ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
    = ∑ M ∈ s, c M * Complex.exp ((M : ℂ) * (x : ℂ) * Complex.I)
  refine Finset.sum_congr rfl fun M _ => ?_
  have h : (M : ℂ) * ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (M : ℂ) * (x : ℂ) * Complex.I + (M : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-derived; formal-checked] The sum stays `2π`-periodic when a clock reweights its modes,
at every clock time and of either sign. -/
theorem heated_lockSum_periodic (s : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) :
    Function.Periodic
      (fun x : ℝ => ∑ M ∈ s,
        (c M * Complex.exp ((t : ℂ) * (M : ℂ) ^ 2)) * Complex.exp ((M : ℂ) * (x : ℂ) * Complex.I))
      (2 * Real.pi) :=
  lockSum_periodic s fun M => c M * Complex.exp ((t : ℂ) * (M : ℂ) ^ 2)

section HeatClock

open Holonics.Coupling.MeanFieldHeatClock Holonics.Coupling.LeeYangIsing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [proved-standard; formal-checked] The magnetization of a configuration is an integer. -/
theorem mag_int (S : Finset V) : ∃ n : ℤ, mag S = n := by
  refine ⟨∑ i, if i ∈ S then 1 else -1, ?_⟩
  rw [mag, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold spin
  split_ifs <;> simp

variable (V) in
/-- [proved-derived; formal-checked] **The heat-clock flow is `2π`-periodic on the seam at every
clock time.** -/
theorem flow_axis_periodic (t : ℝ) :
    Function.Periodic (fun θ : ℝ => flow V t (Complex.I * (θ : ℂ))) (2 * Real.pi) := by
  intro θ
  show flow V t (Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ)) = flow V t (Complex.I * (θ : ℂ))
  unfold flow
  refine Finset.sum_congr rfl fun S _ => ?_
  obtain ⟨n, hn⟩ := mag_int S
  have h : ((t * mag S ^ 2 : ℝ) : ℂ) + Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ) * (mag S : ℂ)
      = (((t * mag S ^ 2 : ℝ) : ℂ) + Complex.I * (θ : ℂ) * (mag S : ℂ))
        + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hn]
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- [counterexample; formal-checked] **No sequence of heat-clock flows reaches, with the seam's
variable held fixed, a function that decays along the multiples of `2π` and is not zero at the
origin**: whatever the counts of locks, the clock times and the normalizations. -/
theorem no_heat_clock_sequence_reaches {f : ℝ → ℂ} (h0 : f 0 ≠ 0)
    (hdecay : Tendsto (fun k : ℕ => f (k * (2 * Real.pi))) atTop (𝓝 0))
    (N : ℕ → ℕ) (t : ℕ → ℝ) (c : ℕ → ℂ) :
    ¬ ∀ θ : ℝ, Tendsto (fun n => c n * flow (Fin (N n)) (t n) (Complex.I * (θ : ℂ))) atTop
      (𝓝 (f θ)) :=
  no_periodic_chart_reaches h0 hdecay
    (fun n θ => c n * flow (Fin (N n)) (t n) (Complex.I * (θ : ℂ)))
    fun n θ => congrArg (fun z => c n * z) (flow_axis_periodic (Fin (N n)) (t n) θ)

end HeatClock

/-! ## 3. Two primes' clocks never close together -/

/-- [proved-standard; formal-checked] Powers of two distinct primes are equal only at exponent
zero. -/
theorem prime_pow_eq_prime_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ}
    (h : p ^ a = q ^ b) : a = 0 ∧ b = 0 := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [pow_zero] at h
    rcases Nat.pow_eq_one.mp h.symm with h1 | h1
    · exact absurd h1 hq.ne_one
    · exact ⟨rfl, h1⟩
  · exfalso
    have hdvd : p ∣ q ^ b := by
      rw [← h]
      exact dvd_pow_self p ha.ne'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- [proved-standard; formal-checked] **The logarithms of two distinct primes are incommensurate**:
`a · log p = b · log q` in whole numbers forces `a = b = 0`. -/
theorem log_prime_clocks_incommensurate {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (h : (a : ℝ) * Real.log p = b * Real.log q) : a = 0 ∧ b = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h1 : Real.log ((p : ℝ) ^ a) = Real.log ((q : ℝ) ^ b) := by
    rw [Real.log_pow, Real.log_pow]
    exact h
  have h2 : (p : ℝ) ^ a = (q : ℝ) ^ b :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 a)) (Set.mem_Ioi.mpr (pow_pos hq0 b)) h1
  have h3 : p ^ a = q ^ b := by exact_mod_cast h2
  exact prime_pow_eq_prime_pow hp hq hpq h3

/-- [proved-derived; formal-checked] The ratio of the logarithms of two distinct primes is
irrational. -/
theorem irrational_log_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  rintro ⟨r, hr⟩
  have hrpos : (0 : ℝ) < r := by
    rw [hr]
    exact div_pos hlp hlq
  have hrq : (0 : ℚ) < r := by exact_mod_cast hrpos
  have hnum : 0 < r.num := Rat.num_pos.mpr hrq
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hnat : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hlog : Real.log p = (r : ℝ) * Real.log q := by
    rw [hr]
    field_simp
  have key : (r.den : ℝ) * Real.log p = (r.num.toNat : ℝ) * Real.log q := by
    rw [hnat, hlog, Rat.cast_def]
    field_simp
  exact absurd (log_prime_clocks_incommensurate hp hq hpq key).1 r.den_pos.ne'

open Holonics.Aeon.Clock.Lock in
/-- [proved-derived; formal-checked] **No aeon of a nonzero number of ticks is a cycle of two
distinct primes' clocks.** -/
theorem prime_clocks_never_cycle {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℤ}
    (hk : k ≠ 0) : ¬ IsCycle (jointReading (Real.log p / Real.log q) k) :=
  no_cycle_of_irrational (irrational_log_ratio hp hq hpq) hk

end Holonics.Zeta.PeriodicChartLimit
