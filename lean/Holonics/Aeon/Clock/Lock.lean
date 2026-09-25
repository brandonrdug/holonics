import Holonics.Aeon.Clock.Winding
import Holonics.Geometry.PairResonance
import Holonics.Transport.HelicalPairInteraction
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

/-!
# Two clocks: the Farey lock and the convergent near-returns

[definition] The aeon record, "two clocks and their crossing axes", and `docs/ELEMENTARY_OBJECTS.md`
§12. Two clocks share one joint motion; the first advances `α` turns per turn of the second. The
aeon of `k` ticks of the second reads `(k α, k)` (`jointReading`), and it is a **cycle** when both
open phases vanish (`IsCycle`, over `Winding.openPhase`).

[proved-derived; formal-checked] What is proved.

1. **The lock at the Farey address.** For `α = p / q` every aeon of `q` ticks (and of every
   multiple) is a cycle reading `(p, q)` whole windings, and the rate pair `(q, p)` is the pair
   contact's no-slip direction of the two clocks read as a pair on one axis
   (`v_a = α·v`, `v_b = v`): `q · v_a = p · v_b`, so on every definite dissipative face it reads
   zero power (`lock_at_address`, through `Transport/HelicalPairInteraction.lock_iff_zero_power`);
   with `p, q` coprime an aeon is a cycle exactly when `q` divides its tick count
   (`cycle_iff_period_dvd`). A joint cycle is read alike in the rational and the real chart of the
   rate (`isCycle_ratCast_iff`), so the lock at `p / q` is a cycle of the real joint clock
   (`isCycle_of_rational`). For irrational `α` no aeon of nonzero ticks is a cycle
   (`no_cycle_of_irrational`). When the aeon of `T` ticks is a cycle of `c` whole windings, an
   address `p / q` is compared with the rate by cross-multiplication against the cycle, without a
   division (`div_lt_rate_iff`, `rate_lt_div_iff`).
1b. **A cycle of two clocks is a closed loop of their torus.** On the lift `clockLift ι` of the
   clock torus with periods `d`, an aeon's readings in turns have zero open phase exactly when it
   closes on the torus (`openPhases_zero_iff_torus_closes`); for two clocks this is
   `IsCycle (turnReading d γ) ↔ torusPoint d x = torusPoint d y` (`isCycle_iff_torus_closes`), and
   the joint reading `(k α, k)` of the lock is the turn reading of the lift aeon whose second clock
   completes `k` periods (`turnReading_eq_jointReading`). The groupoid's aeon is the one aeon the
   lock reads.
2. **The convergents.** For `GenContFract.of α` the convergent addresses `(p_n, q_n)` are integers
   (`nums_integral`, `dens_integral`) with `q_n ≥ 1` (`one_le_dens`). For irrational `α`:
   - the exact near-return bound `|q_n α − p_n| ≤ 1/q_(n+1)` (`convergent_near_return`, from
     Mathlib's `GenContFract.abs_sub_convs_le`), strictly below `1/q_n` for `n ≥ 1`
     (`convergent_near_return_lt`, since `q_n < q_(n+1)`: `dens_lt_dens_succ`);
   - closure at no grain: `q_n α − p_n ≠ 0` (`convergent_never_closes`);
   - consecutive convergents are Farey neighbours, `p_n q_(n+1) − q_n p_(n+1) = (−1)^(n+1)`
     (`convergents_are_farey_neighbours`, Mathlib's determinant formula), so by the
     `Geometry/PairResonance` owner every lock address strictly between them costs at least the
     mediant's period `q_n + q_(n+1)` (`between_consecutive_convergents_costs_the_mediant`).
3. **The best near-returns are convergents.** A near-return `|q α − p| < 1/(2q)` in lowest terms is
   a convergent (`good_near_return_is_convergent`, Legendre, Mathlib); a near-return within
   `1/(N+1)` exists at every grain `N` (`near_return_at_every_grain`, Dirichlet, Mathlib); and for
   irrational `α` there are infinitely many near-returns `|q α − p| < 1/q`
   (`infinitely_many_near_returns`).
4. **A rational ratio locks at a convergent.** For rational `α` the continued fraction terminates
   and some convergent closes exactly, so its aeon of `q_n` ticks is a cycle
   (`rational_ratio_locks_at_a_convergent`).

[open] The strict form `|q_n α − p_n| < 1/q_(n+1)` and the three-distance theorem are not proved
here; Mathlib states the non-strict bound. The Farey address theory beyond neighbours and mediants
lives in `HolonicsResearch/Geometry/Farey`, which this foundation module does not import.

No `axiom`, no `sorry`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.Lock

open Holonics.Aeon.Clock.Winding
open GenContFract

/-! ## 1. Two clocks and the cycles of their joint motion -/

section Joint

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- [definition] The readings of two clocks over the aeon of `k` ticks of the second clock, when
the first advances `α` turns per turn of the second. -/
def jointReading (α : R) (k : ℤ) : R × R := ((k : R) * α, (k : R))

/-- [definition] A joint reading is a **cycle** when both clocks return to their phase. -/
def IsCycle (t : R × R) : Prop := openPhase t.1 = 0 ∧ openPhase t.2 = 0

/-- [proved-derived; formal-checked] The aeon of `k` ticks is a cycle exactly when the first clock
completes a whole number of turns. -/
theorem jointReading_isCycle_iff (α : R) (k : ℤ) :
    IsCycle (jointReading α k) ↔ ∃ m : ℤ, (k : R) * α = m := by
  constructor
  · rintro ⟨h1, -⟩
    exact (openPhase_eq_zero_iff _).mp h1
  · intro h
    exact ⟨(openPhase_eq_zero_iff _).mpr h, (openPhase_eq_zero_iff _).mpr ⟨k, rfl⟩⟩

end Joint

/-! ### A cycle of two clocks is a closed loop of their torus -/

section Torus

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading

/-- [proved-derived; formal-checked] A micro-step reading of a `d`-step ring has zero open phase
exactly when `d` divides it (the ratio's division with remainder, `Winding.ratio_split`). -/
theorem openPhase_turns_eq_zero_iff {d : ℕ} (hd : 0 < d) (m : ℤ) :
    openPhase (turns d m) = 0 ↔ (d : ℤ) ∣ m := by
  obtain ⟨-, hrem, -, -, -⟩ := ratio_split m d hd
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [turns, Int.dvd_iff_emod_eq_zero]
  constructor
  · intro h
    rw [h, mul_zero] at hrem
    exact_mod_cast hrem.symm
  · intro h
    rw [h] at hrem
    push_cast at hrem
    exact (mul_eq_zero.mp hrem).resolve_left hdq

variable {ι : Type*} [DecidableEq ι]

/-- [proved-derived; formal-checked] **Every navigator's reading in turns has zero open phase
exactly when the aeon closes on the clock torus** (`Winding.torus_closes_iff`). -/
theorem openPhases_zero_iff_torus_closes (d : ι → ℕ) (hd : ∀ i, 0 < d i) {x y : ι → ℤ}
    (γ : Aeon (clockLift ι) x y) :
    (∀ i, openPhase (turns (d i) (reading (navigatorClock i) γ)) = 0) ↔
      torusPoint d x = torusPoint d y := by
  rw [torus_closes_iff]
  exact forall_congr' fun i => openPhase_turns_eq_zero_iff (hd i) _

/-- [definition] The readings in turns of an aeon of the two-clock torus. -/
def turnReading (d : Fin 2 → ℕ) {x y : Fin 2 → ℤ} (γ : Aeon (clockLift (Fin 2)) x y) : ℚ × ℚ :=
  (turns (d 0) (reading (navigatorClock 0) γ), turns (d 1) (reading (navigatorClock 1) γ))

/-- [proved-derived; formal-checked] **A two-clock cycle is a closed loop of the clock torus.** -/
theorem isCycle_iff_torus_closes (d : Fin 2 → ℕ) (hd : ∀ i, 0 < d i) {x y : Fin 2 → ℤ}
    (γ : Aeon (clockLift (Fin 2)) x y) :
    IsCycle (turnReading d γ) ↔ torusPoint d x = torusPoint d y := by
  rw [← openPhases_zero_iff_torus_closes d hd γ, IsCycle, turnReading, Fin.forall_fin_two]

/-- [proved-derived; formal-checked] **The lock's joint reading is the turn reading of a lift
aeon.** When the second clock completes `k` periods along the aeon and the first advances `k α`
turns, the aeon's turn reading is `jointReading α k`. -/
theorem turnReading_eq_jointReading (d : Fin 2 → ℕ) (hd : ∀ i, 0 < d i) {x y : Fin 2 → ℤ}
    (γ : Aeon (clockLift (Fin 2)) x y) (α : ℚ) (k : ℤ)
    (h₁ : reading (navigatorClock 1) γ = k * d 1) (h₀ : turns (d 0) (reading (navigatorClock 0) γ) = k * α) :
    turnReading d γ = jointReading α k := by
  have hd1 : (d 1 : ℚ) ≠ 0 := by exact_mod_cast (hd 1).ne'
  refine Prod.ext h₀ ?_
  simp only [turnReading, jointReading, turns, h₁]
  push_cast
  field_simp

end Torus

open Matrix Holonics.Geometry.ScrewGeometry Holonics.Transport.HolonicInteraction
  Holonics.Transport.HelicalPairInteraction in
/-- [proved-derived; formal-checked] **Two clocks lock at their Farey address.** When the first
clock advances `p / q` turns per turn of the second, every aeon of `q · m` ticks reads `(p m, q m)`
whole windings and is a cycle. Read as a pair contact on one axis `v` (`v_a = (p/q)·v`, `v_b = v`),
the rate pair `(q, p)` is the no-slip direction `q · v_a = p · v_b`, and on every definite
dissipative face of positive weight it reads zero power
(`Transport/HelicalPairInteraction.lock_iff_zero_power`). -/
theorem lock_at_address (p : ℤ) (q : ℕ) (hq : 0 < q) (m : ℤ) :
    jointReading ((p : ℚ) / q) (q * m) = (((p * m : ℤ) : ℚ), ((q * m : ℤ) : ℚ)) ∧
      IsCycle (jointReading ((p : ℚ) / q) (q * m)) ∧
      (∀ v : Vec, ((q : ℤ) : ℚ) • (((p : ℚ) / q) • v) = (p : ℚ) • v) ∧
      (∀ (w : ℚ), 0 < w → ∀ (D : Matrix (Fin 3) (Fin 3) ℚ),
        (∀ x : Vec, x ⬝ᵥ (D *ᵥ x) = 0 → x = 0) → ∀ v : Vec,
        quad (faceForm w (pairSlip (((p : ℚ) / q) • v) v) D) ![((q : ℤ) : ℚ), (p : ℚ)] = 0) := by
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hread : jointReading ((p : ℚ) / q) (q * m) = (((p * m : ℤ) : ℚ), ((q * m : ℤ) : ℚ)) := by
    refine Prod.ext ?_ rfl
    simp only [jointReading]
    push_cast
    field_simp
  have hslip : ∀ v : Vec, ((q : ℤ) : ℚ) • (((p : ℚ) / q) • v) = (p : ℚ) • v := by
    intro v
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  refine ⟨hread, ?_, hslip, fun w hw D hdef v => (lock_iff_zero_power hw _ _ D hdef p q).mpr
    (hslip v)⟩
  rw [hread]
  exact ⟨(openPhase_eq_zero_iff _).mpr ⟨_, rfl⟩, (openPhase_eq_zero_iff _).mpr ⟨_, rfl⟩⟩

/-- [proved-derived; formal-checked] **The lock's period.** With `p` and `q` coprime, an aeon is a
cycle exactly when its tick count is a multiple of `q`. -/
theorem cycle_iff_period_dvd (p : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime (q : ℤ) p)
    (k : ℤ) : IsCycle (jointReading ((p : ℚ) / q) k) ↔ (q : ℤ) ∣ k := by
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [jointReading_isCycle_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hz : k * p = q * m := by
      have : (k : ℚ) * p = q * m := by
        rw [← hm]
        field_simp
      exact_mod_cast this
    exact hcop.dvd_of_dvd_mul_right ⟨m, hz⟩
  · rintro ⟨m, rfl⟩
    exact ⟨p * m, by push_cast; field_simp⟩

/-- [proved-derived; formal-checked] **Closure at no grain.** For an irrational ratio no aeon of a
nonzero number of ticks is a cycle. -/
theorem no_cycle_of_irrational {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    ¬ IsCycle (jointReading α k) := by
  rw [jointReading_isCycle_iff]
  rintro ⟨m, hm⟩
  exact (hα.intCast_mul hk).ne_int m hm

/-- [proved-derived; formal-checked] A joint cycle is read alike in the rational and the real chart
of the rate. -/
theorem isCycle_ratCast_iff (x : ℚ) (k : ℤ) :
    IsCycle (jointReading (x : ℝ) k) ↔ IsCycle (jointReading x k) := by
  rw [jointReading_isCycle_iff, jointReading_isCycle_iff]
  constructor <;> rintro ⟨m, hm⟩ <;> exact ⟨m, by exact_mod_cast hm⟩

/-- [proved-derived; formal-checked] **The Farey lock is a cycle of the real joint clock.** At rate
`p / q` the aeon of `q` ticks is the cycle of `lock_at_address`. -/
theorem isCycle_of_rational {α : ℝ} {p : ℤ} {q : ℕ} (hq : 0 < q) (hα : α = (p : ℝ) / q) :
    IsCycle (jointReading α (q : ℤ)) := by
  have hlock := (lock_at_address p q hq 1).2.1
  rw [mul_one] at hlock
  rw [hα, show ((p : ℝ) / q) = (((p : ℚ) / q : ℚ) : ℝ) by norm_cast, isCycle_ratCast_iff]
  exact hlock

/-- [proved-derived; formal-checked] **An address below the rate of a cycle, cross-multiplied.**
When the aeon of `T` ticks is a cycle of `c` whole windings (`T α = c`), `p / q < α` exactly when
`p T < c q`: the comparison of two addresses without a division. -/
theorem div_lt_rate_iff {α : ℝ} {T : ℕ} {c : ℤ} (hc : (T : ℝ) * α = c) (hT : 0 < T) {p q : ℤ}
    (hq : 0 < q) : (p : ℝ) / q < α ↔ p * (T : ℤ) < c * q := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : α * q * T = c * q := by rw [← hc]; ring
  rw [div_lt_iff₀ hqr]
  constructor
  · intro h
    have a := mul_lt_mul_of_pos_right h hTr
    have h' : (p : ℝ) * T < c * q := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (p : ℝ) * T < c * q := by exact_mod_cast h
    by_contra hne
    have a := mul_le_mul_of_nonneg_right (not_lt.mp hne) hTr.le
    linarith

/-- [proved-derived; formal-checked] **An address above the rate of a cycle, cross-multiplied.**
When `T α = c`, `α < p / q` exactly when `c q < p T`. -/
theorem rate_lt_div_iff {α : ℝ} {T : ℕ} {c : ℤ} (hc : (T : ℝ) * α = c) (hT : 0 < T) {p q : ℤ}
    (hq : 0 < q) : α < (p : ℝ) / q ↔ c * q < p * (T : ℤ) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : α * q * T = c * q := by rw [← hc]; ring
  rw [lt_div_iff₀ hqr]
  constructor
  · intro h
    have a := mul_lt_mul_of_pos_right h hTr
    have h' : (c : ℝ) * q < p * T := by linarith
    exact_mod_cast h'
  · intro h
    have h' : (c : ℝ) * q < p * T := by exact_mod_cast h
    by_contra hne
    have a := mul_le_mul_of_nonneg_right (not_lt.mp hne) hTr.le
    linarith

/-! ## 2. The convergents of the frequency ratio -/

section Convergents

variable (α : ℝ)

/-- [proved-derived; formal-checked] The continuants of `GenContFract.of α` are integers: every
partial numerator is `1` and every partial denominator an integer. -/
theorem contsAux_integral : ∀ n : ℕ, ∃ a b : ℤ, (GenContFract.of α).contsAux n = ⟨(a : ℝ), (b : ℝ)⟩
  | 0 => ⟨1, 0, by simp [zeroth_contAux_eq_one_zero]⟩
  | 1 => ⟨⌊α⌋, 1, by simp [first_contAux_eq_h_one, of_h_eq_floor]⟩
  | n + 2 => by
    obtain ⟨a₀, b₀, h₀⟩ := contsAux_integral n
    obtain ⟨a₁, b₁, h₁⟩ := contsAux_integral (n + 1)
    rcases hs : (GenContFract.of α).s.get? n with _ | gp
    · rw [contsAux_stable_step_of_terminated hs]
      exact ⟨a₁, b₁, h₁⟩
    · have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hs)
      obtain ⟨z, hz⟩ := exists_int_eq_of_partDen (partDen_eq_s_b hs)
      refine ⟨z * a₁ + a₀, z * b₁ + b₀, ?_⟩
      rw [contsAux_recurrence hs h₀ h₁, ha, hz]
      push_cast
      ring_nf

/-- [proved-derived; formal-checked] The convergent numerators are integers. -/
theorem nums_integral (n : ℕ) : ∃ p : ℤ, (GenContFract.of α).nums n = p := by
  obtain ⟨a, b, h⟩ := contsAux_integral α (n + 1)
  exact ⟨a, by rw [num_eq_conts_a, nth_cont_eq_succ_nth_contAux, h]⟩

/-- [proved-derived; formal-checked] The convergent denominators are integers. -/
theorem dens_integral (n : ℕ) : ∃ q : ℤ, (GenContFract.of α).dens n = q := by
  obtain ⟨a, b, h⟩ := contsAux_integral α (n + 1)
  exact ⟨b, by rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, h]⟩

/-- [proved-derived; formal-checked] Every convergent denominator is at least one tick. -/
theorem one_le_dens (n : ℕ) : 1 ≤ (GenContFract.of α).dens n := by
  induction n with
  | zero => rw [zeroth_den_eq_one]
  | succ n ih => exact ih.trans of_den_mono

theorem dens_pos (n : ℕ) : 0 < (GenContFract.of α).dens n := lt_of_lt_of_le one_pos (one_le_dens α n)

variable {α}

/-- [proved-derived; formal-checked] The continued fraction of an irrational ratio never
terminates. -/
theorem not_terminatedAt_of_irrational (hα : Irrational α) (n : ℕ) : ¬ (GenContFract.of α).TerminatedAt n := by
  intro h
  have hv := of_correctness_of_terminatedAt h
  obtain ⟨p, hp⟩ := nums_integral α n
  obtain ⟨q, hq⟩ := dens_integral α n
  have hq0 : (q : ℝ) ≠ 0 := by rw [← hq]; exact (dens_pos α n).ne'
  rw [conv_eq_num_div_den, hp, hq] at hv
  exact hα ⟨(p : ℚ) / q, by rw [hv]; push_cast; rfl⟩

/-- [proved-derived; formal-checked] For `n ≥ 1` the convergent denominators grow strictly. -/
theorem dens_lt_dens_succ (hα : Irrational α) (n : ℕ) :
    (GenContFract.of α).dens (n + 1) < (GenContFract.of α).dens (n + 2) := by
  obtain ⟨gp, hs⟩ : ∃ gp, (GenContFract.of α).s.get? (n + 1) = some gp :=
    Option.ne_none_iff_exists'.mp (not_terminatedAt_of_irrational hα (n + 1))
  have hrec := dens_recurrence (g := GenContFract.of α) (ppredB := (GenContFract.of α).dens n)
    (predB := (GenContFract.of α).dens (n + 1)) hs rfl rfl
  have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hs)
  have hb : 1 ≤ gp.b := of_one_le_get?_partDen (partDen_eq_s_b hs)
  have h0 := dens_pos α n
  have h1 := dens_pos α (n + 1)
  rw [hrec, ha]
  nlinarith

/-- [proved-derived; formal-checked] **The convergent near-return bound.** The aeon of `q_n` ticks
misses closure by at most `1/q_(n+1)` turns: `|q_n α − p_n| ≤ 1/q_(n+1)`. -/
theorem convergent_near_return (hα : Irrational α) (n : ℕ) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| ≤ 1 / (GenContFract.of α).dens (n + 1) := by
  have hq := dens_pos α n
  have hq' := dens_pos α (n + 1)
  have h := abs_sub_convs_le (not_terminatedAt_of_irrational hα n)
  rw [conv_eq_num_div_den] at h
  have hsplit : (GenContFract.of α).dens n * α - (GenContFract.of α).nums n =
      (GenContFract.of α).dens n * (α - (GenContFract.of α).nums n / (GenContFract.of α).dens n) := by
    field_simp
  rw [hsplit, abs_mul, abs_of_pos hq]
  calc (GenContFract.of α).dens n * |α - (GenContFract.of α).nums n / (GenContFract.of α).dens n|
      ≤ (GenContFract.of α).dens n * (1 / ((GenContFract.of α).dens n * (GenContFract.of α).dens (n + 1))) := by gcongr
    _ = 1 / (GenContFract.of α).dens (n + 1) := by field_simp

/-- [proved-derived; formal-checked] **Every convergent from the first on is a near-return within
one tick's share:** `|q_n α − p_n| < 1/q_n` for `n ≥ 1`. -/
theorem convergent_near_return_lt (hα : Irrational α) (n : ℕ) (hn : 1 ≤ n) :
    |(GenContFract.of α).dens n * α - (GenContFract.of α).nums n| < 1 / (GenContFract.of α).dens n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine (convergent_near_return hα (m + 1)).trans_lt ?_
  exact one_div_lt_one_div_of_lt (dens_pos α (m + 1)) (dens_lt_dens_succ hα m)

/-- [proved-derived; formal-checked] **Near-returns at every grain, closure at none.** -/
theorem convergent_never_closes (hα : Irrational α) (n : ℕ) :
    (GenContFract.of α).dens n * α - (GenContFract.of α).nums n ≠ 0 := by
  obtain ⟨p, hp⟩ := nums_integral α n
  obtain ⟨q, hq⟩ := dens_integral α n
  have hq0 : q ≠ 0 := by
    intro h
    have := dens_pos α n
    rw [hq, h] at this
    simp at this
  rw [hp, hq, sub_ne_zero]
  exact (hα.intCast_mul hq0).ne_int p

/-- [proved-derived; formal-checked] **Consecutive convergents are Farey neighbours:**
`p_n q_(n+1) − q_n p_(n+1) = (−1)^(n+1)` (Mathlib's determinant formula, every partial numerator
being `1`). -/
theorem convergents_are_farey_neighbours (hα : Irrational α) (n : ℕ) :
    (GenContFract.of α).nums n * (GenContFract.of α).dens (n + 1) - (GenContFract.of α).dens n * (GenContFract.of α).nums (n + 1) = (-1) ^ (n + 1) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      -(((GenContFract.of α).partNums.get? i).getD 0) = (-1 : ℝ) := by
    intro i _
    obtain ⟨gp, hs⟩ : ∃ gp, (GenContFract.of α).s.get? i = some gp :=
      Option.ne_none_iff_exists'.mp (not_terminatedAt_of_irrational hα i)
    rw [partNum_eq_s_a hs, Option.getD_some, of_partNum_eq_one (partNum_eq_s_a hs)]
  rw [determinant, Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_range]

/-- [proved-derived; formal-checked] **A lock strictly between two consecutive convergents costs at
least their mediant's period.** Consecutive convergents are neighbours, so the
`Geometry/PairResonance` owner applies: any address `a / b` strictly between them has
`b ≥ q_n + q_(n+1)`. -/
theorem between_consecutive_convergents_costs_the_mediant (hα : Irrational α) (n : ℕ)
    {P Q P' Q' : ℤ} (hP : (GenContFract.of α).nums n = P) (hQ : (GenContFract.of α).dens n = Q)
    (hP' : (GenContFract.of α).nums (n + 1) = P') (hQ' : (GenContFract.of α).dens (n + 1) = Q') (a b : ℤ) (hb : 0 < b)
    (hbetween : (P * b < a * Q ∧ a * Q' < P' * b) ∨ (P' * b < a * Q' ∧ a * Q < P * b)) :
    Q + Q' ≤ b := by
  have hQpos : 0 < Q := by exact_mod_cast hQ ▸ dens_pos α n
  have hQ'pos : 0 < Q' := by exact_mod_cast hQ' ▸ dens_pos α (n + 1)
  have hdet : P * Q' - Q * P' = (-1) ^ (n + 1) := by
    have h := convergents_are_farey_neighbours hα n
    rw [hP, hQ, hP', hQ'] at h
    exact_mod_cast h
  have hunit : P * Q' - Q * P' = 1 ∨ P * Q' - Q * P' = -1 := by
    rw [hdet]; exact neg_one_pow_eq_or ℤ (n + 1)
  rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hlt : P * Q' < P' * Q := by
      have e1 : P * b * Q' < a * Q * Q' := mul_lt_mul_of_pos_right h1 hQ'pos
      have e2 : a * Q' * Q < P' * b * Q := mul_lt_mul_of_pos_right h2 hQpos
      have : (P * Q') * b < (P' * Q) * b := by nlinarith
      exact lt_of_mul_lt_mul_right this hb.le
    have hadj : P' * Q - P * Q' = 1 := by rcases hunit with h | h <;> linarith
    exact Holonics.Geometry.PairResonance.between_neighbours_costs_at_least_the_mediant
      P Q P' Q' a b hQpos hQ'pos hadj h1 h2
  · have hlt : P' * Q < P * Q' := by
      have e1 : P' * b * Q < a * Q' * Q := mul_lt_mul_of_pos_right h1 hQpos
      have e2 : a * Q * Q' < P * b * Q' := mul_lt_mul_of_pos_right h2 hQ'pos
      have : (P' * Q) * b < (P * Q') * b := by nlinarith
      exact lt_of_mul_lt_mul_right this hb.le
    have hadj : P * Q' - P' * Q = 1 := by rcases hunit with h | h <;> linarith
    have := Holonics.Geometry.PairResonance.between_neighbours_costs_at_least_the_mediant
      P' Q' P Q a b hQ'pos hQpos hadj h1 h2
    linarith

end Convergents

/-! ## 3. The best near-returns are the convergents -/

/-- [proved-standard; formal-checked] **A near-return exists at every grain** (Dirichlet, Mathlib):
among the aeons of at most `N` ticks one misses closure by at most `1/(N+1)` turns. -/
theorem near_return_at_every_grain (α : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ p q : ℤ, 0 < q ∧ q ≤ N ∧ |(q : ℝ) * α - p| ≤ 1 / (N + 1) :=
  Real.exists_int_int_abs_mul_sub_le α hN

/-- [proved-standard; formal-checked] **Infinitely many near-returns within one tick's share**
for an irrational ratio: `|q α − p| < 1/q` for infinitely many addresses `p / q` in lowest terms
(Mathlib). -/
theorem infinitely_many_near_returns {α : ℝ} (hα : Irrational α) :
    {r : ℚ | |(r.den : ℝ) * α - r.num| < 1 / r.den}.Infinite := by
  refine (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hα).mono ?_
  intro r hr
  simp only [Set.mem_ofPred_eq] at hr ⊢
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hsplit : (r.den : ℝ) * α - r.num = r.den * (α - r) := by
    rw [Rat.cast_def]
    field_simp
  rw [hsplit, abs_mul, abs_of_pos hd]
  calc (r.den : ℝ) * |α - r| < r.den * (1 / (r.den : ℝ) ^ 2) := by gcongr
    _ = 1 / r.den := by field_simp

/-- [proved-standard; formal-checked] **A good near-return is a convergent** (Legendre, Mathlib):
if the aeon of `q` ticks misses closure by less than `1/(2q)` turns, with `p / q` in lowest terms,
then `p / q` is a convergent of the frequency ratio. -/
theorem good_near_return_is_convergent (α : ℝ) (r : ℚ)
    (h : |(r.den : ℝ) * α - r.num| < 1 / (2 * r.den)) : ∃ n, r = α.convergent n := by
  apply Real.exists_rat_eq_convergent
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hsplit : (r.den : ℝ) * α - r.num = r.den * (α - r) := by
    rw [Rat.cast_def]
    field_simp
  rw [hsplit, abs_mul, abs_of_pos hd] at h
  have : |α - r| < 1 / (2 * r.den) / r.den := by
    rw [lt_div_iff₀ hd]
    linarith
  calc |α - r| < 1 / (2 * r.den) / r.den := this
    _ = 1 / (2 * (r.den : ℝ) ^ 2) := by field_simp

/-- [proved-derived; formal-checked] **A rational ratio locks at a convergent.** Its continued
fraction terminates, some convergent closes exactly, and the aeon of `q_n` ticks is a cycle. -/
theorem rational_ratio_locks_at_a_convergent (x : ℚ) :
    ∃ n : ℕ, ∃ P Q : ℤ, (GenContFract.of (x : ℝ)).nums n = P ∧ (GenContFract.of (x : ℝ)).dens n = Q ∧ 0 < Q ∧
      (Q : ℝ) * x - P = 0 ∧ IsCycle (jointReading (x : ℝ) Q) := by
  obtain ⟨n, hn⟩ := of_correctness_of_terminates ((terminates_iff_rat (x : ℝ)).mpr ⟨x, rfl⟩)
  obtain ⟨P, hP⟩ := nums_integral (x : ℝ) n
  obtain ⟨Q, hQ⟩ := dens_integral (x : ℝ) n
  have hQpos : (0 : ℝ) < Q := hQ ▸ dens_pos (x : ℝ) n
  have hclose : (Q : ℝ) * x - P = 0 := by
    rw [conv_eq_num_div_den, hP, hQ] at hn
    rw [hn]
    field_simp
    ring
  refine ⟨n, P, Q, hP, hQ, by exact_mod_cast hQpos, hclose, ?_⟩
  exact (jointReading_isCycle_iff _ _).mpr ⟨P, by linarith⟩

end Holonics.Aeon.Clock.Lock
