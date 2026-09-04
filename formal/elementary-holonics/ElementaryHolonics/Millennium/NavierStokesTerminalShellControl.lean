import ElementaryHolonics.Millennium.NavierStokesOfficialAnalyticDischarges

/-!
# Dyadic terminal-shell plumbing for canonical control

**[proved-derived; formal-checked]** This module is plumbing only.  It partitions the open
lifespan into two exact half-open dyadic shell families, records the canonical derivative-rate
integral on each shell, and turns a genuinely summable nonnegative shell majorant into the official
`CanonicalTerminalControl` field.  It does not construct such a majorant from the
Navier--Stokes equations and therefore does not close the terminal analytic obstruction.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval NNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesTerminalShellControl

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOfficialAnalyticDischarges
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime

/-! ## Exact two-sided dyadic partition -/

/-- [definition] The positive dyadic radius `T * 2⁻ⁿ` measured from either endpoint. -/
def terminalDyadicRadius (T : ℝ) (n : ℕ) : ℝ :=
  T * (1 / 2 : ℝ) ^ n

@[simp]
theorem terminalDyadicRadius_zero (T : ℝ) :
    terminalDyadicRadius T 0 = T := by
  simp [terminalDyadicRadius]

theorem terminalDyadicRadius_pos {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < terminalDyadicRadius T n := by
  exact mul_pos hT (pow_pos (by norm_num) n)

theorem terminalDyadicRadius_lt_terminal {T : ℝ} (hT : 0 < T) (n : ℕ) :
    terminalDyadicRadius T (n + 1) < T := by
  have hanti : StrictAnti (terminalDyadicRadius T) := by
    apply strictAnti_nat_of_succ_lt
    intro m
    unfold terminalDyadicRadius
    rw [pow_succ]
    have hp : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
    nlinarith
  simpa using hanti (Nat.zero_lt_succ n)

theorem terminalDyadicRadius_strictAnti {T : ℝ} (hT : 0 < T) :
    StrictAnti (terminalDyadicRadius T) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  unfold terminalDyadicRadius
  rw [pow_succ]
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  nlinarith

theorem tendsto_terminalDyadicRadius_atTop {T : ℝ} :
    Tendsto (terminalDyadicRadius T) atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun n : ℕ ↦ T * (1 / 2 : ℝ) ^ n) atTop (nhds 0)
  simpa only [mul_zero] using hpow.const_mul T

/-- [definition] `false` addresses shells accumulating at the initial endpoint and `true`
addresses their reflected shells accumulating at the terminal endpoint.  Every shell is half-open
and compactly contained in `(0,T)`. -/
def terminalDyadicShell (T : ℝ) : Bool × ℕ → Set ℝ
  | (false, n) =>
      Ioc (terminalDyadicRadius T (n + 2)) (terminalDyadicRadius T (n + 1))
  | (true, n) =>
      Ioc (T - terminalDyadicRadius T (n + 1))
        (T - terminalDyadicRadius T (n + 2))

/-- **[proved-derived; formal-checked]** The two addressed dyadic shell families cover the open
lifespan exactly.  No endpoint occurrence is silently added. -/
theorem iUnion_terminalDyadicShell {T : ℝ} (hT : 0 < T) :
    (⋃ i : Bool × ℕ, terminalDyadicShell T i) = Ioo 0 T := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨⟨side, n⟩, hx⟩
    cases side with
    | false =>
        change terminalDyadicRadius T (n + 2) < x ∧
          x ≤ terminalDyadicRadius T (n + 1) at hx
        exact ⟨(terminalDyadicRadius_pos hT (n + 2)).trans hx.1,
          hx.2.trans_lt (terminalDyadicRadius_lt_terminal hT n)⟩
    | true =>
        change T - terminalDyadicRadius T (n + 1) < x ∧
          x ≤ T - terminalDyadicRadius T (n + 2) at hx
        exact ⟨sub_pos.mpr (terminalDyadicRadius_lt_terminal hT n) |>.trans hx.1,
          hx.2.trans_lt (sub_lt_self T (terminalDyadicRadius_pos hT (n + 2)))⟩
  · intro hx
    have hradiusHalf : terminalDyadicRadius T 1 = T / 2 := by
      norm_num [terminalDyadicRadius, div_eq_mul_inv]
    by_cases hxLower : x ≤ terminalDyadicRadius T 1
    · have hex : ∃ n : ℕ, terminalDyadicRadius T (n + 2) < x := by
        have heventually : ∀ᶠ n in atTop, terminalDyadicRadius T n < x :=
          (tendsto_terminalDyadicRadius_atTop.eventually (Iio_mem_nhds hx.1))
        rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
        exact ⟨N, hN (N + 2) (by omega)⟩
      let n := Nat.find hex
      have hnLower : terminalDyadicRadius T (n + 2) < x := Nat.find_spec hex
      have hnUpper : x ≤ terminalDyadicRadius T (n + 1) := by
        by_cases hn : n = 0
        · simpa [n, hn] using hxLower
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hpred : Nat.pred n < n := Nat.pred_lt hn
          have hminimal := Nat.find_min hex hpred
          have hpredSucc : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnpos
          have hindex : Nat.pred n + 2 = n + 1 := by omega
          rw [hindex] at hminimal
          exact le_of_not_gt hminimal
      apply Set.mem_iUnion.2
      exact ⟨(false, n), hnLower, hnUpper⟩
    · have hxUpper' : terminalDyadicRadius T 1 < x := lt_of_not_ge hxLower
      let y : ℝ := T - x
      have hyPos : 0 < y := sub_pos.mpr hx.2
      have hyHalf : y < terminalDyadicRadius T 1 := by
        dsimp [y]
        rw [hradiusHalf] at hxUpper' ⊢
        linarith
      have hex : ∃ n : ℕ, terminalDyadicRadius T (n + 2) ≤ y := by
        have heventually : ∀ᶠ n in atTop, terminalDyadicRadius T n < y :=
          (tendsto_terminalDyadicRadius_atTop.eventually (Iio_mem_nhds hyPos))
        rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
        exact ⟨N, (hN (N + 2) (by omega)).le⟩
      let n := Nat.find hex
      have hnUpper : terminalDyadicRadius T (n + 2) ≤ y := Nat.find_spec hex
      have hnLower : y < terminalDyadicRadius T (n + 1) := by
        by_cases hn : n = 0
        · simpa [n, hn] using hyHalf
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hpred : Nat.pred n < n := Nat.pred_lt hn
          have hminimal := Nat.find_min hex hpred
          have hpredSucc : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnpos
          have hindex : Nat.pred n + 2 = n + 1 := by omega
          rw [hindex] at hminimal
          exact lt_of_not_ge hminimal
      apply Set.mem_iUnion.2
      refine ⟨(true, n), ?_, ?_⟩
      · dsimp [y] at hnLower
        linarith
      · dsimp [y] at hnUpper
        linarith

/-! ## Compact-interior shell integrals -/

/-- **[proved-derived; formal-checked]** The official terminal derivative rate is integrable on
every compact interval strictly inside the lifespan. -/
theorem terminalCanonicalVorticityDerivativeRate_intervalIntegrable_compactInterior
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (habOrder : a ≤ b) (hb : b < T) :
    IntervalIntegrable (terminalCanonicalVorticityDerivativeRate solution) volume a b := by
  rw [terminalCanonicalVorticityDerivativeRate_eq_openPeriodic solution]
  have hab : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  let lift : Icc a b → Ioo (0 : ℝ) T := fun s ↦ ⟨s.1, hab s.2⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hrestricted : Continuous (fun s : Icc a b ↦
      openPeriodicCanonicalVorticityDerivativeRate solution s.1) := by
    have hcomposed := NNReal.continuous_coe.comp
      ((openPeriodicCanonicalVorticityLipschitzConstant_continuous solution).comp hlift)
    apply hcomposed.congr
    intro s
    exact (openPeriodicCanonicalVorticityDerivativeRate_eq solution (hab s.2)).symm
  have hcontinuousOn : ContinuousOn
      (openPeriodicCanonicalVorticityDerivativeRate solution) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa only [Set.domRestrict_def] using hrestricted
  have huIcc : ContinuousOn
      (openPeriodicCanonicalVorticityDerivativeRate solution) [[a, b]] := by
    simpa [uIcc_of_le habOrder] using hcontinuousOn
  exact huIcc.intervalIntegrable

/-- The totalized official terminal derivative rate is pointwise nonnegative. -/
theorem terminalCanonicalVorticityDerivativeRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s : ℝ) :
    0 ≤ terminalCanonicalVorticityDerivativeRate solution s := by
  rw [terminalCanonicalVorticityDerivativeRate_eq_openPeriodic solution]
  exact openPeriodicCanonicalVorticityDerivativeRate_nonneg solution s

/-- [definition] The exact nonnegative canonical derivative-rate integral on one addressed dyadic
shell. -/
def terminalCanonicalVorticityDerivativeShellIntegral
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (i : Bool × ℕ) : ℝ :=
  ∫ s in terminalDyadicShell T i,
    terminalCanonicalVorticityDerivativeRate solution s

theorem terminalCanonicalVorticityDerivativeShellIntegral_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (i : Bool × ℕ) :
    0 ≤ terminalCanonicalVorticityDerivativeShellIntegral solution i := by
  unfold terminalCanonicalVorticityDerivativeShellIntegral
  exact integral_nonneg fun s ↦ terminalCanonicalVorticityDerivativeRate_nonneg solution s

/-- Every addressed shell is discharged by the already proved compact-interior integrability. -/
theorem integrableOn_terminalCanonicalVorticityDerivativeRate_terminalDyadicShell
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hT : 0 < T) (i : Bool × ℕ) :
    IntegrableOn (terminalCanonicalVorticityDerivativeRate solution)
      (terminalDyadicShell T i) volume := by
  rcases i with ⟨side, n⟩
  have hanti := terminalDyadicRadius_strictAnti hT
  cases side with
  | false =>
      change IntegrableOn (terminalCanonicalVorticityDerivativeRate solution)
        (Ioc (terminalDyadicRadius T (n + 2)) (terminalDyadicRadius T (n + 1))) volume
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (hanti (by omega : n + 1 < n + 2)).le).1
      exact terminalCanonicalVorticityDerivativeRate_intervalIntegrable_compactInterior
        solution (terminalDyadicRadius_pos hT (n + 2))
          (hanti (by omega : n + 1 < n + 2)).le
          (terminalDyadicRadius_lt_terminal hT n)
  | true =>
      change IntegrableOn (terminalCanonicalVorticityDerivativeRate solution)
        (Ioc (T - terminalDyadicRadius T (n + 1))
          (T - terminalDyadicRadius T (n + 2))) volume
      have horder : T - terminalDyadicRadius T (n + 1) ≤
          T - terminalDyadicRadius T (n + 2) := by
        linarith [hanti (by omega : n + 1 < n + 2)]
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).1
      exact terminalCanonicalVorticityDerivativeRate_intervalIntegrable_compactInterior
        solution (sub_pos.mpr (terminalDyadicRadius_lt_terminal hT n)) horder
          (sub_lt_self T (terminalDyadicRadius_pos hT (n + 2)))

/-! ## Summable shell receipt and official control -/

/-- [definition; plumbing] A genuinely summable nonnegative majorant for the exact shell
integrals.  The domination field is the source-specific analytic obligation; this structure does
not manufacture it. -/
structure TerminalShellMajorantReceipt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) where
  majorant : Bool × ℕ → ℝ
  majorant_nonneg : ∀ i, 0 ≤ majorant i
  majorant_summable : Summable majorant
  dominates : ∀ i,
    terminalCanonicalVorticityDerivativeShellIntegral solution i ≤ majorant i

/-- **[proved-derived; formal-checked; plumbing]** Compact-interior shell integrability plus an
actually summable nonnegative shell majorant returns `CanonicalTerminalControl`.  This theorem is
an exact countable-gluing adapter, not a PDE estimate and not a completion claim. -/
theorem canonicalTerminalControl_of_terminalShellMajorant
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hT : 0 < T) (receipt : TerminalShellMajorantReceipt solution) :
    CanonicalTerminalControl solution := by
  have hshellSummable : Summable
      (terminalCanonicalVorticityDerivativeShellIntegral solution) :=
    Summable.of_nonneg_of_le
      (terminalCanonicalVorticityDerivativeShellIntegral_nonneg solution)
      receipt.dominates receipt.majorant_summable
  have hnormSummable : Summable (fun i : Bool × ℕ ↦
      ∫ s in terminalDyadicShell T i,
        ‖terminalCanonicalVorticityDerivativeRate solution s‖) := by
    apply hshellSummable.congr
    intro i
    simp only [terminalCanonicalVorticityDerivativeShellIntegral, Real.norm_eq_abs,
      abs_of_nonneg (terminalCanonicalVorticityDerivativeRate_nonneg solution _)]
  have hunion : IntegrableOn (terminalCanonicalVorticityDerivativeRate solution)
      (⋃ i : Bool × ℕ, terminalDyadicShell T i) volume :=
    integrableOn_iUnion_of_summable_integral_norm
      (integrableOn_terminalCanonicalVorticityDerivativeRate_terminalDyadicShell solution hT)
      hnormSummable
  unfold CanonicalTerminalControl
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
  simpa only [iUnion_terminalDyadicShell hT] using hunion

section Audit

#print axioms iUnion_terminalDyadicShell
#print axioms terminalCanonicalVorticityDerivativeRate_intervalIntegrable_compactInterior
#print axioms integrableOn_terminalCanonicalVorticityDerivativeRate_terminalDyadicShell
#print axioms canonicalTerminalControl_of_terminalShellMajorant

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalShellControl
