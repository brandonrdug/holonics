import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# A terminal velocity trace from uniform tail transport

**[open]** Mathlib supplies Picard--Lindelöf for ordinary differential equations in a Banach space,
but the current library has no periodic Sobolev-space realization, Leray projector,
infinite-dimensional Stokes/heat semigroup, or local Navier--Stokes theorem.  In particular, the
Navier--Stokes vector field is not an ODE on `H³`: its Laplacian loses two derivatives.

**[conditional]** This module closes a smaller prerequisite.  Interior velocity slices are first
descended to the genuine spatial torus.  A named Lipschitz control in the Banach space of continuous
torus fields supplies time compactness.  Completeness then constructs a continuous periodic
terminal velocity trace as the limit of the complete strict tail; an addressed dyadic approach is
proved to select that same terminal face.

**[open]** The premise is deliberately independent of the repository's scalar H³ receiver: an
integral H³ bound alone does not imply this time-Lipschitz law.  The returned trace is `C⁰`; it does
not yet prove preservation of three spatial derivatives, incompressibility, or existence of a
restarted Navier--Stokes patch.
-/

noncomputable section

open Filter Set Topology

namespace Soma.Holonics.Millennium.NavierStokesTerminalTrace

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-- The controlled half-open tail, retaining the proof that every represented time precedes the
terminal face. -/
abbrev TailTime (a T : ℝ) := Ico a T

/-- The same strict tail, now situated inside its closed completion `[a,T]`. -/
def ClosedTailPreterminalTimes (a T : ℝ) : Set (Icc a T) :=
  {t | (t : ℝ) < T}

/-- The strict tail is dense in its closed completion.  This is the carrier needed to extend the
whole tail, rather than merely select one convergent subsequence. -/
theorem closedTailPreterminalTimes_dense
    {a T : ℝ} (haT : a < T) : Dense (ClosedTailPreterminalTimes a T) := by
  rw [Subtype.dense_iff]
  have himage :
      ((fun t : Icc a T => (t : ℝ)) '' ClosedTailPreterminalTimes a T) = Ico a T := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2.1, hs⟩
    · intro ht
      exact ⟨⟨t, ht.1, ht.2.le⟩, ht.2, rfl⟩
  rw [himage, closure_Ico haT.ne]

/-- The absent terminal face, represented in the closed time carrier. -/
def closedTailTerminalTime (a T : ℝ) (haT : a ≤ T) : Icc a T :=
  ⟨T, haT, le_rfl⟩

/-- Forget the closed ambient carrier while retaining the strict-tail address. -/
def closedPreterminalToTailTime
    {a T : ℝ} (t : ClosedTailPreterminalTimes a T) : TailTime a T :=
  ⟨t.1.1, t.1.2.1, t.2⟩

/-- A geometric sequence of strict interior times approaching `T` from the left. -/
def terminalApproachTime (a T : ℝ) (n : ℕ) : ℝ :=
  T - (T - a) * (1 / 2 : ℝ) ^ (n + 1)

/-- Every dyadic approach time lies in the controlled half-open tail. -/
theorem terminalApproachTime_mem_Ico
    {a T : ℝ} (haT : a < T) (n : ℕ) :
    terminalApproachTime a T n ∈ Ico a T := by
  have hpowPos : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have hpowLt : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
  constructor <;> unfold terminalApproachTime <;> nlinarith

/-- The addressed dyadic times converge to the absent terminal face. -/
theorem terminalApproachTime_tendsto
    (a T : ℝ) : Tendsto (terminalApproachTime a T) atTop (𝓝 T) := by
  have hpow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa [pow_succ] using hbase.mul_const (1 / 2 : ℝ)
  change Tendsto
    (fun n : ℕ ↦ T - (T - a) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 T)
  have hmul : Tendsto
      (fun n : ℕ ↦ (T - a) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ ↦ (T - a) * (1 / 2 : ℝ) ^ (n + 1)) atTop
        (𝓝 ((T - a) * 0)))
  simpa using (tendsto_const_nhds.sub hmul : Tendsto
    (fun n : ℕ ↦ T - (T - a) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (T - 0)))

/-- The dyadic approach as an inhabitant of the controlled tail subtype. -/
def terminalApproachTailTime
    {a T : ℝ} (haT : a < T) (n : ℕ) : TailTime a T :=
  ⟨terminalApproachTime a T n, terminalApproachTime_mem_Ico haT n⟩

/-- The same addressed approach, now living in the dense subset of `[a,T]`. -/
def terminalApproachClosedPreterminalTime
    {a T : ℝ} (haT : a < T) (n : ℕ) : ClosedTailPreterminalTimes a T :=
  ⟨⟨terminalApproachTime a T n,
      (terminalApproachTime_mem_Ico haT n).1,
      (terminalApproachTime_mem_Ico haT n).2.le⟩,
    (terminalApproachTime_mem_Ico haT n).2⟩

/-- The addressed approach converges to the terminal face in the dense-subset filter used by
uniform extension. -/
theorem terminalApproachClosedPreterminalTime_tendsto
    {a T : ℝ} (haT : a < T) :
    Tendsto (terminalApproachClosedPreterminalTime haT) atTop
      (Filter.comap ((↑) : ClosedTailPreterminalTimes a T → Icc a T)
        (𝓝 (closedTailTerminalTime a T haT.le))) := by
  rw [Filter.tendsto_comap_iff, tendsto_subtype_rng]
  simpa [Function.comp_def, terminalApproachClosedPreterminalTime,
    closedTailTerminalTime] using terminalApproachTime_tendsto a T

/-- Although the half-open tail is not complete, its addressed terminal approach is Cauchy. -/
theorem terminalApproachTailTime_cauchy
    {a T : ℝ} (haT : a < T) :
    CauchySeq (terminalApproachTailTime haT) := by
  have hreal : CauchySeq (terminalApproachTime a T) :=
    (terminalApproachTime_tendsto a T).cauchySeq
  rw [Metric.cauchySeq_iff'] at hreal ⊢
  simpa [terminalApproachTailTime, Subtype.dist_eq] using hreal

/-- A strict-interior velocity slice descended to the genuine compact spatial torus. -/
def tailTorusVelocitySlice
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (t : TailTime a T) : C(SpatialTorus, Space) := by
  have ht : (t : ℝ) ∈ Ioo 0 T := ⟨ha.trans_le t.2.1, t.2.2⟩
  exact periodicTorusLift (fun x ↦ velocity x (t : ℝ))
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht).continuous
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)

@[simp]
theorem tailTorusVelocitySlice_projection
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (t : TailTime a T) (x : Space) :
    tailTorusVelocitySlice solution ha t (euclideanToSpatialTorus x) = velocity x t := by
  unfold tailTorusVelocitySlice
  apply periodicTorusLift_projection

/-- The actual torus velocity, regarded as a function on the dense subset of the closed time
carrier. -/
def closedPreterminalTorusVelocitySlice
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) : ClosedTailPreterminalTimes a T → C(SpatialTorus, Space) :=
  fun t => tailTorusVelocitySlice solution ha (closedPreterminalToTailTime t)

/-- The precise time-compactness receipt.  The Lipschitz inequality is measured in the supremum
norm on continuous genuine-torus fields; no H³ consequence is built into this carrier. -/
structure UniformTorusVelocityTailControl
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  base_pos : 0 < a
  base_lt_terminal : a < T
  timeLipschitzConstant : NNReal
  timeLipschitz : LipschitzWith timeLipschitzConstant
    (tailTorusVelocitySlice solution base_pos)

/-- Lipschitz control survives the change from the open-tail subtype to the dense subset of its
closed completion. -/
theorem UniformTorusVelocityTailControl.closedPreterminal_lipschitz
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    LipschitzWith control.timeLipschitzConstant
      (closedPreterminalTorusVelocitySlice solution control.base_pos) := by
  intro s t
  simpa [closedPreterminalTorusVelocitySlice, closedPreterminalToTailTime,
    Subtype.edist_eq] using
    control.timeLipschitz (closedPreterminalToTailTime s) (closedPreterminalToTailTime t)

/-- Canonical full-tail extension to the terminal face. -/
def UniformTorusVelocityTailControl.fullTailTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    C(SpatialTorus, Space) :=
  (closedTailPreterminalTimes_dense control.base_lt_terminal).extend
    (closedPreterminalTorusVelocitySlice solution control.base_pos)
    (closedTailTerminalTime a T control.base_lt_terminal.le)

/-- The canonical extension is approached by every strict-tail history converging to `T`, not
only by the chosen dyadic history. -/
theorem UniformTorusVelocityTailControl.tendsto_fullTailTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    Tendsto (closedPreterminalTorusVelocitySlice solution control.base_pos)
      (Filter.comap ((↑) : ClosedTailPreterminalTimes a T → Icc a T)
        (𝓝 (closedTailTerminalTime a T control.base_lt_terminal.le)))
      (𝓝 control.fullTailTrace) := by
  exact (closedTailPreterminalTimes_dense control.base_lt_terminal).extend_spec
    control.closedPreterminal_lipschitz.uniformContinuous
    (closedTailTerminalTime a T control.base_lt_terminal.le)

/-- The dyadic history converges to the same canonical value as the complete strict tail. -/
theorem UniformTorusVelocityTailControl.tendsto_fullTailTrace_dyadic
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    Tendsto
      (fun n ↦ tailTorusVelocitySlice solution control.base_pos
        (terminalApproachTailTime control.base_lt_terminal n))
      atTop (𝓝 control.fullTailTrace) := by
  have h := control.tendsto_fullTailTrace.comp
    (terminalApproachClosedPreterminalTime_tendsto control.base_lt_terminal)
  convert h using 1
  funext n
  rfl

/-- A continuous genuine-torus field reached as the uniform limit of the addressed interior
velocity slices. -/
structure TerminalTorusVelocityTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (control : UniformTorusVelocityTailControl (a := a) solution) where
  trace : C(SpatialTorus, Space)
  tendsto_dyadic :
    Tendsto
      (fun n ↦ tailTorusVelocitySlice solution control.base_pos
        (terminalApproachTailTime control.base_lt_terminal n))
      atTop (𝓝 trace)

/-- Any dyadic terminal trace is the canonical full-tail extension; Lipschitz transport rules out
subsequence-dependent terminal faces. -/
theorem TerminalTorusVelocityTrace.trace_eq_fullTailTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control) :
    terminal.trace = control.fullTailTrace := by
  exact tendsto_nhds_unique terminal.tendsto_dyadic control.tendsto_fullTailTrace_dyadic

/-- Consequently every strict-tail history approaching `T` converges to the returned terminal
trace, not only the construction's selected dyadic sequence. -/
theorem TerminalTorusVelocityTrace.tendsto_fullTail
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control) :
    Tendsto (closedPreterminalTorusVelocitySlice solution control.base_pos)
      (Filter.comap ((↑) : ClosedTailPreterminalTimes a T → Icc a T)
        (𝓝 (closedTailTerminalTime a T control.base_lt_terminal.le)))
      (𝓝 terminal.trace) := by
  simpa [terminal.trace_eq_fullTailTrace] using control.tendsto_fullTailTrace

/-- The controlled velocity slices form a Cauchy sequence in the continuous-map Banach space. -/
theorem UniformTorusVelocityTailControl.cauchySeq_velocitySlices
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    CauchySeq
      (fun n ↦ tailTorusVelocitySlice solution control.base_pos
        (terminalApproachTailTime control.base_lt_terminal n)) := by
  simpa [Function.comp_def] using control.timeLipschitz.cauchySeq_comp
    (terminalApproachTailTime_cauchy control.base_lt_terminal)

/-- Completeness of continuous fields on the compact torus constructs the terminal trace. -/
def UniformTorusVelocityTailControl.terminalTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (control : UniformTorusVelocityTailControl (a := a) solution) :
    TerminalTorusVelocityTrace (a := a) solution control where
  trace := limUnder atTop
    (fun n ↦ tailTorusVelocitySlice solution control.base_pos
      (terminalApproachTailTime control.base_lt_terminal n))
  tendsto_dyadic := control.cauchySeq_velocitySlices.tendsto_limUnder

/-- Pull the terminal torus trace back to the repository's Euclidean presentation. -/
def TerminalTorusVelocityTrace.euclideanTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control) :
    InitialVelocity :=
  fun x ↦ terminal.trace (euclideanToSpatialTorus x)

/-- The constructed Euclidean terminal trace is continuous. -/
theorem TerminalTorusVelocityTrace.continuous_euclideanTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control) :
    Continuous terminal.euclideanTrace := by
  exact terminal.trace.continuous.comp
    euclideanToSpatialTorus_isOpenQuotientMap.continuous

/-- The quotient pullback makes the constructed terminal trace exactly one-periodic. -/
theorem TerminalTorusVelocityTrace.isOnePeriodic_euclideanTrace
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control) :
    IsOnePeriodic terminal.euclideanTrace := by
  intro x i
  apply congrArg terminal.trace
  ext coordinate
  simp [euclideanToSpatialTorus, piToSpatialTorus]
  split_ifs <;> simp

/-- Uniform torus convergence implies convergence at every Euclidean spatial receiver. -/
theorem TerminalTorusVelocityTrace.tendsto_euclideanTrace_dyadic
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control)
    (x : Space) :
    Tendsto
      (fun n ↦ velocity x
        (terminalApproachTime a T n))
      atTop (𝓝 (terminal.euclideanTrace x)) := by
  have heval := (continuous_eval_const (euclideanToSpatialTorus x)).continuousAt.tendsto.comp
    terminal.tendsto_dyadic
  change Tendsto
    (fun n ↦ tailTorusVelocitySlice solution control.base_pos
      (terminalApproachTailTime control.base_lt_terminal n)
        (euclideanToSpatialTorus x))
    atTop (𝓝 (terminal.trace (euclideanToSpatialTorus x))) at heval
  have hfunctions :
      (fun n ↦ tailTorusVelocitySlice solution control.base_pos
        (terminalApproachTailTime control.base_lt_terminal n)
          (euclideanToSpatialTorus x)) =
      (fun n ↦ velocity x (terminalApproachTime a T n)) := by
    funext n
    exact tailTorusVelocitySlice_projection solution control.base_pos
      (terminalApproachTailTime control.base_lt_terminal n) x
  rw [hfunctions] at heval
  simpa [TerminalTorusVelocityTrace.euclideanTrace] using heval

section Audit

#print axioms terminalApproachTime_tendsto
#print axioms closedTailPreterminalTimes_dense
#print axioms terminalApproachClosedPreterminalTime_tendsto
#print axioms UniformTorusVelocityTailControl.tendsto_fullTailTrace
#print axioms UniformTorusVelocityTailControl.tendsto_fullTailTrace_dyadic
#print axioms TerminalTorusVelocityTrace.trace_eq_fullTailTrace
#print axioms TerminalTorusVelocityTrace.tendsto_fullTail
#print axioms terminalApproachTailTime_cauchy
#print axioms UniformTorusVelocityTailControl.cauchySeq_velocitySlices
#print axioms UniformTorusVelocityTailControl.terminalTrace
#print axioms TerminalTorusVelocityTrace.continuous_euclideanTrace
#print axioms TerminalTorusVelocityTrace.isOnePeriodic_euclideanTrace
#print axioms TerminalTorusVelocityTrace.tendsto_euclideanTrace_dyadic

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalTrace
