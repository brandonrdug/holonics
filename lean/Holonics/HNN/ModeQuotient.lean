import Holonics.Compression.Core.FaceMap

/-!
# HNN.ModeQuotient: a loaded ring's modes descend to their future quotient

[definition] Campaign 3, first construction (#73; `docs/plans/THE_REBUILD.md`, "Campaign 3"). A
loaded ring at a fixed publication (Decision 38, `HNN/Ring`) ticks, under the exact law, as one
linear system per pump phase: its word-local state `x = (u, w)` moves by `x′ = T_t x + B_t e` and
returns `s′ = ρ_t x + D_t e`, the phase `t mod P`. The Rust owner is `holonics::hnn::modes`.

[proved-derived; formal-checked] What is proved.

1. **The admitted words are the pump's cycle, and the period lift reads them exactly**
   (`periodic_lift_exact`). With `Φ 0 = 1`, `Φ (t+1) = T_t Φ t` and `P`-periodic `T` and `ρ`,
   `Φ (mP + k) = Φ k (Φ P)^m` (`cycle_mul_add`), so the admitted reading of receiver `r` at tick
   `t = mP + k` is the face `ρ_{r,k} Φ k` after `m` letters of the single period navigator `Φ P`.
   A state is silent to every admitted reading exactly when it lies in the kernel of the face map
   of the lift (`Compression/Core/FaceMap.faceMap` with navigator `Φ P` and phase-offset receivers
   `ρ_{r,k} Φ k`, `k < P`). Arbitrary words of the phase family are not admitted: their kernel is
   the smaller one of item 2.
2. **One chart for every phase releases less** (`phase_kernel_le_cycle`). The face map of the
   phase family (navigators `T_i`, `i < P`, every word; receivers `ρ_{r,i}`) has its kernel inside
   the admitted kernel, since every admitted reading is one of its readings after the cycle's word
   `[t−1 mod P, …, 0]` (`wordMap_cycleWord`). Its kernel is the largest subspace carried by every
   `T_i` and read by no `ρ_{r,i}` (`FaceMap.ker_faceMap_invariant`), and the kernel of any chart
   `V` that closes every square `V T_i = T̄_i V`, `ρ_{r,i} = ρ̄_{r,i} V` lies in it
   (`shared_chart_le_phase_kernel`): it is the largest release one chart can make.
3. **The descended ring runs** (`descended_run`, `descended_run_reads`). If `V T_t = T̄_t V` and
   `ρ_t = ρ̄_t V` at every tick, the descended run `q′ = T̄_t q + (V B_t) e` from `V x₀` stays the
   chart of the full run, `V x_t = q_t`, and returns the same wave `ρ̄_t q_t + D_t e_t = ρ_t x_t +
   D_t e_t` for every drive sequence.
4. **The released part stores nothing** (`released_pair_storage_null`). A state `(u, w)` silent at
   the loaded port has a zero rate (`s′ = −(2/Y)ω` at zero drive), so its tick is `(u, −w)`; if
   that is silent at the same phase too, `2Cw = hK_t u` and `−2Cw = hK_t u`, hence `Cw = 0` and
   `K_t u = 0`. A release that closes every square with the port admitted is carried by every tick
   and silent at every phase, so it lies in `ker K_t × ker C` at every phase: the storage form
   `Q_t = diag(K_t, C)` annihilates it, the split is `Q_t`-orthogonal for every complement, and the
   storage descends.

The present receiver is admitted, so `ker F_future ⊆ ker F_now` (`Holarchy/Hearing`,
`HearingLaw.futureNull_le_ker_present`); the navigator runs on retention by
`FaceMap.kernelClass_after_word`, and every future face factors by `FaceMap.kernelReceiverQuotient`.
-/

namespace Holonics.HNN.ModeQuotient

open Holonics.Compression.Core.FaceMap

/-! ## 1. The pump's cycle and its period lift -/

section Cycle

/-- [definition] A function of the tick with period `P`. -/
def Periodic (P : ℕ) {α : Type*} (f : ℕ → α) : Prop := ∀ t, f (t + P) = f t

theorem Periodic.mul_add {P : ℕ} {α : Type*} {f : ℕ → α} (hf : Periodic P f) (m k : ℕ) :
    f (m * P + k) = f k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, Nat.add_right_comm, hf, ih]

theorem Periodic.mod {P : ℕ} {α : Type*} {f : ℕ → α} (hf : Periodic P f) (t : ℕ) :
    f (t % P) = f t := by
  conv_rhs => rw [← Nat.div_add_mod' t P]
  exact (hf.mul_add _ _).symm

variable {K : Type*} [Field K] {X V R : Type} [AddCommGroup X] [Module K X]
  [AddCommGroup V] [Module K V]

/-- [definition] **The pump cycle's transport from phase `0`**: `Φ 0 = 1`, `Φ (t+1) = T_t Φ t`. -/
def cycle (T : ℕ → X →ₗ[K] X) : ℕ → X →ₗ[K] X
  | 0 => LinearMap.id
  | t + 1 => T t ∘ₗ cycle T t

theorem cycle_add_period {T : ℕ → X →ₗ[K] X} {P : ℕ} (hT : Periodic P T) (t : ℕ) :
    cycle T (t + P) = cycle T t ∘ₗ cycle T P := by
  induction t with
  | zero => simp [cycle]
  | succ t ih =>
    rw [Nat.add_right_comm]
    simp only [cycle, ih, hT t, LinearMap.comp_assoc]

/-- [proved-derived; formal-checked] **The cycle factors through its period**:
`Φ (mP + k) = Φ k (Φ P)^m`. -/
theorem cycle_mul_add {T : ℕ → X →ₗ[K] X} {P : ℕ} (hT : Periodic P T) (m k : ℕ) :
    cycle T (m * P + k) = cycle T k ∘ₗ cycle T P ^ m := by
  induction m with
  | zero => simp [Module.End.one_eq_id]
  | succ m ih =>
    rw [Nat.succ_mul, Nat.add_right_comm, cycle_add_period hT, ih, pow_succ,
      Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- A word of the single period navigator is its power. -/
theorem wordMap_const (A : X →ₗ[K] X) (w : List Unit) :
    wordMap (fun _ : Unit => A) w = A ^ w.length := by
  induction w with
  | nil => simp [wordMap, Module.End.one_eq_id]
  | cons g w ih => rw [wordMap, ih, List.length_cons, pow_succ', Module.End.mul_eq_comp]

theorem faceMap_apply' {Navigator Receiver : Type} (read : Receiver → X →ₗ[K] V)
    (transport : Navigator → X →ₗ[K] X) (x : X) (request : Receiver × List Navigator) :
    faceMap read transport x request = read request.1 (wordMap transport request.2 x) := rfl

variable (T : ℕ → X →ₗ[K] X) (ρ : R → ℕ → X →ₗ[K] V) (P : ℕ)

/-- [definition] **The phase-offset receivers of the lift**: receiver `r` at phase `k < P` reads
after the cycle's first `k` ticks. -/
def liftedRead : R × Fin P → X →ₗ[K] V := fun rk => ρ rk.1 rk.2 ∘ₗ cycle T rk.2

/-- [proved-derived; formal-checked] **The period lift is exact.** A state is silent to every
admitted reading of the pump's cycle (receiver `r` at every tick `t`, at phase `t mod P`) exactly
when it lies in the kernel of the face map of the single period navigator `Φ P` read by the
phase-offset receivers `ρ_{r,k} Φ k`. -/
theorem periodic_lift_exact (hT : Periodic P T) (hρ : ∀ r, Periodic P (ρ r)) (hP : 0 < P)
    (x : X) :
    (∀ r t, ρ r t (cycle T t x) = 0) ↔
      x ∈ LinearMap.ker (faceMap (liftedRead T ρ P) (fun _ : Unit => cycle T P)) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    funext request
    obtain ⟨⟨r, k⟩, w⟩ := request
    rw [faceMap_apply', wordMap_const]
    have hread := h r (w.length * P + k)
    rw [cycle_mul_add hT, (hρ r).mul_add] at hread
    simpa [liftedRead] using hread
  · intro h r t
    have hread := congrFun h (⟨r, ⟨t % P, Nat.mod_lt t hP⟩⟩, List.replicate (t / P) ())
    rw [faceMap_apply', wordMap_const, List.length_replicate] at hread
    have hcycle := cycle_mul_add hT (t / P) (t % P)
    rw [Nat.div_add_mod'] at hcycle
    simp only [liftedRead, LinearMap.comp_apply, Pi.zero_apply] at hread
    rw [hcycle, LinearMap.comp_apply, ← (hρ r).mod]
    exact hread

/-! ## 2. One chart for every phase -/

/-- [definition] The phase family's receivers: receiver `r` at phase `i < P`. -/
def phaseRead : R × Fin P → X →ₗ[K] V := fun ri => ρ ri.1 ri.2

/-- [definition] The phase family's navigators: the tick at phase `i < P`. -/
def phaseTransport : Fin P → X →ₗ[K] X := fun i => T i

/-- [definition] **The cycle's word in the phase family**: `[t−1 mod P, …, 1, 0]`, its last letter
acting first. -/
def cycleWord (hP : 0 < P) : ℕ → List (Fin P)
  | 0 => []
  | t + 1 => ⟨t % P, Nat.mod_lt t hP⟩ :: cycleWord hP t

theorem wordMap_cycleWord (hT : Periodic P T) (hP : 0 < P) (t : ℕ) :
    wordMap (phaseTransport T P) (cycleWord P hP t) = cycle T t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [cycleWord, wordMap, ih, phaseTransport, hT.mod, cycle]

/-- [proved-derived; formal-checked] **One chart for every phase releases no more than the cycle
admits**: the phase family's kernel (every word, every phase's receivers) is silent to every
admitted reading. -/
theorem phase_kernel_le_cycle (hT : Periodic P T) (hρ : ∀ r, Periodic P (ρ r)) (hP : 0 < P)
    {x : X} (hx : x ∈ LinearMap.ker (faceMap (phaseRead ρ P) (phaseTransport T P))) (r : R)
    (t : ℕ) : ρ r t (cycle T t x) = 0 := by
  rw [LinearMap.mem_ker] at hx
  have hread := congrFun hx (⟨r, ⟨t % P, Nat.mod_lt t hP⟩⟩, cycleWord P hP t)
  rw [faceMap_apply', wordMap_cycleWord T P hT hP] at hread
  simpa [phaseRead, (hρ r).mod] using hread

/-- [proved-derived; formal-checked] **A chart shared by every phase releases no more than the
phase family's kernel**: if the chart `V` closes `V T_i = T̄_i V` at every phase and every reading
factors through it, then `ker V` is silent to every reading after every word. -/
theorem shared_chart_le_phase_kernel {Q : Type} [AddCommGroup Q] [Module K Q]
    (retain : X →ₗ[K] Q) (T' : Fin P → Q →ₗ[K] Q) (ρ' : R × Fin P → Q →ₗ[K] V)
    (hsq : ∀ i, retain ∘ₗ phaseTransport T P i = T' i ∘ₗ retain)
    (hread : ∀ ri, phaseRead ρ P ri = ρ' ri ∘ₗ retain) :
    LinearMap.ker retain ≤ LinearMap.ker (faceMap (phaseRead ρ P) (phaseTransport T P)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have carried : ∀ w, retain (wordMap (phaseTransport T P) w x) = 0 := by
    intro w
    induction w with
    | nil => exact hx
    | cons i w ih =>
      rw [wordMap, LinearMap.comp_apply, ← LinearMap.comp_apply retain, hsq,
        LinearMap.comp_apply, ih, map_zero]
  funext request
  rw [faceMap_apply', hread, LinearMap.comp_apply, carried, map_zero]
  rfl

/-- [proved-derived; formal-checked] The phase family's kernel lies in the lift's. -/
theorem phase_kernel_le_lift (hT : Periodic P T) (hρ : ∀ r, Periodic P (ρ r)) (hP : 0 < P) :
    LinearMap.ker (faceMap (phaseRead ρ P) (phaseTransport T P)) ≤
      LinearMap.ker (faceMap (liftedRead T ρ P) (fun _ : Unit => cycle T P)) := fun _ hx =>
  (periodic_lift_exact T ρ P hT hρ hP _).mp (phase_kernel_le_cycle T ρ P hT hρ hP hx)

end Cycle

/-! ## 3. The descended ring runs -/

section Descent

variable {K : Type*} [Field K] {X Q E W : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [AddCommGroup W] [Module K W]

/-- [definition] **The driven run** of a tick-indexed linear system from `x₀` on the drives `e`. -/
def run (T : ℕ → X →ₗ[K] X) (B : ℕ → E →ₗ[K] X) (e : ℕ → E) (x₀ : X) : ℕ → X
  | 0 => x₀
  | t + 1 => T t (run T B e x₀ t) + B t (e t)

/-- [proved-derived; formal-checked] **The chart carries the run**: with `V T_t = T̄_t V`, the
descended run from `V x₀` on the sources `V B_t` is the chart of the full run. -/
theorem descended_run (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (B : ℕ → E →ₗ[K] X) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V) (e : ℕ → E) (x₀ : X) (t : ℕ) :
    V (run T B e x₀ t) = run T' (fun t => V ∘ₗ B t) e (V x₀) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run, map_add, LinearMap.comp_apply, ← ih]
    rw [← LinearMap.comp_apply V (T t), hsq, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] **The descended ring returns the same wave**:
`ρ̄_t q_t + D_t e_t = ρ_t x_t + D_t e_t` at every tick, for every drive sequence. -/
theorem descended_run_reads (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (B : ℕ → E →ₗ[K] X) (ρ : ℕ → X →ₗ[K] W) (ρ' : ℕ → Q →ₗ[K] W) (D : ℕ → E →ₗ[K] W)
    (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V) (hρ : ∀ t, ρ t = ρ' t ∘ₗ V) (e : ℕ → E) (x₀ : X)
    (t : ℕ) :
    ρ' t (run T' (fun t => V ∘ₗ B t) e (V x₀) t) + D t (e t) =
      ρ t (run T B e x₀ t) + D t (e t) := by
  rw [← descended_run V T T' B hsq, hρ, LinearMap.comp_apply]

end Descent

/-! ## 4. The released part stores nothing -/

section StorageNull

variable {𝕜 E : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- [proved-derived; formal-checked] **A pair silent at the loaded port on its state and on its
tick stores nothing** (the solve and the returned wave of `HNN/Ring.{ringRight, ringOut}` at zero
drive). If the port returns no wave for `(u, w)`, its rate `ω` is zero and its tick is
`(u + hω, 2ω − w)`; if the port returns none for that too, `Cw = 0` and `K u = 0`. -/
theorem released_pair_storage_null (M C K : E →ₗ[𝕜] E) {h Y : 𝕜} (hh : h ≠ 0) (hY : Y ≠ 0)
    {u w ω ω' : E}
    (solve : M ω = (2 : 𝕜) • C w - h • K u)
    (silent : -((2 : 𝕜) / Y) • ω = 0)
    (solve' : M ω' = (2 : 𝕜) • C ((2 : 𝕜) • ω - w) - h • K (u + h • ω))
    (silent' : -((2 : 𝕜) / Y) • ω' = 0) :
    C w = 0 ∧ K u = 0 := by
  have hport : -((2 : 𝕜) / Y) ≠ 0 := neg_ne_zero.mpr (div_ne_zero two_ne_zero hY)
  have hω : ω = 0 := (smul_eq_zero.mp silent).resolve_left hport
  have hω' : ω' = 0 := (smul_eq_zero.mp silent').resolve_left hport
  subst hω hω'
  simp only [map_zero, smul_zero, zero_sub, add_zero, map_neg, smul_neg] at solve solve'
  -- `0 = 2Cw − hKu` and `0 = −2Cw − hKu`.
  have hsum : ((2 : 𝕜) + 2) • C w = 0 := by
    rw [add_smul]
    have := congrArg₂ (· - ·) solve solve'
    simp only [sub_self] at this
    rw [this]
    abel
  have hC : C w = 0 := (smul_eq_zero.mp hsum).resolve_left (by norm_num)
  refine ⟨hC, ?_⟩
  rw [hC, smul_zero, zero_sub] at solve
  have hK : h • K u = 0 := neg_eq_zero.mp solve.symm
  exact (smul_eq_zero.mp hK).resolve_left hh

end StorageNull

section Audit

#print axioms periodic_lift_exact
#print axioms phase_kernel_le_lift
#print axioms shared_chart_le_phase_kernel
#print axioms descended_run_reads
#print axioms released_pair_storage_null

end Audit

end Holonics.HNN.ModeQuotient
