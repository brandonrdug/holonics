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

5. **The learning covector factors through the chart** (`descended_costate`,
   `costate_null_on_release`, `descended_drive_covector`, `descended_gain`, `gain_fibre_invariant`).
   A declared comparison's costate `λ_t = λ_{t+1} T_t + c_t` (`c_t` the covectors on the admitted
   readings) is `λ̄_t V` when every tick descends and every reading factors, so it vanishes on the
   release; the drive covector is `λ̄_{t+1} (V B_t)`. A gain family's covector, the solved covector
   paired with the family's variation `φ_t x_t + H_t e_t`, descends when `φ_t = φ̄_t V`, and is then
   the same at `x₀ + k` for released `k`.
6. **The exact condition** (`released_variation_shift`, `solved_pairing_null_iff`,
   `squared_gain_variation_null`, `half_turn_separates`, `standing_pump_threshold_reads_release`,
   `learning_chart_le_kernel`). On a released pair the rate does not move, so the variation moves by
   `2δC k_w − hδK k_u` alone; every solved covector is reached by a port comparison, so a family
   factors for every admitted comparison iff its variation vanishes on the release. Capacity and
   dissipation always factor; stiffness and pump factor whenever the pump's cycle holds a
   half-turn, and fail for a standing pump at threshold, `(K₀ + ½Π)(1, 0) = 0` with `K₀ (1, 0) ≠ 0`.
   A chart through which every variation factors releases no more than the phase family's kernel
   with the variations admitted as receivers: in a learning aeon the deposit is a receiver.
7. **The descended block ticks** (`modeForm_radical`, `descended_form`, `descended_balance_terms`,
   `descended_balance`). The released pair lies in the radical of the mode form, so a form whose
   radical holds the release is `S x x = S̄(Vx, Vx)` with `S̄ = S(σ ·, σ ·)` for a section `σ`; the
   descended tick's storage before and after, pump re-basing and returned wave are the full ring's
   on every state, and the full balance on every state gives the descended balance on every
   retained state.

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

/-! ## 5. The learning covector factors through the chart -/

section Covector

variable {K : Type*} [Field K] {X Q E F : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- [definition] **The costate of a tick-indexed linear system**, `m` ticks remaining from tick
`t`: the declared comparison's covector read at tick `t` through the admitted readings, `c t`
(`Σ_r ȳ_(r,t) ∘ ρ_(r,t)`), carried backward through the ticks,
`λ_(m+1, t) = λ_(m, t+1) ∘ T_t + c_t`, and `λ_(0, t) = 0`: the word-local state is dropped at the
word's end. -/
def costate (T : ℕ → X →ₗ[K] X) (c : ℕ → X →ₗ[K] K) : ℕ → ℕ → X →ₗ[K] K
  | 0, _ => 0
  | m + 1, t => costate T c m (t + 1) ∘ₗ T t + c t

/-- [proved-derived; formal-checked] **The costate lies in the chart's row space.** If every tick
descends (`V T_t = T̄_t V`) and every admitted reading factors (`c_t = c̄_t V`), the costate is the
descended costate read through the chart, `λ_t = λ̄_t V`: it vanishes on the released kernel and
runs on the quotient. -/
theorem descended_costate (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (c : ℕ → X →ₗ[K] K) (c' : ℕ → Q →ₗ[K] K) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V)
    (hc : ∀ t, c t = c' t ∘ₗ V) (m t : ℕ) :
    costate T c m t = costate T' c' m t ∘ₗ V := by
  induction m generalizing t with
  | zero => ext x; simp [costate]
  | succ m ih =>
    ext x
    simp only [costate, LinearMap.add_apply, LinearMap.comp_apply]
    rw [ih, hc]
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply V (T t), hsq, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] The costate vanishes on the released kernel. -/
theorem costate_null_on_release (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (c : ℕ → X →ₗ[K] K) (c' : ℕ → Q →ₗ[K] K) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V)
    (hc : ∀ t, c t = c' t ∘ₗ V) {k : X} (hk : V k = 0) (m t : ℕ) : costate T c m t k = 0 := by
  rw [descended_costate V T T' c c' hsq hc, LinearMap.comp_apply, hk, map_zero]

/-- [proved-derived; formal-checked] **The drive covector descends**: `λ_(t+1) B_t = λ̄_(t+1) B̄_t`
with `B̄_t = V B_t`. -/
theorem descended_drive_covector (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (c : ℕ → X →ₗ[K] K) (c' : ℕ → Q →ₗ[K] K) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V)
    (hc : ∀ t, c t = c' t ∘ₗ V) (B : E →ₗ[K] X) (m t : ℕ) :
    costate T c m t ∘ₗ B = costate T' c' m t ∘ₗ (V ∘ₗ B) := by
  rw [descended_costate V T T' c c' hsq hc, LinearMap.comp_assoc]

/-- [definition] **A gain family's covector** over `N` ticks of a declared comparison: at each tick
the solved covector `a_t = r̄_t` pairs the family's material variation, a linear reading of the
tick's state and drive, `φ_t x_t + H_t e_t` (Decision 38:
`2δC(w − ω) − hδD ω − hδK_t(u + hω/2)` along `δ = 2g·base`, with `ω` read from the port). -/
def gainCovector (a : ℕ → F →ₗ[K] K) (φ : ℕ → X →ₗ[K] F) (H : ℕ → E →ₗ[K] F)
    (T : ℕ → X →ₗ[K] X) (B : ℕ → E →ₗ[K] X) (e : ℕ → E) (x₀ : X) (N : ℕ) : K :=
  ∑ t ∈ Finset.range N, a t (φ t (run T B e x₀ t) + H t (e t))

/-- [proved-derived; formal-checked] **The gain covector descends** when the family's variation
reads the state through the chart, `φ_t = φ̄_t V`: it is the same pairing on the descended run. -/
theorem descended_gain (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (B : ℕ → E →ₗ[K] X) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V) (φ : ℕ → X →ₗ[K] F)
    (φ' : ℕ → Q →ₗ[K] F) (hφ : ∀ t, φ t = φ' t ∘ₗ V) (a : ℕ → F →ₗ[K] K)
    (H : ℕ → E →ₗ[K] F) (e : ℕ → E) (x₀ : X) (N : ℕ) :
    gainCovector a φ H T B e x₀ N =
      gainCovector a φ' H T' (fun t => V ∘ₗ B t) e (V x₀) N := by
  unfold gainCovector
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hφ, LinearMap.comp_apply, descended_run V T T' B hsq]

/-- [proved-derived; formal-checked] **The gain covector is constant on the fibre**: at `x₀ + k`,
`k` released, it equals its value at `x₀`. -/
theorem gain_fibre_invariant (V : X →ₗ[K] Q) (T : ℕ → X →ₗ[K] X) (T' : ℕ → Q →ₗ[K] Q)
    (B : ℕ → E →ₗ[K] X) (hsq : ∀ t, V ∘ₗ T t = T' t ∘ₗ V) (φ : ℕ → X →ₗ[K] F)
    (φ' : ℕ → Q →ₗ[K] F) (hφ : ∀ t, φ t = φ' t ∘ₗ V) (a : ℕ → F →ₗ[K] K)
    (H : ℕ → E →ₗ[K] F) (e : ℕ → E) (x₀ : X) {k : X} (hk : V k = 0) (N : ℕ) :
    gainCovector a φ H T B e (x₀ + k) N = gainCovector a φ H T B e x₀ N := by
  rw [descended_gain V T T' B hsq φ φ' hφ, descended_gain V T T' B hsq φ φ' hφ, map_add, hk,
    add_zero]

/-- [proved-derived; formal-checked] **On a released pair the variation moves by its storage
part.** The rate is unchanged on a released pair (it moves no rate at any phase), so the material
variation at `(u + k_u, w + k_w)` differs from that at `(u, w)` by `2δC k_w − hδK k_u` alone; the
dissipation's `δD ω` does not move. -/
theorem released_variation_shift (dC dD dK : F →ₗ[K] F) (h : K) (u w ω ku kw : F) :
    ((2 : K) • dC ((w + kw) - ω) - h • dD ω - h • dK ((u + ku) + (h / 2) • ω)) -
        ((2 : K) • dC (w - ω) - h • dD ω - h • dK (u + (h / 2) • ω)) =
      (2 : K) • dC kw - h • dK ku := by
  simp only [map_add, map_sub, smul_add, smul_sub]
  abel

/-- [proved-derived; formal-checked] **Every solved covector is reached by a port comparison**, so
the condition below is exact. The solved covector obeys `r̄ M = λ′J − (2/Y)s̄` (`J ω = (hω, 2ω)`,
the port's `s′ = e − (2/Y)ω`): with `M` invertible, a family's pairing `r̄(φ k)` vanishes for every
port covector `s̄` exactly when `φ k = 0`. -/
theorem solved_pairing_null_iff [CharZero K] (M : F ≃ₗ[K] F) (J : F →ₗ[K] X) (lam : X →ₗ[K] K)
    {Y : K} (hY : Y ≠ 0) (v : F) :
    (∀ s : F →ₗ[K] K, ((lam ∘ₗ J - (2 / Y) • s) ∘ₗ (M.symm : F →ₗ[K] F)) v = 0) ↔ v = 0 := by
  constructor
  · intro hs
    refine (Module.forall_dual_apply_eq_zero_iff K v).mp fun a => ?_
    have hreach := hs ((Y / 2) • (lam ∘ₗ J - a ∘ₗ (M : F →ₗ[K] F)))
    have hc : (2 / Y) * (Y / 2) = (1 : K) := by field_simp
    rw [smul_smul, hc, one_smul, sub_sub_cancel, LinearMap.comp_assoc] at hreach
    simpa using hreach
  · rintro rfl s
    exact map_zero _

/-- [proved-derived; formal-checked] **A squared gain's variation reads nothing its form does not**:
with `g ≠ 0`, `(g² A₀) v = 0` gives `(2g A₀) v = 0`. The capacity family factors on every released
pair (`C k_w = 0`); the dissipation family factors because the released rate is zero. -/
theorem squared_gain_variation_null {g : K} (hg : g ≠ 0) (A₀ : F →ₗ[K] F) {v : F}
    (hv : (g ^ 2 • A₀) v = 0) : ((2 * g) • A₀) v = 0 := by
  rw [LinearMap.smul_apply] at hv ⊢
  rw [(smul_eq_zero.mp hv).resolve_left (pow_ne_zero 2 hg), smul_zero]

/-- [proved-derived; formal-checked] **A half-turn in the pump's cycle separates stiffness from
pump.** A released displacement lies in `ker K_t` at every phase; if the cycle holds the phases
`ψ` and `ψ + π` (every quarter-turn pump of order `2` or `4`), `K_t = aK₀ ± bΠ`, and with `a, b ≠ 0`
it lies in `ker K₀ ∩ ker Π`: the stiffness and pump families factor. -/
theorem half_turn_separates [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (K₀ P₀ : F →ₗ[K] F)
    {u : F} (h₀ : a • K₀ u + b • P₀ u = 0) (h₁ : a • K₀ u - b • P₀ u = 0) :
    K₀ u = 0 ∧ P₀ u = 0 := by
  have hsum : ((2 : K) * a) • K₀ u = 0 := by
    have h := congrArg₂ (· + ·) h₀ h₁
    simp only [add_zero] at h
    rw [← h, mul_smul, two_smul]
    abel
  have hK : K₀ u = 0 :=
    (smul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero ha)
  refine ⟨hK, ?_⟩
  rw [hK, smul_zero, zero_add] at h₀
  exact (smul_eq_zero.mp h₀).resolve_left hb

end Covector

/-- [counterexample; formal-checked] **A standing pump at threshold reads a released direction.**
One node, `K₀ = 1`, a standing pump (`P = 1`) of base block `Π = diag(−2, 2)` and strength `½`:
`K_0 = K₀ + ½Π = diag(0, 2)`, so the displacement `(1, 0)` moves no rate and is released, but
`K₀ (1, 0) ≠ 0` and `Π (1, 0) ≠ 0`: the stiffness and pump families read it, and a learning aeon
retains it. The joint scaling `g_K ∂_(g_K) + g_P ∂_(g_P)` pairs `2K_0 u = 0` and factors. -/
theorem standing_pump_threshold_reads_release :
    let u : Fin 2 → ℚ := ![1, 0]
    let P₀ : Matrix (Fin 2) (Fin 2) ℚ := Matrix.diagonal ![-2, 2]
    Matrix.mulVec ((1 : Matrix (Fin 2) (Fin 2) ℚ) + (1 / 2 : ℚ) • P₀) u = 0 ∧
      Matrix.mulVec (1 : Matrix (Fin 2) (Fin 2) ℚ) u ≠ 0 ∧ Matrix.mulVec P₀ u ≠ 0 := by
  intro u P₀
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [u, P₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.one_apply, Matrix.diagonal_apply]
  · intro h
    have := congrFun h 0
    simp [u] at this
  · intro h
    have := congrFun h 0
    simp [u, P₀, Matrix.mulVec, dotProduct, Matrix.diagonal_apply] at this

section Learning

variable {K : Type*} [Field K] {X V R G : Type} [AddCommGroup X] [Module K X]
  [AddCommGroup V] [Module K V]

/-- [proved-derived; formal-checked] **In a learning aeon the deposit is a receiver.** A chart
through which every tick descends, every admitted reading factors and every gain family's variation
factors releases no more than the phase family's kernel with the variations `φ_(f,t)` admitted
beside the readings (`shared_chart_le_phase_kernel` on the receivers `R ⊕ G`). A released direction
that a variation reads is retained, with the reading that separates it. -/
theorem learning_chart_le_kernel (T : ℕ → X →ₗ[K] X) (ρ : R → ℕ → X →ₗ[K] V)
    (φ : G → ℕ → X →ₗ[K] V) (P : ℕ) {Q : Type} [AddCommGroup Q] [Module K Q]
    (retain : X →ₗ[K] Q) (T' : Fin P → Q →ₗ[K] Q) (ρ' : R × Fin P → Q →ₗ[K] V)
    (φ' : G × Fin P → Q →ₗ[K] V)
    (hsq : ∀ i, retain ∘ₗ phaseTransport T P i = T' i ∘ₗ retain)
    (hread : ∀ ri, phaseRead ρ P ri = ρ' ri ∘ₗ retain)
    (hvar : ∀ gi, phaseRead φ P gi = φ' gi ∘ₗ retain) :
    LinearMap.ker retain ≤
      LinearMap.ker (faceMap (phaseRead (fun s : R ⊕ G => Sum.elim ρ φ s) P)
        (phaseTransport T P)) :=
  shared_chart_le_phase_kernel T (fun s : R ⊕ G => Sum.elim ρ φ s) P retain T'
    (fun si => Sum.elim (fun r => ρ' (r, si.2)) (fun g => φ' (g, si.2)) si.1) hsq
    (fun ⟨s, i⟩ => by cases s with
      | inl r => exact hread (r, i)
      | inr g => exact hvar (g, i))

end Learning

/-! ## 6. The descended block ticks, with its storage and its balance -/

section DescendedBalance

variable {K : Type*} [Field K] {X Q E W : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [AddCommGroup W] [Module K W]

/-- [proved-derived; formal-checked] **The released pair lies in the storage form's radical.** For
`β`-symmetric `K_t`, `C`, the mode form `β(x_u, K_t y_u) + β(x_w, C y_w)` vanishes against every
pair with `K_t k_u = 0`, `C k_w = 0` (`released_pair_storage_null`), on either side. -/
theorem modeForm_radical (β : E →ₗ[K] E →ₗ[K] K) (Kt C : E →ₗ[K] E)
    (hK : ∀ a b, β (Kt a) b = β a (Kt b)) (hC : ∀ a b, β (C a) b = β a (C b)) {ku kw : E}
    (hku : Kt ku = 0) (hkw : C kw = 0) (yu yw : E) :
    β ku (Kt yu) + β kw (C yw) = 0 ∧ β yu (Kt ku) + β yw (C kw) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← hK, ← hC, hku, hkw]
    simp
  · rw [hku, hkw]
    simp

/-- [proved-derived; formal-checked] **A form whose radical holds the release descends**: with a
section `σ` of the chart (`V σ = 1`), `S x x = S̄(Vx, Vx)` for `S̄ = S(σ ·, σ ·)`, whatever the
lift. -/
theorem descended_form (V : X →ₗ[K] Q) (σ : Q →ₗ[K] X) (hσ : V ∘ₗ σ = LinearMap.id)
    (S : X →ₗ[K] X →ₗ[K] K) (hl : ∀ k, V k = 0 → ∀ y, S k y = 0)
    (hr : ∀ k, V k = 0 → ∀ y, S y k = 0) (x : X) :
    S.compl₁₂ σ σ (V x) (V x) = S x x := by
  have hk : V (x - σ (V x)) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply V σ, hσ, LinearMap.id_apply, sub_self]
  have hx : σ (V x) + (x - σ (V x)) = x := by abel
  have key : S x x = S (σ (V x)) (σ (V x)) := by
    calc S x x = S (σ (V x) + (x - σ (V x))) (σ (V x) + (x - σ (V x))) := by rw [hx]
    _ = S (σ (V x)) (σ (V x)) := by
      simp only [map_add, LinearMap.add_apply, hl _ hk, hr _ hk, add_zero]
  rw [LinearMap.compl₁₂_apply, key]

/-- [proved-derived; formal-checked] **The descended tick's terms are the full ring's**, on every
state `x` and drive `e`: the storage before (the previous phase's form `S₀`) and after (this
phase's `S₁`), the pump's re-basing `S₁ − S₀` at the state, and the returned wave (so the rate
`ω = (Y/2)(e − s′)`, the port work and the dissipation). -/
theorem descended_balance_terms (V : X →ₗ[K] Q) (σ : Q →ₗ[K] X) (hσ : V ∘ₗ σ = LinearMap.id)
    (T : X →ₗ[K] X) (T' : Q →ₗ[K] Q) (B : E →ₗ[K] X) (ρ : X →ₗ[K] W) (ρ' : Q →ₗ[K] W)
    (D : E →ₗ[K] W) (hsq : V ∘ₗ T = T' ∘ₗ V) (hρ : ρ = ρ' ∘ₗ V) (S₀ S₁ : X →ₗ[K] X →ₗ[K] K)
    (h₀l : ∀ k, V k = 0 → ∀ y, S₀ k y = 0) (h₀r : ∀ k, V k = 0 → ∀ y, S₀ y k = 0)
    (h₁l : ∀ k, V k = 0 → ∀ y, S₁ k y = 0) (h₁r : ∀ k, V k = 0 → ∀ y, S₁ y k = 0)
    (x : X) (e : E) :
    V (T x + B e) = T' (V x) + V (B e) ∧
      S₁.compl₁₂ σ σ (T' (V x) + V (B e)) (T' (V x) + V (B e)) = S₁ (T x + B e) (T x + B e) ∧
      S₀.compl₁₂ σ σ (V x) (V x) = S₀ x x ∧ S₁.compl₁₂ σ σ (V x) (V x) = S₁ x x ∧
      ρ' (V x) + D e = ρ x + D e := by
  have hstep : V (T x + B e) = T' (V x) + V (B e) := by
    rw [map_add, ← LinearMap.comp_apply V T, hsq, LinearMap.comp_apply]
  refine ⟨hstep, ?_, descended_form V σ hσ S₀ h₀l h₀r x, descended_form V σ hσ S₁ h₁l h₁r x, ?_⟩
  · rw [← hstep, descended_form V σ hσ S₁ h₁l h₁r]
  · rw [hρ, LinearMap.comp_apply]

/-- [proved-derived; formal-checked] **The descended block's balance.** If the full ring's tick
balances on every state, `S₁(x′) − S₀(x) = (S₁ − S₀)(x) + work(e, s′)` (storage after, before, the
pump's work at the state, and the port work less dissipation, a function of the drive and the
returned wave), then the descended tick `q′ = T̄q + V B e`, `s′ = ρ̄q + D e` balances on every
retained state with the descended forms `S̄ = S(σ ·, σ ·)`, term for term. -/
theorem descended_balance (V : X →ₗ[K] Q) (σ : Q →ₗ[K] X) (hσ : V ∘ₗ σ = LinearMap.id)
    (T : X →ₗ[K] X) (T' : Q →ₗ[K] Q) (B : E →ₗ[K] X) (ρ : X →ₗ[K] W) (ρ' : Q →ₗ[K] W)
    (D : E →ₗ[K] W) (hsq : V ∘ₗ T = T' ∘ₗ V) (hρ : ρ = ρ' ∘ₗ V) (S₀ S₁ : X →ₗ[K] X →ₗ[K] K)
    (h₀l : ∀ k, V k = 0 → ∀ y, S₀ k y = 0) (h₀r : ∀ k, V k = 0 → ∀ y, S₀ y k = 0)
    (h₁l : ∀ k, V k = 0 → ∀ y, S₁ k y = 0) (h₁r : ∀ k, V k = 0 → ∀ y, S₁ y k = 0)
    (work : E → W → K)
    (hfull : ∀ x e, S₁ (T x + B e) (T x + B e) - S₀ x x = (S₁ x x - S₀ x x) + work e (ρ x + D e))
    (q : Q) (e : E) :
    S₁.compl₁₂ σ σ (T' q + V (B e)) (T' q + V (B e)) - S₀.compl₁₂ σ σ q q =
      (S₁.compl₁₂ σ σ q q - S₀.compl₁₂ σ σ q q) + work e (ρ' q + D e) := by
  have hq : V (σ q) = q := by rw [← LinearMap.comp_apply V σ, hσ, LinearMap.id_apply]
  obtain ⟨_, hafter, hbefore, hnow, hwave⟩ :=
    descended_balance_terms V σ hσ T T' B ρ ρ' D hsq hρ S₀ S₁ h₀l h₀r h₁l h₁r (σ q) e
  rw [hq] at hafter hbefore hnow hwave
  rw [hafter, hbefore, hnow, hwave]
  exact hfull (σ q) e

end DescendedBalance

section Audit

#print axioms periodic_lift_exact
#print axioms phase_kernel_le_lift
#print axioms shared_chart_le_phase_kernel
#print axioms descended_run_reads
#print axioms released_pair_storage_null
#print axioms descended_costate
#print axioms descended_drive_covector
#print axioms gain_fibre_invariant
#print axioms released_variation_shift
#print axioms solved_pairing_null_iff
#print axioms squared_gain_variation_null
#print axioms half_turn_separates
#print axioms standing_pump_threshold_reads_release
#print axioms learning_chart_le_kernel
#print axioms modeForm_radical
#print axioms descended_balance_terms
#print axioms descended_balance

end Audit

end Holonics.HNN.ModeQuotient
