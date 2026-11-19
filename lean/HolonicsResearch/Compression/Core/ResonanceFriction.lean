import Holonics.Compression.Core.Resonance

/-!
# Friction in the resonance/emanation split: holding a mode costs its dissipated power

[proved-derived; formal-checked] The source is #410's box "the dissipative (friction) part of the
resonance/emanation split, beyond the conservative split of `Compression/Core/Resonance`".
Resonance's opening paragraph splits a drive `d = r + e` against a constitution `(K, C)` with no
dissipation: `r ∈ ker(K − ω²C)` resonates (RIDE) and `e ⟂_C ker(K − ω²C)` emanates (FOUND). Its atlas
rows `compression.resonate-emanate` and `compression.found-effort-work` carry the scope "no
dissipation". The constitution row of the elementary objects names the third relation,
`dissipation D ⪰ 0, power ⟨Jv, D Jv⟩`, and the Holon's motion law
`d/dτ E_Θ = −dissipation + port power + …` (ELEMENTARY_OBJECTS, the Holon as one object). This
module adds `D` in Resonance's chart: `Node → ℝ`, the owners' `diagonalStorage`,
`diagonalResponse`, `storageForm`, `modeEnergy`, `motionEnergy`, `portPower` and `holdingEffort`, with
the dissipation `D = BᵀW_D B` the response of branch conductances `W_D` on the same incidence, so
its storage `S_D(v) = ½⟨v, D v⟩` is Rayleigh's dissipation function and `⟨D ẋ, ẋ⟩ = 2 S_D(ẋ)`.

Atlas rows served: `compression.resonate-emanate`, `compression.found-effort-work`,
`compression.held-motion-balance`, `compression.ride-free`, `compression.motion-energy-balance`
(each lifted past "no dissipation"), `floor.ride-found` ("sustained at minimal work"),
`pair.dissipative-face-force`, `learn.dissipation-not-loss`, `motion.port-hamiltonian-turn-boost`
and `store.finite-quality`; ELEMENTARY_OBJECTS "Holding a dormant key is free only when its ring is
lossless. A mode held against dissipation costs its pump work every tick" (under the egg).

What is proved.

1. [proved-standard; formal-checked] **The dissipation form.** Nonnegative conductances give
   `S_D ⪰ 0` (`storage_nonneg_of_weight_nonneg`), and for any `S_D ⪰ 0` a state of zero dissipation
   storage has zero dissipation response: `S_D(d) = 0 ⇔ D d = 0`
   (`response_eq_zero_of_storage_eq_zero`, `storage_eq_zero_iff_response`).
2. [proved-standard; formal-checked] **The damped energy balance.** For every twice-differentiable
   motion `x`, Resonance's stored energy `E = S_C(ẋ) + S_K(x)` changes at the port power less the
   dissipated power, `dE/dt = ⟨C ẍ + D ẋ + K x, ẋ⟩ − ⟨D ẋ, ẋ⟩` (`hasDerivAt_motionEnergy_damped`,
   with `dampedPortPower_eq`), so over `[0, t]` the port work is the change of stored energy plus the
   dissipated energy (`damped_motion_work_ledger`). A free motion (`C ẍ + D ẋ + K x = 0`) rings
   down: `dE/dt = −2 S_D(ẋ) ≤ 0` and `E` is antitone (`free_motion_rings_down`), losing over `[0, t]`
   the dissipated energy (`free_motion_ledger`).
3. [proved-derived; formal-checked] **Holding a motion against friction.** To hold
   `x(t) = cos(ωt) d` the effort is `f(t) = cos(ωt)(K − ω²C) d − ω sin(ωt) D d`
   (`dampedHoldingEffort_newton`). The in-phase part is Resonance's `holdingEffort` and sees only the
   emanating part; the quadrature part `frictionEffort` sees the whole drive, resonating part
   included (`dampedHoldingEffort_split`). **RIDE is no longer free:** for `d` in the mode space at
   `ω² ≠ 0` the holding effort is the quadrature term alone, and it vanishes at every time when and
   only when `D d = 0` (`ride_against_friction`), that is when and only when `S_D(d) = 0`
   (`ride_needs_effort_iff`). The held power is the port power of item 2 on the held motion
   (`dampedHeldPower_eq_portPower`).
4. [proved-derived; formal-checked] **The work ledger with friction.** The held power is
   Resonance's reactive power plus the dissipated power `ω² sin²(ωs)·2 S_D(d)` (`dampedHeldPower_eq`,
   `dissipatedPower_held`). For `d = r + e` the work over `[0, t]` is Resonance's
   `sin²(ωt)·(ω² S_C(e) − S_K(e))` plus `∫₀ᵗ ω² sin²(ωs)·2 S_D(r + e) ds` (`damped_work_ledger`;
   `damped_held_ledger` for any `d`), and that integral is `ω(ωt − sin(ωt) cos(ωt))·S_D(d)`
   (`heldDissipation_integral`). Over one period `2π/ω` (`ω > 0`) the reactive part returns to zero
   and the work is `2π ω S_D(d) = π ω ⟨D d, d⟩` (`damped_work_period`): the factor `2` is the
   house's `S = ½⟨·,·⟩`.
5. [proved-standard; formal-checked] **Quality.** The mean dissipated power over a period is
   `P̄ = ω² S_D(d)` (`meanDissipatedPower_eq`), and so is the mean port power (`meanPortPower_eq`):
   the reactive part averages to zero. The quality of a held mode is carried as the undivided ratio
   `(ω E, P̄)` with `E = ω² S_C(d)` its stored energy at every time (`quality`, `quality_reads`); its
   denominator is nonzero when and only when `S_D(d) > 0`, when and only when `D d ≠ 0`
   (`quality_finite_iff`), and then `Q = ω S_C(d)/S_D(d)`, which is also `E` over the energy
   dissipated per radian (`quality_quotient`). With `S_D(d) = 0` the numerator stays positive over a
   zero denominator (`quality_lossless`): the lossless ring of Resonance's RIDE.
6. [proved-derived; formal-checked] **Friction's counterpart of `clamp_witness`**
   (`friction_ride_witness`). On `Parametron.chainIncidence` the drive `(1, 1)` lies in the mode
   space at `ω = 1`, so `e = 0` and Resonance's holding effort is zero at every time; with a resistor
   from each node to ground (`groundDamping`, `D = C`) the holding effort at `t = π/2` is `−1` on
   node `0`, one period costs `2π`, and `Q = 1`. A resistor between the two nodes (`bridgeDamping`)
   carries no slip on `(1, 1)`, whose holding stays free, while it dissipates on `(1, −1)`
   (`S_D = 2`).

What is not claimed. `D` is not assumed to respect the split (no proportional damping): the
dissipated energy of `r + e` keeps its cross term `⟨D r, e⟩`, and no share of it is assigned to the
resonating or the emanating part. The held motion is held by a stated effort at a stated `ω`;
nothing is claimed of the free damped modes (the quadratic eigenproblem `(λ²C + λD + K)v = 0`, their
decay rates or their placement off the imaginary axis), of the driven steady state reached from
rest, or of a parametron's pump replacing the dissipated energy (its lock is `Objects/ParametronLock`
and `HNN/Floquet`). The quality is that of a held mode; the bandwidth reading `Q = ω₀/Δω` and the
discrete circle of `store.finite-quality` (`Physics/TwoWayField`) are not joined here. Every
statement is on real-valued motion; no width or register is declared.

The computational object is the helical pair interaction read through its dissipative relation: a
branch's drop `(Bẋ)_b` is a pair contact's slip, `S_D` is the contact material's form, the dissipated
power `⟨D ẋ, ẋ⟩ = Σ_b W_D,b (Bẋ)_b²` is the slip power of `pair.dissipative-face-force`, and the
friction effort `D ẋ` is its pullback to the nodes. Of the winding guide's six general objects this
touches the helix (the held motion is one circle per period `2π/ω`, and the ledger is read per turn
and per radian), the pair (the slip that dissipates) and faces and placement (the in-phase effort is
the reactive face, whose work returns each period, and the quadrature effort the resistive one, the
relation `motion.port-hamiltonian-turn-boost` reads as the boost); cell holonomy, the tube and the
tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Core.ResonanceFriction

open scoped BigOperators
open Holonics.Physics.HolonicComplexParametron
open Holonics.Objects.Parametron
open Holonics.Compression.Core.Resonance

variable {Node Branch : Type*} [Fintype Node] [Fintype Branch]

/-! ## 1. The dissipation form -/

section Form

/-- [proved-derived; formal-checked] Pairing a state's response with the state is twice its
storage, in the order `⟨W v, v⟩`. -/
theorem sum_response_mul_self (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (v : Node → ℝ) :
    ∑ node, diagonalResponse weight incidence v node * v node =
      2 * diagonalStorage weight incidence v := by
  rw [← sum_mul_diagonalResponse]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- [proved-standard; formal-checked] Nonnegative branch conductances give a positive
semidefinite dissipation `D = BᵀW_D B`: `S_D(v) ≥ 0`. -/
theorem storage_nonneg_of_weight_nonneg {weight : Branch → ℝ} (hw : ∀ b, 0 ≤ weight b)
    (incidence : Branch → Node → ℝ) (v : Node → ℝ) : 0 ≤ diagonalStorage weight incidence v := by
  unfold diagonalStorage
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun b _ => mul_nonneg (hw b) (sq_nonneg _))

/-- [proved-standard; formal-checked] **A semidefinite form's null states are in its kernel**: with
`S_D ⪰ 0`, `S_D(d) = 0` gives `D d = 0` at every node. -/
theorem response_eq_zero_of_storage_eq_zero {weight : Branch → ℝ} {incidence : Branch → Node → ℝ}
    (hpsd : ∀ v, 0 ≤ diagonalStorage weight incidence v) {d : Node → ℝ}
    (h0 : diagonalStorage weight incidence d = 0) (node : Node) :
    diagonalResponse weight incidence d node = 0 := by
  classical
  have hud : storageForm weight incidence (Pi.single node 1) d =
      diagonalResponse weight incidence d node := by
    rw [storageForm_eq_pairing]
    simp [Pi.single_apply]
  have hdu : storageForm weight incidence d (Pi.single node 1) =
      diagonalResponse weight incidence d node := by
    rw [storageForm_symm]
    exact hud
  have key : ∀ s : ℝ, 0 ≤ s * diagonalResponse weight incidence d node +
      s ^ 2 * diagonalStorage weight incidence (Pi.single node 1) := by
    intro s
    have h := hpsd (d + s • Pi.single node 1)
    have e : storageForm weight incidence (d + s • Pi.single node 1) (d + s • Pi.single node 1) =
        storageForm weight incidence d d + s * storageForm weight incidence d (Pi.single node 1) +
          s * storageForm weight incidence (Pi.single node 1) d +
          s ^ 2 * storageForm weight incidence (Pi.single node 1) (Pi.single node 1) := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [storageForm_self, storageForm_self, storageForm_self, hud, hdu, h0] at e
    linarith
  generalize diagonalResponse weight incidence d node = a at key ⊢
  have hb : 0 ≤ diagonalStorage weight incidence (Pi.single node 1) := hpsd _
  generalize diagonalStorage weight incidence (Pi.single node 1) = b at key hb
  have hb1 : b + 1 ≠ 0 := by positivity
  have hprod := mul_nonneg (key (-a / (b + 1))) (sq_nonneg (b + 1))
  have hval : (-a / (b + 1) * a + (-a / (b + 1)) ^ 2 * b) * (b + 1) ^ 2 = -a ^ 2 := by
    field_simp
    ring
  rw [hval] at hprod
  have ha2 : a ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg a)
  exact pow_eq_zero_iff two_ne_zero |>.mp ha2

/-- [proved-standard; formal-checked] With `S_D ⪰ 0`, a state stores no dissipation when and only
when its dissipation response is zero. -/
theorem storage_eq_zero_iff_response {weight : Branch → ℝ} {incidence : Branch → Node → ℝ}
    (hpsd : ∀ v, 0 ≤ diagonalStorage weight incidence v) (d : Node → ℝ) :
    diagonalStorage weight incidence d = 0 ↔ ∀ node, diagonalResponse weight incidence d node = 0 := by
  constructor
  · exact fun h0 node => response_eq_zero_of_storage_eq_zero hpsd h0 node
  · intro h
    have hs := sum_response_mul_self weight incidence d
    simp only [h, zero_mul, Finset.sum_const_zero] at hs
    linarith

end Form

/-! ## 2. The damped energy balance of any motion -/

section Balance

/-- [definition] The **dissipated power** of a motion, `⟨D x', x'⟩`, with `D = BᵀW_D B` the response
of the branch conductances `damping`. -/
def dissipatedPower (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (x' : ℝ → Node → ℝ)
    (t : ℝ) : ℝ :=
  ∑ node, diagonalResponse damping incidence (x' t) node * x' t node

/-- [proved-standard; formal-checked] The dissipated power is twice Rayleigh's dissipation
function: `⟨D x', x'⟩ = 2 S_D(x')`. -/
theorem dissipatedPower_eq (damping : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (x' : ℝ → Node → ℝ) (t : ℝ) :
    dissipatedPower damping incidence x' t = 2 * diagonalStorage damping incidence (x' t) :=
  sum_response_mul_self damping incidence (x' t)

/-- [proved-standard; formal-checked] A semidefinite dissipation never returns power. -/
theorem dissipatedPower_nonneg {damping : Branch → ℝ} {incidence : Branch → Node → ℝ}
    (hpsd : ∀ v, 0 ≤ diagonalStorage damping incidence v) (x' : ℝ → Node → ℝ) (t : ℝ) :
    0 ≤ dissipatedPower damping incidence x' t := by
  rw [dissipatedPower_eq]
  linarith [hpsd (x' t)]

/-- [definition] The port power of a motion against the damped constitution:
`⟨C x'' + D x' + K x, x'⟩`, the effort the damped equation requires, paired with the velocity. -/
def dampedPortPower (stiffness capacity damping : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (x x' x'' : ℝ → Node → ℝ) (t : ℝ) : ℝ :=
  ∑ node, (diagonalResponse capacity incidence (x'' t) node +
    diagonalResponse damping incidence (x' t) node +
    diagonalResponse stiffness incidence (x t) node) * x' t node

/-- [proved-standard; formal-checked] The damped port power is Resonance's port power plus the
dissipated power. -/
theorem dampedPortPower_eq (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (x x' x'' : ℝ → Node → ℝ) (t : ℝ) :
    dampedPortPower stiffness capacity damping incidence x x' x'' t =
      portPower stiffness capacity incidence x x' x'' t + dissipatedPower damping incidence x' t := by
  simp only [dampedPortPower, portPower, dissipatedPower, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-standard; formal-checked] **The damped energy balance**: the stored energy changes at the
port power less the dissipated power, `dE/dt = ⟨C x'' + D x' + K x, x'⟩ − ⟨D x', x'⟩`. -/
theorem hasDerivAt_motionEnergy_damped (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s) (t : ℝ) :
    HasDerivAt (motionEnergy stiffness capacity incidence x x')
      (dampedPortPower stiffness capacity damping incidence x x' x'' t -
        dissipatedPower damping incidence x' t) t := by
  refine (hasDerivAt_motionEnergy stiffness capacity incidence hx hx' t).congr_deriv ?_
  rw [dampedPortPower_eq]
  ring

/-- [proved-standard; formal-checked] **The damped work ledger of any motion**: over `[0, t]` the
port work is the change of stored energy plus the dissipated energy. -/
theorem damped_motion_work_ledger (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s)
    (hx'' : ∀ node, Continuous fun s => x'' s node) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, dampedPortPower stiffness capacity damping incidence x x' x'' s =
      (motionEnergy stiffness capacity incidence x x' t -
        motionEnergy stiffness capacity incidence x x' 0) +
        ∫ s in (0 : ℝ)..t, dissipatedPower damping incidence x' s := by
  have hxc : ∀ node, Continuous fun s => x s node := fun node =>
    continuous_iff_continuousAt.mpr fun s => (hx s node).continuousAt
  have hx'c : ∀ node, Continuous fun s => x' s node := fun node =>
    continuous_iff_continuousAt.mpr fun s => (hx' s node).continuousAt
  have hP : Continuous (portPower stiffness capacity incidence x x' x'') := by
    unfold portPower diagonalResponse branchDrop
    fun_prop
  have hD : Continuous (dissipatedPower damping incidence x') := by
    unfold dissipatedPower diagonalResponse branchDrop
    fun_prop
  have hsplit : (∫ s in (0 : ℝ)..t, dampedPortPower stiffness capacity damping incidence x x' x'' s) =
      ∫ s in (0 : ℝ)..t, (portPower stiffness capacity incidence x x' x'' s +
        dissipatedPower damping incidence x' s) := by
    congr 1
    funext s
    exact dampedPortPower_eq stiffness capacity damping incidence x x' x'' s
  rw [hsplit, intervalIntegral.integral_add (hP.intervalIntegrable 0 t) (hD.intervalIntegrable 0 t),
    motion_work_ledger stiffness capacity incidence hx hx' hx'' t]

/-- [proved-standard; formal-checked] **Ring-down.** A free motion of the damped constitution
(`C x'' + D x' + K x = 0`) with `S_D ⪰ 0` loses energy at the dissipated power,
`dE/dt = −2 S_D(x') ≤ 0`, and its stored energy is antitone. -/
theorem free_motion_rings_down (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (hpsd : ∀ v, 0 ≤ diagonalStorage damping incidence v)
    {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s)
    (hfree : ∀ s node, diagonalResponse capacity incidence (x'' s) node +
      diagonalResponse damping incidence (x' s) node +
      diagonalResponse stiffness incidence (x s) node = 0) :
    (∀ t, HasDerivAt (motionEnergy stiffness capacity incidence x x')
      (-(2 * diagonalStorage damping incidence (x' t))) t) ∧
      Antitone (motionEnergy stiffness capacity incidence x x') := by
  have hderiv : ∀ t, HasDerivAt (motionEnergy stiffness capacity incidence x x')
      (-(2 * diagonalStorage damping incidence (x' t))) t := by
    intro t
    refine (hasDerivAt_motionEnergy_damped stiffness capacity damping incidence hx hx' t).congr_deriv
      ?_
    rw [dampedPortPower, dissipatedPower_eq]
    simp [hfree t]
  refine ⟨hderiv, antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_⟩
  rw [(hderiv t).deriv]
  linarith [hpsd (x' t)]

/-- [proved-standard; formal-checked] **The free motion's ledger**: over `[0, t]` a free motion loses
the dissipated energy, `E(0) − E(t) = ∫₀ᵗ ⟨D x', x'⟩`. -/
theorem free_motion_ledger (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s)
    (hx'' : ∀ node, Continuous fun s => x'' s node)
    (hfree : ∀ s node, diagonalResponse capacity incidence (x'' s) node +
      diagonalResponse damping incidence (x' s) node +
      diagonalResponse stiffness incidence (x s) node = 0) (t : ℝ) :
    motionEnergy stiffness capacity incidence x x' 0 -
        motionEnergy stiffness capacity incidence x x' t =
      ∫ s in (0 : ℝ)..t, dissipatedPower damping incidence x' s := by
  have h := damped_motion_work_ledger stiffness capacity damping incidence hx hx' hx'' t
  have hzero : (∫ s in (0 : ℝ)..t, dampedPortPower stiffness capacity damping incidence x x' x'' s) =
      0 := by
    have hfun : dampedPortPower stiffness capacity damping incidence x x' x'' = fun _ => 0 := by
      funext s
      simp [dampedPortPower, hfree s]
    rw [hfun]
    simp
  linarith

end Balance

/-! ## 3. Holding a motion against friction -/

section Holding

/-- [definition] The **friction effort** of the held motion `x(t) = cos(ωt) d`: `D ẋ = −ω sin(ωt) D d`,
the quadrature part of the holding effort. -/
def frictionEffort (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (ω : ℝ) (d : Node → ℝ)
    (t : ℝ) (node : Node) : ℝ :=
  -(ω * Real.sin (ω * t)) * diagonalResponse damping incidence d node

/-- [definition] The **damped holding effort**: the effort `C ẍ + D ẋ + K x` needed to hold
`x(t) = cos(ωt) d`, Resonance's in-phase `holdingEffort` plus the quadrature `frictionEffort`. -/
def dampedHoldingEffort (stiffness capacity damping : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (t : ℝ) (node : Node) : ℝ :=
  holdingEffort stiffness capacity incidence ω d t node + frictionEffort damping incidence ω d t node

/-- [proved-derived; formal-checked] **The damped holding effort is Newton's residual**
`C ẍ + D ẋ + K x` of `x(t) = cos(ωt) d`, with `ẋ = −ω sin(ωt) d` and `ẍ = −ω² cos(ωt) d`. -/
theorem dampedHoldingEffort_newton (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) (d : Node → ℝ) (t : ℝ) (node : Node) :
    dampedHoldingEffort stiffness capacity damping incidence ω d t node =
      diagonalResponse capacity incidence (fun n => -(ω ^ 2 * Real.cos (ω * t)) * d n) node +
        diagonalResponse damping incidence (fun n => -(ω * Real.sin (ω * t)) * d n) node +
        diagonalResponse stiffness incidence (fun n => Real.cos (ω * t) * d n) node := by
  rw [diagonalResponse_smul, diagonalResponse_smul, diagonalResponse_smul, dampedHoldingEffort,
    holdingEffort, frictionEffort]
  ring

/-- [proved-derived; formal-checked] **The two parts of the damped holding effort.** For `d = r + e`
with `r` in the mode space at `ω²`, the in-phase part sees only `e` and the quadrature part sees the
whole drive. -/
theorem dampedHoldingEffort_split (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) {r : Node → ℝ}
    (hr : r ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (e : Node → ℝ) (t : ℝ) (node : Node) :
    dampedHoldingEffort stiffness capacity damping incidence ω (r + e) t node =
      holdingEffort stiffness capacity incidence ω e t node +
        (frictionEffort damping incidence ω r t node + frictionEffort damping incidence ω e t node) := by
  have hresp := (mem_modeSpace_iff_response stiffness capacity incidence _ _).mp hr
  simp only [dampedHoldingEffort, holdingEffort, frictionEffort, diagonalResponse_add, hresp node]
  ring

/-- [proved-derived; formal-checked] **RIDE is no longer free.** For `d` in the mode space at `ω²`,
`ω ≠ 0`, the holding effort against friction is the quadrature term alone, and it is zero at every
time when and only when `D d = 0`. -/
theorem ride_against_friction (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : ω ≠ 0) {d : Node → ℝ}
    (hd : d ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2)) :
    (∀ t node, dampedHoldingEffort stiffness capacity damping incidence ω d t node =
        frictionEffort damping incidence ω d t node) ∧
      ((∀ t node, dampedHoldingEffort stiffness capacity damping incidence ω d t node = 0) ↔
        ∀ node, diagonalResponse damping incidence d node = 0) := by
  have hresp := (mem_modeSpace_iff_response stiffness capacity incidence _ _).mp hd
  have hfric : ∀ t node, dampedHoldingEffort stiffness capacity damping incidence ω d t node =
      frictionEffort damping incidence ω d t node := by
    intro t node
    simp only [dampedHoldingEffort, holdingEffort, hresp node, sub_self, mul_zero, zero_add]
  refine ⟨hfric, fun h node => ?_, fun h t node => ?_⟩
  · have hq := h (Real.pi / 2 / ω) node
    have harg : ω * (Real.pi / 2 / ω) = Real.pi / 2 := by field_simp
    rw [hfric, frictionEffort, harg, Real.sin_pi_div_two, mul_one] at hq
    rcases mul_eq_zero.mp hq with h1 | h1
    · exact absurd (neg_eq_zero.mp h1) hω
    · exact h1
  · rw [hfric, frictionEffort, h node, mul_zero]

/-- [proved-derived; formal-checked] With `S_D ⪰ 0`, holding a mode at `ω ≠ 0` against friction
needs a nonzero effort at some time when and only when `S_D(d) > 0`. -/
theorem ride_needs_effort_iff (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (hpsd : ∀ v, 0 ≤ diagonalStorage damping incidence v)
    {ω : ℝ} (hω : ω ≠ 0) {d : Node → ℝ}
    (hd : d ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2)) :
    (∃ t node, dampedHoldingEffort stiffness capacity damping incidence ω d t node ≠ 0) ↔
      0 < diagonalStorage damping incidence d := by
  have h1 := (ride_against_friction stiffness capacity damping incidence hω hd).2
  have h2 := storage_eq_zero_iff_response hpsd d
  have h3 : 0 < diagonalStorage damping incidence d ↔ diagonalStorage damping incidence d ≠ 0 :=
    ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hpsd d) (Ne.symm h)⟩
  rw [h3, Ne, h2, ← h1]
  push Not
  rfl

end Holding

/-! ## 4. The work ledger with friction -/

section Ledger

/-- [definition] The port power of the held motion against friction: `⟨f(s), ẋ(s)⟩` with `f` the
damped holding effort and `ẋ(s) = −ω sin(ωs) d`. -/
def dampedHeldPower (stiffness capacity damping : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (s : ℝ) : ℝ :=
  ∑ node, dampedHoldingEffort stiffness capacity damping incidence ω d s node *
    (-(ω * Real.sin (ω * s)) * d node)

/-- [proved-derived; formal-checked] The held power is the damped port power of item 2 on the
motion `x(s) = cos(ωs) d`. -/
theorem dampedHeldPower_eq_portPower (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) (d : Node → ℝ) (s : ℝ) :
    dampedHeldPower stiffness capacity damping incidence ω d s =
      dampedPortPower stiffness capacity damping incidence (fun τ n => Real.cos (ω * τ) * d n)
        (fun τ n => -(ω * Real.sin (ω * τ)) * d n) (fun τ n => -(ω ^ 2 * Real.cos (ω * τ)) * d n)
        s := by
  simp only [dampedHeldPower, dampedPortPower, dampedHoldingEffort_newton]

/-- [proved-derived; formal-checked] The dissipated power of the held motion is
`ω² sin²(ωs)·2 S_D(d)`. -/
theorem dissipatedPower_held (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (ω : ℝ)
    (d : Node → ℝ) (s : ℝ) :
    dissipatedPower damping incidence (fun τ n => -(ω * Real.sin (ω * τ)) * d n) s =
      ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d) := by
  rw [dissipatedPower_eq, diagonalStorage_smul]
  ring

/-- [proved-derived; formal-checked] **The held power splits** into Resonance's reactive power and
the dissipated power `ω² sin²(ωs)·2 S_D(d)`. -/
theorem dampedHeldPower_eq (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) (d : Node → ℝ) (s : ℝ) :
    dampedHeldPower stiffness capacity damping incidence ω d s =
      ∑ node, holdingEffort stiffness capacity incidence ω d s node *
          (-(ω * Real.sin (ω * s)) * d node) +
        ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d) := by
  rw [← sum_response_mul_self damping incidence d]
  simp only [dampedHeldPower, dampedHoldingEffort, frictionEffort, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] The antiderivative of the held dissipated power. -/
theorem hasDerivAt_heldDissipation (ω S t : ℝ) :
    HasDerivAt (fun s => ω * (ω * s - Real.sin (ω * s) * Real.cos (ω * s)) * S)
      (ω ^ 2 * Real.sin (ω * t) ^ 2 * (2 * S)) t := by
  have hlin : HasDerivAt (fun τ => ω * τ) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hs : HasDerivAt (fun τ => Real.sin (ω * τ)) (Real.cos (ω * t) * ω) t :=
    (Real.hasDerivAt_sin (ω * t)).comp t hlin
  have hc : HasDerivAt (fun τ => Real.cos (ω * τ)) (-Real.sin (ω * t) * ω) t :=
    (Real.hasDerivAt_cos (ω * t)).comp t hlin
  refine (((hlin.sub (hs.mul hc)).const_mul ω).mul_const S).congr_deriv ?_
  have htrig := Real.sin_sq_add_cos_sq (ω * t)
  linear_combination (-(ω ^ 2 * S)) * htrig

/-- [proved-derived; formal-checked] **The dissipated energy of the held motion** over `[0, t]`:
`∫₀ᵗ ω² sin²(ωs)·2 S_D(d) ds = ω(ωt − sin(ωt) cos(ωt))·S_D(d)`. -/
theorem heldDissipation_integral (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (ω : ℝ)
    (d : Node → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d) =
      ω * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) * diagonalStorage damping incidence d := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_heldDissipation ω (diagonalStorage damping incidence d) s)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- [proved-derived; formal-checked] **The held ledger with friction**, for any drive: the work over
`[0, t]` is the change of stored energy plus the dissipated energy `ω(ωt − sin(ωt) cos(ωt))·S_D(d)`. -/
theorem damped_held_ledger (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) (d : Node → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, dampedHeldPower stiffness capacity damping incidence ω d s =
      (modeEnergy stiffness capacity incidence ω d t - modeEnergy stiffness capacity incidence ω d 0) +
        ω * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) * diagonalStorage damping incidence d := by
  have hreact : Continuous fun s => ∑ node, holdingEffort stiffness capacity incidence ω d s node *
      (-(ω * Real.sin (ω * s)) * d node) := by
    unfold holdingEffort
    fun_prop
  have hfric : Continuous fun s =>
      ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d) := by
    fun_prop
  have hsplit : (∫ s in (0 : ℝ)..t, dampedHeldPower stiffness capacity damping incidence ω d s) =
      ∫ s in (0 : ℝ)..t, ((∑ node, holdingEffort stiffness capacity incidence ω d s node *
          (-(ω * Real.sin (ω * s)) * d node)) +
        ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d)) := by
    congr 1
    funext s
    exact dampedHeldPower_eq stiffness capacity damping incidence ω d s
  rw [hsplit, intervalIntegral.integral_add (hreact.intervalIntegrable 0 t)
      (hfric.intervalIntegrable 0 t), heldDissipation_integral,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_modeEnergy stiffness capacity incidence ω d s)
      (hreact.intervalIntegrable 0 t)]

/-- [proved-derived; formal-checked] **The work ledger with friction.** For `d = r + e` with `r` in
the mode space at `ω²`, the work over `[0, t]` is Resonance's `sin²(ωt)·(ω² S_C(e) − S_K(e))` plus the
dissipated energy `∫₀ᵗ ω² sin²(ωs)·2 S_D(r + e) ds`, which sees the whole drive. -/
theorem damped_work_ledger (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) {r : Node → ℝ}
    (hr : r ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (e : Node → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, dampedHeldPower stiffness capacity damping incidence ω (r + e) s =
      Real.sin (ω * t) ^ 2 *
          (ω ^ 2 * diagonalStorage capacity incidence e - diagonalStorage stiffness incidence e) +
        ∫ s in (0 : ℝ)..t,
          ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence (r + e)) := by
  rw [damped_held_ledger, work_ledger stiffness capacity incidence ω hr e t, heldDissipation_integral]

/-- [proved-derived; formal-checked] **One period.** For `ω > 0`, over `[0, 2π/ω]` the reactive part
returns to zero and the work is `2π ω S_D(d) = π ω ⟨D d, d⟩`. -/
theorem damped_work_period (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : 0 < ω) (d : Node → ℝ) :
    modeEnergy stiffness capacity incidence ω d (2 * Real.pi / ω) -
        modeEnergy stiffness capacity incidence ω d 0 = 0 ∧
      ∫ s in (0 : ℝ)..(2 * Real.pi / ω), dampedHeldPower stiffness capacity damping incidence ω d s =
        2 * Real.pi * ω * diagonalStorage damping incidence d ∧
      2 * Real.pi * ω * diagonalStorage damping incidence d =
        Real.pi * ω * ∑ node, diagonalResponse damping incidence d node * d node := by
  have hω0 : ω ≠ 0 := hω.ne'
  have hT : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  have hreact : modeEnergy stiffness capacity incidence ω d (2 * Real.pi / ω) -
      modeEnergy stiffness capacity incidence ω d 0 = 0 := by
    rw [modeEnergy_closed, modeEnergy_closed, hT]
    simp
  refine ⟨hreact, ?_, ?_⟩
  · rw [damped_held_ledger, hreact, hT, Real.sin_two_pi]
    ring
  · rw [sum_response_mul_self]
    ring

end Ledger

/-! ## 5. Quality -/

section Quality

/-- [definition] The **mean dissipated power** of the held motion `x(t) = cos(ωt) d` over one period
`2π/ω`: `(ω/2π) ∫₀^{2π/ω} ⟨D ẋ, ẋ⟩`. -/
def meanDissipatedPower (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (ω : ℝ)
    (d : Node → ℝ) : ℝ :=
  ω / (2 * Real.pi) * ∫ s in (0 : ℝ)..(2 * Real.pi / ω),
    dissipatedPower damping incidence (fun τ n => -(ω * Real.sin (ω * τ)) * d n) s

/-- [proved-standard; formal-checked] For `ω > 0` the mean dissipated power is `ω² S_D(d)`. -/
theorem meanDissipatedPower_eq (damping : Branch → ℝ) (incidence : Branch → Node → ℝ) {ω : ℝ}
    (hω : 0 < ω) (d : Node → ℝ) :
    meanDissipatedPower damping incidence ω d = ω ^ 2 * diagonalStorage damping incidence d := by
  have hω0 : ω ≠ 0 := hω.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT : ω * (2 * Real.pi / ω) = 2 * Real.pi := by field_simp
  have hfun : (fun s => dissipatedPower damping incidence
      (fun τ n => -(ω * Real.sin (ω * τ)) * d n) s) =
      fun s => ω ^ 2 * Real.sin (ω * s) ^ 2 * (2 * diagonalStorage damping incidence d) := by
    funext s
    exact dissipatedPower_held damping incidence ω d s
  rw [meanDissipatedPower, hfun, heldDissipation_integral, hT]
  simp
  field_simp

/-- [proved-derived; formal-checked] For `ω > 0` the mean port power of the held motion over one
period is the mean dissipated power: the reactive part averages to zero. -/
theorem meanPortPower_eq (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : 0 < ω) (d : Node → ℝ) :
    ω / (2 * Real.pi) * ∫ s in (0 : ℝ)..(2 * Real.pi / ω),
        dampedHeldPower stiffness capacity damping incidence ω d s =
      meanDissipatedPower damping incidence ω d := by
  have hω0 : ω ≠ 0 := hω.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [(damped_work_period stiffness capacity damping incidence hω d).2.1,
    meanDissipatedPower_eq damping incidence hω d]
  field_simp

/-- [definition] The **quality** of the held motion `x(t) = cos(ωt) d`, carried as an undivided ratio
`(ω E, P̄)`: `E = ω² S_C(d)` the stored energy of a held mode and `P̄` the mean dissipated power.
Its quotient `Q = ω E / P̄` is read only where the denominator is nonzero. -/
def quality (capacity damping : Branch → ℝ) (incidence : Branch → Node → ℝ) (ω : ℝ)
    (d : Node → ℝ) : ℝ × ℝ :=
  (ω * (ω ^ 2 * diagonalStorage capacity incidence d), meanDissipatedPower damping incidence ω d)

/-- [proved-derived; formal-checked] For a held mode at `ω > 0` the quality's numerator is `ω` times
the stored energy at every time, and its denominator is `ω² S_D(d)`. -/
theorem quality_reads (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : 0 < ω) {d : Node → ℝ}
    (hmode : IsGeneralizedMode stiffness capacity incidence (ω ^ 2) d) :
    (∀ t, (quality capacity damping incidence ω d).1 =
        ω * modeEnergy stiffness capacity incidence ω d t) ∧
      (quality capacity damping incidence ω d).2 = ω ^ 2 * diagonalStorage damping incidence d := by
  refine ⟨fun t => ?_, meanDissipatedPower_eq damping incidence hω d⟩
  rw [quality, modeEnergy_conserved hmode t]

/-- [proved-derived; formal-checked] **The quality is finite when and only when the mode
dissipates**: for `ω > 0` and `S_D ⪰ 0`, the denominator is nonzero when and only when
`S_D(d) > 0`, when and only when `D d ≠ 0`. -/
theorem quality_finite_iff (capacity damping : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (hpsd : ∀ v, 0 ≤ diagonalStorage damping incidence v) {ω : ℝ} (hω : 0 < ω) (d : Node → ℝ) :
    ((quality capacity damping incidence ω d).2 ≠ 0 ↔ 0 < diagonalStorage damping incidence d) ∧
      (0 < diagonalStorage damping incidence d ↔
        ∃ node, diagonalResponse damping incidence d node ≠ 0) := by
  have hden : (quality capacity damping incidence ω d).2 =
      ω ^ 2 * diagonalStorage damping incidence d :=
    meanDissipatedPower_eq damping incidence hω d
  have hpos : 0 < ω ^ 2 := by positivity
  have h3 : 0 < diagonalStorage damping incidence d ↔ diagonalStorage damping incidence d ≠ 0 :=
    ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hpsd d) (Ne.symm h)⟩
  refine ⟨?_, ?_⟩
  · rw [hden, h3]
    exact ⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero hpos.ne' h⟩
  · rw [h3, Ne, storage_eq_zero_iff_response hpsd d]
    push Not
    rfl

/-- [proved-standard; formal-checked] **The quality of a held mode**: where `S_D(d) > 0` and `ω > 0`,
`Q = ω E / P̄ = ω S_C(d)/S_D(d)`, which is also the stored energy over the energy dissipated per
radian (one period's dissipated energy over `2π`). -/
theorem quality_quotient (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : 0 < ω) (d : Node → ℝ)
    (hD : 0 < diagonalStorage damping incidence d) :
    (quality capacity damping incidence ω d).1 / (quality capacity damping incidence ω d).2 =
        ω * diagonalStorage capacity incidence d / diagonalStorage damping incidence d ∧
      ω ^ 2 * diagonalStorage capacity incidence d /
          ((∫ s in (0 : ℝ)..(2 * Real.pi / ω),
            dampedHeldPower stiffness capacity damping incidence ω d s) / (2 * Real.pi)) =
        ω * diagonalStorage capacity incidence d / diagonalStorage damping incidence d := by
  have hω0 : ω ≠ 0 := hω.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hD0 : diagonalStorage damping incidence d ≠ 0 := hD.ne'
  refine ⟨?_, ?_⟩
  · rw [show (quality capacity damping incidence ω d).2 =
        ω ^ 2 * diagonalStorage damping incidence d from
      meanDissipatedPower_eq damping incidence hω d, quality]
    field_simp
  · rw [(damped_work_period stiffness capacity damping incidence hω d).2.1]
    field_simp

/-- [proved-derived; formal-checked] **The lossless ring.** A nonzero held mode at `ω > 0` with
positive capacitive storage and `S_D(d) = 0` has a positive numerator over a zero denominator: its
quality is unbounded, the RIDE of Resonance. -/
theorem quality_lossless (stiffness capacity damping : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : 0 < ω)
    (hpos : ∀ v, v ≠ 0 → 0 < diagonalStorage capacity incidence v) {d : Node → ℝ}
    (hmode : IsGeneralizedMode stiffness capacity incidence (ω ^ 2) d)
    (hD : diagonalStorage damping incidence d = 0) :
    0 < (quality capacity damping incidence ω d).1 ∧ (quality capacity damping incidence ω d).2 = 0 := by
  refine ⟨?_, ?_⟩
  · have := hpos d hmode.1
    simp only [quality]
    positivity
  · rw [(quality_reads stiffness capacity damping incidence hω hmode).2, hD, mul_zero]

end Quality

/-! ## 6. Friction's counterpart of the clamp -/

section Witness

/-- Conductance weights on `Parametron.chainIncidence`: a resistor from each node to ground and none
between the nodes, so `D = C = I`. -/
def groundDamping : Fin 3 → ℝ := ![1, 0, 1]

/-- Conductance weights on `Parametron.chainIncidence`: one resistor between the two nodes and none
to ground. -/
def bridgeDamping : Fin 3 → ℝ := ![0, 1, 0]

/-- [proved-derived; formal-checked] **Pure RIDE that friction charges.** On the chain the drive
`(1, 1)` lies in the mode space at `ω = 1` (`e = 0`), so Resonance's holding effort is zero at every
time; with `groundDamping` the holding effort at `t = π/2` is `−1` on node `0`, one period costs `2π`
and `Q = 1`. With `bridgeDamping` the holding of `(1, 1)` stays free, while `(1, −1)` has
`S_D = 2`. -/
theorem friction_ride_witness :
    (![1, 1] : Fin 2 → ℝ) ∈ modeSpace (storageForm chainStiffness chainIncidence)
        (storageForm chainCapacity chainIncidence) (1 ^ 2) ∧
      (∀ t node, holdingEffort chainStiffness chainCapacity chainIncidence 1 ![1, 1] t node = 0) ∧
      dampedHoldingEffort chainStiffness chainCapacity groundDamping chainIncidence 1 ![1, 1]
        (Real.pi / 2) 0 = -1 ∧
      ∫ s in (0 : ℝ)..(2 * Real.pi / 1),
          dampedHeldPower chainStiffness chainCapacity groundDamping chainIncidence 1 ![1, 1] s =
        2 * Real.pi ∧
      (quality chainCapacity groundDamping chainIncidence 1 ![1, 1]).1 /
          (quality chainCapacity groundDamping chainIncidence 1 ![1, 1]).2 = 1 ∧
      (∀ t node, dampedHoldingEffort chainStiffness chainCapacity bridgeDamping chainIncidence 1
          ![1, 1] t node = 0) ∧
      diagonalStorage bridgeDamping chainIncidence ![1, -1] = 2 := by
  have hr : (![1, 1] : Fin 2 → ℝ) ∈ modeSpace (storageForm chainStiffness chainIncidence)
      (storageForm chainCapacity chainIncidence) (1 ^ 2) := by
    rw [one_pow]
    exact ((isGeneralizedMode_iff _ _ _ _ _).mp modeWitness.2.1).2
  have hSD : diagonalStorage groundDamping chainIncidence ![1, 1] = 1 := by
    simp [diagonalStorage, branchDrop, chainIncidence, groundDamping, Fin.sum_univ_three,
      Fin.sum_univ_two]
    norm_num
  have hSC : diagonalStorage chainCapacity chainIncidence ![1, 1] = 1 := by
    simp [diagonalStorage, branchDrop, chainIncidence, chainCapacity, Fin.sum_univ_three,
      Fin.sum_univ_two]
    norm_num
  have hbridge : ∀ node, diagonalResponse bridgeDamping chainIncidence ![1, 1] node = 0 := by
    intro node
    fin_cases node <;>
      simp [diagonalResponse, branchDrop, chainIncidence, bridgeDamping, Fin.sum_univ_three,
        Fin.sum_univ_two]
  have hride := ride_against_friction chainStiffness chainCapacity groundDamping chainIncidence
    one_ne_zero hr
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t node
    have h := (mem_modeSpace_iff_response chainStiffness chainCapacity chainIncidence _ _).mp hr node
    simp [holdingEffort, h]
  · rw [hride.1, frictionEffort]
    simp [diagonalResponse, branchDrop, chainIncidence, groundDamping, Fin.sum_univ_three,
      Fin.sum_univ_two]
  · rw [(damped_work_period chainStiffness chainCapacity groundDamping chainIncidence one_pos
      ![1, 1]).2.1, hSD]
    ring
  · rw [(quality_quotient chainStiffness chainCapacity groundDamping chainIncidence one_pos ![1, 1]
      (by rw [hSD]; norm_num)).1, hSC, hSD]
    norm_num
  · exact ((ride_against_friction chainStiffness chainCapacity bridgeDamping chainIncidence
      one_ne_zero hr).2).mpr hbridge
  · simp [diagonalStorage, branchDrop, chainIncidence, bridgeDamping, Fin.sum_univ_three,
      Fin.sum_univ_two]
    norm_num

end Witness

end Holonics.Compression.Core.ResonanceFriction
