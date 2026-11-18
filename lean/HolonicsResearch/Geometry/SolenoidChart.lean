import Mathlib

/-!
# The finite solenoidal chart: a circle cover with its longitudinal lift and signed carry

The winding guide (`docs/WINDING_CARRY_AND_PLACEMENT.md` §9, "Finite solenoidal charts and their physical consumer";
atlas `solenoid.finite-compatible-chart`, `solenoid.restriction-action-square`) states the finite chart that the October
library ran as `geometry::solenoid` (held at `d5ed4adc1`): positive moduli `N_i ∣ N_(i+1)`, a normalized rational phase `s`,
a signed winding `w` and compatible transverse residues `z_i`; an advance by `a` takes `c = ⌊s + a⌋` and publishes
`(s + a − c, w + c, z_i + c mod N_i)`; restriction commutes with addition and advance; the current keeps the longitudinal
lift `w + s`; equal finite faces do not erase different windings. The guide and #410 (the "carry tower" box) carried the
Lean proof of this joined operator as owed. This file states the operator and proves those laws, and beside them the guide's
[proved-derived] paragraph on the completed additive solenoid: its translation flow has no nonzero return time.

[proved-derived; formal-checked] What is proved.

1. **The chart and its advance** (`Chart`, `advance`): a state at modulus `N` is `(s, w, z)` with `0 ≤ s < 1` rational, `w`
   an integer and `z : ZMod N`; `advance x a` is `(s + a − c, w + c, z + c)` with `c = ⌊s + a⌋` (`advance_s`, `advance_w`,
   `advance_z`). Negative motion uses the floor, never truncation (`advance_neg_example`).
2. **The lift moves by the advance, and the advance is an action of `ℚ`** (`lift_advance`, `advance_zero`,
   `advance_advance`): `lift x = w + s`, `lift (advance x a) = lift x + a`.
3. **The lift and the transverse charge are the whole state** (`floor_lift`, `fract_lift`, `charge_advance`,
   `ext_lift_charge`, `liftCharge`): `⌊lift x⌋ = w`, `fract (lift x) = s`, the charge `z − w` in `ZMod N` is kept by every
   advance, and `x ↦ (lift x, charge x)` is a bijection onto `ℚ × ZMod N` under which `advance a` is `(ℓ, u) ↦ (ℓ + a, u)`
   (`liftCharge_advance`).
4. **The finite face returns and the lift does not** (`advance_intCast`, `advance_modulus`, `face_returns_iff`,
   `advance_eq_self_iff`, `same_face_different_winding`): an advance returns the finite face `(s, z)` when and only when it
   is a whole multiple of `N` turns, and then the winding has moved by that multiple; no nonzero advance returns the state.
   Equal finite faces do not erase different windings.
5. **The carried group law** (`instAddCommGroup`, `add_s`, `add_w`, `add_z`, `liftChargeAddEquiv`, `advance_eq_add_turn`):
   the sum of two states is `(s₁ + s₂ − c, w₁ + w₂ + c, z₁ + z₂ + c)` with `c = ⌊s₁ + s₂⌋`, the group law of `ℚ × ZMod N`
   in the chart of statement 3, and an advance is the sum with `turn a`.
6. **Restriction commutes with advance and with addition** (`restrict`, `restrict_advance`, `restrict_add`,
   `restrictHom`, `lift_restrict`, `charge_restrict`, `restrict_restrict`): along `M ∣ N` the transverse residue is cast by
   `ZMod.castHom`, the phase and the winding are kept, and the square of the atlas row closes for both operations.
7. **A compatible section stays compatible** (`Compatible`, `Compatible.advance`, `Compatible.add`, `Compatible.lift_eq`):
   over a divisibility chain `N i ∣ N (i + 1)` a section whose levels restrict to one another keeps that under a common
   advance and under the levelwise sum, and all its levels share one longitudinal lift.
8. **The circle face** (`phase`, `phase_advance`, `phase_restrict`): `phase x = s + z` read in `ℚ / Nℤ` (the guide's
   `θ = (s + z)/N` in turns of the level's circle) satisfies `phase (advance x a) = phase x + a`, and the cover
   `ℚ / Nℤ → ℚ / Mℤ` carries the phase of a state to the phase of its restriction.
9. **The completed solenoid's flow has no nonzero return time** (`cover`, `Solenoid`, `flow`, `flow_eq_self_iff`,
   `no_return_of_unbounded`, `no_return_all_moduli`, `no_return_prime_power_chain`): for moduli unbounded along the chain,
   translation by `t` fixes a point of the inverse limit of the circles `ℝ / N_i ℤ` only for `t = 0`. For all positive
   integers and for a prime-power chain the hypothesis holds. Beside statement 4 this is the contrast the guide draws: each
   finite face has the return period `N`, and the completed object has none.

Limits. The chart is finite and rational: no inverse limit of charts, no real-circle completion of the chart itself and no
continuation theorem is stated (statement 9 is about the circles `ℝ / N_i ℤ`, joined to the chart only through statement
8's phase over `ℚ`). The character groups the guide names (`ℚ` for the full divisibility order, `ℤ[1/p]` for a prime-power
chain) are not stated here. A supplied finer continuation of a section is not constructed: `Compatible` is a hypothesis.
The Rust owner retired with the October library; nothing here is tied to running code. The return-time statement concerns
this translation flow alone, and says nothing of prime-power terms in an explicit formula (the guide's own caution).

The computational object is the helical pair interaction: the chart is one strand's helix read at a tower of rings, and
the charge `z − w` is what a pair contact between the longitudinal winding and a transverse ring conserves. Of the winding
guide's six general objects this is the helix (circle + carry: `advance`, `lift`) and the tower thread (`restrict`,
`Compatible`, `Solenoid`); the faces and placement appear as `phase`; the pair, cell holonomy and the tube stay attached.

Consumers: the atlas rows `solenoid.finite-compatible-chart` and `solenoid.restriction-action-square`; #410's box for the
carry tower. `Geometry/PhaseCarry` owns the one-level carry cocycle and odometer on `ℕ` (`winding_add`, `carry_cocycle`,
`digits_succ`); this file is the rational chart with a signed winding and a tower.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.SolenoidChart

/-! ## 1. The chart, its advance and its lift -/

/-- [definition] **A state of the finite solenoidal chart at modulus `N`**: a normalized rational phase `s` in `[0, 1)`, a
signed winding `w`, and a transverse residue `z` on the ring of `N` places. -/
@[ext]
structure Chart (N : ℕ) where
  /-- The normalized longitudinal phase. -/
  s : ℚ
  /-- The signed winding. -/
  w : ℤ
  /-- The transverse residue at this level. -/
  z : ZMod N
  s_nonneg : 0 ≤ s
  s_lt_one : s < 1

variable {N M : ℕ}

/-- [definition] **The advance**: with `c = ⌊s + a⌋`, the state `(s, w, z)` goes to `(s + a − c, w + c, z + c)`. The carry
`c` is the floor, so a negative advance borrows. -/
def advance (x : Chart N) (a : ℚ) : Chart N where
  s := Int.fract (x.s + a)
  w := x.w + ⌊x.s + a⌋
  z := x.z + ((⌊x.s + a⌋ : ℤ) : ZMod N)
  s_nonneg := Int.fract_nonneg _
  s_lt_one := Int.fract_lt_one _

/-- [definition] **The longitudinal lift** `w + s`, the strand's place on the line that covers the circle. -/
def lift (x : Chart N) : ℚ := x.w + x.s

/-- [definition] **The transverse charge** `z − w` in `ZMod N`: the residue with the winding's carries taken out. -/
def charge (x : Chart N) : ZMod N := x.z - (x.w : ZMod N)

/-- [formal-checked] The advanced phase is `s + a − c` with `c = ⌊s + a⌋`. -/
theorem advance_s (x : Chart N) (a : ℚ) : (advance x a).s = x.s + a - ⌊x.s + a⌋ := rfl

/-- [formal-checked] The advanced winding is `w + c`. -/
theorem advance_w (x : Chart N) (a : ℚ) : (advance x a).w = x.w + ⌊x.s + a⌋ := rfl

/-- [formal-checked] The advanced residue is `z + c`. -/
theorem advance_z (x : Chart N) (a : ℚ) : (advance x a).z = x.z + ((⌊x.s + a⌋ : ℤ) : ZMod N) := rfl

/-- [formal-checked] The winding is the floor of the lift. -/
theorem floor_lift (x : Chart N) : ⌊lift x⌋ = x.w := by
  unfold lift
  rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨x.s_nonneg, x.s_lt_one⟩, add_zero]

/-- [formal-checked] The phase is the fractional part of the lift. -/
theorem fract_lift (x : Chart N) : Int.fract (lift x) = x.s := by
  unfold lift
  rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨x.s_nonneg, x.s_lt_one⟩]

/-- [formal-checked] **The lift moves by the advance**: `(w + c) + (s + a − c) = (w + s) + a`. -/
theorem lift_advance (x : Chart N) (a : ℚ) : lift (advance x a) = lift x + a := by
  simp only [lift, advance, Int.fract]
  push_cast
  ring

/-- [formal-checked] **Every advance keeps the transverse charge**: the residue and the winding take the same carry. -/
theorem charge_advance (x : Chart N) (a : ℚ) : charge (advance x a) = charge x := by
  simp only [charge, advance]
  push_cast
  ring

/-- [formal-checked] **The lift and the charge are the whole state.** -/
theorem ext_lift_charge {x y : Chart N} (hl : lift x = lift y) (hc : charge x = charge y) : x = y := by
  have hs : x.s = y.s := by rw [← fract_lift x, ← fract_lift y, hl]
  have hw : x.w = y.w := by rw [← floor_lift x, ← floor_lift y, hl]
  refine Chart.ext hs hw ?_
  have := hc
  simp only [charge, hw] at this
  exact sub_left_injective this

/-- [formal-checked] An advance by nothing is no move. -/
theorem advance_zero (x : Chart N) : advance x 0 = x :=
  ext_lift_charge (by rw [lift_advance, add_zero]) (charge_advance x 0)

/-- [formal-checked] **The advance is an action of `ℚ`**: two advances compose into the advance by their sum. -/
theorem advance_advance (x : Chart N) (a b : ℚ) : advance (advance x a) b = advance x (a + b) :=
  ext_lift_charge (by rw [lift_advance, lift_advance, lift_advance, add_assoc])
    (by rw [charge_advance, charge_advance, charge_advance])

/-- [formal-checked] **Negative motion borrows by the floor**: from phase `1/4`, an advance by `−1/2` lands at phase `3/4`
with the winding lowered by one and the residue lowered by one, where truncation toward zero would have kept the winding. -/
theorem advance_neg_example (w : ℤ) (z : ZMod N) :
    advance (⟨1 / 4, w, z, by norm_num, by norm_num⟩ : Chart N) (-1 / 2)
      = ⟨3 / 4, w - 1, z - 1, by norm_num, by norm_num⟩ := by
  have hfloor : ⌊(1 / 4 : ℚ) + -1 / 2⌋ = -1 := by
    rw [Int.floor_eq_iff]; norm_num
  ext
  · simp only [advance, Int.fract, hfloor]; norm_num
  · simp only [advance, hfloor]; ring
  · simp only [advance, hfloor]; push_cast; ring

/-! ## 2. The chart `(lift, charge)` -/

/-- [definition] **The state as its lift and its charge**: a bijection of the chart at modulus `N` onto `ℚ × ZMod N`. -/
def liftCharge : Chart N ≃ ℚ × ZMod N where
  toFun x := (lift x, charge x)
  invFun p :=
    { s := Int.fract p.1
      w := ⌊p.1⌋
      z := p.2 + ((⌊p.1⌋ : ℤ) : ZMod N)
      s_nonneg := Int.fract_nonneg _
      s_lt_one := Int.fract_lt_one _ }
  left_inv x := by
    refine Chart.ext (fract_lift x) (floor_lift x) ?_
    simp only [floor_lift, charge]
    ring
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [lift]
      exact Int.floor_add_fract p.1
    · simp only [charge]
      ring

/-- [formal-checked] In the chart `(lift, charge)` the advance by `a` is `(ℓ, u) ↦ (ℓ + a, u)`: a translation along the
line with the transverse charge held. -/
theorem liftCharge_advance (x : Chart N) (a : ℚ) :
    liftCharge (advance x a) = ((liftCharge x).1 + a, (liftCharge x).2) :=
  Prod.ext (lift_advance x a) (charge_advance x a)

/-! ## 3. The finite face returns; the lift does not -/

/-- [formal-checked] A whole advance `k` keeps the phase and moves the winding and the residue by `k`. -/
theorem advance_intCast (x : Chart N) (k : ℤ) :
    (advance x k).s = x.s ∧ (advance x k).w = x.w + k ∧ (advance x k).z = x.z + (k : ZMod N) := by
  have hfloor : ⌊x.s + (k : ℚ)⌋ = k := by
    rw [Int.floor_add_intCast, Int.floor_eq_zero_iff.mpr ⟨x.s_nonneg, x.s_lt_one⟩, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · simp only [advance, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨x.s_nonneg, x.s_lt_one⟩
  · simp only [advance, hfloor]
  · simp only [advance, hfloor]

/-- [formal-checked] **`N` whole turns return the finite face and move the winding by `N`.** -/
theorem advance_modulus (x : Chart N) :
    (advance x (N : ℚ)).s = x.s ∧ (advance x (N : ℚ)).z = x.z ∧ (advance x (N : ℚ)).w = x.w + N := by
  have h := advance_intCast x (N : ℤ)
  have hcast : ((N : ℤ) : ℚ) = (N : ℚ) := by norm_cast
  rw [hcast] at h
  refine ⟨h.1, ?_, h.2.1⟩
  rw [h.2.2]
  simp

/-- [formal-checked] **The finite face `(s, z)` returns exactly at whole multiples of `N` turns.** -/
theorem face_returns_iff (x : Chart N) (a : ℚ) :
    ((advance x a).s = x.s ∧ (advance x a).z = x.z) ↔ ∃ k : ℤ, a = k * N := by
  constructor
  · rintro ⟨hs, hz⟩
    have hfr : Int.fract (x.s + a) = Int.fract x.s := by
      rw [Int.fract_eq_self.mpr ⟨x.s_nonneg, x.s_lt_one⟩]; exact hs
    obtain ⟨m, hm⟩ := Int.fract_eq_fract.mp hfr
    have ha : a = m := by linarith
    subst ha
    have hz' := (advance_intCast x m).2.2
    rw [hz] at hz'
    have hm0 : ((m : ℤ) : ZMod N) = 0 := by
      have := hz'
      exact (add_eq_left.mp this.symm)
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m N).mp hm0
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    ring
  · rintro ⟨k, rfl⟩
    have hcast : ((k : ℚ) * (N : ℚ)) = ((k * N : ℤ) : ℚ) := by push_cast; ring
    rw [hcast]
    have h := advance_intCast x (k * N)
    refine ⟨h.1, ?_⟩
    rw [h.2.2]
    simp

/-- [formal-checked] **No nonzero advance returns the state**: the lift keeps every winding the finite face forgets. -/
theorem advance_eq_self_iff (x : Chart N) (a : ℚ) : advance x a = x ↔ a = 0 := by
  constructor
  · intro h
    have := lift_advance x a
    rw [h] at this
    linarith
  · rintro rfl
    exact advance_zero x

/-- [formal-checked] **Equal finite faces do not erase different windings**: after `N` turns the face is the one it was and
the state is another, told apart by its lift. -/
theorem same_face_different_winding (x : Chart N) (hN : 0 < N) :
    (advance x (N : ℚ)).s = x.s ∧ (advance x (N : ℚ)).z = x.z ∧ advance x (N : ℚ) ≠ x ∧
      lift (advance x (N : ℚ)) = lift x + N := by
  obtain ⟨hs, hz, -⟩ := advance_modulus x
  refine ⟨hs, hz, ?_, lift_advance x N⟩
  intro h
  have := (advance_eq_self_iff x N).mp h
  have : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  contradiction

/-! ## 4. The carried group law -/

/-- [definition] **The carried group law**: the group law of `ℚ × ZMod N` read through `liftCharge`. `add_s`, `add_w` and
`add_z` give it in the chart's own coordinates. -/
instance instAddCommGroup : AddCommGroup (Chart N) := liftCharge.addCommGroup

/-- [definition] The chart `(lift, charge)` as an isomorphism of groups. -/
def liftChargeAddEquiv : Chart N ≃+ ℚ × ZMod N := liftCharge.addEquiv

/-- [formal-checked] The lift of a sum is the sum of the lifts. -/
theorem lift_add (x y : Chart N) : lift (x + y) = lift x + lift y :=
  congrArg Prod.fst (liftChargeAddEquiv.map_add x y)

/-- [formal-checked] The charge of a sum is the sum of the charges. -/
theorem charge_add (x y : Chart N) : charge (x + y) = charge x + charge y :=
  congrArg Prod.snd (liftChargeAddEquiv.map_add x y)

/-- [formal-checked] The phase of a sum: `s₁ + s₂ − c`, `c = ⌊s₁ + s₂⌋`. -/
theorem add_s (x y : Chart N) : (x + y).s = x.s + y.s - ⌊x.s + y.s⌋ := by
  rw [← fract_lift (x + y), lift_add, lift, lift]
  have : (x.w : ℚ) + x.s + (y.w + y.s) = (x.s + y.s) + ((x.w + y.w : ℤ) : ℚ) := by push_cast; ring
  rw [this, Int.fract_add_intCast, Int.fract]

/-- [formal-checked] The winding of a sum: `w₁ + w₂ + c`, the carry `c = ⌊s₁ + s₂⌋` being `0` or `1`. -/
theorem add_w (x y : Chart N) : (x + y).w = x.w + y.w + ⌊x.s + y.s⌋ := by
  rw [← floor_lift (x + y), lift_add, lift, lift]
  have : (x.w : ℚ) + x.s + (y.w + y.s) = (x.s + y.s) + ((x.w + y.w : ℤ) : ℚ) := by push_cast; ring
  rw [this, Int.floor_add_intCast]
  ring

/-- [formal-checked] The residue of a sum: `z₁ + z₂ + c`, the same carry as the winding's. -/
theorem add_z (x y : Chart N) : (x + y).z = x.z + y.z + ((⌊x.s + y.s⌋ : ℤ) : ZMod N) := by
  have h := charge_add x y
  simp only [charge, add_w] at h
  push_cast at h
  linear_combination h

/-- [formal-checked] The carry of a sum of two phases is none or one turn. -/
theorem carry_zero_or_one (x y : Chart N) : ⌊x.s + y.s⌋ = 0 ∨ ⌊x.s + y.s⌋ = 1 := by
  have h0 : (0 : ℤ) ≤ ⌊x.s + y.s⌋ := Int.floor_nonneg.mpr (add_nonneg x.s_nonneg y.s_nonneg)
  have h2 : ⌊x.s + y.s⌋ < 2 := by
    rw [Int.floor_lt]
    have := x.s_lt_one
    have := y.s_lt_one
    push_cast
    linarith
  omega

/-- [definition] **A pure longitudinal turn** by `a`: the state of lift `a` and charge zero. -/
def turn (a : ℚ) : Chart N := liftCharge.symm (a, 0)

/-- [formal-checked] **An advance is the sum with a turn.** -/
theorem advance_eq_add_turn (x : Chart N) (a : ℚ) : advance x a = x + turn a := by
  refine ext_lift_charge ?_ ?_
  · rw [lift_advance, lift_add]
    congr 1
    exact (congrArg Prod.fst (liftCharge.apply_symm_apply (a, (0 : ZMod N)))).symm
  · rw [charge_advance, charge_add]
    have : charge (turn a : Chart N) = 0 :=
      congrArg Prod.snd (liftCharge.apply_symm_apply (a, (0 : ZMod N)))
    rw [this, add_zero]

/-! ## 5. Restriction along a divisor -/

/-- [definition] **Restriction along `M ∣ N`**: the phase and the winding are kept and the transverse residue is read on the
coarser ring. -/
def restrict (h : M ∣ N) (x : Chart N) : Chart M where
  s := x.s
  w := x.w
  z := ZMod.castHom h (ZMod M) x.z
  s_nonneg := x.s_nonneg
  s_lt_one := x.s_lt_one

/-- [formal-checked] Restriction keeps the longitudinal lift. -/
theorem lift_restrict (h : M ∣ N) (x : Chart N) : lift (restrict h x) = lift x := rfl

/-- [formal-checked] Restriction reads the charge on the coarser ring. -/
theorem charge_restrict (h : M ∣ N) (x : Chart N) :
    charge (restrict h x) = ZMod.castHom h (ZMod M) (charge x) := by
  simp only [charge, restrict, map_sub, map_intCast]

/-- [formal-checked] **Restriction commutes with the advance** (the atlas row's first square). -/
theorem restrict_advance (h : M ∣ N) (x : Chart N) (a : ℚ) :
    restrict h (advance x a) = advance (restrict h x) a := by
  refine Chart.ext rfl rfl ?_
  simp only [restrict, advance, map_add, map_intCast]

/-- [formal-checked] **Restriction commutes with the carried addition** (the atlas row's second square). -/
theorem restrict_add (h : M ∣ N) (x y : Chart N) :
    restrict h (x + y) = restrict h x + restrict h y := by
  refine ext_lift_charge ?_ ?_
  · rw [lift_restrict, lift_add, lift_add, lift_restrict, lift_restrict]
  · rw [charge_restrict, charge_add, charge_add, charge_restrict, charge_restrict, map_add]

/-- [definition] Restriction as a homomorphism of the carried groups. -/
def restrictHom (h : M ∣ N) : Chart N →+ Chart M :=
  AddMonoidHom.mk' (restrict h) (restrict_add h)

/-- [formal-checked] Restrictions compose along a chain of divisors. -/
theorem restrict_restrict {L : ℕ} (h₁ : L ∣ M) (h₂ : M ∣ N) (x : Chart N) :
    restrict h₁ (restrict h₂ x) = restrict (h₁.trans h₂) x := by
  refine Chart.ext rfl rfl ?_
  simp only [restrict]
  exact congrFun (congrArg DFunLike.coe (ZMod.castHom_comp h₁ h₂)) x.z

/-! ## 6. Compatible sections over a divisibility chain -/

/-- [definition] **A compatible section** over a chain `N i ∣ N (i + 1)`: each level is the restriction of the next. -/
def Compatible (N : ℕ → ℕ) (hN : ∀ i, N i ∣ N (i + 1)) (x : ∀ i, Chart (N i)) : Prop :=
  ∀ i, restrict (hN i) (x (i + 1)) = x i

/-- [formal-checked] **A common advance keeps a section compatible.** -/
theorem Compatible.advance {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} {x : ∀ i, Chart (N i)}
    (hx : Compatible N hN x) (a : ℚ) : Compatible N hN (fun i => SolenoidChart.advance (x i) a) := by
  intro i
  show restrict (hN i) (SolenoidChart.advance (x (i + 1)) a) = SolenoidChart.advance (x i) a
  rw [restrict_advance, hx i]

/-- [formal-checked] **The levelwise sum of two compatible sections is compatible.** -/
theorem Compatible.add {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} {x y : ∀ i, Chart (N i)}
    (hx : Compatible N hN x) (hy : Compatible N hN y) : Compatible N hN (fun i => x i + y i) := by
  intro i
  show restrict (hN i) (x (i + 1) + y (i + 1)) = x i + y i
  rw [restrict_add, hx i, hy i]

/-- [formal-checked] **A compatible section has one longitudinal lift**: every level carries the phase and the winding of
the first. -/
theorem Compatible.lift_eq {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} {x : ∀ i, Chart (N i)}
    (hx : Compatible N hN x) (i : ℕ) : lift (x i) = lift (x 0) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← ih, ← hx i, lift_restrict]

/-! ## 7. The circle face -/

/-- [formal-checked] Two rationals that differ by a whole multiple of the period are one point of the circle. -/
theorem coe_eq_of_sub_eq_zsmul {𝕜 : Type*} [AddCommGroup 𝕜] {p a b : 𝕜} (k : ℤ) (h : a - b = k • p) :
    (a : AddCircle p) = (b : AddCircle p) := by
  have hab : a = b + k • p := by rw [← h]; abel
  rw [hab, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, add_zero]

/-- [definition] **The circle face of a level**: the total phase `s + z` read in `ℚ / Nℤ`. In turns of the level's own
circle it is the guide's `θ = (s + z)/N`. -/
def phase (x : Chart N) : AddCircle (N : ℚ) := ((x.s + (x.z.val : ℚ) : ℚ) : AddCircle (N : ℚ))

/-- [formal-checked] **The face turns by the advance**: `phase (advance x a) = phase x + a` on the circle `ℚ / Nℤ`. The
carry leaves the phase `s` and enters the residue `z`, and the face does not see the exchange. -/
theorem phase_advance [NeZero N] (x : Chart N) (a : ℚ) :
    phase (advance x a) = phase x + (a : AddCircle (N : ℚ)) := by
  set c : ℤ := ⌊x.s + a⌋ with hc
  have hcast : (((((x.z + (c : ZMod N)).val : ℕ) : ℤ) - c - ((x.z.val : ℕ) : ℤ) : ℤ) : ZMod N) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hcast
  have hkq : (((x.z + (c : ZMod N)).val : ℕ) : ℚ) - c - ((x.z.val : ℕ) : ℚ) = (N : ℚ) * k := by
    have := congrArg (fun n : ℤ => (n : ℚ)) hk
    push_cast at this
    exact this
  unfold phase
  rw [← AddCircle.coe_add]
  refine coe_eq_of_sub_eq_zsmul k ?_
  simp only [advance, Int.fract, ← hc, zsmul_eq_mul]
  linarith

/-- [definition] **The cover of one circle by a finer one**: for `M ∣ N` the identity of the line descends to
`𝕜 / N ℤ → 𝕜 / M ℤ`, the `N/M`-fold cover of the guide. -/
def cover (𝕜 : Type*) [CommRing 𝕜] (h : M ∣ N) : AddCircle (N : 𝕜) →+ AddCircle (M : 𝕜) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (N : 𝕜)) (AddSubgroup.zmultiples (M : 𝕜)) (AddMonoidHom.id 𝕜)
    (by
      obtain ⟨d, rfl⟩ := h
      refine AddSubgroup.zmultiples_le_of_mem ?_
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(d : ℤ), ?_⟩
      simp only [zsmul_eq_mul]
      push_cast
      ring)

/-- [formal-checked] The cover takes the class of a point of the line to its class on the coarser circle. -/
theorem cover_coe (𝕜 : Type*) [CommRing 𝕜] (h : M ∣ N) (t : 𝕜) :
    cover 𝕜 h (t : AddCircle (N : 𝕜)) = (t : AddCircle (M : 𝕜)) := rfl

/-- [formal-checked] **The face of a restriction is the cover of the face**: the levels' circle faces form a compatible
family, so a compatible section of charts is a point of the tower of circles `ℚ / N_i ℤ`. -/
theorem phase_restrict [NeZero N] [NeZero M] (h : M ∣ N) (x : Chart N) :
    cover ℚ h (phase x) = phase (restrict h x) := by
  have hcast : ((((x.z.val : ℕ) : ℤ) - (((ZMod.castHom h (ZMod M) x.z).val : ℕ) : ℤ) : ℤ) : ZMod M) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.castHom_apply, ZMod.cast_eq_val]
    ring
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hcast
  have hkq : ((x.z.val : ℕ) : ℚ) - (((ZMod.castHom h (ZMod M) x.z).val : ℕ) : ℚ) = (M : ℚ) * k := by
    have := congrArg (fun n : ℤ => (n : ℚ)) hk
    push_cast at this
    exact this
  unfold phase
  rw [cover_coe]
  refine coe_eq_of_sub_eq_zsmul k ?_
  simp only [restrict, zsmul_eq_mul]
  linarith

/-! ## 8. The completed solenoid's translation flow has no nonzero return time -/

/-- [proved-derived; formal-checked] **Along unbounded moduli only `t = 0` returns on every circle.** If `t` is a whole
multiple of `n` for every `n` in an unbounded set of moduli, then `t = 0`: a modulus beyond `|t|` leaves no nonzero
multiple that small. No divisibility between the moduli is used. -/
theorem no_return_of_unbounded {S : Set ℕ} (hS : ∀ B : ℕ, ∃ n ∈ S, B < n) {t : ℝ}
    (h : ∀ n ∈ S, (t : AddCircle ((n : ℕ) : ℝ)) = 0) : t = 0 := by
  obtain ⟨B, hB⟩ := exists_nat_gt |t|
  obtain ⟨n, hnS, hBn⟩ := hS B
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).mp (h n hnS)
  by_contra ht
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hk
    exact ht hk.symm
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    exact_mod_cast this
  have hn : (B : ℝ) < n := by exact_mod_cast hBn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have habs : |t| = |(k : ℝ)| * n := by rw [← hk, zsmul_eq_mul, abs_mul, Nat.abs_cast]
  have := mul_le_mul_of_nonneg_right h1 hn0
  linarith

/-- [proved-derived; formal-checked] **The full additive solenoid** (every positive modulus): a time that returns on every
circle `ℝ / nℤ` is zero. The guide's argument reads level `1` first; a modulus beyond `|t|` suffices. -/
theorem no_return_all_moduli {t : ℝ} (h : ∀ n : ℕ, 0 < n → (t : AddCircle ((n : ℕ) : ℝ)) = 0) : t = 0 :=
  no_return_of_unbounded (S := {n | 0 < n}) (fun B => ⟨B + 1, Nat.succ_pos B, Nat.lt_succ_self B⟩) h

/-- [proved-derived; formal-checked] **A prime-power chain** `1, p, p², …` with `p ≥ 2`: a time that returns on every
circle `ℝ / pᵏℤ` is zero. -/
theorem no_return_prime_power_chain {p : ℕ} (hp : 2 ≤ p) {t : ℝ}
    (h : ∀ k : ℕ, (t : AddCircle ((p ^ k : ℕ) : ℝ)) = 0) : t = 0 := by
  refine no_return_of_unbounded (S := Set.range fun k : ℕ => p ^ k) ?_ ?_
  · intro B
    exact ⟨p ^ B, ⟨B, rfl⟩, Nat.lt_pow_self hp⟩
  · rintro n ⟨k, rfl⟩
    exact h k

/-- [definition] **The inverse limit of the circles over a divisibility chain**: families `x i ∈ ℝ / N_i ℤ` with each level
the cover of the next. Over the full divisibility order this is the additive solenoid; here it is one cofinal chain's. -/
def Solenoid (N : ℕ → ℕ) (hN : ∀ i, N i ∣ N (i + 1)) : Type :=
  {x : ∀ i, AddCircle ((N i : ℕ) : ℝ) // ∀ i, cover ℝ (hN i) (x (i + 1)) = x i}

/-- [definition] **The translation flow**: every level turns by the same real time `t`. -/
def flow {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} (t : ℝ) (x : Solenoid N hN) : Solenoid N hN :=
  ⟨fun i => x.1 i + (t : AddCircle ((N i : ℕ) : ℝ)), fun i => by
    rw [map_add, x.2 i, cover_coe]⟩

/-- [formal-checked] The flow is an action of the line: time zero is no move and times add. -/
theorem flow_zero {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} (x : Solenoid N hN) : flow 0 x = x := by
  apply Subtype.ext
  funext i
  simp [flow]

/-- [formal-checked] Two flows compose into the flow by the sum of their times. -/
theorem flow_flow {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} (x : Solenoid N hN) (s t : ℝ) :
    flow t (flow s x) = flow (s + t) x := by
  apply Subtype.ext
  funext i
  simp [flow, add_assoc]

/-- [proved-derived; formal-checked] **The completed solenoid's translation flow has no nonzero return time**: over a chain
whose moduli are unbounded, the flow by `t` fixes a point only for `t = 0`. Each finite face returns after its own `N`
turns (`face_returns_iff`); the limit of the faces never does. -/
theorem flow_eq_self_iff {N : ℕ → ℕ} {hN : ∀ i, N i ∣ N (i + 1)} (hunb : ∀ B : ℕ, ∃ i, B < N i)
    (x : Solenoid N hN) (t : ℝ) : flow t x = x ↔ t = 0 := by
  constructor
  · intro h
    refine no_return_of_unbounded (S := Set.range N) ?_ ?_
    · intro B
      obtain ⟨i, hi⟩ := hunb B
      exact ⟨N i, ⟨i, rfl⟩, hi⟩
    · rintro n ⟨i, rfl⟩
      have := congrFun (congrArg Subtype.val h) i
      simp only [flow] at this
      exact add_eq_left.mp this
  · rintro rfl
    exact flow_zero x

end Holonics.Geometry.SolenoidChart
