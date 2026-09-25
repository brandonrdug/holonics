import Holonics.Objects.Ratio
import Holonics.Aeon.Clock.Reading

/-!
# Holarchy.Receipt: receipts and `Ratio.between`

[definition] Object 10 of `docs/ELEMENTARY_OBJECTS.md`. A **receipt** is a field of readings over a
partition into regions, each region's reading carried in its own frame and clock (`Receipt`). Each
reading has a **clock exponent** `k` (`clockExponent`): `1` for a rate (per tick), `0` for a count
or a phase, `−1` for a duration. The frame of a region is a transport into the declared common
frame; its clock is its tick rate against the common clock. The common reading
(`Receipt.common`) is the framed reading carried to the common clock: under a change of clock
`t' = a t + b` a rate becomes `r/a` while a count is unchanged, so a clock unit `c` scales a
reading of exponent `k` by `c^(−k)` (`Receipt.common_reclock`).

Frames are group-valued transports. In the scalar chart (`Receipt`) the group is `𝕜ˣ` acting on
`𝕜`; in the gauge chart (`GaugeReceipt`) readings and frames lie in any group `G`, possibly
noncommutative, and the frame acts by left transport.

`Ratio.between a b` compares two receipts region by region, **after** their common transport, as
the undivided pair `(b : a)` of `Geometry/CrossRatio.RatioPresentation` (`between`): "`b` per `a`",
both operands kept, no division performed. In the gauge chart it is the relative transport
`a⁻¹ b` (`betweenGauge`).

[proved-derived; formal-checked]

* **Frame invariance.** A common change of frame scales both transported readings of a region by
  one unit, so `between` changes by the common scale (`between_reframe`) and is projectively
  unchanged (`between_reframe_projectivelyEq`); its log fibre is exactly unchanged
  (`logFibre_between_reframe`). In the gauge chart a common left change of frame leaves
  `between` exactly unchanged in any group (`betweenGauge_reframe`).
* **Clock invariance by kind.** A common change of clock scales a region's pair by `c^(−k)` when
  both readings have the clock exponent `k` (`between_reclock`): rates compare projectively
  across clocks, and counts and phases are exactly clock-invariant
  (`between_reclock_count`). Comparing a rate with a count is not clock-invariant
  (`rate_against_count_is_clock_dependent`).
* **Composition.** `between a b` followed by `between b c` is **exactly** `between a c` scaled by the
  middle common reading (`between_comp`); so through an admitted middle reading it is projectively
  `between a c` and admitted exactly when it is (`between_comp_projectivelyEq`), and through a zero
  middle reading it is the undetermined pair `(0 : 0)` (`between_comp_through_zero`), which
  `Aeon/Clock/Reading.undetermined_breaks_transitivity` shows is not a comparison. In the log
  chart the lifts add (`between_log_comp`) and two lifts differ by whole turns
  (`between_log_winding`). In the gauge chart `between` composes exactly, noncommutatively as well
  (`betweenGauge_comp`).

[counterexample; formal-checked] Comparing raw readings before the common transport is not a
comparison: one physical reading carried in frames `2` and `1` reads `(2 : 1)` raw while `between`
returns `(2 : 2)` (`raw_comparison_is_frame_dependent`). A zero reading has no logarithm against a
nonzero one (`between_refuses_log`).

[open] A receipt's provenance fields of §10 — its source and receiver, its locus and grain as
cells of the complex, the per-region distribution and variability of its readings over the
region's own ticks joined to the flux along the region's interface, and the unresolved fibre — are
carried by `Holarchy/Reception.InteractionReturn` (unresolved fibre, boundary bond) and
`Holarchy/View.view` (faces, interface flux and epochs per receiver tick), not by `Receipt` itself;
joining them into one receipt object is owed (#62).
-/

noncomputable section

namespace Holonics.Receiver

open Holonics.Objects.Ratio
open Holonics.Aeon.Clock.Reading (Admitted)

/-! ## 1. Receipts in the scalar chart -/

section Receipt

variable {𝕜 : Type*} [Field 𝕜] {Region State : Type*}

/-- [definition] **A receipt**: a reading per region, its clock exponent, and the region's frame and
clock as units transporting it into the declared common frame and clock. -/
structure Receipt (𝕜 : Type*) [Field 𝕜] (Region : Type*) where
  reading : Region → 𝕜
  clockExponent : Region → ℤ
  frame : Region → 𝕜ˣ
  clock : Region → 𝕜ˣ

/-- [definition] A region's reading transported into the common frame and carried to the common
clock according to its clock exponent. -/
def Receipt.common (a : Receipt 𝕜 Region) (r : Region) : 𝕜 :=
  (a.frame r : 𝕜) * a.reading r * (((a.clock r) ^ (-a.clockExponent r) : 𝕜ˣ) : 𝕜)

/-- [definition] A common change of frame: the region's frame composed with `k r`. -/
def Receipt.reframe (k : Region → 𝕜ˣ) (a : Receipt 𝕜 Region) : Receipt 𝕜 Region :=
  { a with frame := fun r => k r * a.frame r }

/-- [definition] A common change of clock: the region's clock composed with `c r`. -/
def Receipt.reclock (c : Region → 𝕜ˣ) (a : Receipt 𝕜 Region) : Receipt 𝕜 Region :=
  { a with clock := fun r => c r * a.clock r }

theorem Receipt.common_reframe (k : Region → 𝕜ˣ) (a : Receipt 𝕜 Region) (r : Region) :
    (a.reframe k).common r = (k r : 𝕜) * a.common r := by
  simp only [Receipt.common, Receipt.reframe, Units.val_mul]; ring

/-- [proved-derived; formal-checked] **A change of clock scales a reading by `c^(−k)`**: a rate
(`k = 1`) is divided by the clock ratio, a count or phase (`k = 0`) is unchanged. -/
theorem Receipt.common_reclock (c : Region → 𝕜ˣ) (a : Receipt 𝕜 Region) (r : Region) :
    (a.reclock c).common r = (((c r) ^ (-a.clockExponent r) : 𝕜ˣ) : 𝕜) * a.common r := by
  simp only [Receipt.common, Receipt.reclock, mul_zpow, Units.val_mul]; ring

/-- [definition] **A receipt law**: how a participant's state is read, region by region, with each
reading's clock exponent and each region's frame and clock. -/
structure ReceiptLaw (𝕜 : Type*) [Field 𝕜] (State Region : Type*) where
  read : Region → State → 𝕜
  clockExponent : Region → ℤ
  frame : Region → 𝕜ˣ
  clock : Region → 𝕜ˣ

/-- [definition] The receipt a law returns on a state. -/
def ReceiptLaw.receive (L : ReceiptLaw 𝕜 State Region) (s : State) : Receipt 𝕜 Region :=
  ⟨fun r => L.read r s, L.clockExponent, L.frame, L.clock⟩

end Receipt

/-! ## 2. `Ratio.between`: the undivided pair after the common transport -/

section Between

variable {𝕜 : Type*} [Field 𝕜] {Region : Type*}

/-- [definition] **`Ratio.between a b`**: in each region, `b` per `a`, both transported into the
common frame and clock and kept as the undivided pair `(b : a)`. -/
def between (a b : Receipt 𝕜 Region) (r : Region) : RatioPresentation 𝕜 :=
  ⟨b.common r, a.common r⟩

/-- [definition] **The ratio's own composition**: follow the pair `p` by the pair `q`, the diagonal
block transport of `Geometry/CrossRatio` with `q`'s entries. -/
def followRatio (p q : RatioPresentation 𝕜) : RatioPresentation 𝕜 :=
  RatioPresentation.blockTransport q.num 0 0 q.den p

theorem followRatio_eq (p q : RatioPresentation 𝕜) :
    followRatio p q = ⟨q.num * p.num, q.den * p.den⟩ := by
  simp [followRatio, RatioPresentation.blockTransport]

/-- [proved-derived; formal-checked] `between` keeps both operands. -/
theorem between_operands (a b : Receipt 𝕜 Region) (r : Region) :
    (between a b r).num = b.common r ∧ (between a b r).den = a.common r := ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] **A common change of frame scales the pair by one unit.** -/
theorem between_reframe (k : Region → 𝕜ˣ) (a b : Receipt 𝕜 Region) (r : Region) :
    between (a.reframe k) (b.reframe k) r = (between a b r).scale (k r : 𝕜) := by
  simp [between, RatioPresentation.scale, Receipt.common_reframe]

/-- [proved-derived; formal-checked] **So `between` is invariant under a common change of frame**,
as an undivided pair up to its projective scale by a unit. -/
theorem between_reframe_projectivelyEq (k : Region → 𝕜ˣ) (a b : Receipt 𝕜 Region) (r : Region) :
    (between (a.reframe k) (b.reframe k) r).ProjectivelyEq (between a b r) ∧
      (Admitted (between a b r) → Admitted (between (a.reframe k) (b.reframe k) r)) := by
  rw [between_reframe]
  exact ⟨ratioPresentation_projectivelyEq_scale _ _, fun h => h.scale (k r).ne_zero⟩

/-- [proved-derived; formal-checked] **A common change of clock scales the pair by `c^(−k)`** when
both readings of the region have the clock exponent `k`. -/
theorem between_reclock (c : Region → 𝕜ˣ) (a b : Receipt 𝕜 Region) (r : Region)
    (hk : a.clockExponent r = b.clockExponent r) :
    between (a.reclock c) (b.reclock c) r =
      (between a b r).scale ((((c r) ^ (-a.clockExponent r) : 𝕜ˣ) : 𝕜)) := by
  simp only [between, RatioPresentation.scale, Receipt.common_reclock, hk]

/-- [proved-derived; formal-checked] So two rates, or any two readings of one kind, compare
projectively across clocks. -/
theorem between_reclock_projectivelyEq (c : Region → 𝕜ˣ) (a b : Receipt 𝕜 Region) (r : Region)
    (hk : a.clockExponent r = b.clockExponent r) :
    (between (a.reclock c) (b.reclock c) r).ProjectivelyEq (between a b r) := by
  rw [between_reclock c a b r hk]; exact ratioPresentation_projectivelyEq_scale _ _

/-- [proved-derived; formal-checked] **Counts and phases are clock-invariant**: two readings of
clock exponent `0` compare identically under any change of clock. -/
theorem between_reclock_count (c : Region → 𝕜ˣ) (a b : Receipt 𝕜 Region) (r : Region)
    (ha : a.clockExponent r = 0) (hb : b.clockExponent r = 0) :
    between (a.reclock c) (b.reclock c) r = between a b r := by
  rw [between_reclock c a b r (ha.trans hb.symm), ha]
  ext <;> simp [RatioPresentation.scale]

/-- [counterexample; formal-checked] **A rate against a count is not clock-invariant.** A rate `1`
and a count `1` in one region compare as `(1 : 1)`; halving the clock rate of the region makes the
rate `2` and leaves the count, so the comparison becomes `(1 : 2)`, not projectively `(1 : 1)`. -/
theorem rate_against_count_is_clock_dependent :
    let a : Receipt ℚ Unit := ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1⟩
    let b : Receipt ℚ Unit := ⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => 1⟩
    let c : Unit → ℚˣ := fun _ => Units.mk0 (1 / 2) (by norm_num)
    between a b () = ⟨1, 1⟩ ∧ between (a.reclock c) (b.reclock c) () = ⟨1, 2⟩ ∧
      ¬ (between (a.reclock c) (b.reclock c) ()).ProjectivelyEq (between a b ()) := by
  intro a b c
  have h1 : between a b () = ⟨1, 1⟩ := by
    ext <;> simp [between, Receipt.common, a, b]
  have h2 : between (a.reclock c) (b.reclock c) () = ⟨1, 2⟩ := by
    ext <;> simp [between, Receipt.common, Receipt.reclock, a, b, c]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  simp [RatioPresentation.ProjectivelyEq]

/-- [proved-derived; formal-checked] **Composition is exact**: `between a b` followed by
`between b c` is `between a c` scaled by the middle common reading `b.common r`, with no
hypothesis. -/
theorem between_comp (a b c : Receipt 𝕜 Region) (r : Region) :
    followRatio (between a b r) (between b c r) = (between a c r).scale (b.common r) := by
  rw [followRatio_eq]
  ext <;> simp only [between, RatioPresentation.scale]
  ring

/-- [proved-derived; formal-checked] **Through an admitted middle reading the composite is
`between a c`**: projectively equal to it, and admitted exactly when it is. -/
theorem between_comp_projectivelyEq (a b c : Receipt 𝕜 Region) (r : Region)
    (hb : b.common r ≠ 0) :
    (followRatio (between a b r) (between b c r)).ProjectivelyEq (between a c r) ∧
      (Admitted (between a c r) ↔ Admitted (followRatio (between a b r) (between b c r))) := by
  rw [between_comp]
  refine ⟨ratioPresentation_projectivelyEq_scale _ _, fun h => h.scale hb, fun h => ?_⟩
  rcases h with h | h
  · exact Or.inl (right_ne_zero_of_mul h)
  · exact Or.inr (right_ne_zero_of_mul h)

/-- [counterexample; formal-checked] **Through a zero middle reading the composite is the
undetermined pair `(0 : 0)`**, retained as such rather than read as a ratio. -/
theorem between_comp_through_zero (a b c : Receipt 𝕜 Region) (r : Region)
    (hb : b.common r = 0) :
    followRatio (between a b r) (between b c r) = ⟨0, 0⟩ := by
  simp [followRatio_eq, between, hb]

/-- [counterexample; formal-checked] **Raw readings are not comparable across frames.** One
common reading `2` carried by a receipt in frame `2` (raw `1`) and by one in frame `1` (raw `2`):
the raw pair `(2 : 1)` is not the identity comparison, while `between` returns `(2 : 2)`. -/
theorem raw_comparison_is_frame_dependent :
    let a : Receipt ℚ Unit := ⟨fun _ => 1, fun _ => 0, fun _ => Units.mk0 2 two_ne_zero, fun _ => 1⟩
    let b : Receipt ℚ Unit := ⟨fun _ => 2, fun _ => 0, fun _ => 1, fun _ => 1⟩
    ¬ (⟨b.reading (), a.reading ()⟩ : RatioPresentation ℚ).ProjectivelyEq ⟨1, 1⟩ ∧
      between a b () = ⟨2, 2⟩ := by
  intro a b
  refine ⟨?_, ?_⟩
  · simp [RatioPresentation.ProjectivelyEq, a, b]
  · ext <;> simp [between, Receipt.common, a, b]

end Between

/-! ## 3. The log chart: lifts add, windings are kept -/

section LogChart

variable {Region : Type*}

/-- [proved-derived; formal-checked] **In the log chart the lifts compose**: a lift of `b per a`
plus a lift of `c per b` is a lift of `c per a` (`Objects/Ratio.logFibre_comp`). -/
theorem between_log_comp (a b c : Receipt ℂ Region) (r : Region) {ℓ₁ ℓ₂ : ℂ}
    (h₁ : ℓ₁ ∈ logFibre (between a b r)) (h₂ : ℓ₂ ∈ logFibre (between b c r)) :
    ℓ₁ + ℓ₂ ∈ logFibre (between a c r) := by
  rw [add_comm]
  exact logFibre_comp (a := c.common r) (b := b.common r) (c := a.common r) h₂ h₁

/-- [proved-derived; formal-checked] **The winding is kept**: two lifts of one comparison differ by
whole turns (`Objects/Ratio.logFibre_torsor`). -/
theorem between_log_winding (a b : Receipt ℂ Region) (r : Region) (ha : a.common r ≠ 0)
    {ℓ ℓ' : ℂ} (hℓ : ℓ ∈ logFibre (between a b r)) :
    ℓ' ∈ logFibre (between a b r) ↔ ∃ n : ℤ, ℓ' = ℓ + n * (2 * Real.pi * Complex.I) :=
  logFibre_torsor ha hℓ

/-- [proved-derived; formal-checked] **The log fibre is unchanged by a common change of frame**
(`Objects/Ratio.logFibre_scale`). -/
theorem logFibre_between_reframe (k : Region → ℂˣ) (a b : Receipt ℂ Region) (r : Region) :
    logFibre (between (a.reframe k) (b.reframe k) r) = logFibre (between a b r) := by
  rw [between_reframe]; exact logFibre_scale _ (k r).ne_zero

/-- [counterexample; formal-checked] **A zero reading refuses the logarithm** against a nonzero one
(`Objects/Ratio.logFibre_eq_empty_of_den_eq_zero`). -/
theorem between_refuses_log (a b : Receipt ℂ Region) (r : Region) (ha : a.common r = 0)
    (hb : b.common r ≠ 0) : logFibre (between a b r) = ∅ :=
  logFibre_eq_empty_of_den_eq_zero ha hb

end LogChart

/-! ## 4. The gauge chart: group-valued readings and frame transports -/

section Gauge

variable {G Region : Type*} [Group G]

/-- [definition] **A gauge receipt**: a group-valued reading per region and the region's frame, a
transport in the same (possibly noncommutative) group into the common frame. -/
structure GaugeReceipt (G Region : Type*) where
  reading : Region → G
  frame : Region → G

/-- [definition] The reading transported into the common frame: `frame · reading`. -/
def GaugeReceipt.common (a : GaugeReceipt G Region) (r : Region) : G := a.frame r * a.reading r

/-- [definition] A common left change of frame. -/
def GaugeReceipt.reframe (k : Region → G) (a : GaugeReceipt G Region) : GaugeReceipt G Region :=
  ⟨a.reading, fun r => k r * a.frame r⟩

/-- [definition] `between` on unit-valued readings: `a⁻¹ b`, the relative transport `Ĝ_(b←a)`. -/
def betweenGauge (a b : Region → G) (r : Region) : G := (a r)⁻¹ * b r

/-- [proved-derived; formal-checked] **Invariant under a common left change of frame**, in any
group, applied to the transported readings. -/
theorem betweenGauge_reframe (k : Region → G) (a b : GaugeReceipt G Region) (r : Region) :
    betweenGauge (a.reframe k).common (b.reframe k).common r =
      betweenGauge a.common b.common r := by
  simp [betweenGauge, GaugeReceipt.common, GaugeReceipt.reframe, mul_assoc]

/-- [proved-derived; formal-checked] **Composes exactly**: `(a⁻¹ b)(b⁻¹ c) = a⁻¹ c`. -/
theorem betweenGauge_comp (a b c : Region → G) (r : Region) :
    betweenGauge a b r * betweenGauge b c r = betweenGauge a c r := by
  simp [betweenGauge, mul_assoc]

/-- [counterexample; formal-checked] **Frames do not commute in general**: in the permutations of
three points, transporting by a transposition and comparing is not transporting after comparing
when the frames act on different sides. -/
theorem gauge_frames_do_not_commute :
    ∃ k a : Equiv.Perm (Fin 3), k * a ≠ a * k := by
  refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, fun h => ?_⟩
  have := congrArg (fun f : Equiv.Perm (Fin 3) => f 0) h
  simp [Equiv.swap_apply_of_ne_of_ne] at this

end Gauge

end Holonics.Receiver
