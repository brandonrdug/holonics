import Holonics.Geometry.PhaseCarry
import HolonicsResearch.Geometry.Crystallographic
import HolonicsResearch.Geometry.RingClosure
import HolonicsResearch.Transport.SerialChainJacobian

/-!
# The Cayley coordinate charts a turn: its clock map, its checked closure and its lifted winding

The #410 box reads: "Phase, action and clock binding: the Cayley coordinate versus the turn rate; the finite action
and its clock map; lifted winding with checked joint closure (`Geometry/PhaseCarry`)." The retired Rust
`RationalPhase { parameter, extra_turns }`
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics/src/geometry/screw.rs)) holds a
rational Cayley half-angle parameter and a declared count of extra whole turns per elementary passage:
`chart_winding(period)` reads the polygon winding of the powers of the Cayley point only after checking that the
`period`-th power returns to `1`, `lifted_winding(period)` returns `polygon + period · extra_turns`, and
`closes_after(period)` checks the return at a positive period. The winding guide
(`docs/WINDING_CARRY_AND_PLACEMENT.md` §1, "helix = circle + carry") says: "`parameter` is a tangent half-angle, not
a turn count or rational angular rate. Its `chart_winding`/`lifted_winding` require a separately checked finite
closure. A rational Cayley point need not close at any finite period." `Transport/SerialChainJacobian` closes its
"What is not claimed" with "the lifted winding (the Rust `RationalPhase`'s `extra_turns`) is not carried here". This
module carries it, on the plane of one turn.

Sources: the box; the winding guide's paragraph above and `docs/HELICAL_GEOMETRY.md` ("`lifted_winding` and
`closes_after` check a supplied finite period, which a general rational Cayley point need not possess"); the record of
September 20, `2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md` ("Quarter turns
with zero extra turns close in four steps with winding 1; one additional full turn per passage gives winding 5"); the
record of September 21, `2026-09-21_THE_HELICAL_PAIR_INTERACTION_IS_THE_HNN_SITE_AND_PHASE_CARRIES_CONTEXT.md`,
obligation 3 ("`RationalPhase` chart/lifted winding and `closes_after`, joined to `phaseTransport`"). Atlas rows
served: `phase.rational-phase-winding`, `chain.cayley-z-chart`, `chain.cayley-rate` and `frame.cayley-rotations`.
Consumed: `winding.niven-star-values` (`Geometry/Crystallographic.niven_values`), `lock.rings-close-at-lcm`
(`Geometry/RingClosure.nsmul_diag_eq_zero_iff`), `winding.odometer` and `ratio.div-rem`
(`Geometry/PhaseCarry.odometer_iterate`, `phase_add_winding`). Read beside `aeon.pairing` and
`aeon.concatenation-carry`: a reading is whole windings plus an open phase, and readings add with the carry.

The Cayley point of the half-angle parameter `q` is `z(q) = (1 + iq)/(1 − iq)` (`cayleyPoint`) and its turn is
`θ(q) = 2 arctan q` (`turnAngle`). The parameter `q` is a chart of the turn: it is neither a count of turns nor a rate.

[proved-standard; formal-checked] What is proved, classical.

1. **The Cayley point and its turn.** `z(q) = (1 − q²)/(1 + q²) + i·2q/(1 + q²)` (`cayleyPoint_eq_chart`,
   `cayleyPoint_re`, `cayleyPoint_im`), and for rational `q` these are the owner's `cayleyCos q`, `cayleySin q` cast
   to `ℝ` (`cayleyPoint_ratCast_re`, `cayleyPoint_ratCast_im`). `z(q) = exp(iθ(q))` (`cayleyPoint_eq_exp`, from
   `SerialChainJacobian.cos_two_arctan`, `sin_two_arctan`), so `|z(q)| = 1` (`norm_cayleyPoint`,
   `cayleyPoint_ne_zero`); `θ(q) ∈ (−π, π)` (`turnAngle_mem_Ioo`) is the principal argument of `z(q)`
   (`arg_cayleyPoint`). Half-angle addition, the owner's `cayleyRot_mul` at `n = 1` read on the complex plane:
   `z(s) z(t) = z((s + t)/(1 − st))` for `st ≠ 1` (`cayleyPoint_mul`). The values `z(0) = 1`, `z(1) = i`,
   `z(−1) = −i` (`cayleyPoint_zero`, `cayleyPoint_one`, `cayleyPoint_neg_one`) and `θ(1) = π/2`, `θ(−1) = −π/2`
   (`turnAngle_one`, `turnAngle_neg_one`).
2. **The Cayley coordinate against the turn rate.** `dθ/dq = 2/(1 + q²)`, the owner's `angularRate 1 q`
   (`hasDerivAt_turnAngle`). Along a uniform parameter clock `q(t) = q₀ + vt` the turn rate is `2v/(1 + q(t)²)`
   (`clockRate`, `hasDerivAt_turnAngle_clock`), and for `v ≠ 0` it is not constant: it reads `2v` where `q(t) = 0`
   and `v` where `q(t) = 1` (`clockRate_ne`). Doubling the parameter does not double the turn: `θ(2) ≠ 2θ(1)`
   (`turnAngle_two_ne`), since `2θ(1) = π` and `θ(2) < π`.
3. **The clock map of the finite action.** `ℤ` acts by powers, `z(q)^k = exp(ikθ(q))` (`cayleyPoint_zpow`,
   `cayleyPoint_pow`, `cayleyPoint_zpow_add`). The lifted phase `kθ(q)/(2π)`, in turns (`liftedPhase`), is its
   floor, the completed turns (`completedTurns`), plus an open phase in `[0, 1)` (`liftedPhase_eq`), and the circle
   reads the open phase alone: `z(q)^k = exp(2πi·fract(kθ(q)/(2π)))` (`cayleyPoint_zpow_fract`). The lifted phase
   is additive in the count (`liftedPhase_add`), and the completed turns add with a carry of `0` or `1`
   (`turnCarry`, `completedTurns_add`, `turnCarry_mem`), the real-lift counterpart of the owner's
   `PhaseCarry.winding_add` and `carry_le_one`.
4. **Checked closure.** `z(q)^n = 1` iff `nθ(q) ∈ 2πℤ` (`cayleyPoint_pow_eq_one_iff`). For rational `q`, some
   `n ≥ 1` has `z(q)^n = 1` iff `q ∈ {0, 1, −1}` (`ratCast_closes_iff`): a closing `z(q)` has `θ(q) = rπ` with `r`
   rational and `cos θ(q) = cayleyCos q` rational, so Niven's values (`Crystallographic.niven_values`) put
   `2 cayleyCos q` in `{−2, −1, 0, 1, 2}`. The values `±1` ask `(3q)² = 3` or `q² = 3`, which no rational meets
   (`not_sq_eq_three`), `−2` is never reached, and `2`, `0` give `q = 0`, `q = ±1` (`eq_of_two_cayleyCos_mem`). The
   test of a declared period: `z(q)^n = 1` iff `n = 0`, or `q = 0`, or `4 ∣ n` with `q = ±1`
   (`ratCast_pow_eq_one_iff`); the minimal periods are `1` at `q = 0` and `4` at `q = ±1`
   (`orderOf_cayleyPoint_zero`, `orderOf_cayleyPoint_one`, `orderOf_cayleyPoint_neg_one`). The 3-4-5 point never
   closes: `z(½) = (3 + 4i)/5` (`cayleyPoint_half`, `cayleyCos_half`) and `z(½)^n ≠ 1` for every `n ≥ 1`
   (`cayleyPoint_half_never_closes`).

[proved-derived; formal-checked] What is proved as the house's statement of the Rust `RationalPhase` and its joins.

5. **The lifted winding at a checked closure.** The polygon winding, the principal step angles of the powers summed
   in turns (`polygonWinding`), is `nθ(q)/(2π)` (`polygonWinding_eq`: each step turns by `arg z(q) = θ(q)`), and it
   is an integer exactly at a closure (`pow_eq_one_iff_polygonWinding`); it reads `0` at `q = 0` and `±n/4` at
   `q = ±1` (`polygonWinding_zero`, `polygonWinding_one`, `polygonWinding_neg_one`). With `e` extra whole turns per
   passage, the lifted winding `w + ne` (`liftedWinding`) is the turns of the lifted passage angle,
   `n(θ + 2πe)/(2π)` (`liftedWinding_eq`), additive over periods (`liftedWinding_add`) and an integer exactly at a
   closure (`pow_eq_one_iff_liftedWinding`). The Cayley point cannot see `e`, `exp(i(θ + 2πe)) = z(q)`
   (`exp_liftedAngle`), while the lifted winding separates every two values of `e` at a positive period
   (`liftedWinding_extra_injective`): the extra turns are the carry the circle forgets. The Rust reading with its
   refusal is `checkedWinding q e n : Option ℤ`, which returns `some w` iff `n ≥ 1`, `z(q)^n = 1` and `w` is the
   lifted winding (`checkedWinding_eq_some_iff`, `checkedWinding_isSome_iff`), and the Rust `closes_after` is
   `closesAfter` (`closesAfter_iff`); both are computable on `ℚ`, and the controls at integer parameters evaluate
   by `decide`. The Rust controls hold:
   `checkedWinding 1 0 4 = some 1`, `checkedWinding 1 1 4 = some 5`, `checkedWinding 0 0 1 = some 0` and
   `checkedWinding 1 1 3 = none` (`checkedWinding_quarter`, `checkedWinding_quarter_extra`, `checkedWinding_still`,
   `checkedWinding_quarter_three`), with `checkedWinding (−1) 0 4 = some (−1)` (`checkedWinding_neg_quarter`) and
   `closesAfter ½ n = false` for every `n` (`closesAfter_half`).
6. **The rational turn on the owner's circle.** For the rational turn `p/m` (`rationalTurn p m = exp(2πi·p/m)`),
   `k` passages lift to `kp/m = winding m (kp) + phase m (kp)/m` (`rationalLift_eq`, from
   `PhaseCarry.phase_add_winding`), whose floor is the owner's `winding m (kp)` (`rationalLift_floor`), and the
   circle reads the owner's `phase m (kp)`: `(e^(2πi·p/m))^k = e^(2πi·phase m (kp)/m)` (`rationalTurn_pow`). The
   Cayley quarter turn is the rational turn `1/4` (`cayleyPoint_one_eq_rationalTurn`), and its clock map is the
   owner's odometer on the circle of four steps: `z(1)^k` reads `phase 4 k`, its completed turns are `winding 4 k`,
   and `odometer 4` iterated `k` times from `(0, 0)` reads `(phase 4 k, winding 4 k)` (`quarterTurn_clock`, from
   `PhaseCarry.odometer_iterate`).
7. **Joint closure.** The phases of a finite family close together at `n` iff their orders tick together on
   `Π i, ZMod (ord i)` (`pow_eq_one_iff_diag`), so iff the closing `lcm_i ord i` divides `n` (`joint_closure_iff`,
   through `RingClosure.nsmul_diag_eq_zero_iff`); for two, iff `lcm(ord x, ord y) ∣ n` (`closing_pair`,
   `pair_closure_iff`), read for Cayley points (`cayleyPoint_joint_iff`) and for rational turns in lowest
   terms, whose orders are their denominators (`orderOf_rationalTurn`, through Mathlib's
   `isPrimitiveRoot_exp_of_coprime`; `rationalTurn_joint_iff`). The test is a divisibility of naturals and evaluates
   by `decide`. The Cayley quarter turn and the sixth turn close together at the multiples of `12` and only there
   (`quarter_sixth_joint_iff`, `quarter_sixth_closes`), and the declared joint period `6` is refused
   (`quarter_sixth_refused`): `z(1)^6 = −1` (`cayleyPoint_one_pow_six`).

What is not claimed. A Cayley point over a number field other than `ℚ`, where other roots of unity have Cayley charts
(over `ℚ(√3)` the parameter `1/√3` turns by `π/3` and closes at `6`), is not treated. The three-dimensional rotation's
lifted winding (`SerialChainJacobian.cayleyRot` about a general axis) is not stated, and neither is the join to
`Transport/HelicalPairInteraction.phaseTransport` that obligation 3 of the September 21 record names: on the
commutative circle that transport is the identity, and its noncommuting instance needs the three-dimensional chart.
The polygon windings of non-closing orbits (the Rust endpoint discrepancy) are not read, beyond the completed turns
and open phase of item 3, which every count has. The screw advance along the axis is not carried. A rational turn's
reduction to lowest terms is item 7's hypothesis, not derived. The carry of item 3 is the floor cocycle of the
universal cover `0 → ℤ → ℝ → S¹ → 0` that the winding guide names, read beside the owner's natural-number carry; the
analytic windings that `PhaseCarry` sets outside its scope are not otherwise extended.

The computational object is the helical pair interaction read on one turning member: its navigator's clock is the
Cayley half-angle parameter, the circle is the face that a contact reads, and the helix keeps the winding as the carry
that face forgets. A uniform tick of the parameter is not a uniform turn: two members ticked by one parameter clock
`v` turn at `2v/(1 + q_a²)` and `2v/(1 + q_b²)`, which differ unless `q_a² = q_b²`. Of the winding guide's six
general objects it touches the helix (the circle chart, its clock map, its completed turns and the lifted winding
with its extra turns) and the cell holonomy (the checked closure of a declared period, and the joint closure of
several phases at the least common multiple of their periods); the pair, faces and placement, the tube and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.CayleyTurnClock

open Complex
open scoped Real
open Holonics.Transport.SerialScrewChain (cayleyCos cayleySin)
open Holonics.Transport.SerialChainJacobian (chartSine chartVersine angularRate)

/-! ## 1. The Cayley point and its turn -/

/-- [definition] The Cayley point of the half-angle parameter `q`: `z(q) = (1 + iq)/(1 − iq)`. -/
noncomputable def cayleyPoint (q : ℝ) : ℂ := (1 + q * I) / (1 - q * I)

/-- [definition] The turn the Cayley chart reads at `q`: `θ(q) = 2 arctan q`, in radians. -/
noncomputable def turnAngle (q : ℝ) : ℝ := 2 * Real.arctan q

/-- [proved-standard; formal-checked] The chart denominator `1 − iq` does not vanish. -/
theorem one_sub_mul_I_ne_zero (q : ℝ) : (1 : ℂ) - q * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- [proved-standard; formal-checked] `z(q) = (1 − q²)/(1 + q²) + i·2q/(1 + q²)`. -/
theorem cayleyPoint_eq_chart (q : ℝ) :
    cayleyPoint q = ofReal ((1 - q ^ 2) / (1 + q ^ 2)) + ofReal (2 * q / (1 + q ^ 2)) * I := by
  have hD : (1 : ℝ) + q ^ 2 ≠ 0 := by positivity
  rw [cayleyPoint, div_eq_iff (one_sub_mul_I_ne_zero q)]
  apply Complex.ext
  · simp only [add_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_re,
      add_im, mul_im, sub_im, one_im]
    field_simp
    ring
  · simp only [add_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_re,
      add_im, mul_im, sub_im, one_im]
    field_simp
    ring

/-- [proved-standard; formal-checked] The real part of the Cayley point is `(1 − q²)/(1 + q²)`. -/
theorem cayleyPoint_re (q : ℝ) : (cayleyPoint q).re = (1 - q ^ 2) / (1 + q ^ 2) := by
  rw [cayleyPoint_eq_chart]
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
  ring

/-- [proved-standard; formal-checked] The imaginary part of the Cayley point is `2q/(1 + q²)`. -/
theorem cayleyPoint_im (q : ℝ) : (cayleyPoint q).im = 2 * q / (1 + q ^ 2) := by
  rw [cayleyPoint_eq_chart]
  simp only [add_im, ofReal_re, mul_im, I_re, ofReal_im, I_im]
  ring

/-- [proved-derived; formal-checked] For rational `q` the real part is the owner's `cayleyCos q`. -/
theorem cayleyPoint_ratCast_re (q : ℚ) : (cayleyPoint q).re = (cayleyCos q : ℝ) := by
  rw [cayleyPoint_re, cayleyCos]; push_cast; rfl

/-- [proved-derived; formal-checked] For rational `q` the imaginary part is the owner's `cayleySin q`. -/
theorem cayleyPoint_ratCast_im (q : ℚ) : (cayleyPoint q).im = (cayleySin q : ℝ) := by
  rw [cayleyPoint_im, cayleySin]; push_cast; rfl

/-- [proved-standard; formal-checked] **The Cayley point is the turn by `2 arctan q`:** `z(q) = exp(iθ(q))`. -/
theorem cayleyPoint_eq_exp (q : ℝ) : cayleyPoint q = exp (turnAngle q * I) := by
  have hc := Holonics.Transport.SerialChainJacobian.cos_two_arctan q
  have hs := Holonics.Transport.SerialChainJacobian.sin_two_arctan q
  have hD : (1 : ℝ) + q ^ 2 ≠ 0 := by positivity
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, turnAngle, hc, hs, cayleyPoint_eq_chart]
  congr 2
  · simp only [chartVersine, one_mul]
    field_simp
    ring
  · simp [chartSine]

/-- [proved-standard; formal-checked] The Cayley point lies on the unit circle. -/
theorem norm_cayleyPoint (q : ℝ) : ‖cayleyPoint q‖ = 1 := by
  rw [cayleyPoint_eq_exp, norm_exp_ofReal_mul_I]

/-- [proved-standard; formal-checked] The Cayley point is a unit, so its integer powers are defined. -/
theorem cayleyPoint_ne_zero (q : ℝ) : cayleyPoint q ≠ 0 := by
  intro h
  have := norm_cayleyPoint q
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- [proved-standard; formal-checked] The turn of the chart lies strictly inside a half-turn either way. -/
theorem turnAngle_mem_Ioo (q : ℝ) : turnAngle q ∈ Set.Ioo (-π) π := by
  have h1 := Real.arctan_lt_pi_div_two q
  have h2 := Real.neg_pi_div_two_lt_arctan q
  constructor <;> unfold turnAngle <;> linarith

/-- [proved-standard; formal-checked] The turn is the principal argument of the Cayley point. -/
theorem arg_cayleyPoint (q : ℝ) : arg (cayleyPoint q) = turnAngle q := by
  rw [cayleyPoint_eq_exp, arg_exp_mul_I, toIocMod_eq_self]
  have h := turnAngle_mem_Ioo q
  exact ⟨h.1, by linarith [h.2]⟩

/-- [proved-standard; formal-checked] **Half-angle addition:** `z(s) z(t) = z((s + t)/(1 − st))` for `st ≠ 1`. -/
theorem cayleyPoint_mul {s t : ℝ} (h : s * t ≠ 1) :
    cayleyPoint s * cayleyPoint t = cayleyPoint ((s + t) / (1 - s * t)) := by
  have h' : (1 : ℂ) - s * t ≠ 0 := by
    intro h0
    apply h
    exact_mod_cast (sub_eq_zero.mp h0).symm
  have hr : (1 : ℝ) - s * t ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hs := one_sub_mul_I_ne_zero s
  have ht := one_sub_mul_I_ne_zero t
  have hu := one_sub_mul_I_ne_zero ((s + t) / (1 - s * t))
  rw [cayleyPoint, cayleyPoint, cayleyPoint, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hs ht) hu]
  push_cast
  field_simp
  linear_combination (-2 * s * t * (s + t) * I) * I_sq

/-- [proved-standard; formal-checked] The parameter `0` charts the identity. -/
theorem cayleyPoint_zero : cayleyPoint 0 = 1 := by simp [cayleyPoint]

/-- [proved-standard; formal-checked] The parameter `1` charts the quarter turn `i`. -/
theorem cayleyPoint_one : cayleyPoint 1 = I := by
  rw [cayleyPoint, div_eq_iff (by simpa using one_sub_mul_I_ne_zero 1)]
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- [proved-standard; formal-checked] The parameter `−1` charts the quarter turn `−i`. -/
theorem cayleyPoint_neg_one : cayleyPoint (-1) = -I := by
  rw [cayleyPoint, div_eq_iff (by simpa using one_sub_mul_I_ne_zero (-1))]
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- [proved-standard; formal-checked] The parameter `½` charts the 3-4-5 point `(3 + 4i)/5`. -/
theorem cayleyPoint_half : cayleyPoint (1 / 2) = (3 + 4 * I) / 5 := by
  rw [cayleyPoint, div_eq_div_iff (by simpa using one_sub_mul_I_ne_zero (1 / 2)) (by norm_num)]
  push_cast
  ring_nf
  rw [I_sq]; ring

/-- [proved-standard; formal-checked] The parameter `1` turns by `π/2`. -/
theorem turnAngle_one : turnAngle 1 = π / 2 := by
  rw [turnAngle, Real.arctan_one]; ring

/-- [proved-standard; formal-checked] The parameter `−1` turns by `−π/2`. -/
theorem turnAngle_neg_one : turnAngle (-1) = -(π / 2) := by
  rw [turnAngle, Real.arctan_neg, Real.arctan_one]; ring

/-! ## 2. The Cayley coordinate against the turn rate -/

/-- [proved-standard; formal-checked] `dθ/dq = 2/(1 + q²)`, the owner's `angularRate 1 q`. -/
theorem hasDerivAt_turnAngle (q : ℝ) : HasDerivAt turnAngle (angularRate 1 q) q :=
  Holonics.Transport.SerialChainJacobian.hasDerivAt_two_arctan q

/-- [definition] The turn rate along the uniform parameter clock `q(t) = q₀ + vt`: `2v/(1 + q(t)²)`. -/
noncomputable def clockRate (q₀ v t : ℝ) : ℝ := 2 * v / (1 + (q₀ + v * t) ^ 2)

/-- [proved-standard; formal-checked] Along `q(t) = q₀ + vt` the turn moves at `2v/(1 + q(t)²)`. -/
theorem hasDerivAt_turnAngle_clock (q₀ v t : ℝ) :
    HasDerivAt (fun t => turnAngle (q₀ + v * t)) (clockRate q₀ v t) t := by
  have hq : HasDerivAt (fun t : ℝ => q₀ + v * t) v t := by
    simpa using ((hasDerivAt_id t).const_mul v).const_add q₀
  refine ((hasDerivAt_turnAngle (q₀ + v * t)).comp t hq).congr_deriv ?_
  simp only [angularRate, clockRate, one_mul]
  ring

/-- [proved-standard; formal-checked] **A uniform parameter clock is not a uniform turn:** for `v ≠ 0` the rate
reads `2v` where `q(t) = 0` and `v` where `q(t) = 1`. -/
theorem clockRate_ne {q₀ v : ℝ} (hv : v ≠ 0) :
    clockRate q₀ v (-q₀ / v) ≠ clockRate q₀ v ((1 - q₀) / v) := by
  have h0 : q₀ + v * (-q₀ / v) = 0 := by field_simp; ring
  have h1 : q₀ + v * ((1 - q₀) / v) = 1 := by field_simp; ring
  rw [clockRate, clockRate, h0, h1]
  intro h
  apply hv
  linarith [h]

/-- [proved-standard; formal-checked] **The parameter is not a turn count:** `θ(2) ≠ 2θ(1)`. -/
theorem turnAngle_two_ne : turnAngle 2 ≠ 2 * turnAngle 1 := by
  rw [turnAngle_one]
  have := (turnAngle_mem_Ioo 2).2
  intro h
  rw [h] at this
  linarith

/-! ## 3. The clock map of the finite action -/

/-- [proved-standard; formal-checked] **The clock map:** `z(q)^k = exp(ikθ(q))` for every integer `k`. -/
theorem cayleyPoint_zpow (q : ℝ) (k : ℤ) :
    cayleyPoint q ^ k = exp (((k * turnAngle q : ℝ) : ℂ) * I) := by
  rw [cayleyPoint_eq_exp, ← exp_int_mul]
  push_cast
  ring_nf

/-- [proved-standard; formal-checked] The clock map on natural counts: `z(q)^n = exp(inθ(q))`. -/
theorem cayleyPoint_pow (q : ℝ) (n : ℕ) :
    cayleyPoint q ^ n = exp (((n * turnAngle q : ℝ) : ℂ) * I) := by
  rw [cayleyPoint_eq_exp, ← exp_nat_mul]
  push_cast
  ring_nf

/-- [proved-standard; formal-checked] The powers are an action of `ℤ`: `z^(j + k) = z^j z^k`. -/
theorem cayleyPoint_zpow_add (q : ℝ) (j k : ℤ) :
    cayleyPoint q ^ (j + k) = cayleyPoint q ^ j * cayleyPoint q ^ k :=
  zpow_add₀ (cayleyPoint_ne_zero q) j k

/-- [definition] The lifted phase of `k` passages, in turns: `kθ(q)/(2π)`. -/
noncomputable def liftedPhase (q : ℝ) (k : ℤ) : ℝ := k * turnAngle q / (2 * π)

/-- [definition] The completed turns of `k` passages: the floor of the lifted phase. -/
noncomputable def completedTurns (q : ℝ) (k : ℤ) : ℤ := ⌊liftedPhase q k⌋

/-- [proved-standard; formal-checked] The lifted phase is its completed turns plus its open phase. -/
theorem liftedPhase_eq (q : ℝ) (k : ℤ) :
    liftedPhase q k = completedTurns q k + Int.fract (liftedPhase q k) :=
  (Int.floor_add_fract _).symm

/-- [proved-standard; formal-checked] **The circle reads the open phase alone:**
`z(q)^k = exp(2πi·fract(kθ(q)/(2π)))`. -/
theorem cayleyPoint_zpow_fract (q : ℝ) (k : ℤ) :
    cayleyPoint q ^ k = exp (((2 * π * Int.fract (liftedPhase q k) : ℝ) : ℂ) * I) := by
  have hk : (k : ℝ) * turnAngle q =
      2 * π * Int.fract (liftedPhase q k) + completedTurns q k * (2 * π) := by
    have h := liftedPhase_eq q k
    rw [liftedPhase] at h ⊢
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    field_simp at h
    linarith
  rw [cayleyPoint_zpow, hk]
  push_cast
  rw [add_mul, exp_add,
    show (completedTurns q k : ℂ) * (2 * π) * I = completedTurns q k * (2 * π * I) by ring,
    exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-standard; formal-checked] The lifted phase is additive in the count of passages. -/
theorem liftedPhase_add (q : ℝ) (j k : ℤ) :
    liftedPhase q (j + k) = liftedPhase q j + liftedPhase q k := by
  simp only [liftedPhase]; push_cast; ring

/-- [definition] The turn carried when two counts of passages are joined: the floor of their open phases' sum. -/
noncomputable def turnCarry (q : ℝ) (j k : ℤ) : ℤ :=
  ⌊Int.fract (liftedPhase q j) + Int.fract (liftedPhase q k)⌋

/-- [proved-standard; formal-checked] **The completed turns add with the carry.** -/
theorem completedTurns_add (q : ℝ) (j k : ℤ) :
    completedTurns q (j + k) = completedTurns q j + completedTurns q k + turnCarry q j k := by
  rw [completedTurns, liftedPhase_add, liftedPhase_eq q j, liftedPhase_eq q k, turnCarry]
  rw [show (completedTurns q j : ℝ) + Int.fract (liftedPhase q j) +
      (completedTurns q k + Int.fract (liftedPhase q k)) =
      ((completedTurns q j + completedTurns q k : ℤ) : ℝ) +
        (Int.fract (liftedPhase q j) + Int.fract (liftedPhase q k)) by push_cast; ring,
    Int.floor_intCast_add]

/-- [proved-standard; formal-checked] The carry is a single turn or none. -/
theorem turnCarry_mem (q : ℝ) (j k : ℤ) : 0 ≤ turnCarry q j k ∧ turnCarry q j k ≤ 1 := by
  have h1 := Int.fract_nonneg (liftedPhase q j)
  have h2 := Int.fract_nonneg (liftedPhase q k)
  have h3 := Int.fract_lt_one (liftedPhase q j)
  have h4 := Int.fract_lt_one (liftedPhase q k)
  constructor
  · exact Int.floor_nonneg.mpr (by linarith)
  · have : turnCarry q j k < 2 := by
      rw [turnCarry, Int.floor_lt]; push_cast; linarith
    omega

/-! ## 4. Checked closure -/

/-- [proved-standard; formal-checked] **Closure is a whole number of turns:** `z(q)^n = 1` iff
`nθ(q) ∈ 2πℤ`. -/
theorem cayleyPoint_pow_eq_one_iff (q : ℝ) (n : ℕ) :
    cayleyPoint q ^ n = 1 ↔ ∃ m : ℤ, n * turnAngle q = 2 * π * m := by
  rw [cayleyPoint_pow, exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    push_cast
    ring

/-- [proved-standard; formal-checked] No rational squares to `3`. -/
theorem not_sq_eq_three (q : ℚ) : q ^ 2 ≠ 3 := by
  intro h
  have hsq : IsSquare (3 : ℚ) := ⟨q, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at hsq
  obtain ⟨⟨r, hr⟩, -⟩ := hsq
  have h3 : (3 : ℚ).num = 3 := rfl
  rw [h3] at hr
  have hb : -2 < r ∧ r < 2 := by constructor <;> nlinarith
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases r <;> omega

/-- [proved-standard; formal-checked] A rational `q` whose `2 cayleyCos q` is one of Niven's values is `0` or
`±1`. -/
theorem eq_of_two_cayleyCos_mem (q : ℚ) (h : 2 * cayleyCos q ∈ ({-2, -1, 0, 1, 2} : Set ℚ)) :
    q = 0 ∨ q = 1 ∨ q = -1 := by
  have hD : (0 : ℚ) < 1 + q ^ 2 := by positivity
  have key : ∀ c : ℚ, 2 * cayleyCos q = c → 2 * (1 - q ^ 2) = c * (1 + q ^ 2) := by
    intro c hc
    rw [cayleyCos] at hc
    field_simp at hc
    linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h <;> have := key _ h
  · nlinarith
  · exact absurd (by linarith : q ^ 2 = 3) (not_sq_eq_three q)
  · have h1 : (q - 1) * (q + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · exact absurd (by nlinarith : (3 * q) ^ 2 = 3) (not_sq_eq_three (3 * q))
  · left; nlinarith

/-- [proved-standard; formal-checked] **A rational Cayley point closes only at `q ∈ {0, 1, −1}`** (Niven's
values through `Crystallographic.niven_values`). -/
theorem ratCast_closes_iff (q : ℚ) :
    (∃ n : ℕ, 0 < n ∧ cayleyPoint q ^ n = 1) ↔ q = 0 ∨ q = 1 ∨ q = -1 := by
  constructor
  · rintro ⟨n, hn, hz⟩
    obtain ⟨m, hm⟩ := (cayleyPoint_pow_eq_one_iff q n).mp hz
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hθ : turnAngle q = ((2 * m / n : ℚ) : ℝ) * π := by
      push_cast
      field_simp
      linarith [hm]
    have hcos : Real.cos (turnAngle q) = (cayleyCos q : ℝ) := by
      rw [← cayleyPoint_ratCast_re, cayleyPoint_eq_exp, exp_ofReal_mul_I_re]
    have hniv := Holonics.Geometry.Crystallographic.niven_values (2 * m / n)
      ⟨2 * cayleyCos q, by rw [← hθ, hcos]; push_cast; ring⟩
    rw [← hθ, hcos] at hniv
    apply eq_of_two_cayleyCos_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hniv ⊢
    exact_mod_cast hniv
  · rintro (h | h | h) <;> subst h
    · exact ⟨1, one_pos, by simp [cayleyPoint_zero]⟩
    · exact ⟨4, by norm_num, by rw [Rat.cast_one, cayleyPoint_one, I_pow_four]⟩
    · exact ⟨4, by norm_num, by
        rw [Rat.cast_neg, Rat.cast_one, cayleyPoint_neg_one]; exact isPrimitiveRoot_neg_I.pow_eq_one⟩

/-- [proved-standard; formal-checked] **The test of a declared period:** for rational `q`, `z(q)^n = 1` iff
`n = 0`, or `q = 0`, or `4 ∣ n` with `q = ±1`. -/
theorem ratCast_pow_eq_one_iff (q : ℚ) (n : ℕ) :
    cayleyPoint q ^ n = 1 ↔ n = 0 ∨ q = 0 ∨ (4 ∣ n ∧ (q = 1 ∨ q = -1)) := by
  constructor
  · intro hz
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    right
    rcases (ratCast_closes_iff q).mp ⟨n, hn, hz⟩ with h | h | h <;> subst h
    · exact Or.inl rfl
    · rw [Rat.cast_one, cayleyPoint_one, isPrimitiveRoot_I.pow_eq_one_iff_dvd] at hz
      exact Or.inr ⟨hz, Or.inl rfl⟩
    · rw [Rat.cast_neg, Rat.cast_one, cayleyPoint_neg_one,
        isPrimitiveRoot_neg_I.pow_eq_one_iff_dvd] at hz
      exact Or.inr ⟨hz, Or.inr rfl⟩
  · rintro (h | h | ⟨hd, h | h⟩)
    · subst h; exact pow_zero _
    · subst h; simp [cayleyPoint_zero]
    · subst h; rw [Rat.cast_one, cayleyPoint_one, isPrimitiveRoot_I.pow_eq_one_iff_dvd]; exact hd
    · subst h
      rw [Rat.cast_neg, Rat.cast_one, cayleyPoint_neg_one, isPrimitiveRoot_neg_I.pow_eq_one_iff_dvd]
      exact hd

/-- [proved-standard; formal-checked] The minimal period at `q = 0` is `1`. -/
theorem orderOf_cayleyPoint_zero : orderOf (cayleyPoint 0) = 1 := by
  rw [cayleyPoint_zero, orderOf_one]

/-- [proved-standard; formal-checked] The minimal period at `q = 1` is `4`. -/
theorem orderOf_cayleyPoint_one : orderOf (cayleyPoint 1) = 4 := by
  rw [cayleyPoint_one, ← isPrimitiveRoot_I.eq_orderOf]

/-- [proved-standard; formal-checked] The minimal period at `q = −1` is `4`. -/
theorem orderOf_cayleyPoint_neg_one : orderOf (cayleyPoint (-1)) = 4 := by
  rw [cayleyPoint_neg_one, ← isPrimitiveRoot_neg_I.eq_orderOf]

/-- [proved-standard; formal-checked] The owner's chart at `½` reads `(3/5, 4/5)`. -/
theorem cayleyCos_half : cayleyCos (1 / 2) = 3 / 5 ∧ cayleySin (1 / 2) = 4 / 5 := by
  constructor <;> norm_num [cayleyCos, cayleySin]

/-- [proved-standard; formal-checked] **The 3-4-5 point never closes:** `z(½)^n ≠ 1` for every `n ≥ 1`. -/
theorem cayleyPoint_half_never_closes (n : ℕ) (hn : 0 < n) : cayleyPoint (1 / 2) ^ n ≠ 1 := by
  intro h
  have h' : cayleyPoint ((1 / 2 : ℚ) : ℝ) ^ n = 1 := by push_cast; exact h
  rcases (ratCast_closes_iff (1 / 2)).mp ⟨n, hn, h'⟩ with h | h | h <;> norm_num at h

/-! ## 5. The lifted winding at a checked closure -/

/-- [definition] The polygon winding of `n` passages: the principal step angles of the powers of `z(q)`,
summed in turns. -/
noncomputable def polygonWinding (q : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, arg (cayleyPoint q ^ (k + 1) / cayleyPoint q ^ k)) / (2 * π)

/-- [proved-derived; formal-checked] Each step turns by `θ(q)`, so the polygon winding is `nθ(q)/(2π)`. -/
theorem polygonWinding_eq (q : ℝ) (n : ℕ) : polygonWinding q n = liftedPhase q n := by
  have hstep : ∀ k : ℕ, cayleyPoint q ^ (k + 1) / cayleyPoint q ^ k = cayleyPoint q := fun k => by
    rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ (cayleyPoint_ne_zero q))]
  simp only [polygonWinding, liftedPhase, hstep, arg_cayleyPoint, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Int.cast_natCast]

/-- [proved-derived; formal-checked] **The polygon winding is an integer exactly at a closure.** -/
theorem pow_eq_one_iff_polygonWinding (q : ℝ) (n : ℕ) :
    cayleyPoint q ^ n = 1 ↔ ∃ w : ℤ, polygonWinding q n = w := by
  rw [cayleyPoint_pow_eq_one_iff, polygonWinding_eq, liftedPhase, Int.cast_natCast]
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; field_simp⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    field_simp at hw
    linarith

/-- [proved-derived; formal-checked] At `q = 0` the polygon winding is `0`. -/
theorem polygonWinding_zero (n : ℕ) : polygonWinding 0 n = 0 := by
  simp [polygonWinding_eq, liftedPhase, turnAngle]

/-- [proved-derived; formal-checked] At `q = 1` the polygon winding is `n/4`: one turn per four steps. -/
theorem polygonWinding_one (n : ℕ) : polygonWinding 1 n = n / 4 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [polygonWinding_eq, liftedPhase, turnAngle_one, Int.cast_natCast]
  field_simp
  ring

/-- [proved-derived; formal-checked] At `q = −1` the polygon winding is `−n/4`. -/
theorem polygonWinding_neg_one (n : ℕ) : polygonWinding (-1) n = -(n / 4) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [polygonWinding_eq, liftedPhase, turnAngle_neg_one, Int.cast_natCast]
  field_simp
  ring

/-- [definition] The lifted winding of `n` passages with `e` extra whole turns per passage: `w + ne`. -/
noncomputable def liftedWinding (q : ℝ) (e : ℤ) (n : ℕ) : ℝ := polygonWinding q n + n * e

/-- [proved-derived; formal-checked] The lifted winding is the turns of the lifted passage angle,
`n(θ + 2πe)/(2π)`. -/
theorem liftedWinding_eq (q : ℝ) (e : ℤ) (n : ℕ) :
    liftedWinding q e n = n * (turnAngle q + 2 * π * e) / (2 * π) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [liftedWinding, polygonWinding_eq, liftedPhase, Int.cast_natCast]
  field_simp

/-- [proved-derived; formal-checked] The lifted winding is additive over periods. -/
theorem liftedWinding_add (q : ℝ) (e : ℤ) (n₁ n₂ : ℕ) :
    liftedWinding q e (n₁ + n₂) = liftedWinding q e n₁ + liftedWinding q e n₂ := by
  simp only [liftedWinding_eq]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The circle cannot see the extra turns:** `exp(i(θ + 2πe)) = z(q)`. -/
theorem exp_liftedAngle (q : ℝ) (e : ℤ) :
    exp (((turnAngle q + 2 * π * e : ℝ) : ℂ) * I) = cayleyPoint q := by
  push_cast
  rw [add_mul, exp_add, show (2 : ℂ) * π * e * I = e * (2 * π * I) by ring, exp_int_mul_two_pi_mul_I,
    mul_one, cayleyPoint_eq_exp]

/-- [proved-derived; formal-checked] **The lifted winding keeps the extra turns:** at a positive period it
separates every two values of `e`. -/
theorem liftedWinding_extra_injective (q : ℝ) {n : ℕ} (hn : 0 < n) {e e' : ℤ}
    (h : liftedWinding q e n = liftedWinding q e' n) : e = e' := by
  rw [liftedWinding, liftedWinding] at h
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h' : (e : ℝ) = e' := mul_left_cancel₀ hn' (by linarith)
  exact_mod_cast h'

/-- [proved-derived; formal-checked] **The lifted winding is an integer exactly at a closure.** -/
theorem pow_eq_one_iff_liftedWinding (q : ℝ) (e : ℤ) (n : ℕ) :
    cayleyPoint q ^ n = 1 ↔ ∃ w : ℤ, liftedWinding q e n = w := by
  rw [pow_eq_one_iff_polygonWinding]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w + n * e, by rw [liftedWinding, hw]; push_cast; ring⟩
  · rintro ⟨w, hw⟩
    exact ⟨w - n * e, by rw [liftedWinding] at hw; push_cast; linarith⟩

/-- [definition] The Rust `lifted_winding` with its refusal: the lifted winding of `n` passages of the rational
Cayley point `z(q)` with `e` extra turns each, returned only at a positive closing period. -/
def checkedWinding (q : ℚ) (e : ℤ) (n : ℕ) : Option ℤ :=
  if n = 0 then none
  else if q = 0 then some (n * e)
  else if q = 1 ∧ 4 ∣ n then some ((n / 4 : ℕ) + n * e)
  else if q = -1 ∧ 4 ∣ n then some (-((n / 4 : ℕ) : ℤ) + n * e)
  else none

/-- [proved-derived; formal-checked] **The checked winding returns `w` iff the period is positive, `z(q)`
closes there and `w` is the lifted winding.** -/
theorem checkedWinding_eq_some_iff (q : ℚ) (e : ℤ) (n : ℕ) (w : ℤ) :
    checkedWinding q e n = some w ↔
      0 < n ∧ cayleyPoint q ^ n = 1 ∧ (w : ℝ) = liftedWinding q e n := by
  rw [ratCast_pow_eq_one_iff]
  unfold checkedWinding
  split_ifs with h0 hq h1 h2
  · simp [h0]
  · subst hq
    simp only [Option.some.injEq, Rat.cast_zero, liftedWinding, polygonWinding_zero, zero_add]
    constructor
    · rintro rfl
      exact ⟨Nat.pos_of_ne_zero h0, by simp, by push_cast; ring⟩
    · rintro ⟨-, -, hw⟩
      exact_mod_cast hw.symm
  · obtain ⟨rfl, hd⟩ := h1
    have hc : ((n / 4 : ℕ) : ℝ) = n / 4 := Nat.cast_div hd (by norm_num)
    simp only [Option.some.injEq, Rat.cast_one, liftedWinding, polygonWinding_one]
    constructor
    · rintro rfl
      refine ⟨Nat.pos_of_ne_zero h0, by simp [hd], ?_⟩
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hc]
    · rintro ⟨-, -, hw⟩
      apply Int.cast_injective (α := ℝ)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, hc]
      exact hw.symm
  · obtain ⟨rfl, hd⟩ := h2
    have hc : ((n / 4 : ℕ) : ℝ) = n / 4 := Nat.cast_div hd (by norm_num)
    simp only [Option.some.injEq, Rat.cast_neg, Rat.cast_one, liftedWinding, polygonWinding_neg_one]
    constructor
    · rintro rfl
      refine ⟨Nat.pos_of_ne_zero h0, by simp [hd], ?_⟩
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg, hc]
    · rintro ⟨-, -, hw⟩
      apply Int.cast_injective (α := ℝ)
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg, hc]
      exact hw.symm
  · simp only [false_iff]
    rintro ⟨-, h | h | ⟨hd, h | h⟩, -⟩
    · exact h0 h
    · exact hq h
    · exact h1 ⟨h, hd⟩
    · exact h2 ⟨h, hd⟩

/-- [proved-derived; formal-checked] The checked winding is defined iff the period is positive and closes. -/
theorem checkedWinding_isSome_iff (q : ℚ) (e : ℤ) (n : ℕ) :
    (checkedWinding q e n).isSome ↔ 0 < n ∧ cayleyPoint q ^ n = 1 := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hn, hz, -⟩ := (checkedWinding_eq_some_iff q e n w).mp hw
    exact ⟨hn, hz⟩
  · rintro ⟨hn, hz⟩
    obtain ⟨w, hw⟩ := (pow_eq_one_iff_liftedWinding q e n).mp hz
    exact ⟨w, (checkedWinding_eq_some_iff q e n w).mpr ⟨hn, hz, hw.symm⟩⟩

/-- [definition] The Rust `closes_after`: a positive declared period at which `z(q)` returns to `1`. -/
def closesAfter (q : ℚ) (n : ℕ) : Bool := (checkedWinding q 0 n).isSome

/-- [proved-derived; formal-checked] `closesAfter q n` holds iff `n ≥ 1` and `z(q)^n = 1`. -/
theorem closesAfter_iff (q : ℚ) (n : ℕ) : closesAfter q n = true ↔ 0 < n ∧ cayleyPoint q ^ n = 1 :=
  checkedWinding_isSome_iff q 0 n

/-- [proved-derived; formal-checked] The Rust control: the quarter turn closes in four steps with winding `1`. -/
theorem checkedWinding_quarter : checkedWinding 1 0 4 = some 1 := by decide

/-- [proved-derived; formal-checked] The Rust control: one extra turn per passage lifts the quarter turn's four
steps to winding `5`. -/
theorem checkedWinding_quarter_extra : checkedWinding 1 1 4 = some 5 := by decide

/-- [proved-derived; formal-checked] The Rust control: the identity closes in one step with winding `0`. -/
theorem checkedWinding_still : checkedWinding 0 0 1 = some 0 := by decide

/-- [proved-derived; formal-checked] The Rust control: the quarter turn refuses the period `3`. -/
theorem checkedWinding_quarter_three : checkedWinding 1 1 3 = none := by decide

/-- [proved-derived; formal-checked] The reversed quarter turn closes in four steps with winding `−1`. -/
theorem checkedWinding_neg_quarter : checkedWinding (-1) 0 4 = some (-1) := by decide

/-- [proved-derived; formal-checked] The 3-4-5 point refuses every declared period. -/
theorem closesAfter_half (n : ℕ) : closesAfter (1 / 2) n = false := by
  rw [Bool.eq_false_iff, Ne, closesAfter_iff]
  rintro ⟨hn, h⟩
  exact cayleyPoint_half_never_closes n hn (by push_cast at h; exact h)

/-! ## 6. The rational turn on the owner's circle -/

open Holonics.Geometry.PhaseCarry (phase winding odometer phase_add_winding odometer_iterate)

/-- [definition] The rational turn `p/m` of the circle: `exp(2πi·p/m)`. -/
noncomputable def rationalTurn (p m : ℕ) : ℂ := exp (2 * π * I * (p / m))

/-- [proved-derived; formal-checked] `k` passages of the turn `p/m` lift to `winding m (kp) + phase m (kp)/m`
turns. -/
theorem rationalLift_eq (p m k : ℕ) (hm : 0 < m) :
    ((k * p : ℕ) : ℝ) / m = winding m (k * p) + (phase m (k * p) : ℝ) / m := by
  have h := phase_add_winding m (k * p)
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hc : ((k * p : ℕ) : ℝ) = phase m (k * p) + m * winding m (k * p) := by exact_mod_cast h.symm
  rw [hc]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The completed turns are the owner's winding:**
`⌊kp/m⌋ = winding m (kp)`. -/
theorem rationalLift_floor (p m k : ℕ) (hm : 0 < m) :
    ⌊((k * p : ℕ) : ℝ) / m⌋ = (winding m (k * p) : ℤ) := by
  rw [Int.floor_eq_iff, rationalLift_eq p m k hm]
  have hlt : phase m (k * p) < m := Nat.mod_lt _ hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt' : (phase m (k * p) : ℝ) / m < 1 := by
    rw [div_lt_one hm']; exact_mod_cast hlt
  have hnn : 0 ≤ (phase m (k * p) : ℝ) / m := by positivity
  push_cast
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The circle reads the owner's phase:**
`(e^(2πi·p/m))^k = e^(2πi·phase m (kp)/m)`. -/
theorem rationalTurn_pow (p m k : ℕ) (hm : 0 < m) :
    rationalTurn p m ^ k = exp (2 * π * I * (phase m (k * p) / m)) := by
  have h := rationalLift_eq p m k hm
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : (k : ℂ) * p / m = winding m (k * p) + (phase m (k * p) : ℂ) / m := by
    have := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at this
    exact this
  rw [rationalTurn, ← exp_nat_mul]
  rw [show (k : ℂ) * (2 * π * I * (p / m)) = 2 * π * I * (phase m (k * p) / m) +
      ((winding m (k * p) : ℕ) : ℤ) * (2 * π * I) by
    rw [show (k : ℂ) * (2 * π * I * (p / m)) = 2 * π * I * (k * p / m) by ring, hc]
    push_cast
    ring]
  rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-derived; formal-checked] The Cayley quarter turn is the rational turn `1/4`. -/
theorem cayleyPoint_one_eq_rationalTurn : cayleyPoint 1 = rationalTurn 1 4 := by
  rw [cayleyPoint_eq_exp, turnAngle_one, rationalTurn]
  congr 1
  push_cast
  ring

/-- [proved-derived; formal-checked] **The quarter turn's clock map is the owner's odometer on four steps:**
`z(1)^k` reads `phase 4 k`, its completed turns are `winding 4 k`, and the odometer reads both. -/
theorem quarterTurn_clock (k : ℕ) :
    cayleyPoint 1 ^ k = exp (2 * π * I * (phase 4 k / 4)) ∧
      completedTurns 1 k = winding 4 k ∧
      (odometer 4)^[k] (0, 0) = (phase 4 k, winding 4 k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cayleyPoint_one_eq_rationalTurn, rationalTurn_pow 1 4 k (by norm_num), mul_one]
    push_cast
    rfl
  · have h := rationalLift_floor 1 4 k (by norm_num)
    rw [mul_one] at h
    rw [completedTurns, liftedPhase, turnAngle_one, ← h]
    congr 1
    have hπ : π ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
    ring
  · have h := odometer_iterate 4 0 0 k (by norm_num) (by norm_num)
    simpa [phase, winding] using h

/-! ## 7. Joint closure -/

open Holonics.Geometry.RingClosure (diag closing nsmul_diag_apply nsmul_diag_eq_zero_iff)

/-- [proved-derived; formal-checked] **Phases closing together are rings ticking together:** a family closes at
`n` iff the diagonal tick on `Π i, ZMod (ord i)` returns at `n`. -/
theorem pow_eq_one_iff_diag {ι : Type*} [Fintype ι] {M : Type*} [Monoid M] (x : ι → M) (n : ℕ) :
    (∀ i, x i ^ n = 1) ↔ n • diag (fun i => orderOf (x i)) = 0 := by
  rw [funext_iff]
  simp only [nsmul_diag_apply, Pi.zero_apply, ZMod.natCast_eq_zero_iff, orderOf_dvd_iff_pow_eq_one]

/-- [proved-standard; formal-checked] **Joint closure at the least common multiple:** a family closes together
at `n` iff the closing `lcm_i ord i` divides `n`. -/
theorem joint_closure_iff {ι : Type*} [Fintype ι] {M : Type*} [Monoid M] (x : ι → M) (n : ℕ) :
    (∀ i, x i ^ n = 1) ↔ closing (fun i => orderOf (x i)) ∣ n :=
  (pow_eq_one_iff_diag x n).trans (nsmul_diag_eq_zero_iff _ n)

/-- [proved-standard; formal-checked] The closing of two rings is the least common multiple of their periods. -/
theorem closing_pair (a b : ℕ) : closing ![a, b] = Nat.lcm a b := by
  simp [closing, Fin.univ_succ, Finset.lcm_insert, lcm_eq_nat_lcm]

/-- [proved-standard; formal-checked] Two phases close together at `n` iff `lcm(ord x, ord y) ∣ n`. -/
theorem pair_closure_iff {M : Type*} [Monoid M] (x y : M) (n : ℕ) :
    (x ^ n = 1 ∧ y ^ n = 1) ↔ Nat.lcm (orderOf x) (orderOf y) ∣ n := by
  have h := joint_closure_iff ![x, y] n
  rw [Fin.forall_fin_two] at h
  have hc : (fun i => orderOf (![x, y] i)) = ![orderOf x, orderOf y] := by
    ext i; fin_cases i <;> rfl
  rw [hc, closing_pair] at h
  simpa using h

/-- [proved-standard; formal-checked] A rational turn in lowest terms has its denominator as its order. -/
theorem orderOf_rationalTurn {p m : ℕ} (hm : 0 < m) (hpm : p.Coprime m) :
    orderOf (rationalTurn p m) = m :=
  ((isPrimitiveRoot_exp_of_coprime p m hm.ne' hpm).eq_orderOf).symm

/-- [proved-derived; formal-checked] **Two rational turns in lowest terms close together at `n` iff
`lcm(m₁, m₂) ∣ n`.** -/
theorem rationalTurn_joint_iff {p₁ m₁ p₂ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h₁ : p₁.Coprime m₁) (h₂ : p₂.Coprime m₂) (n : ℕ) :
    (rationalTurn p₁ m₁ ^ n = 1 ∧ rationalTurn p₂ m₂ ^ n = 1) ↔ Nat.lcm m₁ m₂ ∣ n := by
  rw [pair_closure_iff, orderOf_rationalTurn hm₁ h₁, orderOf_rationalTurn hm₂ h₂]

/-- [proved-derived; formal-checked] Two Cayley points close together at `n` iff the least common multiple of
their minimal periods divides `n`. -/
theorem cayleyPoint_joint_iff (q₁ q₂ : ℝ) (n : ℕ) :
    (cayleyPoint q₁ ^ n = 1 ∧ cayleyPoint q₂ ^ n = 1) ↔
      Nat.lcm (orderOf (cayleyPoint q₁)) (orderOf (cayleyPoint q₂)) ∣ n :=
  pair_closure_iff _ _ n

/-- [proved-derived; formal-checked] The Cayley quarter turn and the sixth turn close together exactly at the
multiples of `12`. -/
theorem quarter_sixth_joint_iff (n : ℕ) :
    (cayleyPoint 1 ^ n = 1 ∧ rationalTurn 1 6 ^ n = 1) ↔ 12 ∣ n := by
  rw [cayleyPoint_one_eq_rationalTurn,
    rationalTurn_joint_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rfl

/-- [proved-derived; formal-checked] **A declared joint period that fails the test is refused:** the quarter
turn and the sixth turn do not close together at `6`. -/
theorem quarter_sixth_refused : ¬ (cayleyPoint 1 ^ 6 = 1 ∧ rationalTurn 1 6 ^ 6 = 1) := by
  rw [quarter_sixth_joint_iff]; decide

/-- [proved-derived; formal-checked] The quarter turn and the sixth turn close together at `12`. -/
theorem quarter_sixth_closes : cayleyPoint 1 ^ 12 = 1 ∧ rationalTurn 1 6 ^ 12 = 1 :=
  (quarter_sixth_joint_iff 12).mpr dvd_rfl

/-- [proved-standard; formal-checked] Six quarter turns are a half-turn: `z(1)^6 = −1`. -/
theorem cayleyPoint_one_pow_six : cayleyPoint 1 ^ 6 = -1 := by
  rw [cayleyPoint_one, show (6 : ℕ) = 4 + 2 from rfl, pow_add, I_pow_four, I_sq, one_mul]

end Holonics.Geometry.CayleyTurnClock
