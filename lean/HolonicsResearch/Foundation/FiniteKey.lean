import Mathlib
import Holonics.Geometry.AffineSwing

/-!
# A proof is a finite key: the diagonal's half-turn, an unending family as the orbit of a finite map, the half forced by a reversal and a pairing, and a route as two sweeps that meet

The record of November 15 (`research/records/2026-11-15_A_PROOF_REACHES_AN_UNENDING_FAMILY_AS_THE_ORBIT_OF_A_FINITE_MAP_…`,
§3 and §4; atlas `key.forall-orbit-of-finite-map`, `key.diagonal-half-turn`, `key.derivation-finite-word-every-reader`) reads a
derivation as a finite word that a reader runs: a statement over an unending family is reached as the orbit of a finite map, and
the diagonal arguments share one engine, a map on finitely many faces with no fixed point. The record of November 10 on the cost
of navigating (`research/records/2026-11-10_THE_COST_OF_NAVIGATING_BETWEEN_STATES_HAS_A_FLOOR_FROM_COUNTING_A_HALF_FROM_REVERSAL_…`;
atlas `key.scaled-form-places-modes`, `key.meet-in-middle-half`) reads the half as the square root of a count, forced by a
reversal and a pairing, and a route of length `2m` as two routes of length `m` that meet. This file states those laws on the
objects' own owners and proves them.

[proved-standard; formal-checked] What is proved.

1. **The diagonal's engine** (`diagonal_fixed_point`, Lawvere 1969): a map `A → (A → Y)` that reaches every map `A → Y` gives
   every map `Y → Y` a fixed point. So a face set that carries a map with no fixed point is never reached
   (`no_reading_reaches_every_assignment`); two digits suffice, the flip (`two_digits_are_a_gap`, Cantor;
   `no_reader_names_every_predicate` with negation on verdicts); with one digit there is no gap (`one_digit_no_gap`,
   `one_digit_every_map_fixed`).
2. **The half-turn is such a map on its two faces.** For the half-turn `S_a x = 2a − x` (`Geometry/AffineSwing.swing`) the
   faces `a − d` and `a + d` are exchanged (`halfTurn_exchanges_faces`), a face is fixed only where `d + d = 0`
   (`halfTurn_fixes_face_iff`), and on a carrier without two-torsion the pivot is the one fixed point of the whole line
   (`halfTurn_fixed_iff_pivot`). The two faces with the turn restricted to them are a face set with no fixed point
   (`faceTurn_no_fixed_point`, `faceTurn_involutive`), so no reading reaches every assignment of them
   (`halfTurn_faces_are_a_gap`). The half-turn of a phase, `−1 = e^{iπ}`, fixes only zero (`neg_fixes_only_zero`,
   `half_turn_phase_fixes_only_zero`), and every fixed-point-free pairing `σ` is such an engine by statement 1.
3. **An unending family is the orbit of a finite map.** The recursor's value at `n` is the step iterated `n` times on the base
   (`rec_eq_iterate`); with a step that reads its index, and for a dependent family, it is the orbit of one map on the total
   space (`rec_eq_orbit`, `dependent_rec_is_orbit`); the principle itself is the recursor (`forall_of_base_and_step`). Descent
   reaches the ground within the count's value (`descent_reaches_ground`) and, on any well-founded count, in finitely many steps
   (`descent_reaches_ground_wellFounded`). The pigeonhole (`pigeonhole`) and exhaustion over a finite partition (`exhaustion`).
   One reading refutes a statement over an unending family and no finite set of readings completes it
   (`refuted_by_one_reading`, `no_finite_set_of_readings_completes`).
4. **The half is forced by a reversal and a pairing** (`scaled_form_places_mode`): for complex matrices with `Bᴴ G B = q • G`
   and a mode `B v = α v` whose form `v†Gv` is not zero, `‖α‖² = q`, hence `‖α‖ = √q` (`scaled_form_mode_is_half`); with the
   scaling `q^k` the mode stands at `q^(k/2)` (`scaled_form_mode_at_weight`). The real chart is the equality case of the
   parametron's certificate `MᵀGM ⪯ ρ²G` (`HNN/Floquet.FloquetCertifies`, `certificate_reading`): `real_scaled_form_places_mode`.
5. **A route of length `2m` is two routes of length `m` that meet** (`meet_in_middle`, `meet_in_middle_sweeps`): for a
   symmetric move matrix `A`, `(A^(2m)) x y = Σ_z (A^m) x z · (A^m) y z = ⟨Aᵐδ_x, Aᵐδ_y⟩`. A landmark pins an orbit and divides
   the volume left to search (`landmark_divides_volume`, Mathlib's orbit and stabilizer count).

Limits. Statement 1 is the set-theoretic chart of Lawvere's theorem; its readings as Gödel's, Tarski's and Turing's theorems
need each reader's own coding of its words and are not stated here. Statement 3's ordinal reach of a reader (Gentzen, Goodstein,
Kirby and Paris) is not stated: the descent is along `ℕ` or a given well-founded order. Statement 4 takes the form's value on the
mode to be nonzero and does not ask `G ≻ 0`; which operators carry such a form is each instance's own theorem (Weil for curves,
the Hodge index), and nothing here supplies one. Statement 5 is the pairing identity; the count of states two sweeps visit before
they meet (Shanks) and the generic lower bound (Shoup) are not stated. No claim about any target statement is made in this file.

The computational object is the helical pair interaction: the half-turn is the pairing's reflection `σ` read on two faces, the
form `G` is the contact's pairing against which a move's rate splits into turn and boost, and the symmetric move matrix is the
pair contacts' reversible exchange. Of the winding guide's six general objects this touches the pair (the pairing and the
reversal), faces and placement (the two faces; the mode's placement at `√q`) and the helix (the orbit of the step, the count
that descends); cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `key.diagonal-half-turn`, `key.forall-orbit-of-finite-map`,
`key.derivation-finite-word-every-reader`, `key.scaled-form-places-modes` and `key.meet-in-middle-half`; `HankelKey` beside this
file holds the finite key of an unending census.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.FiniteKey

open Holonics.Geometry.AffineSwing

/-! ## 1. The diagonal's engine -/

/-- [proved-standard; formal-checked] **The diagonal's engine** (Lawvere 1969): if a reading `f : A → (A → Y)` reaches every
map `A → Y`, then every map `g : Y → Y` has a fixed point. The fixed point is the diagonal word read at itself. -/
theorem diagonal_fixed_point {A Y : Type*} (f : A → A → Y) (hf : Function.Surjective f)
    (g : Y → Y) : ∃ y, g y = y := by
  obtain ⟨a, ha⟩ := hf fun x => g (f x x)
  exact ⟨f a a, (congrFun ha a).symm⟩

/-- [proved-standard; formal-checked] **A face set that carries a map with no fixed point is never reached**: no reading
`A → (A → Y)` reaches every assignment of faces `A → Y`. -/
theorem no_reading_reaches_every_assignment {A Y : Type*} (g : Y → Y) (hg : ∀ y, g y ≠ y)
    (f : A → A → Y) : ¬ Function.Surjective f := fun hf =>
  let ⟨y, hy⟩ := diagonal_fixed_point f hf g
  hg y hy

/-- [proved-standard; formal-checked] **Two digits are a gap** (Cantor 1891): the flip of two digits has no fixed point, so no
reading of `A` reaches every digit string indexed by `A`. -/
theorem two_digits_are_a_gap {A : Type*} (f : A → A → Bool) : ¬ Function.Surjective f :=
  no_reading_reaches_every_assignment (fun b => !b) Bool.not_ne_self f

/-- [proved-standard; formal-checked] **A reader's words do not name every predicate on its words**: the flip is negation on
verdicts. Mathlib's `Function.cantor_surjective` is the same statement for sets. -/
theorem no_reader_names_every_predicate {A : Type*} (f : A → A → Prop) : ¬ Function.Surjective f :=
  no_reading_reaches_every_assignment Not (fun _ h => not_iff_self (iff_of_eq h)) f

/-- [proved-standard; formal-checked] **With one digit there is no gap**: a reading of a nonempty `A` reaches every
assignment into a one-point face set. -/
theorem one_digit_no_gap (A : Type*) [Nonempty A] : ∃ f : A → A → Unit, Function.Surjective f :=
  ⟨fun _ _ => (), fun _ => ⟨Classical.arbitrary A, rfl⟩⟩

/-- [proved-standard; formal-checked] **With one digit every map has a fixed point.** -/
theorem one_digit_every_map_fixed (g : Unit → Unit) : ∃ y, g y = y := ⟨(), rfl⟩

/-! ## 2. The half-turn on its two faces -/

section HalfTurn

variable {G : Type*} [AddCommGroup G]

/-- [proved-derived; formal-checked] **The half-turn exchanges its two faces**: `S_a (a − d) = a + d` and
`S_a (a + d) = a − d`. -/
theorem halfTurn_exchanges_faces (a d : G) :
    swing a (a - d) = a + d ∧ swing a (a + d) = a - d := by
  constructor <;> simp only [swing] <;> abel

/-- [proved-derived; formal-checked] **A point is fixed if and only if its doubled displacement from the pivot is zero.** -/
theorem halfTurn_fixed_iff (a x : G) : swing a x = x ↔ (x - a) + (x - a) = 0 := by
  simp only [swing]
  constructor
  · intro h
    have h2 : a + a = x + x := by
      calc a + a = (a + a - x) + x := by abel
        _ = x + x := by rw [h]
    calc (x - a) + (x - a) = (x + x) - (a + a) := by abel
      _ = 0 := by rw [h2]; abel
  · intro h
    have h2 : x + x = a + a := by
      calc x + x = ((x - a) + (x - a)) + (a + a) := by abel
        _ = a + a := by rw [h, zero_add]
    calc a + a - x = (x + x) - x := by rw [h2]
      _ = x := by abel

/-- [proved-derived; formal-checked] **A face is fixed only where `d + d = 0`.** -/
theorem halfTurn_fixes_face_iff (a d : G) : swing a (a + d) = a + d ↔ d + d = 0 := by
  rw [halfTurn_fixed_iff]
  simp

/-- [proved-derived; formal-checked] **Neither face is fixed when the doubled displacement is not zero.** -/
theorem halfTurn_fixes_neither_face (a d : G) (hd : d + d ≠ 0) :
    swing a (a - d) ≠ a - d ∧ swing a (a + d) ≠ a + d := by
  refine ⟨fun h => hd ?_, fun h => hd ((halfTurn_fixes_face_iff a d).mp h)⟩
  have h' : swing a (a + -d) = a + -d := by simpa [sub_eq_add_neg] using h
  have h2 := (halfTurn_fixes_face_iff a (-d)).mp h'
  calc d + d = -(-d + -d) := by abel
    _ = 0 := by rw [h2, neg_zero]

/-- [proved-derived; formal-checked] **On a carrier without two-torsion the pivot is the one fixed point of the whole
line.** -/
theorem halfTurn_fixed_iff_pivot (h2 : ∀ z : G, z + z = 0 → z = 0) (a x : G) :
    swing a x = x ↔ x = a := by
  rw [halfTurn_fixed_iff]
  constructor
  · intro h
    exact sub_eq_zero.mp (h2 _ h)
  · rintro rfl
    simp

/-- [proved-derived; formal-checked] **The half-turn of a phase fixes only zero**: on a carrier without two-torsion,
`−x = x` only at `x = 0`. -/
theorem neg_fixes_only_zero (h2 : ∀ z : G, z + z = 0 → z = 0) (x : G) : -x = x ↔ x = 0 := by
  constructor
  · intro h
    apply h2
    calc x + x = -x + x := by rw [h]
      _ = 0 := neg_add_cancel x
  · rintro rfl
    simp

/-- [definition] **The two faces of a half-turn** about `a` at displacement `d`. -/
def Faces (a d : G) : Type _ := {x : G // x = a - d ∨ x = a + d}

/-- [definition] **The half-turn restricted to its two faces.** -/
def faceTurn (a d : G) (x : Faces a d) : Faces a d :=
  ⟨swing a x.1, by
    rcases x.2 with h | h
    · exact Or.inr (by rw [h]; exact (halfTurn_exchanges_faces a d).1)
    · exact Or.inl (by rw [h]; exact (halfTurn_exchanges_faces a d).2)⟩

/-- [proved-derived; formal-checked] **The restricted turn is an involution** (two half-turns are a whole turn). -/
theorem faceTurn_involutive (a d : G) : Function.Involutive (faceTurn a d) := fun x =>
  Subtype.ext (theSwingIsAnInvolution a x.1)

/-- [proved-derived; formal-checked] **The half-turn on its two faces has no fixed point** when the doubled displacement
is not zero. -/
theorem faceTurn_no_fixed_point (a d : G) (hd : d + d ≠ 0) (x : Faces a d) : faceTurn a d x ≠ x := by
  intro h
  have hx : swing a x.1 = x.1 := congrArg Subtype.val h
  rcases x.2 with hf | hf
  · rw [hf] at hx
    exact (halfTurn_fixes_neither_face a d hd).1 hx
  · rw [hf] at hx
    exact (halfTurn_fixes_neither_face a d hd).2 hx

/-- [proved-derived; formal-checked] **The half-turn's two faces are a gap**: no reading of `A` reaches every assignment
of the two faces to `A`. This is `two_digits_are_a_gap` with the tree's own flip. -/
theorem halfTurn_faces_are_a_gap {A : Type*} (a d : G) (hd : d + d ≠ 0)
    (f : A → A → Faces a d) : ¬ Function.Surjective f :=
  no_reading_reaches_every_assignment (faceTurn a d) (faceTurn_no_fixed_point a d hd) f

end HalfTurn

/-- [proved-standard; formal-checked] **The phase's half-turn `e^{iπ} = −1` fixes only zero.** -/
theorem half_turn_phase_fixes_only_zero (z : ℂ) :
    Complex.exp (Real.pi * Complex.I) * z = z ↔ z = 0 := by
  rw [Complex.exp_pi_mul_I, neg_one_mul]
  refine neg_fixes_only_zero (fun w hw => ?_) z
  have h2 : (2 : ℂ) * w = 0 := by rw [two_mul]; exact hw
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## 3. An unending family is the orbit of a finite map -/

/-- [proved-standard; formal-checked] **The recursor's value at `n` is the step iterated `n` times on the base.** -/
theorem rec_eq_iterate {α : Type*} (base : α) (step : α → α) (n : ℕ) :
    Nat.rec (motive := fun _ => α) base (fun _ ih => step ih) n = step^[n] base := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]

/-- [proved-standard; formal-checked] **A step that reads its index is one map on the counted space**: the pair of the
index and the recursor's value is the orbit of `(k, x) ↦ (k + 1, step k x)` from `(0, base)`. -/
theorem rec_eq_orbit {α : Type*} (base : α) (step : ℕ → α → α) (n : ℕ) :
    (fun p : ℕ × α => (p.1 + 1, step p.1 p.2))^[n] (0, base)
      = (n, Nat.rec (motive := fun _ => α) base step n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

/-- [proved-standard; formal-checked] **A dependent family of readings is the orbit of one map on its total space**: the
reading at `n`, with its index, is the map `⟨k, x⟩ ↦ ⟨k + 1, step k x⟩` iterated `n` times on `⟨0, base⟩`. The family is
produced on demand and never held as a list. -/
theorem dependent_rec_is_orbit {P : ℕ → Type*} (base : P 0) (step : ∀ n, P n → P (n + 1)) (n : ℕ) :
    (fun p : Σ k, P k => (⟨p.1 + 1, step p.1 p.2⟩ : Σ k, P k))^[n] ⟨0, base⟩
      = ⟨n, Nat.rec (motive := P) base step n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

/-- [proved-standard; formal-checked] **Induction is a base word and a step map**: the proof of `∀ n, P n` is the
recursor on them, a function from `n` to a proof of `P n`. -/
theorem forall_of_base_and_step {P : ℕ → Prop} (base : P 0) (step : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := fun n => Nat.rec base step n

/-- [proved-standard; formal-checked] **Descent reaches the ground within the count's value**: if a map lowers a count
`μ : X → ℕ` off the ground, every `x` reaches the ground in at most `μ x` steps. -/
theorem descent_reaches_ground {X : Type*} (f : X → X) (μ : X → ℕ) (ground : X → Prop)
    (h : ∀ x, ¬ ground x → μ (f x) < μ x) (x : X) : ∃ n ≤ μ x, ground (f^[n] x) := by
  induction hm : μ x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    by_cases hg : ground x
    · exact ⟨0, Nat.zero_le _, hg⟩
    · have hlt : μ (f x) < m := hm ▸ h x hg
      obtain ⟨n, hn, hgn⟩ := ih (μ (f x)) hlt (f x) rfl
      exact ⟨n + 1, by omega, by simpa [Function.iterate_succ_apply] using hgn⟩

/-- [proved-standard; formal-checked] **Descent along any well-founded count reaches the ground in finitely many
steps.** -/
theorem descent_reaches_ground_wellFounded {X α : Type*} [LT α] [WellFoundedLT α] (f : X → X)
    (μ : X → α) (ground : X → Prop) (h : ∀ x, ¬ ground x → μ (f x) < μ x) (x : X) :
    ∃ n, ground (f^[n] x) := by
  induction hm : μ x using WellFoundedLT.induction generalizing x with
  | _ m ih =>
    by_cases hg : ground x
    · exact ⟨0, hg⟩
    · have hlt : μ (f x) < m := hm ▸ h x hg
      obtain ⟨n, hgn⟩ := ih (μ (f x)) hlt (f x) rfl
      exact ⟨n + 1, by simpa [Function.iterate_succ_apply] using hgn⟩

/-- [proved-standard; formal-checked] **The pigeonhole**: `n + 1` items in `n` cells put two in one (Mathlib's
`Fintype.exists_ne_map_eq_of_card_lt`). -/
theorem pigeonhole {n : ℕ} (f : Fin (n + 1) → Fin n) : ∃ i j, i ≠ j ∧ f i = f j :=
  Fintype.exists_ne_map_eq_of_card_lt f (by simp)

/-- [proved-standard; formal-checked] **Exhaustion**: a statement read on every cell of a partition holds of every
member. -/
theorem exhaustion {X C : Type*} (cell : X → C) (P : X → Prop)
    (h : ∀ c, ∀ x, cell x = c → P x) : ∀ x, P x := fun x => h (cell x) x rfl

/-- [proved-standard; formal-checked] **One reading refutes a statement over an unending family.** -/
theorem refuted_by_one_reading {P : ℕ → Prop} {n : ℕ} (h : ¬ P n) : ¬ ∀ n, P n := fun hall => h (hall n)

/-- [proved-standard; formal-checked] **No finite set of readings completes a statement over an unending family**: for
every finite set of cases there is a decidable statement that holds at each of them and fails beyond them, so the cases
read do not tell it from one that holds at every `n`. What completes the statement is its cause, a finite word
(`forall_of_base_and_step`, `descent_reaches_ground`). -/
theorem no_finite_set_of_readings_completes (S : Finset ℕ) :
    ∃ Q : ℕ → Prop, ∃ _ : DecidablePred Q, (∀ n ∈ S, Q n) ∧ ¬ ∀ n, Q n := by
  refine ⟨fun n => n ≤ S.sup id, fun n => Nat.decLe _ _, fun n hn => Finset.le_sup (f := id) hn, fun h => ?_⟩
  have := h (S.sup id + 1)
  omega

/-! ## 4. The half is forced by a reversal and a pairing -/

section ScaledForm

open Matrix

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] **The pulled-back form reads the carried mode**:
`v† (Bᴴ G B) v = (B v)† G (B v)`. The complex chart of `HNN/Floquet.energy_transport`. -/
theorem form_transport (B G : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((Bᴴ * G * B) *ᵥ v) = star (B *ᵥ v) ⬝ᵥ (G *ᵥ (B *ᵥ v)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- [proved-derived; formal-checked] **A form scaled by `q` places its modes at `‖α‖² = q`**: with `Bᴴ G B = q • G`
(the reversal against the pairing) and a mode `B v = α v` whose form `v†Gv` is not zero. -/
theorem scaled_form_places_mode (B G : Matrix n n ℂ) (q : ℝ) (hBG : Bᴴ * G * B = (q : ℂ) • G)
    (v : n → ℂ) (α : ℂ) (hv : B *ᵥ v = α • v) (hG : star v ⬝ᵥ (G *ᵥ v) ≠ 0) :
    ‖α‖ ^ 2 = q := by
  have h := form_transport B G v
  rw [hBG, hv, smul_mulVec, dotProduct_smul, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
  have h2 : ((q : ℂ) - star α * α) * (star v ⬝ᵥ (G *ᵥ v)) = 0 := by
    rw [sub_mul, h]; ring
  have h3 : (q : ℂ) = star α * α := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hG)
  have h4 : (q : ℂ) = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
    rw [h3, Complex.star_def, Complex.conj_mul']; push_cast; rfl
  exact (Complex.ofReal_injective h4).symm

/-- [proved-derived; formal-checked] **The half**: the mode stands at `‖α‖ = √q`. The count `q` is not assumed
nonnegative: the form forces it. -/
theorem scaled_form_mode_is_half (B G : Matrix n n ℂ) (q : ℝ) (hBG : Bᴴ * G * B = (q : ℂ) • G)
    (v : n → ℂ) (α : ℂ) (hv : B *ᵥ v = α • v) (hG : star v ⬝ᵥ (G *ᵥ v) ≠ 0) :
    ‖α‖ = Real.sqrt q := by
  rw [← scaled_form_places_mode B G q hBG v α hv hG, Real.sqrt_sq (norm_nonneg α)]

/-- [proved-derived; formal-checked] **At weight `k` the mode stands at `q^(k/2)`**: a move that scales the pairing by
`q^k` (`q ≥ 0`) has `‖α‖ = q^(k/2)`. -/
theorem scaled_form_mode_at_weight (B G : Matrix n n ℂ) (q : ℝ) (hq : 0 ≤ q) (k : ℕ)
    (hBG : Bᴴ * G * B = ((q ^ k : ℝ) : ℂ) • G)
    (v : n → ℂ) (α : ℂ) (hv : B *ᵥ v = α • v) (hG : star v ⬝ᵥ (G *ᵥ v) ≠ 0) :
    ‖α‖ = q ^ ((k : ℝ) / 2) := by
  rw [scaled_form_mode_is_half B G (q ^ k) hBG v α hv hG, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hq]
  congr 1
  ring

/-- [proved-derived; formal-checked] **The real chart, the equality case of the parametron's certificate**: with
`Mᵀ G M = ρ² • G` and a real mode `M v = μ v` whose energy `v ⬝ᵥ G v` is not zero, `μ² = ρ²`. The inequality
`MᵀGM ⪯ ρ²G` is `HNN/Floquet.FloquetCertifies`. -/
theorem real_scaled_form_places_mode (M G : Matrix n n ℝ) (ρ2 : ℝ) (hMG : Mᵀ * G * M = ρ2 • G)
    (v : n → ℝ) (μ : ℝ) (hv : M *ᵥ v = μ • v) (hG : v ⬝ᵥ (G *ᵥ v) ≠ 0) : μ ^ 2 = ρ2 := by
  have h : v ⬝ᵥ ((Mᵀ * G * M) *ᵥ v) = (M *ᵥ v) ⬝ᵥ (G *ᵥ (M *ᵥ v)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [hMG, hv, smul_mulVec, dotProduct_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
  have h2 : (ρ2 - μ ^ 2) * (v ⬝ᵥ (G *ᵥ v)) = 0 := by
    rw [sub_mul, h]; ring
  have h3 := sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hG)
  exact h3.symm

end ScaledForm

/-! ## 5. A route of length `2m` is two routes of length `m` that meet -/

section MeetInMiddle

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

/-- [proved-standard; formal-checked] **Two sweeps that meet**: for a symmetric move matrix,
`(A^(2m)) x y = Σ_z (A^m) x z · (A^m) y z`. The routes of length `2m` from `x` to `y` are the pairs of routes of length
`m`, one from each end, that arrive at one state. -/
theorem meet_in_middle (A : Matrix n n R) (hA : A.IsSymm) (m : ℕ) (x y : n) :
    (A ^ (2 * m)) x y = ∑ z, (A ^ m) x z * (A ^ m) y z := by
  rw [two_mul, pow_add, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun z _ => by rw [(hA.pow m).apply y z]

/-- [proved-standard; formal-checked] **The same identity as a pairing of the two sweeps**:
`(A^(2m)) x y = ⟨Aᵐ δ_x, Aᵐ δ_y⟩`. -/
theorem meet_in_middle_sweeps (A : Matrix n n R) (hA : A.IsSymm) (m : ℕ) (x y : n) :
    (A ^ (2 * m)) x y = ((A ^ m) *ᵥ Pi.single x 1) ⬝ᵥ ((A ^ m) *ᵥ Pi.single y 1) := by
  rw [meet_in_middle A hA m x y, mulVec_single_one, mulVec_single_one]
  exact Finset.sum_congr rfl fun z _ => by
    simp only [Matrix.col_apply]
    rw [(hA.pow m).apply x z, (hA.pow m).apply y z]

end MeetInMiddle

/-- [proved-standard; formal-checked] **A landmark pins an orbit and divides the volume left to search**: the orbit of
the pinned state times its stabilizer is the group (Mathlib's
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`); pinning a base one landmark at a time factors the volume as
the product of the orbits (Sims 1970). -/
theorem landmark_divides_volume (G : Type*) {X : Type*} [Group G] [MulAction G X] (b : X) [Fintype G]
    [Fintype (MulAction.orbit G b)] [Fintype (MulAction.stabilizer G b)] :
    Fintype.card (MulAction.orbit G b) * Fintype.card (MulAction.stabilizer G b) = Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group G b

end Holonics.Foundation.FiniteKey
