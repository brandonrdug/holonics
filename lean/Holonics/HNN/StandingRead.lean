import Holonics.HNN.Ratio

/-!
# HNN.StandingRead: the face reads the receiving parametron's bound harmonic coordinate

[definition; agent-inferred] Decision 26 of the step 4 design (`docs/plans/THE_REBUILD.md`,
campaign 1's repair), from the located failure and Sol's derivation. The receiving read
`f = R P_R^(τ_R) v_R` reads only the word's change `v_R`, which opens at zero; at zero change the
face reads nothing the constitution retains. The repair reads the receiving parametron's **bound
harmonic coordinate** `h_R`: a coordinate of its constitution fixed by the ring,
`P_R h_R = h_R` (the harmonic, dormant part of the motion), changed only by deposition:

```text
read        f_j = R P_R^(τ_R(j)) (v_R(e_j) + h_R) = R P_R^(τ_R(j)) v_R(e_j) + R h_R
return      ⟨g, f⟩ = ⟨(P_R^τ)ᵀ Rᵀ g, v_R⟩ + ⟨Π_harm Rᵀ g, h_R⟩     (wave + harmonic return)
deposit     h_R ← h_R + η Π_harm Rᵀ g        stays harmonic: P_R h_R' = h_R'
```

The standing term `R h_R` persists when the word opens at zero change, independent of the
path's rotation and of the wave. A constant supplied without such a constitutive coordinate would
invent a port value; this law reads only an actual coordinate of the constitution.

Everything is realified and exact, as in `HNN/Normal`: statements are over a commutative ring
(so over `ℚ`), with transposes; the read `R` and the ring's port operator `P` are matrices.

[proved-derived; formal-checked] What is proved.

1. **The harmonic read is rotation invariant** (`harmonic_read_rotation_invariant`): if
   `P h = h` then `R P^t (v + h) = R P^t v + R h` at every receiving phase `t`, and at zero
   change the read is `R h` (`standing_read_at_zero_change`). A coordinate the ring rotates is
   not standing (`rotating_coordinate_is_not_standing`).
2. **The pullback** (`standing_read_pullback`): the pairing of a covector `g` with the read splits
   into the existing wave return `⟨(P^t)ᵀ Rᵀ g, v⟩` (`HNN/Ratio.receivingPhase_pullback` in the
   realified chart) and the harmonic return `⟨Rᵀ g, h⟩ = ⟨Π Rᵀ g, h⟩`, `Π` the orthogonal
   projection onto the fixed space of `P` (`HarmonicProjection`: idempotent, commuting with `P`,
   with range fixed by `P`, fixing every fixed vector, symmetric). The harmonic part of the wave
   is itself rotation invariant (`harmonic_part_rotation_invariant`), and a deposit along the
   harmonic return keeps the coordinate harmonic and in the projection's range
   (`harmonic_deposit_stays_standing`). The projection is not vacuous
   (`harmonicProjection_witness`, the half-turn sheet `diag(1, −1)` with `Π = diag(1, 0)`).
3. **The face's common-shift fibre** (`standing_read_common_shift`): a standing read that is a
   common shift of every class, `R h = c·1`, leaves every code length unchanged (the owner's
   `face_add_common`), so only the standing read's differences between classes reach the face.

[open] That today's lock coordinate already supplies a readable harmonic value is not proved; the
rotation-invariant feature measured in the located failure supports looking at this mode, and the
exposure's receipt decides.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.StandingRead

open Matrix
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.HNN.Ratio (codeLength codeLength_eq_face)

/-! ## 1. The standing read -/

section Read

variable {𝕜 : Type*} [CommRing 𝕜] {n m : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The receiving read** at receiving phase `t`: `f = R P^t (v + h)`, the word's
change `v` and the bound harmonic coordinate `h` read through the ring's port operator `P` and the
receiving map `R`. -/
def standingRead (R : Matrix m n 𝕜) (P : Matrix n n 𝕜) (t : ℕ) (v h : n → 𝕜) : m → 𝕜 :=
  R *ᵥ ((P ^ t) *ᵥ (v + h))

/-- [proved-derived; formal-checked] A coordinate the ring fixes is fixed by every power of it. -/
theorem pow_mulVec_fixed {P : Matrix n n 𝕜} {h : n → 𝕜} (hP : P *ᵥ h = h) (t : ℕ) :
    (P ^ t) *ᵥ h = h := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mulVec_mulVec, hP, ih]

/-- [proved-derived; formal-checked] **The harmonic read is rotation invariant.** If the ring fixes
the bound coordinate, `P h = h`, then at every receiving phase `t`,
`R P^t (v + h) = R P^t v + R h`: the standing term `R h` is independent of the phase, of the
ring's rotation and of the wave `v`. -/
theorem harmonic_read_rotation_invariant (R : Matrix m n 𝕜) {P : Matrix n n 𝕜} {h : n → 𝕜}
    (hP : P *ᵥ h = h) (v : n → 𝕜) (t : ℕ) :
    standingRead R P t v h = R *ᵥ ((P ^ t) *ᵥ v) + R *ᵥ h := by
  simp only [standingRead, mulVec_add, pow_mulVec_fixed hP]

/-- [proved-derived; formal-checked] **The read at zero change is the standing read.** When the
word opens at zero change, the face reads `R h` at every receiving phase. -/
theorem standing_read_at_zero_change (R : Matrix m n 𝕜) {P : Matrix n n 𝕜} {h : n → 𝕜}
    (hP : P *ᵥ h = h) (t : ℕ) :
    standingRead R P t 0 h = R *ᵥ h := by
  rw [harmonic_read_rotation_invariant R hP 0 t, mulVec_zero, mulVec_zero, zero_add]

/-- [definition] **The harmonic projection** of the ring's port operator `P`: the orthogonal
projection `Π` onto the fixed space of `P`. It is idempotent, commutes with `P`, has range fixed
by `P`, fixes every vector `P` fixes, and is symmetric (so it is the pairing's own projection). -/
structure HarmonicProjection (P Hm : Matrix n n 𝕜) : Prop where
  idem : Hm * Hm = Hm
  comm : P * Hm = Hm * P
  onto : P * Hm = Hm
  fixes : ∀ h : n → 𝕜, P *ᵥ h = h → Hm *ᵥ h = h
  symm : Hmᵀ = Hm

/-- [proved-derived; formal-checked] **The harmonic part is rotation invariant**:
`Π P^t v = Π v`. The wave never moves the harmonic coordinate; only deposition does. -/
theorem harmonic_part_rotation_invariant {P Hm : Matrix n n 𝕜} (hH : HarmonicProjection P Hm)
    (v : n → 𝕜) (t : ℕ) :
    Hm *ᵥ ((P ^ t) *ᵥ v) = Hm *ᵥ v := by
  have hfix : ∀ k : ℕ, P ^ k * Hm = Hm := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, hH.onto, ih]
  have hcomm : Hm * P ^ t = P ^ t * Hm :=
    (Commute.pow_right (show Commute Hm P from hH.comm.symm) t).eq
  rw [mulVec_mulVec, hcomm, hfix t]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] The transpose carries a covector through a read:
`⟨y, A x⟩ = ⟨Aᵀ y, x⟩`. -/
theorem pairing_transpose {k : Type*} [Fintype k] (A : Matrix k n 𝕜) (y : k → 𝕜) (x : n → 𝕜) :
    y ⬝ᵥ (A *ᵥ x) = (Aᵀ *ᵥ y) ⬝ᵥ x := by
  rw [dotProduct_mulVec, ← mulVec_transpose]

/-- [proved-derived; formal-checked] **The standing read's pullback.** For a covector `g` on the
logits:
* the pairing with the read splits into the wave return and the harmonic return,
  `⟨g, R P^t (v + h)⟩ = ⟨(P^t)ᵀ Rᵀ g, v⟩ + ⟨Π Rᵀ g, h⟩`;
* the pairing with the standing term is `⟨g, R h⟩ = ⟨Rᵀ g, h⟩`;
* and it equals the pairing of the projection `Π Rᵀ g` with `h`.

So the bound coordinate receives `Π Rᵀ g`, alongside the wave's existing return. -/
theorem standing_read_pullback [Fintype m] (R : Matrix m n 𝕜) {P Hm : Matrix n n 𝕜}
    (hH : HarmonicProjection P Hm) {h : n → 𝕜} (hP : P *ᵥ h = h) (g : m → 𝕜) (v : n → 𝕜)
    (t : ℕ) :
    g ⬝ᵥ standingRead R P t v h = ((P ^ t)ᵀ *ᵥ (Rᵀ *ᵥ g)) ⬝ᵥ v + (Hm *ᵥ (Rᵀ *ᵥ g)) ⬝ᵥ h ∧
      g ⬝ᵥ (R *ᵥ h) = (Rᵀ *ᵥ g) ⬝ᵥ h ∧
      (Rᵀ *ᵥ g) ⬝ᵥ h = (Hm *ᵥ (Rᵀ *ᵥ g)) ⬝ᵥ h := by
  have hproj : (Rᵀ *ᵥ g) ⬝ᵥ h = (Hm *ᵥ (Rᵀ *ᵥ g)) ⬝ᵥ h := by
    rw [dotProduct_comm (Hm *ᵥ _), pairing_transpose Hm h, hH.symm, hH.fixes h hP, dotProduct_comm]
  have hstand : g ⬝ᵥ (R *ᵥ h) = (Rᵀ *ᵥ g) ⬝ᵥ h := pairing_transpose R g h
  refine ⟨?_, hstand, hproj⟩
  rw [harmonic_read_rotation_invariant R hP v t, dotProduct_add, hstand, hproj,
    pairing_transpose R g, pairing_transpose (P ^ t) (Rᵀ *ᵥ g)]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **A deposit along the harmonic return stays standing.** The
deposit `h' = h + η Π x` of a harmonic coordinate `h` along the projection of any return `x` is
again fixed by the ring and lies in the projection's range: only deposition changes the bound
coordinate, and it keeps it harmonic. -/
theorem harmonic_deposit_stays_standing {P Hm : Matrix n n 𝕜} (hH : HarmonicProjection P Hm)
    {h : n → 𝕜} (hP : P *ᵥ h = h) (η : 𝕜) (x : n → 𝕜) :
    P *ᵥ (h + η • (Hm *ᵥ x)) = h + η • (Hm *ᵥ x) ∧
      Hm *ᵥ (h + η • (Hm *ᵥ x)) = h + η • (Hm *ᵥ x) := by
  constructor
  · rw [mulVec_add, mulVec_smul, mulVec_mulVec, hH.onto, hP]
  · rw [mulVec_add, mulVec_smul, mulVec_mulVec, hH.idem, hH.fixes h hP]

end Read

/-! ### Witnesses -/

/-- The half-turn sheet `P = diag(1, −1)` on `ℚ²`: one standing coordinate, one rotating one. -/
def halfTurnSheet : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- Its harmonic projection `Π = diag(1, 0)`. -/
def halfTurnHarmonic : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]

/-- The read summing both coordinates. -/
def sumRead : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1]

/-- [proved-derived; formal-checked] **The harmonic projection is not vacuous.** For the half-turn
sheet `diag(1, −1)`, `diag(1, 0)` is its harmonic projection. -/
theorem harmonicProjection_witness : HarmonicProjection halfTurnSheet halfTurnHarmonic := by
  refine ⟨?_, ?_, ?_, fun h hh => ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [halfTurnHarmonic, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [halfTurnSheet, halfTurnHarmonic, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [halfTurnSheet, halfTurnHarmonic, Matrix.mul_apply, Fin.sum_univ_two]
  · have h1 := congrFun hh 1
    simp [halfTurnSheet, mulVec, dotProduct, Fin.sum_univ_two] at h1
    have h10 : h 1 = 0 := by linarith
    funext i
    fin_cases i <;> simp [halfTurnHarmonic, mulVec, dotProduct, Fin.sum_univ_two, h10]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [halfTurnHarmonic]

/-- [counterexample; formal-checked] **A rotating coordinate is not standing.** On the half-turn
sheet, the coordinate `(0, 1)` is not fixed (`P(0, 1) = (0, −1)`), and its read through the sum
flips sign at one tick, `R P (0, 1) = −1` while `R (0, 1) = 1`; the fixed coordinate `(1, 0)`
reads `1` at every tick. The hypothesis `P h = h` of `harmonic_read_rotation_invariant` is
load-bearing. -/
theorem rotating_coordinate_is_not_standing :
    halfTurnSheet *ᵥ ![0, 1] ≠ ![0, 1] ∧
      sumRead *ᵥ ((halfTurnSheet ^ 1) *ᵥ ![0, 1]) = ![-1] ∧ sumRead *ᵥ ![0, 1] = ![1] ∧
      ∀ t : ℕ, standingRead sumRead halfTurnSheet t 0 ![1, 0] = ![1] := by
  have hfix : halfTurnSheet *ᵥ ![1, 0] = ![1, 0] := by
    funext i; fin_cases i <;> simp [halfTurnSheet, mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨fun h => ?_, ?_, ?_, fun t => ?_⟩
  · have := congrFun h 1
    simp [halfTurnSheet, mulVec, dotProduct, Fin.sum_univ_two] at this
    norm_num at this
  · funext i; fin_cases i; simp [sumRead, halfTurnSheet, mulVec, dotProduct, Fin.sum_univ_two]
  · funext i; fin_cases i; simp [sumRead, mulVec, dotProduct, Fin.sum_univ_two]
  · rw [standing_read_at_zero_change sumRead hfix t]
    funext i; fin_cases i; simp [sumRead, mulVec, dotProduct, Fin.sum_univ_two]

/-! ## 2. The face's common-shift fibre -/

section CommonShift

variable {Index : Type*} [Fintype Index] [Nonempty Index]

/-- [proved-derived; formal-checked] **A common shift is invisible to the face.** If the standing
read is a common shift of every class, `(R h)_c = s`, adding it to the logits leaves every code
length unchanged (the owner's `face_add_common`): only the standing read's differences between
classes reach the receiver's face. -/
theorem standing_read_common_shift (f : Index → ℝ) (s : ℝ) (t : Index) :
    codeLength (fun c => f c + s) t = codeLength f t := by
  rw [codeLength_eq_face, codeLength_eq_face]
  have hshift := face_add_common (fun c => f c * Real.log 2) (s * Real.log 2)
  have hfun : (fun c => (f c + s) * Real.log 2) =
      fun c => (fun c => f c * Real.log 2) c + s * Real.log 2 := by
    funext c; ring
  rw [hfun, hshift]

end CommonShift

section Audit

#print axioms pow_mulVec_fixed
#print axioms harmonic_read_rotation_invariant
#print axioms standing_read_at_zero_change
#print axioms harmonic_part_rotation_invariant
#print axioms pairing_transpose
#print axioms standing_read_pullback
#print axioms harmonic_deposit_stays_standing
#print axioms harmonicProjection_witness
#print axioms rotating_coordinate_is_not_standing
#print axioms standing_read_common_shift

end Audit

end Holonics.HNN.StandingRead
