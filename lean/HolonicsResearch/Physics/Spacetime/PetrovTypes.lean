import HolonicsResearch.Physics.Spacetime.Raychaudhuri
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Petrov's types: the tide and the frame dragging joined as one complex `Q`, sorted by its powers

[definition] The box of #410, "Curvature's strain and rotation: the Weyl tensor's electric/magnetic
split and Petrov's classification; Raychaudhuri's equation from a Lorentzian metric, connection and
congruence", is part done in #1024 by `Physics/Spacetime/Raychaudhuri`, whose "What is not claimed"
opens: "Petrov's classification (the eigenvalue types of `E + iH`) is not stated" (atlas
`coupling.weyl-electric-magnetic` carries the same limit). This module states the classification as
finite algebra. Sources: that owner's §4 (`WeylSymmetries`, `electric`, `magnetic`, `electric_symm`,
`electric_traceless`, `magnetic_symm`, `magnetic_traceless`, used here as they stand); the Swing
record
(`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`
§5.6: "tidal curvature is a strain field, frame dragging a rotation field … joined as the complex
`E + iB` whose eigenvalues give the Petrov classification"); the record of November 19 that answers
#1024 (its file name opens `2026-11-19_A_CONGRUENCES_RATE_IS_A_BOOST_AND_A_TURN`), which names
Petrov's classification as the box's part left; `Geometry/Motion` (atlas `motion.turn-boost-split`);
the two-dimensional counterpart, a site's traceless part squaring to a quarter of its discriminant
(atlas `landmark.site-traceless-square`); and definite storage forbidding a square-zero defect
(atlas `coupling.holonic-invariant-storage-nilpotent`).

The observer `u = e₀` reads a tensor `C` with the Weyl symmetries as its electric part `E` (the tide)
and its magnetic part `H` (frame dragging), both real, symmetric and traceless. They are joined as
one complex matrix `Q = E + iH` (`complexQ`, `weylQ`): complex symmetric (`Qᵀ = Q`, not Hermitian)
and traceless, with the invariants `I = tr Q²` (`invI`) and `J = tr Q³` (`invJ`). Petrov's six types
(`PetrovType`) are read on `Q` by its powers and its shifted products (`HasType`): O `Q = 0`; N
`Q ≠ 0`, `Q² = 0`; III `Q² ≠ 0`, `Q³ = 0`; D `(Q − λ)(Q + 2λ) = 0` for some `λ ≠ 0`; II
`(Q − λ)²(Q + 2λ) = 0` and `(Q − λ)(Q + 2λ) ≠ 0` for some `λ ≠ 0`; I `I³ ≠ 6J²`. The classifier
`classify` reads the type from `I`, `J` and the repeated eigenvalue `λ = −J/I` (`repeatedRoot`).

[proved-standard; formal-checked] What is proved. Items 2 to 5 hold for any traceless `3 × 3`
matrix over a field of characteristic zero (the symmetry of `Q` is not used there); item 6 is over ℝ
read through ℂ; items 1, 7 and 8 are over ℂ.

1. **The observer's `Q`** (`weylQ_symm`, `weylQ_trace`). For `C` with `WeylSymmetries`,
   `Q = E + iH` is symmetric and traceless, from the owner's four lemmas.
2. **Cayley–Hamilton for a traceless `3 × 3`** (`trace_smul_one`, `cayley_hamilton`, `det_eq`,
   `charpoly_eq`). `Q³ = (I/2)·Q + (J/3)·1` and `det Q = J/3`, so Mathlib's characteristic
   polynomial is `X³ − (I/2)X − J/3` (computed entry by entry).
3. **The repeated root** (`discriminant_eq`, `repeated_root_iff`, `charpoly_repeated_root_iff`,
   `hasType_I_iff`). The discriminant `−4p³ − 27q²` at `p = −I/2`, `q = −J/3` is `(I³ − 6J²)/2`;
   `X³ − (I/2)X − J/3` and its derivative share a root iff `I³ = 6J²` (the root is `−J/I`, or `0`
   where `I = 0`). So type I is the case of three distinct eigenvalues (over ℂ, where the polynomial
   splits), and the other five types are the algebraically special ones.
4. **Petrov's classification** (`shifted_mul`, `shifted_sq_mul`, `invariants_of_shifted`,
   `invariants_of_shifted_sq`, `pow_three_eq_zero_iff`, `charpoly_of_invariants`,
   `charpoly_of_nilpotent`, `charpoly_of_hasType_D_or_II`, `ne_zero_of_hasType_D`,
   `special_of_invariants`, `hasType_classify`, `classify_eq_of_hasType`, `existsUnique_hasType`,
   `hasType_unique`, `special_iff`, `pow_three_eq_zero_iff_classify`). Every traceless `Q` has
   exactly one of the six types, and it is `classify Q`. Type D's or II's relation at `λ ≠ 0` forces
   `I = 6λ²` and `J = −6λ³`, so the eigenvalues are `(λ, λ, −2λ)` and `λ = −J/I`; `Q³ = 0` iff
   `I = J = 0`, the types III, N and O, with polynomial `X³`; and D against II is whether
   `(Q − λ)(Q + 2λ)` vanishes.
5. **The type does not depend on the field it is read in** (`invI_map`, `invJ_map`, `shifted_map`,
   `matrix_map_eq_zero_iff`, `classify_map`). A field map `f : K → L` carries `I`, `J`, `λ` and every
   shifted product, so `classify (f Q) = classify Q`.
6. **No purely electric Weyl tensor is null** (`eq_zero_of_symm_sq`, `eq_zero_of_symm_pow_three`,
   `not_hasType_II_of_symm`, `classify_of_symm`, `classify_weylQ_of_magnetic_eq_zero`,
   `weylQ_not_null_of_magnetic_eq_zero`). A real symmetric `E` with `E² = 0` is `0`, since
   `(E²)_ii = Σ_j E_ij²`: no spectral theorem is used. The same reading kills `E³ = 0`, and type II
   too, whose shifted product `(E − λ)(E + 2λ)` is symmetric with square
   `(E − λ)²(E + 2λ)·(E + 2λ) = 0`. So a real symmetric traceless `E` is of type I, D or O, and,
   through item 5, a Weyl tensor with `H = 0` has `Q` of type I, D or O, never N, III or II.
7. **Strain and rotation cancel in the null types** (`complexQ_transpose`, `complexQ_trace`,
   `complexQ_eq_zero_iff`, `complexQ_sq`, `complexQ_sq_eq_zero_iff`, `hasType_N_iff`,
   `weylQ_sq_eq_zero_iff`). `(E + iH)² = (E² − H²) + i(EH + HE)`, so `Q² = 0` iff `E² − H² = 0` and
   `EH + HE = 0`: type N is a nonzero pair whose strain and rotation have one square and anticommute.
8. **The witnesses** (`schwarzschildTide_admissible`, `classify_schwarzschild`, `planeWave_eq`,
   `classify_planeWave`, `classify_typeIIIQ`, `classify_typeIIQ`, `classify_typeIQ`). Each is
   symmetric and traceless. D: `E = μ·diag(−2, 1, 1)`, `μ ≠ 0`, `H = 0` (the Schwarzschild tide);
   N: the plane wave `E = diag(0, 1, −1)`, `H` the same tide turned by an eighth of a turn about
   the first axis, `Q = [[0, 0, 0], [0, 1, i], [0, i, −1]]`; III: `Q = [[0, 1, i], [1, 0, 0], [i, 0, 0]]`;
   II: `Q = λ·diag(1, 1, −2) + [[1, i, 0], [i, −1, 0], [0, 0, 0]]` for every `λ ≠ 0`;
   I: `Q = diag(1, −1, 0)`.

What is not claimed. The type is read for one observer at one point: its Lorentz invariance (a boost
of the observer acting on `(E, H)` as a complex rotation `Q ↦ OQOᵀ`, `O ∈ SO(3, ℂ)`) is not stated.
The principal null directions and their multiplicities, the Bel–Debever criteria and the
Newman–Penrose scalars `Ψ₀ … Ψ₄` (whose invariants are normalized otherwise) are not stated. That
every complex symmetric traceless `Q` is the `Q` of some tensor with the Weyl symmetries is not
stated. The witnesses here are given as matrices; `Physics/Spacetime/CurvatureJets` builds `C` from
a metric's 2-jet, a plane wave of type N (`wave_classify`) and the point mass's weak field, whose
tide is `μ·diag(−2, 1, 1)` with `μ = M/r³` under its sign convention (`pointMass_classify`). The
box's other part stays owed: the deviation equation `J″ = −RJ` along a geodesic (the tide
`R_ij = R_(i0j0)` from a metric's connection at a point is `CurvatureJets`').

Read on the Swing. In Motion's split a rate against a receiver's metric is a skew turn plus a
self-adjoint boost. The tide `E` is the strain, a self-adjoint boost of the deviation (the owner
reads it as the vacuum's tidal matrix in Raychaudhuri's equation). The frame dragging `H` is the
rotation field, the turn it drives in gyroscopes carried along; as a matrix it is symmetric too
(`magnetic_symm`; atlas `coupling.weyl-electric-magnetic`: "both are boost-type in Motion's split"),
and its turn is carried by the quarter-turn `i = e^{iπ/2}` at which it enters `Q`, not by a skew
part. Joined at that quarter-turn the two square to `(E² − H²) + i(EH + HE)` (`complexQ_sq`): a
strain and a rotation of one size that anticommute cancel into a nilpotent `Q`, and the null types
are those in which they do, N at the second power (`complexQ_sq_eq_zero_iff`) and III at the third.
A nilpotent `Q` generates a unipotent flow, `exp(tQ) = 1 + tQ + t²Q²/2`, and is read as the third
kind of motion, free fall's shear, as a null site's traceless part squares to zero in two
dimensions (atlas `landmark.site-traceless-square`; the flow is not stated here). A tide with no frame
dragging cannot cancel: its square's diagonal is a sum of squares, a definite storage that forbids
a square-zero defect (atlas `coupling.holonic-invariant-storage-nilpotent`), so the null types, and
type II with them, need `H`.

The computational object is the helical pair interaction read on one observer's curvature: the tide
`E` and the frame dragging `H` are a pair, carried together as one undivided complex `Q = E + iH`
with the second strand joined at the quarter-turn `i`, and the type is read from the pair's own
powers `Q`, `Q²`, `Q³`, which Cayley–Hamilton closes at the third: every higher power winds back
onto `1`, `Q`, `Q²` with the carries `I/2` and `J/3`. The invariants `I`, `J` and `λ` are the
observer's faces of `Q`, and the type is a placement of its eigenvalues: three apart (I), two
together at `λ ≠ 0` with the shifted product closed (D) or open (II), or all three at zero with the
first vanishing power the first, second or third (O, N, III). Of the winding guide's six general
objects this touches the pair (`E` and `H` joined as `Q`) and faces and placement (`I`, `J`, `λ` and
the type); the helix, the cell holonomy, the tube (the congruence of `Raychaudhuri`, along which no
type is read here) and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.PetrovTypes

open Matrix Polynomial
open Holonics.Physics.Spacetime.Raychaudhuri

/-- [definition] The `3 × 3` matrices over `K`. -/
abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-! ## 1. The observer's `Q = E + iH` -/

section Observer

/-- [definition] The complex matrix `Q = E + iH` of a real pair `(E, H)`. -/
def complexQ (E H : Mat3 ℝ) : Mat3 ℂ := Matrix.of fun i j => (E i j : ℂ) + (H i j : ℂ) * Complex.I

/-- [definition] **The observer's `Q`**: `Q = E + iH` of a Weyl-type tensor `C` read by `u = e₀`. -/
def weylQ (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Mat3 ℂ :=
  complexQ (Matrix.of (electric C)) (Matrix.of (magnetic C))

variable {C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}

/-- [proved-standard; formal-checked] **`Q` is symmetric** (`Qᵀ = Q`, not Hermitian). -/
theorem weylQ_symm (h : WeylSymmetries C) : (weylQ C)ᵀ = weylQ C := by
  ext i j
  simp only [weylQ, complexQ, transpose_apply, of_apply, electric_symm h j i, magnetic_symm h j i]

/-- [proved-standard; formal-checked] **`Q` is traceless.** -/
theorem weylQ_trace (h : WeylSymmetries C) : (weylQ C).trace = 0 := by
  have hE := electric_traceless h
  have hH := magnetic_traceless h
  rw [Fin.sum_univ_three] at hE hH
  rw [trace_fin_three]
  simp only [weylQ, complexQ, of_apply]
  have hE' : (electric C 0 0 : ℂ) + electric C 1 1 + electric C 2 2 = 0 := by exact_mod_cast hE
  have hH' : (magnetic C 0 0 : ℂ) + magnetic C 1 1 + magnetic C 2 2 = 0 := by exact_mod_cast hH
  linear_combination hE' + Complex.I * hH'

end Observer

/-! ## 2. The invariants and Cayley–Hamilton -/

section Invariants

variable {K : Type*} [Field K]

/-- [definition] The invariant `I = tr Q²`. -/
def invI (Q : Mat3 K) : K := (Q ^ 2).trace

/-- [definition] The invariant `J = tr Q³`. -/
def invJ (Q : Mat3 K) : K := (Q ^ 3).trace

/-- [proved-standard; formal-checked] `tr(c·1) = 3c`. -/
theorem trace_smul_one (c : K) : (c • (1 : Mat3 K)).trace = 3 * c := by
  rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, mul_comm]
  norm_num

variable [CharZero K] {Q : Mat3 K}

/-- [proved-standard; formal-checked] **Cayley–Hamilton for a traceless `3 × 3`**:
`Q³ = (I/2)·Q + (J/3)·1`. -/
theorem cayley_hamilton (hQ : Q.trace = 0) : Q ^ 3 = (invI Q / 2) • Q + (invJ Q / 3) • (1 : Mat3 K) := by
  rw [trace_fin_three] at hQ
  have h22 : Q 2 2 = -Q 0 0 - Q 1 1 := by linear_combination hQ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invI, invJ, pow_three, sq, mul_apply, Fin.sum_univ_three, trace_fin_three, h22,
      one_apply] <;> ring

/-- [proved-standard; formal-checked] **The determinant of a traceless `3 × 3`** is `J/3`. -/
theorem det_eq (hQ : Q.trace = 0) : Q.det = invJ Q / 3 := by
  rw [trace_fin_three] at hQ
  have h22 : Q 2 2 = -Q 0 0 - Q 1 1 := by linear_combination hQ
  simp [invJ, pow_three, mul_apply, Fin.sum_univ_three, trace_fin_three, h22, det_fin_three]
  ring

/-- [proved-standard; formal-checked] **The characteristic polynomial** of a traceless `3 × 3` is
`X³ − (I/2)X − J/3`. -/
theorem charpoly_eq (hQ : Q.trace = 0) : Q.charpoly = X ^ 3 - C (invI Q / 2) * X - C (invJ Q / 3) := by
  rw [← det_eq hQ]
  rw [trace_fin_three] at hQ
  have h22 : Q 2 2 = -Q 0 0 - Q 1 1 := by linear_combination hQ
  have eI : invI Q / 2 = -(Q 0 0 * Q 1 1 + Q 0 0 * Q 2 2 + Q 1 1 * Q 2 2 - Q 0 1 * Q 1 0
      - Q 0 2 * Q 2 0 - Q 1 2 * Q 2 1) := by
    simp only [invI, sq, mul_apply, Fin.sum_univ_three, trace_fin_three, h22]
    ring
  rw [eI, Matrix.charpoly, det_fin_three, det_fin_three]
  simp only [charmatrix_apply, Fin.isValue, Fin.reduceEq, diagonal_apply_eq,
    diagonal_apply_ne, ne_eq, not_false_eq_true, map_sub, map_neg, map_mul, map_add, h22]
  ring

end Invariants

/-! ## 3. The repeated root -/

section Root

variable {K : Type*} [Field K] [CharZero K] {Q : Mat3 K}

/-- [proved-standard; formal-checked] **The discriminant** of `X³ + pX + q` at `p = −I/2`,
`q = −J/3`: `−4p³ − 27q² = (I³ − 6J²)/2`. -/
theorem discriminant_eq (I J : K) : -4 * (-(I / 2)) ^ 3 - 27 * (-(J / 3)) ^ 2 = (I ^ 3 - 6 * J ^ 2) / 2 := by
  ring

/-- [proved-standard; formal-checked] **A repeated root of `X³ − (I/2)X − J/3`** (a root of it and of
its derivative) exists iff `I³ = 6J²`. -/
theorem repeated_root_iff (I J : K) :
    (∃ r : K, r ^ 3 - I / 2 * r - J / 3 = 0 ∧ 3 * r ^ 2 - I / 2 = 0) ↔ I ^ 3 = 6 * J ^ 2 := by
  constructor
  · rintro ⟨r, h1, h2⟩
    have hI : I = 6 * r ^ 2 := by linear_combination -2 * h2
    have hJ : J = -6 * r ^ 3 := by linear_combination -3 * h1 - 3 / 2 * r * hI
    rw [hI, hJ]; ring
  · intro h
    by_cases hI : I = 0
    · have hJ : J = 0 := by
        rw [hI] at h
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linear_combination -h / 6)
      exact ⟨0, by rw [hI, hJ]; ring, by rw [hI]; ring⟩
    · refine ⟨-(J / I), ?_, ?_⟩
      · field_simp
        linear_combination J * h
      · field_simp
        linear_combination -h

/-- [proved-standard; formal-checked] **The repeated root read on the characteristic polynomial**:
for a traceless `Q`, `charpoly Q` and its derivative share a root iff `I³ = 6J²`. -/
theorem charpoly_repeated_root_iff (hQ : Q.trace = 0) :
    (∃ r : K, Q.charpoly.IsRoot r ∧ (derivative Q.charpoly).IsRoot r) ↔ invI Q ^ 3 = 6 * invJ Q ^ 2 := by
  rw [← repeated_root_iff, charpoly_eq hQ]
  norm_num [IsRoot]

end Root

/-! ## 4. The six types -/

section Types

/-- [definition] **Petrov's six types.** -/
inductive PetrovType
  | I
  | II
  | D
  | III
  | N
  | O
  deriving DecidableEq

variable {K : Type*} [Field K]

/-- [definition] **The type's defining relation** on `Q`, by its powers and shifted products:
O `Q = 0`; N `Q ≠ 0`, `Q² = 0`; III `Q² ≠ 0`, `Q³ = 0`; D `(Q − λ)(Q + 2λ) = 0` for some
`λ ≠ 0`; II `(Q − λ)²(Q + 2λ) = 0 ≠ (Q − λ)(Q + 2λ)` for some `λ ≠ 0`; I `I³ ≠ 6J²`. -/
def HasType (Q : Mat3 K) : PetrovType → Prop
  | .I => invI Q ^ 3 ≠ 6 * invJ Q ^ 2
  | .II => ∃ l : K, l ≠ 0 ∧ (Q - l • 1) ^ 2 * (Q + (2 * l) • 1) = 0 ∧
      (Q - l • 1) * (Q + (2 * l) • 1) ≠ 0
  | .D => ∃ l : K, l ≠ 0 ∧ (Q - l • 1) * (Q + (2 * l) • 1) = 0
  | .III => Q ^ 2 ≠ 0 ∧ Q ^ 3 = 0
  | .N => Q ≠ 0 ∧ Q ^ 2 = 0
  | .O => Q = 0

/-- [definition] **The repeated eigenvalue** `λ = −J/I` of an algebraically special `Q`. -/
def repeatedRoot (Q : Mat3 K) : K := -(invJ Q / invI Q)

open Classical in
/-- [definition] **The classifier**: `I` where `I³ ≠ 6J²`; else, where `J = 0`, `O`, `N` or `III` by
the first vanishing power; else `D` or `II` by whether `(Q − λ)(Q + 2λ)` vanishes at `λ = −J/I`. -/
def classify (Q : Mat3 K) : PetrovType :=
  if invI Q ^ 3 ≠ 6 * invJ Q ^ 2 then .I
  else if invJ Q = 0 then (if Q = 0 then .O else if Q ^ 2 = 0 then .N else .III)
  else if (Q - repeatedRoot Q • 1) * (Q + (2 * repeatedRoot Q) • 1) = 0 then .D else .II

/-- [proved-standard; formal-checked] `(Q − λ)(Q + 2λ) = Q² + λQ − 2λ²`. -/
theorem shifted_mul (Q : Mat3 K) (l : K) :
    (Q - l • 1) * (Q + (2 * l) • 1) = Q ^ 2 + l • Q - (2 * l ^ 2) • 1 := by
  simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sq]
  module

/-- [proved-standard; formal-checked] `(Q − λ)²(Q + 2λ) = Q³ − 3λ²Q + 2λ³`. -/
theorem shifted_sq_mul (Q : Mat3 K) (l : K) :
    (Q - l • 1) ^ 2 * (Q + (2 * l) • 1) = Q ^ 3 - (3 * l ^ 2) • Q + (2 * l ^ 3) • 1 := by
  simp only [sub_mul, mul_sub, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sq,
    pow_three, mul_assoc]
  module

variable {Q : Mat3 K}

/-- [proved-standard; formal-checked] **Type D's invariants**: `(Q − λ)(Q + 2λ) = 0` gives
`I = 6λ²` and `J = −6λ³`. -/
theorem invariants_of_shifted (hQ : Q.trace = 0) {l : K} (h : (Q - l • 1) * (Q + (2 * l) • 1) = 0) :
    invI Q = 6 * l ^ 2 ∧ invJ Q = -6 * l ^ 3 := by
  rw [shifted_mul] at h
  have h1 := congrArg Matrix.trace h
  rw [trace_sub, trace_add, trace_smul, trace_smul_one, hQ, trace_zero, smul_zero] at h1
  have h2 := congrArg (fun M => (Q * M).trace) h
  simp only [mul_sub, mul_add, mul_smul_comm, mul_one, mul_zero, trace_sub, trace_add, trace_smul,
    hQ, trace_zero, smul_eq_mul] at h2
  rw [← sq, ← pow_succ'] at h2
  have hI : invI Q = 6 * l ^ 2 := by rw [invI]; linear_combination h1
  refine ⟨hI, ?_⟩
  rw [invJ]
  have : invI Q = (Q ^ 2).trace := rfl
  linear_combination h2 + l * this - l * hI

variable [CharZero K]

/-- [proved-standard; formal-checked] **Type II's invariants**: `(Q − λ)²(Q + 2λ) = 0` with `λ ≠ 0`
gives `I = 6λ²` and `J = −6λ³`. -/
theorem invariants_of_shifted_sq (hQ : Q.trace = 0) {l : K} (hl : l ≠ 0)
    (h : (Q - l • 1) ^ 2 * (Q + (2 * l) • 1) = 0) : invI Q = 6 * l ^ 2 ∧ invJ Q = -6 * l ^ 3 := by
  rw [shifted_sq_mul] at h
  have h1 := congrArg Matrix.trace h
  rw [trace_add, trace_sub, trace_smul, trace_smul_one, hQ, trace_zero, smul_zero] at h1
  have hJ : invJ Q = -6 * l ^ 3 := by rw [invJ]; linear_combination h1
  rw [cayley_hamilton hQ, hJ] at h
  have hc : (invI Q / 2 - 3 * l ^ 2) • Q = 0 := by rw [← h]; module
  refine ⟨?_, hJ⟩
  rcases smul_eq_zero.mp hc with hc | hc
  · linear_combination 2 * hc
  · exfalso
    rw [invJ, hc, zero_pow three_ne_zero, trace_zero] at hJ
    exact hl (pow_eq_zero_iff three_ne_zero |>.mp (by linear_combination hJ / 6))

/-- [proved-standard; formal-checked] **Type D's `Q` is not zero**: `(0 − λ)(0 + 2λ) = −2λ²`. -/
theorem ne_zero_of_hasType_D (h : HasType Q .D) : Q ≠ 0 := by
  obtain ⟨l, hl, hP⟩ := h
  rintro rfl
  obtain ⟨hI, -⟩ := invariants_of_shifted (by simp) hP
  have h6 : (6 : K) * l ^ 2 = 0 := by rw [← hI]; simp [invI]
  exact hl (pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h6).resolve_left (by norm_num)))

/-- [proved-standard; formal-checked] **Type I is three distinct eigenvalues**: a traceless `Q` is of
type I iff its characteristic polynomial and its derivative share no root. -/
theorem hasType_I_iff (hQ : Q.trace = 0) :
    HasType Q .I ↔ ¬∃ r : K, Q.charpoly.IsRoot r ∧ (derivative Q.charpoly).IsRoot r := by
  rw [charpoly_repeated_root_iff hQ]
  exact Iff.rfl

/-- [proved-standard; formal-checked] **Nilpotent iff `I = J = 0`**: for a traceless `Q`,
`Q³ = 0` iff both invariants vanish. -/
theorem pow_three_eq_zero_iff (hQ : Q.trace = 0) : Q ^ 3 = 0 ↔ invI Q = 0 ∧ invJ Q = 0 := by
  constructor
  · intro h
    have hJ : invJ Q = 0 := by rw [invJ, h, trace_zero]
    refine ⟨?_, hJ⟩
    have hc : (invI Q / 2) • Q = 0 := by
      have := cayley_hamilton hQ
      rw [h, hJ, zero_div, zero_smul, add_zero] at this
      exact this.symm
    rcases smul_eq_zero.mp hc with hc | hc
    · linear_combination 2 * hc
    · rw [invI, hc, zero_pow two_ne_zero, trace_zero]
  · rintro ⟨hI, hJ⟩
    rw [cayley_hamilton hQ, hI, hJ]
    simp

/-- [proved-standard; formal-checked] **A repeated eigenvalue `λ ≠ 0` is `(λ, λ, −2λ)`**: where
`I = 6λ²` and `J = −6λ³`, `charpoly Q = (X − λ)²(X + 2λ)`. -/
theorem charpoly_of_invariants (hQ : Q.trace = 0) {l : K} (hI : invI Q = 6 * l ^ 2)
    (hJ : invJ Q = -6 * l ^ 3) : Q.charpoly = (X - C l) ^ 2 * (X + C (2 * l)) := by
  rw [charpoly_eq hQ, hI, hJ]
  have e1 : 6 * l ^ 2 / 2 = 3 * l ^ 2 := by ring
  have e2 : -6 * l ^ 3 / 3 = -(2 * l ^ 3) := by ring
  rw [e1, e2]
  simp only [map_mul, map_pow, map_neg, map_ofNat]
  ring

/-- [proved-standard; formal-checked] **The null and flat types' polynomial**: where `I = J = 0`,
`charpoly Q = X³`. -/
theorem charpoly_of_nilpotent (hQ : Q.trace = 0) (h : Q ^ 3 = 0) : Q.charpoly = X ^ 3 := by
  obtain ⟨hI, hJ⟩ := (pow_three_eq_zero_iff hQ).mp h
  rw [charpoly_eq hQ, hI, hJ]
  simp

/-- [proved-standard; formal-checked] **Types D and II have eigenvalues `(λ, λ, −2λ)`**, `λ ≠ 0`. -/
theorem charpoly_of_hasType_D_or_II (hQ : Q.trace = 0) (h : HasType Q .D ∨ HasType Q .II) :
    ∃ l : K, l ≠ 0 ∧ Q.charpoly = (X - C l) ^ 2 * (X + C (2 * l)) := by
  rcases h with ⟨l, hl, hP⟩ | ⟨l, hl, hII, -⟩
  · obtain ⟨hI, hJ⟩ := invariants_of_shifted hQ hP
    exact ⟨l, hl, charpoly_of_invariants hQ hI hJ⟩
  · obtain ⟨hI, hJ⟩ := invariants_of_shifted_sq hQ hl hII
    exact ⟨l, hl, charpoly_of_invariants hQ hI hJ⟩

/-- [proved-standard; formal-checked] **The classifier meets its type**: a traceless `Q` has the type
`classify Q`. -/
theorem hasType_classify (hQ : Q.trace = 0) : HasType Q (classify Q) := by
  unfold classify
  by_cases hs : invI Q ^ 3 ≠ 6 * invJ Q ^ 2
  · rw [if_pos hs]; exact hs
  rw [if_neg hs]
  rw [ne_eq, not_not] at hs
  by_cases hJ : invJ Q = 0
  · rw [if_pos hJ]
    have hI : invI Q = 0 := by
      rw [hJ] at hs
      exact pow_eq_zero_iff three_ne_zero |>.mp (by linear_combination hs)
    have h3 : Q ^ 3 = 0 := (pow_three_eq_zero_iff hQ).mpr ⟨hI, hJ⟩
    by_cases h0 : Q = 0
    · rw [if_pos h0]; exact h0
    rw [if_neg h0]
    by_cases h2 : Q ^ 2 = 0
    · rw [if_pos h2]; exact ⟨h0, h2⟩
    · rw [if_neg h2]; exact ⟨h2, h3⟩
  rw [if_neg hJ]
  have hI0 : invI Q ≠ 0 := by
    intro h
    rw [h] at hs
    exact hJ (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -hs / 6))
  have hl : repeatedRoot Q ≠ 0 := neg_ne_zero.mpr (div_ne_zero hJ hI0)
  have hIl : invI Q = 6 * repeatedRoot Q ^ 2 := by
    rw [repeatedRoot]
    field_simp
    linear_combination hs
  have hJl : invJ Q = -6 * repeatedRoot Q ^ 3 := by
    rw [repeatedRoot]
    field_simp
    linear_combination hs
  have hII : (Q - repeatedRoot Q • 1) ^ 2 * (Q + (2 * repeatedRoot Q) • 1) = 0 := by
    rw [shifted_sq_mul, cayley_hamilton hQ, hIl, hJl]
    module
  by_cases hP : (Q - repeatedRoot Q • 1) * (Q + (2 * repeatedRoot Q) • 1) = 0
  · rw [if_pos hP]; exact ⟨_, hl, hP⟩
  · rw [if_neg hP]; exact ⟨_, hl, hII, hP⟩

/-- [proved-standard; formal-checked] A root `λ ≠ 0` with `I = 6λ²` and `J = −6λ³` is
algebraically special, has `J ≠ 0`, and is the classifier's `λ = −J/I`. -/
theorem special_of_invariants {l : K} (hl : l ≠ 0) (hI : invI Q = 6 * l ^ 2)
    (hJ : invJ Q = -6 * l ^ 3) :
    invI Q ^ 3 = 6 * invJ Q ^ 2 ∧ invJ Q ≠ 0 ∧ repeatedRoot Q = l := by
  refine ⟨by rw [hI, hJ]; ring, by rw [hJ]; simp [hl], ?_⟩
  rw [repeatedRoot, hI, hJ]
  field_simp

/-- [proved-standard; formal-checked] **The type is unique**: a traceless `Q` of type `t` has
`classify Q = t`. -/
theorem classify_eq_of_hasType (hQ : Q.trace = 0) {t : PetrovType} (h : HasType Q t) :
    classify Q = t := by
  unfold classify
  cases t with
  | I => rw [if_pos (show invI Q ^ 3 ≠ 6 * invJ Q ^ 2 from h)]
  | O =>
    have h0 : Q = 0 := h
    subst h0
    simp [invI, invJ]
  | N =>
    obtain ⟨h0, h2⟩ := h
    have h3 : Q ^ 3 = 0 := by rw [pow_succ, h2, zero_mul]
    obtain ⟨hI, hJ⟩ := (pow_three_eq_zero_iff hQ).mp h3
    rw [if_neg (by rw [hI, hJ]; simp), if_pos hJ, if_neg h0, if_pos h2]
  | III =>
    obtain ⟨h2, h3⟩ := h
    obtain ⟨hI, hJ⟩ := (pow_three_eq_zero_iff hQ).mp h3
    have h0 : Q ≠ 0 := by rintro rfl; exact h2 (by simp)
    rw [if_neg (by rw [hI, hJ]; simp), if_pos hJ, if_neg h0, if_neg h2]
  | D =>
    obtain ⟨l, hl, hP⟩ := h
    obtain ⟨hI, hJ⟩ := invariants_of_shifted hQ hP
    obtain ⟨hs, hJ0, hr⟩ := special_of_invariants hl hI hJ
    rw [if_neg (not_not.mpr hs), if_neg hJ0, hr, if_pos hP]
  | II =>
    obtain ⟨l, hl, hII, hP⟩ := h
    obtain ⟨hI, hJ⟩ := invariants_of_shifted_sq hQ hl hII
    obtain ⟨hs, hJ0, hr⟩ := special_of_invariants hl hI hJ
    rw [if_neg (not_not.mpr hs), if_neg hJ0, hr, if_neg hP]

/-- [proved-standard; formal-checked] **Petrov's classification**: every traceless `3 × 3` `Q` has
exactly one of the six types. -/
theorem existsUnique_hasType (hQ : Q.trace = 0) : ∃! t : PetrovType, HasType Q t :=
  ⟨classify Q, hasType_classify hQ, fun _ ht => (classify_eq_of_hasType hQ ht).symm⟩

/-- [proved-standard; formal-checked] **The types exclude each other**: two types of one traceless
`Q` are one. -/
theorem hasType_unique (hQ : Q.trace = 0) {s t : PetrovType} (hs : HasType Q s)
    (ht : HasType Q t) : s = t :=
  (classify_eq_of_hasType hQ hs).symm.trans (classify_eq_of_hasType hQ ht)

/-- [proved-standard; formal-checked] **Algebraically special** (`I³ = 6J²`, a repeated eigenvalue)
iff the type is not I. -/
theorem special_iff (hQ : Q.trace = 0) : invI Q ^ 3 = 6 * invJ Q ^ 2 ↔ classify Q ≠ .I := by
  constructor
  · intro hs hI
    have := hasType_classify hQ
    rw [hI] at this
    exact this hs
  · intro hc
    by_contra hs
    exact hc (classify_eq_of_hasType hQ (t := .I) hs)

/-- [proved-standard; formal-checked] **The nilpotent types**: for a traceless `Q`, `Q³ = 0` iff its
type is III, N or O. -/
theorem pow_three_eq_zero_iff_classify (hQ : Q.trace = 0) :
    Q ^ 3 = 0 ↔ classify Q = .III ∨ classify Q = .N ∨ classify Q = .O := by
  constructor
  · intro h3
    by_cases h0 : Q = 0
    · exact Or.inr (Or.inr (classify_eq_of_hasType hQ (t := .O) h0))
    by_cases h2 : Q ^ 2 = 0
    · exact Or.inr (Or.inl (classify_eq_of_hasType hQ (t := .N) ⟨h0, h2⟩))
    · exact Or.inl (classify_eq_of_hasType hQ (t := .III) ⟨h2, h3⟩)
  · intro h
    have hT := hasType_classify hQ
    rcases h with h | h | h <;> rw [h] at hT
    · exact hT.2
    · rw [pow_succ, hT.2, zero_mul]
    · have h0 : Q = 0 := hT
      rw [h0, zero_pow three_ne_zero]

end Types

/-! ## 5. The type does not depend on the field it is read in -/

section FieldMap

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (Q : Mat3 K)

/-- [proved-standard; formal-checked] `I` is carried by a field map. -/
theorem invI_map : invI (Q.map f) = f (invI Q) := by
  rw [invI, invI, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply,
    AddMonoidHom.map_trace]

/-- [proved-standard; formal-checked] `J` is carried by a field map. -/
theorem invJ_map : invJ (Q.map f) = f (invJ Q) := by
  rw [invJ, invJ, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply,
    AddMonoidHom.map_trace]

/-- [proved-standard; formal-checked] A shifted product is carried by a field map. -/
theorem shifted_map (l : K) :
    (Q.map f - f l • 1) * (Q.map f + (2 * f l) • 1) = ((Q - l • 1) * (Q + (2 * l) • 1)).map f := by
  have hs : ∀ c : K, (c • (1 : Mat3 K)).map f = f c • 1 := by
    intro c
    ext i j
    by_cases hij : i = j <;> simp [one_apply, hij]
  rw [← RingHom.mapMatrix_apply f ((Q - l • 1) * (Q + (2 * l) • 1)), map_mul, map_sub, map_add]
  simp only [RingHom.mapMatrix_apply, hs, map_mul, map_ofNat]

/-- [proved-standard; formal-checked] A matrix vanishes iff its image under a field map does. -/
theorem matrix_map_eq_zero_iff (A : Mat3 K) : A.map f = 0 ↔ A = 0 := by
  rw [← Matrix.map_zero f (map_zero f)]
  exact (Matrix.map_injective f.injective).eq_iff

variable [CharZero K] [CharZero L]

/-- [proved-standard; formal-checked] **The type is the field's to keep**: under any field map
`f : K → L`, `classify (f Q) = classify Q`. -/
theorem classify_map : classify (Q.map f) = classify Q := by
  have hs : (invI (Q.map f) ^ 3 ≠ 6 * invJ (Q.map f) ^ 2) ↔ (invI Q ^ 3 ≠ 6 * invJ Q ^ 2) := by
    rw [invI_map, invJ_map, ← map_pow, ← map_pow, ← map_ofNat f 6, ← map_mul, ne_eq, ne_eq,
      f.injective.eq_iff]
  have hJ : invJ (Q.map f) = 0 ↔ invJ Q = 0 := by rw [invJ_map, map_eq_zero_iff f f.injective]
  have h0 : Q.map f = 0 ↔ Q = 0 := matrix_map_eq_zero_iff f Q
  have h2 : (Q.map f) ^ 2 = 0 ↔ Q ^ 2 = 0 := by
    rw [← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, matrix_map_eq_zero_iff]
  have hr : repeatedRoot (Q.map f) = f (repeatedRoot Q) := by
    rw [repeatedRoot, repeatedRoot, invI_map, invJ_map, map_neg, map_div₀]
  have hP : (Q.map f - repeatedRoot (Q.map f) • 1) * (Q.map f + (2 * repeatedRoot (Q.map f)) • 1) = 0 ↔
      (Q - repeatedRoot Q • 1) * (Q + (2 * repeatedRoot Q) • 1) = 0 := by
    rw [hr, shifted_map, matrix_map_eq_zero_iff]
  classical
  unfold classify
  simp only [hs, hJ, h0, h2, hP]

end FieldMap

/-! ## 6. Strain and rotation cancel in the null types -/

section Null

open Complex

/-- [proved-standard; formal-checked] `(E + iH)ᵀ = Eᵀ + iHᵀ`. -/
theorem complexQ_transpose (E H : Mat3 ℝ) : (complexQ E H)ᵀ = complexQ Eᵀ Hᵀ := by
  ext i j
  simp [complexQ]

/-- [proved-standard; formal-checked] `tr(E + iH) = tr E + i·tr H`. -/
theorem complexQ_trace (E H : Mat3 ℝ) : (complexQ E H).trace = E.trace + H.trace * I := by
  simp only [complexQ, trace_fin_three, of_apply]
  push_cast
  ring

/-- [proved-standard; formal-checked] `E + iH = 0` iff `E = 0` and `H = 0`. -/
theorem complexQ_eq_zero_iff (E H : Mat3 ℝ) : complexQ E H = 0 ↔ E = 0 ∧ H = 0 := by
  constructor
  · intro h
    have hij : ∀ i j, E i j = 0 ∧ H i j = 0 := fun i j => by
      have := congrFun (congrFun h i) j
      simpa [complexQ, Complex.ext_iff] using this
    exact ⟨Matrix.ext fun i j => (hij i j).1, Matrix.ext fun i j => (hij i j).2⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    simp [complexQ]

/-- [proved-standard; formal-checked] **The square of `E + iH`** is `(E² − H²) + i(EH + HE)`. -/
theorem complexQ_sq (E H : Mat3 ℝ) : complexQ E H ^ 2 = complexQ (E * E - H * H) (E * H + H * E) := by
  ext i j
  simp only [complexQ, sq, mul_apply, of_apply, Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_three]
  push_cast
  linear_combination ((H i 0 : ℂ) * H 0 j + (H i 1 : ℂ) * H 1 j + (H i 2 : ℂ) * H 2 j) * I_sq

/-- [proved-standard; formal-checked] **Strain and rotation cancel**: `(E + iH)² = 0` iff
`E² − H² = 0` and `EH + HE = 0`. -/
theorem complexQ_sq_eq_zero_iff (E H : Mat3 ℝ) :
    complexQ E H ^ 2 = 0 ↔ E * E - H * H = 0 ∧ E * H + H * E = 0 := by
  rw [complexQ_sq, complexQ_eq_zero_iff]

/-- [proved-standard; formal-checked] **Type N on the pair**: `E + iH` is of type N iff it is nonzero,
`E² = H²` and `EH = −HE`. -/
theorem hasType_N_iff (E H : Mat3 ℝ) :
    HasType (complexQ E H) .N ↔ (E ≠ 0 ∨ H ≠ 0) ∧ E * E - H * H = 0 ∧ E * H + H * E = 0 := by
  show complexQ E H ≠ 0 ∧ complexQ E H ^ 2 = 0 ↔ _
  rw [complexQ_sq_eq_zero_iff, ne_eq, complexQ_eq_zero_iff, not_and_or]

/-- [proved-standard; formal-checked] **The observer's null condition**: `Q² = 0` for the Weyl
tensor's `Q` iff `E² − H² = 0` and `EH + HE = 0`. -/
theorem weylQ_sq_eq_zero_iff (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    weylQ C ^ 2 = 0 ↔ Matrix.of (electric C) * Matrix.of (electric C) - Matrix.of (magnetic C) *
      Matrix.of (magnetic C) = 0 ∧ Matrix.of (electric C) * Matrix.of (magnetic C) +
      Matrix.of (magnetic C) * Matrix.of (electric C) = 0 :=
  complexQ_sq_eq_zero_iff _ _

end Null

/-! ## 7. No purely electric `Q` is of type N, III or II -/

section Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-standard; formal-checked] **A real symmetric `E` with `E² = 0` is `0`** (`tr(EᵀE)` is a sum
of squares). -/
theorem eq_zero_of_symm_sq {E : Matrix n n ℝ} (hE : Eᵀ = E) (h : E ^ 2 = 0) : E = 0 := by
  have hs : ∀ a b, E b a = E a b := fun a b => by rw [← transpose_apply E a b, hE]
  ext i k
  have hii : ∑ j, E i j ^ 2 = 0 := by
    have := congrFun (congrFun h i) i
    rw [sq, mul_apply, Matrix.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [sq, hs j i]
  have hk := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (E i j)).mp hii k
    (Finset.mem_univ k)
  simpa using hk

/-- [proved-standard; formal-checked] A real symmetric `E` with `E³ = 0` is `0`. -/
theorem eq_zero_of_symm_pow_three {E : Matrix n n ℝ} (hE : Eᵀ = E) (h : E ^ 3 = 0) : E = 0 := by
  have h2s : (E ^ 2)ᵀ = E ^ 2 := by rw [transpose_pow, hE]
  have h4 : (E ^ 2) ^ 2 = 0 := by rw [← pow_mul, show 2 * 2 = 1 + 3 from rfl, pow_add, h, mul_zero]
  exact eq_zero_of_symm_sq hE (eq_zero_of_symm_sq h2s h4)

/-- [proved-standard; formal-checked] **No real symmetric `E` is of type II**: `(E − λ)(E + 2λ)` is
symmetric and squares to `(E − λ)²(E + 2λ)·(E + 2λ)`. -/
theorem not_hasType_II_of_symm {E : Mat3 ℝ} (hE : Eᵀ = E) : ¬HasType E .II := by
  rintro ⟨l, -, hII, hP⟩
  apply hP
  have hPs : ((E - l • 1) * (E + (2 * l) • 1))ᵀ = (E - l • 1) * (E + (2 * l) • 1) := by
    rw [transpose_mul, transpose_sub, transpose_add, transpose_smul, transpose_smul, transpose_one,
      hE]
    simp only [sub_mul, mul_add, mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hP2 : ((E - l • 1) * (E + (2 * l) • 1)) ^ 2 = 0 := by
    have e : ((E - l • 1) * (E + (2 * l) • 1)) ^ 2 =
        (E - l • 1) ^ 2 * (E + (2 * l) • 1) * (E + (2 * l) • 1) := by
      simp only [sq, sub_mul, mul_add, mul_sub, add_mul, smul_mul_assoc, mul_smul_comm, one_mul,
        mul_one, mul_assoc]
      module
    rw [e, hII, zero_mul]
  exact eq_zero_of_symm_sq hPs hP2

/-- [proved-standard; formal-checked] **A real symmetric traceless `E` is of type I, D or O.** -/
theorem classify_of_symm {E : Mat3 ℝ} (hE : Eᵀ = E) (hT : E.trace = 0) :
    classify E = .I ∨ classify E = .D ∨ classify E = .O := by
  have hc := hasType_classify hT
  generalize classify E = t at hc
  cases t with
  | I => exact Or.inl rfl
  | D => exact Or.inr (Or.inl rfl)
  | O => exact Or.inr (Or.inr rfl)
  | II => exact absurd hc (not_hasType_II_of_symm hE)
  | III =>
    exfalso
    apply hc.1
    rw [eq_zero_of_symm_pow_three hE hc.2]
    simp
  | N => exact absurd (eq_zero_of_symm_sq hE hc.2) hc.1

variable {C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}

/-- [proved-standard; formal-checked] **The purely electric Weyl tensor** (`H = 0`) is of type I, D
or O. -/
theorem classify_weylQ_of_magnetic_eq_zero (h : WeylSymmetries C) (hH : ∀ i j, magnetic C i j = 0) :
    classify (weylQ C) = .I ∨ classify (weylQ C) = .D ∨ classify (weylQ C) = .O := by
  have he : weylQ C = (Matrix.of (electric C)).map Complex.ofRealHom := by
    ext i j
    simp [weylQ, complexQ, hH]
  rw [he, classify_map]
  exact classify_of_symm (electric_transpose h) (electric_trace h)

/-- [proved-standard; formal-checked] **No purely electric Weyl tensor is null**: with `H = 0`, `Q`
is of none of the types N, III and II. -/
theorem weylQ_not_null_of_magnetic_eq_zero (h : WeylSymmetries C) (hH : ∀ i j, magnetic C i j = 0)
    {t : PetrovType} (ht : HasType (weylQ C) t) : t ≠ .N ∧ t ≠ .III ∧ t ≠ .II := by
  rw [← classify_eq_of_hasType (weylQ_trace h) ht]
  rcases classify_weylQ_of_magnetic_eq_zero h hH with hc | hc | hc <;> rw [hc] <;> decide

end Real

/-! ## 8. The witnesses -/

section Witnesses

open Complex

/-- [definition] **The Schwarzschild tide** `E = μ·diag(−2, 1, 1)`: stretched along the radius,
squeezed across it. -/
def schwarzschildTide (μ : ℝ) : Mat3 ℝ := μ • diagonal ![-2, 1, 1]

/-- [proved-standard; formal-checked] The Schwarzschild tide is symmetric and traceless. -/
theorem schwarzschildTide_admissible (μ : ℝ) :
    (schwarzschildTide μ)ᵀ = schwarzschildTide μ ∧ (schwarzschildTide μ).trace = 0 := by
  refine ⟨by simp [schwarzschildTide], ?_⟩
  rw [schwarzschildTide, trace_smul, trace_diagonal, Fin.sum_univ_three]
  simp
  norm_num

/-- [proved-standard; formal-checked] **Type D**: the Schwarzschild tide with `H = 0` and `μ ≠ 0`
gives a symmetric `Q` of type D. -/
theorem classify_schwarzschild {μ : ℝ} (hμ : μ ≠ 0) :
    (complexQ (schwarzschildTide μ) 0)ᵀ = complexQ (schwarzschildTide μ) 0 ∧
      classify (complexQ (schwarzschildTide μ) 0) = .D := by
  refine ⟨by rw [complexQ_transpose, (schwarzschildTide_admissible μ).1, transpose_zero], ?_⟩
  apply classify_eq_of_hasType
  · rw [complexQ_trace, (schwarzschildTide_admissible μ).2, trace_zero]
    simp
  · refine ⟨(μ : ℂ), by exact_mod_cast hμ, ?_⟩
    have hd : complexQ (schwarzschildTide μ) 0 = diagonal ![-2 * (μ : ℂ), μ, μ] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [complexQ, schwarzschildTide, mul_comm]
    rw [hd, smul_one_eq_diagonal, smul_one_eq_diagonal, diagonal_sub, diagonal_add,
      diagonal_mul_diagonal, diagonal_eq_zero]
    funext i
    fin_cases i <;> simp

/-- [definition] A plane wave's tide `diag(0, 1, −1)`. -/
def planeWaveTide : Mat3 ℝ := !![0, 0, 0; 0, 1, 0; 0, 0, -1]

/-- [definition] A plane wave's frame dragging: the tide turned by an eighth of a turn about the first
axis (the cross polarization). -/
def planeWaveDrag : Mat3 ℝ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]

/-- [proved-standard; formal-checked] The plane wave's `Q` is `[[0, 0, 0], [0, 1, i], [0, i, −1]]`. -/
theorem planeWave_eq : complexQ planeWaveTide planeWaveDrag = !![0, 0, 0; 0, 1, I; 0, I, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexQ, planeWaveTide, planeWaveDrag]

/-- [proved-standard; formal-checked] **Type N**: the plane wave's symmetric `Q`, whose strain and
rotation have equal squares and anticommute. -/
theorem classify_planeWave :
    (complexQ planeWaveTide planeWaveDrag)ᵀ = complexQ planeWaveTide planeWaveDrag ∧
      classify (complexQ planeWaveTide planeWaveDrag) = .N := by
  refine ⟨?_, ?_⟩
  · rw [planeWave_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply classify_eq_of_hasType
  · rw [planeWave_eq, trace_fin_three]
    simp
  · rw [hasType_N_iff]
    refine ⟨Or.inl fun h => ?_, ?_, ?_⟩
    · have := congrFun (congrFun h 1) 1
      simp [planeWaveTide] at this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [planeWaveTide, planeWaveDrag]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [planeWaveTide, planeWaveDrag]

/-- [definition] A type III `Q = [[0, 1, i], [1, 0, 0], [i, 0, 0]]`. -/
def typeIIIQ : Mat3 ℂ := !![0, 1, I; 1, 0, 0; I, 0, 0]

/-- [proved-standard; formal-checked] **Type III**: `Q² ≠ 0` and `Q³ = 0`. -/
theorem classify_typeIIIQ : typeIIIQᵀ = typeIIIQ ∧ classify typeIIIQ = .III := by
  refine ⟨?_, classify_eq_of_hasType ?_ ⟨fun h => ?_, ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [typeIIIQ]
  · simp [typeIIIQ, trace_fin_three]
  · have := congrFun (congrFun h 1) 1
    simp [typeIIIQ, sq, mul_apply, Fin.sum_univ_three] at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [typeIIIQ, pow_three, mul_apply, Fin.sum_univ_three]

/-- [definition] A type II `Q = λ·diag(1, 1, −2) + [[1, i, 0], [i, −1, 0], [0, 0, 0]]`. -/
def typeIIQ (l : ℂ) : Mat3 ℂ := l • diagonal ![1, 1, -2] + !![1, I, 0; I, -1, 0; 0, 0, 0]

/-- [proved-standard; formal-checked] **Type II** for `λ ≠ 0`: `(Q − λ)²(Q + 2λ) = 0` and
`(Q − λ)(Q + 2λ)` has `3λ` at its corner. -/
theorem classify_typeIIQ {l : ℂ} (hl : l ≠ 0) : (typeIIQ l)ᵀ = typeIIQ l ∧ classify (typeIIQ l) = .II := by
  refine ⟨?_, classify_eq_of_hasType ?_ ⟨l, hl, ?_, fun h => ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [typeIIQ]
  · rw [trace_fin_three]
    simp [typeIIQ]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [typeIIQ, sq, mul_apply, Fin.sum_univ_three, one_apply]
    right
    ring
  · have := congrFun (congrFun h 0) 0
    simp [typeIIQ, mul_apply, Fin.sum_univ_three, one_apply] at this
    ring_nf at this
    simp [hl] at this

/-- [definition] A type I `Q = diag(1, −1, 0)`. -/
def typeIQ : Mat3 ℂ := diagonal ![1, -1, 0]

/-- [proved-standard; formal-checked] **Type I**: `I = 2`, `J = 0`, so `I³ ≠ 6J²`. -/
theorem classify_typeIQ : typeIQᵀ = typeIQ ∧ classify typeIQ = .I := by
  refine ⟨by simp [typeIQ], classify_eq_of_hasType ?_ ?_⟩
  · rw [trace_fin_three]
    simp [typeIQ]
  · show invI typeIQ ^ 3 ≠ 6 * invJ typeIQ ^ 2
    simp [typeIQ, invI, invJ, pow_three, sq, Fin.sum_univ_three]

end Witnesses

end Holonics.Physics.Spacetime.PetrovTypes
