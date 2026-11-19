import Holonics.Transport.NavigatorTraceFaces
import Holonics.Aeon.Production.Zeta
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.ZMod.Basic

/-!
# Trace faces of arbitrary material: singular carriers, Newton's identities and sites of any size

`Transport/NavigatorTraceFaces` proves that carrying material to another phase conserves its
determinant, its trace sequence `tr(Mᵏ)` and its transfer determinant `det(1 − T·M)`, with the
material itself a unit of the matrix ring (its `phaseTransport` lives in a group), and reads a
machine of independent sites only for two-by-two sites. This file lifts each restriction: the
material may be singular or a reset, the carrier need not be invertible at all, the charpoly
coefficients are read from the trace sequence by Newton's identities over every commutative ring,
and the sites of a machine may have any sizes.

Sources: #410's box "Trace faces of arbitrary material: frame conjugation beyond unit-valued
material (singular and reset included), Newton identities at their coefficient domain, block
products for independent sites (`Transport/NavigatorTraceFaces`)", and the box merged into it, "The
certified wake, and the turn traces' Newton identities"; the owner's open paragraph ("Scope:
matrices over a commutative ring and invertible carriers. Coupled sites … are outside this
module"); the record `research/records/2026-09-21_WINDING_CARRY_FACES_AND_PLACEMENT_GENERALIZE_THE_HELICAL_PAIR.md`
and the winding guide §3; atlas rows `trace.phase-carriage-conserves-faces`, `navigator.trace-faces`,
`trace.det-one-minus-tm`, `trace.local-factor-companion`, `trace.faces-not-certificate` and
`aeon.zeta-log-derivative`. The last row already holds Newton's identities as one identity of power
series over every commutative ring (`Aeon/Production/Zeta.transferDet_derivative`); this file reads
it coefficient by coefficient and states where the coefficients are recovered from the traces.

[proved-standard; formal-checked] [proved-derived; formal-checked] What is proved. Items 1, 4, 5 and
6 are classical results restated on the objects; items 2 and 3, and the recoveries of the owner's
theorems, are the house's readings of them.

1. **The reversed carrier** (Sylvester). For any `A : Matrix m n R`, `B : Matrix n m R` over a
   commutative ring, rectangular and singular allowed: `det(1 − T·AB) = det(1 − T·BA)` at every
   scalar `T` (`transfer_determinant_mul_comm`) and as polynomials (`charpolyRev_mul_comm`);
   `(AB)ᵏ⁺¹ = A(BA)ᵏB` (`pow_succ_mul_comm`), so `tr((AB)ᵏ) = tr((BA)ᵏ)` for every `k ≥ 1`
   (`trace_pow_mul_comm`); `Xⁿ·χ_(AB) = Xᵐ·χ_(BA)` with `m`, `n` the two sizes
   (`charpoly_mul_comm_rect`), and for square `A`, `B`: `χ_(AB) = χ_(BA)` and `det(AB) = det(BA)`
   (`charpoly_mul_comm_square`, `det_mul_comm_square`). The transfer determinant carries no change
   of size; the size enters only the charpoly's power of `X`, the zeroth trace and `det`.
2. **A unit frame carries material of any kind.** For a unit phase shift `S` and any material `P`,
   singular or a reset included, the carried material `carry S P d = S⁻ᵈ P Sᵈ` (`carry`) has powers
   the carried powers (`carry_pow`) and conserves `det`, every `tr(Pᵏ)`, `det(1 − T·P)`, the
   transfer polynomial and the charpoly (`carry_conserves_determinant`,
   `carry_conserves_trace_sequence`, `carry_conserves_transfer_determinant`,
   `carry_conserves_charpolyRev`, `carry_conserves_charpoly`). The transfer faces are read from
   item 1 with `X = S⁻ᵈ`, `Y = P Sᵈ`: unit conjugation is a case of the reversed carrier. On unit
   material `carry` is the owner's `phaseTransport` (`carry_units`), and the owner's three
   conservation theorems follow (`recovers_carried_determinant`,
   `recovers_carried_trace_sequence`, `recovers_carried_transfer_determinant`). An intertwining
   `U P = Q U` by a unit conserves the trace sequence (`unit_intertwiner_conserves_trace_sequence`).
3. **Reset carriers.** A reset is an idempotent carrier `E·E = E` (`IsReset`), the zero carrier the
   full reset (`isReset_zero`). With `X = E`, `Y = P`, item 1 gives `E P` the faces of `P E`; the
   material read through a reset, `E P E`, has the trace sequence from `k = 1`, the transfer
   determinant and the charpoly of `P E` (`reset_compression_trace_pow`,
   `reset_compression_transfer_determinant`, `reset_compression_charpoly`); through the zero reset
   it reads `det(1 − T·0) = 1` and traces zero (`zero_reset_faces`).
4. **Newton's identities at their coefficient domain.** Over every commutative ring, with
   `r_j` the coefficients of `det(1 − T·M)`: `(k + 1)·r_(k+1) = −Σ_(i+j=k) r_i·tr(Mʲ⁺¹)` for every
   `k` (`newton_transfer`), whose part past the size is the recurrence of the trace sequence
   (`trace_recurrence`); `r_j = c_(n−j)` for `j ≤ n` and `r_j = 0` past `n`, with `c` the charpoly
   coefficients (`coeff_charpolyRev`, `coeff_charpolyRev_eq_zero`); hence the division-free form
   `k·c_(n−k) = −Σ_(i=1..k) c_(n−k+i)·tr(Mⁱ)` for `k ≤ n` (`newton_charpoly`), with the two-by-two
   turn's instance `2·det M = (tr M)² − tr(M²)` (`two_site_newton`). The traces `tr(Mⁱ)`,
   `1 ≤ i ≤ n`, determine the transfer polynomial and the charpoly wherever `1, …, n` cancel
   (`charpolyRev_eq_of_trace_eq`, `charpoly_eq_of_trace_eq`): over a `ℚ`-algebra
   (`charpoly_eq_of_trace_eq_rat`) and over a domain of characteristic zero such as `ℤ`, where
   `2, …, n` are not units (`charpoly_eq_of_trace_eq_charZero`).
5. **Sites of any size.** For finitely many sites of one shape `o` (`Matrix.blockDiagonal`) and of
   varying shapes `ι s` (`Matrix.blockDiagonal'`), the machine's transfer determinant, transfer
   polynomial and charpoly are the products of the sites', and its trace sequence the sum
   (`transfer_determinant_blockDiagonal`, `charpoly_blockDiagonal`, `trace_pow_blockDiagonal`;
   `det_blockDiagonal'`, `transfer_determinant_blockDiagonal'`, `charpolyRev_blockDiagonal'`,
   `charpoly_blockDiagonal'`, `trace_pow_blockDiagonal'`). The owner's two-by-two theorems are the
   case `o = Fin 2` (`recovers_machine_transfer_determinant`, `recovers_machine_trace_sequence`).
6. **Two sites run together uncoupled.** `(A ⊗ B)ᵏ = Aᵏ ⊗ Bᵏ` and
   `tr((A ⊗ B)ᵏ) = tr(Aᵏ)·tr(Bᵏ)` (`kronecker_pow`, `trace_pow_kronecker`).

[counterexample; formal-checked] The witnesses.

- **`det` and the zeroth trace do not pass a carrier between sizes.** With the row `(1, 0)` and the
  column `(1, 0)ᵀ`, the product one way is the one-by-one identity and the other way the reset
  `diag(1, 0)` (`rowCarrier_mul_columnCarrier`, `columnCarrier_mul_rowCarrier`,
  `reversed_carrier_isReset`): the transfer determinants agree (`transfer_determinant_mul_comm`),
  but `det` reads `1` against `0` and the zeroth trace `1` against `2` (`rect_det_differs`,
  `rect_trace_zero_differs`).
- **A singular intertwiner need not conserve the trace.** `E·1 = E·E` for the reset
  `E = diag(1, 0)`, so `E` intertwines the identity with `E`, while `tr 1 = 2` and `tr E = 1`
  (`singular_intertwiner_breaks_trace`).
- **Where `p` does not cancel, the traces do not determine the charpoly.** Over `ZMod p` at size
  `p`, the zero and identity materials have the same trace sequence from `k = 1`
  (`zmod_trace_sequences_agree`) and the charpolys `Xᵖ` and `(X − 1)ᵖ`
  (`zmod_charpolys_differ`); `p` is no unit there (`zmod_prime_is_not_unit`).

What is not claimed. Trace faces stay invariants and not an action certificate
(`NavigatorTraceFaces.identityTwo_and_unipotentTwo_are_separated_by_source_receiver`): nothing here
recovers the material from its faces. No source in the tree defines "the certified wake", so that
part of the merged box is left as it stands; its Newton identities are item 4. Coupled sites, the
transfer determinant of a Kronecker composite, and a product over infinitely many sites are not
treated. The reversed carrier conserves the faces of the material it reads, `XY` against `YX`; it
does not conserve the faces of a material `P` that the carrier merely meets, as the intertwining
witness shows.

The computational object is the helical pair interaction: a site's material is a pair contact's
transfer over one tick, its class functions are the faces a receiver reads, a unit phase shift is
the helix's winding carrying the material to another phase, and a reset is a contact that drops a
direction. Of the winding guide's six general objects this touches the helix (phase carriage), the
faces and placement (trace faces, the transfer determinant and its Newton coefficients) and the tube
(a carrier `X : n → m` with its return `Y : m → n` is a transfer between two cross-section charts,
and `XY`, `YX` are the round trips read at either end); the pair enters through the two-by-two site
and the uncoupled composite of two sites; the cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open scoped BigOperators Matrix Kronecker
open Matrix Polynomial Finset

namespace Holonics.Transport.TraceFacesGeneral

open Holonics.Transport.HelicalPairInteraction

/-! ## 1. The reversed carrier -/

section Carrier

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- [proved-standard; formal-checked] **Sylvester:** `det(1 − T·AB) = det(1 − T·BA)`, any sizes. -/
theorem transfer_determinant_mul_comm (A : Matrix m n R) (B : Matrix n m R) (T : R) :
    ((1 : Matrix m m R) - T • (A * B)).det = ((1 : Matrix n n R) - T • (B * A)).det := by
  rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]

/-- [proved-standard; formal-checked] The transfer polynomials of `AB` and `BA` agree. -/
theorem charpolyRev_mul_comm (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).charpolyRev = (B * A).charpolyRev := by
  simp only [charpolyRev, Matrix.map_mul]
  exact transfer_determinant_mul_comm _ _ _

/-- [proved-standard; formal-checked] `(AB)ᵏ⁺¹ = A (BA)ᵏ B`. -/
theorem pow_succ_mul_comm (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

/-- [proved-standard; formal-checked] `tr((AB)ᵏ) = tr((BA)ᵏ)` for every `k ≥ 1`, any sizes. -/
theorem trace_pow_mul_comm (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    ((A * B) ^ (k + 1)).trace = ((B * A) ^ (k + 1)).trace := by
  rw [pow_succ_mul_comm, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- [proved-standard; formal-checked] `Xⁿ·χ_(AB) = Xᵐ·χ_(BA)`: the size enters as a power of `X`. -/
theorem charpoly_mul_comm_rect (A : Matrix m n R) (B : Matrix n m R) :
    X ^ Fintype.card n * (A * B).charpoly = X ^ Fintype.card m * (B * A).charpoly :=
  charpoly_mul_comm' A B

/-- [proved-standard; formal-checked] For square carriers `χ_(AB) = χ_(BA)`, singular allowed. -/
theorem charpoly_mul_comm_square (A B : Matrix n n R) : (A * B).charpoly = (B * A).charpoly :=
  charpoly_mul_comm A B

/-- [proved-standard; formal-checked] For square carriers `det(AB) = det(BA)`, singular allowed. -/
theorem det_mul_comm_square (A B : Matrix n n R) : (A * B).det = (B * A).det :=
  det_mul_comm A B

end Carrier

/-! ## 2. A unit frame carries material of any kind -/

section UnitFrame

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- [definition] Material `P` of any kind carried to phase `d` by the unit phase shift `S`. -/
def carry (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) : Matrix ι ι R :=
  (((S ^ d)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * P * ((S ^ d : (Matrix ι ι R)ˣ) : Matrix ι ι R)

/-- [proved-derived; formal-checked] On unit material, `carry` is the owner's `phaseTransport`. -/
theorem carry_units (S P : (Matrix ι ι R)ˣ) (d : ℤ) :
    carry S (P : Matrix ι ι R) d = ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by
  simp [carry, phaseTransport, _root_.zpow_neg, Units.val_mul]

/-- [proved-derived; formal-checked] The powers of carried material are the carried powers. -/
theorem carry_pow (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) (k : ℕ) :
    carry S P d ^ k = carry S (P ^ k) d :=
  Units.conj_pow' (S ^ d) P k

/-- [proved-derived; formal-checked] A unit frame conserves the determinant of any material. -/
theorem carry_conserves_determinant (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) :
    (carry S P d).det = P.det :=
  det_units_conj' (S ^ d) P

/-- [proved-derived; formal-checked] A unit frame conserves the whole trace sequence of any material. -/
theorem carry_conserves_trace_sequence (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) (k : ℕ) :
    ((carry S P d) ^ k).trace = (P ^ k).trace := by
  rw [carry_pow]
  exact trace_units_conj' (S ^ d) (P ^ k)

/-- [proved-derived; formal-checked] The transfer determinant, read from the reversed carrier. -/
theorem carry_conserves_transfer_determinant (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ)
    (T : R) : ((1 : Matrix ι ι R) - T • carry S P d).det = ((1 : Matrix ι ι R) - T • P).det := by
  rw [carry, Matrix.mul_assoc, transfer_determinant_mul_comm, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one]

/-- [proved-derived; formal-checked] The transfer polynomial, read from the reversed carrier. -/
theorem carry_conserves_charpolyRev (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) :
    (carry S P d).charpolyRev = P.charpolyRev := by
  rw [carry, Matrix.mul_assoc, charpolyRev_mul_comm, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one]

/-- [proved-derived; formal-checked] The charpoly, read from the reversed carrier. -/
theorem carry_conserves_charpoly (S : (Matrix ι ι R)ˣ) (P : Matrix ι ι R) (d : ℤ) :
    (carry S P d).charpoly = P.charpoly := by
  rw [carry, charpoly_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

/-- [proved-derived; formal-checked] The owner's `carried_material_conserves_determinant`. -/
theorem recovers_carried_determinant (S P : (Matrix ι ι R)ˣ) (d : ℤ) :
    ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R).det = (P : Matrix ι ι R).det := by
  rw [← carry_units]
  exact carry_conserves_determinant S P d

/-- [proved-derived; formal-checked] The owner's `carried_material_conserves_trace_sequence`. -/
theorem recovers_carried_trace_sequence (S P : (Matrix ι ι R)ˣ) (d : ℤ) (k : ℕ) :
    (((phaseTransport S P d) ^ k : (Matrix ι ι R)ˣ) : Matrix ι ι R).trace
      = ((P ^ k : (Matrix ι ι R)ˣ) : Matrix ι ι R).trace := by
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← carry_units]
  exact carry_conserves_trace_sequence S P d k

/-- [proved-derived; formal-checked] The owner's `carried_material_conserves_transfer_determinant`. -/
theorem recovers_carried_transfer_determinant (S P : (Matrix ι ι R)ˣ) (d : ℤ) (T : R) :
    ((1 : Matrix ι ι R) - T • ((phaseTransport S P d : (Matrix ι ι R)ˣ) : Matrix ι ι R)).det
      = ((1 : Matrix ι ι R) - T • (P : Matrix ι ι R)).det := by
  rw [← carry_units]
  exact carry_conserves_transfer_determinant S P d T

/-- [proved-derived; formal-checked] An intertwining `U P = Q U` by a unit conserves `tr` of powers. -/
theorem unit_intertwiner_conserves_trace_sequence (U : (Matrix ι ι R)ˣ) {P Q : Matrix ι ι R}
    (h : (U : Matrix ι ι R) * P = Q * U) (k : ℕ) : (P ^ k).trace = (Q ^ k).trace := by
  have hP : P = (↑U⁻¹ : Matrix ι ι R) * Q * U := by
    rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [hP, Units.conj_pow', trace_units_conj']

end UnitFrame

/-! ## 3. Reset carriers -/

section Reset

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- [definition] A reset carrier: an idempotent `E·E = E`, a projection onto what it keeps. -/
def IsReset (E : Matrix ι ι R) : Prop := E * E = E

/-- [proved-derived; formal-checked] The zero carrier is the full reset. -/
theorem isReset_zero : IsReset (0 : Matrix ι ι R) := by
  simp [IsReset]

/-- [proved-derived; formal-checked] Material read through a reset has the trace sequence of `P E`. -/
theorem reset_compression_trace_pow {E : Matrix ι ι R} (hE : IsReset E) (P : Matrix ι ι R)
    (k : ℕ) : ((E * P * E) ^ (k + 1)).trace = ((P * E) ^ (k + 1)).trace := by
  rw [Matrix.mul_assoc, trace_pow_mul_comm, Matrix.mul_assoc, hE]

/-- [proved-derived; formal-checked] Material read through a reset has the transfer determinant of `P E`. -/
theorem reset_compression_transfer_determinant {E : Matrix ι ι R} (hE : IsReset E)
    (P : Matrix ι ι R) (T : R) :
    ((1 : Matrix ι ι R) - T • (E * P * E)).det = ((1 : Matrix ι ι R) - T • (P * E)).det := by
  rw [Matrix.mul_assoc, transfer_determinant_mul_comm, Matrix.mul_assoc, hE]

/-- [proved-derived; formal-checked] Material read through a reset has the charpoly of `P E`. -/
theorem reset_compression_charpoly {E : Matrix ι ι R} (hE : IsReset E) (P : Matrix ι ι R) :
    (E * P * E).charpoly = (P * E).charpoly := by
  rw [Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hE]

/-- [proved-derived; formal-checked] Through the zero reset: transfer determinant one, traces zero. -/
theorem zero_reset_faces (P : Matrix ι ι R) (T : R) (k : ℕ) :
    ((1 : Matrix ι ι R) - T • (0 * P)).det = 1 ∧ ((0 * P) ^ (k + 1)).trace = 0 := by
  simp

end Reset

/-! ### The witnesses: a carrier between sizes, and a singular intertwiner -/

/-- [definition] The row carrier `(1, 0)` from two states to one. -/
def rowCarrier : Matrix (Fin 1) (Fin 2) ℤ := !![1, 0]

/-- [definition] The column carrier `(1, 0)ᵀ` from one state to two. -/
def columnCarrier : Matrix (Fin 2) (Fin 1) ℤ := !![1; 0]

/-- [definition] The two-state reset `diag(1, 0)`. -/
def resetTwo : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- [proved-derived; formal-checked] One way round, the carriers give the one-state identity. -/
theorem rowCarrier_mul_columnCarrier : rowCarrier * columnCarrier = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [rowCarrier, columnCarrier, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The other way round, they give the reset `diag(1, 0)`. -/
theorem columnCarrier_mul_rowCarrier : columnCarrier * rowCarrier = resetTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowCarrier, columnCarrier, resetTwo, Matrix.mul_apply]

/-- [proved-derived; formal-checked] `diag(1, 0)` is a reset carrier. -/
theorem resetTwo_isReset : IsReset resetTwo := by
  unfold IsReset
  ext i j
  fin_cases i <;> fin_cases j <;> simp [resetTwo, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The reversed carrier between sizes is a reset. -/
theorem reversed_carrier_isReset : IsReset (columnCarrier * rowCarrier) := by
  rw [columnCarrier_mul_rowCarrier]
  exact resetTwo_isReset

/-- [counterexample; formal-checked] `det(AB) = 1` and `det(BA) = 0` for the row and column. -/
theorem rect_det_differs : (rowCarrier * columnCarrier).det ≠ (columnCarrier * rowCarrier).det := by
  rw [rowCarrier_mul_columnCarrier, columnCarrier_mul_rowCarrier, det_one, resetTwo,
    det_fin_two_of]
  norm_num

/-- [counterexample; formal-checked] The zeroth traces read the two sizes, `1` and `2`. -/
theorem rect_trace_zero_differs :
    ((rowCarrier * columnCarrier) ^ 0).trace ≠ ((columnCarrier * rowCarrier) ^ 0).trace := by
  simp [trace_one]

/-- [counterexample; formal-checked] The singular reset `E` intertwines `1` with `E`, yet `tr 1 = 2 ≠ 1 = tr E`. -/
theorem singular_intertwiner_breaks_trace :
    resetTwo * (1 : Matrix (Fin 2) (Fin 2) ℤ) = resetTwo * resetTwo ∧ resetTwo.det = 0 ∧
      (1 : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ resetTwo.trace := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_one, resetTwo_isReset]
  · simp [resetTwo, det_fin_two_of]
  · simp [resetTwo, trace_fin_two_of]

/-! ## 4. Newton's identities at their coefficient domain -/

section Newton

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- [proved-standard; formal-checked] **Newton**, any commutative ring: `(k + 1)·r_(k+1) = −Σ_(i+j=k) r_i·tr(Mʲ⁺¹)`. -/
theorem newton_transfer (M : Matrix ι ι R) (k : ℕ) :
    ((k : R) + 1) * M.charpolyRev.coeff (k + 1) =
      -∑ p ∈ antidiagonal k, M.charpolyRev.coeff p.1 * (M ^ (p.2 + 1)).trace := by
  have h := congrArg (PowerSeries.coeff k)
    (Holonics.Aeon.Production.Zeta.transferDet_derivative M)
  rw [PowerSeries.coeff_derivative, neg_mul, map_neg, PowerSeries.coeff_mul] at h
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at h
  rw [mul_comm, h]

/-- [proved-standard; formal-checked] `r_j = c_(n−j)` for `j ≤ n`: the transfer polynomial reverses the charpoly. -/
theorem coeff_charpolyRev (M : Matrix ι ι R) {j : ℕ} (hj : j ≤ Fintype.card ι) :
    M.charpolyRev.coeff j = M.charpoly.coeff (Fintype.card ι - j) := by
  nontriviality R
  rw [← M.reverse_charpoly, coeff_reverse, charpoly_natDegree_eq_dim, revAt_le hj]

/-- [proved-standard; formal-checked] The transfer polynomial has no coefficient past the size. -/
theorem coeff_charpolyRev_eq_zero (M : Matrix ι ι R) {j : ℕ} (hj : Fintype.card ι < j) :
    M.charpolyRev.coeff j = 0 := by
  nontriviality R
  apply coeff_eq_zero_of_natDegree_lt
  rw [← M.reverse_charpoly]
  calc _ ≤ M.charpoly.natDegree := reverse_natDegree_le _
    _ = Fintype.card ι := charpoly_natDegree_eq_dim M
    _ < j := hj

/-- [proved-standard; formal-checked] Past the size Newton is the recurrence `Σ_(i+j=k) r_i·tr(Mʲ⁺¹) = 0`. -/
theorem trace_recurrence (M : Matrix ι ι R) {k : ℕ} (hk : Fintype.card ι ≤ k) :
    ∑ p ∈ antidiagonal k, M.charpolyRev.coeff p.1 * (M ^ (p.2 + 1)).trace = 0 := by
  have h := newton_transfer M k
  rw [coeff_charpolyRev_eq_zero M (by omega), mul_zero] at h
  exact neg_eq_zero.mp h.symm

/-- [proved-standard; formal-checked] **Newton, charpoly form:** `k·c_(n−k) = −Σ_(i=1..k) c_(n−k+i)·tr(Mⁱ)`, `k ≤ n`. -/
theorem newton_charpoly (M : Matrix ι ι R) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (k : R) * M.charpoly.coeff (Fintype.card ι - k) =
      -∑ i ∈ range k, M.charpoly.coeff (Fintype.card ι - k + (i + 1)) * (M ^ (i + 1)).trace := by
  rcases k with _ | k
  · simp
  · have hs : ∑ p ∈ antidiagonal k, M.charpolyRev.coeff p.1 * (M ^ (p.2 + 1)).trace =
        ∑ i ∈ range (k + 1), M.charpolyRev.coeff (k - i) * (M ^ (i + 1)).trace := by
      rw [← Finset.Nat.sum_antidiagonal_swap]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => M.charpolyRev.coeff b * (M ^ (a + 1)).trace) k
    have h := newton_transfer M k
    rw [hs, coeff_charpolyRev M hk] at h
    push_cast
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [coeff_charpolyRev M (by omega)]
    congr 2
    omega

/-- [proved-standard; formal-checked] The two-by-two turn: `2·det M = (tr M)² − tr(M²)`, from `newton_charpoly`. -/
theorem two_site_newton (M : Matrix (Fin 2) (Fin 2) R) :
    2 * M.det = M.trace ^ 2 - (M ^ 2).trace := by
  nontriviality R
  have h := newton_charpoly M (k := 2) (by simp)
  rw [charpoly_fin_two] at h
  simp only [Fintype.card_fin, Nat.sub_self, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, pow_one, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at h
  norm_num at h
  linear_combination h

/-- [proved-standard; formal-checked] Where `1, …, n` cancel, the traces `tr(Mⁱ)` fix the transfer polynomial. -/
theorem charpolyRev_eq_of_trace_eq
    (hreg : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι → IsLeftRegular (k : R)) {M N : Matrix ι ι R}
    (htr : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card ι → (M ^ i).trace = (N ^ i).trace) :
    M.charpolyRev = N.charpolyRev := by
  ext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases j with _ | k
  · rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev,
      Matrix.eval_charpolyRev]
  · by_cases hk : k + 1 ≤ Fintype.card ι
    · have hu : IsLeftRegular ((k : R) + 1) := by exact_mod_cast hreg (k + 1) (by omega) hk
      refine hu ?_
      show ((k : R) + 1) * _ = ((k : R) + 1) * _
      rw [newton_transfer, newton_transfer]
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega), htr (p.2 + 1) (by omega) (by omega)]
    · rw [coeff_charpolyRev_eq_zero M (by omega), coeff_charpolyRev_eq_zero N (by omega)]

/-- [proved-standard; formal-checked] Where `1, …, n` cancel, the traces `tr(Mⁱ)`, `1 ≤ i ≤ n`, fix the charpoly. -/
theorem charpoly_eq_of_trace_eq
    (hreg : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι → IsLeftRegular (k : R)) {M N : Matrix ι ι R}
    (htr : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card ι → (M ^ i).trace = (N ^ i).trace) :
    M.charpoly = N.charpoly := by
  nontriviality R
  have h := charpolyRev_eq_of_trace_eq hreg htr
  ext i
  by_cases hi : i ≤ Fintype.card ι
  · have hj : Fintype.card ι - i ≤ Fintype.card ι := Nat.sub_le _ _
    have e : i = Fintype.card ι - (Fintype.card ι - i) := by omega
    rw [e, ← coeff_charpolyRev M hj, ← coeff_charpolyRev N hj, h]
  · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt] <;>
      simp only [charpoly_natDegree_eq_dim] <;> omega

/-- [proved-standard; formal-checked] Over a `ℚ`-algebra the traces determine the charpoly. -/
theorem charpoly_eq_of_trace_eq_rat [Algebra ℚ R] {M N : Matrix ι ι R}
    (htr : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card ι → (M ^ i).trace = (N ^ i).trace) :
    M.charpoly = N.charpoly := by
  refine charpoly_eq_of_trace_eq (fun k hk _ => ?_) htr
  rw [← map_natCast (algebraMap ℚ R) k]
  exact ((IsUnit.mk0 (k : ℚ) (by exact_mod_cast (show k ≠ 0 by omega))).map _).isRegular.left

/-- [proved-standard; formal-checked] Over a domain of characteristic zero, `ℤ` among them, traces fix the charpoly. -/
theorem charpoly_eq_of_trace_eq_charZero [IsDomain R] [CharZero R] {M N : Matrix ι ι R}
    (htr : ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card ι → (M ^ i).trace = (N ^ i).trace) :
    M.charpoly = N.charpoly :=
  charpoly_eq_of_trace_eq
    (fun k hk _ => (IsRegular.of_ne_zero (by exact_mod_cast (show k ≠ 0 by omega))).left) htr

end Newton

/-- [counterexample; formal-checked] Over `ZMod p` at size `p`, `0` and `1` have one trace sequence from `k = 1`. -/
theorem zmod_trace_sequences_agree (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) :
    ((0 : Matrix (Fin p) (Fin p) (ZMod p)) ^ k).trace
      = ((1 : Matrix (Fin p) (Fin p) (ZMod p)) ^ k).trace := by
  rw [zero_pow (by omega), one_pow, trace_zero, trace_one, Fintype.card_fin, ZMod.natCast_self]

/-- [counterexample; formal-checked] Their charpolys `Xᵖ` and `(X − 1)ᵖ` differ (at `X = 0`). -/
theorem zmod_charpolys_differ (p : ℕ) [hp : Fact p.Prime] :
    (0 : Matrix (Fin p) (Fin p) (ZMod p)).charpoly
      ≠ (1 : Matrix (Fin p) (Fin p) (ZMod p)).charpoly := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  rw [charpoly_zero, charpoly_one, Fintype.card_fin] at h0
  simp only [eval_pow, eval_X, eval_sub, eval_one, zero_sub] at h0
  rw [zero_pow hp.out.ne_zero] at h0
  exact pow_ne_zero p (neg_ne_zero.mpr one_ne_zero) h0.symm

/-- [counterexample; formal-checked] There `p` is no unit: `newton_charpoly` at `k = p` cannot solve for `c_0`. -/
theorem zmod_prime_is_not_unit (p : ℕ) [Fact p.Prime] : ¬ IsUnit ((p : ℕ) : ZMod p) := by
  rw [ZMod.natCast_self]
  exact not_isUnit_zero

/-! ## 5. Sites of any size -/

section UniformSites

variable {σ o R : Type*} [Fintype σ] [DecidableEq σ] [Fintype o] [DecidableEq o] [CommRing R]

/-- [proved-standard; formal-checked] The characteristic matrix of a block-diagonal machine is block-diagonal. -/
theorem charmatrix_blockDiagonal (M : σ → Matrix o o R) :
    charmatrix (blockDiagonal M) = blockDiagonal fun g => charmatrix (M g) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hab : a = b
  · subst hab
    by_cases hij : i = j
    · subst hij
      simp [blockDiagonal_apply_eq]
    · rw [charmatrix_apply_ne _ _ _ (by simp [hij]), blockDiagonal_apply_eq,
        blockDiagonal_apply_eq, charmatrix_apply_ne _ _ _ hij]
  · rw [charmatrix_apply_ne _ _ _ (by simp [hab]), blockDiagonal_apply_ne _ _ _ hab,
      blockDiagonal_apply_ne _ _ _ hab, map_zero, neg_zero]

/-- [proved-standard; formal-checked] The machine's charpoly is the product of the sites'. -/
theorem charpoly_blockDiagonal (M : σ → Matrix o o R) :
    (blockDiagonal M).charpoly = ∏ g, (M g).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal, det_blockDiagonal]
  rfl

/-- [proved-standard; formal-checked] The machine's transfer determinant is the product of the sites', any site size. -/
theorem transfer_determinant_blockDiagonal (M : σ → Matrix o o R) (T : R) :
    ((1 : Matrix (o × σ) (o × σ) R) - T • blockDiagonal M).det
      = ∏ g, ((1 : Matrix o o R) - T • M g).det := by
  have h : (1 : Matrix (o × σ) (o × σ) R) - T • blockDiagonal M
      = blockDiagonal (fun g => (1 : Matrix o o R) - T • M g) := by
    rw [← blockDiagonal_one, ← blockDiagonal_smul, ← blockDiagonal_sub]
    rfl
  rw [h, det_blockDiagonal]

/-- [proved-standard; formal-checked] The machine's trace sequence is the sum of the sites'. -/
theorem trace_pow_blockDiagonal (M : σ → Matrix o o R) (k : ℕ) :
    ((blockDiagonal M) ^ k).trace = ∑ g, ((M g) ^ k).trace := by
  rw [← blockDiagonal_pow, trace_blockDiagonal]
  rfl

/-- [proved-derived; formal-checked] The owner's `machine_transfer_determinant` is the case `o = Fin 2`. -/
theorem recovers_machine_transfer_determinant (M : σ → Matrix (Fin 2) (Fin 2) R) (T : R) :
    ((1 : Matrix (Fin 2 × σ) (Fin 2 × σ) R) - T • Matrix.blockDiagonal M).det
      = ∏ g, ((1 : Matrix (Fin 2) (Fin 2) R) - T • M g).det :=
  transfer_determinant_blockDiagonal M T

/-- [proved-derived; formal-checked] The owner's `machine_trace_sequence` is the case `o = Fin 2`. -/
theorem recovers_machine_trace_sequence (M : σ → Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    ((Matrix.blockDiagonal M) ^ k).trace = ∑ g, ((M g) ^ k).trace :=
  trace_pow_blockDiagonal M k

end UniformSites

section VaryingSites

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
variable {ι : σ → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]

/-- [proved-standard; formal-checked] The determinant of sites of varying sizes is the product of theirs. -/
theorem det_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) :
    (blockDiagonal' M).det = ∏ s, (M s).det := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← det_submatrix_equiv_self (Equiv.sigmaSubtype s).symm]
  congr 1
  ext i j
  simp only [submatrix_apply, toSquareBlock_def, of_apply]
  exact blockDiagonal'_apply_eq M s i j

/-- [proved-standard; formal-checked] The characteristic matrix of sites of varying sizes is block-diagonal. -/
theorem charmatrix_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) :
    charmatrix (blockDiagonal' M) = blockDiagonal' fun s => charmatrix (M s) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst hab
    by_cases hij : i = j
    · subst hij
      simp [blockDiagonal'_apply_eq]
    · rw [charmatrix_apply_ne _ _ _ (by simp [hij]), blockDiagonal'_apply_eq,
        blockDiagonal'_apply_eq, charmatrix_apply_ne _ _ _ hij]
  · rw [charmatrix_apply_ne _ _ _ (by simp [hab]), blockDiagonal'_apply_ne _ _ _ hab,
      blockDiagonal'_apply_ne _ _ _ hab, map_zero, neg_zero]

/-- [proved-standard; formal-checked] The charpoly of sites of varying sizes is the product of theirs. -/
theorem charpoly_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) :
    (blockDiagonal' M).charpoly = ∏ s, (M s).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal', det_blockDiagonal']
  rfl

/-- [proved-standard; formal-checked] The transfer determinant of sites of varying sizes is the product of theirs. -/
theorem transfer_determinant_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) (T : R) :
    ((1 : Matrix (Σ s, ι s) (Σ s, ι s) R) - T • blockDiagonal' M).det
      = ∏ s, ((1 : Matrix (ι s) (ι s) R) - T • M s).det := by
  have h : (1 : Matrix (Σ s, ι s) (Σ s, ι s) R) - T • blockDiagonal' M
      = blockDiagonal' (fun s => (1 : Matrix (ι s) (ι s) R) - T • M s) := by
    rw [← blockDiagonal'_one, ← blockDiagonal'_smul, ← blockDiagonal'_sub]
    rfl
  rw [h, det_blockDiagonal']

/-- [proved-standard; formal-checked] The transfer polynomial of sites of varying sizes is the product of theirs. -/
theorem charpolyRev_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) :
    (blockDiagonal' M).charpolyRev = ∏ s, (M s).charpolyRev := by
  rw [charpolyRev, blockDiagonal'_map _ _ (map_zero _), transfer_determinant_blockDiagonal']
  rfl

/-- [proved-standard; formal-checked] The trace sequence of sites of varying sizes is the sum of theirs. -/
theorem trace_pow_blockDiagonal' (M : ∀ s, Matrix (ι s) (ι s) R) (k : ℕ) :
    ((blockDiagonal' M) ^ k).trace = ∑ s, ((M s) ^ k).trace := by
  rw [← blockDiagonal'_pow, trace_blockDiagonal']
  rfl

end VaryingSites

/-! ## 6. Two sites run together uncoupled -/

section Kronecker

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- [proved-standard; formal-checked] `(A ⊗ B)ᵏ = Aᵏ ⊗ Bᵏ`. -/
theorem kronecker_pow (A : Matrix m m R) (B : Matrix n n R) (k : ℕ) :
    (A ⊗ₖ B) ^ k = (A ^ k) ⊗ₖ (B ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- [proved-standard; formal-checked] `tr((A ⊗ B)ᵏ) = tr(Aᵏ)·tr(Bᵏ)`: the composite's closed words are pairs. -/
theorem trace_pow_kronecker (A : Matrix m m R) (B : Matrix n n R) (k : ℕ) :
    ((A ⊗ₖ B) ^ k).trace = (A ^ k).trace * (B ^ k).trace := by
  rw [kronecker_pow, trace_kronecker]

end Kronecker

end Holonics.Transport.TraceFacesGeneral
