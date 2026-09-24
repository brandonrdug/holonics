import ElementaryHolonics.Foundation.TransportLift
import Mathlib.Tactic

/-!
# Exact partitions, paired cut boundaries, and arithmetic factor lifts

A partition is not an instruction to divide an object by an integer.  It is a typed map from
situated occurrences to piece addresses.  The source occurrence population reconstructs exactly
as the dependent sum of its piece fibres.

When a partition is produced by a cut, each boundary side retains its piece address, its paired
side, and an oriented hand.  The gluing involution reverses that hand and therefore cancels each
paired boundary exactly.  No equality of piece sizes is assumed.

Natural-number divisibility is then placed at its proper, much narrower altitude: a factor witness
is a lift through multiplication by one declared scalar face.  Its cofactor is unique only after
the nonzero divisor hypothesis is returned.
-/

namespace Soma.Holonics.Foundation.ExactPartition

open Soma.Holonics.Foundation.Lift

universe u v w

/-- [definition] An exact partition with its paired, oriented cut-boundary occurrences. -/
structure PartitionReceipt (Occurrence : Type u) (Piece : Type v) (BoundarySide : Type w) where
  /-- The addressed piece containing each source occurrence. -/
  pieceOf : Occurrence → Piece
  /-- The piece on whose boundary this side lies. -/
  boundaryPiece : BoundarySide → Piece
  /-- The side glued to this side when the cut is closed. -/
  mate : BoundarySide → BoundarySide
  mate_involutive : Function.Involutive mate
  mate_fixedPointFree : ∀ side, mate side ≠ side
  /-- The oriented incidence of one side. -/
  hand : BoundarySide → ℤ
  mate_reverses_hand : ∀ side, hand (mate side) = -hand side

namespace PartitionReceipt

variable {Occurrence : Type u} {Piece : Type v} {BoundarySide : Type w}

/-- [definition] One geometric piece is the complete fibre over its address. -/
def PieceFibre (P : PartitionReceipt Occurrence Piece BoundarySide) (piece : Piece) : Type u :=
  TransportLift P.pieceOf piece

/-- [definition] The disassembled population retains each occurrence together with its piece
address and exact incidence proof. -/
def Disassembled (P : PartitionReceipt Occurrence Piece BoundarySide) : Type (max u v) :=
  Σ piece, P.PieceFibre piece

/-- [proved-derived; formal-checked] The source occurrence population is exactly equivalent to the
dependent sum of all piece fibres.  This is reconstruction, not a cardinality comparison. -/
def disassemblyEquiv (P : PartitionReceipt Occurrence Piece BoundarySide) :
    Occurrence ≃ P.Disassembled where
  toFun occurrence := ⟨P.pieceOf occurrence, occurrence, rfl⟩
  invFun disassembled := disassembled.2.1
  left_inv _ := rfl
  right_inv disassembled := by
    rcases disassembled with ⟨piece, occurrence, exact⟩
    subst exact
    rfl

/-- [proved-derived; formal-checked] Each paired cut boundary returns zero total oriented hand. -/
theorem pairedBoundaryCancels (P : PartitionReceipt Occurrence Piece BoundarySide)
    (side : BoundarySide) :
    P.hand side + P.hand (P.mate side) = 0 := by
  rw [P.mate_reverses_hand]
  exact add_neg_cancel _

/-- [proved-derived; formal-checked] Gluing a side twice returns the original addressed side. -/
@[simp] theorem mate_mate (P : PartitionReceipt Occurrence Piece BoundarySide)
    (side : BoundarySide) : P.mate (P.mate side) = side :=
  P.mate_involutive side

end PartitionReceipt

/-! ## Arithmetic factorization is one specialized transport lift -/

/-- [definition] An exact arithmetic factor witness retains the cofactor and its multiplication
receipt.  It is not a factorization of an arbitrary source holon. -/
structure NatFactorWitness (divisor value : ℕ) where
  cofactor : ℕ
  reconstructs : value = divisor * cofactor

namespace NatFactorWitness

/-- A factor witness is a transport lift through multiplication by the declared divisor. -/
def asTransportLift {divisor value : ℕ} (witness : NatFactorWitness divisor value) :
    TransportLift (fun cofactor ↦ divisor * cofactor) value :=
  ⟨witness.cofactor, witness.reconstructs.symm⟩

/-- A multiplication lift returns the corresponding arithmetic factor witness. -/
def ofTransportLift {divisor value : ℕ}
    (lift : TransportLift (fun cofactor ↦ divisor * cofactor) value) :
    NatFactorWitness divisor value :=
  ⟨lift.1, lift.2.symm⟩

/-- [proved-derived; formal-checked] Arithmetic divisibility is exactly the existence of this
specialized multiplication lift. -/
theorem nonempty_iff_dvd (divisor value : ℕ) :
    Nonempty (NatFactorWitness divisor value) ↔ divisor ∣ value := by
  constructor
  · rintro ⟨witness⟩
    exact ⟨witness.cofactor, witness.reconstructs⟩
  · rintro ⟨cofactor, reconstructs⟩
    exact ⟨⟨cofactor, reconstructs⟩⟩

/-- [proved-derived; formal-checked] A positive divisor gives the scalar multiplication lift a
unique cofactor.  The proof does not promote that scalar fact to a source-holon decomposition. -/
theorem cofactor_unique_of_positive {divisor value : ℕ} (hdivisor : 0 < divisor)
    (left right : NatFactorWitness divisor value) :
    left.cofactor = right.cofactor := by
  have h : divisor * left.cofactor = divisor * right.cofactor := by
    exact left.reconstructs.symm.trans right.reconstructs
  exact Nat.eq_of_mul_eq_mul_left hdivisor h

end NatFactorWitness

/-! ## Equal and unequal piece measures remain distinct laws -/

/-- [proved-derived; formal-checked] Equal piece measures imply the familiar scalar product only
after equality of every piece measure has been supplied. -/
theorem sum_piece_measure_of_equal {Piece : Type*} [Fintype Piece]
    (measure : Piece → ℕ) (unit : ℕ) (equal : ∀ piece, measure piece = unit) :
    ∑ piece, measure piece = Fintype.card Piece * unit := by
  simp_rw [equal]
  simp

section Audit

#print axioms PartitionReceipt.disassemblyEquiv
#print axioms PartitionReceipt.pairedBoundaryCancels
#print axioms NatFactorWitness.nonempty_iff_dvd
#print axioms NatFactorWitness.cofactor_unique_of_positive
#print axioms sum_piece_measure_of_equal

end Audit

end Soma.Holonics.Foundation.ExactPartition
