import ElementaryHolonics.Millennium.FamilyTunnellBrandtUnitWeights

/-!
# Finite transport fibres and the retained stabilizer-weight bridge

The explicit q₁/q₂ classifications are now packaged as equivalences with the
full additive isometry types.  The final paragraph deliberately leaves the
identification with quaternionic right-order stabilizer weights as a typed
source obligation: an equal cardinality of quadratic automorphism fibres does
not, by itself, identify the Brandt convention's unit groups.
-/

noncomputable section
namespace Soma.Holonics.Millennium.FamilyTunnellBrandtStabilizerWeights

open Soma.Holonics.Millennium.FamilyTunnellBrandtUnitWeights
open Soma.Holonics.Millennium.FamilyTunnellBrandtTwoClassInterchange

private theorem q₁_exists_label (A : LatticeTransport q₁) :
    ∃ abc : Bool × Bool × Bool, q₁Aut abc.1 abc.2.1 abc.2.2 = A := by
  classical
  have hmem := q₁_exhaustive_unit_classification A
  rw [q₁UnitTransports] at hmem
  rcases Finset.mem_image.mp hmem with ⟨abc, _, h⟩
  exact ⟨abc, h⟩

private theorem q₂_exists_label (A : LatticeTransport q₂) :
    ∃ abc : Bool × Bool × Bool, q₂Aut abc.1 abc.2.1 abc.2.2 = A := by
  classical
  have hmem := q₂_exhaustive_unit_classification A
  rw [q₂UnitTransports] at hmem
  rcases Finset.mem_image.mp hmem with ⟨abc, _, h⟩
  exact ⟨abc, h⟩

noncomputable def q₁LabelOf (A : LatticeTransport q₁) : Bool × Bool × Bool :=
  Classical.choose (q₁_exists_label A)

private theorem q₁LabelOf_spec (A : LatticeTransport q₁) :
    q₁Aut (q₁LabelOf A).1 (q₁LabelOf A).2.1 (q₁LabelOf A).2.2 = A :=
  Classical.choose_spec (q₁_exists_label A)

noncomputable def q₂LabelOf (A : LatticeTransport q₂) : Bool × Bool × Bool :=
  Classical.choose (q₂_exists_label A)

private theorem q₂LabelOf_spec (A : LatticeTransport q₂) :
    q₂Aut (q₂LabelOf A).1 (q₂LabelOf A).2.1 (q₂LabelOf A).2.2 = A :=
  Classical.choose_spec (q₂_exists_label A)

noncomputable def q₁TransportEquiv :
    (Bool × Bool × Bool) ≃ LatticeTransport q₁ where
  toFun abc := q₁Aut abc.1 abc.2.1 abc.2.2
  invFun := q₁LabelOf
  left_inv := by
    intro abc
    apply q₁Aut_injective
    exact q₁LabelOf_spec (q₁Aut abc.1 abc.2.1 abc.2.2)
  right_inv := q₁LabelOf_spec

noncomputable def q₂TransportEquiv :
    (Bool × Bool × Bool) ≃ LatticeTransport q₂ where
  toFun abc := q₂Aut abc.1 abc.2.1 abc.2.2
  invFun := q₂LabelOf
  left_inv := by
    intro abc
    apply q₂Aut_injective
    exact q₂LabelOf_spec (q₂Aut abc.1 abc.2.1 abc.2.2)
  right_inv := q₂LabelOf_spec

noncomputable instance : Fintype (LatticeTransport q₁) :=
  Fintype.ofEquiv (Bool × Bool × Bool) q₁TransportEquiv

noncomputable instance : Fintype (LatticeTransport q₂) :=
  Fintype.ofEquiv (Bool × Bool × Bool) q₂TransportEquiv

theorem q₁_transport_card : Fintype.card (LatticeTransport q₁) = 8 := by
  rw [← Fintype.card_congr q₁TransportEquiv]
  simp

theorem q₂_transport_card : Fintype.card (LatticeTransport q₂) = 8 := by
  rw [← Fintype.card_congr q₂TransportEquiv]
  simp

theorem q₁_q₂_transport_card_equal :
    Fintype.card (LatticeTransport q₁) = Fintype.card (LatticeTransport q₂) := by
  rw [q₁_transport_card, q₂_transport_card]

/-- The source-neutral weighted Brandt consequence available from the two
classified additive fibres.  It is intentionally a typed equality of the
finite transport fibres, not yet an identification with right-order units. -/
theorem classified_transport_fibres_equal_weight :
    Fintype.card (LatticeTransport q₁) = Fintype.card (LatticeTransport q₂) :=
  q₁_q₂_transport_card_equal

theorem classified_transport_card_cast_equal :
    (Fintype.card (LatticeTransport q₁) : ℤ) =
      (Fintype.card (LatticeTransport q₂) : ℤ) := by
  rw [q₁_transport_card, q₂_transport_card]

/-- If the Brandt weight chart is calibrated by the classified additive
fibres, weighted self-adjointness descends exactly to the signed difference
receiver.  The calibration equalities are explicit inputs, not inferred from
the finite cardinality alone. -/
theorem weighted_interchange_of_classified_card_calibration
    {lambda : ℤ} (A : WeightedTwoClassNeighborAction lambda)
    (hfirst : A.unitWeightFirst = (Fintype.card (LatticeTransport q₁) : ℤ))
    (hsecond : A.unitWeightSecond = (Fintype.card (LatticeTransport q₂) : ℤ)) :
    A.offDiagonalFirst = A.offDiagonalSecond := by
  apply A.offDiagonalInterchange_of_equal_weight
  rw [hfirst, hsecond, classified_transport_card_cast_equal]

theorem weighted_difference_of_classified_card_calibration
    {lambda : ℤ} (A : WeightedTwoClassNeighborAction lambda)
    (hfirst : A.unitWeightFirst = (Fintype.card (LatticeTransport q₁) : ℤ))
    (hsecond : A.unitWeightSecond = (Fintype.card (LatticeTransport q₂) : ℤ))
    (r₁ r₂ : ℤ) :
    ∃ hweight : A.unitWeightFirst = A.unitWeightSecond,
      (A.toTwoClassNeighborAction hweight).differenceReturn r₁ r₂ =
        lambda * (r₁ - r₂) := by
  have hweight : A.unitWeightFirst = A.unitWeightSecond := by
    rw [hfirst, hsecond, classified_transport_card_cast_equal]
  exact ⟨hweight, A.differenceReturn_eq_calibration_mul hweight r₁ r₂⟩

/-- The missing source-specific bridge, parameterized by the actual right-order
unit populations once they have been constructed.  An inhabitant must identify
those addressed populations with the complete quadratic-automorphism fibres;
bare equal natural numbers are deliberately insufficient. -/
structure RightOrderStabilizerWeightBridge
    (RightOrderUnitsFirst RightOrderUnitsSecond : Type*)
    [Fintype RightOrderUnitsFirst] [Fintype RightOrderUnitsSecond] where
  first_population_equiv : RightOrderUnitsFirst ≃ LatticeTransport q₁
  second_population_equiv : RightOrderUnitsSecond ≃ LatticeTransport q₂

def rightOrderStabilizerWeightBridgeObligation
    (RightOrderUnitsFirst RightOrderUnitsSecond : Type*)
    [Fintype RightOrderUnitsFirst] [Fintype RightOrderUnitsSecond] : Prop :=
  Nonempty
    (RightOrderStabilizerWeightBridge RightOrderUnitsFirst RightOrderUnitsSecond)

theorem rightOrder_weight_cardinality_of_bridge
    {RightOrderUnitsFirst RightOrderUnitsSecond : Type*}
    [Fintype RightOrderUnitsFirst] [Fintype RightOrderUnitsSecond]
    (bridge : RightOrderStabilizerWeightBridge
      RightOrderUnitsFirst RightOrderUnitsSecond) :
    Fintype.card RightOrderUnitsFirst = 8 ∧
      Fintype.card RightOrderUnitsSecond = 8 := by
  constructor
  · rw [Fintype.card_congr bridge.first_population_equiv, q₁_transport_card]
  · rw [Fintype.card_congr bridge.second_population_equiv, q₂_transport_card]

#print axioms q₁_transport_card
#print axioms q₂_transport_card
#print axioms q₁_q₂_transport_card_equal
#print axioms weighted_interchange_of_classified_card_calibration
#print axioms weighted_difference_of_classified_card_calibration
#print axioms rightOrder_weight_cardinality_of_bridge

end Soma.Holonics.Millennium.FamilyTunnellBrandtStabilizerWeights
