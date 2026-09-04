import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver

/-!
# The rational Hodge receiver is no longer a semantic predicate

The earlier receiver allowed a semantics predicate to approve any proposed rational Hodge
submodule.  Its firing counterexample chose the top submodule independently of the cohomology and
then paired it with the zero cycle-class map.

That aperture has been removed.  A realization now carries a complete internal decomposition of
the complexified rational Betti cohomology into the addressed components
`H^{r,weight-r}`, together with conjugation exchange.  The rational `(p,p)` receiver is
definitionally the preimage of the middle component under rational complexification.  Consequently
declaring the receiver to be top entails the concrete statement that every rational class lands in
that component; it is no longer a freely selected field.

Construction of complex analytification, the complete Hodge splitting, and the cycle-class map
remain explicit source-specific obligations in `HodgeSemantics X`.  This file records exactly the
free-semantic aperture deleted by the stronger type.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSemanticsFaithfulness

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

/-- [proved-derived; formal-checked] The rational Hodge submodule of a genuine realization is
definitionally reconstructed from its complete Hodge splitting. -/
theorem realization_hodge_receiver_is_derived
    (realization : Realization) (p : ℕ) :
    (realization.datum p).rationalHodgeClasses =
      (realization.hodgeDecomposition p).rationalMiddle p :=
  rfl

/-- [proved-derived; formal-checked] Two complete splittings with the same addressed component
population return exactly the same rational middle receiver. -/
theorem rationalMiddle_eq_of_components_eq {H : ModuleCat ℚ} (p : ℕ)
    (left right : PureHodgeDecomposition H (2 * p))
    (components : left.component = right.component) :
    left.rationalMiddle p = right.rationalMiddle p := by
  unfold PureHodgeDecomposition.rationalMiddle
  rw [components]

/-- [proved-derived; formal-checked] The rational middle receiver is top exactly when every
rational occurrence complexifies into the declared `(p,p)` component.  Thus `⊤` is a theorem
about the splitting, not an independently writable semantic label. -/
theorem rationalMiddle_eq_top_iff {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) :
    splitting.rationalMiddle p = ⊤ ↔
      ∀ hodgeClass : H,
        rationalToComplex H hodgeClass ∈
          splitting.component (middleHodgeIndex p) := by
  rw [eq_top_iff]
  constructor
  · intro allClasses hodgeClass
    exact (splitting.mem_rationalMiddle_iff p hodgeClass).mp
      (allClasses Submodule.mem_top)
  · intro allMiddle hodgeClass _
    exact (splitting.mem_rationalMiddle_iff p hodgeClass).mpr
      (allMiddle hodgeClass)

/-! ## The remaining canonicality boundary is necessary -/

/-- [definition] Erase only the cycle-class current of a source-indexed semantics while retaining
its scheme, analytic-point population, complete Hodge splitting, and every point-chart law.

This operation is deliberately not an admitted geometric realization.  It exposes the exact
freedom which `Canonical : Realization → Prop` must exclude. -/
def eraseCycleClass {X : AlgebraicGeometry.Scheme}
    (semantics : HodgeSemantics X) : HodgeSemantics X where
  complexDimension := semantics.complexDimension
  analyticSpace := semantics.analyticSpace
  toZariski := semantics.toZariski
  toZariski_closed := semantics.toZariski_closed
  toClosedPoint_bijective := semantics.toClosedPoint_bijective
  hodgeDecomposition := semantics.hodgeDecomposition
  cycleClass := fun _ => 0
  cycleClassesAreHodge := by
    intro p
    simpa using
      (bot_le : (⊥ : Submodule ℚ
        (RationalBettiCohomology semantics.analyticSpace p)) ≤
          (semantics.hodgeDecomposition p).rationalMiddle p)

/-- [definition] The corresponding deformation of a realization keeps the complete geometric
source and erases only its proposed cycle-class passage. -/
def eraseCycleClassRealization (realization : Realization) : Realization where
  geometry := realization.geometry
  semantics := eraseCycleClass realization.semantics

/-- [proved-derived; formal-checked] Erasing the cycle current leaves the derived rational Hodge
receiver definitionally unchanged. -/
@[simp]
theorem eraseCycleClassRealization_rationalHodgeClasses
    (realization : Realization) (p : ℕ) :
    ((eraseCycleClassRealization realization).datum p).rationalHodgeClasses =
      (realization.datum p).rationalHodgeClasses :=
  rfl

/-- [proved-derived; formal-checked] The algebraic receiver of the erased realization is exactly
the bottom submodule. -/
@[simp]
theorem eraseCycleClassRealization_algebraicSpan
    (realization : Realization) (p : ℕ) :
    ((eraseCycleClassRealization realization).datum p).algebraicSpan = ⊥ := by
  change LinearMap.range (0 : _ →ₗ[ℚ] _) = ⊥
  exact LinearMap.range_zero

/-- [counterexample; formal-checked] Whenever the retained middle Hodge receiver is nontrivial,
the cycle-erased deformation fails the Hodge conclusion.  Therefore a source-indexed bundle of
analytic points and Hodge components is not yet the canonical classical receiver: its admission
must characterize the genuine geometric cycle-class map. -/
theorem eraseCycleClassRealization_not_conclusion_of_nontrivial_middle
    (realization : Realization) (p : ℕ)
    (nontrivialMiddle : (realization.datum p).rationalHodgeClasses ≠ ⊥) :
    ¬ ((eraseCycleClassRealization realization).datum p).Conclusion := by
  intro conclusion
  change ((eraseCycleClassRealization realization).datum p).rationalHodgeClasses =
    ((eraseCycleClassRealization realization).datum p).algebraicSpan at conclusion
  rw [eraseCycleClassRealization_rationalHodgeClasses,
    eraseCycleClassRealization_algebraicSpan] at conclusion
  exact nontrivialMiddle conclusion

/-- [counterexample; formal-checked] The receiver obtained by admitting every data-bearing
`Realization` is refuted as soon as one realization has a nonzero middle Hodge class.  This is a
counterexample to that receiver, not to the classical Hodge conjecture: the erased cycle map is
precisely what geometric canonicality must reject. -/
theorem not_theHodgeConjecture_allRealizations_of_nontrivial_middle
    (realization : Realization) (p : ℕ)
    (nontrivialMiddle : (realization.datum p).rationalHodgeClasses ≠ ⊥) :
    ¬ TheHodgeConjecture (fun _ => True) := by
  intro universal
  exact eraseCycleClassRealization_not_conclusion_of_nontrivial_middle
    realization p nontrivialMiddle
    (universal (eraseCycleClassRealization realization) trivial p)

/-! ## Canonical admission must retain the actual cycle current -/

/-- [definition] A receiver admission is rigid against cycle-current erasure when no admitted
realization with a nontrivial rational middle carrier remains admitted after its cycle-class map
is replaced by zero.  This is a necessary source-faithfulness law, not the Hodge conclusion. -/
def CycleClassErasureRigid (Canonical : Realization → Prop) : Prop :=
  ∀ (realization : Realization), Canonical realization → ∀ p : ℕ,
    (realization.datum p).rationalHodgeClasses ≠ ⊥ →
      ¬ Canonical (eraseCycleClassRealization realization)

/-- [proved-derived; formal-checked] Every admission family satisfying the Hodge conjecture is
necessarily rigid against cycle-current erasure.  Thus the official receiver cannot be closed by
an admission predicate which sees only the scheme, analytic point population, or Hodge splitting;
it must distinguish the genuine geometric cycle-class current itself. -/
theorem cycleClassErasureRigid_of_hodgeConjecture
    (Canonical : Realization → Prop)
    (hodge : TheHodgeConjecture Canonical) :
    CycleClassErasureRigid Canonical := by
  intro realization hcanonical p nontrivialMiddle erasedCanonical
  exact eraseCycleClassRealization_not_conclusion_of_nontrivial_middle
    realization p nontrivialMiddle
    (hodge (eraseCycleClassRealization realization) erasedCanonical p)

/-- [proved-derived; formal-checked] Source-determined admission detects cycle-current erasure
without appealing to the Hodge conclusion whenever the emitted cycle map is nonzero.  Both the
original and erased realizations address the same complete geometric source, so admitting both
would force their cycle currents to be equal; the erased current is definitionally zero. -/
theorem eraseCycleClassRealization_not_sourceCanonical_of_cycleClass_ne_zero
    (theory : SourceDeterminedHodgeTheory) (realization : Realization)
    (hcanonical : theory.Canonical realization) (p : ℕ)
    (cycleClass_ne_zero : (realization.cycleClass p).hom ≠ 0) :
    ¬ theory.Canonical (eraseCycleClassRealization realization) := by
  intro erasedCanonical
  unfold SourceDeterminedHodgeTheory.Canonical at hcanonical erasedCanonical
  change realization.semantics = theory.semantics realization.geometry at hcanonical
  change eraseCycleClass realization.semantics =
    theory.semantics realization.geometry at erasedCanonical
  have semantics_eq_erasure :
      realization.semantics = eraseCycleClass realization.semantics :=
    hcanonical.trans erasedCanonical.symm
  apply cycleClass_ne_zero
  change (realization.semantics.cycleClass p).hom = 0
  rw [semantics_eq_erasure]
  rfl

/-- [proved-derived; formal-checked] In the strengthened source theory the hypothesis above is
itself the nonvanishing of the geometric fundamental-class/Poincaré composite.  Thus erasure is
detected at the exact constituent passage; no independently named cycle map remains to audit. -/
theorem eraseCycleClassRealization_not_sourceCanonical_of_geometricComposite_ne_zero
    (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) (p : ℕ)
    (composite_ne_zero :
      ((theory.cyclePassage geometry).cycleClass p).hom ≠ 0) :
    ¬ theory.Canonical
      (eraseCycleClassRealization (theory.realization geometry)) := by
  have cycleClass_ne_zero :
      ((theory.realization geometry).cycleClass p).hom ≠ 0 := by
    change ((theory.cyclePassage geometry).cycleClass p).hom ≠ 0
    exact composite_ne_zero
  apply eraseCycleClassRealization_not_sourceCanonical_of_cycleClass_ne_zero
    theory (theory.realization geometry)
    (theory.canonical_realization geometry) p
  exact cycleClass_ne_zero

section Audit

#print axioms realization_hodge_receiver_is_derived
#print axioms rationalMiddle_eq_of_components_eq
#print axioms rationalMiddle_eq_top_iff
#print axioms eraseCycleClassRealization_algebraicSpan
#print axioms eraseCycleClassRealization_not_conclusion_of_nontrivial_middle
#print axioms not_theHodgeConjecture_allRealizations_of_nontrivial_middle
#print axioms cycleClassErasureRigid_of_hodgeConjecture
#print axioms eraseCycleClassRealization_not_sourceCanonical_of_cycleClass_ne_zero
#print axioms eraseCycleClassRealization_not_sourceCanonical_of_geometricComposite_ne_zero

end Audit

end Soma.Holonics.Millennium.HodgeSemanticsFaithfulness
