import ElementaryHolonics.Millennium.HolonicParametron

/-!
# The complex parametron is an oriented coupled-LC lattice before phase locking

**[proved-derived]** A finite oriented branch population presents its node variables through an
incidence map.  Diagonal capacitive or inverse-inductive storage is unchanged by a pure reversal
of branch coordinates.  A drive is unchanged only when its branch coordinates are transported
with the incidence, and mutual constitutive coefficients transform by the corresponding two-sided
sign action.  Hence winding orientation as a chart choice is distinct from changing a physical
drive or mutual coupling.

The resulting node response is a generalized `K v = omega^2 C v` mode relation.  The file retains
that distributed linear body before the nonlinear pump selects the two half-turn sheets proved in
`HolonicParametron`.  It proves no spectral completeness, damping law, Floquet reduction, or
hardware realization theorem.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.HolonicComplexParametron

open Soma.Holonics.Millennium.HolonicParametron

variable {Node Branch : Type*}

/-! ## Oriented incidence and branch storage -/

/-- The real voltage or flux drop presented by an oriented branch. -/
def branchDrop [Fintype Node]
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) (branch : Branch) : ℝ :=
  ∑ node, incidence branch node * state node

/-- The sign action which reverses the selected branch charts. -/
def orientationSign (selected : Branch → Bool) (branch : Branch) : ℝ :=
  if selected branch then -1 else 1

/-- Reversal of selected rows of the branch--node incidence map. -/
def reorientIncidence (selected : Branch → Bool) (incidence : Branch → Node → ℝ) :
    Branch → Node → ℝ :=
  fun branch node ↦ orientationSign selected branch * incidence branch node

/-- A branch sign is a unit of square one. -/
theorem orientationSign_sq (selected : Branch → Bool) (branch : Branch) :
    orientationSign selected branch ^ 2 = 1 := by
  simp only [orientationSign]
  split <;> norm_num

/-- An oriented branch reversal reverses exactly the returned branch drop. -/
theorem branchDrop_reorient [Fintype Node]
    (selected : Branch → Bool) (incidence : Branch → Node → ℝ)
    (state : Node → ℝ) (branch : Branch) :
    branchDrop (reorientIncidence selected incidence) state branch =
      orientationSign selected branch * branchDrop incidence state branch := by
  simp only [branchDrop, reorientIncidence]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro node hnode
  ring

/-- Energy stored independently on the branches.  A capacitance population uses its capacitance
as `weight`; an inductive stiffness population uses inverse inductance. -/
def diagonalStorage [Fintype Node] [Fintype Branch]
    (weight : Branch → ℝ) (incidence : Branch → Node → ℝ) (state : Node → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ branch, weight branch * branchDrop incidence state branch ^ 2

/-- Pure branch reorientation cannot change diagonal stored energy. -/
theorem diagonalStorage_reorient [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (weight : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) :
    diagonalStorage weight (reorientIncidence selected incidence) state =
      diagonalStorage weight incidence state := by
  unfold diagonalStorage
  congr 1
  apply Finset.sum_congr rfl
  intro branch hbranch
  rw [branchDrop_reorient]
  rw [mul_pow, orientationSign_sq, one_mul]

/-! ## Nodal response and the generalized LC mode -/

/-- The node response `B^T D B section` of a diagonal branch constitutive population. -/
def diagonalResponse [Fintype Node] [Fintype Branch]
    (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (state : Node → ℝ) (node : Node) : ℝ :=
  ∑ branch,
    weight branch * incidence branch node * branchDrop incidence state branch

/-- Both incidence occurrences change sign, so a diagonal nodal response is invariant under a
pure reversal of branch charts. -/
theorem diagonalResponse_reorient [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (weight : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) (node : Node) :
    diagonalResponse weight (reorientIncidence selected incidence) state node =
      diagonalResponse weight incidence state node := by
  unfold diagonalResponse
  apply Finset.sum_congr rfl
  intro branch hbranch
  rw [branchDrop_reorient]
  simp only [reorientIncidence]
  have hsign := orientationSign_sq selected branch
  calc
    weight branch * (orientationSign selected branch * incidence branch node) *
          (orientationSign selected branch * branchDrop incidence state branch) =
        orientationSign selected branch ^ 2 *
          (weight branch * incidence branch node * branchDrop incidence state branch) := by ring
    _ = weight branch * incidence branch node * branchDrop incidence state branch := by
      rw [hsign, one_mul]

/-- A generalized finite LC normal mode.  `stiffnessWeight` may be read as inverse inductance and
`capacityWeight` as capacitance. -/
def IsGeneralizedMode [Fintype Node] [Fintype Branch]
    (stiffnessWeight capacityWeight : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (omegaSq : ℝ) (mode : Node → ℝ) : Prop :=
  mode ≠ 0 ∧ ∀ node,
    diagonalResponse stiffnessWeight incidence mode node =
      omegaSq * diagonalResponse capacityWeight incidence mode node

/-- A pure change of branch orientation preserves every generalized LC mode. -/
theorem isGeneralizedMode_reorient_iff [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (stiffnessWeight capacityWeight : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (omegaSq : ℝ) (mode : Node → ℝ) :
    IsGeneralizedMode stiffnessWeight capacityWeight
        (reorientIncidence selected incidence) omegaSq mode ↔
      IsGeneralizedMode stiffnessWeight capacityWeight incidence omegaSq mode := by
  constructor <;> rintro ⟨hnonzero, hmode⟩ <;> refine ⟨hnonzero, ?_⟩
  · intro node
    simpa only [diagonalResponse_reorient] using hmode node
  · intro node
    simpa only [diagonalResponse_reorient] using hmode node

/-! ## Drive orientation is a transported coordinate, not an erased sign -/

/-- The work pairing between an addressed branch drive and the branch drops. -/
def driveAction [Fintype Node] [Fintype Branch]
    (drive : Branch → ℝ) (incidence : Branch → Node → ℝ) (state : Node → ℝ) : ℝ :=
  ∑ branch, drive branch * branchDrop incidence state branch

/-- Transport a drive covector through the same branch reversal. -/
def reorientDrive (selected : Branch → Bool) (drive : Branch → ℝ) : Branch → ℝ :=
  fun branch ↦ orientationSign selected branch * drive branch

/-- Reversing incidence alone is visible as the corresponding reversal of the drive coordinates. -/
theorem driveAction_reorientIncidence [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (drive : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) :
    driveAction drive (reorientIncidence selected incidence) state =
      driveAction (reorientDrive selected drive) incidence state := by
  unfold driveAction reorientDrive
  apply Finset.sum_congr rfl
  intro branch hbranch
  rw [branchDrop_reorient]
  ring

/-- When the drive and incidence charts travel together, their physical work pairing is
unchanged. -/
theorem driveAction_reorientBoth [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (drive : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) :
    driveAction (reorientDrive selected drive)
        (reorientIncidence selected incidence) state =
      driveAction drive incidence state := by
  unfold driveAction reorientDrive
  apply Finset.sum_congr rfl
  intro branch hbranch
  rw [branchDrop_reorient]
  have hsign := orientationSign_sq selected branch
  calc
    orientationSign selected branch * drive branch *
          (orientationSign selected branch * branchDrop incidence state branch) =
        orientationSign selected branch ^ 2 *
          (drive branch * branchDrop incidence state branch) := by ring
    _ = drive branch * branchDrop incidence state branch := by rw [hsign, one_mul]

/-! ## Mutual capacitance and inductance carry two orientation indices -/

/-- The two-sided sign transport of a mutual constitutive table.  This is the coordinate form of
`S M S`, where `S` is the diagonal branch-orientation action. -/
def reorientCoupling (selected : Branch → Bool) (coupling : Branch → Branch → ℝ) :
    Branch → Branch → ℝ :=
  fun first second ↦
    orientationSign selected first * coupling first second * orientationSign selected second

/-- The node response `B^T M B section` of a general mutual branch coupling. -/
def coupledResponse [Fintype Node] [Fintype Branch]
    (coupling : Branch → Branch → ℝ) (incidence : Branch → Node → ℝ)
    (state : Node → ℝ) (node : Node) : ℝ :=
  ∑ first, incidence first node *
    ∑ second, coupling first second * branchDrop incidence state second

/-- A mutual response is invariant precisely when the two-index constitutive table is transported
with both reoriented branch charts. -/
theorem coupledResponse_reorient [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (coupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) (node : Node) :
    coupledResponse (reorientCoupling selected coupling)
        (reorientIncidence selected incidence) state node =
      coupledResponse coupling incidence state node := by
  unfold coupledResponse
  apply Finset.sum_congr rfl
  intro first hfirst
  simp only [reorientIncidence, reorientCoupling]
  rw [show
      (∑ second,
          (orientationSign selected first * coupling first second *
              orientationSign selected second) *
            branchDrop (reorientIncidence selected incidence) state second) =
        orientationSign selected first *
          ∑ second, coupling first second * branchDrop incidence state second by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro second hsecond
      rw [branchDrop_reorient]
      have hsign := orientationSign_sq selected second
      calc
        orientationSign selected first * coupling first second *
              orientationSign selected second *
              (orientationSign selected second * branchDrop incidence state second) =
            orientationSign selected first *
              (orientationSign selected second ^ 2 *
                (coupling first second * branchDrop incidence state second)) := by ring
        _ = orientationSign selected first *
              (coupling first second * branchDrop incidence state second) := by
          rw [hsign, one_mul]]
  have hsign := orientationSign_sq selected first
  calc
    orientationSign selected first * incidence first node *
          (orientationSign selected first *
            ∑ second, coupling first second * branchDrop incidence state second) =
        orientationSign selected first ^ 2 *
          (incidence first node *
            ∑ second, coupling first second * branchDrop incidence state second) := by ring
    _ = incidence first node *
          ∑ second, coupling first second * branchDrop incidence state second := by
      rw [hsign, one_mul]

/-- If incidence is reversed while the constitutive table is held fixed, the returned response is
the response of the two-sided sign-changed coupling in the original chart.  This is the exact
distinction between a coordinated chart transport and a physical winding/coupling intervention. -/
theorem coupledResponse_reorientIncidence [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (coupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) (node : Node) :
    coupledResponse coupling (reorientIncidence selected incidence) state node =
      coupledResponse (reorientCoupling selected coupling) incidence state node := by
  unfold coupledResponse
  apply Finset.sum_congr rfl
  intro first hfirst
  simp only [reorientIncidence, reorientCoupling]
  rw [show
      (∑ second, coupling first second *
          branchDrop (reorientIncidence selected incidence) state second) =
        ∑ second, coupling first second * orientationSign selected second *
          branchDrop incidence state second by
      apply Finset.sum_congr rfl
      intro second hsecond
      rw [branchDrop_reorient]
      ring]
  rw [show
      (∑ second, orientationSign selected first * coupling first second *
          orientationSign selected second * branchDrop incidence state second) =
        orientationSign selected first *
          ∑ second, coupling first second * orientationSign selected second *
            branchDrop incidence state second by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro second hsecond
      ring]
  ring

/-- A generalized mode with full mutual capacitance and inverse-inductance tables. -/
def IsCoupledGeneralizedMode [Fintype Node] [Fintype Branch]
    (stiffness capacity : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (omegaSq : ℝ) (mode : Node → ℝ) : Prop :=
  mode ≠ 0 ∧ ∀ node,
    coupledResponse stiffness incidence mode node =
      omegaSq * coupledResponse capacity incidence mode node

/-- The full mutual generalized eigenproblem is covariant under simultaneous two-sided transport
of its constitutive tables and incidence charts. -/
theorem isCoupledGeneralizedMode_reorient_iff [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (stiffness capacity : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (omegaSq : ℝ) (mode : Node → ℝ) :
    IsCoupledGeneralizedMode (reorientCoupling selected stiffness)
        (reorientCoupling selected capacity) (reorientIncidence selected incidence) omegaSq mode ↔
      IsCoupledGeneralizedMode stiffness capacity incidence omegaSq mode := by
  constructor <;> rintro ⟨hnonzero, hmode⟩ <;> refine ⟨hnonzero, ?_⟩
  · intro node
    simpa only [coupledResponse_reorient] using hmode node
  · intro node
    simpa only [coupledResponse_reorient] using hmode node

/-- The mutual quadratic storage before any phase-locking receiver. -/
def coupledStorage [Fintype Node] [Fintype Branch]
    (coupling : Branch → Branch → ℝ) (incidence : Branch → Node → ℝ)
    (state : Node → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ first, ∑ second,
    coupling first second * branchDrop incidence state first *
      branchDrop incidence state second

/-- Two-sided transport of a mutual table preserves the complete mutual storage. -/
theorem coupledStorage_reorient [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (coupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) :
    coupledStorage (reorientCoupling selected coupling)
        (reorientIncidence selected incidence) state =
      coupledStorage coupling incidence state := by
  unfold coupledStorage
  congr 1
  apply Finset.sum_congr rfl
  intro first hfirst
  apply Finset.sum_congr rfl
  intro second hsecond
  simp only [reorientCoupling]
  rw [branchDrop_reorient, branchDrop_reorient]
  have hfirstSign := orientationSign_sq selected first
  have hsecondSign := orientationSign_sq selected second
  calc
    orientationSign selected first * coupling first second * orientationSign selected second *
          (orientationSign selected first * branchDrop incidence state first) *
          (orientationSign selected second * branchDrop incidence state second) =
        orientationSign selected first ^ 2 * orientationSign selected second ^ 2 *
          (coupling first second * branchDrop incidence state first *
            branchDrop incidence state second) := by ring
    _ = coupling first second * branchDrop incidence state first *
          branchDrop incidence state second := by
      rw [hfirstSign, hsecondSign]
      ring

/-- Holding a mutual table fixed while reversing physical incidence changes exactly the
off-diagonal orientation signs described by `reorientCoupling`. -/
theorem coupledStorage_reorientIncidence [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool) (coupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state : Node → ℝ) :
    coupledStorage coupling (reorientIncidence selected incidence) state =
      coupledStorage (reorientCoupling selected coupling) incidence state := by
  unfold coupledStorage
  congr 1
  apply Finset.sum_congr rfl
  intro first hfirst
  apply Finset.sum_congr rfl
  intro second hsecond
  simp only [reorientCoupling]
  rw [branchDrop_reorient, branchDrop_reorient]
  ring

/-! ## Complex phase drives before the binary receiver -/

/-- A real incidence map presenting a complex phasor section on its branches. -/
def complexBranchDrop [Fintype Node]
    (incidence : Branch → Node → ℝ) (state : Node → ℂ) (branch : Branch) : ℂ :=
  ∑ node, (incidence branch node : ℂ) * state node

/-- The complex receiver of a branch-drive population. -/
def complexDriveAction [Fintype Node] [Fintype Branch]
    (drive : Branch → ℂ) (incidence : Branch → Node → ℝ) (state : Node → ℂ) : ℂ :=
  ∑ branch, drive branch * complexBranchDrop incidence state branch

/-- The phase-labelled complex drive carried by each branch. -/
def phaseDrive (amplitude phase : Branch → ℝ) (branch : Branch) : ℂ :=
  (amplitude branch : ℂ) * phaseCarrier (phase branch)

/-- A half-turn reverses a branch's complex drive exactly. -/
theorem phaseDrive_halfTurn (amplitude phase : Branch → ℝ) (branch : Branch) :
    phaseDrive amplitude (fun index ↦ halfTurnSheet (phase index)) branch =
      -phaseDrive amplitude phase branch := by
  simp only [phaseDrive, phaseCarrier_halfTurnSheet]
  ring

/-- A complex drive may retain arbitrary relative phases before the two-sheet receiver is taken. -/
def phaseSuperposition [Fintype Branch] (amplitude phase : Branch → ℝ) : ℂ :=
  ∑ branch, phaseDrive amplitude phase branch

/-- A common half-turn negates the complete complex superposition. -/
theorem phaseSuperposition_halfTurn [Fintype Branch]
    (amplitude phase : Branch → ℝ) :
    phaseSuperposition amplitude (fun index ↦ halfTurnSheet (phase index)) =
      -phaseSuperposition amplitude phase := by
  unfold phaseSuperposition
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro branch hbranch
  exact phaseDrive_halfTurn amplitude phase branch

end Soma.Holonics.Millennium.HolonicComplexParametron

#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.diagonalStorage_reorient
#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.isGeneralizedMode_reorient_iff
#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.driveAction_reorientBoth
#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.coupledResponse_reorient
#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.isCoupledGeneralizedMode_reorient_iff
#print axioms Soma.Holonics.Millennium.HolonicComplexParametron.phaseSuperposition_halfTurn
