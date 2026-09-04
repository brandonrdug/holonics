import ElementaryHolonics.Millennium.HolonicGranularBoundaryRadiation
import ElementaryHolonics.Millennium.LineageCompression
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The quadratic receiver factors through one exact moment field

**[proved-derived]** A finite family of local current sections need not be materialized after the
declared future receiver has been fixed. Every bilinear constitutive, generator-action, or receiver
pairing of that family factors through its exact weighted second moment. The source family remains
the reconstruction fibre; equality of moments identifies it only for receivers which themselves
factor through the contraction below.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicQuadraticMomentCondensation

open scoped BigOperators

variable {Scalar Support Cell : Type*}
  [CommRing Scalar] [Fintype Support] [Fintype Cell]

/-- The exact weighted second moment of a finite current family. -/
def quadraticMoment
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    Matrix Cell Cell Scalar :=
  fun left right => ∑ support, weight support * current support left * current support right

/-- Contract a moment field with one declared bilinear receiver. -/
def contractMoment
    (receiver moment : Matrix Cell Cell Scalar) : Scalar :=
  ∑ left, ∑ right, receiver left right * moment left right

/-- The corresponding support-by-support receiver before moment condensation. -/
def enumerateQuadraticReceiver
    (receiver : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) : Scalar :=
  ∑ support, weight support *
    (∑ left, ∑ right, receiver left right * current support left * current support right)

/-- Every finite quadratic receiver is exactly a contraction of the second-moment field. -/
theorem contract_quadraticMoment_eq_enumerateQuadraticReceiver
    (receiver : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    contractMoment receiver (quadraticMoment weight current) =
      enumerateQuadraticReceiver receiver weight current := by
  simp only [contractMoment, quadraticMoment, enumerateQuadraticReceiver]
  simp_rw [Finset.mul_sum]
  calc
    (∑ left, ∑ right, ∑ support,
        receiver left right * (weight support * current support left * current support right)) =
        ∑ left, ∑ support, ∑ right,
          receiver left right * (weight support * current support left * current support right) := by
      apply Finset.sum_congr rfl
      intro left _
      rw [Finset.sum_comm]
    _ = ∑ support, ∑ left, ∑ right,
          receiver left right * (weight support * current support left * current support right) := by
      rw [Finset.sum_comm]
    _ = ∑ support, ∑ left, ∑ right,
          weight support * (receiver left right * current support left * current support right) := by
      apply Finset.sum_congr rfl
      intro support _
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      ring

/-- Equal moment fields are indistinguishable to every receiver which factors through a moment
contraction. The source families are not identified by this theorem. -/
theorem equal_quadraticMoment_forces_equal_contractedReceiver
    {leftWeight rightWeight : Support → Scalar}
    {leftCurrent rightCurrent : Support → Cell → Scalar}
    (equalMoment : quadraticMoment leftWeight leftCurrent =
      quadraticMoment rightWeight rightCurrent)
    (receiver : Matrix Cell Cell Scalar) :
    enumerateQuadraticReceiver receiver leftWeight leftCurrent =
      enumerateQuadraticReceiver receiver rightWeight rightCurrent := by
  rw [← contract_quadraticMoment_eq_enumerateQuadraticReceiver,
    ← contract_quadraticMoment_eq_enumerateQuadraticReceiver, equalMoment]

/-! ## Receiver forms remain factored -/

/-- One receiver functional acting on one current section. -/
def linearReading (functional current : Cell → Scalar) : Scalar :=
  ∑ cell, functional cell * current cell

/-- A bilinear receiver presented by two functionals.  This is a construction chart for the form,
not a requirement to materialize its ambient matrix in an implementation. -/
def rankOneReceiver (left right : Cell → Scalar) : Matrix Cell Cell Scalar :=
  fun leftCell rightCell => left leftCell * right rightCell

/-- Direct contraction of one factored receiver against the retained rank-one source family. -/
def enumerateRankOneReceiver
    (left right : Cell → Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) : Scalar :=
  ∑ support, weight support *
    linearReading left (current support) * linearReading right (current support)

/-- A rank-one receiver acts directly through its two functional readings.  The ambient receiver
matrix is therefore an equality witness, not an executable storage obligation. -/
theorem contract_rankOneReceiver_quadraticMoment_eq_enumerate
    (left right : Cell → Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    contractMoment (rankOneReceiver left right) (quadraticMoment weight current) =
      enumerateRankOneReceiver left right weight current := by
  rw [contract_quadraticMoment_eq_enumerateQuadraticReceiver]
  simp only [enumerateQuadraticReceiver, enumerateRankOneReceiver, rankOneReceiver, linearReading]
  apply Finset.sum_congr rfl
  intro support _
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro leftCell _
  apply Finset.sum_congr rfl
  intro rightCell _
  ring

/-! ## Exterior restriction descends after the native moment -/

/-- Restrict both legs of a moment by one exterior boundary current. -/
def restrictMoment
    (restriction : Cell → Scalar) (moment : Matrix Cell Cell Scalar) :
    Matrix Cell Cell Scalar :=
  fun left right => restriction left * moment left right * restriction right

/-- The exact boundary moment obtained by integrating a plural restriction family. -/
def sumRestrictedMoments {Boundary : Type*} [Fintype Boundary]
    (restriction : Boundary → Cell → Scalar) (moment : Matrix Cell Cell Scalar) :
    Matrix Cell Cell Scalar :=
  fun left right => ∑ boundary, restrictMoment (restriction boundary) moment left right

/-- Direct support-by-restriction enumeration of the same boundary moment. -/
def enumerateRestrictedQuadraticMoment {Boundary : Type*} [Fintype Boundary]
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (restriction : Boundary → Cell → Scalar) : Matrix Cell Cell Scalar :=
  fun left right => ∑ boundary, ∑ support,
    weight support *
      (restriction boundary left * current support left) *
      (restriction boundary right * current support right)

omit [Fintype Cell] in
/-- Restriction and native-moment formation interchange exactly. Thus the native covariance may
remain hot while the complete exterior restriction family stays in its reconstruction fibre. -/
theorem sumRestrictedMoments_quadraticMoment_eq_enumerate
    {Boundary : Type*} [Fintype Boundary]
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (restriction : Boundary → Cell → Scalar) :
    sumRestrictedMoments restriction (quadraticMoment weight current) =
      enumerateRestrictedQuadraticMoment weight current restriction := by
  ext left right
  simp only [sumRestrictedMoments, restrictMoment, quadraticMoment,
    enumerateRestrictedQuadraticMoment]
  apply Finset.sum_congr rfl
  intro boundary _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro support _
  ring

/-- A linear generator transports the moment by acting on both tensor legs. -/
def transportMoment
    (generator moment : Matrix Cell Cell Scalar) : Matrix Cell Cell Scalar :=
  generator * moment * generator.transpose

/-- The second moment of every generated section is exactly the two-leg transport of the entering
moment. This is the quadratic analogue of `q T_i = U_i q`. -/
theorem quadraticMoment_generated_eq_transportMoment
    (generator : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    quadraticMoment weight (fun support => generator.mulVec (current support)) =
      transportMoment generator (quadraticMoment weight current) := by
  ext left right
  simp only [quadraticMoment, transportMoment, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ rightSource, ∑ support, ∑ leftSource,
          weight support * (generator left leftSource * current support leftSource) *
            (generator right rightSource * current support rightSource) := by
      rw [Finset.sum_comm]
    _ = ∑ rightSource, ∑ leftSource, ∑ support,
          weight support * (generator left leftSource * current support leftSource) *
            (generator right rightSource * current support rightSource) := by
      apply Finset.sum_congr rfl
      intro rightSource _
      rw [Finset.sum_comm]
    _ = ∑ rightSource, ∑ leftSource, ∑ support,
          generator left leftSource *
            (weight support * current support leftSource * current support rightSource) *
              generator right rightSource := by
      apply Finset.sum_congr rfl
      intro rightSource _
      apply Finset.sum_congr rfl
      intro leftSource _
      apply Finset.sum_congr rfl
      intro support _
      ring

/-! ## Plural generator faces remain a direct sum -/

variable {Generator : Type*} [Fintype Generator]

/-- A plural generator front carries one separately transported moment for every addressed
generator.  It is not the moment of a prematurely added current, which would introduce unlicensed
cross-generator terms. -/
def directSumGeneratedMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    Matrix Cell Cell Scalar :=
  ∑ generatorFace, quadraticMoment weight
    (fun support => (generator generatorFace).mulVec (current support))

/-- Every plural addressed face transports the entering moment on its own two tensor legs; the
plural return is their exact sum.  Reconvergence may occur after this passage, never before it. -/
theorem directSumGeneratedMoment_eq_sum_transportMoment
    (generator : Generator → Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    directSumGeneratedMoment generator weight current =
      ∑ generatorFace, transportMoment (generator generatorFace)
        (quadraticMoment weight current) := by
  apply Finset.sum_congr rfl
  intro generatorFace _
  exact quadraticMoment_generated_eq_transportMoment
    (generator generatorFace) weight current

/-! ## A projective current front descends without founding its transitive ray atlas -/

/-- When several transported source rays meet one primitive target ray, their exact quadratic
weights add after each removed projective scale is squared.  This is a dependent target frame: its
population belongs to the current front and need not equal the preceding population. -/
def descendedProjectiveWeight {Target : Type*} [DecidableEq Target]
    (target : Support → Target) (weight scale : Support → Scalar) : Target → Scalar :=
  fun targetRay => ∑ source,
    if target source = targetRay
    then weight source * scale source * scale source
    else 0

/-- Exact projective normalization and equal-ray condensation commute with one quadratic moment
transport.  The source rays and removed scales remain the reconstruction fibre; only the target
rays and their summed weights continue. -/
theorem transportMoment_eq_quadraticMoment_descendedProjectiveWeight
    {Target : Type*} [Fintype Target] [DecidableEq Target]
    (generator : Matrix Cell Cell Scalar)
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (target : Support → Target) (scale : Support → Scalar)
    (targetCurrent : Target → Cell → Scalar)
    (transported : ∀ source,
      generator.mulVec (current source) =
        fun cell => scale source * targetCurrent (target source) cell) :
    transportMoment generator (quadraticMoment weight current) =
      quadraticMoment (descendedProjectiveWeight target weight scale) targetCurrent := by
  rw [← quadraticMoment_generated_eq_transportMoment]
  ext left right
  simp only [quadraticMoment, descendedProjectiveWeight, transported]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.sum_eq_single (target source)]
  · simp only [if_pos]
    ring
  · intro targetRay _ different
    simp [different.symm]
  · simp

/-! ## The hot moment is an incidence frame with a constitutive form -/

variable {Rank RebasedRank : Type*} [Fintype Rank] [Fintype RebasedRank]

/-- A quadratic moment carried without an ambient `Cell × Cell` population.  `frame` is the
addressed incidence from a derived image population into the native cells; `constitutive` is the
receiver form on that image.  The ambient covariance is only the exterior reconstruction chart
displayed by this definition. -/
def lowRankMoment
    (frame : Matrix Rank Cell Scalar) (constitutive : Matrix Rank Rank Scalar) :
    Matrix Cell Cell Scalar :=
  frame.transpose * constitutive * frame

/-- A native generator acts on the cell leg of the incidence frame.  The constitutive form stays
on the derived image population, so no ambient covariance and no source rank-one family has to be
rescanned. -/
theorem transportMoment_lowRankMoment
    (generator : Matrix Cell Cell Scalar)
    (frame : Matrix Rank Cell Scalar) (constitutive : Matrix Rank Rank Scalar) :
    transportMoment generator (lowRankMoment frame constitutive) =
      lowRankMoment (frame * generator.transpose) constitutive := by
  simp only [transportMoment, lowRankMoment, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

omit [Fintype Cell] in
/-- Exact rank refactorization is a change of image coordinates, not a loss.  If the old frame
factors through a newly derived frame, pulling the constitutive form through the same addressed
map preserves the complete quadratic moment.  This is the algebraic heart of dynamic
compactification after a plural generator front. -/
theorem lowRankMoment_refactor
    (oldFrame : Matrix Rank Cell Scalar)
    (newFrame : Matrix RebasedRank Cell Scalar)
    (coordinates : Matrix Rank RebasedRank Scalar)
    (constitutive : Matrix Rank Rank Scalar)
    (factorization : oldFrame = coordinates * newFrame) :
    lowRankMoment oldFrame constitutive =
      lowRankMoment newFrame
        (coordinates.transpose * constitutive * coordinates) := by
  rw [factorization]
  simp only [lowRankMoment, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Transport and exact image refactorization commute.  This is the one-step generator square
needed by a resident dynamic moment passage: first move the incidence through the generator, then
derive its actual image and pull the constitutive form onto that image. -/
theorem transportMoment_lowRankMoment_refactor
    (generator : Matrix Cell Cell Scalar)
    (frame : Matrix Rank Cell Scalar)
    (rebasedFrame : Matrix RebasedRank Cell Scalar)
    (coordinates : Matrix Rank RebasedRank Scalar)
    (constitutive : Matrix Rank Rank Scalar)
    (factorization : frame * generator.transpose = coordinates * rebasedFrame) :
    transportMoment generator (lowRankMoment frame constitutive) =
      lowRankMoment rebasedFrame
        (coordinates.transpose * constitutive * coordinates) := by
  rw [transportMoment_lowRankMoment]
  exact lowRankMoment_refactor _ _ _ _ factorization

/-! ## The descended square acts through every ordered successor word -/

/-- Apply an ordered generator word to one current section. -/
def generateCurrentWord
    (generators : List (Matrix Cell Cell Scalar)) (current : Cell → Scalar) : Cell → Scalar :=
  match generators with
  | [] => current
  | generator :: later => generateCurrentWord later (generator.mulVec current)

/-- Apply the corresponding two-leg transport word to one moment section. -/
def transportMomentWord
    (generators : List (Matrix Cell Cell Scalar)) (moment : Matrix Cell Cell Scalar) :
    Matrix Cell Cell Scalar :=
  match generators with
  | [] => moment
  | generator :: later => transportMomentWord later (transportMoment generator moment)

/-- The one-generator square carries the complete quadratic factorization through every finite
ordered successor word. No enumerated campaign is needed to preserve later bilinear receivers. -/
theorem quadraticMoment_generatedWord_eq_transportMomentWord
    (generators : List (Matrix Cell Cell Scalar))
    (weight : Support → Scalar) (current : Support → Cell → Scalar) :
    quadraticMoment weight (fun support => generateCurrentWord generators (current support)) =
      transportMomentWord generators (quadraticMoment weight current) := by
  induction generators generalizing current with
  | nil => rfl
  | cons generator later induction =>
      rw [show (fun support => generateCurrentWord (generator :: later) (current support)) =
          fun support => generateCurrentWord later (generator.mulVec (current support)) by rfl]
      rw [induction]
      rw [quadraticMoment_generated_eq_transportMoment]
      rfl

/-! ## The observable moment is a receiver-history quotient -/

/-- Pull a quadratic receiver backward through one generator. -/
def pullbackReceiver
    (generator receiver : Matrix Cell Cell Scalar) : Matrix Cell Cell Scalar :=
  generator.transpose * receiver * generator

/-- Pull one functional backward through a generator without constructing a bilinear matrix. -/
def pullbackFunctional
    (generator : Matrix Cell Cell Scalar) (functional : Cell → Scalar) : Cell → Scalar :=
  generator.transpose.mulVec functional

/-- Backward transport preserves the rank-one factorization exactly.  Non-injective generators
remain lawful: their complete preimage current is accumulated by `mulVec`. -/
theorem pullbackReceiver_rankOneReceiver
    (generator : Matrix Cell Cell Scalar) (left right : Cell → Scalar) :
    pullbackReceiver generator (rankOneReceiver left right) =
      rankOneReceiver (pullbackFunctional generator left)
        (pullbackFunctional generator right) := by
  ext leftCell rightCell
  simp only [pullbackReceiver, rankOneReceiver, pullbackFunctional, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rightTarget _
  apply Finset.sum_congr rfl
  intro leftTarget _
  ring

/-- The contraction spelling is exactly the trace pairing. -/
theorem contractMoment_eq_trace (receiver moment : Matrix Cell Cell Scalar) :
    contractMoment receiver moment = Matrix.trace (receiver.transpose * moment) := by
  simp only [contractMoment, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Two-leg moment transport is adjoint to pulling the receiver backward. -/
theorem contract_transportMoment_eq_contract_pullbackReceiver
    (generator receiver moment : Matrix Cell Cell Scalar) :
    contractMoment receiver (transportMoment generator moment) =
      contractMoment (pullbackReceiver generator receiver) moment := by
  rw [contractMoment_eq_trace, contractMoment_eq_trace]
  simp only [transportMoment, pullbackReceiver, Matrix.transpose_mul]
  calc
    Matrix.trace (receiver.transpose * (generator * moment * generator.transpose)) =
        Matrix.trace ((receiver.transpose * generator) * moment * generator.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (generator.transpose * (receiver.transpose * generator) * moment) :=
      Matrix.trace_mul_cycle (receiver.transpose * generator) moment generator.transpose
    _ = Matrix.trace
        ((generator.transpose * (receiver.transpose * generator.transpose.transpose)) * moment) := by
      simp only [Matrix.transpose_transpose]

/-- The complete coordinate section returned by one founded receiver family. -/
def observableMoment {Receiver : Type*}
    (receiverForm : Receiver → Matrix Cell Cell Scalar)
    (moment : Matrix Cell Cell Scalar) : Receiver → Scalar :=
  fun receiver => contractMoment (receiverForm receiver) moment

/-- Descended generator transport on observable coordinates is backward receiver action. -/
def observableTransport {Generator Receiver : Type*}
    (backwardReceiver : Generator → Receiver → Receiver)
    (generator : Generator) (coordinates : Receiver → Scalar) : Receiver → Scalar :=
  fun receiver => coordinates (backwardReceiver generator receiver)

/-- A receiver family closed under exact backward generator action gives a lawful
receiver-history compression of the whole covariance field. The quotient owns only observable
coordinates; the full moment and its rank-one presentation remain the reconstruction fibre. -/
def observableMomentReceiverHistoryCompression
    {Generator Receiver : Type*}
    (generatorMatrix : Generator → Matrix Cell Cell Scalar)
    (receiverForm : Receiver → Matrix Cell Cell Scalar)
    (backwardReceiver : Generator → Receiver → Receiver)
    (backwardExact : ∀ generator receiver,
      receiverForm (backwardReceiver generator receiver) =
        pullbackReceiver (generatorMatrix generator) (receiverForm receiver)) :
    LineageCompression.ReceiverHistoryCompression
      Generator Receiver (Matrix Cell Cell Scalar) (Receiver → Scalar) Scalar where
  present :=
    { quotient := observableMoment receiverForm
      receiver := fun receiver moment => contractMoment (receiverForm receiver) moment
      factor := fun receiver coordinates => coordinates receiver
      exact := fun _ _ => rfl }
  sourceTransport := fun generator moment => transportMoment (generatorMatrix generator) moment
  quotientTransport := observableTransport backwardReceiver
  generatorExact := by
    intro generator moment
    funext receiver
    simp only [observableMoment, observableTransport]
    rw [contract_transportMoment_eq_contract_pullbackReceiver]
    rw [backwardExact]

section Audit

#print axioms contract_quadraticMoment_eq_enumerateQuadraticReceiver
#print axioms equal_quadraticMoment_forces_equal_contractedReceiver
#print axioms contract_rankOneReceiver_quadraticMoment_eq_enumerate
#print axioms pullbackReceiver_rankOneReceiver
#print axioms sumRestrictedMoments_quadraticMoment_eq_enumerate
#print axioms quadraticMoment_generated_eq_transportMoment
#print axioms directSumGeneratedMoment_eq_sum_transportMoment
#print axioms transportMoment_eq_quadraticMoment_descendedProjectiveWeight
#print axioms transportMoment_lowRankMoment
#print axioms lowRankMoment_refactor
#print axioms transportMoment_lowRankMoment_refactor
#print axioms quadraticMoment_generatedWord_eq_transportMomentWord
#print axioms contract_transportMoment_eq_contract_pullbackReceiver
#print axioms observableMomentReceiverHistoryCompression

end Audit

end Soma.Holonics.Millennium.HolonicQuadraticMomentCondensation
