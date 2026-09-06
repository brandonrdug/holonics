import ElementaryHolonics.Computation.HolonicDiffusionCharts
import ElementaryHolonics.Computation.HolonicRecurrentEcology
import ElementaryHolonics.Computation.HolonicInformationTheory
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Oriented port current between realization sites

**[proved-derived]** A coherent exterior recurrence needs more than a port reading at each site.
It needs an addressed current from a source site to a target site.  This file gives that current
the same owner as every other holonic neural step: one finite local-current ecology.

`depart p` carries a source site into an oriented incidence carrier under exterior port `p`;
`arrive` carries that incidence into a target site.  Their composition is the port-indexed
transport `A_p(z,z')`.  The pair current retains both endpoints before aggregation, the returned
site current sums only the source endpoint, and the exterior port current is the later sum over
targets.  Consequently a port projection can never substitute for the continuing site section.

No string, token, language, architecture, or apparatus coordinate occurs in the construction.
An implementation may realize `Site` as an oriented face--cell incidence carrying an additional
local boundary state; that is a chart of this object, not a new inference law.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicOrientedSiteTransport

open scoped BigOperators
open Soma.Holonics.Computation.HolonicNeuralEcology
open Soma.Holonics.Computation.HolonicDiffusionCharts

universe uS uI uP uK uF

/-- A port-indexed oriented incidence factorization.  `depart` and `arrive` are deliberately
distinct: replacing them by one unsigned incidence would erase endpoint orientation. -/
structure OrientedPortSiteTransport
    (Scalar : Type uK) (Site : Type uS) (Incidence : Type uI) (Port : Type uP)
    [CommSemiring Scalar] [Fintype Site] [Fintype Incidence] where
  depart : Port → Matrix Incidence Site Scalar
  arrive : Matrix Site Incidence Scalar

namespace OrientedPortSiteTransport

variable
    {Scalar : Type uK} {Site : Type uS} {Incidence : Type uI} {Port : Type uP}
    [CommSemiring Scalar] [Fintype Site] [Fintype Incidence]
    (T : OrientedPortSiteTransport Scalar Site Incidence Port)

/-- The complete oriented port law `A_p(target, source)`. -/
def localTransport (port : Port) : Matrix Site Site Scalar :=
  T.arrive * T.depart port

/-- Current on one addressed source--target pair before either endpoint is forgotten. -/
def pairCurrent (port : Port) (state : Site → Scalar)
    (target source : Site) : Scalar :=
  state source * T.localTransport port target source

/-- Continuing current at one target after the complete source junction. -/
def returnedSiteCurrent (port : Port) (state : Site → Scalar)
    (target : Site) : Scalar :=
  ∑ source : Site, T.pairCurrent port state target source

/-- Exterior port current is a later receiver projection of the complete target section. -/
def portCurrent (port : Port) (state : Site → Scalar) : Scalar :=
  ∑ target : Site, T.returnedSiteCurrent port state target

/-- The complete port-potential section is the exterior receiver shadow before any one port is
realized.  It is retained as a family, rather than silently converted into one selected state. -/
def portPotentialSection (state : Site → Scalar) : Port → Scalar :=
  fun port ↦ T.portCurrent port state

/-- The complete counterfactual target section before one exterior interaction is enacted.  Its
port index is orientation, not an axis to be summed away. -/
def returnedSiteSection (state : Site → Scalar) : Port → Site → Scalar :=
  fun port ↦ T.returnedSiteCurrent port state

/-- The pair-current fibre reconstructs every returned target coordinate exactly. -/
theorem returnedSiteCurrent_eq_sum_pairCurrent (port : Port) (state : Site → Scalar)
    (target : Site) :
    T.returnedSiteCurrent port state target =
      ∑ source : Site, T.pairCurrent port state target source := rfl

/-- The exterior port face is exactly the sum of the continuing target section; it is not that
section and no inverse is asserted. -/
theorem portCurrent_eq_sum_returnedSiteCurrent (port : Port) (state : Site → Scalar) :
    T.portCurrent port state =
      ∑ target : Site, T.returnedSiteCurrent port state target := rfl

/-- Every member of the complete section reconstructs from its pair-current fibre. -/
theorem returnedSiteSection_apply (state : Site → Scalar) (port : Port) (target : Site) :
    T.returnedSiteSection state port target =
      ∑ source : Site, T.pairCurrent port state target source := rfl

/-- Expand one local coefficient through the two distinctly oriented incidence maps. -/
theorem localTransport_apply (port : Port) (target source : Site) :
    T.localTransport port target source =
      ∑ incidence : Incidence,
        T.arrive target incidence * T.depart port incidence source := rfl

/-- This transport is one ordinary holonic neural ecology.  The constitutive reaction is the
identity because every nontrivial coefficient already lives in the oriented local current. -/
def ecology :
    FiniteLocalCurrentEcology Site Scalar
      (OrientedPortSiteTransport Scalar Site Incidence Port) Port Unit (Site → Scalar) where
  localCurrent morphology port state target source :=
    morphology.pairCurrent port state target source
  reaction _ _ _ current := current
  observe _ state := state

/-- HNN aggregation is precisely the oriented returned-site current. -/
theorem ecology_step_eq_returnedSiteCurrent (port : Port) (state : Site → Scalar) :
    (ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).step
        T port state =
      T.returnedSiteCurrent port state := by
  funext target
  rfl

/-- Enacting one exterior orientation continues with that member of the retained section.  The
other members remain reconstruction fibre; summing mutually exclusive ports would be a separate
receiver quotient and is not this state transition. -/
theorem ecology_step_eq_returnedSiteSection (port : Port) (state : Site → Scalar) :
    (ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).step
        T port state = T.returnedSiteSection state port :=
  ecology_step_eq_returnedSiteCurrent T port state

/-- Every ordered exterior history therefore uses the standing HNN recurrence rather than a
separate surface algorithm. -/
theorem ecology_inferWord_append (left right : List Port) (state : Site → Scalar) :
    (ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).inferWord
        T (left ++ right) state =
      (ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).inferWord
        T left
        ((ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).inferWord
          T right state) :=
  FiniteLocalCurrentEcology.inferWord_append
    (ecology (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port))
    T left right state

/-- If a target current is nonzero, at least one addressed source--target pair in its retained
fibre is nonzero.  This is the shortest local witness of genuine transport. -/
theorem exists_pairCurrent_ne_zero_of_returnedSiteCurrent_ne_zero
    (port : Port) (state : Site → Scalar) (target : Site)
    (nonzero : T.returnedSiteCurrent port state target ≠ 0) :
    ∃ source : Site, T.pairCurrent port state target source ≠ 0 := by
  by_contra absent
  apply nonzero
  rw [returnedSiteCurrent]
  apply Finset.sum_eq_zero
  intro source _
  exact not_ne_iff.mp (not_exists.mp absent source)

/-! ## Conserved realization current and enacted-port conditioning

The runtime realization carrier has one further constitutive requirement: each addressed source
site distributes its entire current across the complete `(port, target-site)` family.  This is a
finite Markov receiver chart of the already-founded current, not a stochastic ontology for Athena.
The joint section stays available as reconstruction testimony; enacting one positive-mass port
returns its exactly normalized conditional site section.
-/

variable {ProbSite : Type uS} {ProbPort : Type uP}
    [Fintype ProbSite] [Fintype ProbPort]

/-- One row-normalized boundary law from a source site to a port-indexed target site. -/
structure ConservedRealizationCurrent where
  boundaryKernel : MarkovKernel ProbSite (ProbPort × ProbSite)

namespace ConservedRealizationCurrent

variable (C : ConservedRealizationCurrent (ProbSite := ProbSite) (ProbPort := ProbPort))

/-- The full transported current before an exterior port is enacted. -/
def jointSection (prior : FiniteProbabilitySection ProbSite) :
    FiniteProbabilitySection (ProbPort × ProbSite) :=
  C.boundaryKernel.pushforward prior

/-- The exterior port current is the marginal of the complete transported section. -/
def portMass (prior : FiniteProbabilitySection ProbSite) (port : ProbPort) : ℝ :=
  ∑ site : ProbSite, (C.jointSection prior).mass (port, site)

theorem portMass_nonnegative (prior : FiniteProbabilitySection ProbSite) (port : ProbPort) :
    0 ≤ C.portMass prior port :=
  Finset.sum_nonneg fun site _ => (C.jointSection prior).nonnegative (port, site)

/-- Row conservation makes the complete port family itself a normalized receiver section. -/
theorem sum_portMass_eq_one (prior : FiniteProbabilitySection ProbSite) :
    ∑ port : ProbPort, C.portMass prior port = 1 := by
  simpa [portMass, Fintype.sum_prod_type] using (C.jointSection prior).normalized

/-- Enacting a positive-current port returns the corresponding normalized target-site section. -/
def conditionedSiteSection (prior : FiniteProbabilitySection ProbSite) (port : ProbPort)
    (positive : 0 < C.portMass prior port) : FiniteProbabilitySection ProbSite where
  mass site := (C.jointSection prior).mass (port, site) / C.portMass prior port
  nonnegative site := div_nonneg
    ((C.jointSection prior).nonnegative (port, site)) positive.le
  normalized := by
    rw [← Finset.sum_div, show (∑ site : ProbSite,
      (C.jointSection prior).mass (port, site)) = C.portMass prior port from rfl]
    exact div_self positive.ne'

/-- The enacted section and its port mass reconstruct the corresponding member of the complete
counterfactual family exactly.  Other ports remain in the joint reconstruction fibre. -/
theorem portMass_mul_conditioned_eq_joint
    (prior : FiniteProbabilitySection ProbSite) (port : ProbPort)
    (positive : 0 < C.portMass prior port) (site : ProbSite) :
    C.portMass prior port * (C.conditionedSiteSection prior port positive).mass site =
      (C.jointSection prior).mass (port, site) := by
  change C.portMass prior port *
      ((C.jointSection prior).mass (port, site) / C.portMass prior port) = _
  field_simp [positive.ne']

end ConservedRealizationCurrent

/-! ## Dependent complex current and the later positive receiver

The positive port chart above is lawful only after the productive oriented current has completed
its linear target and port junction.  A realization may carry several dependent factor lines.  We
therefore keep one complex port current per factor, and only a later constitutive receiver forms
the sum of their squared norms.  This is the precise boundary between Complex-Parametron current
and a probability/potential face.
-/

variable {ComplexSite : Type uS} {ComplexIncidence : Type uI} {ComplexPort : Type uP}
    {Factor : Type uF}
    [Fintype ComplexSite] [Fintype ComplexIncidence] [Fintype Factor]

/-- The complete linearly contracted port section, still indexed by its dependent factor line. -/
def complexPortFactorSection
    (T : OrientedPortSiteTransport ℂ ComplexSite ComplexIncidence ComplexPort)
    (state : Factor → ComplexSite → ℂ) (port : ComplexPort) : Factor → ℂ :=
  fun factor ↦ T.portCurrent port (state factor)

/-- A positive exterior receiver formed only after every source has joined at its target and every
target has joined at the port, separately on each dependent factor line. -/
def postContractionPortMass
    (T : OrientedPortSiteTransport ℂ ComplexSite ComplexIncidence ComplexPort)
    (state : Factor → ComplexSite → ℂ) (port : ComplexPort) : ℝ :=
  ∑ factor : Factor, Complex.normSq (complexPortFactorSection T state port factor)

/-- The definition exposes the required constitutive order: both linear junctions occur inside
`normSq`; the positive receiver cannot be pushed down to pair-current occurrences in general. -/
theorem postContractionPortMass_eq_norm_joined_current
    (T : OrientedPortSiteTransport ℂ ComplexSite ComplexIncidence ComplexPort)
    (state : Factor → ComplexSite → ℂ) (port : ComplexPort) :
    postContractionPortMass T state port =
      ∑ factor : Factor, Complex.normSq
        (∑ target : ComplexSite, ∑ source : ComplexSite,
          T.pairCurrent port (state factor) target source) := rfl

theorem postContractionPortMass_nonnegative
    (T : OrientedPortSiteTransport ℂ ComplexSite ComplexIncidence ComplexPort)
    (state : Factor → ComplexSite → ℂ) (port : ComplexPort) :
    0 ≤ postContractionPortMass T state port :=
  Finset.sum_nonneg fun _factor _ ↦ Complex.normSq_nonneg _

/-- Norm-before-junction is not an algebraic refactoring of the lawful receiver.  Oppositely
oriented nonzero currents cancel in the linear junction while their separately squared shadows do
not.  Any runtime which replaces the former by the latter has changed the receiver and erased
relative phase. -/
theorem norm_before_linear_join_is_not_postContraction :
    Complex.normSq ((1 : ℂ) + (-1 : ℂ)) ≠
      Complex.normSq (1 : ℂ) + Complex.normSq (-1 : ℂ) := by
  norm_num [Complex.normSq]

end OrientedPortSiteTransport

/-! ## Constitutive return of an ordinary joined section

This is a finite diagonal-admittance/diagonal-duality chart, not a universal update rule.
The source section and the arriving section are data on two genuinely joined occurrences.
Their difference is formed after the source crosses the contemporary cross-section.  Local
admittance returns its signed current; the source duality carries the other factor of the
existing additive morphology deposit.  Neither a scalar loss nor a next-token label enters.

The frame coefficients are constitutive chart data: no claim derives an arbitrary admittance
from shape, count, or magnitude.  The proofs below give coefficient support, complete later
transport, and the nonzero relation the deposit can found.  Universal future-cone soundness,
useful learning, and a physical calibration are not consequences of this finite algebra.
-/

namespace ConstitutiveSectionReturn

open Soma.Holonics
open Soma.Holonics.Computation.HolonicInformationTheory

variable {K Site : Type*} [CommRing K] [Fintype Site]

/-- Local admittance and source tangent-to-cotangent chart of the admitted cross-section. -/
structure Frame (K Site : Type*) where
  admittance : Site → K
  sourceDuality : Site → K

/-- Current is still a source--target section before the target junction is read. -/
def pairCurrent (morphology : Matrix Site Site K) (presented : Site → K)
    (target source : Site) : K := morphology target source * presented source

def conduct (morphology : Matrix Site Site K) (presented : Site → K) : Site → K :=
  fun target ↦ ∑ source, pairCurrent morphology presented target source

/-- The arriving section is compared in the target fibre, after source transport. -/
def difference (morphology : Matrix Site Site K) (presented arrived : Site → K) : Site → K :=
  arrived - conduct morphology presented

def current (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) : Site → K :=
  fun target ↦ frame.admittance target * difference morphology presented arrived target

def sourceCovector (frame : Frame K Site) (presented : Site → K) : Site → K :=
  fun source ↦ frame.sourceDuality source * presented source

/-- The two factors are derived from the actual signed current and presented source section. -/
def deposit (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) : Matrix Site Site K :=
  Matrix.vecMulVec (current frame morphology presented arrived) (sourceCovector frame presented)

def successor (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) : Matrix Site Site K :=
  morphology + deposit frame morphology presented arrived

/-- One actual joining, with section charts on its occurrences rather than a fabricated key. -/
structure JoinedSections {Source Middle Target : Type*}
    (first : AddressedPassage Source Middle) (second : AddressedPassage Middle Target)
    (K Site : Type*) where
  joining : first.Join second
  sourceSection : first.Occurrence → Site → K
  targetSection : second.Occurrence → Site → K

def JoinedSections.presented {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (sections : JoinedSections first second K Site) : Site → K :=
  sections.sourceSection sections.joining.left

def JoinedSections.arrived {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (sections : JoinedSections first second K Site) : Site → K :=
  sections.targetSection sections.joining.right

omit [CommRing K] [Fintype Site] in
/-- The declaration of a joining preserves its actual common boundary. -/
theorem JoinedSections.boundary_joins {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (sections : JoinedSections first second K Site) :
    first.target sections.joining.left = second.source sections.joining.right :=
  sections.joining.joins

theorem deposit_apply (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) (target source : Site) :
    deposit frame morphology presented arrived target source =
      current frame morphology presented arrived target * sourceCovector frame presented source := rfl

/-- An unaffected coefficient is proved unchanged; no magnitude threshold chooses its support. -/
theorem successor_eq_of_zero_factor (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) (target source : Site)
    (zeroFactor : current frame morphology presented arrived target = 0 ∨
      sourceCovector frame presented source = 0) :
    successor frame morphology presented arrived target source = morphology target source := by
  rcases zeroFactor with zeroCurrent | zeroSource
  · simp [successor, deposit, Matrix.vecMulVec, zeroCurrent]
  · simp [successor, deposit, Matrix.vecMulVec, zeroSource]

/-- Every later input sees the whole additive transport, not a stored output from the exposure. -/
theorem successor_conduct (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived query : Site → K) (target : Site) :
    conduct (successor frame morphology presented arrived) query target =
      conduct morphology query target + current frame morphology presented arrived target *
        (∑ source, sourceCovector frame presented source * query source) := by
  change (∑ source, (morphology target source +
      current frame morphology presented arrived target * sourceCovector frame presented source) *
      query source) = (∑ source, morphology target source * query source) +
      current frame morphology presented arrived target *
        (∑ source, sourceCovector frame presented source * query source)
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Unchanged later conduct requires vanishing complete coupling, not just a remote address. -/
theorem successor_conduct_eq_of_annihilates
    (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived query : Site → K)
    (annihilates : (∑ source, sourceCovector frame presented source * query source) = 0) :
    conduct (successor frame morphology presented arrived) query = conduct morphology query := by
  funext target
  rw [successor_conduct, annihilates, mul_zero, add_zero]

/-- A previously absent relation can be founded only by the nonzero returned factor product. -/
theorem absent_relation_founded (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived : Site → K) (target source : Site)
    (absent : morphology target source = 0)
    (couples : current frame morphology presented arrived target *
      sourceCovector frame presented source ≠ 0) :
    successor frame morphology presented arrived target source ≠ 0 := by
  simpa [successor, deposit, Matrix.vecMulVec, absent] using couples

/-- A matched arrival causes no deposit, even though its chronology is a new occurrence. -/
theorem matched_successor (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented : Site → K) :
    successor frame morphology presented (conduct morphology presented) = morphology := by
  ext target source
  simp [successor, deposit, current, difference, Matrix.vecMulVec]

/-! ### The existing physical-crossing and recurrent-operation owners are instantiated -/

/-- This chart's transport is the actual finite cross-section, not a byte/identifier conversion. -/
def physicalCrossing {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (frame : Frame K Site) (morphology : Matrix Site Site K)
    (sections : JoinedSections first second K Site) :
    AddressedPhysicalCrossing (first.Join second) Source Target (Site → K) (Site → K)
      (Site → K) where
  occurrence := sections.joining
  exteriorBoundary := first.source sections.joining.left
  interiorBoundary := second.target sections.joining.right
  exteriorPotential := sections.presented
  interiorPotential := sections.arrived
  transport := morphology.mulVecLin.toAddMonoidHom
  admittance := {
    toFun := fun carrier site ↦ frame.admittance site * carrier site
    map_zero' := by ext site; simp
    map_add' := by intros; ext site; simp [mul_add]
  }

theorem physicalCrossing_current {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (frame : Frame K Site) (morphology : Matrix Site Site K)
    (sections : JoinedSections first second K Site) :
    (physicalCrossing frame morphology sections).returnedCurrent =
      current frame morphology sections.presented sections.arrived := by
  rfl

/-- The cross-section is the existing source--target current ecology, with identity reaction. -/
def neural : FiniteLocalCurrentEcology Site K (Matrix Site Site K) (Site → K) Unit (Site → K) where
  localCurrent morphology _ presented target source := pairCurrent morphology presented target source
  reaction _ _ _ joined := joined
  observe _ carrier := carrier

theorem neural_step (morphology : Matrix Site Site K) (presented arrived : Site → K) :
    (neural (K := K) (Site := Site)).step morphology arrived presented =
      conduct morphology presented := rfl

open Soma.Holonics.Computation.HolonicRecurrentEcology

/-- No update callback: both presentation and morphology advance have the concrete laws above. -/
def recurrentOperation {Source Middle Target : Type*}
    (first : AddressedPassage Source Middle) (second : AddressedPassage Middle Target)
    (frame : Frame K Site) :
    FiniteRecurrentOperation (neural (K := K) (Site := Site))
      (JoinedSections first second K Site) where
  present _ sections := (sections.arrived, (), sections.presented)
  advanceMorphology morphology sections presented _ :=
    successor frame morphology presented sections.arrived

theorem recurrent_successor {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (frame : Frame K Site)
    (state : FiniteEcologyState Site K (Matrix Site Site K) (JoinedSections first second K Site))
    (sections : JoinedSections first second K Site) :
    ((recurrentOperation first second frame).operate state sections).2.2 =
      { morphology := successor frame state.morphology sections.presented sections.arrived
        carrier := conduct state.morphology sections.presented
        chronology := state.chronology ++ [sections] } := rfl

/-- The second return's difference is read through the already changed transport, not the base. -/
theorem next_difference_uses_successor (frame : Frame K Site) (morphology : Matrix Site Site K)
    (presented arrived nextPresented nextArrived : Site → K) (target : Site) :
    difference (successor frame morphology presented arrived) nextPresented nextArrived target =
      difference morphology nextPresented nextArrived target -
        current frame morphology presented arrived target *
          (∑ source, sourceCovector frame presented source * nextPresented source) := by
  change nextArrived target - conduct (successor frame morphology presented arrived) nextPresented target = _
  rw [successor_conduct]
  change nextArrived target - (conduct morphology nextPresented target + _) =
    (nextArrived target - conduct morphology nextPresented target) - _
  ring

/-! ### Reindex the whole local chart, not just its final receiver -/

variable {OtherSite : Type*} [Fintype OtherSite]

def rebaseSection (equiv : Site ≃ OtherSite) (carrier : Site → K) : OtherSite → K :=
  carrier ∘ equiv.symm

def rebaseMatrix (equiv : Site ≃ OtherSite) (matrix : Matrix Site Site K) :
    Matrix OtherSite OtherSite K := fun target source ↦ matrix (equiv.symm target) (equiv.symm source)

def rebaseFrame (equiv : Site ≃ OtherSite) (frame : Frame K Site) : Frame K OtherSite :=
  ⟨rebaseSection equiv frame.admittance, rebaseSection equiv frame.sourceDuality⟩

theorem conduct_rebase (equiv : Site ≃ OtherSite) (matrix : Matrix Site Site K)
    (presented : Site → K) :
    conduct (rebaseMatrix equiv matrix) (rebaseSection equiv presented) =
      rebaseSection equiv (conduct matrix presented) := by
  funext target
  exact equiv.symm.sum_comp (fun source ↦ matrix (equiv.symm target) source * presented source)

theorem difference_rebase (equiv : Site ≃ OtherSite) (matrix : Matrix Site Site K)
    (presented arrived : Site → K) :
    difference (rebaseMatrix equiv matrix) (rebaseSection equiv presented)
      (rebaseSection equiv arrived) = rebaseSection equiv (difference matrix presented arrived) := by
  rw [difference, conduct_rebase]
  rfl

theorem current_rebase (equiv : Site ≃ OtherSite) (frame : Frame K Site)
    (matrix : Matrix Site Site K) (presented arrived : Site → K) :
    current (rebaseFrame equiv frame) (rebaseMatrix equiv matrix)
      (rebaseSection equiv presented) (rebaseSection equiv arrived) =
      rebaseSection equiv (current frame matrix presented arrived) := by
  unfold current
  rw [difference_rebase]
  rfl

theorem successor_rebase (equiv : Site ≃ OtherSite) (frame : Frame K Site)
    (matrix : Matrix Site Site K) (presented arrived : Site → K) :
    successor (rebaseFrame equiv frame) (rebaseMatrix equiv matrix)
      (rebaseSection equiv presented) (rebaseSection equiv arrived) =
      rebaseMatrix equiv (successor frame matrix presented arrived) := by
  unfold successor deposit
  rw [current_rebase]
  rfl

def rebaseJoined {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite) (sections : JoinedSections first second K Site) :
    JoinedSections first second K OtherSite where
  joining := sections.joining
  sourceSection carried := rebaseSection equiv (sections.sourceSection carried)
  targetSection carried := rebaseSection equiv (sections.targetSection carried)

def rebaseState {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite)
    (state : FiniteEcologyState Site K (Matrix Site Site K) (JoinedSections first second K Site)) :
    FiniteEcologyState OtherSite K (Matrix OtherSite OtherSite K)
      (JoinedSections first second K OtherSite) where
  morphology := rebaseMatrix equiv state.morphology
  carrier := rebaseSection equiv state.carrier
  chronology := state.chronology.map (rebaseJoined equiv)

omit [CommRing K] [Fintype Site] [Fintype OtherSite] in
/-- Reindexing leaves the actual joining occurrence in place, rather than replacing its identity. -/
theorem rebaseJoined_same_join {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite) (sections : JoinedSections first second K Site) :
    (rebaseJoined equiv sections).joining = sections.joining := rfl

theorem recurrent_emission_rebase {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite) (frame : Frame K Site)
    (state : FiniteEcologyState Site K (Matrix Site Site K) (JoinedSections first second K Site))
    (sections : JoinedSections first second K Site) :
    ((recurrentOperation first second (rebaseFrame equiv frame)).operate
      (rebaseState equiv state) (rebaseJoined equiv sections)).1 =
      rebaseSection equiv (((recurrentOperation first second frame).operate state sections).1) :=
  conduct_rebase equiv state.morphology sections.presented

/-- The whole successor commutes: morphology, continuing carrier and the complete chronology. -/
theorem recurrent_successor_rebase {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite) (frame : Frame K Site)
    (state : FiniteEcologyState Site K (Matrix Site Site K) (JoinedSections first second K Site))
    (sections : JoinedSections first second K Site) :
    ((recurrentOperation first second (rebaseFrame equiv frame)).operate
      (rebaseState equiv state) (rebaseJoined equiv sections)).2.2 =
      rebaseState equiv (((recurrentOperation first second frame).operate state sections).2.2) := by
  rw [recurrent_successor, recurrent_successor]
  simp only [rebaseState, rebaseJoined, JoinedSections.presented, JoinedSections.arrived,
    successor_rebase, conduct_rebase, List.map_append, List.map_cons, List.map_nil]

/-- The formal trace keeps every addressed contribution under the same endpoint reindexing.
This is a denotation theorem, not an instruction to copy that population off the GPU. -/
theorem recurrent_pairCurrent_rebase {Source Middle Target : Type*}
    {first : AddressedPassage Source Middle} {second : AddressedPassage Middle Target}
    (equiv : Site ≃ OtherSite) (frame : Frame K Site)
    (state : FiniteEcologyState Site K (Matrix Site Site K) (JoinedSections first second K Site))
    (sections : JoinedSections first second K Site) (target source : OtherSite) :
    ((recurrentOperation first second (rebaseFrame equiv frame)).operate
      (rebaseState equiv state) (rebaseJoined equiv sections)).2.1.localCurrent target source =
      (((recurrentOperation first second frame).operate state sections).2.1.localCurrent
        (equiv.symm target) (equiv.symm source)) := rfl

/-! ### A chart can grow without changing old transport, but silence alone learns nothing -/

def extendSection (carrier : Site → K) : Option Site → K
  | some site => carrier site
  | none => 0

def extendMatrix (matrix : Matrix Site Site K) : Matrix (Option Site) (Option Site) K
  | some target, some source => matrix target source
  | _, _ => 0

def extendFrame (frame : Frame K Site) (newAdmittance newDuality : K) : Frame K (Option Site) where
  admittance site := site.elim newAdmittance frame.admittance
  sourceDuality site := site.elim newDuality frame.sourceDuality

theorem conduct_extend (matrix : Matrix Site Site K) (carrier : Site → K) :
    conduct (extendMatrix matrix) (extendSection carrier) = extendSection (conduct matrix carrier) := by
  funext site
  cases site <;> simp [conduct, pairCurrent, extendMatrix, extendSection, Fintype.sum_option]

theorem successor_extend (frame : Frame K Site) (matrix : Matrix Site Site K)
    (presented arrived : Site → K) (newAdmittance newDuality : K) :
    successor (extendFrame frame newAdmittance newDuality) (extendMatrix matrix)
      (extendSection presented) (extendSection arrived) =
      extendMatrix (successor frame matrix presented arrived) := by
  ext target source
  cases target <;> cases source <;>
    simp [successor, deposit, current, difference, conduct_extend, sourceCovector,
      extendFrame, extendMatrix, extendSection, Matrix.vecMulVec]

namespace Control

def unitFrame : Frame ℚ (Fin 2) := ⟨fun _ ↦ 1, fun _ ↦ 1⟩

/-- Equal squared receiver faces do not identify orthogonally situated returns. -/
theorem equal_scalar_distinct_deposits :
    ((1 : ℚ)^2 + 0^2 = 0^2 + 1^2) ∧
      deposit unitFrame 0 ![1, 0] ![1, 0] ≠ deposit unitFrame 0 ![1, 0] ![0, 1] := by
  constructor
  · norm_num
  · intro same
    have atSite := congrFun (congrFun same 0) 0
    norm_num [deposit, current, difference, conduct, pairCurrent, sourceCovector,
      unitFrame, Matrix.vecMulVec, Fin.sum_univ_two] at atSite

/-- The new site is not a silent padding trick: a caused nonzero contact forms a later-used edge. -/
theorem new_site_contact_is_used :
    let frame : Frame ℚ (Option (Fin 1)) := ⟨fun _ ↦ 1, fun _ ↦ 1⟩
    let source : Option (Fin 1) → ℚ := fun site ↦ site.elim 1 (fun _ ↦ 0)
    let arrival : Option (Fin 1) → ℚ := fun site ↦ site.elim 2 (fun _ ↦ 0)
    successor frame 0 source arrival none none = 2 ∧
      conduct (successor frame 0 source arrival) source none = 2 ∧
      successor frame 0 source arrival (some 0) (some 0) = 0 := by
  norm_num [successor, deposit, current, difference, conduct, pairCurrent,
    sourceCovector, Matrix.vecMulVec, Fintype.sum_option, Fintype.sum_unique]

end Control

/-! ### Rectangular cross-sections are bipartite charts of the same local operation

The embedding is formal only: the implementation stores the rectangular factors, never the
zero-filled square. Identity admittance is the derivative of the native additive junction in
either input slot; the source-coordinate pairing is declared in that native chart. The dyadic
deposit readout remains the explicit scalar `eta`, not a derived learning constant.
-/

section Rectangular
variable {InputSite OutputSite : Type*} [Fintype InputSite] [Fintype OutputSite]

def bipartiteMatrix (matrix : Matrix OutputSite InputSite K) :
    Matrix (OutputSite ⊕ InputSite) (OutputSite ⊕ InputSite) K
  | Sum.inl target, Sum.inr source => matrix target source
  | _, _ => 0

def bipartiteSource (carrier : InputSite → K) : OutputSite ⊕ InputSite → K :=
  Sum.elim (fun _ ↦ 0) carrier

def bipartiteArrival (carrier : OutputSite → K) : OutputSite ⊕ InputSite → K :=
  Sum.elim carrier (fun _ ↦ 0)

def bipartiteFrame (eta : K) : Frame K (OutputSite ⊕ InputSite) where
  admittance := Sum.elim (fun _ ↦ eta) (fun _ ↦ 0)
  sourceDuality := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)

theorem bipartite_conduct (matrix : Matrix OutputSite InputSite K) (presented : InputSite → K)
    (target : OutputSite) :
    conduct (bipartiteMatrix matrix) (bipartiteSource presented) (Sum.inl target) =
      ∑ source, matrix target source * presented source := by
  simp [conduct, pairCurrent, bipartiteMatrix, bipartiteSource, Fintype.sum_sum_type]

theorem rectangular_deposit (eta : K) (matrix : Matrix OutputSite InputSite K)
    (presented : InputSite → K) (arrived : OutputSite → K) (target : OutputSite) (source : InputSite) :
    deposit (bipartiteFrame eta) (bipartiteMatrix matrix)
      (bipartiteSource presented) (bipartiteArrival arrived) (Sum.inl target) (Sum.inr source) =
      eta * (arrived target - ∑ inner, matrix target inner * presented inner) * presented source := by
  change eta * (arrived target -
    conduct (bipartiteMatrix matrix) (bipartiteSource presented) (Sum.inl target)) *
    (1 * presented source) = _
  rw [one_mul, bipartite_conduct]

/-- Both branches of an additive junction have identity local differential, without a score. -/
theorem additive_junction_input_differences (left right dl dr : K) :
    ((left + dl) + right - (left + right) = dl) ∧
      (left + (right + dr) - (left + right) = dr) := by
  constructor <;> ring

/-- A sum and its input derivative do not determine the individual constitutive routes. Both
these bodies return the same complete sum for every input, while a branch receiver separates
them. Thus the Add primitive cannot by itself authorize equalizing its arriving fields. -/
theorem additive_face_does_not_found_an_equalization_target :
    (∀ x : ℚ, 1 * x + 0 * x = (1 / 2) * x + (1 / 2) * x) ∧
      (1 : ℚ) ≠ 1 / 2 := by
  constructor
  · intro x; ring
  · norm_num

/-- The actual joined passage compares the joining operation's OUTPUT with its transported
input. Its returned effect is the partner current, not partner-minus-transported. This records
what the interaction did and introduces no desired setpoint for either incoming branch. -/
theorem additive_joined_passage_effect (transported partner : K) :
    (transported + partner) - transported = partner := by
  ring

/-- A zero partner leaves the actual passage unchanged; the rejected equalization still changes
a nonzero branch. This separates the two candidate bindings before any model-quality claim. -/
theorem zero_partner_separates_passage_effect_from_equalization :
    ((1 : ℚ) + 0) - 1 = 0 ∧ (0 : ℚ) - 1 ≠ 0 := by
  norm_num

/-! ### A bounded paired-feedback growth control

This is a counterexample to unconditional stability: two reciprocal legs can amplify their
shared sum.  The leg deposits below are the already-defined rectangular deposit, with unit source
scalar and each evolving transported coefficient; `partner` is the joined residual returned by
that leg.
-/

def unitLegDeposit (eta transported partner : ℚ) : ℚ :=
  deposit (bipartiteFrame eta)
    (bipartiteMatrix (OutputSite := Fin 1) (InputSite := Fin 1)
      (fun _ : Fin 1 => fun _ : Fin 1 => transported))
    (bipartiteSource (InputSite := Fin 1) (fun _ : Fin 1 ↦ 1))
    (bipartiteArrival (OutputSite := Fin 1) (fun _ : Fin 1 ↦ transported + partner))
      (Sum.inl 0) (Sum.inr 0)

theorem unitLegDeposit_eq (eta transported partner : ℚ) :
    unitLegDeposit eta transported partner = eta * partner := by
  unfold unitLegDeposit
  norm_num [deposit, current, difference, conduct, pairCurrent, sourceCovector,
    bipartiteFrame, bipartiteMatrix, bipartiteSource, bipartiteArrival,
    Matrix.vecMulVec, Fintype.sum_sum_type]

def pairedFeedbackStep (eta a b : ℚ) : ℚ × ℚ :=
  (a + unitLegDeposit eta a b, b + unitLegDeposit eta b a)

theorem pairedFeedbackStep_eq (eta a b : ℚ) :
    pairedFeedbackStep eta a b = (a + eta * b, b + eta * a) := by
  simp [pairedFeedbackStep, unitLegDeposit_eq]

theorem pairedFeedbackStep_sum (eta a b : ℚ) :
    (pairedFeedbackStep eta a b).1 + (pairedFeedbackStep eta a b).2 =
      (1 + eta) * (a + b) := by
  rw [pairedFeedbackStep_eq]
  ring

def pairedFeedbackState (eta a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (a, b)
  | n + 1 => pairedFeedbackStep eta
      (pairedFeedbackState eta a b n).1 (pairedFeedbackState eta a b n).2

def pairedFeedbackSum (eta a b : ℚ) : ℕ → ℚ
  | n => (pairedFeedbackState eta a b n).1 + (pairedFeedbackState eta a b n).2

theorem pairedFeedbackSum_succ (eta a b : ℚ) (n : ℕ) :
    pairedFeedbackSum eta a b (n + 1) =
      (1 + eta) * pairedFeedbackSum eta a b n := by
  simpa only [pairedFeedbackSum, pairedFeedbackState] using
    (pairedFeedbackStep_sum eta
      (pairedFeedbackState eta a b n).1
      (pairedFeedbackState eta a b n).2)

theorem pairedFeedbackSum_eq_pow (eta a b : ℚ) (n : ℕ) :
    pairedFeedbackSum eta a b n = (1 + eta) ^ n * (a + b) := by
  induction n with
  | zero => norm_num [pairedFeedbackSum, pairedFeedbackState]
  | succ n ih =>
      rw [pairedFeedbackSum_succ, ih, pow_succ]
      ring

theorem pairedFeedback_sum_strictly_grows (eta a b : ℚ)
    (eta_pos : 0 < eta) (sum_pos : 0 < a + b) :
    a + b < (pairedFeedbackStep eta a b).1 + (pairedFeedbackStep eta a b).2 := by
  rw [pairedFeedbackStep_sum]
  nlinarith

end Rectangular
end ConstitutiveSectionReturn

/-! ### Finite positive-metric passive contact

This is a candidate contact law over actual same-fibre source and arrived observations.  It is
not the `Add` equalization of an internal child and its sum: `x` and `y` are the observations
which caused the contact.  The extra one-dimensional axis below records the signed energy gap;
it is a passive lifting, not an application or full-network stability theorem.
-/

namespace PassiveContact

open scoped BigOperators

abbrev Vector (n : ℕ) := Fin n → ℝ

def dot {n : ℕ} (u v : Vector n) : ℝ :=
  ∑ i, u i * v i

def squaredNorm {n : ℕ} (v : Vector n) : ℝ := dot v v

theorem dot_add_left {n : ℕ} (u v w : Vector n) :
    dot (u + v) w = dot u w + dot v w := by
  simp [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (u v w : Vector n) :
    dot u (v + w) = dot u v + dot u w := by
  simp [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_neg_left {n : ℕ} (u v : Vector n) :
    dot (-u) v = -dot u v := by
  simp [dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem dot_neg_right {n : ℕ} (u v : Vector n) :
    dot u (-v) = -dot u v := by
  simp [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem dot_smul_left {n : ℕ} (r : ℝ) (u v : Vector n) :
    dot (r • u) v = r * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, (r * u i) * v i) = ∑ i, r * (u i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = r * ∑ i, u i * v i := by rw [Finset.mul_sum]

theorem dot_smul_right {n : ℕ} (u v : Vector n) (r : ℝ) :
    dot u (r • v) = r * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, u i * (r * v i)) = ∑ i, r * (u i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = r * ∑ i, u i * v i := by rw [Finset.mul_sum]

theorem dot_comm {n : ℕ} (u v : Vector n) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem squaredNorm_nonneg {n : ℕ} (v : Vector n) : 0 ≤ squaredNorm v := by
  unfold squaredNorm dot
  exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (v i))

theorem squaredNorm_eq_zero {n : ℕ} {v : Vector n}
    (h : squaredNorm v = 0) : v = 0 := by
  have hz : ∀ i : Fin n, v i * v i = 0 := by
    have h' := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (f := fun i : Fin n ↦ v i * v i)
      (fun i _ ↦ mul_self_nonneg (v i))).mp h
    simpa [squaredNorm, dot] using h'
  funext i
  have hi := hz i
  exact mul_self_eq_zero.mp hi

theorem dot_sub_left {n : ℕ} (u v w : Vector n) :
    dot (u - v) w = dot u w - dot v w := by
  rw [show u - v = u + (-v) by rfl, dot_add_left, dot_neg_left]
  simp [sub_eq_add_neg]

theorem dot_sub_right {n : ℕ} (u v w : Vector n) :
    dot u (v - w) = dot u v - dot u w := by
  rw [show v - w = v + (-w) by rfl, dot_add_right, dot_neg_right]
  simp [sub_eq_add_neg]

def difference {n : ℕ} (x y : Vector n) : Vector n := x - y

def energyGap {n : ℕ} (x y : Vector n) : ℝ :=
  squaredNorm y - squaredNorm x

def positiveGap {n : ℕ} (x y : Vector n) : ℝ := max (energyGap x y) 0

def gapMagnitude {n : ℕ} (x y : Vector n) : ℝ := |energyGap x y|

def denominator {n : ℕ} (x y : Vector n) : ℝ :=
  squaredNorm (difference x y) + gapMagnitude x y

def contact {n : ℕ} (x y z : Vector n) : Vector n :=
  if denominator x y = 0 then z else
    z - (2 * (dot (difference x y) z + positiveGap x y) /
      denominator x y) • difference x y

theorem energyGap_eq_dot_difference_add {n : ℕ} (x y : Vector n) :
    energyGap x y = squaredNorm (difference x y) - 2 * dot (difference x y) x := by
  unfold energyGap difference squaredNorm
  simp only [dot_sub_left, dot_sub_right]
  rw [dot_comm y x]
  ring

theorem denominator_nonneg {n : ℕ} (x y : Vector n) : 0 ≤ denominator x y := by
  unfold denominator
  exact add_nonneg (squaredNorm_nonneg _) (abs_nonneg _)

theorem denominator_eq_zero_iff {n : ℕ} (x y : Vector n) :
    denominator x y = 0 ↔ x = y ∧ energyGap x y = 0 := by
  constructor
  · intro h
    have hd : squaredNorm (difference x y) = 0 := by
      have hn := squaredNorm_nonneg (difference x y)
      have hc := abs_nonneg (energyGap x y)
      unfold denominator at h
      exact le_antisymm
        (calc
          squaredNorm (difference x y) ≤ squaredNorm (difference x y) +
              gapMagnitude x y := le_add_of_nonneg_right hc
          _ = 0 := h)
        hn
    have hxy : difference x y = 0 := squaredNorm_eq_zero hd
    have hgap : |energyGap x y| = 0 := by
      have hn := squaredNorm_nonneg (difference x y)
      have hc := abs_nonneg (energyGap x y)
      unfold denominator at h
      exact le_antisymm
        (calc
          gapMagnitude x y ≤ squaredNorm (difference x y) + gapMagnitude x y :=
            le_add_of_nonneg_left hn
          _ = 0 := h)
        hc
    exact ⟨sub_eq_zero.mp hxy, abs_eq_zero.mp hgap⟩
  · rintro ⟨rfl, hgap⟩
    simp [denominator, difference, energyGap, gapMagnitude, squaredNorm, dot]

theorem positiveGap_eq_of_pos {n : ℕ} {x y : Vector n}
    (h : 0 < energyGap x y) : positiveGap x y = energyGap x y := by
  exact max_eq_left h.le

theorem positiveGap_eq_zero_of_nonpos {n : ℕ} {x y : Vector n}
    (h : energyGap x y ≤ 0) : positiveGap x y = 0 := by
  exact max_eq_right h

theorem contact_eq_identity_of_denominator_zero {n : ℕ} {x y : Vector n}
    (h : denominator x y = 0) : contact x y = id := by
  funext z
  simp only [contact, if_pos h]
  rfl

theorem contact_matched (x : Vector n) : contact x x = id := by
  apply contact_eq_identity_of_denominator_zero
  simp [denominator, difference, energyGap, gapMagnitude, squaredNorm, dot]

theorem contact_x_eq_y {n : ℕ} (x y : Vector n) : contact x y x = y := by
  by_cases hN : denominator x y = 0
  · have hid := contact_eq_identity_of_denominator_zero hN
    rw [hid]
    change x = y
    exact (denominator_eq_zero_iff x y).mp hN |>.1
  · have hden : denominator x y ≠ 0 := hN
    have hkey : dot (difference x y) x + positiveGap x y =
        denominator x y / 2 := by
      have hgap := energyGap_eq_dot_difference_add x y
      by_cases hD : 0 < energyGap x y
      · unfold denominator
        rw [positiveGap_eq_of_pos hD, show gapMagnitude x y = energyGap x y by
          exact abs_of_pos hD]
        nlinarith
      · have hD' : energyGap x y ≤ 0 := le_of_not_gt hD
        unfold denominator
        rw [positiveGap_eq_zero_of_nonpos hD', show gapMagnitude x y = -energyGap x y by
          exact abs_of_nonpos hD']
        nlinarith
    simp only [contact, if_neg hden]
    rw [hkey]
    have hcoef : 2 * (denominator x y / 2) / denominator x y = 1 := by
      field_simp
    rw [hcoef, one_smul]
    change x - (x - y) = y
    abel

theorem contact_difference {n : ℕ} {x y z w : Vector n}
    (hN : denominator x y ≠ 0) :
    contact x y z - contact x y w =
      (z - w) - (2 * dot (difference x y) (z - w) / denominator x y) •
        difference x y := by
  simp only [contact, if_neg hN]
  have hcoef :
      2 * (dot (difference x y) z + positiveGap x y) / denominator x y -
        2 * (dot (difference x y) w + positiveGap x y) / denominator x y =
      2 * dot (difference x y) (z - w) / denominator x y := by
    rw [dot_sub_right]
    ring
  rw [← hcoef]
  simp only [sub_smul]
  module

theorem squaredNorm_sub_smul {n : ℕ} (q d : Vector n) (r : ℝ) :
    squaredNorm (q - r • d) = squaredNorm q - 2 * r * dot d q +
      r ^ 2 * squaredNorm d := by
  unfold squaredNorm
  simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
  rw [dot_comm q d]
  ring

theorem contact_squared_distance {n : ℕ} {x y z w : Vector n}
    (hN : denominator x y ≠ 0) :
    squaredNorm (contact x y z - contact x y w) =
      squaredNorm (z - w) -
        4 * gapMagnitude x y / denominator x y ^ 2 *
          dot (difference x y) (z - w) ^ 2 := by
  rw [contact_difference hN]
  rw [squaredNorm_sub_smul]
  unfold denominator
  have hden : squaredNorm (difference x y) + gapMagnitude x y ≠ 0 := hN
  field_simp
  ring

theorem contact_nonexpansive {n : ℕ} {x y z w : Vector n}
    (hN : denominator x y ≠ 0) :
    squaredNorm (contact x y z - contact x y w) ≤ squaredNorm (z - w) := by
  rw [contact_squared_distance hN]
  have hc : 0 ≤ gapMagnitude x y := abs_nonneg _
  have hden : 0 < denominator x y := lt_of_le_of_ne
    (denominator_nonneg x y) (Ne.symm hN)
  have hs : 0 ≤ dot (difference x y) (z - w) ^ 2 := sq_nonneg _
  have hcoef : 0 ≤ 4 * gapMagnitude x y / denominator x y ^ 2 := by
    positivity
  nlinarith

def sourceAxis {n : ℕ} (x y : Vector n) : ℝ :=
  if 0 < energyGap x y then 1 else 0

def targetAxis {n : ℕ} (x y : Vector n) : ℝ :=
  if energyGap x y < 0 then 1 else 0

def axisDifference {n : ℕ} (x y : Vector n) : ℝ :=
  sourceAxis x y - targetAxis x y

def contactCoefficient {n : ℕ} (x y z : Vector n) : ℝ :=
  2 * (dot (difference x y) z + positiveGap x y) / denominator x y

def liftedEnergy {n : ℕ} (x y : Vector n) (z : Vector n) (a : ℝ) : ℝ :=
  squaredNorm z + gapMagnitude x y * a ^ 2

def liftedContact {n : ℕ} (x y z : Vector n) : Vector n × ℝ :=
  (contact x y z,
    sourceAxis x y - axisDifference x y * contactCoefficient x y z)

theorem axis_energy_eq_positiveGap {n : ℕ} (x y : Vector n) :
    gapMagnitude x y * sourceAxis x y ^ 2 = positiveGap x y := by
  unfold gapMagnitude sourceAxis positiveGap
  by_cases hD : 0 < energyGap x y
  · rw [if_pos hD, abs_of_pos hD, max_eq_left hD.le]
    ring
  · have hD' : energyGap x y ≤ 0 := le_of_not_gt hD
    rw [if_neg hD, abs_of_nonpos hD', max_eq_right hD']
    ring

theorem axisDifference_sq_eq_one {n : ℕ} (x y : Vector n) :
    axisDifference x y ^ 2 = 1 ∨ gapMagnitude x y = 0 := by
  unfold axisDifference sourceAxis targetAxis
  by_cases hD : 0 < energyGap x y
  · left
    rw [if_pos hD, if_neg (not_lt_of_ge hD.le)]
    norm_num
  · by_cases hneg : energyGap x y < 0
    · left
      rw [if_neg hD, if_pos hneg]
      norm_num
    · right
      have hzero : energyGap x y = 0 := le_antisymm (le_of_not_gt hD) (le_of_not_gt hneg)
      simp [gapMagnitude, hzero]

theorem axisDifference_sq_metric {n : ℕ} (x y : Vector n) :
    gapMagnitude x y * axisDifference x y ^ 2 = gapMagnitude x y := by
  rcases axisDifference_sq_eq_one x y with hs | hz
  · rw [hs, mul_one]
  · rw [hz, zero_mul]

theorem axisDifference_cross_metric {n : ℕ} (x y : Vector n) :
    gapMagnitude x y * sourceAxis x y * axisDifference x y = positiveGap x y := by
  unfold gapMagnitude sourceAxis axisDifference targetAxis positiveGap
  by_cases hD : 0 < energyGap x y
  · have ha : sourceAxis x y = 1 := by simp [sourceAxis, hD]
    rw [ha]
    simp [hD, not_lt_of_ge hD.le, abs_of_pos hD, max_eq_left hD.le]
  · have hD' : energyGap x y ≤ 0 := le_of_not_gt hD
    rw [if_neg hD]
    by_cases hneg : energyGap x y < 0
    · simp [hneg, abs_of_nonpos hD', max_eq_right hD']
    · simp [hneg, abs_of_nonpos hD', max_eq_right hD']

theorem lifted_reflection_energy {n : ℕ} (d z : Vector n)
    (c p a sigma N r : ℝ)
    (hN : N ≠ 0) (hden : N = squaredNorm d + c)
    (hcross : c * a * sigma = p) (hsquare : c * sigma ^ 2 = c)
    (hr : r = 2 * (dot d z + p) / N) :
    squaredNorm (z - r • d) + c * (a - sigma * r) ^ 2 =
      squaredNorm z + c * a ^ 2 := by
  rw [squaredNorm_sub_smul]
  calc
    squaredNorm z - 2 * r * dot d z + r ^ 2 * squaredNorm d +
        c * (a - sigma * r) ^ 2 =
      (squaredNorm z - 2 * r * dot d z + r ^ 2 * squaredNorm d) +
        (c * a ^ 2 - 2 * (c * a * sigma) * r + (c * sigma ^ 2) * r ^ 2) := by
          ring
    _ = squaredNorm z - 2 * r * dot d z + r ^ 2 * squaredNorm d +
        (c * a ^ 2 - 2 * p * r + c * r ^ 2) := by rw [hcross, hsquare]
    _ = squaredNorm z + c * a ^ 2 := by
      rw [hr, hden]
      have hden' : squaredNorm d + c ≠ 0 := by
        rw [← hden]
        exact hN
      field_simp [hden']
      ring

theorem liftedContact_energy_preserved {n : ℕ} {x y : Vector n}
    (hN : denominator x y ≠ 0) (z : Vector n) :
    liftedEnergy x y (liftedContact x y z).1 (liftedContact x y z).2 =
      liftedEnergy x y z (sourceAxis x y) := by
  simp only [liftedEnergy, liftedContact]
  simp only [contact, if_neg hN]
  unfold contactCoefficient axisDifference
  apply lifted_reflection_energy (difference x y) z
    (gapMagnitude x y) (positiveGap x y) (sourceAxis x y)
      (sourceAxis x y - targetAxis x y) (denominator x y)
      (2 * (dot (difference x y) z + positiveGap x y) / denominator x y)
  · exact hN
  · rfl
  · exact axisDifference_cross_metric x y
  · exact axisDifference_sq_metric x y
  · rfl

theorem liftedContact_passive {n : ℕ} {x y : Vector n}
    (hN : denominator x y ≠ 0) (z : Vector n) :
    squaredNorm (contact x y z) ≤ squaredNorm z + positiveGap x y := by
  have hp := liftedContact_energy_preserved hN z
  have haxis : 0 ≤ gapMagnitude x y *
      (sourceAxis x y - axisDifference x y * contactCoefficient x y z) ^ 2 :=
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hsource : gapMagnitude x y * sourceAxis x y ^ 2 = positiveGap x y :=
    axis_energy_eq_positiveGap x y
  unfold liftedEnergy at hp
  rw [hsource] at hp
  change squaredNorm (contact x y z) + gapMagnitude x y *
      (sourceAxis x y - axisDifference x y * contactCoefficient x y z) ^ 2 =
    squaredNorm z + positiveGap x y at hp
  nlinarith

end PassiveContact

/-! ### A tied-map next-arrival contrast

Historical bounded algebra from the withdrawn inherited-model draft (2026-09-05). The prefix
receipt and shared-map contrast do not found contextual applicability; `context` below is the
declared vector chart, not the full situated conditions of HNA. Its runtime integration is archived
under `archive/experiments/2026-09-05-tied-next-arrival/`. No native foundation is scheduled here.

The following is an independently defined next-arrival contrast, not the endogenous `Add` effect.
The map owns both row covectors and the declared deterministic receiver face.  An occurrence keeps
the actual context, receiver address, a nonempty source word, and an entering word whose first
post-source element is the observed address.  This is an abstract prefix-join receipt, not a proof
of the whole Rust runtime; no answer, logit margin, or gain is selected by the theorem.  The
Euclidean metric is the same declared chart used by `PassiveContact`: equal widths alone do not
found a returned current.
-/

namespace TiedMapNextArrival

abbrev Address (a : ℕ) := Fin a
abbrev Chart (h : ℕ) := PassiveContact.Vector h

/-- A finite tied coefficient map `W : H → A`, represented by its row covectors in the H chart.
The receiver-face selector is an actual deterministic receiver owner, not a score or answer map. -/
structure TiedCoefficientMap (h a : ℕ) where
  row : Address a → Chart h
  receiverFace : Chart h → Address a

namespace TiedCoefficientMap

variable {h a : ℕ} (W : TiedCoefficientMap h a)

def coefficientMap : Address a → Chart h := W.row

theorem coefficientMap_eq_row (address : Address a) :
    W.coefficientMap address = W.row address := rfl

end TiedCoefficientMap

/-- A joined occurrence with an actual deterministic receiver face `p` and a causally next
observed input address `a`.  The field `receiver_face` is the occurrence's receiver-scope receipt. -/
structure ActualNextArrival {h a : ℕ} (W : TiedCoefficientMap h a) where
  context : Chart h
  observedAddress : Address a
  receiverAddress : Address a
  receiver_face : receiverAddress = W.receiverFace context
  sourceWord : List (Address a)
  enteringWord : List (Address a)
  remainder : List (Address a)
  source_nonempty : sourceWord ≠ []
  joining : enteringWord = sourceWord ++ observedAddress :: remainder

namespace ActualNextArrival

variable {h a : ℕ} {W : TiedCoefficientMap h a}

def returnedCurrent (occurrence : ActualNextArrival W) : Chart h :=
  W.row occurrence.observedAddress - W.row occurrence.receiverAddress

def joinedField (occurrence : ActualNextArrival W) : Chart h :=
  occurrence.context + occurrence.returnedCurrent

def passiveCalibration (occurrence : ActualNextArrival W) : Chart h :=
  PassiveContact.contact occurrence.context occurrence.joinedField occurrence.context

theorem observedAddress_after_source (occurrence : ActualNextArrival W) :
    occurrence.enteringWord =
      occurrence.sourceWord ++ occurrence.observedAddress :: occurrence.remainder :=
  occurrence.joining

theorem enteringWord_nonempty (occurrence : ActualNextArrival W) :
    occurrence.enteringWord ≠ [] := by
  rw [occurrence.joining]
  simp

/-- The paired margin reads the returned current against the actual joined field.  Its second term
is the squared norm of the same row difference, so it is not an externally supplied margin. -/
theorem paired_margin_identity (occurrence : ActualNextArrival W) :
    PassiveContact.dot occurrence.returnedCurrent occurrence.joinedField =
      PassiveContact.dot occurrence.returnedCurrent occurrence.context +
        PassiveContact.squaredNorm occurrence.returnedCurrent := by
  simp [joinedField, PassiveContact.dot_add_right, PassiveContact.squaredNorm]

/-- When the observed address is the actual receiver address, the shared tied map returns zero. -/
theorem matched_returnedCurrent (occurrence : ActualNextArrival W)
    (matched : occurrence.observedAddress = occurrence.receiverAddress) :
    occurrence.returnedCurrent = 0 := by
  simp [returnedCurrent, matched]

theorem matched_joinedField (occurrence : ActualNextArrival W)
    (matched : occurrence.observedAddress = occurrence.receiverAddress) :
    occurrence.joinedField = occurrence.context := by
  simp [joinedField, matched_returnedCurrent occurrence matched]

/-- A matched next arrival is the passive identity contact in the same declared metric chart. -/
theorem matched_passiveCalibration_identity (occurrence : ActualNextArrival W)
    (matched : occurrence.observedAddress = occurrence.receiverAddress) :
    PassiveContact.contact occurrence.context occurrence.joinedField = id := by
  rw [matched_joinedField occurrence matched]
  exact PassiveContact.contact_matched occurrence.context

/-- Passive calibration of the actual joined passage returns that same actual joined field. -/
theorem passiveCalibration_eq_joinedField (occurrence : ActualNextArrival W) :
    occurrence.passiveCalibration = occurrence.joinedField := by
  exact PassiveContact.contact_x_eq_y occurrence.context occurrence.joinedField

end ActualNextArrival

/-! Equal finite widths do not identify a row contrast: the shared coefficient map and its metric
chart are constitutive inputs.  This explicit control keeps that boundary visible without making
the contrast a claim about a top face, useful learning, or global HNA stability. -/

theorem equal_widths_do_not_found_return :
    ∃ (W₁ W₂ : TiedCoefficientMap 1 2) (a p : Address 2),
      (W₁.row a - W₁.row p) ≠ (W₂.row a - W₂.row p) := by
  refine ⟨
    { row := fun _ ↦ ![0]
      receiverFace := fun _ ↦ 0 },
    { row := fun address ↦ if address = 0 then ![1] else ![0]
      receiverFace := fun _ ↦ 0 },
    0, 1, ?_⟩
  intro same
  have hcoord := congrFun same 0
  norm_num at hcoord

end TiedMapNextArrival

end Soma.Holonics.Computation.HolonicOrientedSiteTransport

section Audit
open Soma.Holonics.Computation.HolonicOrientedSiteTransport
#print axioms OrientedPortSiteTransport.localTransport_apply
#print axioms OrientedPortSiteTransport.ecology_step_eq_returnedSiteCurrent
#print axioms OrientedPortSiteTransport.ecology_step_eq_returnedSiteSection
#print axioms OrientedPortSiteTransport.ecology_inferWord_append
#print axioms OrientedPortSiteTransport.exists_pairCurrent_ne_zero_of_returnedSiteCurrent_ne_zero
#print axioms OrientedPortSiteTransport.ConservedRealizationCurrent.sum_portMass_eq_one
#print axioms OrientedPortSiteTransport.ConservedRealizationCurrent.portMass_mul_conditioned_eq_joint
#print axioms OrientedPortSiteTransport.postContractionPortMass_eq_norm_joined_current
#print axioms OrientedPortSiteTransport.postContractionPortMass_nonnegative
#print axioms OrientedPortSiteTransport.norm_before_linear_join_is_not_postContraction
#print axioms ConstitutiveSectionReturn.successor_conduct
#print axioms ConstitutiveSectionReturn.successor_conduct_eq_of_annihilates
#print axioms ConstitutiveSectionReturn.absent_relation_founded
#print axioms ConstitutiveSectionReturn.physicalCrossing_current
#print axioms ConstitutiveSectionReturn.recurrent_successor
#print axioms ConstitutiveSectionReturn.next_difference_uses_successor
#print axioms ConstitutiveSectionReturn.successor_rebase
#print axioms ConstitutiveSectionReturn.recurrent_successor_rebase
#print axioms ConstitutiveSectionReturn.recurrent_pairCurrent_rebase
#print axioms ConstitutiveSectionReturn.successor_extend
#print axioms ConstitutiveSectionReturn.Control.equal_scalar_distinct_deposits
#print axioms ConstitutiveSectionReturn.Control.new_site_contact_is_used
#print axioms ConstitutiveSectionReturn.rectangular_deposit
#print axioms ConstitutiveSectionReturn.additive_junction_input_differences
#print axioms ConstitutiveSectionReturn.additive_face_does_not_found_an_equalization_target
#print axioms ConstitutiveSectionReturn.additive_joined_passage_effect
#print axioms ConstitutiveSectionReturn.zero_partner_separates_passage_effect_from_equalization
#print axioms PassiveContact.contact_x_eq_y
#print axioms PassiveContact.contact_squared_distance
#print axioms PassiveContact.contact_nonexpansive
#print axioms PassiveContact.liftedContact_energy_preserved
#print axioms PassiveContact.liftedContact_passive
#print axioms TiedMapNextArrival.ActualNextArrival.paired_margin_identity
#print axioms TiedMapNextArrival.ActualNextArrival.matched_passiveCalibration_identity
#print axioms TiedMapNextArrival.ActualNextArrival.passiveCalibration_eq_joinedField
#print axioms TiedMapNextArrival.equal_widths_do_not_found_return
end Audit
