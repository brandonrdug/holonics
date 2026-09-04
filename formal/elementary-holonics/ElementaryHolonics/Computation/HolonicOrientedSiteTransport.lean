import ElementaryHolonics.Computation.HolonicDiffusionCharts
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
end Audit
