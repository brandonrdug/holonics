#import "../lib/holonics.typ": *

#let orientation = [
#pagebreak(weak: true)
= Orientation <orientation>

#local-contents((
  ([Five kinds of sentence], <orientation-sentences>),
  ([The research object], <orientation-object>),
))

This volume replaces a prospectus which catalogued possible papers but did not yet expose their
mathematical dependence. The present order follows the requested research sequence:
foundations (J1), exact formula and RH-facing mathematics (J4), comparative geometry and physics
(J5), learning and modern machine learning (J3), and machine realization (J2). The order is
epistemic, not chronological. A later measurement may depend on an earlier definition; an older
external theorem may enter only after the receiver which uses it has been declared.

The central methodological rule is simple: a shared word or visual resemblance never supplies a
mathematical identification. A relation crosses domains only through an explicit map whose
assumptions, receiver, and failure modes are stated. Thus a triangle may be an oriented boundary,
a parallel-path comparison, a local rewrite hinge, or a geometric simplex. These are compatible
readings only when the relevant structures have actually been supplied.

#provenance(
  kind: [Authorship and standing],
  body: [
    Brandon's direct constraints, hypotheses, intuitions, questions, and corrections open the
    research direction. Definitions, derivations, reconstructions, and proposed formal
    consequences written by Sol remain assistant contributions unless independently established.
    External theorems retain their original authorship. Machine claims are restricted to the
    named implementation or observation.
  ],
  source: [
    #link("../../RESEARCH/2026-07-21_THE_CONVERSATION_OPENS_THE_HYPOTHESIS_THE_RECORD_PRESERVES_WHO_SAID_WHAT.md")[
      The conversation opens the hypothesis; the record preserves who said what
    ].
  ],
  boundary: [
    Ratification preserves a presented relation at its stated boundary. It does not convert an
    analogy into identity, a modeling choice into theorem, or a predicted signature into a
    measurement.
  ],
)

== Five kinds of sentence <orientation-sentences>

The manuscript uses five compact grades. A *direct constraint or hypothesis* records Brandon's
stated boundary or research posture. A *working definition* fixes terminology for this calculus.
An *exact derivation* follows from written definitions or inherited mathematics. An
*implementation or measurement* reports source or runtime evidence at a named cut. An *open
bridge* names the mechanism, theorem, or observation still missing. These grades are orthogonal:
an exact derivation need not be physically realized, and an exact runtime observation need not
generalize.

#dependency-figure() <dependency-graph>

The solid portion of @dependency-graph is the theory developed in this volume. The rightmost
dashed edge is intentionally not a single conjecture. In the RH direction it contains analytic
continuation, a complete explicit-formula carrier, and positivity on an admissible test space. In
the physical direction it contains domain laws, units, covariance, limiting correspondence, and
discriminating measurement. Holonics supplies a language for keeping these obligations connected
without pretending that they have already been discharged.

== The research object <orientation-object>

#definition[
  A *relational ecology at a receiver* is a tuple
  $
    cal(E)_rho = (O, I, D, T; K_t, S_t, F_rho),
  $
  where $O$ is a population of actual occurrences, $I$ is oriented boundary incidence, $D$ is
  causal dependency, $T$ is local transport, $K_t$ is current material, $S_t$ is available
  Standing, and $F_rho$ is the face available to receiver $rho$. No component is inferred merely
  from equality of labels, coordinates, values, or rendered positions.
]

The word *holon* will therefore not name a permanently bounded object with intrinsic scale.
It names a receiver-relative consequential relation which may continue through changing
constituents. “Whole” and “part” are faces of a live construction, not absolute types attached to
atoms.

#source-note[
  Routine claim routing comes from #link("../../README.md")[the Soma claim and evidence index].
  The formal spine is reconstructed from #link("../../ELEMENTARY_MECHANICS.md")[Elementary
  Mechanics], #link("../../FORMULA.md")[the Formula], and the
  #link("../../RESEARCH/2026-07-13_THE_RELATIONAL_HOLONIC_CALCULUS.md")[Relational Holonic
  Calculus deposit]. These sources are evidence and provenance, not a second sequence of
  definitions beside the one fixed here.
]
]
