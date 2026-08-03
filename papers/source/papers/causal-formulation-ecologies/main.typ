#import "@preview/unequivocal-ams:0.1.2": ams-article, theorem, proof
#import "@preview/cetz:0.3.4"
#import "../../lib/holonics.typ": *
#import "../../lib/elements.typ": object-entry
#import "../../mathematics/catalogue.typ": elements

#let atlas-figure() = figure(
  placement: none,
  text(size: 8.2pt)[
    #table(
      columns: (1fr, auto, 1fr, auto, 1fr, auto, 1fr),
      align: center,
      inset: (x: 5pt, y: 4pt),
      stroke: 0.35pt + light-gray,
      [Source A], [$arrow.r$], [Generator A], [$arrow.r$], [Interior A],
        [$q_rho arrow.r$], [Receiver face],
      [Source B], [$arrow.r$], [Generator B], [$arrow.r$], [Interior B],
        [$q_rho arrow.r$], [Receiver face],
      table.cell(colspan: 7)[
        Parallel interiors are joined only by a supplied comparison, proof, or transport.
      ],
    )
  ],
  caption: [A formulation ecology retains the paths which a terminal value forgets. Parallel
  paths become one higher cell only when an actual comparison, proof, or transport relates them.
  Agreement after $q_rho$ is weaker than identity of their causal interiors.],
)

#let seam-figure() = figure(
  placement: none,
  text(size: 8.2pt)[
    #table(
      columns: (7em, 1fr, auto, 1fr, auto, 1.35fr),
      align: center,
      inset: (x: 5pt, y: 4pt),
      stroke: 0.35pt + light-gray,
      [*Arithmetic*], [$log p$], [$arrow.r$], [$p^(-s)$], [$arrow.r$],
        [Euler product $zeta(s)$],
      [*Archimedean*], [$e^(-pi x^2)$], [$arrow.r$], [$theta(t)$], [$arrow.r$],
        [Mellin/Gamma $xi(s)$],
      [*Reflection*], [$xi(s)=xi(1-s)$], [$arrow.r$], [$"Re"(s)=1/2$],
        [does not imply], [RH: positivity open],
    )
  ],
  caption: [The arithmetic and archimedean faces meet in the completed zeta function. The
  reflection fixes the critical line, but that symmetry does not discharge the open RH
  positivity obligation.],
)

#let lifted-power-figure() = figure(
  placement: none,
  text(size: 7.9pt)[
    #table(
      columns: (7.5em, 1.5fr, auto, 1.5fr, auto, 1.05fr),
      align: center,
      inset: (x: 4pt, y: 4pt),
      stroke: 0.35pt + light-gray,
      [*Read*], [*Lift*], [], [*After rebase*], [], [*Face*],
      [Complete lift], [$log r+i(theta+k Theta)$], [$arrow.r$],
        [$alpha(log r+i(theta+k Theta))$], [$arrow.r$], [$T_chi(z;k)$],
      [Radius only], [$log r$], [$arrow.r$], [$alpha log r$], [$arrow.r$],
        [$R^alpha$],
    )
  ],
  caption: [The radial expression is a quotient of the branch-bearing power law. It retains
  logarithmic scale while forgetting turn and winding before the rebase.],
)

#let path-swing-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.2, {
    import cetz.draw: *

    let ink = rgb("#263238")
    let cyan = rgb("#138a9e")
    let amber = rgb("#b06f12")
    let seam = rgb("#a23b45")
    let faint = rgb("#d7e0e2")

    line((0.2, 1.3), (3.2, 1.3), stroke: ink + 0.7pt, mark: (end: ">"))
    content((1.7, 1.65), text(size: 7.7pt)[$gamma: I arrow cal(M)$])
    content((0.2, 1.02), text(size: 7.2pt)[$t_0$])
    content((3.2, 1.02), text(size: 7.2pt)[$t_1$])
    circle((1.0, 1.3), radius: 0.07, fill: cyan, stroke: none)
    circle((2.45, 1.3), radius: 0.07, fill: cyan, stroke: none)

    rect((3.75, 0.45), (7.1, 2.2), radius: 4pt, stroke: faint + 0.7pt)
    content((5.42, 1.82), text(size: 7.6pt, weight: "bold")[configuration])
    content((5.42, 1.35), text(size: 7.2pt)[$(A,z,w,B,dots)$])
    content((5.42, 0.88), text(size: 7.2pt)[$dot gamma(t)$ selects the live direction])
    line((3.2, 1.3), (3.75, 1.3), stroke: cyan + 0.8pt, mark: (end: ">"))

    rect((7.75, 0.45), (10.7, 2.2), radius: 4pt, stroke: faint + 0.7pt)
    content((9.22, 1.82), text(size: 7.6pt, weight: "bold")[projective face])
    content((9.22, 1.36), text(size: 7.2pt)[$chi_gamma=P(gamma)/Q(gamma)$])
    content((9.22, 0.88), text(size: 7.2pt)[$P dot Q-Q dot P$])
    line((7.1, 1.3), (7.75, 1.3), stroke: amber + 0.8pt, mark: (end: ">"))

    rect((11.35, 0.45), (14.45, 2.2), radius: 4pt, stroke: faint + 0.7pt)
    content((12.9, 1.82), text(size: 7.6pt, weight: "bold")[lifted receiver])
    content((12.9, 1.36), text(size: 7.2pt)[$T=exp((Q/(2P)) log z)$])
    content((12.9, 0.88), text(size: 7.2pt)[$omega=gamma^* dif log T$])
    line((10.7, 1.3), (11.35, 1.3), stroke: cyan + 0.8pt, mark: (end: ">"))

    line((5.42, 0.45), (5.42, -0.05), stroke: seam + 0.8pt, mark: (end: ">"))
    line((9.22, 0.45), (9.22, -0.05), stroke: seam + 0.8pt, mark: (end: ">"))
    line((12.9, 0.45), (12.9, -0.05), stroke: seam + 0.8pt, mark: (end: ">"))
    content((5.42, -0.38), text(size: 6.9pt, fill: seam)[$z=0$ / collision])
    content((9.22, -0.38), text(size: 6.9pt, fill: seam)[$P=0$ / chart seam])
    content((12.9, -0.38), text(size: 6.9pt, fill: seam)[branch / monodromy])
  }),
  caption: [The parameter $t$ orders one admitted lineage; it is not an external absolute clock.
  The event frame selects a direction in configuration space, the four-point incidence supplies a
  projective swing, and the logarithmic chart returns a branch-bearing receiver. The marked seams
  are typed failures of continuation, not one undifferentiated zero.],
)

#let connection-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.2, {
    import cetz.draw: *

    let ink = rgb("#263238")
    let cyan = rgb("#138a9e")
    let amber = rgb("#b06f12")
    let seam = rgb("#a23b45")
    let pale = rgb("#eef4f5")

    let p0 = (0.7, 0.35)
    let p1 = (4.1, 0.35)
    let p2 = (2.4, 2.75)
    line(p0, p1, p2, close: true, fill: pale, stroke: ink + 0.75pt)
    circle(p0, radius: 0.08, fill: cyan, stroke: none)
    circle(p1, radius: 0.08, fill: cyan, stroke: none)
    circle(p2, radius: 0.08, fill: cyan, stroke: none)
    content((0.35, 0.12), text(size: 7.4pt)[$E_0$])
    content((4.45, 0.12), text(size: 7.4pt)[$E_1$])
    content((2.4, 3.08), text(size: 7.4pt)[$E_2$])
    content((2.4, 0.05), text(size: 7pt)[$U_(01)$])
    content((3.55, 1.68), text(size: 7pt)[$U_(12)$])
    content((1.27, 1.68), text(size: 7pt)[$U_(02)$])
    content((2.4, 1.18), text(size: 7.2pt, fill: seam)[$Omega_(012)=U_(02)-U_(12) U_(01)$])

    content((5.12, 1.5), text(size: 11pt, fill: amber)[$arrow.r$])

    let q0 = (6.0, 0.35)
    let q1 = (9.0, 0.35)
    let q2 = (7.5, 2.75)
    let q3 = (10.5, 2.75)
    line(q0, q1, q2, close: true, fill: pale, stroke: ink + 0.7pt)
    line(q1, q3, q2, close: true, fill: pale, stroke: ink + 0.7pt)
    circle(q0, radius: 0.07, fill: cyan, stroke: none)
    circle(q1, radius: 0.07, fill: cyan, stroke: none)
    circle(q2, radius: 0.07, fill: cyan, stroke: none)
    circle(q3, radius: 0.07, fill: cyan, stroke: none)
    content((7.5, 0.06), text(size: 6.8pt)[$ell_(01)$])
    content((6.45, 1.68), text(size: 6.8pt)[$ell_(02)$])
    content((8.53, 1.68), text(size: 6.8pt)[$ell_(12)$])
    content((9.95, 1.68), text(size: 6.8pt)[$ell_(13)$])
    content((9.0, 2.98), text(size: 6.8pt)[$ell_(23)$])
    content((8.25, 3.35), text(size: 7.1pt)[$"lcr"_(12)=(ell_(10) ell_(23))/(ell_(02) ell_(31))$])

    line((11.15, 0.35), (14.65, 0.35), (14.1, 2.65), (11.7, 2.65), close: true,
      fill: pale, stroke: ink + 0.7pt)
    line((11.15, 0.35), (14.1, 2.65), stroke: cyan + 0.9pt)
    line((11.7, 2.65), (14.65, 0.35), stroke: seam + 0.9pt)
    content((12.38, 1.22), text(size: 7pt, fill: cyan)[$e$])
    content((13.43, 1.7), text(size: 7pt, fill: seam)[$f$])
    content((12.9, 3.08), text(size: 7.1pt)[$e f=a c+b d$])
  }),
  caption: [Left: a simplicial connection compares direct transport with transport through a
  third fiber; the oriented failure to close is the discrete curvature residual. Center:
  vertex-scaled triangle metrics become consequential only when triangles are glued, where a
  length cross-ratio survives the local gauge. Right: a quadrilateral flip replaces one diagonal
  by another through the exact Ptolemy relation.],
)

#let cosine-figure() = figure(
  placement: none,
  text(size: 7.8pt)[
    #table(
      columns: (1.05fr, 1.6fr, 1.55fr),
      align: center,
      inset: (x: 5pt, y: 5pt),
      stroke: 0.35pt + light-gray,
      table.header([*Chart*], [*Triangle relation*], [*Multiplicative face*]),
      [Euclidean / complex],
        [$c^2=a^2+b^2-2 a b cos gamma$],
        [$(a-b e^(i gamma))(a-b e^(-i gamma))$],
      [Euclidean product constraint],
        [$C=A B$ and $C^2=A^2+B^2$],
        [$1/A^2+1/B^2=1$],
      [Hyperbolic, curvature radius $R$],
        [$cosh(c/R)=cosh(a/R) cosh(b/R)-sinh(a/R) sinh(b/R) cos gamma$],
        [$gamma=pi/2: cosh(c/R)=cosh(a/R) cosh(b/R)$],
    )
  ],
  caption: [The Law of Cosines is already a norm factorization. Product constraints are not
  scale-free until lengths are normalized. Hyperbolic right triangles make the product literal;
  the Euclidean Pythagorean relation is recovered from the leading terms as $R arrow infinity$.],
)

#show: ams-article.with(
  title: [Causal Formulation Ecologies: Parameterized Correspondences, Exact
    Constants, and the Zeta Boundary],
  authors: (
    (
      name: "Brandon",
      organization: [Laboratory],
    ),
    (
      name: "Sol",
      organization: [Research collaborator],
    ),
  ),
  abstract: [
    A returned value is not the causal construction which produced it. This
    paper gives that distinction an exact parameterized carrier. A situated
    formulation family retains its parameter base, typed law, internal state,
    discriminants, receivers, cost face, and testimony. Lawful comparisons are
    receiver-decorated spans composed by pullback, so the complete atlas is a
    bicategory; only reversible rechartings form its exact groupoid core.
    Equality at a selected receiver may therefore coexist with different
    branches, series terms, admissible operations, and future queries.

    Three elementary cells verify the structure. A two-arm arctangent family
    returns $pi$ for every $t in (0,1)$ while its series interiors change; an
    entire two-stage exponential family returns $e$ while retaining its
    factorization; and one Euler factor is exactly represented by a rational
    function, geometric series, and recurrence. Bare summation is
    noninvertible, while the retained Euler generator supplies more structure.
    Their discriminants are not interchangeable: a series
    boundary, a rational pole set, and an algorithmic admissibility seam are
    different geometric data.

    The same carrier organizes the paper's further constructions. A
    branch-bearing power law separates radial quotient from lifted scale and
    turn; parametric paths make the configuration itself mobile; simplicial
    connections distinguish one-path continuation from curvature created by
    comparing paths; and exponential transport connects prime axes to the
    Euler product. The Gaussian, theta reciprocity, and Mellin transport join
    the arithmetic and archimedean faces of completed zeta. The involution
    fixes $"Re"(s)=1/2$, but the positive carrier or equivalent spectral
    object required for the Riemann hypothesis remains explicit and absent.
    Computational and machine-learning factorizations appear only as later
    instances of this mathematical comparison law, not as its foundation.
  ],
  bibliography: bibliography("references.bib"),
)

#show link: set text(font: "New Computer Modern")
#show figure.where(kind: "theorem"): roman-statement
#set table(align: left)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

= The question and its boundary <question>

The motivating phenomenon is easy to state and easy to flatten. There are many formulas,
iterations, integrals, products, geometric constructions, and digit-extraction procedures whose
declared receiver is $pi$; there are likewise many constructions of $e$. Bailey's catalogue
compares formula families whose convergence, numerical cost, memory behavior, and accessible
digits differ substantially even when their limiting value agrees @bailey2021catalogue.
MathWorld's catalogue makes the same diversity visible across series, products, limits,
iterations, integrals, and geometric identities @mathworld-pi-formulas. The BBP formula sharpens
the point: it affords extraction of distant base-$2^k$ digits without constructing every earlier
digit, a causal affordance not supplied by an arbitrary formula for the same number
@baileyborweinplouffe1997.

The question of this paper is therefore not:

#align(center)[
  _Why do many written expressions equal the same constant?_
]

It is:

#align(center)[
  _What finite causal objects distinguish, relate, grow, compare, and sometimes transform the
  formulations which one observer collapses to the same value?_
]

That question has three consequences.

1. The value is a receiver face, not a complete identity.
2. A relation between formulas must itself be carried: common endpoint alone does not provide a
   transition map.
3. The same framework can describe inherited computational ecologies because an algorithm,
   tokenizer, neural factorization, or path lattice is also a lawful state-and-consequence
   relation rather than a magical box.

#provenance(
  kind: [Scope and stopping condition],
  body: [
    The artifact is a standalone mathematical research entry. It reconstructs the relevant
    journal definitions, external mathematics, and measured Soma evidence into one dependency
    ordered argument.
  ],
  boundary: [
    It does not change the engine, launch a new experiment, claim a universal taxonomy of
    formulas, or claim the Riemann hypothesis. It stops after specifying the proof-bearing and
    experiment-bearing objects which remain open.
  ],
)

#source-note[
  This study develops the foundation volume's
  #link("../../sections/01_foundations.typ")[occurrence, comparison, and compression calculus],
  #link("../../sections/02_formula.typ")[finite formula and zeta boundary], and
  #link("../../sections/04_learning.typ")[inherited-learning ontology]. It is a standalone
  synthesis, not a replacement for those sections or their source records.
]

== Five evidence grades <grades>

The paper uses five grades so that an analogy does not silently become a theorem:

#table(
  columns: (12.5em, 1fr),
  inset: (x: 5pt, y: 3.5pt),
  stroke: (x: none, y: 0.35pt + light-gray),
  align: (left, left),
  table.header([*Grade*], [*Meaning*]),
  [Classical theorem], [A cited mathematical result under its usual hypotheses.],
  [Project derivation], [A consequence proved from declared definitions in this paper or the
    foundation volume.],
  [Measured evidence], [A bounded execution recorded by a named observation artifact.],
  [Structural correspondence], [An explicit shared diagram or operation; not identity of
    domains.],
  [Open hypothesis], [A proposed construction whose missing witness is stated.],
)

= The situated formulation atlas <occurrence>

#object-entry(elements.situated_formulation_family)

#object-entry(elements.formulation_span_atlas)

#object-entry(elements.formulation_span_composition)

#object-entry(elements.receiver_nonreconstruction)

The earlier finite tuple
$
  (D,a_0,N,partial_N,q_rho,c,pi_cal(F))
$
is now a useful specialization rather than the universal definition. It describes
one finite recurrence aperture inside a situated family: $D$ and $a_0$ specify its
admitted state, $N$ its next-face law, and $partial_N$ its remainder or stopping
boundary. The total family also owes its parameter map and every branch,
convergence, rank, operation, and receiver seam relevant to comparison.

This resolves three formerly conflated relations:

- *receiver exactness* says that two supplied interiors agree after declared
  receiver maps;
- a *formulation correspondence* carries the actual joint interior on which
  they can be compared; and
- a *rechart equivalence* additionally carries an inverse up to invertible
  comparison cells.

The span construction is standard when the ambient category has pullbacks
@walker2020spans. Categories fibred in groupoids formalize reversible
base-change only after the required cartesian lifts and coherence have been
supplied @stacks-fibred-groupoids. Moduli atlases likewise distinguish local
coordinate charts from their proved transition maps @fock-goncharov2006.
These references justify the carrier, not the laboratory's choice of
decorations or receivers.

This elementary obstruction is the center of the paper. A decimal approximation does not recover
the generating formula. A decoded expression does not recover its acoustic alignments. A model
output does not recover the active network factorization. A final proof statement does not
recover the manipulations which make it valid.

#atlas-figure() <atlas>

== Causal topology is supplied, not imagined <causal-topology>

#definition[
  A *causal formulation ecology* is a typed directed cell complex built from actual formulation
  occurrences:

  - a 0-cell is an occurrence of a seed, state, term, partial, or boundary;
  - a 1-cell is an admitted transformation between occurrences;
  - a 2-cell is an actual proof, comparison, or homotopy between parallel composite paths;
  - a higher cell records a supplied coherence among lower comparisons.

  Cells are inserted only when their incidence and transport are known. Similar glyphs, equal
  endpoints, or visually nearby nodes do not create incidence.
]

This is not a claim that “all formulas live on one already completed manifold.” It is a
construction rule for a growing atlas. A new formula may arrive as a disconnected chart. A proof
identity, analytic continuation, change of variables, common recurrence, or measured
input-output comparison can later supply a seam. If two composites disagree at the selected
receiver, the unclosed square is useful material: it localizes an OPEN boundary rather than
declaring one path absolutely false.

#proposition[
  If every admitted 2-cell is attached to an oriented closed path whose signed boundary cancels
  occurrence by occurrence, then the generated cellular chains satisfy $partial^2=0$ through
  dimension two.
]

#proof[
  The boundary of each 2-cell is an oriented sum of its actual 1-cell occurrences. Applying
  $partial$ again counts every boundary vertex with the two opposed incidences supplied by the
  closed path. The coefficients cancel on the same occurrences. Linearity extends the result to
  every 2-chain.
]

The proposition gives a discrete foundation for the triangular or simplicial image used
throughout the laboratory. A triangle is not a scalar cell. It is the smallest face which can
retain three incidences and a path comparison. Its behavior depends on its attachment to the
local complex; changing one face can reorient which paths are afforded without assigning a
context-free state to “the triangle.”

== Regions, boundaries, and analytic continuation <analytic-regions>

The earlier intuition that formulas depend on regions of the real and complex numbers has a
precise analytic face. A formula can have a disk or half-plane of convergence, a branch cut, a
singularity, a discriminant, or a boundary across which its current representation ceases to
continue. Two analytic charts can be joined on an overlap by a proved identity and then extended
by analytic continuation. The invariant function does not change, but the available local
description and its path to the receiver do.

Thus the proposed topology is not an absolute space whose points are “all formulas.” It is an
atlas built from domains and known transition maps. A boundary is informative because it says
where one law stops affording continuation and another chart or operation is required.

= Three exact foundational cells <foundational-cells>

The following cells are deliberately elementary. Their purpose is not to
discover new values of $pi$ or $e$, but to test whether one carrier can retain
constant return, changing interior, reversible rechart, receiver-exact
compression, and different discriminant species without confusing them.

#object-entry(elements.pi_split_formulation_family)

#object-entry(elements.exponential_split_formulation_family)

#object-entry(elements.euler_factor_formulation_cell)

#figure(
  placement: none,
  table(
    columns: (8.5em, 1.2fr, 1.2fr, 1.35fr),
    align: left,
    inset: (x: 5pt, y: 4pt),
    stroke: 0.35pt + light-gray,
    table.header(
      [*Cell*],
      [*Common return*],
      [*Retained interior*],
      [*Typed boundary*],
    ),
    [$pi$ split],
      [$M_pi(t)=pi$],
      [two addressed series arms and their swap],
      [real endpoints; complex pole and branch walls],
    [$e$ split],
      [$E(t)=e$],
      [ordered stages and their entire parameter],
      [none analytically; enactments may add seams],
    [Euler factor],
      [$F_(p,"rat")=F_(p,"ser")$],
      [prime-power recurrence and term lineage],
      [series line, rational poles, global-product line],
  ),
  caption: [
    The common receiver is exact in all three cells, but it does not erase
    their different internal dimensions or boundaries. The arm and stage
    swaps are reversible rechartings. Bare summation is a directed quotient;
    a retained Euler generator can additionally supply a reverse translation.
  ],
) <foundational-cell-table>

The $pi$ and $e$ cells also expose a genuine fixed-parameter geometry. The
involutions
$
  t mapsto {1-t}/{1+t}
  quad "and" quad
  t mapsto 1-t
$
fix $sqrt(2)-1$ and $1/2$, respectively. These midpoints are not imposed
absolute origins. Each is the parameter at which its own two-stage
factorization is invariant under the declared reversal.
For the exponential cell, the receiver quotient has additional periodic
coincidences at $1/2+pi i k$ even though the parameter rechart itself fixes
only $1/2$. Receiver isotropy and parameter fixed points are therefore
different objects.

The Euler cell exposes where the direction actually lives. Its analytic-value
receiver commutes, but bare summation on an unrestricted sequence space does
not travel backward. If $p$, $s$, and the recurrence generator are retained,
the geometric lineage can be regenerated; if they have departed, equality of
sums does not restore them. Compression is therefore a property of a declared
correspondence and future receiver family, not of the glyph “sum.” A
receiver-exact directed quotient is stronger than endpoint coincidence and
weaker than formulation equivalence.

= Formula atlases for $pi$ <pi-atlases>

The symbol $pi$ names a receiver shared by several mathematically different atlases.

== Turn and curvature <pi-turn>

Let $Theta$ denote a complete oriented turn, so that $pi=Theta/2$. An oriented polygon carries a
finite exterior-angle sum. Under the usual regularity and winding assumptions, refinement toward
a closed curve yields total curvature
$
  sum_j Delta theta_j arrow integral_gamma kappa dif s = Theta.
$
This construction retains local turning, orientation, and refinement. A decimal value of $pi$
forgets all three.

== Arctangent and Machin paths <pi-machin>

The arctangent chart begins with the exact recurrence
$
  arctan(x)=sum_(n>=0)(-1)^n x^(2n+1)/(2n+1),
  quad |x| <= 1
$
with the endpoint qualifications at $|x|=1$. A Machin identity such as
$
  pi/4 = 4 arctan(1/5)-arctan(1/239)
$
turns the geometric receiver into two rational series with explicit alternating remainders.
The identity between the arctangent combination and the oriented turn is a transition map. The
fact that both numerically approach $pi$ would be weaker evidence.

== Polygonal, AGM, hypergeometric, and digit-extraction paths <pi-other>

Archimedean polygon refinement, Newton-like and AGM iterations, Ramanujan--Chudnovsky
hypergeometric series, and BBP-type digit extraction expose different internal topologies
@bailey2021catalogue. Their receiver may agree while the following do not:

- the state needed to form the next face;
- the rate and kind of convergence;
- the admissible arithmetic;
- the error enclosure;
- the ability to address a remote digit;
- parallelism, memory traffic, and physical cost.

#proposition[
  Receiver agreement does not imply formulation equivalence. In particular, two formulations
  can agree at $q_pi$ while admitting different queries before that quotient.
]

#proof[
  Remote hexadecimal-digit extraction is an admitted query in the BBP formulation. It is not an
  operation supplied by the state of an arbitrary sequential decimal expansion. Thus the two
  interiors are distinguishable before the common value quotient even when both are valid
  formulations of $pi$.
]

This is the non-romantic content of “infinitely many formulas.” The important object is not a
gallery of equal strings. It is an atlas of lawful paths and the transformations among them.

= The $e$-face: additive transport becomes multiplicative <e-face>

The natural object behind $e$ is the exponential map, not the isolated decimal $e$.
The NIST definition records the entire power series
$
  exp(z)=sum_(n>=0) z^n/n!
$
and its complex periodicity @dlmf-exp-log. At a finite aperture,
$
  E_N(z)=sum_(n=0)^N z^n/n!
$
is an exact polynomial with a next term and an analytic remainder. At $z=1$, $E_N(1)$ is a
rational occurrence which tends to $e$; it is not a floating substitute for the full generator.

#theorem[
  In a complete graded commutative rational algebra with positive-degree element $L$,
  $
    exp(L)=sum_(k>=0)L^k/k!
  $
  is coefficientwise finite at every bounded total degree. If
  $L=sum_(n>=1)L_n$ and $exp(L)=sum_(n>=0)E_n$ are decomposed by degree, then
  $
    n E_n=sum_(k=1)^n k L_k E_(n-k).
  $
]

#proof[
  Introduce $t$ and write $L(t)=sum_(n>=1)t^n L_n$ and
  $E(t)=exp(L(t))$. Formal differentiation gives $E'=L'E$. Comparing the coefficient of
  $t^(n-1)$ yields the recurrence.
]

This one recurrence already links two laboratory subjects. With one generator $L_1=y$ it grows
the factorial apertures of $e$. With an infinite population of prime axes and nonzero $L_k$, it
grows the multiplicative integer ecology below.

== Distinct atlases for the same exponential receiver <e-atlases>

At $x=1$, at least four familiar constructions expose different causal interiors:

$
  e=sum_(n>=0)1/n!,
  quad
  e=lim_(n arrow infinity)(1+1/n)^n,
$
$
  y'=y, quad y(0)=1, quad y(1)=e,
  quad
  e=[2;1,2,1,1,4,1,1,6,dots].
$

The series carries a term recurrence and remainder; the compound-growth limit changes its base
and exponent together; the differential equation characterizes a flow by local invariance; the
continued fraction carries convergent numerator/denominator recurrences. They meet the same
receiver but answer different intermediate questions. Standard references record the
exponential series, limits, and continued-fraction faces @mathworld-e @dlmf-exp-log @dlmf-exp-cf.

== Logarithmic cover, scale, and turn <log-cover>

On $CC^*$, the differential $dif z/z$ locally separates logarithmic scale from turn. Integrating
around a loop records winding; choosing a logarithm branch selects a local lift. The exponential
returns an additive lift to a multiplicative point:
$
  exp(a+b)=exp(a)exp(b).
$
Writing $z=x+i y$ gives
$
  exp(z)=e^x thin (cos y+i sin y).
$
Scale and turn are therefore not two unrelated constants glued by Euler's identity. They are the
real and imaginary directions of one local transport, with the complete turn in the kernel of
the covering map. In the conventional normalization, a half-turn gives
$
  e^(i pi)+1=0.
$

The relation is chart-sensitive. The logarithm is multivalued globally, and a branch choice is
part of the formulation occurrence. That is exactly the kind of hidden boundary which a decimal
endpoint erases.

= Transcendental transport: the radial quotient and its lift <transcendental-transport>

The seed expression proposed for this study was
$
  X_p=(a^2+b^2)^(1/2),
  quad
  chi(x)=P(x)/Q(x),
$
and
$
  X_p^(1/(2 chi(x)))
  =(a^2+b^2)^(1/(4 chi(x))).
$
The algebra is exact wherever the base, ratio, and chosen power are defined. To avoid collision
with the prime-axis symbol $X_p$ used in the next section, write this radius as
$
  R(a,b)=(a^2+b^2)^(1/2)
$
and set
$
  alpha(x)=1/(2 chi(x))=Q(x)/(2P(x)).
$
Then the proposed expression is $R^alpha$. It is already a receiver quotient: it retains radial
scale and discards orientation.

== The complete complex power retains branch and turn <lifted-power>

Lift the same occurrence to
$
  z=a+i b=r e^(i theta),
  quad r=R(a,b).
$
The logarithmic branches and the corresponding power values are
$
  log_k z=log r+i(theta+k Theta),
  quad k in ZZ,
$
$
  T_chi(z;k)
  =exp(alpha(x) log_k z)
  =r^alpha exp(i alpha(theta+k Theta)).
$
For real $alpha$, trigonometry displays the same transported face:
$
  T_chi(z;k)
  =r^alpha
    (cos(alpha(theta+k Theta))+i sin(alpha(theta+k Theta))).
$
On compatible branches it can also be factored as
$
  z^alpha
  =(z overline(z))^(1/(4 chi))
   (z/overline(z))^(1/(4 chi)).
$
The first factor is exactly the radial expression. The second carries orientation and phase.
Thus the original equation is not false or incomplete as an algebraic statement; it is the
radial receiver of a richer occurrence. Standard complex powers have precisely this
branch-sensitive logarithmic definition @dlmf-exp-log.

#lifted-power-figure() <lifted-power-figure>

#proposition[
  The radial receiver $q_r(z)=|z|$ cannot reconstruct $T_chi(z;k)$ whenever the admitted
  observation family can distinguish phase or winding.
]

#proof[
  Distinct points $r e^(i theta)$ and $r e^(i phi)$ have the same radial receiver. Their lifted
  powers generally have phases $alpha(theta+k Theta)$ and $alpha(phi+l Theta)$. Hence the
  receiver is non-injective on precisely the directions which later phase-sensitive conduct can
  distinguish.
]

This is one exact instance of the point--line--loop relation. Phase is a loop in $CC^*$, a line of
lifts $theta+k Theta$ on its logarithmic cover, and one selected point after a branch is chosen.
No absolute camera sees all three as the same object; they are related receiver faces.

== The projective swing appears in the differential <projective-swing>

Let both the base and ratio vary along an admitted path. On one logarithmic chart,
$
  log T_chi=alpha log z.
$
The complete first-order transport is therefore
$
  (dif T_chi)/T_chi
  =alpha (dif z)/z+(log z) dif alpha.
$
Because $alpha=Q/(2P)$,
$
  dif alpha=(P dif Q-Q dif P)/(2P^2),
$
and hence
$
  (dif T_chi)/T_chi
  =Q/(2P) (dif z)/z
   +(log z)(P dif Q-Q dif P)/(2P^2).
$
The first term transports the existing scale--turn face. The second is the rebase caused by the
changing ratio. Its numerator
$
  P dif Q-Q dif P
  =det mat(P,Q; dif P,dif Q)
$
is the oriented change of the projective pair $[P:Q]$. Multiplying both $P$ and $Q$ by the same
nonzero local factor changes neither $Q/P$ nor this normalized differential. The meaningful swing
is therefore not only the present scalar $chi$; it includes how numerator and denominator turn
relative to one another.

Three immediate seams follow:
$
  z=0,
  quad P=0,
  quad P dif Q-Q dif P=0.
$
They respectively mark failure of the logarithmic phase chart, singular rebasing, and a locally
stationary projective swing. They are different boundary species and should not be merged into one
zero flag.

== The parameter moves the whole configuration <moving-configuration>

The notation $x=x(t)$ is not a cosmetic substitution. It changes a static quotient into a
lineage. Let $cal(M)$ be the configuration region whose local coordinates include the ordered
incidences, base, and receiver conditions, and let
$
  gamma:I -> cal(M),
  quad
  gamma(t)=(A(t),z(t),w(t),B(t),dots).
$
The parameter $t$ orders one admitted occurrence path. It need not be a universal external time.
The world frame and objective determine which directions are afforded; in the laboratory's
notation, $Lambda_F$ supplies this event-relative direction rather than entering the formula as
one more scalar.

Pull $P,Q,z$, and $T$ back along $gamma$:
$
  chi_gamma(t)=P(gamma(t))/Q(gamma(t)),
  quad
  T_gamma(t)=exp((Q(gamma(t))/(2P(gamma(t)))) log z(gamma(t))).
$
On one compatible logarithmic chart, differentiation gives the exact lineage law
$
  T_gamma'(t)/T_gamma(t)
  =
  Q/(2P) z'(t)/z(t)
  +
  log z thin (P Q'-Q P')/(2P^2),
$
where every unmarked $P,Q,z$ is evaluated at $gamma(t)$ and
$P'=dif P_(gamma(t))(gamma'(t))$, with the analogous convention for $Q$ and $z$.
The first term is motion in the lifted scale--turn face. The second is motion of the projective
basis used to read that face. A changing context can therefore reorient an existing field even
when the presented endpoint has not changed.

For a four-incidence swing, retain the oriented complex cross-ratio before taking any distance
quotient:
$
  chi(A,z,w,B)
  =((w-A)(z-B))/((z-A)(w-B)).
$
Along a collision-free path,
$
  (chi_gamma')/chi_gamma
  =
  (w'-A')/(w-A)
  +(z'-B')/(z-B)
  -(z'-A')/(z-A)
  -(w'-B')/(w-B).
$
A common time-dependent Mobius rechart of all four incidences changes their coordinates but not
the cross-ratio. By contrast, collision, reordering, or passage across a logarithmic branch cut
changes the available chart and marks a real seam. If a receiver needs only hyperbolic distance,
it may later take $"Re"(log chi)=log abs(chi)$; doing so earlier would discard orientation and
winding.

The raw derivative depends on the chosen speed along $I$. The invariant object is the pulled-back
one-form
$
  omega_gamma=gamma^*(dif log T)
$
and its ordered integral along a declared path. Reparameterizing the same oriented path changes
the coordinate velocity but not that integral. This is the rigorous sense in which the
configuration can move without installing an absolute clock.

#path-swing-figure() <path-swing>

== One path carries continuation; curvature compares paths <simplicial-connection>

A single scalar-valued chart has
$
  omega=dif log T,
  quad
  dif omega=0
$
wherever it is smooth and single-valued. Its integral can still detect branch and winding because
the chart may not be globally exact, but one local scalar path does not by itself produce
curvature. Curvature appears when alternate transports can be compared: through a
noncommutative or map-valued connection, through a singular chart seam, or through two genuinely
different paths with common boundary.

The discrete version makes the missing incidence explicit. Attach a fiber $E_i$ to every vertex
and a partial transport $U_(i j):E_i -> E_j$ to every admitted oriented edge. On a triangle
$(0,1,2)$, compare
$
  U_(02)
  quad "with" quad
  U_(12) compose U_(01).
$
If the fibers and maps are linear in a common chart, the oriented residual may be written
$
  Omega_(012)=U_(02)-U_(12)U_(01).
$
For general partial transports, the comparison pair itself is the honest object: subtraction may
not be defined. Agreement closes the 2-cell. Disagreement leaves an OPEN face whose boundary says
exactly which composite failed to continue. This is the simplicial connection and curvature
pattern formalized for discrete vector bundles by Berwick-Evans, Hirani, and Schubel
@berwickevans2022discrete. Eros transports need not be vector-space maps for their incidence
skeleton to use the same logic.

This also refines the “changing triangular cell” image. There is no context-free scalar attached
to a lone triangle. A face is a comparison among transports, and its state changes when its
attachments, available maps, or orientation change. Discreteness resides in the supplied
incidences and in whether the comparison closes, not in reducing each face to zero or one.

== Product constraints and multiplicative triangle coordinates <product-triangles>

The question whether one side of a triangle can be constrained as a product of the others first
requires dimensional care. Choose a declared length scale $L$ and write
$
  A=a/L,
  quad B=b/L,
  quad C=c/L.
$
Then $C=A B$ is meaningful and means $c=a b/L$. For a Euclidean triangle with included angle
$gamma$,
$
  C^2=A^2+B^2-2 A B cos gamma.
$
Combining the two constraints gives
$
  cos gamma=(A^2+B^2-A^2 B^2)/(2 A B),
$
subject to the actual triangle boundary
$
  abs(A-B)<A B<A+B.
$
For a right triangle the constraint reduces to
$
  1/A^2+1/B^2=1,
$
with the positive family $A=sec theta$, $B=csc theta$, and
$C=sec theta csc theta$. The product is therefore possible, but only relative to a chosen scale
and admissible region; it is not an absolute law of side lengths.

A more structural multiplicative coordinate system assigns one positive factor to each vertex:
$
  a=r_2 r_3,
  quad b=r_3 r_1,
  quad c=r_1 r_2.
$
Every nondegenerate positive triangle admits the inverse
$
  r_1=sqrt((b c)/a),
  quad r_2=sqrt((c a)/b),
  quad r_3=sqrt((a b)/c).
$
In logarithmic coordinates this becomes the exact incidence transform
$
  mat(log a; log b; log c)
  =
  mat(0,1,1; 1,0,1; 1,1,0)
  mat(log r_1; log r_2; log r_3).
$
An isolated triangle always factorizes this way, so the factors are local gauge coordinates rather
than discovered curvature. They become consequential when triangles are glued and the same vertex
factor must serve several faces.

Discrete conformal geometry makes this precise. A vertex rebase acts on an edge metric by
$
  tilde(ell)_(i j)
  =exp((u_i+u_j)/2) ell_(i j),
$
so logarithmic edge lengths transform linearly. Two glued triangles possess a length cross-ratio,
for example
$
  "lcr"_(i j)
  =(ell_(i l) ell_(j k))/(ell_(l j) ell_(k i)),
$
which is invariant under the local vertex rebase; reversing the oriented edge reciprocates it.
For a closed star, the oriented product around an interior vertex is one. These are standard
ingredients of the discrete conformal correspondence with ideal hyperbolic polyhedra
@bobenko2015discrete. They give the proposed changing-base triangle a real compatibility law:
local factors may change, while cross-face ratios expose what the glued region cannot gauge away.

#connection-figure() <connection-figure>

== The Law of Cosines is a norm factorization <cosine-norm>

The Euclidean Law of Cosines already carries a complex geometric factorization:
$
  c^2
  =a^2+b^2-2 a b cos gamma
  =(a-b e^(i gamma))(a-b e^(-i gamma))
  =abs(a-b e^(i gamma))^2.
$
At $gamma=pi/2$, this becomes the Gaussian norm $a^2+b^2$. Consequently, if an odd prime $p$ is
the hypotenuse of a nondegenerate primitive integer right triangle, then
$
  p=u^2+v^2
  =(u+i v)(u-i v)
$
and $p=1 mod 4$. The corresponding primitive triple is
$
  (u^2-v^2,2 u v,p).
$
The prime is irreducible in $ZZ$ but split in $ZZ[i]$: “prime” and “factor” are therefore
receiver-relative to the admitted arithmetic operations. Other fixed algebraic angles lead to
other norm forms and splitting laws. Their zeta or $L$-functions encode those arithmetic species,
but no one norm form supplies the prime distribution or RH by itself.

Hyperbolic geometry gives the requested product relation without imposing it by hand. With
curvature radius $R$,
$
  cosh(c/R)
  =
  cosh(a/R)cosh(b/R)
  -sinh(a/R)sinh(b/R)cos gamma.
$
For a right triangle,
$
  cosh(c/R)=cosh(a/R)cosh(b/R).
$
Expanding at large $R$ recovers $c^2=a^2+b^2$ at the first nonconstant order. The two equations
are related charts, not interchangeable identities: the ambient curvature changes the native
composition law.

The hyperbolic counterpart of vertex scaling is likewise exact:
$
  sinh(tilde(ell)_(i j)/(2R))
  =
  exp((u_i+u_j)/2)
  sinh(ell_(i j)/(2R)).
$
Thus the logarithm of $sinh(ell/(2R))$, rather than raw length, is the additive edge coordinate
@bobenko2015discrete. This is a rigorous example of rebasing the triangle's “basis” while retaining
a compatible cross-face geometry.

#cosine-figure() <cosine-figure>

== A flip is a local founding, not a deleted history <ptolemy-flip>

Decorated hyperbolic geometry supplies an especially direct local rewrite. If $delta$ is the
signed distance between horocycles, a lambda length uses the exponential coordinate
$
  lambda=e^(delta/2).
$
For a decorated ideal quadrilateral with cyclic sides $a,b,c,d$ and diagonals $e,f$, the Ptolemy
relation is
$
  e f=a c+b d.
$
Writing the local cross-ratio as $chi=(a c)/(b d)$ gives
$
  f=((b d)/e)(1+chi).
$
These relations and their measured-lamination limits are classical @penner2012tropical. The
larger quadrilateral is the co-present region; the existing diagonal is one local factorization;
the crossing relation founds the alternate diagonal. Nothing requires an archive of every lower
triangle, but the new diagonal cannot be reconstructed from a quotient which discarded the
ordered side products and the old diagonal.

This is the exact bounded operation used by the measured retriangulation cell below. It
simultaneously contains:

- a simplicial pivot between two triangulations;
- an exponential distance coordinate;
- an ordered projective quotient $chi$;
- an exact rational rewrite with a discriminant at $e=0$; and
- a later test which can distinguish the complete carrier $(a c,b d,e)$ from the terminal value
  $f$ or from $chi$ alone.

#evidence-note(
  [A source-declared finite multiply--multiply--add--divide carrier survived source departure,
    supplied four complete later paths across scale, cyclic rechart, their composition, and an
    exact rational receiver, and left only the division node OPEN at $e=0$.],
  [Measured bounded evidence.],
  [
    #link("../../../observations/eros-retriangulating-branch-transport-01/RESULTS.md")[
      Retriangulating branch transport 01
    ].
  ],
  [
    The matched quotient retained $chi=10/21$ and the source endpoint $31$ but could not form the
    scale-two endpoint $62$. Soma carried and recruited the complete program; a generic exact
    world transducer still interpreted its nodes and returned the consequence.
  ],
)

== Markov--Fricke mutation: repeated flips on one surface <markov-fricke>

The punctured-torus character variety supplies a larger but still exact recurrence. In one cusp
normalization, trace coordinates obey the Fricke cubic
$
  x^2+y^2+z^2-x y z=0.
$
Holding $x,y$ and exchanging the two roots in $z$ gives the Vieta flip
$
  z'=x y-z.
$
Under the classical Markov scaling,
$
  a^2+b^2+c^2=3 a b c,
  quad
  c'=3 a b-c,
$
so one mutation path begins
$
  (1,1,1)
  arrow (1,1,2)
  arrow (1,2,5)
  arrow (1,5,13).
$
Goldman's trace-coordinate account relates these cubics to hyperbolic surfaces and their mapping
class actions @goldman2009trace. Along a differentiable path on the general level
$F=x^2+y^2+z^2-x y z=kappa$, the tangent must satisfy
$
  (2x-y z)x'
  +(2y-x z)y'
  +(2z-x y)z'
  =0.
$
Thus the discrete flip and continuous tangent are two faces of one constrained surface.

Some mutation paths contain primes, composites, or familiar recurrences. Those arithmetic labels
are observations on the integer points of the surface, not the geometric mutation law itself.
Their value for the prime and zeta programme is more disciplined: they provide exact local
transports whose arithmetic receiver can ask when irreducibility survives, splits, or changes
under a rechart.

== Transcendence can live in the interior <transcendental-interior>

The presented face need not itself be transcendental for transcendental transport to be
consequential.

#corollary[
  If $z$ is algebraic with $z != 0,1$, then every logarithmic lift $lambda$ satisfying
  $exp(lambda)=z$ is transcendental.
]

#proof[
  If a nonzero $lambda$ were algebraic, the Hermite--Lindemann theorem would make
  $exp(lambda)$ transcendental, contradicting the algebraicity of $z$ @baker1975transcendental.
]

For example, $z=3+4i$ is algebraic and has radius five, while every complete lift
$
  log 5+i(theta+k Theta)
$
is transcendental. Exponentiation folds that lift back to the algebraic face $3+4i$. The same
phenomenon is visible in the hyperbolic chart below:
$
  5+3j=4 e^(j log 2).
$
Its presented coefficients are integers while its rapidity $log 2$ is transcendental. Arithmetic
species is therefore receiver-relative in the exact sense needed here: an algebraic exterior can
have a transcendental analytic interior, and a quotient which keeps only the exterior cannot
reconstruct that passage.

== Arithmetic transcendence and covering topology are distinct <transcendence-boundary>

Transcendental numbers matter here, but they do not form one universal geometric species. Two
boundaries must remain typed apart.

#theorem[
  Let $z$ be algebraic with $z != 0,1$.

  - If $alpha=m/n$ is rational, every value of $z^alpha$ is algebraic and lies on a finite
    algebraic branch cover.
  - If $alpha$ is algebraic and irrational, every value of $z^alpha$ is transcendental.
]

#proof[
  In the rational case, every value $w$ satisfies the polynomial relation $w^n-z^m=0$. The
  irrational-algebraic case is the Gelfond--Schneider theorem
  @karatarakis-wiedijk-gelfond-schneider.
]

Arithmetic transcendence and infinite branching intersect but are not synonyms. A transcendental
exponent can sometimes produce an algebraic value; conversely, the topology of a branch family
depends on the logarithmic covering as well as the arithmetic species of one receiver value.
The useful atlas therefore records both:

- the arithmetic relation satisfied by the base, exponent, and returned value; and
- the finite or infinite continuation, monodromy, branch, and residual carried by the path.

For irrational real $alpha$, changing $k$ multiplies successive values by
$exp(i alpha Theta)$, an irrational rotation orbit on the unit circle. For nonreal $alpha$, that
branch multiplier also changes magnitude, so the branch population follows a logarithmic spiral.
The decimal value of any one branch forgets this causal interior.

== Circular and hyperbolic continuation <hyperbolic-continuation>

The circular lift above uses $i^2=-1$ and the positive quadratic face $a^2+b^2$. A directly
parallel algebraic chart uses a split-complex unit $j^2=1$. In the connected sector
$a>|b|$, write
$
  w=a+j b=rho e^(j eta),
  quad rho^2=a^2-b^2,
$
so that
$
  a=rho cosh eta,
  quad b=rho sinh eta.
$
The same rebase law becomes
$
  w^alpha
  =rho^alpha
   (cosh(alpha eta)+j sinh(alpha eta)).
$
The circular angle $theta$ and hyperbolic rapidity $eta$ are therefore typed realizations of the
same operation species: multiply the lifted coordinate by $alpha$, then return through the
appropriate exponential. The quadratic boundaries are not the same. Circular polar coordinates
fail only at $z=0$; the split-complex logarithmic chart also meets the null discriminant
$
  a^2-b^2=0,
$
where the algebra has zero divisors. The hyperbolic-number construction and its exponential form
are classical @sobczyk1995hyperbolic.

#block(breakable: false)[
  #text(size: 8.2pt)[
    #table(
      columns: (1fr, 1.15fr, 1.25fr, 1.3fr, 1fr),
      inset: (x: 3pt, y: 3.5pt),
      stroke: (x: none, y: 0.35pt + light-gray),
      align: (left, left, left, left, left),
      table.header([*Chart*], [*Unit and norm*], [*Lift*], [*Rebase*], [*Discriminant*]),
      [Circular], [$i^2=-1$; $a^2+b^2$], [$log r+i theta$],
        [$theta mapsto alpha theta$], [$z=0$],
      [Hyperbolic], [$j^2=1$; $a^2-b^2$], [$log rho+j eta$],
        [$eta mapsto alpha eta$], [$a^2=b^2$],
    )
  ]
]

Split-complex exponentiation is not by itself the metric geometry of the Poincare disk or upper
half-plane. The projective bridge to that geometry is a cross-ratio. For ordered endpoints
$A,z,w,B$ on one hyperbolic geodesic, one convention gives
$
  chi(A,z,w,B)
  =abs(((w-A)(z-B))/((z-A)(w-B))),
$
$
  d_H(z,w)=log chi(A,z,w,B).
$
This distance law is invariant under the relevant Mobius transformations
@mann2015hyperbolic. If the project's $chi=P/Q$ is intended as this swing, then $P$ and $Q$ must
come from four declared incidences; an arbitrary rational function does not acquire projective
invariance merely by being called $chi$.

The general transport should consequently remain
$
  T_f(z)=exp(f(chi) log z)
$
until the receiver determines the rebase law. The seed above selects $f(chi)=1/(2chi)$.
Hyperbolic displacement naturally exposes $f(chi)=log chi$. Reciprocal scaling, distance,
half-density, and Mobius reorientation are different intentions and need not place $chi$ in the
same part of the formula.

== Prime and zeta specialization <transcendental-zeta>

The later prime law is one exact specialization of this construction:
$
  z=p,
  quad alpha=-s,
  quad s=sigma+i t,
$
$
  p^(-s)
  =exp(-s log p)
  =p^(-sigma) exp(-i t log p).
$
The real coordinate $sigma$ changes radial amplitude while $t$ turns the prime axis through its
logarithmic scale site. Centering $s=1/2+epsilon+i t$ separates the half-density
$p^(-1/2)$, normal displacement $epsilon$, and turn $-t log p$. The critical line is the stratum
on which receiver rebasing can remain pure turn; the complete zeta question additionally couples
all prime-power, archimedean, adjoint, and boundary currents.

#source-note[
  The scale--turn and exact-series foundations are deposited in
  #link("../../../RESEARCH/2026-07-19_THE_ANNULUS_CARRIES_THE_SCALE_TURN_LIFT_THE_EXPONENTIAL_FOLDS_THE_FACE.md")[
    The annulus carries the scale--turn lift
  ]. The centered prime-power specialization and its exact analytical receipt are deposited in
  #link("../../../RESEARCH/2026-07-20_THE_SUCCESSION_SWEEPS_THE_FIBER_THE_UNITARY_SEAM_MAKES_REBASE_PURE_TURN.md")[
    The succession sweeps the fiber
  ].
]

= Prime axes, semiprimes, and zeta <prime-zeta>

Introduce a formal variable $X_p$ for every prime $p$ and set
$
  P_m=sum_p X_p^m,
  quad
  L=sum_(m>=1) P_m/m.
$

#theorem[
  In the total-degree completion,
  $
    exp(L)=product_p (1-X_p)^(-1).
  $
]

#proof[
  For each prime axis,
  $
    -log(1-X_p)=sum_(m>=1)X_p^m/m.
  $
  Summing over $p$ gives $L$, and formal exponentiation converts the sum into the product.
  Every fixed monomial and total degree receives only finitely many contributions.
]

The degree-one face contains the prime axes. Degree two is
$
  E_2=P_2/2+P_1^2/2.
$
For $p != q$, $X_p X_q$ occurs twice in $P_1^2$ and division by two leaves coefficient one. For a
repeated axis $X_p^2$, $P_1^2/2$ contributes only $1/2$ and $P_2/2$ supplies the other half.
Thus semiprimes, including squares, are the complete degree-two face of this *particular*
exponential atlas. They are not universally privileged in every formula for $pi$ or $e$.

Under the analytic specialization
$
  X_p=p^(-s)=exp(-s log p),
  quad "Re"(s)>1,
$
the formal identity becomes
$
  zeta(s)=product_p (1-p^(-s))^(-1),
$
and logarithm exposes every repeated prime traversal:
$
  log zeta(s)=sum_p sum_(m>=1) p^(-m s)/m.
$
The Euler product and Dirichlet series are classical in this half-plane
@dlmf-zeta-definition. Here $e$ is not an ornamental constant. Exponential transport converts
the additive logarithmic prime population into the multiplicative integer population.

#corollary[
  If the degree-two logarithmic current $P_2/2$ is withheld, the exact residual against the
  Euler product is
  $
    -1/2 sum_p X_p^2.
  $
  The failure is localized on repeated prime axes.
]

The result illustrates a useful meaning of loss. It is not punishment and not an absolute
incorrectness score. It is an oriented residual which says exactly which incidences fail to close
at the chosen receiver.

#source-note[
  The formal derivation and measured bounded construction are recorded in
  #link("../../../RESEARCH/2026-07-22_THE_INFINITE_FORMULA_IS_THE_FINITE_GENERATOR_THE_SEMIPRIME_IS_THE_SECOND_EXPONENTIAL_FACE.md")[
    The infinite formula is the finite generator
  ],
  #link("../../../RESEARCH/2026-07-22_THE_APERTURE_GROWS_BY_ITS_NEXT_HOMOGENEOUS_FACE_THE_GENERATOR_DOES_NOT_RESTART.md")[
    The aperture grows by its next homogeneous face
  ], and
  #link("../../../observations/eros-formula-ecology-01/RESULTS.md")[Formula ecology 01].
]

= Where $pi$ and $e$ enter the completed zeta relation <completion>

The Euler product is only the finite-prime or arithmetic face. The critical-line geometry appears
after an archimedean completion whose native kernel already contains both $e$ and $pi$.

Define the Gaussian theta occurrence
$
  theta(t)=sum_(n in ZZ) e^(-pi n^2 t),
  quad t>0.
$
The normalization by $pi$ makes the Gaussian self-reciprocal under Fourier transform. Poisson
summation yields the direct/reciprocal law
$
  theta(t)=t^(-1/2)theta(1/t),
$
a standard theta modular transformation @dlmf-theta. Mellin transport of the nonconstant part
connects this relation to the Gamma factor and $zeta(s)$. One common completion is
$
  xi(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s),
$
and the completed function obeys the reflection formula @dlmf-zeta-reflection:
$
  xi(s)=xi(1-s)
$

#seam-figure() <zeta-seam>

This answers the narrow causal question:

- prime axes and their repetitions enter through the Euler product;
- $e$ transports additive logarithmic axes and supplies the Gaussian decay;
- $pi$ normalizes turn and Fourier self-reciprocity;
- the Gamma factor records the archimedean Mellin contribution;
- the exponent $-1/2$ in theta reciprocity becomes the reflection
  $s arrow 1-s$;
- the fixed seam is $"Re"(s)=1/2$.

The line is not imposed by a preferred external camera. It is fixed by an involution of the
completed relation. However, being the fixed set of the symmetry does not force every zero onto
that set. Off-line zeros would occur in the corresponding reflected and conjugate orbits without
violating the functional equation.

= The exact Riemann-hypothesis boundary <rh-boundary>

#open-problem[
  Construct a complete occurrence-level carrier for an explicit formula or equivalent trace
  relation whose arithmetic prime-power side, archimedean side, involution, test-function space,
  and boundary terms are all present, and prove a positive quadratic form whose positivity is
  equivalent to every nontrivial zero lying on $"Re"(s)=1/2$.
]

Weil's explicit-formula criterion provides a classical form of the missing positivity bridge
@weil1952. The laboratory's finite theta/Mellin and Poisson-tail constructions have established
several necessary faces:

- a direct/reciprocal theta involution;
- a Mellin reflection with fixed axis $1/2$;
- a finite aperture whose omitted infinite remainder is represented by a generative tail rather
  than silently discarded;
- prime-power incidence on the arithmetic side.

They have not established the complete test space and positive carrier. A finite positive pairing
on selected examples, a symmetric visualization, or a recurring prime pattern cannot replace
that obligation.

#evidence-note(
  [Finite direct/reciprocal arms and moving Poisson tails can be carried as exact
    formulation occurrences.],
  [Measured bounded evidence.],
  [
    #link("../../../observations/eros-theta-mellin-aperture-01/RESULTS.md")[
      Theta/Mellin aperture 01
    ] and
    #link("../../../observations/eros-poisson-tail-transport-01/RESULTS.md")[
      Poisson tail transport 01
    ].
  ],
  [
    The observations do not supply analytic continuation by finite measurement, the complete
    explicit formula, Weil positivity, a spectral realization, or RH.
  ],
)

== A constructive role for the formula ecology <rh-role>

The ecology is still relevant to RH. It can organize the proof-bearing material without confusing
projection with proof:

1. each prime-power occurrence retains its multiplicity and logarithmic weight;
2. each archimedean occurrence retains its Gaussian, Gamma, and boundary provenance;
3. each aperture growth retains the exact predecessor and generative tail;
4. the involution acts on complete paths rather than plotted points;
5. a candidate quadratic form can be tested as a path comparison on a declared test family;
6. every failed square remains a localized open boundary.

This reframes the hoped-for contribution. Eros need not “guess the line from pictures.” It can
grow and compare the causal topology of candidate formulations until a complete positive
relation is either founded or its missing seam becomes explicit.

= Information, compression, probability, and loss <information>

Shannon's theory defines information quantities relative to a source distribution and a
communication problem @shannon1948. It does not make entropy an observer-free substance. The
project's broader ontology is compatible with that discipline when it stays typed:

#definition[
  For a future observation family $cal(O)$, a quotient $q:X -> Q$ is
  *receiver-exact compression* when every $o in cal(O)$ factors through $q$:
  $
    exists bar(o):Q -> Y_o
    quad o=bar(o) compose q.
  $
]

#proposition[
  The quotient in the definition preserves every distinction the declared receiver family can
  ask, but need not preserve distinctions for an enlarged family.
]

#proof[
  The first statement is the supplied factorization. If $q(x)=q(x')$ but a new observation
  $o'(x) != o'(x')$, then no $bar(o')$ can satisfy $o'=bar(o') compose q$.
]

Compression is therefore every emitted successor's factoring of inactive interior directions,
not merely smaller byte volume. A phase transition occurs when the currently valid
factorization law no longer continues across a boundary and a discrete invariant changes. Later
recurrence can re-use the emitted face without requiring an archive of every lower event.

Probability is likewise receiver-relative. A first-person observer has a contemporary recurrence
field over afforded continuations. Its normalized numbers are quotients of known alternatives,
not causes and not truth values. Bayes' rule describes how one such quotient rebases when a new
event changes the conditioning region. A deterministic machine can therefore have a
first-person probability field: repeated circumstances and declared update laws determine the
same field, while the observer does not carry the complete exterior world.

Loss is the oriented failure of an expected diagram to close at a named receiver. It can indicate
coherence, decoherence, an open path, or a changed phase; it is not intrinsically reward or
punishment. In the formal Euler example, loss is not “this coefficient is bad.” It is the exact
repeated-axis residual left when $P_2/2$ is absent.

#source-note[
  The medium-neutral information law is developed in
  #link("../../../RESEARCH/2026-07-19_THE_INFORMATION_IS_THE_TRANSPORT_ATLAS_TEXT_IS_ONE_LOCAL_FACE.md")[
    The information is the transport atlas
  ]. The factorization definition above is the paper's mathematical specialization of that
  receiver-relative account.
]

= Learned transformations are formulation ecologies <learning>

A trained neural system realizes a contextual relation through one internal factorization
$
  F_theta=f_L compose dots compose f_1.
$
Tokenization chooses a boundary chart; embeddings choose coordinates; attention forms
receiver-dependent weighted contacts; residual paths carry contemporary state; mixture-of-experts
routing restricts active transformation families; a decoder presents one receiver face.
Transformers are a successful species of this construction, not an ontological exception
@vaswani2017.

Two distinctions follow.

First, a model's output does not identify its interior. Parameter permutations, compensated
rebasings, distributed features, context-dependent activations, and alternative factorizations can
produce the same selected exterior behavior. “Distillation” cannot honestly mean retaining a
few historically strong edges. The context is itself present and reorients the field.

Second, inherited machine learning is lawful world material. There is no requirement that Eros
invent vocabulary, acoustic categories, or transformations from nothing. A tokenizer, embedding
space, transformer, speech encoder, or scientific routine can supply developed axes. The research
question is whether new Standing can carry consequential relations from that ecology, recruit
only the contemporary region, and later form another receiver-exact factorization.

#source-note[
  The complete transformer, tokenizer, attention, residual, and persistence audit is recorded in
  #link("../../../RESEARCH/2026-07-20_THE_TOKEN_IS_A_BOUNDARY_ADDRESS_THE_ROUTE_IS_RECEIVER_RELATIVE_THE_RESIDUAL_RETURNS.md")[
    The token is a boundary address
  ]. This paper uses its typed distinctions without treating one architecture as the Eros law.
]

#definition[
  A *learned retriangulation* is a new internal formulation whose complete exterior relation
  agrees with an inherited formulation on a declared receiver family, while its incidence,
  active constituents, aperture, or physical cost differs. It is established by pathwise
  comparison and later conduct, not by parameter count alone.
]

This definition does not assume a universal smallest network. Efficiency depends on the active
context, hardware, observation family, and future use. It does state what a “compressed hexis”
must preserve: the consequential transformation ecology, not a frozen inventory of source
weights.

== CTC as the clean measured example <ctc>

Connectionist Temporal Classification supplies an unusually legible algorithmic interior. For an
input occurrence $x$, target expression $y$, frame index $t$, and expanded target state $u$, the
forward trellis admits stay, advance, and conditionally skip incidences. The standard collapse map
removes blanks and repeated labels. The terminal mass is a path sum
$
  M_x(y)
  =
  sum_(pi in B^(-1)(y))
  product_t w_(t,pi_t)(x),
$
where the sum and product can be understood in the probability semiring, log semiring, or another
declared weighted-automaton semiring @graves2006ctc @mohri2009weighted.

The scalar $M_x(y)$ is not the capability which was recently tested. The capability was:

1. retain the complete target-specific state/frontier/transition surface;
2. let that surface become cellular Standing;
3. remove the lower teaching lineage from active participation;
4. present a nonidentical acoustic occurrence;
5. recover the prior recurrence boundary and use it to condition a new complete surface.

Two pronunciations can therefore have different frame fields and different alignment interiors
while meeting the same expression receiver. That is the same abstract relation as two formulas
with different recurrences meeting the same constant receiver. It is not an assertion that speech
and analytic number theory use the same domain law.

#evidence-note(
  [A complete algorithmic execution surface, rather than only its terminal score, can
    cross the membrane and condition a later nonidentical occurrence.],
  [Measured bounded evidence.],
  [
    #link("../../../observations/eros-ctc-temporal-surface-01/RESULTS.md")[
      CTC temporal surface 01
    ] and
    #link("../../../observations/eros-audio-ctc-path-fiber-01/RESULTS.md")[
      Audio CTC path fiber 01
    ].
  ],
  [
    The source world still interprets the recovered recurrence and constructs the later trellis.
    The carried formulation does not yet directly enact the later input through the one Eros
    circuit.
  ],
)

#source-note[
  The derivations which define the measured surface are
  #link("../../../RESEARCH/2026-07-23_THE_CTC_FRONTIER_IS_A_FACE_THE_RECURRENCE_SWEEPS_AN_INTERIOR.md")[
    The CTC frontier is a face
  ] and
  #link("../../../RESEARCH/2026-07-23_THE_PRONUNCIATION_IS_THE_PATH_FIBER_THE_EXPRESSION_RETURNS_ACROSS_DIFFERENT_VOICES.md")[
    The pronunciation is the path fiber
  ].
]

The measured result is important precisely because it identifies the next general boundary. The
problem is not “more audio.” It is the hand-up of an algorithmic lineage: a finite generator,
state transition law, admissibility boundary, and receiver map must become capable of acting on
later material without a world-side reimplementation of the same law.

= One abstraction, different semirings <semirings>

The shared grammar is path composition, not one universal numerical calculus. Weighted automata
make the distinction precise. A semiring supplies an operation for composing consecutive arcs
and another for combining alternative paths @mohri2009weighted.

#block(breakable: false)[
  #text(size: 8.2pt)[
    #table(
      columns: (1.05fr, 1.1fr, 1.15fr, 1.7fr),
      inset: (x: 3pt, y: 3.5pt),
      stroke: (x: none, y: 0.35pt + light-gray),
      align: (left, left, left, left),
      table.header([*Ecology*], [*Along a path*], [*Across paths*], [*Receiver*]),
      [Reachability], [AND], [OR], [an afforded path exists],
      [CTC], [multiply weights], [sum paths], [target-label mass],
      [Shortest path], [add costs], [minimum], [least-cost path],
      [Formal series], [multiply terms], [add coefficients], [bounded-degree face],
      [Proof paths], [compose], [prove comparison], [commuting exterior diagram],
    )
  ]
]

This table prevents a recurrent overgeneralization. CTC does not provide the law for zeta, and
formal exponentiation does not provide acoustic classification. They share a transport grammar
which allows their algorithms to be represented, compared, and potentially carried by one
medium-neutral machine.

= Consequences for Soma and Eros <consequences>

The paper changes the interpretation of what the engine should eventually receive, not its current
source in this entry.

== The machine should carry executable relations <executable>

For a formulation $cal(F)$, the necessary live object is not the text of a formula and not its
terminal value. It is a bounded carrier for:
$
  (a_t, N, D, partial_N, q_rho)
  arrow
  (a_(t+1), R_t),
$
where $R_t$ is immediate radiation and the successor may become later Standing. The source may
declare the initial identity and constraints. If later construction internalizes a deeper
topology, lower source constituents may depart while their consequential relation remains active.

The exact boundary now visible in both the formula and CTC lines is *enactment after hand-up*.
The finite generator has crossed as information, but a world interpreter still performs some of
the domain operation. A general solution cannot be another registry of named algorithms. It must
let the carried incidence and transport law participate directly in the next event.

== What should be measured <measure>

Scalar endpoint agreement is necessary but insufficient. A formulation experiment should report:

- the complete source and later paths;
- which cells and transitions were reused, rebased, formed, or allowed to depart;
- exact residual support at every unclosed comparison;
- receiver agreement across held-out occurrences;
- aperture growth without lower replay;
- active versus available constituents in each context;
- physical work, memory traffic, and parallel conduct when efficiency is claimed.

These are qualitative and structural observables. Counts support them; counts do not replace them.

== No universal taxonomy <no-taxonomy>

The ecology does not seek one absolute hierarchy of formulas, algorithms, models, or media.
Taxonomy is itself receiver-relative Standing grown from actual comparisons. A Machin formula may
be near another arctangent identity under proof transformation, near a BBP formula under
polylogarithmic structure, and near a neural recurrence under execution topology. Those
neighborhoods need not coincide. New evidence can rebase them.

= A bounded research programme <programme>

The next research should cultivate a small but complete atlas rather than scale a shallow corpus.

== Stage A: exact formulation bodies <stage-a>

Select a few causally distinct families:

- $e$: factorial recurrence, limit of compound growth, and a continued fraction;
- $pi$: Machin arctangent, polygon or AGM iteration, one hypergeometric series, one BBP path, and
  the $zeta(2)$ receiver;
- transcendental transport: one branch-bearing complex-power family, its radial quotient,
  projective swing, circular chart, and split-complex continuation;
- zeta: finite Euler product, prime-power logarithm, theta/Mellin completion, and generative tail.

For each, encode the seed, next-face law, domain, exact boundary or enclosure, receiver, and cost.
Do not encode a floating endpoint as the body.

== Stage B: explicit transition cells <stage-b>

Add a 2-cell only when a derivation or executable comparison supplies it:

- change of variables;
- formal logarithm or exponential;
- logarithmic lift, branch continuation, and projective rebase;
- Mobius-invariant cross-ratio comparison in a declared hyperbolic chart;
- recurrence equivalence;
- Fourier--Poisson transport;
- Mellin transport;
- interval enclosure showing two finite apertures meet the same receiver;
- held-out behavioral comparison for learned factorizations.

Failed comparisons remain OPEN faces with oriented residuals. They are not discarded training
examples.

== Stage C: hand-up and later enactment <stage-c>

Teach one formulation occurrence, allow the source-local lineage to depart, and present later
material which requires the same law in a changed chart. The decisive observation is not that a
label or constant reappears. It is that the carried recurrence or transition structure itself
forms the later path and returns a consequence.

Four bounded cells are especially informative:

1. the factorial exponential recurrence grows a held-out aperture without a domain-side
   exponential interpreter;
2. the homogeneous prime recurrence repairs a withheld repeated-axis residual at the next
   degree;
3. an inherited neural or CTC factorization is retriangulated for a held-out receiver context
   while preserving its complete exterior relation;
4. an exact simplicial flip is carried through scale and chart rebase while a matched projective
   quotient fails precisely where it discarded metric and operation directions.

== Stage D: RH-facing carrier <stage-d>

Only after the previous stages are causal should the arithmetic programme grow toward RH. The
target is a complete explicit-formula event complex with:

- prime-power occurrences and von Mangoldt weights;
- the archimedean Gamma and boundary terms;
- a declared test-function space;
- Mellin/Fourier involution;
- an exact adjoint relation;
- a positive quadratic form or equivalent spectral witness.

The stopping condition is binary and structural: either the complete carrier closes the
positivity relation, or the remaining open seam is named by an actual missing cell. More prime
plots or symmetric finite samples do not move that boundary.

= Derived hypotheses <hypotheses>

#proposition[
  The factorial expansion of $e$ and the prime-power expansion of the Euler product instantiate
  the same formal exponential law in different graded algebras.
]

#proof[
  Both are restrictions of $exp(L)$ and obey the homogeneous recurrence proved in @e-face. Their
  generators, monomials, and receiver maps differ, so this is a common operation species rather
  than identity of the resulting ecologies.
]

#proposition[
  The classical theta/Mellin construction supplies a non-arbitrary seam joining $e$, $pi$, prime
  powers, and the completed zeta function.
]

#proof[
  The Gaussian contains $e$ as exponential transport and $pi$ as the self-Fourier normalization.
  Poisson summation gives theta reciprocity. Mellin transport contributes the Gamma factor and
  joins the theta relation to $zeta(s)$, whose Euler product carries prime powers in the
  half-plane of absolute convergence.
]

#open-problem[
  *Formulation retriangulation hypothesis.* Given a finite inherited formulation and a declared
  receiver family, determine conditions under which an occurrence-level rewrite can construct a
  different bounded factorization that preserves all receiver observations while reducing
  contextual physical work. The witness must include transition maps, complete path comparisons,
  and later conduct.
]

#open-problem[
  *Growing formulation-atlas hypothesis.* A bounded ecology which carries generators,
  comparisons, and residual support can use a newly presented formulation to found transition
  cells which were not source-declared, provided their consequences close on later held-out
  occurrences. Common endpoint alone is not sufficient evidence.
]

These hypotheses are the precise bridge between mathematical formula discovery and learning.
Finding another expression for $pi$ is not merely symbolic search if the machine can retain why
the path is admissible, how its aperture grows, where it is efficient, and how it transforms into
known charts. Likewise, inheriting a transformer ecology is not merely copying weights if later
events cultivate a new receiver-exact causal factorization.

= Conclusion <conclusion>

The unifying object is neither a number nor a model. It is a live, finite, situated formulation:
actual material transformed through an admissible causal interior into a receiver face, with its
boundary and consequence intact.

This view resolves the apparent split among the laboratory's recent subjects.

- The many formulas for $pi$ and $e$ are an atlas of nonidentical paths, not redundant equal
  strings.
- A radial or algebraic exterior can forget a transcendental logarithmic lift, branch, phase,
  rapidity, and monodromy which later conduct can still distinguish.
- A changing-base triangle can be represented by vertex scaling, cross-face ratios, simplicial
  path comparison, and exact local flips rather than by a scalar “cell state.”
- A cross-ratio and endpoint can agree at one occurrence while losing the metric scale, divisor,
  and composition required by a later retriangulation.
- Prime powers and semiprimes emerge as graded faces of the formal exponential which becomes the
  Euler product.
- The Gaussian theta relation joins exponential scale, circular normalization, Fourier
  reciprocity, Mellin transport, and the completed zeta function.
- The critical line is the fixed seam of that completed involution; RH still owes a complete
  positive carrier.
- Information compression is exact only relative to named future observations.
- Probability and loss are local recurrence quotients and oriented residuals, not chance,
  reward, or punishment.
- A neural architecture or CTC trellis is one executable formulation ecology.
- The recent CTC result demonstrates carriage of an algorithmic interior, not merely audio
  matching; its open boundary is later direct enactment.

The constructive objective is therefore clear: let Eros inherit developed ecologies, carry their
causal interiors rather than their terminal scalars, and cultivate new formulations whose
relations are established by later consequence. That objective applies equally to mathematical
solvers, learned models, speech, code, and any other world whose lawful transformations can cross
the membrane.
