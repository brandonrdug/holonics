#import "../../lib/elements.typ": elements-paper, proof-block, by-rule, by-blue, by-muted, by-paper

#let source(path, label) = link("https://github.com/brandonrdug/holonics/blob/3a242c99/" + path, label)
#let history(path, label) = link("https://github.com/brandonrdug/holonics/blob/13f8c734/" + path, label)
#let note(body) = block(above: 5pt, below: 5pt)[
  #set par(first-line-indent: 0pt)
  #text(size: 8.5pt, fill: by-muted)[#body]
]
#let node(title, body) = block(
  width: 100%, inset: 5pt, fill: by-paper, stroke: 0.5pt + by-rule,
)[
  #set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  #text(size: 8.2pt)[*#title* #linebreak() #body]
]

#show: elements-paper.with(
  title: [Energy signatures #linebreak() and contextual refinement],
  subtitle: [A supplement to HNN and Athena's common foundation],
  authors: [Holonics · Brandon's framework · Codex source consolidation],
  date: [4 October 2026 · separate source supplement],
  abstract: [
    A signature is received through moving material, boundary and receiver.
    Its compatible fibre determines what a task can infer and what further
    reception it needs. The construction below joins port work, moving area,
    future-sufficient retention and a concrete HNN work-and-error gate.
    Historical evidence, checked mathematics and proposed consumers remain
    distinct. No universal unique signature or unified force law is established.
  ],
)

#set par(spacing: 0.5em)
#set table(inset: 5pt, stroke: 0.4pt + by-rule, align: left)

= One received construction

An energy signature is a field of receipts of a source, intervening material
and a participating receiver at a declared grain, frame and clock. Complex
parametrons and helical pair contacts carry the motion; their constitution
determines storage, modes and response. The medium and receiver also move,
store and exchange power.

#block(above: 9pt, below: 6pt)[
  #grid(
    columns: (1fr, auto, 1fr, auto, 1fr, auto, 1fr, auto, 1fr),
    column-gutter: 3pt, align: horizon,
    node([Source], [constituted motion]), [→],
    node([Medium], [material and boundary]), [→],
    node([Receiver], [frame, clock, grain]), [→],
    node([Retention], [future-sufficient quotient]), [→],
    node([Refinement], [partition or admitted probe]),
  )
]
#note[
  The arrows abbreviate compositions of Holons and their reception.
  A receipt reaches the receiver before retention; its paired return can reach
  the producing material. Certified deposition changes that constitution.
  Refinement obtains a finer face or another actual reception.
]

For symmetric quadratic storage $E = (1/2)x^T Q x$, an admitted motion obeys
the existing port law:

$ dot(E) = -chevron.l f_D, R f_D chevron.r
  + chevron.l e_P, f_P chevron.r + chevron.l e_A, f_A chevron.r
  + (1/2)x^T dot(Q)x. $

Oppositely oriented internal powers cancel when the participants interconnect.
A pump, changing constitution or moving grip supplies work. Dissipated
mechanical energy enters thermal storage or an outward heat receipt according
to the chosen cut. Storage positivity and passivity require their hypotheses.

#note[
  #source("lean/Holonics/Holon/Element.lean", [PortHolon.energy_balance])
  owns the identity; #source("docs/ELEMENTARY_OBJECTS.md", [the elementary objects])
  own the vocabulary. The parameter used in a calculation is a declared joined
  clock with the participants' conversion relations.
]

#text(size: 8.6pt)[
  *Grades used here.* *Checked* identifies a named formal owner or sealed Lean
  receipt. *Historical* identifies a retired source or measured apparatus.
  *Derived* identifies a calculation under stated premises, without a new
  formal or production join. *Proposed* identifies an acceptance or consumer
  still to be built and tested.
]

#pagebreak()

= Moving area and future-visible material

*Derived.* Let a continuum chart supply energy density $e$, current $j_E$,
source $s_E$, a smooth moving region $Omega(tau)$ and its physical boundary
velocity $w$. Continuity and the transport theorem give

$ dif/(dif tau) integral_(Omega(tau)) e
  = -integral_(partial Omega(tau)) (j_E-e w) dot n
    + integral_(Omega(tau)) s_E. $

Volume and surface measures are understood. A fixed surface reads $j_E$;
a moving surface reads the relative current $j_E-e w$. Its oriented area
comes from the actual spatial derivative of the chart $X$, through
$(j_E-e w) dot ("cof"(D X)N)$, where $N$ is the reference oriented area.
The metric, physical units and boundary velocity are operands of the law.

#proof-block(title: [Checked E1; pointwise scope])[
  Five local Lean closures check the polynomial tube chart's actual derivative,
  its section and the supplied relative-current pairing through that section's
  cofactor area. The consuming theorem is
  `FrameTransport.egg_relative_current_section_flux`.
  Its sealed owner and axiom audit passed. This receipt supplies a transverse
  pointwise law. Physical embedding, material-time velocity, continuity and
  the integrated moving-volume theorem remain separate obligations.
]
#note[
  E1 receipt: `e1-relative-current-11/audit-accepted-12.json`, in the local
  foundation integration packet. E1 has not been promoted into the public
  owner. The continuum premises and work terms are routed by
  #source("docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md", [mass, energy and causal transport]).
]

*Derived.* For positive $Q$ and a $Q$-orthogonal coarse projection $P$, write
$x_g=P x$, $r=(I-P)x$. Then

$ E = (1/2) norm(x_g)_Q^2 + (1/2) norm(r)_Q^2. $

The hidden term remains in the material. A nonorthogonal projection also leaves
a cross term; changing $P$ or $Q$ adds their rates. Eliminating a dynamic interior
likewise leaves its causal return and initial stored state. A static Schur
restriction alone does not close that changing response.

*Checked retention law; proposed error consumer.* Fix context $c$, a coarse
receiving map $S_g$ and the admitted future faces $Y_a$, including actions,
receivers and clocks. The compatible fibre is
$cal(F)_g(s,c) = {z in cal(Z)_c : S_g(z)=s}$.
Exact sufficiency requires

$ S_g(z)=S_g(z') => Y_a(z)=Y_a(z') quad "for every admitted" a. $

For a supplied output metric, a certified fibre diameter at most the exact
tolerance $epsilon$ is a sufficient error bound for any compatible
representative. Refinement is needed when that bound fails. Context narrows
the fibre through reached receipts and declared material restrictions.

#note[
  #source("lean/Holonics/Foundation/Standing/Law.lean", [StandingLaw's future factorization])
  owns exact sufficiency. #source("lean/Holonics/Objects/SourceHolon.lean", [future observability])
  explains reopening: $(0,0)$ and $(0,1)$ share their present first-coordinate
  face; the quarter-turn $(x,y) mapsto (-y,x)$ separates their next face.
  Receiver-null contrast can therefore contain future-visible motion.
]

#pagebreak()

= What the evidence actually supports

The September 24 reset keeps these sources as evidence to recover deliberately.
Each row supplies a premise for the same source–medium–receiver construction;
it does not inherit a production HNN consumer.

#text(size: 9pt)[
  #table(
    columns: (0.85fr, 2.25fr, 1.9fr),
    table.header([*Source and grade*], [*Actual evidence*], [*Consuming distinction*]),
    [*RELAMPAGO* #linebreak() Historical],
    [The #history("research/records/2026-07-30_THE_CAUSAL_BODY_OWNS_THE_BOUNDARY_THE_PROJECTION_CANNOT_INVENT_A_FACE.md", [corrected July 30 record])
     uses real GLM/ABI/IGRA material with typed phase branches and conditional
     vertical fibres. The terminal-picture topology claim was retracted.],
    [Conditional vertical support is not measured lightning altitude.
     Learned coordinates are not automatically electromagnetic components;
     that receipt caused no filled two-cell or connection holonomy.],
    [*MMS* #linebreak() Historical],
    [The #history("research/records/2026-07-30_THE_CURRENT_RETAINS_THE_BOUNDARY_THE_RETURN_REFORMS_THE_NEXT_PASSAGE.md", [July 30 current/return record])
     uses four spacecraft at the 16 October 2015 magnetopause reconnection
     crossing, retaining the instruments' different clocks and alignment offsets.],
    [A real plasma source cut with multiple receiving frames and clocks.
     It establishes neither a planet-core observation nor the current Resident join.],
    [*Synthetic Kepler* #linebreak() Historical],
    [Laboratory `physics_world.py` supplies a planar unit-central-potential
     truth world with Cartesian leapfrog. A historical standalone predictor
     was trained on its fixed-point byte presentation.],
    [Its own header marks it a contaminated toy. Generated rollouts have
     substantial energy and angular-momentum variation, quantified below.
     No observed-star or many-body prediction is validated.],
    [*Retina* #linebreak() External evidence],
    [#link("https://www.nature.com/articles/s41586-024-08212-3", [Karamanlis et al.])
     find cell-type-dependent correlated responses to natural gaze shifts;
     nonlinear receptive fields can evoke redundant coding.],
    [Repeated structure can be functional. A native refinement rule must preserve
     distinctions needed for contrast, reliability or a future action.
     This supplies no HNN compute-saving measurement.],
    [*Billiards* #linebreak() Mathematical sources],
    [#link("https://math.brown.edu/reschwar/M272/advances.pdf", [Tabachnikov's dual billiard]),
     #link("https://arxiv.org/abs/1311.6763", [Hughes's regular polygons]) and
     #link("https://arxiv.org/abs/2510.11869", [Edwards-Costa's outer length billiards])
     supply distinct maps, orbit words and geometric invariants.],
    [Keep their hypotheses and first-return maps distinct. Area preservation
     requires additional metric, units and port work to become an energy claim.
     Fold fibres count preimages, not optical energy splitting.],
  )
]

#note[
  Kepler's `physics_kepler.log` reports a generated passage of
  $300=2^2 dot 3 dot 5^2$ frames: relative peak-to-peak energy variation
  $2583/10000$ and angular-momentum variation $569/5000$ at its recorded
  precision. `physics_forward.py` owns the contamination warning. These sidecar
  files were directly inspected; no rerun. The separate historical Hénon–Heiles
  world is a synthetic polynomial Hamiltonian, not Kepler gravity.
]

*Derived inverse limitation.* Even $y=h s$ leaves the same receipt under
$(h,s) mapsto (h/a,a s)$ for nonzero $a$. Multiple channels, calibrated probes,
clocked change and constitutive restrictions can reduce this fibre. Unique
reconstruction requires a separating family with its gauge handled. A spectrum
or total energy alone generally leaves multiple compatible responses.

#note[
  #source("lean/Holonics/Foundation/CausalChord.lean", [CausalChord's spectral counterexample])
  owns `spectrum_does_not_determine_response`. A finite operator's complete
  coordinate-probe atlas is a stronger, specifically framed premise.
  #link("https://journals.aps.org/rmp/abstract/10.1103/RevModPhys.93.015001", [Aerts's asteroseismology review])
  supplies a real surface-mode/interior inference route under stellar forward models.
]

#pagebreak()

= The HNN work-and-error acceptance

*Proposed consuming gate.* Familiar constituted relations may need less
additional refinement, while a reached separating comparison demands new
participation or deposition. Test that claim against a declared uniform-fine
realization on the same source/task family, hardware and admitted future.
Charge the whole reception and return:

$ W_"adapt" = W_"coarse" + W_"inference" + W_"refine"
  + W_"move" + W_"retain", quad W_"adapt" < W_"all". $

Reception, encoding, routing, exact arithmetic, rebasing, deposition and storage
belong inside these terms. Native work, device memory, elapsed time and physical
energy are separate receipts with their units. An error reduction or smaller
display alone is not a work measurement.

#set enum(indent: 1em, body-indent: 0.5em)
+ *Same task, same future.* Fix the source partition, receiving metric,
  exact tolerance, admitted actions, clocks and held-out family before the run.
  Both realizations must meet that receiving acceptance. Show Athena's actual
  joint output and executed continuation as required by its current gate.
+ *A charged saving.* Establish the exact ordering above after every cost is
  counted. If learning is also claimed to reduce work from first exposure,
  measure that separate comparison. Familiarity alone does not imply a saving.
+ *Quiet separating probes.* A weak peripheral change that affects the target
  must trigger enough refinement for the correct future receipt. Include an
  off-axis return, equal-energy signals with different phase, a changed
  constitution and a moving receiver. A frozen central receiving patch fails
  whenever one of these changes the requested face.
+ *Reached learning and retained distinction.* Use the comparison covector
  through its producing operands and certified deposition. Carry the
  future-sufficient quotient, decoder and unresolved fibre. A discarded
  distinction needs renewed reception to be recovered.
+ *An honest failure receipt.* A violated error bound, missed quiet probe,
  unstable return or routing/storage cost that removes the saving falsifies
  the claimed gate. Report exact orderings and failed faces with the result.

The native source must enter the HNN's own encoding and dynamics. A classifier,
answer table, imposed text window or authored sensory pyramid would repeat the
recorded catered-machinery failure. The historical pyramidal-eye correction
places coarse-to-fine organization in the constituted body receiving the raw
field, rather than in a hand-supplied solution organ.

#note[
  The #source("research/records/2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md", [catered-machinery lesson])
  fixes that boundary. The existing
  #source("crates/holonics/src/hnn/word/continuation.rs", [ContactCut continuation])
  and #source("crates/holonics/src/hnn/reference/continuation.rs", [focused reference consumer])
  establish a contact-C path with its stated scope. They do not supply this
  proposed compute comparison or complete production Resident acceptance.
]

Current HNN continuation and useful output remain the first consuming gate;
existing protein work retains its place. A later bounded astronomy inverse
would fix an observation cutoff, competing forward models, uncertainty and
held-out receiving acceptance. Original observations and fitted ephemeris
conformance are different tests. This supplement starts no such campaign.

#note[
  *Further primary routes, with their separate regimes.*
  #link("https://agupubs.onlinelibrary.wiley.com/doi/full/10.1002/2016JD025365", [Warner's lightning leaders]),
  #link("https://arxiv.org/abs/2005.14588", [Nijdam–Teunissen–Ebert's streamers]),
  #link("https://doi.org/10.1103/PhysRev.58.919", [Eckart's relativistic fluid]),
  #link("https://doi.org/10.1039/C7CP00667E", [Liu–He–Zhang's liquid water]),
  #link("https://journals.biologists.com/jeb/article/202/23/3295/8324/The-mechanical-design-of-spider-silks-from-fibroin", [Gosline's silk mechanics]),
  #link("https://www.nature.com/articles/s41428-025-01039-3", [Zeußel's silk phase separation]),
  #link("https://doi.org/10.1147/rd.53.0183", [Landauer's erasure heat]),
  #link("https://doi.org/10.1103/PhysRevA.40.1539", [Zanetti's lattice-gas hydrodynamics]).
  #link("https://arxiv.org/abs/0709.1173", [Toffoli's lattice-gas rewriting]) and
  #link("https://arxiv.org/abs/0812.4373", [Lizier's transfer versus causal effect]) /
  #link("https://doi.org/10.1103/PhysRevE.77.026110", [local transfer filter]) are distinct mathematical contexts.
  #link("https://arxiv.org/abs/physics/0610101", [Li–Sinai's complex fluid solutions]) and
  #link("https://github.com/openai/NavierStokesAndEuler", [OpenAI's Lean fluid certificates])
  supply specified fluid results, not a native physical predictor.
  These links extend the source premises; they establish no common constitutive
  identity or checked HNN consumer. The reference recovery covered a bounded
  inventory; October userPC logs were unavailable.
]
