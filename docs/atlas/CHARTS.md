# Charts: one operation read through many disciplines

Agent context. A discipline is a boundary chart of the elementary objects: it names the same
operations in its own nouns and adds an application of its own. This file routes a discipline to
the object and operation it is a chart of, to the atlas rows that hold what is already derived, and
to what stays behind in the discipline. It asserts nothing: every claim belongs to the row or record
it points at. The older, wider index of field vocabularies is the canon's
[correspondence atlas](../canon/THE_CORRESPONDENCE_ATLAS.md) (August, historical).

## How to pivot through a discipline

Brandon's lenses arrive in a discipline's language (music, lightning, a vortex ring, a cipher). A
lens is used, never filed. To use one:

1. **Name the object and the operation.** Say which elementary object the discipline's noun is
   (a note is a ring's rate, a chord a set of rings, a temperament a coholon) and which operation
   its verb is (tuning is zeroing a slip, modulation is a rebase).
2. **Recover.** `rg -i '<noun|operation|classical name>' docs/atlas/` and open the owner. Most
   charts below already hold dozens of rows. A row found is used and cited by id.
3. **Take the discipline's theorem as a statement about the operation**, with its hypotheses
   restated on the objects. A theorem whose hypothesis the machine does not meet does not apply.
4. **Leave the application behind.** The right-hand column of the table names what belongs to the
   discipline alone. Importing it is catered machinery (a tuning table, a parser, a cipher attack).
5. **State what follows for the machine as a test**, with its guess fixed before the read, and say
   what does not transfer.

The failure this prevents has two sides: a lens filed as "changes nothing", and a lens taken
literally so that the discipline's apparatus is built into the machine.

## The charts

| Discipline | On the objects | The operation that transfers | Atlas | Stays behind |
|---|---|---|---|---|
| Music, acoustics | A tone is a ring's rate, an interval a Ratio, a chord a set of rings closing at their least common multiple, a temperament a coholon whose kernel is its commas, timbre the modes of a constitution | Lock and slip at a pair contact; identity as a pattern of ratios modulo a common shift; a rhythm as the carries of one rate read on another's circle; compression with a declared kernel and a heard residual | `pair.beat-is-slip`, `ratio.comma-*`, `rotation.*`, `lock.*`, `holon.song-is-a-family`, `encoding.chord-cross-terms`, `radix.carry-rhythm`, `fractal.*`, `spectro.*` | Preference, style, any tuning table or scale as an authored list |
| Number, radix, places | A numeral is a reading down a tower of rings, one phase a ring; depth is the digit's place; a ratio is two windings carried undivided; each prime is a place | Winding with carry; the product formula across places; a ratio's expansion closing with a period; rebase | `radix.*`, `series.*`, `prime.*`, `arith.*`, `trace.place-ledger`, `solenoid.*`, `winding.*`, `code.form-kraft-sparse`, `code.count-digits-second-order`, `code.region-scale-chain`, `code.digit-conserved-carried`, `ratio.sign-edge-turn`, `radix.digit-shift-spectrum`, `lock.euclid-walk-cost`, `prime.wheel-step-inversion` | A fixed word size, a float, any width chosen by hand |
| Induction, circuits | Stores exchanging through a power-neutral interconnection; a contact as a junction; a parametron as a pumped ring | The skew part circulates, the positive part dissipates; flux through a cell drives circulation on its boundary; elimination of an interior returns a boundary law with memory | `em.*`, `maxwell.stokes-dirac`, `ph.*`, `parametron.*`, `resolvent.dynamic-schur`, `junction.*` | Component values, lumped-circuit idealizations |
| Fluids, vortices | A vortex line is a strand, a ring a closed strand held by its medium, helicity the linking of closed strands | Self-induction of a strand; conserved linking changed only at reconnection; the relevance tail | `fluid.*`, `ns.*`, `wave.*`, `phase.*` | Any closure model or turbulence constant |
| Lightning, breakdown | A leader is a navigator founding a channel in a medium, and the return rides it | FOUND then RIDE: a path paid for once conducts afterwards; the streamer's drift | `em.streamer-drift`, `fluid.plasma-source`, `plasma.*`, `constitution.flux-from-constitution` | Atmospheric chemistry |
| Heat, information | Cross-entropy is flux across a section; temperature the integrating frame; a deposit is retained where heat left | Entropy production along a passage; the receiver's second law; code length as storage growth | `heat.*`, `thermal.*`, `xent.*`, `info.*`, `code.*` | A single scalar of progress |
| Relativity, refraction | A receiver's clock and metric; an index is a ratio of clock rates at an interface | The turn and boost split against a receiver's metric; phase matching at a boundary | `gr.*`, `lorentz.*`, `mass.*`, `clock.*`, `motion.*` | A privileged frame |
| Quantum readings | A face read at a pivot with its aftermath; statistics from the orientation of a pairing | Conjugate pairs; the sign of an exchange | `quantum.*`, `wigner.*` | Any claim about microscopic physics |
| Cryptanalysis | A key is the navigators' initial configuration; a menu is a set of contacts; a crib a known passage | Key location by loop closure; unicity as the length at which one key remains | `key.*`, `unicity.*`, `infer.*`, `key.meet-in-middle-half`, `key.isogeny-terrain` | An attack on any deployed cipher |
| Packing, quasicrystals | A lock count is a capacity; a packing a partition of capacity at a tolerance; a quasicrystal a rate that never locks | Three gaps of a rotation; cut and project; the string of holes | `fractal.*`, `egg.*`, `rotation.*`, `quasicrystal.*`, `kam.*` | Dimension-specific optimal lattices as authored layouts |
| RH | The half line is where scale transport is unitary; primes are primitive closed paths; a zero is a cancelled comb | The trace over closed paths; positivity of a completed response | `rh.*`, `trace.*`, `theta.*`, `analytic.*`, `receipt.seam-g-skew`, `rh.escape-threshold-half`, `rh.prime-count-half-digits`, `rh.normal-no-resonance`, `key.scaled-form-places-modes` | Numerical zeros as evidence of the theorem |
| Hodge | Motion is exact ⊕ coexact ⊕ harmonic; a face is a cohomology class | The harmonic representative; what friction keeps | `hodge.*`, `cell.*`, `holonomy.*`, `key.scaled-form-places-modes` | A classification by table |
| Elliptic curves, BSD | A torus of two periods; torsion is locked phase pairs; rank is the free windings | Descent; local counts assembled into a global reading | `bsd.*`, `egg.arithmetic-two-torsion`, `bsd.odd-zeta-regulator`, `key.isogeny-terrain` | Curve databases as oracles |
| Gauge, Yang–Mills | A connection on the complex; curvature as holonomy on declared circuits | The heat flow of curvature; the commutator as stretching | `ym.*`, `coupling.*`, `holonomy.*` | A choice of gauge as a fact |
| Learning, compression | Deposition from covectors that reached a locus; retention as a quotient sufficient for the admitted future | The covector of a declared comparison; kernel, cokernel and landmark | `learn.*`, `deposition.*`, `compression.*`, `retention.*`, `quotient.*`, `release.*`, `receiver.*`, `navigator.content-stride-moment`, `navigator.unit-composite-move`, `contact.carried-product` | Any industry architecture taken as the model |
| Kinematics, control, inference | A joint is a contact with a screw, a chain a serial screw word, a wrench the coholon of a twist, a blanket a joint's ports, a filter's update the elimination of a joint | The end's wrench pulled back through each joint's lever; elimination one joint at a time (a filter in, a smoother out), on a tree in two sweeps, a loop paid at its cut | `chain.*`, `screw.*`, `tube.dn-elimination`, `resolvent.dynamic-schur`, `spectro.reading-mass`, `infer.*`, `code.register-content-by-distance` | Joint lists, a solver for a target pose, the Gaussian form, any anatomy |
| Sensing, apertures | A receiver's section; facets are receivers whose readings are joined after each is read, an aperture joins amplitudes before the read; a hair is one receiver read at two times | A difference has two ends, in place or in time; a further receiver adds its content given the others | `receiver.*`, `receipt.*`, `frame.receiver-projection`, `code.register-content-by-distance` | Eyes, ears and hair cells; the number two |
| Crystals, plasticity | A crystal is a constitution whose deposited directions repeat, a slip system a contact's plane and direction, a grain boundary a face between frames | Deposition as dyads along the directions that carried flux; a drive acts by its part resolved on a system; transmission across a face by the alignment of frames | `deposition.dyad-anisotropy`, `contact.material`, `winding.crystallographic-restriction`, `ns.anisotropic-frame`, `quasicrystal.*` | Point groups, slip systems and lattice tables as authored layouts; material constants |
| Strings, loops, knots | A string is a tube under tension, a grip a junction's impedance, a loop a closed strand, a crossing a local contact | A partition sees the rest only through the response at its cuts; reflection by mismatch; a winding changed only by a slip; a three-body link that no pair reads | `wave.boundary-response-family`, `wave.junction-reflection`, `tube.dn-elimination`, `winding.linking-number`, `ns.helicity-linking-form`, `code.pair-contact-conditional`, `radix.register-composition` | Instruments, superconducting materials, any claim of motion without loss |
| Navigation, puzzles, complexity | A configuration is a state of a terrain whose moves generate a group, a solution a word in the moves, a landmark one stored column of the distance potential, a number a count of reachable states under the relations | The pricing of a route: a floor from the count on the cover, a ceiling from the gap read against the cover's radius, the square root from two sweeps that meet, descent on a potential, and the division of the volume by each orbit a landmark pins | `key.navigation-floor-ceiling`, `key.tempered-relative-to-cover`, `key.meet-in-middle-half`, `landmark.distance-potential`, `landmark.pin-worth-surprise`, `key.slow-modes-landmarks`, `key.unique-games-frontier`, `lock.euclid-walk-cost`, `prime.wheel-step-inversion`, `motion.two-turns-compose` | Solvers, pattern databases and distance tables as machinery; any claim about a complexity class |
| Tokenizers, coarse graining | A token is a founded unit: a word's letters composed into one move at a coarser grain; a vocabulary is a store of such moves; a boundary is a stride that contracts | Telescoping by the associativity of composed moves; a stop as a landmark where every history arrives at one state; founding as the exchange of storing for composing | `navigator.unit-composite-move`, `navigator.content-stride-moment`, `contact.carried-product`, `hnn.founded-units`, `hnn.tower-news-clock`, `tower.field-scale-packets`, `tower.field-pace`, `radix.packet-affine-move`, `encoding.merge-moment-square` | An authored vocabulary, a merge table or a boundary rule as machinery; units as the input codec |

## Maintaining this file

A chart is added when a lens arrives in a discipline that has no row, in the same change as the
record that derives it. A row names atlas prefixes that exist (`cut -f1 docs/atlas/*.tsv`), never a
planned one.
