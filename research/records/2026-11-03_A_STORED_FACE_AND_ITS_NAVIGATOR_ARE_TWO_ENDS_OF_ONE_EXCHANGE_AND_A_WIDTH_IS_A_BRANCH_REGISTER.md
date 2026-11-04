# A stored face and its navigator are two ends of one exchange, and a width is a branch register

November 3. Refs #404 #601. Status: [lens] for Brandon's statement (paraphrased; his words stay outside the repository),
[source-inspected] for the owners it joins, [definition; agent-inferred] for what it changes in the field's plan. Claude
(opus), design lead.

Computational object: the helical pair interaction. Of the winding guide's six general objects the lens touches the
**helix** (a ring's period is a register's base, its winding the carry) and **faces and placement** (a stored face against
the navigator that regenerates it); the pair, cell holonomy, the tube and the tower thread stay attached through the field.

## 1. The lens

Brandon, November 3 (two messages, on the field's growth by copies from width 32 to 64):
- **A width is a branch register.** A width is a partition, a sum of parts such as `2² + 2¹ + 2⁰`, each part a lane of a
  morphodynamic circuit, not one undivided register doubled.
- **A stored face and its navigator are two ends of one exchange.** `17179869185` and `2³⁴ + 2⁰` carry one value; the second
  stores less and must be navigated (converted) to give the first's face; storing a value in the form it will be read
  saves the navigation, storing its generator saves the memory. A float's sign, exponent and most of its mantissa are
  stored although the system they sit in already implies them. A constraint identity (π, `e`) is the extreme: the
  navigator alone, no stored digits, at the most navigation. A machine that keeps both, cached partial faces and fitted
  fractal navigators, and moves between them, optimizes whatever it holds. He called this keystone.

## 2. Where the framework already holds it, and the one refinement

- `docs/ELEMENTARY_OBJECTS.md` (π and `e`): the identity is the navigator; digits are a receiver face
  (`RadixWindowReceiver`); the **partial navigators** (the compiled binary-splitting blocks `(P, Q, T)`, composing
  associatively) are the cached partials, extendable where stored digits are not.
- The canon's compression tablet §5 and the atlas rows `code.levin-kt`, `code.compact-program-pi`, `code.window-cost`: the
  exchange's standard carrier is Levin's `Kt(x) = min_p {|p| + log₂ t(p)}`; a window at offset `k` costs about `2 log₂ k`
  against `ℓ log₂ b` for its literal digits.
- **The refinement** (the tablet's own): the exchange is a Pareto frontier over description bits, work, time, space,
  erasures and energy, not a conserved product. Blum's speedup theorem gives functions with no fastest program, and the
  only fundamental energy floor is on erasures (Landauer), so a change of base, a bijection, costs time and the erasure of
  its intermediates, never a fixed energy per bit.
- **Number bases.** A part of a width is a coordinate (parts add, a direct sum); a base-`b` digit is a register of `b`
  states (`ℤ/b`; lanes multiply state counts); `2² + 2¹ + 2⁰` is the integer seven written in base two, equal in value to
  `10₇` and unlike it in carries. Exact parallel lanes are the Chinese remainder theorem's, over coprime periods
  (`ℤ/14 ≅ ℤ/2 × ℤ/7`, no carry between lanes); `1097 − 1 = 2³ · 137` is the split `n − 1 = 2ˢ d`, `d` odd, of Fermat's
  and Miller–Rabin's tests.

## 3. Where the field stands against it

[source-inspected] `hnn::tower::field`:
- **The rings already hold the lens.** The ring periods (`ring_periods`) are powers of two and three (2, 3, 4, 9, 16, 27,
  … 4,096, 6,561), so the place clock is carried in coprime lanes `ℤ/2ᵃ × ℤ/3ᵇ`, and the source enters as phase-carried
  moments on them, the passage held in a navigator's basis rather than as a tape (the retention law).
- **The material does not.** The learned material is a dense array of exact integers on one fixed grain (`2^(−24)`), every
  site's state a dense register of `D` coordinates read by dense charts, and growth by copies
  (`FieldLearner::widened`) doubles that register. Apart from its clocks' paces (located keys, §16.15 of the field record),
  nothing in the field fits a navigator to a regularity and then regenerates its faces instead of storing them.
- **GSM8K's arithmetic is where the exchange bites.** `<<65*5=325>>` cannot be learned as a stored table of products; the
  field must locate the carry law. Its rings are odometers with carry (selective stepping, the carry chain), so that
  navigator is of the machine's own kind, located, never authored (no catered machinery).

## 4. What it changes in the plan

[definition; agent-inferred] In order, each a short loop on the card:
1. **The answer reads its question first** (the field record's §16.35: the copy lab, and the question's information
   through the joint code). Arithmetic presupposes it.
2. **Growth by a fresh branch** in place of copies: a part with its own normalization and frame, opened from its own
   drawn rows and read through columns founded at zero, so every face is kept and no copy has to part from its source
   (§16.29 measured copies parting slowly). Its size is the part the withheld code's stall asks for, never a doubling by
   rule.
3. **A located carry navigator for the calculations**: a ring whose winding is the carry, its keys located from the
   answers' own calculations, read against the joint code's information on the calculation sites.

Failures this could repeat, checked: **catered machinery** (no calculator: the carry navigator's keys are located by the
field's deposition); **a design thought in the programming language** (a width is stated as parts and lanes, never as an
array size picked by hand); **a lens resetting the work** (it changes item 2's law and adds item 3, and the order keeps the
failed gate, the question's coherence, first).

## 5. The elementary statistics of the passage (Brandon's second message)

[lens] Brandon, November 3, later: the exchange is about addressing and statistical distributions in general, pattern
matching and fitting everywhere, not about the machine parsing arithmetic out of text; text carries physical patterns, the
distributions of how people place characters and grammar, and knowing the most basic flexible elements first (as valid UTF-8
is known before a tokenizer's units) is where the rest follows from. The inputs stay raw bytes (no stores): whatever units a
word becomes must emerge from the field's own geometry and contacts.

[measurement] A reading of GSM8K's training passage (3,528,168 bytes; `_receipts/dissect.py`, `dissect.txt`; a reading only,
never part of the field):
- **The alphabet.** 121 bytes used, 4.924 bits a byte unconditioned; spaces 17.5 %, lower-case letters 60.6 %, digits 10.1 %.
- **Where the information sits in a word.** The `k`-th letter given the word's letters before it: 4.099, 2.323, 1.879,
  0.868, 0.366, 0.210 and 0.154 bits for `k = 0 … 6`. The information is the choice of a word; its spelling, once begun, is
  nearly a stored face. 13,464 word types; the top 100 cover 56.5 % of the tokens, the top 1,000 83.9 %, the top 5,000
  96.4 % (Zipf exponent 1.12 over ranks 10 to 1,000; Heaps' `β = 0.59`); hapaxes are 27 % of types and 0.7 % of tokens.
- **The falloff.** The mutual information of two bytes `d` apart: 1.413 bits at `d = 1`, 0.809, 0.503, 0.371 at 2 to 4,
  0.198 at 8, 0.057 at 16, 0.017 at 32, 0.005 at 128, and nothing above the counts' floor past about 250; over 8 to 256 it
  falls about as `d^(−1.6)`, faster than the field's participation prior `2^(−⌊log₂ d⌋)`.
- **The question is read by content.** 54.4 % of an answer's words and numbers, and 37.7 % of its numbers, stand in its own
  question, a median 300 bytes back, where the fixed-distance information is nil: the relation exists only through
  matching (the field's still heads and its listeners), never through place.
- **The clocks.** A token and its space about 5.4 bytes (the space indicator's spectrum peaks at 4.72 bytes), a line 72
  (quartiles 43 and 115), a question 216 and an answer 256 at the median.

[definition; agent-inferred] What it says for the writer: §16.35's written words break where letters are drawn before
their word is chosen, each at about four bits with its neighbours then held to agree with it; a word clicks only if its
places keep moving together until they align (the field record's §16.36, the refining writer). The falloff and the clocks
are the terrain's own periods, read against the rings' (`2ᵃ`, `3ᵇ`) when the founding's periods are next derived.

## 6. Language is composed geometrically; a symbol is what its modes do (Brandon's third message)

[lens] Brandon, November 3, evening: a player who wins at Scrabble in languages he does not speak reads words by their
composition, not their meaning; language is composed geometrically (cryptanalysis, tropical geometry). Strokes cross into a
character, characters cross into a word at coordinates of the word's parametric orientation, and words meet in a paragraph
by friction-like intersections from which their meaning follows; the resolution changes as attention moves from the
character to the word, the packet becoming the word. Loud partials carry the inference and the rest is dark information,
curvature for navigation and compression. A symbol is irrelevant: relabel the digits and a learner gives `9` the magnitude
of `1` if and only if `9` behaves as counting; it is the phases and modes that say what an object is. Mutual loss is
respected, with no privileged perspective.

[source-inspected; definition; agent-inferred] Its joins in the field:
- **A symbol is a pointer.** A byte enters only as a class index into the encoding `E`, founded from keys and learned, and
  the face reads a class through the same row (§16.26), so a relabeled alphabet is the same learner up to its founding
  draws: what a class becomes is what its modes do.
- **Loud partials and dark information.** A contact row is the series `Σ 2^z μ` (`SeriesRow`), a log-sum-exp in base two;
  its tropical limit (`max z`, as the temperature grows) keeps the loudest term, so the lens's loud partials are the terms
  that win a row's tropical sum and its dark information the rest, which bends the row's current without winning it.
- **The packet moves from character to word.** The fine rings carry the word a site stands in (§16.22); the writer fixed a
  character once and never revisited it, so the word's packet could not form while writing. The refining writer (§16.36)
  keeps a word's places moving until they align.
- **Meaning from intersections.** The contact field across a passage, the participation of its sites through the field's
  own transport (the October 28 record), is the only route by which an answer reads its question (§16.35's information).
- **Mutual loss.** The comparison is the ratio of two Holons and its covector reaches both strands (§16.26); no receiver is
  privileged (the receiver law).
The general-English terrain is on the host (TinyStories, 24 MB of training stories in the laboratory's corpora), for the
read against GSM8K's English when the writer is next measured.

## 7. Nats per code length, densities, and expansion (Brandon's fourth message)

[lens] Brandon, November 3, evening: prefer nats, read per code length, and read per area or volume as well, coupled to
winding and friction, since the cross-entropy's diffusion exchanges action along junctions as it propagates; information
expansion is to be read as cosmological expansion is, `length_a / (time × length_b)`, whose lengths do not cancel, with a
non-commutative order of the operations, the rate a velocity of separation per gap between locales (closest point of
approach, Doppler curves), and the dynamics swinging between which gap is held as the constraint while the others vary.
Sources he named: Bais and Farmer, *The Physics of Information* (arXiv 0708.2837); Su and Liu, *Geometric Capacity of
Transformers: A Tropical Geometry Perspective* (arXiv 2604.14727); Beck and Ramstead, *Dynamic Markov Blanket Detection for
Macroscopic Physics Discovery* (arXiv 2502.21217); Marcolli's course *Geometry of Information* (Caltech, Winter 2025).

[source-inspected; definition; agent-inferred] The joins, each to an owner that already states it or to the term it lacks:
- **The expansion rate is a ratio's logarithmic derivative.** `H = a⁻¹ da/dt` is the ratio calculus `R⁻¹ dR` (the loss
  law); `km s⁻¹ Mpc⁻¹` refusing to cancel is the ratio's undivided pair (the velocity of a separation and the separation,
  typed), never a bare `1/time`. A reading keeps both terms and its clock.
- **Densities.** Nats per volume is an entropy density `s`, nats per time and volume its production `σ`, balanced under the
  material derivative, `∂s/∂t + ∇·J_s = σ ≥ 0` (the cross-entropy law's flux across sections). Expansion of information is
  Liouville's `d ln V/dt = ∇·v` for a flow's phase volume and Pesin's `h = Σ λᵢ⁺` for the rate new information appears;
  packing at a resolution `ε` counts about `ε^(−D)` distinguishable cells, `D` the information dimension (Bais and Farmer
  give the horizon of prediction `τ = (D/h) log s` at signal-to-noise `s`).
- **The denominator.** The field reads bare nats per place, and a place is not a unit of content (a word's first letter
  4.1 bits, its seventh 0.15, §5). The density belongs on the receiver's own partition: per crossing of a section (a word's
  boundary, an epoch), per region and tick (the receipt law), and per 2-cell of the complex, where winding per area is a
  curvature, the Stokes face of a declared loop (holonomy only on declared circuits).
- **The contact row is a thermodynamic semiring.** The row `Σ 2^z μ` at the head's temperature is Maslov's deformed sum
  `h log(e^(a/h) + e^(b/h))`; its tropical limit (`max`, Maslov dequantization) is the loudest partial, and the entropy is
  the deformation between the two (Marcolli's thermodynamic and tropical semirings). Su and Liu's zero-temperature limit:
  keys at equal norm, as the contact holds them (`ratio_to_power`), route by a Voronoi diagram of cosine, and a row whose
  loudest term leads by `δ` errs from its tropical limit by at most `τ log(1 + (N − 1) e^(−δ/τ))`. The held rows' Rényi-2
  effective count (`HeldRows`, §16.20) is already the reading of how tropical a row is; the copy onset (§16.37) is where it
  falls.
- **Markov blankets.** Beck and Ramstead's partition (internal `z`, boundary `b`, external `s`, `p(s, z | b) = p(s | b)
  p(z | b)`) is the probabilistic face of the relatively complete region: the boundary bounds the interior for its
  receivers, and the interior is coupled to the exterior, never determined by it (#410 owes the full theorem).

What a run would need before it honours the lens: the readings above as typed densities on the receiver's partition (not a
scalar per byte), and a per-tick reading of the constitution's expansion (the tick map's growth of a perturbation, the
discrete Lyapunov reading), each with its own clock. None changes a law of the field; they change what a receipt states.
