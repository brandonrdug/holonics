# The problem is one field: every site reads every other, and the answer is refined, not spoken

November 1. Refs #404 #406 #407. Status: [definition; agent-inferred] for the law and each choice,
[source-inspected] for the owners it reuses, [measured] only where a receipt is cited. Claude
(opus), design lead.

Computational object: the helical pair interaction. Of the winding guide's six general objects the
field touches the **helix** (each mode's ring on the dyadic and triadic towers, its residue and whole winding), the
**pair** (every pair of sites meets through its framed modes; the pair contact of two reads of one
site), **faces and placement** (the Gibbs face, the release by lock) and the **tube** (one
constitution iterated over ticks). Cell holonomy and the tower thread stay attached through the
tower, which this owner does not replace.

## 1. Why the machine is rebuilt whole

Brandon, November 1 (paraphrased; his words stay outside the repository): runs launched on a
machine with missing parts waste the time they take, so the machine is to be completed and reviewed
before it runs; the problem is the reading of an object (a dead language from its artifacts, a
species from its fossils) as its solution, which is a question of ontology and non-privileged
perspective, and passes of one byte at a time degrade it.

Read against the working declaration and its receipts (the October 31 codec record, §3 to §5, and
the bytes receipts of `…_receipts/bytes-1101/`), four parts were missing, each measured:
- **Reach.** A question's numbers sit a median 190 bytes before the first calculation (81% more
  than 127 back), and a section's participation reaches at most 128 fine sites, with the frames'
  rotation misaligning a match across sections. No built configuration let an answer's digit read
  the question's.
- **The codec.** The founded units weld digits to their neighbours: of 2,287 first-calculation
  operands the question writes, 552 (24.1%) are the same unit in the question and in the
  calculation. Read in bytes, all 2,287 are.
- **Refinement.** The release spoke one class a pass and never revised it, while the generation law
  asks for a joint field that is refined and whose boundary is released (`CLAUDE.md`, generation and
  action).
- **The card.** Each stream was one serial scan: the profile read the card 42% to 73% busy and its
  memory traffic 10% to 23%, so the parallel extent of the work never reached the device.

These are one omission seen four ways: the problem was heard as a clocked stream when it is one
relatively complete region whose answer is unresolved.

## 2. The object and its law

A GSM8K problem is one relatively complete region. Its question's sites are resolved (their classes
arrived); its answer's are unresolved, held on the encoding's extra last row. Each site carries a
face `x_t` on `2^(−16)`, framed by its place. A head's first `still` modes carry `U = 1`; its
turned mode `l` is slot `s = (l − still)·frames + (h mod frames)` and carries the ring phasor
`U_(t,s) = e^(2πi (t mod n_s)/n_s)`. The periods `n_s` are the solenoid's two coprime towers, the
dyadic `2, 4, 8, …` and the triadic `3, 9, 27, …`, each from its finest closure to the first that
spans the **reach** (the passage's longest region): `⌈S/2⌉` slots on the dyadic tower and `⌊S/2⌋`
on the triadic, each spread evenly from the finest ring to the top (`ring_periods`). A tower read
together is a place's residue and its whole windings at every scale, and its top ring turns less
than once across any region, so it reads a distance and not only a residue. The `frames` ring sets
are the founding's heads and are kept on growth. One constitution is iterated `K` ticks:

```text
open       x⁰_t = E(u_t), or E(∗) at an unresolved site
chart      r̂_t = x_t/‖x_t‖_rms,   q, k, v = Q r̂ + b_q,  K r̂ + b_k,  V r̂ + b_v
frame      q̃_t = U_t ⊙ q_t,   k̃_t = U_t ⊙ k_t,   ṽ_t = U_t ⊙ v_t       complex modes, by head
contact    z_ij = 2^(−β) Σ_(m∈h) Re(conj(q̃_im) k̃_jm),   β = ⌈⌈log₂ 2n⌉/2⌉
weights    e_ij = 2^(z_ij − max_j z_ij),   mass_i = Σ_j e_ij           every pair, both ways
current    y_i = conj(U_i) ⊙ Σ_j e_ij ṽ_j / mass_i,   x ← x + O y + b_o
pair       x ← x + W_c((W_a r̂′ + b_a) ⊙ (W_b r̂′ + b_b)) + b_c        the pair contact law
face       p̂_t = 2^(z_t)/Σ 2^(z),  z_t = R r̂(x^K_t) + c                at the unresolved sites
```

`Re(conj(q̃_i) k̃_j) = Re(conj(q_i) U_i^* U_j k_j)`: a turned mode looks at the relative place
modulo its ring, and `conj(U_i) U_j v_j` carries back what it found turned by that same relative
place, so the current says where its content came from as well as what it was (the phase-carried
moment of the retention law, `m = Σ_k Ĝ(τ(k))⁻¹ E(u_k)`, at the reading site's frame). A still mode
reads and carries contents alone at any distance. There is no clock between sites and no carry
across problems: the region is the whole terrain, so the transferred response a scan's carried
state owed is absent by construction. The pair contact is the tower's `ContactLaw::Pair`, the
contact that led the rectifier on every lap it was raced. A region longer than the reach is
refused, never read on rings that alias it.

**Exact integers.** Faces, charts and currents on `2^(−16)`; material on `2^(−24)`; frames on
`2^(−30)`; the weights `e_ij` read on `2^(−62)` from their row's peak (the exponential's resident
navigator face) and released to `2^(−40)`, so a row of up to `2^(22)` sites sums within 64 bits.
The current is the numerators' sum over their row's one denominator `mass_i`, divided once, so no
weight is rounded into a share before it is summed; the ring phasors are exact at the quarter turns
and the series' faces between. Every product's remainder is released to the nearest numerator and
every sum is an integer sum, so sites, heads and regions summed in any order give the same bits:
any partition of the card agrees with the host.

Owner: `hnn::tower::field` (`Field`, `FieldDeclaration`, `ring_periods`). It reuses the tower's
`affine`, `transposed`, `ratio_to_power` and its adjoint, `covector`, `face_code`, `deposit_step`,
`toward`, `fewer_bits` and `Exponential::below_one` unchanged.

## 3. Learning is completion

Any subset of a region is unresolved and the classes that arrived there are its targets; the code
is `Σ −log₂ p̂_t(u_t)` over the unresolved sites. The covector `p̂ − q` returns exactly through the
`K` ticks with the operands that produced each carrier: the framed values, the weight numerators
and their row's mass. With `δỹ_i = U_i ⊙ δy_i`,

```text
values     δṽ_j = Σ_i e_ij (δỹ_i/mass_i)                         δỹ/mass on 2^(−70)
contact    δp_ij = ⟨δỹ_i, ṽ_j⟩,   μ_i = Σ_k e_ik δp_ik/mass_i,   δz_ij = ln 2 · e_ij (δp_ij − μ_i)/mass_i
frames     δq, δk, δv = conj(U) ⊙ δq̃, δk̃, δṽ
```

checked against the code's central difference on the largest entries of every family and on the
largest turned and still chart rows. The deposit is the tower's: the covector's two moments, the
step at `2^(−k)`, halved until the section's own regions reread under it code strictly fewer bits
(`fewer_bits`, exact cross products of the faces) or it moves nothing. [agent-inferred] Each
coordinate's moments open at its own first nonzero covector (`m = g`, `v = g²`) and move toward
`g, g²` after it; a learner whose moments opened at the first section's mean would carry the
first section's coordinates that read nothing as zero for every later one.

[agent-inferred] **The masks** come from an exterior keyed stream: with even odds the answer's
sites (its void included) or the whole region's are open, each unresolved with probability `τ`
drawn uniform on `(0, 1]` at `2^(−16)`, at least one site. The answer-only half is the release's
own situation at every stage of its refinement; the whole-region half lets the question's language
be learned by the same law. They choose what is compared, never what is deposited.

[agent-inferred] **A training region takes the release's shapes.** The release opens the answer
at the training answers' longest extent `A` and the region shrinks as voids are released, so a
training region is the question, its answer of `a` sites and a void tail of length drawn
octave-uniform on `[1, A − a]` (an octave first, then a length within it, from the same keyed
stream). Every length the release can meet is met, the short tails a release reaches last most
often, at 1.86 times the site pairs of a one-void region (a uniform tail would be 3.42 times). The
held-out read opens the question and all `A` answer sites at once, as the release does, and codes
the answer and its first void.

## 4. The release is refinement

The answer's sites open unresolved (the training answers' longest extent plus its void). Over `S`
sweeps, sweep `s` reads every unresolved face and releases the `⌈r_s/(S − s)⌉` most locked sites
(the top class's share of its face, compared by exact cross products; a tie takes the earlier site,
then the lower class) at their top class. The answer ends at the earliest released void and the
sites past it leave the region, so the next sweep reads the region one site past its answer, as a
training region is read ([agent-inferred]: opened at the longest training answer, 1,228 bytes
against a held median of 270, the void tail would otherwise be carried through every sweep). The
released sites are terrain for the next sweep. No class is spoken in order, and a site is released
where the field is surest, wherever it stands.

## 5. Width is the trained body's

[agent-inferred] `Field::grown` widens by the tower's copies law (`hnn::tower::growth`): width,
heads and contacts by `f`, a head's modes and frames kept, every face coordinate repeated, every
matrix entry split over its column copies into parts that sum to it, with zero-sum differences at
the grown founding's scale (`√(3/fD)`) read from the founding key stream past every earlier draw;
the returns and the readout split evenly. The grown field reads the old faces exactly; the moments
lift to `m/f`, `v/f²` (the readout's kept). Head `bH + h` keeps ring set `h mod frames`, so every
copy of a head reads place on its parent's rings; the frames and the reach are kept. The step's
rate bits rise by `⌈log₂ f⌉`: the lifted moments make each copy's step the parent's, and `f`
copies of it would move the old face `f` times as far, so the first certified deposit on the grown
body moves it no further than the old body's would have. The trainer grows the body by two after a lap whose code
a site, read before each section's deposit, is not below the lap before's: the body has spent its
width. No width is a dial past the founding's.

## 6. The codec is the bytes

The regions are read in classes of a founded-units file compacted to the units the training passage
uses, plus the void. The run reads the founding of no merges, the bytes: every number is the same
classes wherever it is written. A first draft of this build read each digit as one class with its
place; that is the hand-written tokenizer retired on October 27 (`2026-10-27_THE_REVIEW_FINDS…`,
§6) and it was refused before any build or run. The field is codec-agnostic: a founded-units file
runs the same route.

## 7. Realization

`FieldRealization` carries a section's read and return and the certificate's rereads; `HostField`
is the host's, each region on one core, regions across cores. The card's realization implements
the same trait and must return the host's bits: faces, codes, the covector and the learner. Its
parallel extent is problems × sites × heads, against the scan's streams.

[agent-inferred] **The card's realization, stated before it is built.**
- *No online softmax.* A row is read in three passes over its keys (the peak, the numerators and
  their mass, the current's numerators): an online rescaling would round each partial sum at a
  peak that later moves, and the bits would depend on the tile order. The three passes give every
  tile order the same bits.
- *Memory.* A region of `S` sites holds `H·S²` weight numerators per tick on `u64`; the
  passage's reach (about 2,221 bytes) at 8 heads and 2 ticks is about 632 MB a region, so a
  section is sized by the card's memory against the 12 GB the runs keep to, or the reverse
  recomputes `e_ij` from the kept `z` peaks and the charts (the weights are a function of the
  carriers the reverse already holds). Either is exact; which one is the measured cheaper.
- *Ragged regions.* A section's regions have their own lengths; a region is a block of the launch,
  never padded to the section's longest.
- *The read and the time.* Parity is read over 32 sections of GSM8K regions on the faces, codes,
  covector and learner; the time per site is measured on the opening sections and projected before
  any learner run.

`release-field` writes each problem's rows as its release returns, so a stopped run keeps what it
read; a release the field refuses (a region past the reach, a carrier outgrown) is written as
refused and counted, never skipped.

Commands (`complete-language`, `hnn::tower::field` through `field_train`): `train-field` (founded
or continued learner, sections of like-length problems, a keyed walk each lap, the held-out read
after each lap, the growth rule), `release-field` (each held problem's release from the question
alone and at each calculation's equals, written for `written_rules.py` as `FREE.tsv` and
`MARKS.tsv`, and each free release's coupling read in `COUPLING.tsv`), `release-field-text` (a
private read of whole releases).

## 8. Acceptance, fixed before the run

1. **Host law** (tests in `field/tests.rs` and `field_train`): the covector agrees with the code's
   central difference on the largest entries of every family and on turned and still chart rows,
   framed and still; a still field is order-free and a framed one reads place; with the contact's
   weights made flat, the current still carries place on turned modes and not on still ones; the
   rings sample both towers to the reach and a region past the reach is refused; regions sum to
   the same bits in any order; certified deposits lower the code; the release ends at its first
   void and its region is cut past it; the grown field reads the old faces by two and by three, the
   draws counted are the draws read, and its learner lifts the moments and parts its copies; the
   training tails meet every octave of their room; the commands train, rest, continue and release
   end to end.
2. **Card parity.** The card's realization equals the host bit for bit (faces, codes, covector,
   learner) over 32 sections of GSM8K regions; its time per site is measured on the opening
   sections and projected before any learner run.
3. **The reading** (the bytes, the 125 held problems the route reads, a run projected and bounded
   at 15 minutes on the card): the held-out answer code beside the written rules (the first
   calculation from the question's numbers; met and never-met calculations right at the equals)
   and the coupling read. **The claim**: the first calculation from the question's numbers in at
   least 24 of 125 releases, twice the route's best (5 to 11). Until it passes, what the run
   measured is reported, not a completion.

**What follows each outcome.** If the copy reading passes, the field is the route's generation
and the next loop is never-met arithmetic (the carry). If it fails with the held-out code falling,
the failure is located by the copy partition (answer digits the question writes against those it
does not) before anything is added. If the code does not fall, the projection and the learner's
receipts (halvings, deposits) are the next loop's subject.

## 9. The recorded failures this build could repeat

- **An authored routine standing in for learning.** The digit-place codec was refused (§6). The
  release has no grammar, stop rule or copier: it releases where the field locks.
- **Text run on its codec's grain as the exception.** The field meets classes; bytes are the grain
  of text, image, acoustic and motor input alike, and nothing names a digit.
- **Bits read as progress.** The claim is a written-rule reading; bits are reported beside it.
- **Seen material graded as unseen.** The held problems never enter a section.
- **An uncertified deposition step.** Every deposit is certified on its own regions.
- **A located cause carried unrepaired.** The welded codec and the 128-site reach are not carried
  into the field.
- **A store.** Nothing is written to be looked up: every site reads every other site's own face
  through the constitution, and the region dissolves after its read.
- **A design thought in arrays.** The places are the rings' residues and windings, the copies the
  growth's parts, the release a placement by lock.
- **A refusal answered with a larger limit.** The run's deadline is its projection's upper end; a
  run past it is reported incomplete.

**Formal obligations (#410).** The field's growth preserves faces (the copies law at the field's
frame map); the completion covector is the logarithmic derivative of the region's code at the
unresolved sites; integer sums over any partition of sites, heads and regions are equal.

## 10. The review before any run

An independent review read the whole machine (law, learner, trainer and release) before any card
work, against this record and the lessons records. Its confirmed findings, and one found while
repairing them (the grown body's step), were repaired in the same change as this section; the host
tests above are the receipt.

| Finding | Repair |
|---|---|
| A training region ended one site past its answer, so its length told the field where the answer ends, and the release, which opens the longest answer and shrinks, never met such a region. | A keyed void tail, octave-uniform on `[1, A − a]` (§3); the held-out read opens at the release's own extent. |
| The prime-power rings `2, 3, 4, 5, 7, 8, …` all closed within a few tens of sites, and sites `lcm` apart (840 for six rings) shared every frame inside a region. | The dyadic and triadic towers to the reach; a region past the reach is refused (§2). |
| The values were not framed: the current said what a site found and not where it came from, so the place a turned mode located was lost on the way back. | The phase-carried current `conj(U_i) Σ e_ij U_j v_j / mass_i` (§2). |
| Each weight was rounded to a share on `2^(−30)` before it was summed, so a row's shares did not sum to one and the covector's mean read rounded shares. | Numerators on `2^(−40)` over the row's one denominator, divided once (§2, §3). |
| The learner's moments opened once, at the first section, so a coordinate the first section did not read opened at zero for every later section. | Each coordinate opens at its own first nonzero covector (§3). |
| A grown body's copies each took the parent's step, so the first deposit moved the old face `f` times as far. | The rate bits rise by `⌈log₂ f⌉` (§5). |
| The release carried its void tail through every sweep, wrote nothing until the end, and stopped at its first refusal. | The region is cut past the first released void; rows are written as each release returns; a refusal is written and counted (§4, §7). |
| The mask stream was seeded by the key file's first word, the same bytes the founding's first draw reads. | The key file's last word seeds it, apart from every founding and growth draw. |
| A continued run keyed its walk and masks by the invocation's own lap count, so it replayed the first lap's. | The learner carries its laps in its text and the walk is keyed by them. |

Read and not adopted:
- *Releasing a site's neighbours with it.* A release that freed a site's neighbours together would
  be a one-dimensional grain authored into a field that has none; joint dependence between sites is
  what the sweep count `S` is for, and its reading is the next loop's subject if the release
  fragments.
- *"Residue and whole winding" as an overclaim.* It was one on the prime powers; on the towers a
  ring `p^(k+1)` reads ring `p^k`'s residue and its whole winding, so the claim now holds as worded.
