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
(`fewer_bits`, exact cross products of the faces) or it moves nothing. The certified step is then
held and read on the next section's regions, which it was not fit on (§11): where the stepped
material codes them higher than the material before the step, it is read at half its size and, if
that codes them higher too, at the halving the parabola through those two reads places lowest, or
refused (§12).
[agent-inferred] Each
coordinate's moments open at its own first nonzero covector (`m = g`, `v = g²`) and move toward
`g, g²` after it; a learner whose moments opened at the first section's mean would carry the
first section's coordinates that read nothing as zero for every later one.

[agent-inferred] **The masks** come from an exterior keyed stream. With even odds a region takes the
whole-region mask, each site unresolved with probability `τ` drawn uniform on `(0, 1]` at
`2^(−16)` (at least one site), or the release's own state at `ρ` drawn uniform on `[0, 1)` at
`2^(−16)`: every answer site open but the first `⌊ρ r⌋` in the release's order (§4), read from the
field's faces with every answer site open, with the question and without it. The second half meets
the state a release opens on and the states its sweeps pass through; the whole-region half lets
the question's language be learned by the same law. They choose what is compared, never what is
deposited. (The first draft's answer-only half opened each answer site with probability `τ`, so it
almost never met a release's states; §11.)

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
sweeps, sweep `s` reads every unresolved face twice, with the question and with the question's
sites unresolved (the released answer kept), and releases the `⌈r_s/(S − s)⌉` sites whose top class
carries the most news (`by_news`): the key is `p̂(c) ν` with `ν = (−log₂ p̄(c)) − (−log₂ p̂(c))`, the
bits the question tells the site about its top class `c` beyond what the place and the released
answer already tell, compared exactly; a tie takes the earlier site, a top-class tie the lower
class. The answer ends at the earliest released void and the
sites past it leave the region, so the next sweep reads the region one site past its answer, as a
training region is read ([agent-inferred]: opened at the longest training answer, 1,228 bytes
against a held median of 270, the void tail would otherwise be carried through every sweep). The
released sites are terrain for the next sweep. No class is spoken in order, and a site is released
where the question tells it most, wherever it stands. Many problems are released together, one
read of every problem a sweep; a region's faces do not depend on the regions read beside it, so
each release is the problem's own. (The first draft released where the field was surest, by the
top class's share; §11.)

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
body moves it no further than the old body's would have. The trainer withholds as many training
problems as the held file holds (keyed, never in a section) and reads them after each lap at the
release's opening, every answer site and a keyed void tail unresolved, the same regions and sites
every lap; the lap's last held step is read on them first. It grows the body by two after a lap
that leaves them coding no fewer bits a site than the lap before left them: the body has spent its
width. (Not at the release's states at `ρ`: their resolved sites are the first in the field's own
news order, so a site the field learns leaves the compared set, and code a site would compare a
different set of sites each lap.) No width is a dial past the founding's. (The first draft read the passage's own code,
which fell every lap; §11.)

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

`release-field` releases every held problem together, a sweep of all of them in one read, then
every calculation's continuation together, and writes each set's rows as it returns (a stopped run
keeps the free releases once they are read); a release the field refuses (a unit the codec never
met, a region past the reach) is written as refused and counted, never skipped.

Commands (`complete-language`, `hnn::tower::field` through `field_train`): `train-field` (founded
or continued learner, sections of like-length problems with the withheld problems apart, a keyed
walk each lap, the held step read on the withheld problems and the held-out read after each lap,
the growth rule), `release-field` (each held problem's release from the question
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
   end to end. Since §11: the release orders by the question's news, not the share; problems
   released together are each problem's own release; a held step read on the next section leaves
   the material the law decides (at its size, at half, at the parabola's halving, or refused), which
   codes it no higher than the material before the step, and the section's opening read is the
   standing material's; a learner holding a step
   does not widen, and the held step crosses the learner's text; the release's state resolves the
   ranked sites first and leaves one open; the withheld problems are in no section and are read
   at the release's opening, the same regions every lap; a held step that climbs the next regions'
   code is refused within four reads and the material before it stands.
2. **Card parity.** The card's realization equals the host bit for bit (faces, codes, covector,
   learner) over 32 sections of GSM8K regions; its time per site is measured on the opening
   sections and projected before any learner run. [measured] Passed (acae723b6, receipts in
   `…_receipts/card/`): at D 32, H 4, n 8, still 2, f 32, K 2, 32 sections of 16 regions, 64 reads
   and 4 releases equal, and the same grown by two; 2.4 to 3.8 ns a site pair, a lap of the
   passage projected at 110 s and 213 s grown, card 7.0 s against host 116.5 s on the parity.
3. **The reading** (the bytes, the 128 held problems the field reads, a run projected and bounded
   at 15 minutes on the card): the held-out answer code beside the written rules (the first
   calculation from the question's numbers; met and never-met calculations right at the equals)
   and the coupling read. **The claim**: the first calculation from the question's numbers in at
   least 24 of 128 releases, twice the route's best (5 to 11 of about 125). Until it passes, what
   the run measured is reported, not a completion. (The held file holds 128 problems and every one
   passes the answer filter; the route's readings counted about 125. The bar stays 24.)

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
- **An uncertified deposition step.** Every deposit is certified on its own regions, then read on
  the next section's regions, which it was not fit on (§11).
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

## 11. The first reading failed, and the four causes it located

[measured] The first reading (receipts in `…_receipts/reading-1/`, counts only; the card on B-PC,
an RTX 4080 SUPER): the field at declaration A (D 32, H 4, n 8, still 2, f 32, K 2; 19,546 values)
trained 4 laps of the 6,730 training problems in sections of 16 at rate 8 in 383 s, then released
the 128 held problems at `S = 16` in 28 s.

| Reading | Value |
|---|---|
| First calculation from the question's numbers (the claim: at least 24 of 128) | 1 of 128: **failed** |
| Right at the equals | 17 of 399 (16 of 260 met, 1 of 139 never met) |
| Values written at the equals | 396, of which 228 are `10`; 10 distinct values |
| Released length | mean 70 classes, held answers' 277 |
| Releases using the problem's own words | 0 of 128 |
| Held answer's code at the release's opening, by lap | 5.38, 5.49, 6.18, 5.22 bits a class (flat 6.93; digits above 6.3) |
| The passage's own code, read before each deposit | 3.43, 2.83, 2.72, 2.64 bits a class |
| Deposits | 420 of 421 sections, then 421 of 421 each lap; the body never grew |

Each cause below is located from those receipts, not inferred from the outcome alone.

1. **Training rarely met the release's states.** The answer-only half opened each answer site with
   probability `τ`, so nearly every compared site had most of its neighbours resolved; a release
   opens with every answer site unresolved and passes through states where the sites it released
   are resolved and the rest open. Read at the release's opening the held answer coded 5.2 bits a
   class against the passage's 2.6, worse than the bytes' own frequencies.
2. **The release by share released what the place alone predicted.** The top class's share counts
   certainty the question did not supply: a space, `e` and the void, which the place predicts
   anywhere, were released first, and each made the next likelier. The void ended releases a median
   71 classes into answers whose median is 254, and the equals wrote `10` in 228 of 396.
3. **The certificate read only its own section.** The held answer's code rose at the second lap and
   the third while the passage's own code fell every section. The tower had recorded this failure
   and its repair (acceptance 77, `TowerLearner::next_section`); the field was built without it: a
   located cause carried unrepaired into a new consumer, the lessons' fourth failure.
4. **Growth read seen code.** It grew when the passage's code, read before each deposit, stopped
   falling; that code fell every lap while the held code rose, so the body never grew.

The repairs, built and tested on the host before any card run:

| Cause | Repair | Owner |
|---|---|---|
| 1 | Half the training regions take the release's state at a keyed `ρ` (§3): every answer site open but the first `⌊ρ r⌋` in the release's order, read from the field's whole-open faces with and without the question. | `field_train::{shape, released_state, section_regions}` |
| 2 | The release orders by the news the question gives each site's top class, `p̂(c) ν` (§4): a class the place and the released answer already predict carries no news and is released after the classes the question decides. | `field::by_news`, `Field::release_realized` |
| 3 | A certified step is held and read on the next section's regions; where it codes them higher it is halved against the material before it, or refused. The lap's last step is read on the withheld problems. The learner's text carries a held step (`hnn-field-learner-v3`). | `FieldLearner::{open, read_step_on, section_realized}` |
| 4 | As many training problems as the held file holds are withheld (keyed, in no section); growth reads their code at the release's opening after each lap, the same sites every lap (§5). The held file stays a reading only. | `field_train::{sections_of, unseen_regions, unseen_read, train}` |

[agent-inferred] **What the repairs cost.** Reading 1 measured a section's read at 31 ms and its
return at 191 ms (1,846 reads in 56.7 s, 1,684 returns in 322.3 s). A section now adds two reads of
its release-state half (one section's read between them) and one read under the material before
the held step, about 62 ms; a halving adds one read. A lap at A projects at about 1.3 times reading
1's, 125 s against 96 s. A release reads twice a sweep, every problem's sweep in one read.

**Read and not adopted.**
- *Releasing the answer in blocks from its start* (semi-autoregressive refinement). It would author
  an order into a release that has none; the void's early release, which blocks are used elsewhere
  to stop, is the place's prediction, and the news cancels exactly that.
- *Reopening released sites of low certainty.* A released site is terrain at width zero; a release
  that withdrew its own terrain would make the sweep count no longer the refinement's measure.

The claim and its bar are unchanged: the first calculation from the question's numbers in at least
24 of 128 releases, read on the same 15-minute reading. What follows each outcome is §8's.

## 12. The second reading stopped in its first lap, on the held step's rereads

[measured] The second reading (receipts in `…_receipts/reading-2/`, count-only; field_pass
`2abf6f50…f5eb` at c846f15bc): the card's parity with every repaired read passed at A over 8
sections and grown by two over 4, each with the withheld problems' read and batched releases
(every read, face, covector, learner and release equal). time-field projected a lap at A at
114.4 s, so the watcher's bound was 149 s a lap. It stopped the training inside its first lap,
after 336 of 413 sections, at 150.0 s; no lap ended, so no state was written and nothing was
released. The claim was not read.

The cause, read from the 336 sections:

| Reading | Value |
|---|---|
| Sections whose held step coded the next section higher | 131 of 334 read (7 of the first 49; 73 of the last 135) |
| Rereads the halving took on them | 1,608; the step was refused on 26 |
| Halvings at which the other 105 stood | 1 to 4 on 27, 5 or 6 on 2, 8 to 18 on 76 (12 or more, `2^(−12)` of its size or less, on 67) |
| Time of those 131 sections | 101.1 s, against 49.0 s for the other 205 (239 ms each, inside the projection) |
| The section's own code read before its deposit | 6.93 at the first, 3.3 to 3.5 by the last hundred |

[agent-inferred] Two failures, both the lessons' own. The halving searched a step's size where its
direction was the cause: a step that still codes the next regions higher at a twelfth halving
raises their code to first order, and halving it further only shrinks it until rounding leaves
nothing. And the projection timed eight opening sections, none of whose held steps coded the next
section higher, so it never met the cost it was bounding: a run projected from a cost it did not
read.

The certificate carried the same search: a section's step was halved until it coded its own
regions strictly fewer bits, and those halvings reached 9 to 18 on 14 of the 336 sections (16 on
five, 18 on two). A located cause was repaired in one consumer and left in the other.

**The repairs** (`scaled`, `FieldLearner::next_scale`, `FieldLearner::section_realized`,
`field_train::train`, `field_parity::time`):
- One law reads a step's size, for the held step on the next regions (no more bits) and for the
  certificate on its own (strictly fewer bits). The step is read at its size and, where that does
  not stand, at half its size. Where both code them higher, the excesses `e(1)`, `e(½)` over the material before the step
  fix the parabola `e(μ) = aμ + bμ²` with `a = 4e(½) − e(1)`: with `a ≥ 0` the direction climbs
  and the step is refused; with `a < 0` it is read once more at the largest halving at or below the
  parabola's lowest point `μ* = −a/2b`, and stands there if it codes them no higher, else is
  refused. For the held step at most four reads precede the opening read, and a refusal leaves
  the material before the step, so the standing material still never codes the next regions
  higher; the certificate makes at most three reads after the opening read, and a section whose
  step stands at none of them deposits nothing. On the second reading's sections the held step's
  halving took eight to nineteen rereads on 102 of the 131 steps (76 stood at eight or more
  halvings, 26 were refused); the law decides each in at most two more reads.
- The stepped material is read without its covector, and the opening read with the covector is
  made once on the material that stands (a halved step's covector was read and discarded).
- time-field times one more read of each timed section and projects a lap with every section's
  reads and return at the worst measured time a pair and four more reads of it, the most the held
  step's read and the certificate add to sections whose steps stood at their size: an upper bound
  that holds whatever the steps do.
- The training's bounds are its own. train-field takes the lap's bound before any growth and after
  one, and the run's, and at the first section that ends past either it reads the pending step on
  the withheld problems as a lap's end does, rests as `STATE.stopped` and stops (`FIELD_STOPPED`,
  with the partial lap's code and its withheld read). The second reading's watcher stopped the
  trainer from outside, so 336 sections of learning left no state; a stopped reading now releases
  from where it stopped and is reported incomplete.

Not adopted: lowering the rate. The tower's half-rate read (record of October 30, §45, acceptance
76) traced its run-away to the step's size; here the harm is the direction on 102 of 131 sections,
and the held step's read refuses exactly those, so the rate stays the founding's until a reading
shows the refusals, not the rereads, are what holds the learner.

The third reading's script is `…_receipts/reading-3/reading3.sh`, its bounds fixed from
time-field's projections before launch.

The claim and its bar are unchanged; the next reading is the same 15-minute reading.

## 13. The third reading wrote the commonest byte at every site

[measured] The third reading (receipts in `…_receipts/reading-3/`, count-only; field_pass
`4f89e62b…bdffb` at 8982ff68b): the card's parity with the bounded law passed at A over 8 sections
and grown by two over 4 (48 and 24 reads, every face, covector, learner and release equal).
time-field projected a lap at 184.8 s at A and 343.0 s at B and the 527 held releases at 96.1 s
from A's founding; two laps did not fit the 870 s reading, so it trained one lap (`LAPS 1`, the
trainer's bound 241 s, the release's 125 s).

| Reading | Value |
|---|---|
| The lap | 413 sections in 117.1 s; 394 deposited; the sections' code 3.823 before their steps, 3.792 after |
| The certificate | read at its size on 368 sections, at one halving on 34, at three to five on 11; 19 deposited nothing (`scaled` decided every one in at most three reads after the opening) |
| The held step on the next section (393 read) | stood at its size on 230, at one to seven halvings on 35; refused on 128 (125 at the first halving, where `a ≥ 0`) |
| The withheld problems at the release's opening | 6.931 bits a site at the founding, 3.534 after the lap |
| The held answers at the release's opening | 6.931 at the founding, 5.342 after the lap (digits 5.767, text 5.259) |
| The card | 2,270 reads in 51.6 s (22.7 ms each), 413 returns in 64.7 s (157 ms each), 1.77·10¹¹ site pairs in 118.9 s: 0.67 ns a pair |
| The release | 128 problems, S = 16, 64 reads in 29.6 s, 7.46·10¹⁰ pairs (0.38 ns a pair) |
| The board | 13,372 MiB at its peak, over the 12 GiB the card's runs keep to: the release's batches were sized from the card's free memory (10.37·10⁹ bytes), not from the bound |
| The claim | the first calculation from the question's numbers in 0 of 128 |

Every released site of the 128 free releases was a space. At the 399 calculations' equals, 366
releases were unfinished and the 27 that wrote a number wrote `0`.

The training answers' own byte tables, the floors a reading compares against (bits a byte, each
class read from the classes before it in the same answer; in-sample, so the longer contexts sit
below what any learner reaches on unseen answers):

| Context | 0 | place | 1 | 2 | 3 | 4 | 6 |
|---|---|---|---|---|---|---|---|
| Bits a byte | 5.045 | 5.008 | 3.459 | 2.693 | 2.215 | 1.983 | 1.956 |

The space is the commonest class, 16.4% of the answers' bytes.

[agent-inferred] Two failures, both the lessons' own.

1. **The release forced a quota where the field had nothing to say.** From the all-open state it
   released `⌈r/(S − s)⌉` sites a sweep, 77 of 1,229 at the first. There every open site reads the
   question and its place alone, and after one lap that face codes the held answers at 5.34 bits a
   byte, just above the bytes' own table (5.05) whose top class is the space. A site's top class
   was the space nearly everywhere, the news key ranked spaces as readily as anything, and each
   released space made its neighbours' spaces likelier. The answer's information lies in its
   neighbouring bytes (four before a site code it at 1.98 bits), and a quota released a twelfth
   of the answer before any neighbour stood: the first reading's `10`, written at 228 of 396
   equals, was the same failure with the commonest number.
2. **The held read and the growth's withheld read sat at the release's opening.** That opening's
   code has the bytes' table, given the question and the place, as its floor, so it could not show
   what the field learned of an answer's own bytes; the growth compared readings that could not
   fall, and a reading at 5.34 was read as the field's state.

**The repairs** (`Field::release`, `resolved`, `field_train::context_regions`, `held_out`,
`unseen_regions`, `field_parity::time`):
- **Release by resolution.** A sweep releases every open site whose top class outweighs every
  other class together (`2 m_c > Σ m`), so a release is likelier right than wrong; where no site of
  a problem resolves, it releases the one site the question tells most (the news key, read once
  more with the question unresolved). A site waits for the sites that inform it, and each released
  site is their terrain. The release returns the answer through its first site still unresolved.
  A sweep makes at most two reads, as before.
- **The answer read with its neighbours.** The withheld problems (the growth's read) and the held
  answers are read in `CONTEXT = 4` parts: in part `r`, the answer's sites and its first void at
  `t ≡ r (mod 4)` from the answer's first site are unresolved and every other site resolved, so each
  site is read once with the three sites on each side of it standing, the terms a release that
  commits only what the field resolves runs on. The held read keeps the opening beside it
  (`FIELD_HELD … context= context_digits= context_text=`).
- **The projections read what they bound.** time-field's lap adds the lap's end (the held step's
  five reads of the withheld problems and the held read, now four and five times their regions)
  at the worst measured read time a pair, where the third reading's script allowed ten seconds.
  The release's time a pair divides by the pairs the timed releases read (counted, as the card
  counts them) instead of the pairs a release reads at most: the founded field at B released its
  void at once, read few pairs, and its projection (17.4 s) came out a sixth of A's.

The memory bound is owed: the release's batches are to be sized from the 12 GiB the card's runs
keep to.

The binding constraint is the card's throughput. A lap of a 19,546-entry field took 117 s, a lap
is 413 steps, and a fifteen-minute reading holds about seven of them. At 0.67 ns a pair the card
spends about 17,000 lane-clocks on a pair (10,240 lanes at about 2.5 GHz; agent-inferred from the
declared clock), where a pair's arithmetic is a few hundred integer operations; the contact row stores every weight
`e_ij` (8 bytes a pair) and reads it once for each of the `n` values, and the keys' return reads
the weights down a column, `sites` words apart. The profile of where the card's time goes is the
next loop's subject, before the next reading.


## 14. Before the fourth reading: the card's passes, its memory and the release's end

[agent-inferred, November 1] The review of §13's three owed items, made before any further run.

**The card's passes** (`kernels/field.cu`; each restructure is stated where it lives). Every
change keeps the host's bits: the sums are integer sums on `Z/2^128`, so any order and any
partition of them give the same 128 bits, and the one division changed in form is the exact
integer quotient.
- The contact's forward computes each weight, its mass and the numerators of eight modes in one
  pass over the row (the first realization read every weight back once for each mode).
- The contact's return of a row divides its pairs by the row's mass as an invariant divisor
  (Möller and Granlund 2011, Algorithm 4: the normalized divisor and its reciprocal read once a
  row, two word steps a quotient), where each pair ran a 128-bit software division; it sums eight
  entries of the span in one pass. The quotient routine agrees with the plain `⌊n/k⌋` rounded to
  the nearest on 300,000 drawn and the edge operands (a host check of the same steps).
- The keys' and values' return reads the weights along rows: a block takes 32 consecutive source
  sites, a lane each, and its eight warps split the receivers, so a warp's reads are one run of
  the store; the warps' partial sums meet in shared memory. The first realization read a column,
  its lanes 32 rows apart, once for every entry of the span.
- A covector entry is summed by one thread a tile of 64 sites, its partial added by the ring's
  atomic step (two 64-bit atomics with the low word's carry); the encoding's rows are cut into
  segments of 64 sites the same way. The first realization gave a bias of 32 entries to 32
  threads over every site of the batch, and the unresolved row's column to one thread.
- Compiled for `sm_89` (NVRTC, then `ptxas -v`), no pass spills: 122, 96, 72, 40 and 32
  registers; the columns' pass holds 32 KiB of shared memory. Parity and time on the card are
  owed before the reading.

**The memory** (the card session's commit `802baa8b5`, receipts `card-memory/`). The batch budget
counted a region's weights and contact returns (its pairs) and left every carrier sized by the
batch's sites to a 1 GiB margin; a batch of short regions holds tens of thousands of sites at
about 35 KB a site with two kept ticks, and the board reached 13,372 MiB against the 12 GiB the
runs keep to. `region_octets` counts everything a region allocates and `batches` plans whole
regions within the budget: reading 3's release from its own state then peaked at 11,256 MiB, its
releases byte-identical, and both parities stayed equal.

**The profile** (commit `857495f53`, receipts `card-profile/`; Nsight is not installed on the
card's host, so every launch, copy and allocation was timed alone with the stream drained). On a
training section at A, the kernels are 75% of the wall and the contact family 72% of the
kernels' time: the forward 3.7 ms a launch, the keys' and values' return 5.1 ms (its column
reads), the rows' return 1.4 ms, the covector sums 14 ms over 30 launches. On a release, the
forward contact is 86% of the kernels' time, and the host a third of the wall (about 7 ms a read:
the regions rebuilt and the material, rings and roots uploaded again each read). These are the
first realization's passes; the rewrite above is aimed at exactly them, and its time is owed.

**The release's end.** Under §13's release a sweep releases at least one site of every open
problem and more where the field resolves them, so a release given `S = 16` sweeps could stop
sixteen sites into an answer whose first calculation sits a median 59 bytes in: the reading's
claim was out of its reach by construction. The release's sweeps are now bounded by the codec's
open answer sites, where every release ends, and its time by its exterior: `ReleaseSweep` is
asked before every sweep and the commands answer from their deadline (`STOP_MS`), fixed before
launch from time-field's projection of one sweep of each set (`free_sweep_ms`, `marks_sweep_ms`).
The free releases run first; a set stopped at the deadline is returned as released and counted
open. Each sweep's line reports the sites released by resolution and by news, which reads whether
the field resolves many sites a sweep once a few stand (a site's three neighbours on each side
coded the withheld answers at 3.53 bits in the third reading) or only the one the news releases.

The fourth reading's bounds (`reading-4/reading4.sh`): the lap bounds as the third reading's,
from time-field's projections; `TEXT_S = 60`; the release keeps at least 1.3 times 128 free sweeps
(`free_sweep_ms` of the widest state the run can reach), the sweeps that release 128 sites of
every answer, past the first calculation's 90th percentile of 110 bytes, if only the news releases
them; two laps only where that release fits beside them, and every second left to 870 s goes to
the release.


## 15. The fourth reading: every answer ended where its void crept, and one lap fit

[measured] The fourth reading (receipts in `…_receipts/reading-4/`, count-only; field_pass
`c8ba33c2…5b1` at 75df5e3f1): the card's parity with the bounded law passed at A and grown by two
(`parityA6`, `parityB6`). time-field projected a lap at 216 s at A and 407 s at B, so the reading
trained one lap (`LAPS 1`, the trainer's bound 226 s) and reserved 554 s for the release.

| Reading | Value |
|---|---|
| The lap | 413 sections in 82.8 s (117.1 s in the third reading); 394 deposited; the sections' code 3.823 before their steps, 3.792 after, the third reading's bits |
| The withheld answers read beside their neighbours | 6.931 bits a site at the founding, 4.534 after the lap (36,763 sites: the answer and its first void) |
| The held answers | at the opening 5.341 (digits 5.765, text 5.258); beside their neighbours 4.548 (digits 4.815, text 4.496); the training answers' own tables 3.459 at one byte of context, 1.983 at four |
| The card | 2,287 reads in 55.6 s, 413 returns in 27.9 s (68 ms each, 157 ms in the third reading), 1.90·10¹¹ pairs in 86.1 s |
| The profile of a section | the forward contact 38 of the kernels' 73 ms (3.8 ms a launch); the rows' return 10 ms, the columns' 8 ms, the affine reads 9 ms |
| The release | 128 free releases in 81 sweeps and 399 marks in 85, none stopped; 289 reads in 35.0 s, 9.2·10¹⁰ pairs; 36 s of the 554 s reserved |
| The board | 11,299 MiB at its peak, within the 12 GiB |
| The claim | the first calculation from the question's numbers in 0 of 128 |

Every free release ended at its void after 7 to 54 sites (3,491 sites over 128 answers, mean
27.3) against held answers of median 254; at the 399 calculations' equals 372 releases had
written no number and 9 were unfinished, and the 18 numbers were all `0`.

[agent-inferred] Two causes, the first a defect of the release's law, the second of its bounds.

1. **The void crept.** Released as an ordinary class, the void is the one variable whose classes
   nest: a void at `t` implies a void at every later site. A released void at `t + 1` says the
   answer's extent `L` is at most `t`, and given that the void at `t` is likely by `1 − h(t)`, `h`
   the hazard of `L` at `t`, small wherever `L` is spread. So each released void made the void
   before it resolve by majority, and the answer's open sites before it, which alone could stop it,
   were not yet standing. A release by marginal majority, iterated on a nested boundary, moves the
   boundary toward the least extent the field admits, whatever the field has learned. The first
   sweep of the free set resolved 108,272 of its 157,312 open sites (128 answers of 1,229), most of
   them past any answer's end, and the answers closed around the few content sites standing.
2. **One lap, because the release was reserved twenty times its cost.** The release's reservation
   came from `free_sweep_ms` at the widest state and the codec's whole extent of sweeps; it ran in
   36 s of 554. The lap's time was bound by the forward contact, untiled: a warp a row read every
   key and value of its region from global memory, so each was read once for every row, and ran
   the exponential's root-product loop for every pair.

**The repairs.**
- **The boundary follows the content** (`Field::release_with`, test
  `the_void_follows_the_released_content`). The void is released only at the answer's first open
  site, every answer site before it released, by resolution or by the news (whose order is then
  searched for the first admitted site, and the first open site is always admitted, so a sweep
  still releases a site of every open problem). No void is ever read beside another released
  void, so the boundary is read against the content alone. The host's bounded tests pass (22).
- **The card's forward contact reads tiles** (`field_contact`, `kernels/field.cu`). A block holds
  eight consecutive receiving rows of one region, a warp a row; the keys and values of 32 source
  sites are loaded once into shared memory, transposed with a stride of 33, and every row of the
  block reads them. The row is read in two passes, its peak and then its scores, weights, mass and
  numerators recomputed, so no partial sum is rounded at a peak that later moves; a lane holds one
  entry of the span. The weights are stored only where a return's reverse reads them.
- **The exponential's resident face** (`field_exponential`, `below_one_face`): the face of
  `2^(−x)` below one is computed once a run by the same root-product loop, `2^digits` words (65,536
  at the reading's declaration, counted against the batch budget), and each pair reads it by one
  lookup and a shift. A table built by the navigator's own loop at its declared grain is its
  resident face, not an authored table.
- **Carriers as wide as their terms** (the precision law: width is dynamic). The frame raises the
  binary lengths of the tick's largest framed probe, key and value (`bits`, zeroed each tick). Where
  `q_b, k_b ≤ 31` and `q_b + k_b + ⌈log₂ span⌉ ≤ 62` a score is summed in 64-bit integers from
  32-bit products; where `v_b ≤ 31` and `21 + v_b + ⌈log₂ sites⌉ ≤ 62` the numerators are two 64-bit
  sums over the weight's 20-bit halves, joined in 128 bits. Otherwise the 128-bit path runs. Both
  are integer sums, so they give the host's bits in any order. `ptxas -v` for `sm_89`: the contact
  64 registers, no spills.
- **The release's bounds** (`reading-5/reading5.sh`). The reading holds 900 s. The release takes
  300 s (agent-inferred: under the boundary law a release reads its whole opening extent until its
  content reaches its end, so its sweeps cost the opening's and their count is the trained field's
  own, which no founding read projects), the text 30 s, the starts 30 s, and training the rest,
  540 s, as `⌊540 000 / P_A⌋` whole laps at the projection's upper end.

An adversarial review of the change before any run (a Sonnet reviewer, read-only) rebuilt the
face with the card's loop and compared it with the host's `below_one` on 201,000 arguments (the
edges among them), emulated the narrow sums and their join for every even span to 32 and region
sizes from 1 to 257, checked the shared carve-up against `contact_shared`, the barriers and the
boundary law's progress (the first open site is always admitted, so no release stalls), and found
these equal. It found one stale test (`a_regions_octets_count_its_carriers_beside_its_weights`
still charged weights to a read), now corrected; the weight's split is derived from the declared
grain (`WEIGHT_HALF`, checked at compile time). The card crate's host tests link only where the
card's driver is, so they run with the parity checks.

Not adopted yet: the rows' and columns' returns in the same tiles and narrow carriers (18 of 73 ms
a section), and the certificate's repeated reads of one section (about 5.5 reads a section). The
fifth reading is `reading-5/checks.sh` (parity at A and B, the profile, time-field), then
`reading5.sh` from the two time logs.

## 16. The fifth reading: the text around the answer was learned, its digits not yet, and the release ran out of time

[measured] The fifth reading (receipts in `…_receipts/reading-5/`, count-only; field_pass
`99c8820e…993e78` at d5cc328ce): the card's parity with the host passed at A and grown by two
(`parityA7`, `parityB7`). The tiled contact ran at 1.26 ms a launch (3.81 ms in the fourth reading);
the columns' return 1.04 ms, the rows' 1.15 ms. time-field projected a lap at 96.7 s at A and
183.4 s at B, so the reading trained `⌊540 000 / 96 682⌋ = 5` laps and reserved 300 s for the release.

| Reading | Value |
|---|---|
| The laps | five, 48.9 to 49.8 s each (82.8 s in the fourth reading); 394, 405, 408, 411 and 413 of 413 sections deposited; the sections' code after their steps 3.792, 3.477, 3.374, 3.172, 3.096 |
| The withheld answers read beside their neighbours | 4.534, 4.192, 3.560, 3.082, 2.895 bits a site (36,763 sites) |
| The held answers beside their neighbours | 4.548, 4.178, 3.553, 3.071, 2.885; their digits 4.815, 4.263, 4.021, 3.684, 3.464; the text 4.496 to 2.772 |
| The held answers at the opening (the question alone) | 5.341, 5.467, 5.743, 5.731, 5.233; the digits 5.765 to 6.017 |
| The card in training | 11,826 reads in 123.7 s, 2,065 returns in 115.7 s, 9.49·10¹¹ pairs in 250.0 s; the largest store 3.02 GB |
| The release | the free set 590 sweeps in 300 s (509 ms a sweep) and stopped at its deadline with 82 of 128 open; the marks never ran (399 open); 1,180 reads, 2.17·10¹² pairs |
| The board | 4,319 MiB at its peak |
| The claim | the first calculation from the question's numbers in 0 of 128 (five calculations written, three of them right sums, none from the question) |

Of the 82 open answers, 77 had released only their first 1 to 16 sites, in order, while sites
further on were released; of the 46 that ended, 34 ran the whole 1,229-site extent, about 96% of
it zeros. The three text answers ran to their end in 942 sweeps and read as GSM8K's text around
calculations: words, `<<`, `=`, `>>`, `####`, with numbers that do not come from the question.

[agent-inferred] Three causes.

1. **The digits are not yet read from the question.** Beside their neighbours the held answers'
   digits reached the one-byte table (3.464 against 3.459) and fell every lap (by 0.55, 0.24, 0.34
   and 0.22 bits); the text fell below it (2.772). Read from the question alone the answers did not
   fall (5.341 to 5.233). The field has learned the answer's text and its local order, but no digit
   is yet read from where the question holds it, so no number written can come from the question.
   The training had not finished: every withheld read fell at every lap, by 0.19 bits at the last.
2. **The front stalled behind released content.** The release admits every content site and,
   where none resolves, the site of the most news, wherever it is. Content far from the front
   resolved first (a zero beside a zero), each released site made its neighbours resolve, and the
   front, whose read is the spread of a real answer, never resolved and was never the most news.
   The void is released only at the front (§15), so an answer whose front stalled kept its whole
   extent and filled it with the commonest content.
3. **Every sweep read the whole extent.** A region kept its question and all 1,229 answer sites
   until its front reached its void, so each sweep cost the opening's, 509 ms, and the free set
   reached its deadline after 590 sweeps.

**The repairs.**
- **The extent is read once, at the opening** (`Field::release_with`, test
  `the_void_follows_the_released_content`). The void is one nested variable: the void at `t` holds
  exactly when the extent `L ≤ t`, so its face at `t` is `P(L ≤ t)`, monotone in `t`, and the
  earliest site whose void resolves (`2·m_void > total`) is where `P(L ≤ t)` first passes one half,
  the median extent the field reads from the question. At the opening that site's void is
  released and the sites past it leave the region unreleased; it is read once, from the question with every
  answer site open, so no released void is read beside another (§15's creep cannot start). After
  the opening the void is released only at the front, as before. An answer whose void resolves
  nowhere at the opening keeps its extent until its front reaches the void. Every later sweep reads
  the question and the extent only; `ReleaseSweep` counts the problems cut (`cut`) and their extents
  (`cut_sites`).
- **A lap starts only while the time left holds its bound** (`field_train::train`). `LAPS` is a
  count bound; before each lap after the first the trainer continues only if the elapsed time plus
  that lap's projected bound stays within the run's (`FIELD_LAPS_HELD`). The body grows at most once
  a run, because a run carries two projections, before and after one growth (`FIELD_GROW_HELD`),
  and the keys are checked to cover that growth before any lap runs.
- **The sixth reading continues the fifth's learner** (`reading-6/reading6.sh`): from `STATE.4`,
  600 s of training (about ten more laps at the fifth reading's longest lap, 50.3 s with its reads),
  240 s of release, 30 s of text, the same 900 s. The kernels did not change, so the fifth reading's
  parity and projections stand. The release's deadline was not raised: its law changed, and the
  partition of the 900 s moved toward the read that had not finished.

Not adopted yet: a strictly front-first release (it is a pass a site again); release in blocks;
open sites carrying their previous faces into the next sweep (self-conditioning); revising released
sites; the returns in tiles and narrow carriers.

## 17. The sixth reading: the answers took GSM8K's shape, and the question was not read

[measured] The sixth reading (receipts in `…_receipts/reading-6/`, count-only) continued the fifth's
learner from `STATE.4` under §16's repairs: eight more laps, six at width 32, one growth to width 64
and two more, then the release and the written rules on the same 128 held problems.

| Reading | Value |
|---|---|
| The release | completed for the first time: every free answer ended at its own end mark (the free set 44 s, the marked places 158 s, of 240 s); the extent read at the opening cut all 128 regions (37,988 sites past their extents) |
| The released lengths | 98 to 336 bytes, median 268 (the held answers' median 254) |
| The held answers beside their neighbours | 2.885 → 2.264 bits a site; the digits 3.464 → 2.776, below the one-byte table (3.46) |
| The held answers at the opening (the question alone) | 5.16 to 5.70 throughout, never falling |
| The claim | the first calculation from the question's numbers in 15 of 128 (bar 24), of 110 releases that wrote one; right values at 9 of 399 marked equals |
| What was written | sentences, `<<a op b=c>>c` calculations and a closing `#### n`; the numbers in them the commonest (`10` written 171 times of 356, 14 distinct values) |

**The question is not read.** A first calculation counts when its operands occur in the question,
so a field that writes common numbers passes it by coincidence at some rate. f8fe73d39 adds the
claim's foil (`c_foil`: the same releases read against the next problem's question) and a held read
of each answer beside the next problem's question (`foil`, `foil_digits`). On the sixth reading's
release `c_from_question = 15` against `c_foil = 14`. On six rested learners, from the fifth
reading's first to the sixth's last (`foil.sh`, `foil.txt`), the held answers code alike beside
their own question and beside another's: within 0.003 bits a site, and within 0.010 bits a digit
(3.464 against 3.474 on the fifth reading's last learner, 2.776 against 2.784 on the sixth's). The
gap did not grow over eight laps while every other read fell. Everything the field learned is the
answer's own text and local order; nothing of it is read from the question.

[agent-inferred] **Why.** Reading a number from the question is finding, in the question, the site
whose word continues the answer's: the digit after a `1` that stands where the answer's `1` stands.
The field opened each site on its own class alone (`x⁰_t = E(u_t)`), so a site's word, its
neighbours, reached its charts only after a first tick's contact had gathered them. Finding a site
by its word was then a composition of two learned contacts, the first tick's gathering of each
site's neighbour and the second tick's match on what it gathered, which in the language of
attention is the induction circuit two layers form. Thirteen laps did not form it.

**The repair: the opening carries the site's strand contacts** (`Field::open`, the module doc). A
site is a ring of the strand joined by pair contacts to the sites before and after it, and its face
is its word, the address it is read by (the elementary objects: a source word is its address). The
opening is

```text
x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)),   u = ∗ at an unresolved site
```

with no neighbour past a region's ends, and `E₋`, `E₊` founded at zero (the founded field opens as
before; the founding's key draws are unchanged). A key then carries the word before it from the
opening, so a query meets the site whose word continues its own in one contact. Growth repeats `E₋`
and `E₊` as it repeats `E`. The card opens each site with its neighbours only within its region and
returns each encoding's covector over its own partition of the sites by the row they opened on.

[measured] **The probes** (host, debug build, `…_receipts/strand-contacts/`). A field of width 16,
two heads of four modes (two still), 16 contacts and two ticks, founded on the same keys, read
the last site of small regions unresolved, 16 regions a section, its held code the mean over 64
withheld regions; the strand-contact opening against the opening on the site's own class alone:

| Probe | Opening on its own class | Strand contacts |
|---|---|---|
| The last word equals the one before it (12 words of 10; 500 sections, rate `2^(−8)`) | 0.914 bits | 0.077 bits |
| Four key–value pairs, then a key and its value unresolved (keys of 8, values of 8; 2 bits knowing only which values are present, 0 recalled); 2,000 sections | 2.088 bits (rate `2^(−8)`, four still modes) | 0.075 (rate `2^(−8)`), 0.130 (four still modes), 0.000 (rate `2^(−6)`, 0.020 at 1,000 sections) |
| A permutation of ten words, the separator, a cue and its successor (3.17 bits without the copy); 2,000 sections, rates `2^(−6)` and `2^(−9)` | 3.30, 3.31 | 3.31, 3.28 |

On its own class the field learned the neighbour by place, slowly, and never recalled by content:
it stayed at the code of the values present. With the strand contacts the recall formed in one
transition (2.43 → 0.33 → 0.02 bits over sections 400 to 1,000 at `2^(−6)`), and the neighbour is
read at the opening. The permutation probe formed in neither within 2,000 sections; there the cue
must be matched among ten successors at once, a narrower key at width 16. The recall is kept as
the law's test (`the_strand_contacts_let_a_value_be_recalled_by_its_key`: under 0.25 bits after
1,000 sections at `2^(−6)`).

[measured] The rate decides whether a step stands at all. At `2^(−4)` the probes stalled from
their first sections (the permutation at 3.34 bits after 600 sections, both openings), and the
certificate's own test (`certified_deposits_lower_the_code`, two fixed regions) deposited once in
twelve sections: after the first step both the full and the half step raised the code, the
parabola through them had no minimum, and the step was refused; the moments still read a step of
the same size the next section, so every later section was refused alike. At `2^(−5)` to `2^(−8)`
all twelve deposited, and the test now runs at `2^(−6)`. A refused step that does not shrink is a
stall at any rate too large for the field; the GSM8K learner at `2^(−8)` deposited 394 to 413 of
413 sections a lap, so it does not stall there.

[agent-inferred] **The seventh reading founds afresh.** A learner saved before the law has no
contact encodings, and its text is refused by length (an old save is a superseded prototype). The
seventh reading founds the field on the same declaration and keys, trains within the same 900 s
(projected about twelve laps, as many as the fifth and sixth readings together), and changes only
the opening: the rate stays `2^(−8)`, under which the sixth reading deposited 394 to 413 of 413
sections with few halvings; the probe's faster rate is untested at the GSM8K width. Its readings
are the claim against its foil (`c_from_question` against `c_foil`) and the held answers' code beside
their own question against another's (`context` against `foil`) at every lap.

Not adopted: a wider word than one neighbour each side (the second tick composes one more); a
separate copy path or pointer (a catered routine); a schedule that withholds the answer's
neighbours to force the question's read (the release states already hold the opening).

## 18. The seventh reading: the question was still not read, and the four parts the machine lacked

[measured] The seventh reading (receipts in `…_receipts/reading-7/`, count-only) founded the field
under §17's opening on the same declaration, keys and data and trained it eleven laps in 529 s, then
released the 128 held problems and read them by the written rules.

| Reading | Value |
|---|---|
| The training | 11 laps of 413 sections, 400 to 413 deposited a lap, about 130 held steps refused a lap; the withheld problems' code 6.931 → 2.025 bits a site |
| The held answers beside their neighbours | `context` 3.887 → 2.009 bits a byte, its digits 4.058 → 2.612 |
| The same beside the next problem's question | `foil` 3.887 → 2.014, its digits 4.059 → 2.633 |
| The release | completed, the free set in 30 s and the marks in 103 s of 240 s; released lengths 271 to 367 bytes, median 315 (held 254) |
| The claim | the first calculation from the question's numbers in 3 of 128 (bar 24), against `c_foil = 4`; right values at 6 of 399 marked equals |

**The question is still not read.** The strand contacts let the field learn its answers' own text
faster than §17's opening (context 2.009 against the sixth reading's 2.264 after a similar time),
but the question told the held digits 0.021 bits after eleven laps, and the first calculation drew
on the question's numbers no more often than on another problem's. The answers' numbers were the
commonest (`10` 171 times of 357 written).

[agent-inferred] **Four parts the machine lacked**, found by reading the law against what the
copy needs (a GSM8K operand stands a median of 190 bytes before the answer site that writes it):

1. **The contact did not concentrate.** A site finds its counterpart only where their contact
   stands above the region's other sites. The charts `Q` and `K` were founded independently, so a
   word's contact with its equal was a random pairing; the strand encodings `E₋`, `E₊` opened at
   zero, so at the founding no site had a word to be found by; `β` was set to bring the contact's
   spread to one bit, while finding one site among 450 needs about nine; a head mixed its still
   and turned modes, whose phase-scattered sum is as large as the still modes' at any distance
   past their finest rings; and a probe's and a key's power varied with their words, so a louder key
   outscored the equal one. Each site gathered the region's average.
2. **A site met itself.** Its own word is always its best match, so a concentrated contact would
   read itself before any other site.
3. **The founding's draws were not tested at a question's size.** The fixtures' key stream (a
   counter's squares and Weyl steps) drew the founding's rows along one lattice, so in the tests
   every founded word was nearly every other: a word's contact with its equal scored about 70
   against the region's 80 to 90 at 450 sites. The tests therefore could not see the first part.
4. **The release spoke each site once.** A released site was never revised, so a digit released
   before the sites that inform it stood whatever the field read afterward.

**The laws** (`Field::found`, `Field::tick`, `Field::release_with`, the card's kernels):

- *The contact is founded as the pair's likeness*: `K = Q` at the founding, and `E`, `E₋`, `E₊`
  each a keyed draw with its unresolved row at zero (a site whose class has not arrived has no word
  to be met by, only a probe).
- *The still and turned modes are whole ring sets*: head `h` belongs to set `h mod frames`, and a
  set below `still` is still in every mode, so a still head compares words at any distance with
  nothing turned beside them.
- *No site meets itself*: `e_ii = 0`, the peak read over the others; a region needs two sites.
- *The contact pairs words at unit power*: within its head the framed probe and key are each read
  as a ratio to their own power over the head's `2n` reals (the chart's own law), so a word's
  contact with an equal word is `2n`, the most any pair reaches, and a key fits its lock exactly
  where the two words agree. The return reads the ratio's adjoint before the frame is undone.
- *The gain is the reach's*: `β` is the largest shift with `2^(−β)·2n ≥ ⌈log₂ reach⌉`, so two
  equal words outweigh every other site of the longest region (`β = 0` at GSM8K's reach of 2,221
  and `2n = 16`).
- *The release refines*: after each sweep's releases, one part of the released answer sites (every
  fourth from the answer's first; the void, the boundary, excepted) is read again open with the
  rest as it stands, and a site whose face now resolves another class takes it. A problem refines
  while it has an open site; once wholly released it refines in rounds, each of its four parts
  reread once, and ends at the round that revises nothing or no fewer sites than the round before
  (the parts revising each other in a cycle; counted as `unsettled`), so a released answer refines
  at most one round more than its first round's revisions. A sweep reads at most three times (the
  faces, the question-open prior where nothing resolves, the reread).

[agent-inferred] **The review before the probe.** An independent read of the change against the
host and the card found the probe's training command one argument long (it would have stopped
after parity, with no state to release), and a refinement that ended only at a round of no change,
so two parts revising each other back and forth would have spent the release's time on the cycle;
both are repaired above (`the_refinement_ends_where_it_stops_settling`). It found the ring sets,
the self-exclusion, the unit power and its adjoint, the founding's draws, `β` and the release's
boundary equal on the host and the card. A read of no open problem is no longer sent to the card.

[measured] **The founded contact at a question's size** (host, before any learning;
`founded_contact_shares_at_a_question_s_size` and a removed scratch fixture of the same shape: a
region of 450 sites drawn over 122 classes, the seventh reading's declaration, a site's whole word
written once more 340 sites before it, both still heads):

| The founding | Rows peaking at the counterpart | The counterpart against the region |
|---|---|---|
| The fixtures' former key stream, charts at their own scale | 4 of 32; 1 of 16 | a score of about 70 against the region's 80 to 90; a median share of the row's weight under 0.01 |
| A mixed key stream, charts at their own scale | 20 of 32 | a score of 12 to 31 against the next site's 9 to 22 |
| A mixed key stream, probe and key at unit power | 16 of 16 | the score `2n = 16`, the most any pair reaches; a share of 0.53 to 0.86 of the row's weight |

At its own scale a probe's power varies with its word (a sum of `2n` squares), so a louder key
outscored the equal one; at unit power the equal word is the maximum by Cauchy–Schwarz. The founding
meets a whole word; what it meets by part of one is what learning has to concentrate: an open site
whose two neighbours recur around one site peaks there in 10 of 16 rows (shares up to 0.66), one
whose left neighbour alone recurs in 3 of 16. The law's test is
`the_founded_contact_meets_the_site_whose_word_is_its_own` (every row of 16 regions of 48 sites).

[measured] **The cue's successor** (host, debug build, `…_receipts/unit-contact/`). §17's
permutation probe (ten words, the separator, a cue and the word that followed it; 3.17 bits
without the copy) had not formed within 2,000 sections under either opening. Under §18's laws, on
the same declaration (width 16, two heads of four modes, 16 contacts, two ticks, 16 regions a
section, the held code the mean over 64 withheld problems):

| Sections | §17 (rates `2^(−6)`, `2^(−9)`) | Rate `2^(−6)`, two still sets | `2^(−6)`, one | `2^(−8)`, one |
|---|---|---|---|---|
| 0 | | 3.459 | 3.459 | 3.459 |
| 200 | | 0.204 | 1.019 | 0.784 |
| 400 | | 0.017 | 0.061 | 0.122 |
| 600 | | 0.006 | 0.021 | 0.046 |
| 1,000 | | 0.001 | 0.005 | 0.013 |
| 2,000 | 3.31, 3.28 | 0.000 | 0.000 | 0.001 |

At `2^(−8)` 1,996 of 2,000 sections deposited; at `2^(−6)` with two still sets 592 of the first 600
and 1,992 of 2,000. The copy is learned exactly, at the slow rate the GSM8K learner uses too. The law's test is
`the_contact_finds_a_cue_s_successor` (under 0.0625 bits after 600 sections at `2^(−6)`, two still
sets); the recall test (`the_strand_contacts_let_a_value_be_recalled_by_its_key`) holds under the
new laws.

[measured] **The crib terrain** (`crib-terrain SEED TRAIN DEV OUT_TRAIN OUT_DEV`, an exterior
generator: no model reads). The probes above copy across a dozen sites; a GSM8K operand stands a
median of 190 bytes before the answer that writes it. The crib terrain puts the copy at that
distance and makes it the only thing to learn: a question of 48 to 79 words, each one to three
syllables of twenty (meaningless, so no word predicts a number), with two or three numbers of one to
three digits at drawn places, then `?`; the answer sums them in the question's order in GSM8K's
markup (`<<a+b=c>>c`, a line a sum, then `#### total`). The answer's operands are read from the
question and from nowhere else. At seed 20261101 over 2,000 problems the questions are 211 to 427
bytes (median 312), and the first calculation's operands stand 55, 182 and 300 bytes before the
answer site that writes them (the tenth, fiftieth and ninetieth percentiles), 69.5% of them past 127.

[agent-inferred] **The crib probe** (`…_receipts/crib-probe/probe.sh`) runs on the card under
reading 7's declaration, key file, section and rate, with only the terrain changed: the key file's
bytes (a degenerate stream would found every word alike); the card against the host on the
terrain's sections, without and with one growth (a stop at the first unequal read ends the probe);
the lap's projection; 300 s of training from the founding; the release of 128 held problems in
150 s, and three releases' text in 30 s; then the written rules against the terrain's own passages.
It holds 900 s at most, every bound fixed in the script before launch. Its acceptance, fixed
here: **the question is read** when the first calculation takes its operands from the question's
numbers in at least 24 of 128 held releases (the claim's bar) and more often than from the next
problem's question (`c_from_question` against `c_foil`), with the held answers' code lower beside
their own question than beside another's. If it fails, its failure is the next loop's subject and
reading 8 waits; if it passes, reading 8 runs GSM8K on the same laws.

[agent-inferred] **The Lean obligation** carried into #410: the unit-power contact's lock, that
two words each at unit power over `2n` reals pair at most `2n`, with equality exactly when they are
equal (Cauchy–Schwarz on the head's chart), and that with `β` as derived a word's counterpart
outweighs a region's other sites together wherever their words stand orthogonal or opposed to it
(its share is the gaps', `(1 + Σ_(j≠*) 2^(−(z_* − z_j)))^(−1)`; amended after the sixth review, §19).

Not adopted: a wider span or more still modes to raise the contact's signal (the width is the
trained body's); a separate copy path or pointer to the question (a catered routine); a learned
temperature beside `β` (the gain is the reach's, derived); revising the void (the boundary follows
the content, §16); a crib terrain whose answers write anything but GSM8K's markup (the probe reads
the copy the claim needs, not another task).

## 19. The crib probe failed, then passed: the field learns no copy the founding did not weigh, and the closure compares the contact with where the answer's class stands

[measured] **The crib probe under §18** (`…_receipts/crib-probe/`, on the card, every step inside
its bound). The card equals the host on nine sections without and with one growth. The probe trained
14 laps of 248 sections in 149 s, released the 128 held problems in 4.6 s, and read them by the
written rules.

| Reading | Value |
|---|---|
| The training | withheld code 5.459 → 1.742 bits a site |
| The held answers beside their own question | `context` 1.738 bits a site; digits 3.305, text 0.075 |
| The same beside the next problem's question | `foil` 1.744; digits 3.309, text 0.083 |
| The claim | the first calculation from the question's numbers in 4 of 103 (bar 24), `c_foil = 0` |

The answers' markup was learned to 0.075 bits a site; their digits were told 0.004 bits more by
their own question than by another's. The acceptance fails at its first count.

[measured] **What the field learns to copy** (host law runs, release build, one thread each; the
debugging builds are not kept). The declaration is width 32, four heads of eight modes, still 2 of 4
ring sets, 32 contacts and two ticks, at 96 sites a region and rate `2^(−8)`. A section is 16
regions; the held code is the mean over 64 withheld problems; the filler is words of a fixed
vocabulary, as the crib's syllables are.

| The copy | What tells the source | Held code (bits a problem), first read → last |
|---|---|---|
| The far successor (one answer digit open; its predecessor resolved) | the resolved digit's equal word stands in the text | 3.480 → 0.051 at 375 sections; 3.485 → 0.154 at 300 sections and 192 sites |
| The same, founded hotter (`β = 2`) | the same | 3.480 → 3.316 at 375 |
| The same, trained under the τ-mask alone | the same | 4.185 → 3.552 at 500 |
| The marked number (both digits open) | a marker word before the number, the same word before the answer | 6.810 → 3.068 at 400 |
| The first of two numbers (both digits open) | only its order | 6.821 → 6.378 at 400 |
| The same, with a learned metric founded at `2^(−1)`, `2^(−2)` | only its order | 6.095, 6.425 at 400 |

[derived] **The cause.** The face's covector reaches the contact of a pair `(i, j)` only through its
weight `e_ij`: `δz_ij = ln 2 · e_ij (δp_ij − μ_i)/mass_i`. A copy is learned where the founding
already makes the source stand above the region:
- a recurring whole word (the far successor), learned exactly;
- a marker shared by the source's neighbour and the answer's, learned about half.

A number told by its order shares no word with the answer site, so its contact opens at the
region's average weight. The covector it receives is no larger than any other site's, and nothing
separates it from the other number's. A crib operand is told by its order (the question's first
number is the first operand), so no operand was copied. Reach is not the blocker (192 sites learn);
the τ-mask only dilutes; a hotter founding or a learned gain spreads the contact further.

[definition; agent-inferred] **The closure** (`Field::reverse`, `FieldDeclaration::closes`, the
card's `field_contact_rows`). On a head of a still ring set, at every tick, an unresolved site `i`
whose class `u_i` is held by resolved sites `j ≠ i` also reads its row as a **copy face**: the code of
its class on the sites that hold it, `−log₂ Σ_(j holds) p_ij` with `p_ij = e_ij/mass_i`. Its
covector in the contact,

`δz_ij += p_ij − [j holds] e_ij / Σ_(k holds) e_ik`,

is added on `2^(−40)` before the release by `β`. The base-2 Gibbs face's `ln 2` cancels against the
bit, so the term is exactly `p − t` with `t` the row's own weight renormalized over the holders. It
is zero on a row whose weight already lies on holders. With a single holder it is `p_ij − [j holds]`.

This is the declared comparison of the learning law, read on the contact's own distribution: the
Bombe's pairwise loop closure, a site's key located from where the class it must receive already
stands. It is not a copy path. No value is routed, written or selected by it, and the face still
reads its class through the contact the field forms. At a release no unresolved class is known, so
the closure compares nothing there; only the probe's and the key's charts have moved. The field reads
raw bytes (`founded-units-v1 0`), every class is compared alike (letters, spaces, markup, voids and
digits), and nothing in it knows a number. The certificate reads the face's code alone, so a step
stands only where it lowers the code the field is judged by.

It closes on the still ring sets only. A still head reads words at any distance, so a holder is
reached wherever it stands; a turned head's phase locates by relative place, and the source's place
changes from problem to problem. The crib's acceptance counts a first calculation whose operands are
among the question's numbers in any order (`written_rules.py`, `free_reads`).

[measured] **The first form failed: every holder asked for alike.** The first closure asked the row
for every holder equally, `p_ij − [j holds]/H_i`. On the number told by order (unique holders) it is
the copy face's law bit for bit, and it learned. In the crib's training, almost every masked site has
many holders (every space, letter, void or repeated digit), so it pulled every row toward all equal
bytes at once. Its probe (`…_receipts/crib-probe-closure/`) trained 11 laps; halvings rose from about
35 a lap to 187 in the first lap. At lap 10 the answers' text coded 0.316 bits, against 0.114 before
the closure, and the question told the digits 0.007 bits. The claim was 1 of 60 first calculations
from the question, `c_foil = 1`.

[measured] **The closure's laws on the host** (`…_receipts/closure-law/`;
`the_closure_locates_a_number_told_by_order`, `the_closure_locates_a_number_among_repeated_digits`).
The declaration is alphabet 15, width 16, four heads of four modes, still 2 of 4, 16 contacts, two
ticks, 16 regions a section, rate `2^(−6)` unless named. The comparisons of the three laws used a
temporary switch, which is not committed; the committed law reproduces the copy face's numbers
exactly.

| The copy (24 sites unless named) | No closure | Every holder alike | Copy face |
|---|---|---|---|
| Order-told, unique holders, 300 sections | 6.60 | 0.40 | 0.40 (bit for bit) |
| The same at 96 sites | 6.62 | 1.254 | 1.254 |
| Three numbers, digits repeated, 300 sections | 5.76 | 0.96 | 0.35 |
| The same, 4 of 16 text sites masked, 1,200 sections | 6.05 | 5.97 (frozen to about section 600) | 2.71 |
| The same, the crib's mask mix, 1,200 sections | 5.57 | 0.70 | 0.54 |
| The same at the crib's rate `2^(−8)`, 2,400 sections | 6.23 | 0.90 | 0.54 |

With 8 of 16 text sites masked nothing learned in 1,200 sections under any law: the copy's sources
are masked as often as its target.

[measured] **The crib probe under the copy face** (`…_receipts/crib-probe-weighted/`, 16:09 to
16:18 UTC, 530 s against a projected 695 s, 0.76). The card equals the host on nine sections
without and with one growth. The training ran 600 s, set from what the law runs needed: the first
closure probe trained only 2,728 sections (11 laps from `P_A`, which projected 1.8 times the measured
lap), and the copy forms after about 2,000 sections even at 24 sites at rate `2^(−8)`. Here it ran 36
laps of 248 sections (about 11.5 s a lap); the field grew at lap 35 to width 64, eight heads, 64
contacts and rate `2^(−9)`; a second growth was held at lap 36 (no projection), ending training.
The release of the 128 held problems took 6.9 s, none left open.

| Lap | `context` digits | `foil` digits | `context` text | `foil` text |
|---|---|---|---|---|
| 9 | 3.447 | 3.468 | 0.336 | 0.338 |
| 20 | 2.876 | 3.052 | 0.205 | 0.208 |
| 30 | 2.006 | 2.534 | 0.149 | 0.153 |
| 34 | 1.687 | 2.351 | 0.108 | 0.111 |
| 36 | 1.735 | 2.325 | 0.102 | 0.107 |

| The claim | Value |
|---|---|
| The first calculation from the question's numbers | 25 of 126 (bar 24), `c_foil = 2` |
| The held answers' code beside their own question against another's | 0.943 against 1.249 bits a site |
| Not this acceptance | 0 of 189 free calculations right; 1 of 200 marked equals |

**The acceptance fixed in §18 passes**: the question is read. The sums are not: the operands are
copied (whole numbers or their fragments), and the arithmetic between them is not yet learned. The
three releases' text, beside their questions' numbers:

| Question's numbers | Released answer |
|---|---|
| 171, 367, 304 | `<<3+7+32=100>>10` / `<<10+104=100>>100` / `#### 100` |
| 379, 665 | `<<665+5=105>>105` / `<<665+39=15>>>15` / `#### 105` |
| 55, 1, 29 | `<<1+295=55>>>555` / `#### 555` |

Reading 8 runs GSM8K on these laws.

[agent-inferred] **The Lean obligation** carried into #410: the closure's covector is the logit
gradient, in bits, of `−log₂ Σ_(j holds) p_ij` under the base-2 Gibbs face, and it vanishes on any
row whose weight lies on holders.

Not adopted:
- every holder asked for alike (measured above: it fails under plural holders);
- the closure on turned heads (their phase locates by relative place, which changes from problem to
  problem);
- a hotter founding or a learned temperature (measured above: both spread the contact);
- a copy path that writes a holder's value into the answer (a catered routine; the closure only
  compares);
- a weight on the closure beside the face's (each is a code in bits, and their sum is the
  comparison).

[agent-inferred] **The sixth review's points, weighed before reading 8** (an independent review of
the field at the first closure's uncommitted form, November 1). Adopted:
- *The closure's covector was not checked against its own code.* The reverse's law test compared
  the face's covector alone. `the_closure_s_covector_matches_its_code_s_difference` now compares the
  closure's part of the reverse with the central difference of `−log₂ Σ_(j holds) p_ij` summed over
  ticks and still heads, on the founded and the grown field.
- *Growth changed the closure's count.* Growth by copies keeps every face, but each copied still head
  closed again, so a grown field compared each set's code `factor` times against one face code. The
  closure is now read over its ring set's heads (`FieldDeclaration::copies`, `H/frames`): at the
  founding (`H = frames`) its bits are unchanged, and the grown field's comparison is the old one
  (the test fails by exactly the factor without it).
- *`β` bounds the peak, not the gaps.* §18's "two equal words outweigh every other site" holds where
  the other words stand orthogonal or opposed (`z_j ≤ 0`); in general the counterpart's share is
  `(1 + Σ_(j≠*) 2^(−(z_* − z_j)))^(−1)`, shared among near-equal words. The doc and §18's Lean
  obligation read in that form.
- *The void's cut is the median only where the void faces rise with `t`*; each is read alone, so the
  cut is the earliest majority (doc).

Already the law: the review's fibre comparison `−log₂ P_H` is the copy face above (its form was the
uniform one that failed). Kept, with the reason: the certificate reads the face's code alone (a step
stands where it lowers the code the release is judged by; the crib passed under it); the training
regions resolve their sites at their own classes, not at the field's released ones (a change of the
training law, the next subject if reading 8 shows the operands read and the composition not);
the card's per-read uploads and allocations (a realization cost no measurement yet shows dominant);
a continuing interior response, a joint-consistency reading and sparse execution (constructions
with no measured failure pointing at them yet).

## 20. The eighth reading: the question tells the answer's words, and the release commits the commonest byte first

[measured] **The eighth reading** (`…_receipts/reading-8/`, count-only; 16:45 to 16:57 UTC, 709 s of
a 900 s bound). GSM8K on §19's laws, reading 7's declaration, data and keys. The card equals the host
on one section and the withheld read, without growth (52.2 s, projected 55, with one release) and
with one (75.7 s, projected 85; each still set holding two copies). The training ran 8 laps of 51.0
to 53.9 s in 429 s (a ninth was held: 99 s left against `P_A` 121 s); 342 to 396 of 413 sections
deposited a lap, with 95 to 208 halvings (reading 7: 400 to 413, 2 to 121).

| Lap | `context` digits | `foil` digits | `context` text | `foil` text |
|---|---|---|---|---|
| 0 | 4.279 | 4.280 | 3.883 | 3.887 |
| 3 | 3.130 | 3.143 | 2.681 | 2.729 |
| 5 | 2.933 | 2.957 | 2.368 | 2.471 |
| 7 | 2.845 | 2.873 | 2.160 | 2.303 |

The question tells the held answers' text 0.143 bits a byte after 8 laps (reading 7: 0.002 after 11)
and their digits 0.028 (0.021).

| The claim | Value |
|---|---|
| The first calculation from the question's numbers | 0 of 128 (bar 24), `c_foil = 0`; one first calculation written |
| The free release | stopped at its 138 s deadline after 268 sweeps, 127 of 128 open; the marks never read |

[measured] **Why the release did not end.** The void's cut at the first sweep left about 516 answer
sites a problem (91,220 cut of 128 × 1,229). After it the field resolved few sites: 7,176 releases
by majority against 25,310 by news, about one site a problem a sweep, at about 520 ms a sweep (2.9
reads of the batch). The free set needed about 500 sweeps; `time-field` projected 73 s from 16. The
three texts released in full (700 sweeps, 9 s) are runs of the commonest bytes (`the`, `2`) with
fragments of markup.

[definition; agent-inferred] **The lens, Brandon, November 1: the hierarchy is not most-certain
first.** A release that commits where the field is surest and builds on it answers by the most
familiar pattern (shown `√4 = 2`, a child following it answers `√−4` wrongly). The problem is a
Rubik's object: a move at one place contorts every coupled place, through contacts that boost and
turn. The order in which the field decomposes an answer is a gradient it surfs, not a fixed order
of commitments. Progress in it is not a falling code. **Frustration** is the state where local
faces cannot all hold at once, and nothing measures improvement there. The answer "clicks" when the
faces align, as a key fits its lock (`{lock, key} = {problem, solution}`). It is not when one site
grows certain.

Read on this owner: the release commits a class where its face holds a majority and otherwise the
one site with the most news, and every committed class is fixed ground for every later read, refined
a part at a time. That is a commitment order by certainty, and the eighth reading shows its failure
in content (the commonest byte committed first) and in time (one site a sweep). The training's
release-state regions resolve the same order at the true classes. The next law follows from the lens:
- every answer site keeps its face as its state, not a committed class;
- all of them are reread together each sweep beside each other's faces, so a change anywhere moves
  every coupled site in the same tick;
- the boundary is released only where the joint field closes (each face, read through the others,
  returns itself);
- frustration, the part that does not close, is reported and kept open rather than forced;
- training meets the same states.
