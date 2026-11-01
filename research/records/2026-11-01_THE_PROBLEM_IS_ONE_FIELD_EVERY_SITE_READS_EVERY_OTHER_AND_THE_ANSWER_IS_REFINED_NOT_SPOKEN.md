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
