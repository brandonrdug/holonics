# The field disperses: a site meets its resonance class at its falloff, and the answer locks under the pump

November 1. Design, agent-inferred, written before any of it is built (Refs #404 #406 #407). It
replaces three laws of the field
([record](2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN.md),
owner `hnn::tower::field`): the contact where every site weighs every other, the release that
commits the surest site first, and the training regions ranked in that order. It also supersedes
the "joint state" sketched at the end of that record's §20, which kept the first law: every site
reread beside every other in one tick is a global pass, the transformer's pattern, and not a
medium. What stays: the codec, the strand encodings, the charts, the pair contacts, the closure of
§19, the deposition and its certification, the extent read at the opening, the acceptance bars.

The measurements cited are reading 8's
([receipts](2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN_receipts/reading-8/)).
The declaration there: 122 classes, width 32, 4 heads of 8 modes (2 still), 32 pair contacts, 2
ticks, reach 2,221.

## 1. What reading 8 convicts

[measured] None of the 128 held answers took the question's numbers into its first calculation
(bar 24, foil 0); the free release stopped at its 138 s deadline with 127 of 128 answers open after
264 sweeps: 7,717 sites released by majority, 28,003 by news, 849 revised. The three texts
released in full are runs of the commonest bytes. What improved: beside its own question an
answer's text codes 0.14 bits a byte below its code beside another's (reading 7: 0.002), its digits
0.03.

Three laws produce this.
- **The contact is a global pass.** Every site weighs every other site at every tick, normalized
  over the whole region, so a change at one site reaches every site in one tick at full strength,
  wherever it stands. It costs the square of the region: 31.0 × 10⁹ pairs a lap, most of each
  48.8 s lap.
- **The release commits by certainty.** It commits the site the field is surest of, and where none
  holds a majority, the site with the most news, usually the commonest byte. Each committed class is
  fixed ground for every later read. It refines a quarter at a time, and stops when the parts revise
  each other in a cycle, which is where frustration is, so it gives up exactly where the work is.
- **Training meets only that order.** The release-state regions (`Shape::Released`) resolve the
  answer's sites in the release's news order at their true classes; any other release meets states
  the field never trained on.

## 2. The field is a medium

[definition; agent-inferred] The field becomes one medium in the sense of
[THE_MEDIUM](../../docs/THE_MEDIUM.md) on the region's complex. The complex holds the sites
(0-cells), the strand's contacts between neighbours, and the contacts a site's resonance class
gives it (1-cells). A merge joins two currents from distinct sources at one site (2-cells, §3). Its
faces:
- **register**: each site's face and its heads' modes (unchanged);
- **contact and friction**: the falloff of §2.3;
- **polarity**: the turned rings, and the release's pump (§4);
- **free energy**: the code, read as the two-part code (§2.3).

Activity starts at sites and spreads through contacts, fainter with distance. No row is normalized
over sites it does not meet.

### 2.1 One word for the lock and the key

[definition; agent-inferred] Each head reads one word per site, `w_t = W_h r̂_t + b_h`, which is
both the probe and the key: `q = k`. The founding already set `K = Q`. A key fits its lock exactly
where the two words agree, and with one word the contact is reciprocal, `z_ij = z_ji`: for a still
head `Re(conj(w_i) w_j)`, for a turned head `Re(conj(w_i) U_i* U_j w_j)`, the real part of a
Hermitian form either way. That is the medium's own law: the contact that admits a force is the
friction that dissipates it, and a passive contact is symmetric. Direction comes from the value
`v_t`, which stays its own chart, and from each receiver's own normalization.

### 2.2 The resonance class: the word's half-turn sheets (superseded by §12's shells)

[definition; agent-inferred] A head's unframed word locks into `b` half-turn sheets: the signs of
the in-phase (real) parts of its first `b` modes, a zero counted on the positive sheet. The sheets
give the site's class `B_h(t) ∈ [0, 2^b)`. Two sites meet through head `h` only if they share its
class or stand in each other's near field (§2.4). Equal words share every class. Each head has its
own sheets, so two words split by one head's sheet can still meet through another's. This is the
parametron's lock (the half-turn sheets are an Ising lock, `holon::parametron`) used as an address:
sites that ring at the same lock resonate, and the rest do not hear each other through that head.

`b = min(n, ⌈½ log₂ reach⌉)`. Then there are about `√reach` classes, each holding about `√reach`
sites of a region at the reach, so the number of classes and their size are balanced. At reading
8's declaration (`n = 8`, reach 2,221) this gives `b = 6`, 64 classes.

### 2.3 The falloff is the octave friction, and it is the contact's address

[definition; agent-inferred] A source `d = |i − j|` sites away reaches `i` with share proportional
to `1/d`. This is the octave ladder of matched frictions (`wave.matched-friction-reach`: rung `s`
carries a push `2^s − 1` ticks best, and the ladder carries every distance with harmonic falloff).
Read in bits, it is the octave rung of the distance, `f(d) = ⌊log₂ d⌋`.

Read as the two-part code, the same term is the cost of the contact's address: naming one site
among the `2^⌊log₂ d⌋` at its octave costs that many bits. So the falloff and the founding cost are
one law. A far site is met only where its resonance pays for its address. Each octave's crowd, about
`2^ℓ` sites at `2^(−ℓ)` each, is heard at about the same total loudness as the nearest site. A
single resonant source stands out of its crowd only by its resonance.

### 2.4 The near field

[definition; agent-inferred] Sites closer than the solenoid's finest joint closure,
`0 < |i − j| < lcm(2, 3) = 6`, meet through every head whatever their classes, at their falloff.
Up close a source is heard at every frequency. Over six sites the finest dyadic and triadic rings
resolve place without winding. Measured support: four bytes before a site code it at 1.98 bits
(field record §13), so a byte's own spelling context lies inside this field.

### 2.5 The contact

```text
support    S_i^h = { j : 0 < |i − j| < 6 } ∪ { j ≠ i : B_h(j) = B_h(i) }
contact    z_ij = 2^(−β) Re(conj(w̃_i) w̃_j) − ⌊log₂ |i − j|⌋              j ∈ S_i^h, framed as before
weights    e_ij = 2^(z_ij − max_(j∈S_i) z_ij),   zero outside S_i^h
current    y_i = conj(U_i) ⊙ Σ_(j∈S_i) e_ij ṽ_j / Σ_(j∈S_i) e_ij
```

The gain covers the falloff. `β` is the largest shift, negative where it must amplify, with
`2^(−β)·2n ≥ 2⌈log₂ reach⌉`. An equal word at the farthest reach pays `⌊log₂ reach⌋` bits of
falloff, and it must then still outweigh the rest of its support together, which needs at most
another `⌈log₂ reach⌉` bits. At reading 8's declaration (`2n = 16`, reach 2,221) the gain is
`2^1`: an equal word pairs at 32 bits, and its falloff at the reach is 11.

The closure of §19 is unchanged in law. It is read over `S_i`, so a holder a site does not meet is
not compared.

### 2.6 What reaches a site, and when

In one tick a site meets its near field and its resonance classes, each at its falloff. A change
anywhere else reaches it only through the sites it meets. Across the `K` ticks, and across the
release's sweeps, a change spreads hop by hop, fainter at each hop: it disperses.

The cost per tick is about `N(10 + N/2^b)` pairs a head against `N²`. At a GSM8K region of 450
sites with `b = 6`, that is about 17 contacts a site against 450. The card's time then goes to width
the body can grow into (`growth.rs`), not to every site reading every other.

## 3. The families: singular objects that carry entropy

[definition; agent-inferred] The contacts fall into families by what they do to the information
crossing them. Each family is one law shared by every site of every problem, which is what lets it
transfer to a problem it has not met:
- **copy** (fan-out, lossless): a still head's class contact carries a source's value to every
  resonant receiver unchanged. Reading 8 shows it beginning: the question tells the answer's text
  0.14 bits a byte.
- **place and carry** (the helix): a turned head reads a source with its relative place, as
  residues and whole windings on the solenoid's rings. A carry is a winding handed to the next
  coarser ring.
- **merge** (fan-in, lossy): pair contact `c` is a rank-one bilinear law, `W_c(a_c ⊙ b_c)`. Its
  operands are reads of the currents a site gathered, which arrive from different sources through
  different heads. It keeps their sum or product and discards the fibre, the operand pairs with the
  same result. Addition is a merge on a ring with carry. Reading 8 shows it absent: digits 0.03 bits.
- **scale**: a gain on one contact, which is a merge with a constant.

A **singular point** is a site where a merge joins currents from distinct sources. It is a 2-cell
of the complex: three sites, two in and one out. In the Hodge network's terms, a loop of contacts
with no such face carries a circulation that never drains, and the face that fills it drains it.
That is the frustration and the click of §4.

The families are founded and pruned by the code (`hnn.sparse-binding`) and learned by deposition.
None is authored: no calculator, no digit table, no routine copies a number.

**Receipt: the landmarks.** For each held problem, the sites of the answer's first calculation and,
for each, the question sites carrying the most weight in its still heads' currents. These are the
places where the answer's contacts converge. A reading only; nothing drives the step from it.

## 4. The release: the answer locks jointly under the pump

[definition; agent-inferred] **The state.** Every open answer site carries a soft face: logits
`ℓ_t` with a momentum `m_t`. It opens on the mixture of its tempered face,
`Σ_a p_t(a) E(a)`, and its strand rows open on the same mixtures (`E₋`, `E₊`). The question's
sites open on their classes. The answer's extent is read once at the opening, as now (one nested
variable, read once; field record §15).

**A sweep.** Every site's face is read with every open site on its mixture, all at once. Then each
open site moves:

```text
momentum   m_t ← μ m_t + (z_t − ℓ_t)
face       ℓ_t ← ℓ_t + m_t
tempered   p_t(a) = 2^(β ℓ_t(a)) / Σ_b 2^(β ℓ_t(b))
```

`μ = ½`. That is the matched friction for a push carried across one sweep (`ρ² = L/(L + 1)` at
`L = 1`): the step a site took last sweep carries into this one, so the state rides through flat
stretches instead of stalling in them.

With `z` held, the error `e = ℓ − z` and the momentum step as `[[0, μ], [−1, μ]]`, whose
eigenvalues have `|λ|² = μ = ½`: a damped oscillation, a graph wave with friction, not a greedy
step.

**The pump.** `β` starts at 1, the face as trained. It doubles, one octave of the pump, after a
sweep whose total change `Σ_t |Δp_t|` fell below the sweep before it: the activity tempered. When
the change did not fall, the coupled sites cannot all hold at once, and that is frustration. Then
`β` holds and the state rides on its momentum. No site is fixed, and no order is imposed. One
frustrated corner holds the pump only while it keeps the whole problem's change from falling.

**Lock and click.** A site is locked when its top class holds a majority at `β`
(`2 m_top > Σ m`, the field's resolution test) and held it through the sweep. Sites that lock at
the same rung lock together; that is a click.

**The end.** The release ends when every open site is locked, or when its sweeps or its time run
out. The answer is released whole: locked sites at their classes, and sites still unlocked shown as
open, never forced into a class.

**Receipt: the circulation.** Per problem:
- the sweeps ridden at each rung;
- the sites whose class left and returned at one rung (a cycle: the configuration circulates around
  a loop of contacts that no assignment satisfies);
- the sites open at the end.

This replaces a falling code as the reading of how a release went.

**Why no certainty order.** The site the field is surest of first may be the one whose class
depends most on a site not yet read: shown `√4 = 2`, the analogy answers `√−4` wrongly. Here every
site stays soft until the pump locks them together. A change at one site, the sign, moves every
site it contacts in the same sweep at its falloff. The answer either settles as one or keeps
circulating, visibly.

## 5. Training meets the release's own states

[definition; agent-inferred] `Shape::Released`, the surest-first state, is replaced by the
release's second sweep. Read 1 opens every answer site on `∗`, as the release opens. Read 2 opens
every answer site on the mixture of its read-1 face at `β = 1`, held as data with no covector
through it. The code is read over the answer's sites at read 2. The covector of read 2 reaches the
encodings through the mixture (`E(a)` weighted by `p(a)`). The other regions keep the completion
masks (any subset open, the truth elsewhere).

Why the second sweep: it is the first state a release meets after its opening, and the farthest from
the masks. Later sweeps sharpen the mixtures toward the classes the masks show, so they lie between
the two states training reads.

## 6. Exact arithmetic and the card

- The class is read from the signs of integer faces (zero on the positive sheet). One stable counting
  sort per head, region and tick lists each class's members, and the host and the card read the same
  lists.
- The falloff is an integer number of bits taken from the score on its grain.
- The weights stay on `2^(−40)` over `S_i`.
- The momentum is on `2^(−16)`. `μ = ½` is an exact halving, released to the nearest numerator.
- `β` doubles by an exact shift.
- A mixture opening's products are released at the material grain.

Every sum is an integer sum, so the host and the card agree bit for bit (the parity checks of
reading 8, unchanged).

## 7. Acceptance (the bars are unchanged)

- **The crib**: at least 24 of 126 first calculations from the question, above its foil.
- **GSM8K reading 9**: at least 24 of 128 first calculations from the question's numbers, above its
  foil; every problem ends locked or reported open within the release's time.
- **Beside it**: per problem, the lock rungs, the circulation and the open sites; the landmarks of
  the first calculation; the pairs a lap beside reading 8's 31.0 × 10⁹.

## 8. The recorded failures this design could repeat

- **An authored routine standing in for learning.** The classes are the words' own locks, and the
  words are learned. The falloff is the medium's law. The families are learned contacts. The pump's
  schedule is read from the field's own settling. No routine computes a task's answer.
- **A design thought in arrays and windows.** The near field is the solenoid's finest closure; it is
  not the only reach and not a context window standing in for learning. The resonance class is
  spectral placement by lock.
- **Text treated as the exception.** Distance is the complex's. On an image, a sound or a motor
  strand, the same falloff reads graph distance, and the classes are the same sheets.
- **A located cause carried into a new consumer.** The certainty order is removed from both the
  release and training, not moved. The void's creep stays repaired: the extent is still read once.
- **An uncertified deposition step.** Deposition is unchanged.
- **Seen material graded as unseen.** The held problems are never trained on; the crib's texts are
  synthetic.
- **Bits read as progress.** The receipts are counts, locks and circulation; the bars are counts.
- **A refusal answered with a larger limit.** A release out of sweeps reports its open sites; it is
  never relaunched with more.

## 9. Owners

- `hnn::tower::field`: the one word, the classes, the support, the falloff, the gain, the soft
  opening and the release.
- `holonics-cuda` `field.cu`: the class lists, the support and the mixture opening.
- `field_train.rs`: the second-sweep regions, the receipts.

The atlas rows of the field's contact, release and training regions change with the build, in the
same commit.

Of the winding guide's six objects this touches:
- the **helix** (the turned rings, the carry);
- the **pair** (reciprocal contacts, merges);
- **faces and placement** (the sheets as addresses, the Gibbs face, the lock);
- the **tube** (the ticks and sweeps).

Attached: the **cell holonomy** (the circulation receipt) and the **tower thread** (the octave
falloff).

Owed to #410:
- the octave balance (`2^ℓ` sites at `2^(−ℓ)` each per octave);
- the reciprocity of the one-word contact;
- the matched momentum at one sweep.

No theorem is claimed for the pump's settling.

## 10. Built

[definition; agent-inferred, November 1] The build, before any run (Brandon's rule: no run of an
incomplete machine), with one review of the whole diff whose findings it repaired. What each law
became, where the design left a choice:

- **One word** (`q = k`): the key chart and its bias leave the material (`hnn-field-v4`, a learner
  `hnn-field-learner-v4`; older saves are superseded prototypes). The word returns both roles,
  `δŵ_i = Σ_(j∈S_i) δs_ij ŵ_j + Σ_(j∈S_i) δs_ji ŵ_j`, each sum released on its own.
- **Classes and support** (`ClassLists`, `NEAR`): the support is the near field and the class past
  it, each site once, never itself, symmetric; the card lists the classes by a stable counting sort
  (`field_classes`, a lane's rank among the earlier lanes of its class) and visits only the support.
  The weights and the contact's return keep the region block's dense address `[i][j]` on the card,
  written and read only on the support, so a column's return finds `e_ij` without an index; the time
  follows the pairs met, the reservation stays the most a region's classes can ask.
- **Far contacts are bipartite** (`ClassLists`): past the near field two class-mates meet only where
  at least one of them is known (resolved, carrying no mixture). The first review found that every
  unresolved site whose neighbours are unresolved opens on one face and so one word; with one word for
  lock and key they met each other at the most any pair reaches, the release's opening a clique of its
  whole extent (about `A²` pairs a head a tick) gathering the unresolved row above the question.
  Stripping every unresolved site of its class left the cue's successor at 2.23 bits and the key's
  recall at 1.52 (an open site's word is its crib address); stripping only the sites that open on
  nothing broke the clique but, the second review found, left the opening's interior hearing only its
  near field: the contact is translation-invariant, so every interior site had one state, the extent
  was read at the region's two ends, and the first sweep's equal mixtures rebuilt the clique. Met only
  by known class-mates, an unknown site still reads the question at its falloff, and unknown sites meet
  each other through the near field and hop by hop. The lists keep each class's known members first,
  so an unknown site's far support is one run.
- **The gain** is signed (`score_shift` → `i32`); a negative `β` doubles the contact's covector
  exactly.
- **The mixture opening** applies at any carried site, resolved or not; a carried site holds no class
  for the closure. Its return is `release(w_a δx, 16)` to each class row, the shares data. An empty
  carried face is refused on both realizations.
- **The release reads logits** (`FieldRealization::read_logits`): the card returns each open site's
  readout `z_t`, and the host moves the state. A content site opens at rest on its opening face
  (`ℓ = z⁰`, `m = 0`), so the pump is the only temperature (the review: stepping from `ℓ = 0` gave
  the first mixtures a hidden sharpness of about `1.5×`). Inside the extent the void is no class
  (`Field::content_face`): the extent is one nested variable read once, and a content site free to
  lock at the void cut every locked site after it (the old creep, through the neighbours' `E(void)`
  mixtures). The change `Σ|Δp|` is read at the sweep's own `β` on both sides, and compared only within
  one rung (after a doubling the comparison starts again). A site is locked where its top class held
  a majority at `β` at the sweep's start and at its end; it unlocks where that fails (no site is
  fixed). The pump's top rung is `2^22` (`PUMP_TOP`: one numerator of logit then weighs 64 bits, past
  the exponential's `2^(−62)` grain). An open site is written as a NUL in `FREE.tsv` (no codec class
  writes it, so a calculation through it is never read as written) and as `░` in the text shown.
- **The landmarks** are read through the realization (`read_landmarks`; on the card, the last tick's
  weight rows of the named sites, the entries outside the support read zero), and ranked by one law
  (`landmarks_of`); nothing drives the release from them.
- **Training's second sweep** replaces `Shape::Released` with even odds against the masks. Its read 1
  gives the extent as the release reads it (`Field::extent`), so the region is cut where the release's
  is, and read 2 carries each content site's read-1 face over the content classes. The learner's held
  step is read first, on the masked regions and the read-1 regions, so the mixtures come from the
  material that stands (the review: read before the held step's read, a refused step left read 2
  carrying mixtures of a material that no longer stood, and the step was read on regions it had
  partly formed).
- **The projection** reads the pairs the card meets (`met_pairs`) beside the site rows; a lap's real
  cost follows the learned classes, so a lap past its bound stops the run (its partial evidence
  reported as incomplete), never a raised bound.
- **Owed**: the falloff reads the strand's distance `|i − j|` (a sound or motor strand is one); the
  graph distance of a two-dimensional region (an image) is owed with that codec.

Measured on the host while building (the field's tests):

- The founded contact: an equal word 30 sites away outweighed every site past the near field in 32 of
  32 rows; it held the whole row's peak in 31 (a near site out-scored it once: the near field is heard
  at every frequency).
- The learned fixtures learn more slowly than under the all-pairs contact, a regression measured, not
  hidden: the cue's successor 0.083 bits at 600 sections (0.006 under all pairs, a bar of 0.0625); the
  key's recall 0.557 bits at 1,000 (0.020 under all pairs, a bar of 0.25; 0.295 with two sheet bits
  before the shells). Their bars are now read against knowing only which classes are present (`log₂ 9`
  and 2.09 bits): below a quarter of a bit and below a third of 2.09 bits. The review named this the
  recorded failure of a bar moved to fit; the laws that slow them (the falloff, the near field, the
  shells) are Brandon's lens and the record's, so the slower learning is reported as their cost.
- The covector's central difference crosses a seam where `±δ` moves a site across a shell: the classes
  are locks, piecewise constant, so those probes are left out and counted; a region of 26 sites reads
  the class contacts past the near field and the closure over far holders.

The card against the host on the crib terrain (the runs' receipts, §13): every read, logits read,
face, covector entry, learner text, release and landmark equal at both widths.

## 11. The three papers of Brandon's lens, joined

[agent-inferred, November 1] Brandon gave three papers with the correction this record answers. Each
is joined to the owner it touches; none changes a law above.

- **Boudourides, "Consensus and persistent harmonic edge circulation in a Hodge-theoretic model of
  networked information flow" (arXiv:2608.15397).** Node values move by the edges' imbalance,
  `ẋ = −d₀*u`; edge flow is forced by node disagreement and dissipated by the Hodge Laplacian,
  `u̇ = −βΔ₁u + d₀x`. The nodes reach consensus, and the edge flow settles at its initial harmonic
  projection: circulation on a cycle no face fills never drains; filling it with a 2-cell moves it to
  the coexact sector, where `d₁*d₁` dissipates it; linear damping drains every flow, nonselectively.
  On the exact sector each mode is `ä + βμȧ + μa = 0`, a damped second-order consensus. Joins: the
  release's momentum is that damped second-order step (§4); the circulation receipt reads the
  harmonic sector, a loop of contacts no assignment satisfies; the merge's 2-cell (§3) is the face
  that drains it. The selective drain is the merge, not the momentum's friction.
- **Gao, Shaikh, Kissinger, "Graphical Algebraic Geometry" (arXiv:2605.13993).** A diagrammatic
  language complete for commutative algebras and affine varieties, generated by copy and delete (a
  comonoid), add and zero, multiply and one (monoids), and scalars, with bialgebra and distributive
  laws; a closed diagram is a counting constraint problem (#CSP), and over `𝔽₂` a SAT network. Joins:
  the families of §3 are these generators read as contacts: copy is a still head's class contact
  (fan-out), merge is the pair contact `a ⊙ b` with the current's sum (fan-in, multiply and add),
  scale is a gain. They transfer because every polynomial constraint network, in any ecology, is
  composed of the same generators; frustration is a closed diagram no assignment satisfies.
- **Liu, Liu, Zhang, Fu, Tang, "Hyper-derivative algebraic geometry codes via local expansions"
  (arXiv:2609.18098).** Codes evaluated through the local expansions of functions at rational places
  (their jets), weighed by the NRT poset metric (a column weighs by the depth of its first nonzero
  coefficient), whose duals, read through the residue theorem, reverse the expansion's order; their
  asymptotics are read on function-field towers. Joins: the octave falloff is a weight of the same
  kind, a distance read by its order rather than its magnitude (§2.3); the residue duality's reversal
  is the helical code's pairing `σ̄(w) = σ(w)ᴿ`; local expansions are the series the exact law stores.

Owed to #410 with the rest of §9: the release's step as the exact-sector mode of a damped consensus.

## 12. Shells, the skin and the foil

[definition; agent-inferred, November 1] Brandon's lens of the same evening (shells, relativity,
Bessel functions, the skin effect, barycentric coordinates, the foil) changes three laws and the
release's receipts. Each is built and checked against the card (parity at both widths).

**The skin phasor.** A diffusive medium carries spatial period `n` with one e-fold of decay a radian
of turn: the skin effect, `J ∝ e^(−(1+i)x/δ)`, in a wire the Bessel function of a complex argument
(the Kelvin functions). So a turned mode of ring period `n_m` carries a pair `d = j − i` apart by
`e^(−2π|d|/n_m) e^(2πi d/n_m)`, not by the bare turn:

```text
contact    z_ij = 2^(−β) Σ_m D_m(|i−j|) Re(conj(ŵ_im) ŵ_jm) − ⌊log₂ |i − j|⌋,   D_m(d) = e^(−2π d/n_m)
current    ỹ_i = Σ_(j∈S_i) e_ij D(|i−j|) ṽ_j / mass_i
```

A still mode's period is infinite and it does not decay. The decay is a resident face per turned slot
and distance on the frames' `2^(−30)`, read from the exponential's face (`skin_decay`); below the grain
it is zero, so the finest ring is heard within eight sites while the top ring and the word reach the
whole region: fine place is heard only near, the blur of far sources the first design lacked. The
decay depends on the distance alone, so the contact stays reciprocal.

**The shells** (superseding §2.2's half-turn sheets). A class digit is a trit, not a bit. On mode `m` of the unframed word: the sky plate
(`+1`) where `Re > |Im|`, the ground plate (`−1`) where `Re < −|Im|`, the bridge (`0`) where
`|Re| ≤ |Im|`. The plates are where the in-phase part dominates (the mode locks and boosts), the bridge
where the quadrature dominates (it turns). `|Re| = |Im|` is the mode's light cone, the null set of its
Lorentz form `Re(w²)`, and lies on the bridge. The class is `Σ_m 3^m (trit_m + 1)` over the first
`b = min(n, ⌈½ log₃ reach⌉)` modes: 4 trits and 81 classes at reading 8's reach. The counting sort is
unchanged apart from the key.

**The falloff's provenance.** A strand wound on rings is a tube surface, two-dimensional, so a source
spreads as the Hankel function: amplitude `1/√d`, power `1/d`. That is the `⌊log₂ d⌋` bits of §2.3.

**The foil.** A lock is a foil, not a fact: a counterfactual surface the rest of the field is read
against, its counter kept in the medium as the opposite charge on the other plate (a hydrofoil or an
airfoil: the counter exists in the medium, and the charges cannot disobey the constraint that binds
the plates). Here the counter cannot vanish: the exponential's face never releases a class's mass to
nothing, so every lock carries its runner-up at a finite margin, however high the pump. Locked sites
keep moving under their momentum. The release's receipts become:

- a trit a site a sweep: `+1` it holds its lock, `0` it is soft (on the bridge), `−1` its top class was
  overturned this sweep;
- each locked site's counter: its runner-up class and the lock's margin over it at the final `β`,
  `β (ℓ_top − ℓ_runner)` bits;
- the free circulation: the `−1` trits, overturns, which are frustration;
- the bound circulation: the locked sites whose lock held through the whole last rung, the foil's lift
  fixed by its constraint (as the Kutta condition fixes an airfoil's circulation).

**The reading.** The pump's `β` is the release's only time: a normalization, not a clock. A soft site
is a barycentric point in the simplex of its classes, and the current a barycentric combination of
what a site hears. A click, sites locking together, is a merge face filling a loop of contacts: the
tube closing into an egg. The geometry is affine: the encoding sends a barycentric point of the
class simplex to its affine image, the mixture opening `Σ_a p(a) E(a)`, and the word is an affine
chart of the face, so placement (the shells, spectral: which modes lock on which plate) and navigation
(the current, a barycentric combination carried by the skin) are read in one affine geometry, and the
merge faces that fill loops are the algebraic cycles the compression keeps.

Of the winding guide's objects this adds the **cell holonomy** to what the build touches (the bound
circulation is a loop's fixed charge) and keeps the **tower thread** attached (the skin decay is each
ring's own reach on the tower).

## 13. The crib probe and the ninth reading failed: the field learns slower, and the release locks the commonest byte

[measured] Both runs at commit `66d1539d1` on the RTX 4080 SUPER under the card lock, reading 8's
declaration, keys, section and rate; receipts `…_receipts/crib9/` and `…_receipts/reading9/`
(count-only; the crib's texts are synthetic).

- **Parity** held at both widths before each run (crib: 9 reads a width and 4 releases; GSM8K: one
  section, the withheld read and 4 releases; every face, covector, learner and release equal).
- **The crib probe** (deadline 900 s, ran 73 s): 0 of 0 first calculations written (bar 24 of 126). The
  learner's withheld code went 5.46 → 4.54 → 4.55 → 4.55 bits over three laps, the second growth was
  held and the run ended; the context read 4.56 bits (§19's law: 2.88 after two laps, 1.93 after
  ten). 205 of 248 held steps were refused in the second lap. The release never resolved a void at the
  opening (no extent cut); 73 of 128 answers locked whole, 55 ended with 2,090 open sites, and from
  sweep 10 the open sites overturned every sweep (free circulation 108,128).
- **Reading 9** (deadline 900 s, ran 309 s): 0 of 0 first calculations (bar 24 of 128). Three laps
  (57, 59 and 93 s, the third grown), the withheld code 5.61 → 5.62 → 5.44 bits (reading 8: 3.94, 3.26,
  2.98), the context read 5.46 (reading 8: 3.26 after two laps). The release never resolved a void at
  the opening, and every one of the 128 answers locked whole within 7 sweeps at rung 2, all 1,229 sites
  at the space byte, each lock's margin 4 bits (bound circulation 157,312, free 0). The three held
  releases shown were 1,229 spaces each.
- **Pairs.** One read of every section of a GSM8K lap meets 4.46 × 10⁹ pairs, projected from the opening
  sections (every site against every other: 31.0 × 10⁹), but the lap took 57 s against reading 8's
  48.8 s: the support's gather costs more a pair than the tiled all-pairs contact did.

Located causes, each the next loop's subject:

1. **The held step was judged on the opening.** The build read the held step on the next section's
   masked regions and its second sweeps' first reads, every answer site on the unresolved row, a state
   training never compares; 205 of 248 steps were refused in the crib's second lap and its withheld code
   stood still. Repaired in the next build: the step is read on the masked regions.
2. **Training's signal halved.** Half the regions are second sweeps, every answer site open on a soft
   mixture of a near-flat read-1 face, so half the compared sites carry little of the answer's own
   context; the passage's own code fell 4.74 → 4.27 bits a lap on GSM8K against reading 8's 3.94 → 3.30.
3. **The release meets states training never compares.** Training reads the second sweep at `β = 1`;
   once the pump sharpens the mixtures toward the field's own tops (not the masks' true classes), the
   faces flip together: on the crib every site locked at sweep 8, the pump doubled, and the whole answer
   overturned at sweep 10 and kept overturning. §5's argument that later sweeps lie between the masks
   and the second sweep fails where the tops are wrong.
4. **The opening's interior is one state.** Every interior answer site opens on one word, so it shares
   one class and meets the same question sites; the falloff and the skin set them apart only by their
   distances, the void is never resolved at the opening, and on GSM8K every interior site locked at the
   commonest byte.

[measured] **The crib probe again, with the held step read on the masked regions** (cause 1 repaired;
receipts `…_receipts/crib10/`, ran 168 s of 900): 0 first calculations again. The withheld code fell
further, 6.01 → 5.88 → 4.91 → 4.34 → 4.27 bits over ten laps (one growth after the first), the context
read to 4.29, but the certificate stopped depositing: 235, 237, 166, 45, 21, 4, 2, 16, 8 and 0 of 248
sections, each later section standing nowhere after its halvings (about one a section). The release
locked every answer whole at rung 4 within 8 sweeps, each the question's `<` and then 52 `#`.

5. **The certificate stalls on the shells' seams** (a cause located from this run, not yet tested): the
   resonance classes are piecewise constant in the material, so a step moves sites across shells and
   changes the support; the covector reads within one support, and the step's direction stops lowering
   the code a section reads (a section's step stood nowhere 248 times in the tenth lap). The covector's
   own test leaves such probes out; the learner meets them at every step.

## 14. The front of the definite: the answer grows from what has settled, each site keeps its own clock, and a lock fades at its light cone

[definition; agent-inferred, November 1] §13's causes 2–5 are laws, settled here before any further
run; cause 1 is a repaired bug. One fault underlies causes 3 and 4 and reading 9's unread question
(its held answer coded 5.629 bits with its question and 5.629 with a foil's): the release and training
both put answer sites where nothing definite reaches them, and one temperature for the whole answer
cooled them there. Cause 5 is the shells' hard edge (§14.2). This section supersedes §4's pump, §5's
second sweep, §10's bipartite far rule and §10's restated fixture bars, and grades §12's shells; the
rest of §2–§12 stands.

### 14.1 Only the plates radiate far

[definition; agent-inferred] Past the near field a source is heard only where it is definite: known
(the question, or the truth in a training region) or locked (a foil). A soft site, on the bridge, is
heard only in its near field, and so is an unreached site (`∗`). The support becomes directional:

```text
S_i^h = { j : 0 < |i − j| < 6 }  ∪  { j : |i − j| ≥ 6, B_h(j) = B_h(i), j known or locked }
```

A mode on a plate is in phase and radiates; on the bridge it turns, and its field is reactive, held
near its source as an antenna's near field is, decaying like the skin's. The contact score stays
reciprocal (§2.1); only which sources are heard far changes, so a receiver of any state (`∗`, soft,
locked) reads the definite sources of its class. No clique can form: `∗` and soft sources are never met
far. Under §10's rule an open answer site met the question only through the class of `∗` or of a
near-flat mixture, which on GSM8K is the class of the space: reading 9's answer read the question's
spaces and nothing else. A definite source outside a receiver's class is still heard, blurred, through
its octave's crowd (§14.10).

### 14.2 A lock fades at its light cone

> **Retired (§15.2, measured).** The hold below was built and is gone: with the least hold over the
> class's modes the cue fixture coded 2.12 bits, and the memberships that replaced it failed too
> (§15.2's table). A far source of the receiver's class is heard at weight one; a seam is crossed at a
> jump, and the held step's exact certificate reads it. The text is kept as the account of what was
> built and measured.

[definition; agent-inferred] §12's shells meet at each mode's light cone, `|Re| = |Im|`, where the mode's
Lorentz form `Re(w²) = |w|² cos 2φ` vanishes. A mode's hold on its shell is its distance from that cone,

```text
λ_m(w) = |Re(w_m²)| / |w_m|²  ∈ [0, 1]        (1 at a shell's centre, pure in phase or pure quadrature; 0 on the cone)
λ(w)   = min over the class's b modes of λ_m(w)
```

and a far contact through a class is weighted by both ends' holds:

```text
e_ij = 2^(z_ij − max_(j∈S_i) z_ij) · λ(w_i) λ(w_j)        |i − j| ≥ 6, j ∈ S_i
```

The near field is heard without it, at every frequency. A site whose word crosses a seam leaves its old
class with weight falling to zero and enters the new one from zero, so the code a section reads is
continuous in the material across every seam, and the covector carries the term through `λ`. That is
cause 5's repair: a held step's direction describes the step it takes, and the covector's test reads
every probe, the seams included (a probe straddling a seam crosses only the kink at zero weight, and is
counted). The hold is exact: a ratio of integer faces, released on the weights' `2^(−40)` grain. It also
pulls each word toward the centre of its shell, where its far contacts are loudest, which is the lock
growing firm as it learns. A word on its cone is heard only in its near field: the bridge's own
reading.

### 14.3 The front

[definition; agent-inferred] An open answer site is **reached** once a known or locked site lies in
its near field, and once reached it stays reached. An unreached site carries `∗`, the unresolved row
the masks show; it is not moved and cannot lock. A reached site opens at rest on its opening face
(`ℓ = z⁰`, `m = 0`) and moves every sweep by §4's momentum. So the answer grows out of the question:
the answer's first five sites, beside the question, are reached at the first sweep, and each lock reaches the sites within its
near field at the next. The front moves at most five sites a sweep, and only where something has
locked; a frustrated stretch holds it until the stretch settles. Every reached site keeps moving and
can be overturned (a foil), and nothing behind the front is fixed.

This is propagation, not a certainty order. A site is reached by its distance from a definite
surface, never by its own sureness, and the site the field is surest of has no precedence. Cause 4 is
removed at its root: no site moves before something definite reaches it, so no interior site can lock
the prior (the space on GSM8K; on the crib's rerun, `#` after the question's `<`).

### 14.4 Each site keeps its own clock

[definition; agent-inferred] The pump is per site. A reached site's `β_t` starts at 1 and doubles after
a sweep in which its own change `Σ_a |Δp_t(a)|` fell below its change the sweep before, compared
within its own rung. A site whose change did not fall holds its `β` and rides its momentum: that is
frustration. A site is locked where its top class held a majority at its own `β` through the sweep;
it unlocks where that fails. A site near the moving front keeps changing as its neighbours are
reached, so it cools only after its near field settles. Each site's time is the normalization of what
has reached it (§12's relativity reading); there is no global temperature. §4's pump (one `β` per
problem, doubling on the problem's total change) is retired: on GSM8K it cooled the whole interior at
the third sweep, before anything had reached it.

The release ends for a problem when every reached site is locked and the extent is read, or at its
sweeps or its time; sites still open are shown open.

### 14.5 The extent is read where the front first locks the void

[definition; agent-inferred] The void is a class at reached sites until the extent is read. The
extent is read once, at the first reached site that locks on the void; the sites after it resolve to
the void, and inside the extent the void is no class (§10's law, its reading moved from the opening,
where on both runs it never resolved, to the front). If the front reaches the answer's bound with no
void locked, the extent is the bound, and the receipt says so.

### 14.6 Training meets the front

[definition; agent-inferred] §5's second-sweep regions are replaced by **front regions**, at even
odds with the completion masks. For a training answer of extent `A`, a keyed front `f ∈ [0, A]` and a
keyed rung `r` over the pump's rungs:

```text
read 1    the question known; answer sites before f: a keyed subset open on ∗ at the masks'
          densities, the rest the truth; the band [f, f + 5) open on ∗; past it ∗ (unreached)
read 2    the prefix's open sites carry their read-1 faces at β = 2^r, locked where the top holds a
          majority at that β (so they radiate far); the band carries its read-1 faces at β = 1
          (soft, heard near); past it ∗
compared  read 1 and read 2 at the prefix's open sites and the band, against the truth; the band may
          hold the true end, so the void is learned at the front
```

The carried mixtures are data with no covector through them; read 2's covector reaches the encodings
through them as now.

- Cause 2: read 1 has the prefix's truth around it, so its faces are informed, not near flat.
- Cause 3: read 2 shows the field its own sharpened tops at every rung of the pump and compares each
  against the truth, so a wrong top is learned as a foil to overturn.
- Cause 1: the held step is read on the next section's regions as training compares them (masks and
  front reads), never on the release's opening.

### 14.7 The card

- The release reads the question, the reached sites and the five sites past the front. No site reads
  an unreached site past its near field, so the region read a sweep grows with the answer.
- Each class lists its definite members first (the counting sort's key gains the definite bit), and a
  receiver reads its class's definite run contiguously, as tiles of class runs. Reading 9's lap met
  4.46 × 10⁹ pairs in 57 s against reading 8's 31.0 × 10⁹ in 48.8 s: the gather cost more a pair than
  the tiled all-pairs pass, and the time must follow the pairs met.
- The per-site `β` is a shift, the reached and locked marks are bits, the front and the extent are site
  indices. Host and card agree bit for bit.

### 14.8 The fixtures' bars

The learned fixtures' bars return to their original values: 0.0625 bits for the cue's successor at
600 sections, 0.25 for the key's recall at 1,000. §10's restatement against class-presence baselines
is withdrawn as a bar moved to fit. Each fixture is read again under the whole build. One that misses
is reported with its measurement and its cause located before any GSM8K run, never restated and
never given more sections.

### 14.9 Acceptance, receipts and owners

The bars are §7's, unchanged. The release receipt adds the reached count and the front a sweep, and
per problem the sweep each site was reached and locked, its own rung at its lock, and the extent's
reading (site and sweep). The held step's refusals are read per lap. A run's projection takes the
release's sweeps from the front's measured speed over the answer's bound, and its deadline is fixed
once.

Owners: `hnn::tower::field` (the directional support, the fading lock, the front, the per-site pump, the extent at
the front, the front regions), `field.cu` (the definite bit in the class lists, the holds on the far
weights, the region cut at the front) and `field_train.rs` (the front regions, the receipts); their atlas rows change in the same
commit.

The recorded failures this could repeat (§8 carries over):
- **A certainty order**: refused; reached is distance from a definite surface, and every reached site
  moves.
- **An authored routine**: none; the front is the near field's propagation, the far rule the shells'
  own reading.
- **Text as the exception**: the near field and the front are the complex's; on an image or a
  sound the same rule reads graph distance.
- **A bar moved to fit**: §14.8 withdraws one.

Owed to #410: the front's monotone growth; the far weight's continuity across a seam; a site's own pump as the exact-sector mode of a damped
consensus with a local clock.

### 14.10 The far field arrives blurred; no definite source is walled off

[definition; agent-inferred, November 1] Reading 9's held answer coded 5.629 bits a byte beside its
own question and 5.629 beside a foil's, equal at every lap to the reading's printed thousandth. In a
dispersing medium every source reaches every site at its falloff, so a disturbance anywhere shows
everywhere, however faintly. Three laws of the build made the question's share vanish instead:
- **A wall, not a falloff.** Past the near field a source outside the receiver's class had weight
  exactly zero. A blank answer site has one class (the blank's), and most of the question lies
  outside it.
- **A fixed width at the row's peak.** Weights stood on `2^(−40)` of a row's peak, and a term below
  that was released to nothing with no remainder kept. That is a hand-picked width and a max, which the
  precision law forbids; §14.11 repairs it.
- ~~**Two hops a read.**~~ Withdrawn: reach is not a count of ticks. The falloff is the matched-friction
  ladder (`wave.matched-friction-reach`): a push crosses any distance `d` at its share `1/d` in one
  contact, so a source's reach was cut by the wall alone. Ticks compose relations; they do not set
  reach. Only the answer's first few sites hold the question's last bytes in their near field, and
  their share, averaged over a whole answer, sits below the printed thousandth.

The wall is not the medium's law. The skin effect says how a far source arrives: blurred, its fine
rings decayed and its coarse modes whole. So past the near field each receiver also hears every
definite source through its octave's crowd, on each side:

```text
crowd       C_ℓ^±(i) = { j definite : ⌊log₂|i − j|⌋ = ℓ, |i − j| ≥ 6, j on side ± of i }
word        w̄ = Σ_(j∈C) ŵ_j D(2^ℓ)          value   v̄ = Σ_(j∈C) ṽ_j D(2^ℓ)
contact     z_(iC) = 2^(−β) Re(conj(ŵ_i) w̄) / |C| − ℓ
weight      e_(iC) = |C| · 2^(z_(iC) − max)       (with the row's sources, one peak)
current     ỹ_i += e_(iC) v̄ / |C|,   normalized with the row
```

`D(2^ℓ)` is the skin phasor at the octave's near edge (§12): still modes whole, a turned mode decayed
and turned by its ring, below the grain absent. The crowd is heard as `|C|` sources at the mean of
their words, each at the octave's falloff, which is the octave balance of §2.3: about `2^ℓ` sites at
`2^(−ℓ)` each, heard together about as loud as one near site. A class-mate is heard both sharply
through its class and blurred through its crowd: resonance stands on top of the background.

- Every definite source now has a path into every site of its region and a share of every receiver's
  covector, which reaches each crowd member through the sums. Learning can find a far source no class
  yet meets: the founding's limit (a copy learned only where the founding already weighs its source)
  is lifted by the blur.
- Whether a far source is loud enough is the field's to learn through the scores, not a wall's to
  forbid. The grain still releases a crowd outscored by more than forty bits.
- The cost is a prefix sum of the definite words and values a head a tick, and two crowds an octave
  a receiver: `O(N log N)`, against the class runs' pairs. Integer sums, so host and card agree bit for
  bit.
- Unreached and soft sites stay out of the crowds (§14.1): only plates radiate far.

Owner `hnn::tower::field` and `field.cu` (the crowds' prefix sums); atlas rows with them. The crowd's
weight against the members' own (`|C| · 2^(mean score)` against `Σ 2^(score_j)`, which Jensen's
inequality orders) is owed to #410.

### 14.11 The row is a series: no term is released without its remainder

[definition; agent-inferred, November 1] The contact's weights are the normalized exponential, whose
denominator is the row's sum: the series the precision law names (numerators grouped over the
denominators they share, softmax among them). The build stored each weight at a fixed `2^(−40)` of its
row's peak and released every term below it to nothing. A hand-picked width and a max are the same
error as a float: they cut the series at one width and lose the small terms without account. In
reading 9 those small terms were the question.

```text
term      e_ij = 2^(z_ij),  z_ij = a_ij + f_ij,  a_ij its whole bits, 2^(f_ij) the exponential's face
group     N_a = Σ_(j : a_ij = a) 2^(f_ij) ṽ_j,   M_a = Σ_(j : a_ij = a) 2^(f_ij)      (one group a power of two)
row       y_i = Σ_a 2^a N_a / Σ_a 2^a M_a
```

- Each term keeps its own exponent. Terms are summed whole within their power of two; the groups are
  combined with their carries in a carrier as wide as the exponents the row actually holds. The width
  is the row's, read from its terms, never chosen.
- Nothing is released before the current. The current is released once, at the precision of the
  register it enters, and its remainder is carried with it (the residue of the row's one division), so
  a source outscored by any number of bits still enters the row's sums.
- No peak is subtracted. The groups need no max: the exponent is the term's own address in the
  series.
- Integer sums in any order, so any partition of the support, of the heads and of the card gives the
  same bits.

Every other fixed width in the field (faces `2^(−16)`, material `2^(−24)`, frames `2^(−30)`, the
contact covector's `2^(−40)`, the skin decay's zero below `2^(−30)`, the pump's top) is read against the
same law in the build's review: a width that releases a term with no remainder kept is repaired the
same way; a width at a declared crossing, with its remainder carried, stands, with its reason written
beside it.

Owner `hnn::tower::field` and `field.cu` (the grouped row); atlas rows with them. The grouped row's
equality with the exact normalized exponential is owed to #410.


## 15. Faces are kept whole: a site carries its moment, the head's row is the face and each mode is locked, a read leaves its echo out, and the release's clock is read

[definition; agent-inferred, November 1] Brandon's lens of the evening (paraphrased): a face is lock
and key, the way a canyon's face is read for the rains that carved it without the whole history; a
numeral's binary places are a face, a vector or matrix, and never one denominator; a byte or a token is
a pointer into phases and modes, and inside the machine only that geometry moves; there is information
in the temporal distribution and its gaps; and a falling code or an answer that lands now and then is no
promise: the output must visibly reconfigure from general patterns, with similar problems handled
alike. Read against the built field, four defects are real, and each breaks a law the repository
already states. They are repaired in this build, before any run.

### 15.1 A site carries its helical moment; its byte is only a pointer

The field opens a site on its byte's row and its two neighbours' rows (§2.1), and its module says so:
there is no clock between sites. The helical code says every Holon carries its phase-carried moment
(`navigator.source-moment`, formal-checked in `Transport/SourceMoment`; `hnn.ring-moment-keys`). With
the pointer alone a number is never a face: `48` is two rows, and `48` in the question and `48` in a
calculation share nothing a contact can fit except byte against byte. The tower had the moment, and on
the generated terrain it coded unseen results within 0.1 bits of seen ones (the October 23 terrain
record); the field's own module names the cause it walked away from instead of repairing: the founded
units spelled one number differently in two places.

```text
moment   s_t,m = Σ_(k ≤ t) ζ_m^(t−k) D_m(t−k) E_m(u_k)      a turned mode, ζ_m = e^(2πi/n_m), D_m its skin;
                                                            the backward strand likewise over k ≥ t
open     x⁰_t = the still word E(u_t) + E₋ + E₊ (§2.1), beside the moments s_t,m
span     f_(i,j],m = s_j,m − ζ_m^(j−i) D_m(j−i) s_i,m = Σ_(i<k≤j) ζ_m^(j−k) D_m(j−k) E_m(u_k)
```

- The span's face does not depend on where the span stands (`D` is exponential, so the transport
  composes). The same digits in the question and in a calculation have the same face under any
  segmentation, which repairs the units' cause. No unit is authored or founded: a contact reads a span
  through its two boundaries (Stokes, `⟨dȞ,H⟩ = ⟨Ȟ,∂H⟩`).
- A head's value is linear in the moment (never normalized before it), so two heads' currents returned
  with opposite signs through `O` form a span's face.
- Superposing and filtering (Brandon's lens of 17:02): the moment is the superposition, every source
  at its skin and none selected; the contact is the filter, the sparse binding. The field had only the
  filter.
- Exact: the moment's near part term by term, its far part through §14.10's octave crowds in the
  absolute frame (prefix sums of `ζ^(−k) E(u_k)`, blurred at `D(2^ℓ)`); integer sums in any order.
  The answer's moments are recomputed each sweep as its sites' mixtures change.
- The pair contact is founded as the complex product per mode, `a_m b_m`, so two ring faces compose by
  adding their phases: the one face law `q(x + y) = q(x) q(y)` for every additive character of the
  rings. A sum's face can then form from its operands' faces wherever both arrive, and no operation is
  named. The founding decides what learning can find (§19); the learned maps around it move it from
  there.

### 15.2 The head's row is the face; each mode is locked against the source as it arrives

[measurement; agent-inferred, November 1] The section as first written asked for a row per mode, a hold
per mode and a membership split across each address mode's cone. Each was built on the host and measured
on the learned fixtures before it was kept (the cue's successor at 600 sections, bar 0.0625 bits; the
key's recall at 1,000, bar 0.25 bits; one founding, the same keys):

| Build | Cue (bits) | Recall (bits) |
|---|---|---|
| §14: one row a head, least hold over the class's modes | 2.124 | 0.916 |
| rows by mode, the pairing `D Re(conj a b)`, memberships | 3.236 | 1.423 |
| rows by mode, the lock (below), memberships | 3.134 | 1.050 |
| rows by mode, the lock, sharp classes | 0.265 | under 0.697 * |
| one row a head, the lock, memberships, band `2^(−3)` | 3.307 | 2.461 |
| the same, band `2^(−5)` | 2.935 | 1.679 |
| the same, band `2^(−8)` | 3.224 | 0.862 |
| the same, band `2^(−12)` | 0.599 | under 0.697 * |
| one row a head, the lock, sharp classes, no hold, the real merge `a ⊙ b` | 0.142 | 0.039 |
| the same, the complex merge (§15.1) | 0.177 | 0.053 |
| **the same, each receiver probing across its seams (below)** | **0.022** | **0.014** |

\* The recall test then asserted §10's withdrawn restatement (0.697 bits), and the cue test 0.25 bits, so
those cells and the first account of this table, which wrote "passes" for the sharp address, were read
against the wrong bars; the review of November 1 found it, and the tests now assert the record's. The cue's
miss at 0.177 bits was located before any run: 80 % of its code sat in 5 of its 64 held problems, where
the successor's earlier site shared the reader's class in at most one of its four head and tick rows and
was heard only blurred, through its octave's crowd (the other 59 coded 0.039 bits). One founding's
reading is not the law's: over six further foundings the sharp address coded the cue at 0.034, 0.021,
0.212, 0.060, 0.107 and 0.050 bits, and with the probes at 0.043, 0.031, 0.043, 0.060, 0.026 and 0.046,
every one inside the bar. Near-equal laws read on one founding (the narrowest band against the sharp
address) differ within that spread.

The last row is the law, with §15.1's moments in the values.

```text
contact  z_ij = 2^(−β) Σ_m [ D_m Re(conj(ŵ_im) ŵ_jm) − D_m² |ŵ_jm|²/2 ] − ⌊log₂ |i − j|⌋        the head's lock
row      y_i = conj(U_i) Σ_a 2^a N_a / Σ_a 2^a M_a                                            §14.11, one a head
address  the sharp shells; a far source of the receiver's class is heard at weight one
gain     β the largest shift with 2^(−β) n ≥ 2⌈log₂ reach⌉ (an equal word locks at n): −2 at the reach of 2,221
```

- **The face is the head's whole word.** A row per mode reads one complex coordinate, and one complex
  number cannot pick a word out of hundreds: a mode's row peaks wherever one coordinate happens to agree.
  The head's row reads the word's `2n` reals together, a vector face (Brandon's lens of the evening:
  a face is a vector or a matrix, never one number), and its one denominator normalizes a vector match;
  it is not a scalar collapse.
- **The lock is the pair contact's own slip.** `(|a|² − |a − D b|²)/2` per mode, up to the receiver's own
  power, which every term of its row shares: greatest exactly where the arriving face equals the
  receiver's. With the bare pairing a mode's louder key outscored the equal word (the cause the head's
  unit power had repaired, §2.5), and it would return wherever the powers of the modes differ; the lock
  is that repair stated as the contact's law. Summed over a still head at unit power it is the head's
  pairing less a constant.
- **The address is sharp, and a receiver probes across its seams.** A membership that is a partition
  of unity across the cone (amplitudes `r_across = (1 − φ)/√2`, `r_own = √(1 − r_across²)`, `φ = λ/ε`
  within a band `ε`, the far weight their overlap `Σ_c a_i(c) a_j(c)`) kept the code continuous across
  every seam, yet faded the weights it should have carried, and failed both fixtures at every band but
  the narrowest. `½(1 ± λ)` everywhere is dense: the bridge borders both plates, so every site holds a
  share of the all-bridge class; and `√μ` has an unbounded slope where a membership reaches zero. §14.2's
  least hold coded the cue at 2.12 bits. The repair reads across the seam without fading: a receiver
  reads its own class and, for each address mode whose word lies within the band `ε = 2^(−⌈log₂ b⌉)` of
  its cone (`|re² − im²| 2^k < re² + im²`, exact), the class across it, every combination of those
  crossings; a source stays in its own class alone and enters a probed run at its full score, and the
  lock decides. The probes are bounded by the modes near a seam, so the rows stay sparse. A seam or a
  band edge is crossed at a jump; the held step's certificate compares the codes exactly, and the
  covector's tests read every probe at a step that crosses none.
- **The row's carrier is the row's own.** On the card a launch's limbs follow the widest exponent spread
  its rows actually hold (about 107 to 122 bits at reading 8's declaration with `β = −2`), refused only
  past the declaration's bound ([`FieldDeclaration::row_bits`]).

### 15.3 A read leaves its own echo out

The release reads every answer site at once through reciprocal contacts, so a site's face returns to it
two ticks later. A symmetric network iterated synchronously settles only at fixed points or two-cycles
(Goles and Olivos; Marcus and Westervelt for the analog case), and the crib's answer flipping whole every
sweep (§13) is that two-cycle; the momentum only slows it. The cavity field removes it: the field a site
feels leaves out what the site itself put there. Under parallel iteration on dense reciprocal couplings
this is the Onsager reaction term (the TAP equations, approximate message passing), and the cavity is
the method behind the Mézard–Parisi formula for diluted spin glasses, proved in openai/math, family 221.

```text
cavity   z_i^(k) ← z_i^(k) − B_i ℓ_i^(k−1)      B_i: the read's response at i to i's own soft face, through
                                                its contacts and back (the round trip p_ij p_ji through the return)
```

`B_i`'s exact form is derived at the consumer and written beside it; training on the release's states
(§14.6) reads the same cavity, so it meets what the release meets.

### 15.4 The release's clock is read

Each site's clock (the sweep the front reached it, the sweep it locked, its trits and the gaps between)
went only into receipts. It enters the face as a turned ring set whose place is the site's own sweep
count since it was reached: sites reached or locked together share phase, their gaps are read like
distance, and the contact reads rhythm beside content. In training, §14.6's rung supplies the count.

### 15.5 The reading shows similar problems side by side

The reading's claim becomes the one Brandon asked for: the output reconfigures with its problem.
- `tools/gsm8k_variants.py`, an exterior terrain generating its truth: in a held problem every question
  number is replaced by another of its digit count, the solution's annotated calculations are
  re-evaluated exactly in order, their results carried into later calculations and into the text, and
  a variant with a fractional, negative or colliding number is refused. Only text reaches the machine;
  the variants are held out like their originals and stay private.
- **Claim, fixed before the run:** of the original releases' calculations that took an operand from the
  question, the variant's release takes the variant's number in the same role in at least half.
- **Shown whole:** three held problems, each beside two of its variants.
- The crib check stays first (§7).

### 15.6 Failures this could repeat

- **Catered machinery.** The variants are exterior truth and never a receiver. The pair contact is
  founded on the face law's product and is told no operation.
- **Text as the exception.** The moment, the lock, the cavity and the clock hold for any strand; no
  numeral is named inside the field.
- **A located cause carried unrepaired.** The units' spelling cause is repaired by spans read at their
  boundaries, not avoided by bytes. The louder key's cause (§2.5) is carried into each mode's term by the
  lock, not reopened by a pairing without power.
- **A refusal answered with a larger limit.** The lap is measured before launch and its deadline fixed
  from that.

### 15.7 Built

[measurement, November 1] On the host (`hnn::tower::field`: 56 of its 61 tests run and pass, 5 are
measurements run apart) and on the card (`field.cu`, `field_moment.cuh`; parity below):

- **§15.1 moments** (`field::moment`): both strands' moments of zero-founded encodings `E⁺`, `E⁻`
  (families `moment_before`, `moment_after`, `(A+1) × 2T` over the turned modes that are not clocks),
  added into each tick's unframed value. The frame turns a source at `k` seen from `t` by `ζ^(k−t)`, the
  conjugate of this section's `ζ^(t−k)` notation, so the moment carries `ζ^(k−t)`. Near terms exact, far
  terms through the octaves' prefix sums at `D(2^ℓ)`, one release; the octave blur reaches about three
  quarters of a unit on a 48-site span under the 729 ring, so a span's face is exact where the near field
  covers it. The return is the moment's transpose with the turned covector's prefix released once at the
  covector's grain (the exact transpose's `2^(−114)` refused real covectors of about sixteen units at a
  406-site region). Founded at zero: the founding is unchanged, and learning grows the moments along a
  linear path. The pair contact is the complex product, contact `e < f/2` read as `a_e + i a_(f/2+e)`.
- **§15.3 the echo**: `B_i = mean over the heads and the consecutive ticks of Σ_j p_ji^(t) p_ij^(t+1)`,
  on `2^(−63)`, the reaction term at the order where the read's currents are their shares' averages; the
  cavity `z ← z − B ℓ` with `ℓ` the logits a site's carried face was formed from and `B` from the read
  that formed them (the release's previous sweep; training's read 1 for read 2), both data.
- **§15.4 the clock**: the last `clocks` turned ring sets are framed by each site's sweeps since it was
  reached (the question by the sweeps since the release began), with no skin. The command founds one
  where at least two turned sets stay on the place (`heads − still ≥ 3`). Training's read 2: the prefix
  at its rung `r`, the question at `r + 1`, the band and past it at zero.
- **§15.5 the variants** (`tools/gsm8k_variants.py`, 35 tests): on the held 128, two variants each for 89
  problems and one for 10; 29 have none (no annotated calculation, a number word, results that would turn
  fractional, or roles that collide). Its `claim` reads the claim at a variant's calculation `i` by
  operand value, and `show` writes the three problems beside their variants under `.local/` only. What the
  claim does not witness (the lesson of October 9, 12): a release that copies the variant's question
  number into calculation `i` takes it whatever the arithmetic, so a release that copies without
  computing passes; the claim reads reconfiguration with the problem, never a calculation's value. So
  reading 10's receipts carry a second reading beside it, fixed here before the run and not a bar: of
  the variant releases' calculations with an operand among the variant's question numbers, how many
  write their expression's exact value at the equals, beside the same count on the originals' releases
  with the originals' numbers (`VARIANTS_COMPUTED`). It reads whether anything is computed rather than
  copied.
- **The review's repairs.** The key's bracket `D ŵ_i − D² ŵ_j` is released by the skin's bits before it
  meets its covector, and its products are checked against the carrier and refused (it had stood 30 bits
  above the guard, and host and card wrapped alike); growth lifts the moment encodings' step state divided,
  as their covector arrives divided over the copies; the echo reads the direct pairs' round trips and
  leaves out the crowds' (a locked site is also a crowd member of the sites it reads), as its formula
  states.

### 15.8 The fixed widths, read against the precision law (§14.11's review)

[definition; agent-inferred, November 1] Each fixed width in the field, with its reason:
- **Faces, charts, currents on `2^(−16)`**: a declared crossing at every tick's state, released to the
  nearest numerator; the state is a face of the field's continuing motion, read by the next tick only,
  and its remainder is the attained face's error, which the next tick's own release bounds. It stands.
- **Material on `2^(−24)`**: the deposit's grain, the step's crossing into the constitution, certified by
  the exact comparison of the codes it moves. It stands.
- **Frames and skins on `2^(−30)`**: resident navigator faces (`ring_phasor`, `skin_decay`) attained once
  at a declared grain, never a store of values; a skin below its grain is zero, which is the skin's own
  reading past `D(d) < 2^(−30)` (the ring's place no longer heard), not a term cut from a sum. It stands.
- **The contact's covector on `2^(−40)`**: the return's grain, a declared crossing of `δz` into `δs`,
  with its carrier guarded and refused past it. It stands.
- **The rows' shares on `2^(−63)`**: formed once by one division of the exact series, for the return. It
  stands.
- **The pump's top `2^22`**: one numerator of logit then weighs 64 bits of the face, past the masses'
  `2^(−62)`; a site there is decided. It stands.
- **The moments' return**: the turned covector released once at its own grain before its prefix (§15.7),
  replacing the exact transpose's `2^(−114)` that refused real covectors.
None releases a term from a sum before the sum is formed; the series row is the one place that did, and
§14.11 repaired it.

### 15.9 The crib run failed, and an open receiver now hears every definite site

[measurement, November 2] The crib run under §15 as built (`…_receipts/crib11/`: 27 laps in 463.7 s on the
card, 8.0 minutes of the 18 Brandon granted, peak resident 0.42 GB, the card's board at 11,118 MiB in the
release) wrote 94 first calculations; 14 took their operands from the question, against the foil's 13
(bar 24). The held answer coded 2.014 bits a byte beside its neighbours with its own question and 2.014
with a foil's: the question told it 0.0001 bits. The three releases shown were one pattern whatever the
question. Every one of the release's 386 landmark digits fell on a question digit, and 47 of them (12 %,
about chance among ten digits) carried the true digit's class: the contact found digits, not which digit.
The minimal witness, §19's number told by its order, coded 6.341 bits at 300 sections on the build, where
the field whose every site read every other coded 0.40; the crib passed under that field (25 of 126
against 2) and failed under the dispersing one (crib 9 and crib 10), so the regression came with §14's far
support, not with §15.

[definition; agent-inferred, November 2] **An open receiver hears every definite site.** Past the near
field a definite receiver (known or locked) hears its class's definite members and those of the classes it
probes, as before; a receiver that is not definite (an answer site open on `∗` or carried soft) hears
every definite site, each at its full lock and its falloff, and hears no crowd, since it hears every one of
them sharply. Why: a question number wanted by its order shares no word with the answer site that wants
it, so the sharp address met it only blurred, in its octave's crowd, where the octave's digits average;
and the closure's covector reaches only the sources a receiver meets, so no address law could be learned
toward a source never met sharply. Read through the dispersal lens it is a listener in a dispersing
field: the definite sites radiate, an open receiver hears them all at their falloff and filters them
through its lock; definite-to-definite stays sparse, so the field is not every site reread against every
other. Its pairs a head and tick are the open sites times the definite ones (about 40 × 400 in a crib
release region against 450² for every pair).

[measurement, November 2] On the host: the cue codes 0.010 bits and the recall 0.004; the number told by
order 3.568 bits at 300 sections, 0.958 at 500, 0.349 at 650 and 0.093 at 900, against 0.40 at 300 under
every-pair. Its slower learning is not the lock (the pairing alone: 2.806 at 300), the merge (the real
merge: 5.039), every receiver's listening (2.850) or the falloff (none: 3.944); its cause is open. The
fixture's reading at 300 sections misses the every-pair field's 0.40; that is reported here as measured.

### 15.10 The lock's temperature is deposited; growth waits for a fall

[measurement, November 2] The crib run with the open listener (`…_receipts/crib12/`) rested after three
laps: its first lap raised the withheld code from 5.459 to 5.912 bits a site, the growth rule read that as
a spent width and grew at lap 0, and at the grown width 240 of 248 steps were refused; a second growth had
no projection, and the run rested. The release wrote no calculation.

[definition; agent-inferred, November 2] **The lock's sharpness is part of the constitution.** The words
are held at unit power (§2.5), so the gain `2^(−β)` was the contact's fixed temperature, nothing learned
could sharpen or soften it, and one temperature served supports of very different size (a class receiver
about ten near sources and its class-mates, a listener about four hundred definite sites). Each head now
carries two temperatures, one for each kind of receiver, a material family deposited like any other
(`z = T · S − ⌊log₂ d⌋`, `S` the lock at unit gain; `δT = Σ δz · S`, `δs = T δz`). The class receiver's
opens at its equal-word guarantee (`2^(−β)`, `β = −2`); the listener's at the largest `g` with
`g² · 2n ≤ (⌊log₂ reach⌋ − 1)²`, so the lock's random spread over a listener's support (`σ = g √(2n)`, two
unrelated words at unit power) stays within the falloff's own span over the support's octaves while an
equal word still leads (its lock `2n g` above the mean, the random maximum over `N` about `σ √(2 ln N)`,
below it while `N < e^n`): `g = 1` at the crib's reach of 484 with `n = 8` (`σ = 4` bits against a span of 7;
an equal word's lead over the maximum of 400 about 2 bits). A listener opening at `+2` was built first and
refuted: the cue coded 2.018 bits. [correction, November 2, from the review of 04:23] `+2` was taken for the
gain of the field whose every site read every other, which passed the crib; that field (`0bf600eaa`) used a
gain shift of `0` at this declaration, held its probe and key at unit power within a head, and kept separate
learned probe and key charts, where this field ties them into one word. The `+2` run was an experiment, not
that control.

[measurement, November 2] The hypothesis this answered, that a listener's founding row peaks on the
loudest of four hundred unrelated far words and drowns its near field, is refuted by its own fixture
(`a_listener_s_founding_row_keeps_its_near_field`, 420 sites, no recurring word, 40 open): at the founding
the near field holds 0.818 of an open listener's row and the loudest far source 0.005 at the listener's
temperature, and 0.836 and 0.018 at the class receiver's. That refutes the story on this fixture; it does
not read the crib's own masks and fronts or the state after lap 0, so the first-lap rise's cause is open. The fixtures with the temperatures: the cue 0.007 bits, the recall
0.001.

[definition; agent-inferred, November 2] **Growth waits until the withheld code has fallen at its width.**
The rule grew when a lap left the withheld code no lower than the lap before, from the founding on; a lap
that raises the code from where the width began has not spent the width but harmed it, and growing copies
the harm. It now grows only once the code has fallen at the width.

### 15.11 The held step is read on the admitted future

[definition; agent-inferred, November 2] A section's step was certified on its own regions and held
against the next section's training regions: masks opening a fraction `τ ∈ (0, 1]` of a region and fronts
with a long unreached tail. The crib is judged on context regions (the question known, one answer site in
four open, its neighbours known) and on the release's front, and the withheld problems the growth reads are
context regions. A step that harms those was accepted unseen, and under the open listener this matters more,
since a listener's support is the definite sites and training's masks and the readings differ exactly in
how many sites are definite. Each section's held read now also reads its problems as context regions (one
part of `CONTEXT` a problem, keyed by its draw), read for the held step only and never fit: a step that codes
the whole held read higher is halved or refused, as before. The crib run's per-lap withheld code is the
measurement of whether lap 0 still harms.

### 15.12 A lock is its key's foil, not its copy: a listener probes with its own chart

[definition; agent-inferred, November 2] One word a head was both the probe and the key (§2.1), so a
receiver's lock had to equal the key it fits: a source was found only where the two words resembled each
other. That serves a cue (an equal word recurs) and fails a number wanted by its order, whose source shares
no word with the answer site that asks for it. The field that passed the crib kept separate probe and key
charts (the review of November 2's correction of §15.10). Read through Brandon's lens, a lock is its key's
foil, related to it by a learned chart, not its copy. A listener (an open receiver, §15.9) now probes with
its own chart `P` of the same read (framed and at unit power within its head as the word is), and its
sources answer with their word; a class receiver's probe stays its word, since its support is the class its
word names. `P` opens as the word chart itself, so the founding reads as before, and learning moves the
probe apart from the key where a receiver asks for what does not resemble it. Growth splits `P` as it splits
the word chart.

[measurement, November 2] The number told by order: 1.148 bits at 300 sections, 0.412 at 350, 0.195 at
400 and 0.046 at 600 (3.568, 2.674, 1.792 and 0.558 with the probe tied to the word; 0.40 at 300 under the
field whose every site read every other). The cue 0.007, the recall 0.001; the field's tests 57 of 57.

Owners `hnn::tower::field`, `field.cu`, `examples/solenoidal_alpha/complete_language/field_train.rs`
and `tools/gsm8k_variants.py`, with their atlas rows. Owed to #410: the span's face as the difference of
boundary moments (from `moment_closed_form`), the head row's equality with the exact normalized
exponential, and the cavity's removal of the synchronous two-cycle.

## 16. A turned head keeps its navigator's own clock: the copy is one relative phase along the answer strand

### 16.1 What crib13 measured

[measurement, November 2] crib13 (the field of §15.9 to §15.12 on the card, the crib terrain, 27 laps fixed)
rested after 10 laps when its second growth came due (§16.7), its release wrote no calculation (bar 24 of 126),
and its held read's question effect was −0.00085 bits. Its ten rested learners read on the card with no deposit
(`peaks-field`, [`FieldRealization::read_row_peaks`], 5 s), at the 258 first-operand digit rows of the 128 held
problems' context parts, tick 1:

| | lap 0 | lap 9, best head |
|---|---|---|
| spread over the question (flat 8.29 bits) | 0.98 to 7.9 bits | 2.0 to 2.5 bits |
| share on digits (flat 0.018) | 0.02 to 0.03 | 0.78 |
| top source a digit | at most 2 % | 79 % |
| top source the right class | at most 1.6 % | 26 % |
| top source the right site | 1.6 % | 20.5 % |

Within the digits the rows sat at chance (right share over digit share 0.29 against 0.27 flat): they sharpened
onto digits over the laps and never onto the digit asked for. The class temperatures fell about 10 % over the
laps and the listeners' rose about 13 % (16.05M to 18.23M on `2^(−24)`, head 0).

[agent-inferred, November 2; the coordinator's diagnosis] The field's only place was the codec's byte index (the
turned rings `ζ_m^(t mod n_m)`, the moment's `ζ^(k−t)`, the falloff). The crib asks for the first and second of
two or three numbers written at random word places in a 240 to 560 site question: an ordinal among the strand's
numbers, which no byte phase carries (the first number's byte distance from the answer ranges over hundreds of
sites). The fixtures passed because at 24 sites with distinct digits an absolute place suffices. This repeated
two recorded lessons, the codec's grain read as time and a design thought in offsets, and broke the guide's time
law: no privileged clock.

### 16.2 Law 1: a turned head's clock is its navigator's own

[definition; agent-inferred, November 2] Each turned ring set that is not a clock (a head that carries a moment)
reads a pace, one material row `c_h` of `D` ([`FieldLayout::pace`], founded at zero):

```text
κ_h(t) = 1 + release(⟨c_h, x⁰_t⟩, 16)          on 2^(−24), x⁰ the opening face
τ_h(t) = Σ_(0<k≤t) κ_h(k),  σ_h(t) = Σ_(0<k≤t) |κ_h(k)|      exact prefix sums, τ(0) = σ(0) = 0
U_(t,m) = ζ_m^(τ_h(t))                          the resident ring at a whole τ, its series between (turn_phasor)
D_m(i, j) = e^(−2π |σ_h(i) − σ_h(j)| / n_m)     the skin follows the turn (skin_of)
```

The frame and the moment read `τ` in place of the byte place (the near term `ζ^(τ_k − τ_t) D(σ)`, the far octave at
the receiver's skin to the place `2^ℓ` away on its side); the falloff and the near field keep the strand's byte
distance. At `c = 0` every rate is `1` exactly, the pace is plain, and the field is today's bit for bit: a plain
pace takes the resident faces, and a strand paced at its own places gives the byte moment and return bit for bit
(the moment's tests). The step into site `k` is ticked by site `k`'s own face.

[definition; agent-inferred, November 2] **An open site ticks by the face it carries.** The rate reads the site's
opening face, whose own term at an open site is its carried mixture of class rows by their shares, or the
unresolved row where it carries none. A clock that reads digits therefore ticks by an open site's expected digit
when it carries a face, and by the unresolved row's pairing with `c` when it carries none (zero for the witness's
digit clock, §16.6).

[agent-inferred, November 2; the coordinator accepted both] Two corrections to the design as briefed:
1. **A digit clock, not a numeral-start clock.** `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))` is additive over the
   sites, so `⟨c, x⁰⟩` cannot express "a digit after a non-digit" (an AND). A digit clock can (`κ = 1` at a digit,
   `0` elsewhere): the answer's copied digits then meet their sources at one clock distance, the question's digit
   count less one at a front, for every digit of both operands.
2. **The skin follows the turn.** "One e-fold a radian of turn" with `τ` turning the ring makes the skin
   `e^(−2π|Δσ|/n)`, the byte distance's at `κ ≡ 1`; with the byte distance kept, any clock mode would vanish at the
   crib's distances (`e^(−2π·300/81) ≈ 0`). The variation `σ = Σ|κ|` keeps the skin multiplicative along the strand
   where a rate runs backward.

[definition; agent-inferred, November 2] **The covector.** The clocks return through every place they enter:
`δτ_t += b Re(conj(δw) i w)` for the word, the value and the probe (unframed charts), `δτ_i −= b Re(conj(δy) i y)` for
the current's return to the receiver's frame, each pair's and crowd's skin `δσ ∓= sgn b D E` with `E = 2^40 ∂/∂D`
from its value (`p Re(conj(δỹ) ṽ)`) and its lock (`δs (2 P 2^g − 2 D Q)` over the lock's grains), and the moments'
`pace_return` (`∂s_t/∂τ_t = −i b s_t`, `∂s_t/∂τ_k = i b W_tk E_k`, each skin at its two ends). Then
`δκ_k = Σ_(t≥k) δτ_t + sgn(κ_k) Σ_(t≥k) δσ_t`, `δc += Σ_k δκ_k x⁰_k` and `δx⁰_k += release(c δκ_k, 24)`: `O(N·D)` a head.
A growth parts each pace row over its face's copies, so `⟨c', x⁰'⟩ = ⟨c, x⁰⟩` exactly.

[measurement, November 2] The field's tests 60 of 60, six ignored (the tower's 217): the covector tests read the pace family
beside the others; the pace's own test reads each paced head's three largest entries by a fitted slope over
`±4δ` and `±8δ` on clocks that stop, run fast and run fractionally, 24 reads, none on a seam. The far-support
test reads its slope by a line fitted to 17 reads over `±4δ`: one central difference could not resolve it at the
narrow step on a paced field (a q-chart entry read −357 and −187 against −509 and −255 at `±2^15` and `±2^14`, a
line over `±2^14` −383.5, over `±2^16` −475.3, over `±2^18` −509.0; at a zero pace −476.1, −513.9 and −542.7
against −543), and 264 probes read so after 344 halvings, none on a seam, within the tolerance it had.

### 16.3 Law 2 and the ticks: a number travels by its strand

[definition; agent-inferred, November 2] The first operand's first digit (the anchor) locates the earliest digit
at tick 1, and its current carries that source's phase relative to its own, `ζ^(τ_(j*) − τ_a0)` on each mode it
reads. At a front (the question and the answer before the receiver definite, the receiver open, so it ticks zero),
the copy's source for every later digit of both operands stands at `τ_src − τ_i = τ_(j*) − τ_a0 + 1`: the anchor's
phase times one constant turn. The receiver reads the anchor's current through a still head, where it arrives
unturned (through a paced head the relative frame would add `len(a) + k`), and its probe on the paced head carries
it at the next tick.

[definition; agent-inferred, November 2] **The ticks the copy needs.** `K = 1 + 1 + 1 + h`: the anchor's find, the
relay's read, the probe that carries it, and `h` relay hops. An open receiver hears every definite site, far
included (§15.9), so it reads the anchor directly at any distance: `h = 0` and `K = 3` for every operand digit, at
any operand length the terrain declares (GSM8K's longer numbers too). A relay through class receivers alone would
need `h = ⌈(s − 5)/5⌉` hops for an operand span of `s` sites past the near reach of 5. crib13's field had `K = 2`,
which cannot carry the anchor's phase into any later digit's probe; the run's declaration is `K = 3` by this law.

### 16.4 The admitted future is the front

[definition; agent-inferred, November 2] §15.11 read the held step on context parts (one answer site in four open).
An open site ticks by its face, so in a part each earlier open digit stops the digit clock and shifts a later
receiver's `τ` by one: at `b₁` of `a = 123` the shift is 2, not the front's uniform 1. The release reads fronts,
and the bar reads the release, so the held step is now read on front-shaped regions (each problem's question and
its answer before a keyed front definite, every site from the front through the answer's first void open). The
held read's context parts stay in the receipts (`FIELD_HELD`) as a measurement, mis-clocked by the earlier open
digits of their part.

### 16.5 The matching lock

[definition; agent-inferred, November 2] **A silent key scores zero, above a decayed match.** Per mode the lock is
`|p|² − |p − D k̃|²`: a receiver scores a source by how near its decayed framed key comes to its probe. A source with
no key scores `0` against every probe; a far source's best score is small (its `D` is), so a far source wins only
where every nearer source scores below it, the silent ones included. Every source a receiver must not find must
therefore oppose its probe. Consequence for learning: the keys of the sites an anchor must pass over (every
non-digit on the anchor's mode) have to be driven to oppose its probe; the covector drives them only where the
anchor's comparison reaches them.

[definition; agent-inferred, November 2] **A key's power where the probe does not read is a cost**, `−D² |k|²` a
mode: two functions in one head, read by different probes, interfere unless each keeps little power where the
other probes. **One mode cannot select an exact clock distance** across the crib's `Δτ ∈ [1, 9]`: the power term
moves its peak by `D`, so the best single-mode phase leaves a worst-case margin of about 0 bits; two periods (16
and 32) fed by the same head's current reach a worst of 4.0 bits in the chart's model after the falloff's charge
(measured 7.07, §16.6). The copy's comb and the anchor's search therefore share one head (the channel must come
from the head whose row found the source), with the anchor's mode at a power of 1 in 16.

### 16.6 The witness

[measurement; agent-inferred, November 2] `the_witness_copies_the_first_calculation_by_its_clock` (tests.rs, set by
hand, no learning, the crib declaration D 32, H 5, n 8 at `K = 3`): 64 problems of the crib's law (`crib_like`:
regions of up to 451 sites, two or three numbers of one to three digits at random word places, repeated digits,
two to nine digits a question), every digit of the first calculation's two operands read at its front. Head 3
(paced, the digit clock) carries the anchor on its period-81 mode (window `bΔτ + ψ ∈ (−π/2, −π/4)`, `ψ = −27/100`
of a turn, where the skin makes the score rise with `Δτ`) and the copy's comb on its periods 16 and 32; head 0
(still) relays the anchor's two channels; the anchor's key is a ratio of the site's own reads, so a read's scale
moves none of it.

- **The copy:** 252 of 252 rows put their largest share on the same digit of the question's number. The margin
  over the next source, in bits: min 7.07, p05 7.93, p10 9.00, p25 10.46, median 12.49, p75 28.89; its minimum by
  the question's digit count 2 to 9: 9.0, 14.9, 14.3, and on to 7.07 at nine.
- **The anchor, read as the receiver it is at each front:** 188 of 188 where it is definite (a class receiver
  probing with its word) and 64 of 64 where it is open.
- **At `κ ≡ 1`** (today's field, the same charts): 7 of 252, no anchor.

The sibling shows that in this construction the clock carries the copy. The general claim, that no setting of a
byte clock carries "the first number" at random places, rests on the derivation of §16.1: its byte distance from
the answer differs from problem to problem, so no fixed relative byte phase, skin or falloff selects it. The
witness shows the design can represent the relation at the terrain's size; only the run can show that the field
learns it.

### 16.7 Growth is held, the laps go on

[agent-inferred, November 2] A run carries the projections of its declaration and of one growth; crib13 ended at
lap 9 of 27 when its second growth came due. A second growth is now held and the laps go on at that width
([`growth`] in `field_train.rs`, with its test), so the run's workload is its laps.

### 16.8 The card realizes the clocks

[definition; agent-inferred, November 2] `field.cu` realizes the pace bit for bit: the rates, clocks and variations
as exact scans a region and head (`field_paces`), the frames at the clock by the turn's series (`field_pframes`,
`turn_dev`), every pair's and crowd's skin from its variation (`skin_ij`, the resident decay at a whole variation
and the series through the exponential's face between), the paced moments (admission at the faces' bound
`PACED_L1 = 2^31`, the paced prefixes, the near terms at `ζ^(τ_k − τ_t) D(σ)`, the far return from the skinned
prefixes), the moments' clock covector, and the frames', the current's and the skins' returns into `δτ` and `δσ`,
then `δκ`, `δc` and `δx⁰`. A plain region reads the resident faces, so the founding is today's card bit for bit.

[measurement, November 2] Parity, host against card (forward, covector, learner, the held rows, the peaks, the
open return): at the founding's learning, 5 sections at width 32 (the withheld section and both releases
included) and 4 at width 64, every one equal, the pace moving off zero from the second section (256 entries);
with the pace drawn far from the founding (`FIELD_PARITY_PACE`), every section equal at both widths:

| width | draw | κ | sections and withheld | releases |
|---|---|---|---|---|
| 32 | `>> 10` | −0.14 to 2.40 | equal | 2 of 2 equal |
| 32 | `>> 8` | −3.55 to 6.61 | equal | 2 of 2 equal |
| 64 | `>> 10` | −1.49 to 2.64 | equal | 2 of 2 equal |
| 64 | `>> 8` | −8.97 to 7.57 | equal | not read (the 180 s guard) |

### 16.9 The founding's route to the clock

[measurement, November 2] At the founding the covector reaches neither the paces nor the paced heads' word rows:
the readout is founded at zero, so no covector reaches a chart until the readout moves (`align-field`, card, crib13's
declaration at `K = 3`). After the run's own first section (nothing saved), the second section's covector:

| head | rate's route: gap (elsewhere − digits) / rms | anchor mode: opposing / near-silent / aligned | near-silent driven to oppose / align |
|---|---|---|---|
| 2 | −0.047 (weakly toward a digit clock) | 570 / 7429 / 465 | 3700 / 3729 |
| 3 | +0.469 (away) | 593 / 7387 / 484 | 3784 / 3603 |

The route exists on one head and is weak; the anchor's mode is near-silent for 88 % of the non-digit keys and the
descent reaches them with no net drive. A clock helps only the charts that read its phase and those charts only
help with a clock, so descent on either half alone may see little: whether descent couples the clock and its
readers is read before any run (§16.10).

### 16.10 Whether descent couples the clock and its readers

[definition; agent-inferred, November 2; the coordinator's decision, fixed before the read] Three reads, no learning,
the covectors off the card, on the witness completed with a readout (the copy's current carries the source digit's
identity on its coarsest mode, which the readout reads, so the code at an operand digit falls when the copy holds):
(i) the witness's readers with `c = 0`, the covector on `c` per paced head (its gap at digits against inside words,
as a share of its root mean square, and its cosine with the witness's `c`); (ii) the witness's clock with the
founding's readers, the covector on the readers (its cosine with the witness's less the founding's) and the anchor
census's drive; (iii) the witness moved a small random step on `c` and the readers, the covector's cosine with the
step's reverse; (iv) (the coordinator's, November 2, §16.13) the descent on each head's and kind's `log₂ T` at the
witness with its temperatures at 4, and at the founding: if it rises at the witness and falls at the founding, the
temperature is coupled to the rows as the clock is. The run launches only if (i) and (ii) both pull toward the
witness, a clear positive sign on at least one head each, and (iii) points back; otherwise the obstacle is this
section's, and the next subject.

[definition; agent-inferred, November 2; fixed into the run's declaration] **The early stop.** After nine laps, a run
whose paced heads' clocks have not moved toward a digit clock (no head's gap `κ̄ at digits − κ̄ inside words` above
its founding's) and whose held question effect is at or below the foil's stops, reported incomplete with its clocks
by lap (`FIELD_PACE`, `FIELD_STOPPED_EARLY`).

### 16.11 The completed witness: the copy rests until its channel arrives

[measurement; agent-inferred, November 2] `the_completed_witness_reads_the_copied_digit` (tests.rs, set by hand, no
learning, §16.6's terrain and declaration at `K = 3`) completes the witness with a readout: the copy's value carries
the source digit's identity `e^(2πi d/10)` on head 3's period-729 mode, written to dimensions 20 and 21, and a digit
class reads its own turn there (a non-digit held down). Its acceptance, fixed before the read: at every operand
digit's front (the question and the answer cut at the digit, the digit open) the face's top class is the question's
digit, 252 of 252, its code there below the founding's 5.46 bits, and the `κ ≡ 1` sibling fails the same assertion.

**The first completion failed on the faces while its rows passed** (93 of 93 rows on the source, 33 of 93 faces,
35 bits). The cause, read tick by tick: the copy's channel is a chain of three contacts (head 3's anchor current at
tick 0, head 0's relay at tick 1, head 3's probe at tick 2), so before tick 2 a receiver's probe is its bias alone and
its row tops on whatever source scores best on keys alone (the digit one before its source). A face reads `x` after
the `K` ticks, the sum of every tick's current: no lock or release law picks a tick inside a pass (the release's
momentum and pump act across sweeps; a pass's temperature is the same at every tick). And tick 0's current was about
70 times the later ticks': the chart reads a source at unit power, `r̂_j = x_j/‖x_j‖`, and once the channel's
currents (gains 64 and 32) land in a digit's `x` its identity's share of that power falls about 70 times. So the
wrong identity of the first two ticks outweighed the right one.

**The rest.** On head 3's mode 6 (period 243) every non-digit's key stands at the anchor's strength (from its own
non-digit read) and a listener's probe has a small bias there (`2^(−6)`). Before the channel arrives the probe is
that bias alone at unit power, so the copy rests on a non-digit, which carries no identity; once the channel arrives
it outweighs the bias. These are coefficients of the word and probe families, which the deposition moves; no
operator was added. At unit strength the rest did nothing (33 of 93): a key is read at unit power over its head, so
beside the anchor's term the rest's share of a non-digit key was `2^(−6)`.

[measurement, November 2] The 252 reads at each temperature (host, the hand-set witness, no learning: a check of the
law's reference, not a learner run; 16 threads, about 48 s a read of 252 against a projection of 50 s, 241 s for the
five under a 1,200 s guard, a resident set of about 1.6 GB):

| T | rows on the source | faces right | code (bits) | first calculations whole | faces by clock distance 1, 2, …, 8 |
|---|---|---|---|---|---|
| 127 | 252 | 252 | 0.299 | 64 of 64 | 14/14, 26/26, 42/42, 44/44, 60/60, 32/32, 22/22, 12/12 |
| 16 | 247 | 213 | 0.730 | 39 of 64 | 11/14, 26/26, 42/42, 36/44, 52/60, 24/32, 13/22, 9/12 |
| 8 | 208 | 143 | 1.600 | 11 of 64 | 10/14, 20/26, 28/42, 27/44, 33/60, 15/32, 6/22, 4/12 |
| 4 | 143 | 101 | 2.913 | 8 of 64 | 10/14, 19/26, 23/42, 21/44, 19/60, 7/32, 2/22, 0/12 |
| 127, `κ ≡ 1` | 4 | 35 | 12.899 | 0 of 64 | (no digit clock: the distances are bytes) |

The acceptance passes at 127, and its sibling fails. "Whole" is a problem whose first calculation has every digit of
both operands right, the bar's own unit (the crib's 24 of 126 is about 19 %). Receipt:
`_receipts/law16/completed_witness.txt`.

### 16.12 The skin bounds a copy's sharpness by its clock distance

[derivation; agent-inferred, November 2] A turned mode of period `n` carries a pair's lock by its skin
`D(u) = e^(−bu)`, `b = 2π/n`, at the pair's clock distance `u = |σ(i) − σ(j)|`, and turns the key by `ζ^u = e^(ibu)`.
The receiver's exponent for a source at distance `u` is, on the head's modes `m`,

```text
z(u) = T Σ_m [ |p_m||k_m| e^(−b_m u) cos(b_m u + φ_m) − e^(−2 b_m u) |k_m|²/2 ]        (bits)
```

with the words at unit power over the head (`Σ_m |p_m|² = Σ_m |k_m|² = 2n_head`). A copy selects one source, so its
source sits at a maximum of `z` over the sources' distances, and a neighbour one tick away trails it by the curvature,
`z(u₀) − z(u₀ ± 1) ≈ −½ z''(u₀)`, to second order. Mode by mode,
`|d²/du² e^(−bu) cos(bu + φ)| = 2b² e^(−bu) |sin(bu + φ)| ≤ 2b² e^(−bu) ≤ 8/(e² u²)` (the most at `b = 2/u`,
a period `n = πu`), and the penalty term's curvature `−2b² e^(−2bu)|k|²` only flattens the maximum. So

```text
lead over a neighbour one tick away  ≤  4 T Σ_m |p_m||k_m| / (e² u₀²)  ≤  8 n_head T / (e² u₀²)   bits
```

whatever the periods: a copy sharpens with its temperature and blunts as the square of its clock distance. (The
first statement sent to the coordinator, about `T/(eΔτ)`, read the first-order slope; at a maximum the slope is zero
and the curvature governs.) In the clock's own units the copy's distance is the digits between its source and its
receiver: with `κ = 1` at a digit and `0` elsewhere, an operand digit's receiver is `D_q − 1` ticks from its source,
its question's digit count less one, 1 to 8 here (read off every read; the `10 to 30` first sent was an error).

[measurement, November 2] The table of §16.11 reads the law: below 127 the faces fall with the clock distance at every
temperature (at 4, from 10 of 14 at distance 1 to none of 12 at 8), and the shortest distance falls too where the
comb's periods (16 and 32) stand far from the sharpest period `πu` (11 of 14 at distance 1 at 16). The copy
discriminates by its curvature, which no period escapes, so a temperature is what sharpens it.

[decision; the coordinator's rule, fixed before the read] crib13's learned temperatures topped out at 3.91 (class)
and 1.28 (listener), and moved about ±10 % in ten laps. The witness clears the bar's 19 % a problem only at `T ≥ 16`
(39 of 64; 11 of 64 at 8, 8 of 64 at 4), so the run would need learning to raise its temperatures 4 to 12 times
(from 3.91 and 1.28 to 16) within 27 laps. **The crib run does not launch.** The next subject is the temperature's chart: a temperature is a
scale, so its deposit belongs to the logarithmic chart of the ratio law (`ℓ = log R`, a step multiplies it); §15.10's
deposit is read, the law written, its covector tested and ported, and §16.10's reads are then taken. Where a learned
temperature must pass the card's row carrier, the carrier widens at a declared crossing (the precision law's dynamic
width), built only when the temperature's law shows it is needed.

### 16.13 A temperature is carried in its logarithm

[definition; agent-inferred, November 2] §15.10 deposited each head's two temperatures in the additive chart: the
material held `T` on `2^(−24)`, the return read `δT = Σ δz S`, and the learner's normalized step moved `T` by about
`2^(−k)` of a unit a section at any `T`, so a temperature moved as far at 1 as at 100 (crib13: about ±10 % in ten
laps). A temperature is a scale, the ratio of a lock's sharpness to the bits it is read in, so it is carried in the
ratio law's logarithmic chart: the material holds `ℓ = log₂ T` on `2^(−24)` and a step multiplies `T` by
`2^(Δℓ)` (`temperature_of` in `field.rs`): `T = 2^c · 2^(ℓ − c)`, `c = ⌈ℓ⌉`, the fraction read through the
exponential's resident face at `ℓ`'s `2^(−16)` (the bits the face resolves, the score's own grain) and released to
`2^(−24)`. The chain is `δℓ = δT · T ln 2`, carried a receiver's row at a time (`temperature_chain`,
`release(δT_row · release(T ln 2, 30), 24)`), so the rows' covectors still sum in any order to the same bits. The card
reads `T` from `ℓ` through its own resident face and carries the chain in its reverse (`temper_of`, `temper_chain`
in `field.cu`); the host's `temperature_of` and `Field::temperatures` are the reference its parity reads, and no part
of the card's forward or return runs on the host. A row's carrier bound reads the temperatures' ceiling octaves
(`Field::row_gain`, `T ≤ 2^⌈ℓ⌉`), from `ℓ` alone. The founding's gains are whole
octaves (`ℓ = −β`: 2 for a class receiver, 0 for a listener at the crib's reach), so the founding reads as before.
The carrier keeps the additive chart's reach on 32 bits, `2^(−23) ≤ T ≤ 2^7`; past it a temperature is refused,
never clipped. The field's text head is `hnn-field-v7`: a v6 state held `T`, not its logarithm.

[measurement, November 2] The completed witness under the chart (`T` held as `ℓ`; 128, 16, 8 and 4): at 128 faces
252 of 252, code 0.299 bits, 64 of 64 whole; its `κ ≡ 1` sibling 35 of 252 at 12.82 bits; at 16, 8 and 4 the same
counts as the additive chart's at those temperatures (213, 143, 101 faces). Receipt:
`_receipts/law16/completed_witness_logt.txt`.

The chart changes the step's size, not its sign: whether descent raises the temperature is §16.10's fourth read,
(iv), the covector on `ℓ` per head and kind at the witness with its temperatures at 4, and at the founding.

### 16.14 The coupling read on the card: the clock's descent points away

[measurement, November 2] The log chart on the card, against the host (`parity-field`, crib13's declaration at width
32, `K = 2`): five sections and the withheld section bit for bit (faces, covector, learner, held rows, peaks, open
return), the temperatures moving off their whole octaves from the first deposit; the releases were not read inside
the 180 s guard (incomplete there). The host's field tests, 60 of 60 (the temperature's covector read by a fitted
slope over 17 reads, since one temperature moves every score of a region at once and a single difference stands
near the code's rounding, about ±50 a read; at the larger steps a single difference agrees, e.g. 712 against 647,
−821 against −899, 946 against 900). Receipts: `_receipts/law16/parity_logt.txt`, `witness_card_t16.txt`.

[measurement, November 2] §16.10's reads on the card (`witness-field`, the crib codec and declaration at `K = 3`, the
515 first-calculation operand digits of the held problems, each a front cut at the digit; 10.6 s):

| read | result |
|---|---|
| the witness at `T = 16` | faces 447 of 515, code 0.742 bits (the founding: none, 5.459) |
| (i) the readers kept, `c = 0`: the clock's descent | cosine with the witness's `c` **−0.579**; the rate at digits less inside words, −0.293 of its root mean square |
| (ii) the clock kept, the founding's readers: the readers' descent | head 3 **+0.160**, head 0 −0.0001 |
| (iii) a keyed step of `2^(−10)` of a unit on the clock and readers | code 24.6 bits; the descent's cosine with the way back **+0.033** |
| (iv) `log₂ T`'s descent at the witness with `T = 4` | head 3 raises both (class +7.8·10^14, listener +2.4·10^14 on the covector's scale); head 0's class lowers (−2.5·10^11), its listener raises (+2.7·10^11); faces 239, code 2.863 bits |
| (iv) at the founding | zero at every head and kind: the readout is founded at zero (§16.9) |

[decision; the rule fixed before the read] (ii) pulls toward the witness on head 3 and (iii) points back, weakly, but
(i) points away: from a byte clock, with the witness's own readers, descent on the clock moves it from the digit clock,
as crib13's head 3 did at its founding (§16.9, +0.469 away). **The run does not launch.** (iv) shows the temperature
coupled to the rows as the clock is: it rises at the copy's head where the copy holds and has no covector at the
founding. The basin is narrow: a step of `2^(−10)` a unit costs 24 bits, so the witness is an isolated point of the
material, and descent cannot be expected to find it from far. The next subject is (i): why the clock's covector at the
byte clock, under readers tuned to a digit clock, points away.

### 16.15 The clock is a key: it is located by loop closure, and the readers and temperatures descend

[decision; the coordinator's, November 2, from §16.14] The clock is a key, and a key is located by loop closure, not
by descent (CLAUDE.md, "learning is locating keys", the Bombe literal); read (i) and the isolated basin are what
descent on a key looks like, and read (ii) says the readers descend once the clock is given. So the pace is located
by loop closure and the readers and `log₂ T` descend by the covector: two existing laws, each on its own object.

[derivation; agent-inferred, November 2] **The mapping, stated at the consumer.** The turn menu's ports read
`S(v) = S(u) + c` (`compression::keys::TurnMenu`); here `S = τ_h`. An edge `(i ← j)`, a receiver `i` and a source `j`
of one region, has the turn `Δτ_ij = Σ_(j<k≤i) κ(k) = n_ij + c·X_ij` with `n_ij = i − j` and `X_ij = Σ_(j<k≤i) x⁰_k`
on the encoding's unit (exact where the encodings are whole multiples of it, as the witness's are; elsewhere the
pace's release at `2^(−24)` is the face of the linear form). A copy is one stationary transport: its edges share one
turn `θ` (§16.3: a number travels by its strand, so every operand digit of one calculation is `D_q − 1` ticks from its
source, §16.12). Two edges of one copy close a loop, `c·(X_1 − X_2) = n_2 − n_1`, linear in `c`; a menu's loops cut
the pace's fibre as an exact affine set, read by the existing owner `ExactRatMatrix::affine_fibre`
(`holon/restriction/fibre.rs`), its radical the clock's gauge: `κ`'s scale (the encodings hold a constant feature,
so `λκ` is reachable, `θ ↦ λθ`) and the encoding's null directions (features whose sums are equal on every span).

**The missing terms, between those owners and the pace:**
1. *The pace's loop form*: edge `(i ← j)` to `(n_ij, X_ij)`, two edges to the row `(X_1 − X_2, n_2 − n_1)`, stacked
   for `affine_fibre`. TurnMenu reads a turn in `ℤ/d` shared by every edge with injective images, and PairLocation one
   turn menu per byte distance `δ`; neither reads a turn that is a linear form in an unknown key.
2. *The menu's admission under an unknown clock*: PairLocation admits every station pair at every byte distance, and
   at the located distance every edge is true by the terrain's law. A copy's edges stand at no one byte distance, so
   the hypothesis PairLocation enumerates has no finite analog here; it is replaced by the crib's alignment (the
   Bombe's crib dragging): a receiver run of the answer and a source run of the question with equal classes (the
   field's own class contact, read from the region alone, no key), each run's edges one hypothesis of one copy. A
   loop pairs two runs' edges; a false alignment shows as a loop that does not close with the others.

**The location, by intersection** (the coordinator's correction: no vote): a region's candidates are every value any
of its loops gives, true and spurious alike, and the located value is their intersection over the regions,
`fibre(loop :: menu) = fibre(menu) ∩ {closes}`; a region holding a loop that closes at every value prunes nothing; an
empty intersection is reported with its region's shortest loop, and a plural one stays plural (hnn::keys's
publication semantics). The second calculation's loops do not close at the first's turn (its copy stands `2 l_c`
ticks further) and cost nothing: they only add candidates within their own region. The own sheet's rate first (`c`
on the encoding's first dimension alone, the class receiver's sheet), then the full rows of the loops that close
there, through `ExactRatMatrix::preimage_fibre`; the gauge fixed by hnn::keys's convention, at the least port the
menu visits: the published member reads a rate of one there.

**The witness, its acceptance fixed before the read** (the coordinator's, with its second item corrected from "252 at
`T = 16`", which §16.12's bound refuses even to the exact digit clock): on the crib's training regions alone, the
located pace's fibre contains the digit clock up to its gauge and excludes `κ ≡ 1`; with the located pace and the
witness's readers, the faces are the digit-clock witness's at `T = 16` (213 of 252, front by front) and 252 of 252 at
`T = 128`. Only then the coupling reads under the located clock (the readers' descent, `log₂ T`), and only then a run.

[measurement, November 2] `the_clock_is_located_by_loop_closure_on_the_crib` (tests.rs; 256 training regions of the
crib's law, a draw apart from the 252 fronts', the witness's encodings; 9.6 s):
- the own sheet's pruning curve, the intersection's size after 1, 8, 64 and 256 regions: **85, 4, 1, 1**; located
  `c₀ = −1`, the digit clock's (100 regions held a loop closing at every value and pruned nothing);
- the full fibre: 7,413 rows from the loops closing there, every region contributing (256 of 256); dimension 27; its
  particular is `c = −e₀` exactly, the digit clock; `κ ≡ 1` is not in it;
- the radical: 25 directions no training site reads (the unused dimensions, the open row's, which no definite site
  carries) and 2 that move only the digits' rate (`e₁`, and `e₃ + e₅ − e₀` on every site with a left neighbour): the
  clock's scale, one orbit on the sites the menu reads;
- published at the least visited port, the class `0`, at a rate of one: the published pace is the witness's row bit
  for bit, so with the witness's readers its faces are the digit-clock witness's, 213 of 252 at `T = 16` and 252 of 252
  at `T = 128` (§16.13's receipt). Both items pass.

The coupling reads under the located clock are therefore §16.14's (ii) and (iv), taken with that clock: the readers
descend toward the witness on head 3 (+0.160), and `log₂ T` rises at the copy's head and is silent at the founding.

[agent-inferred, November 2] **What the run's location meets.** The witness's encodings are whole units on a few
dimensions, so the digit clock is a linear form of them. The run's encodings are the founding's keyed draws, dense
over 32 dimensions, and a site's opening is its class's row plus its neighbours' rows: the digit indicator is a linear
form of them only if 44 classes' three rows admit one `c` (132 constraints on 32 coordinates), which a generic draw
does not. There the full rows of a plural menu have no exact common member, and the own sheet has no first dimension
to restrict to; the run's location needs the loops' intersection over the full rows, with the clock read on the class
sheet its encoding carries.


### 16.16 On the class sheet the copies cannot separate the digit bytes' rates

[decision; the coordinator's, November 2] The clock is read on the class sheet, hnn::keys's port convention: a
crib's cells are the codec's classes, each its own port, known before any key, so `κ(t) = 1 + c[class(u_t)]`, one
located rate per class, a resident face beside `E(u)`. The class is the codec's own cell (here the byte) or one the
field derived, never an authored grouping: no digit list enters the pace or its locator. The neighbours' terms `E±`
of the opening leave the rate (a copy's turn is the sum of its span's rates, and the loop law reads only the span's
classes). Depositing the encodings first would couple the key to descent again (§16.14).

[measurement, November 2] On the same 256 training regions and menu (§16.15), read on per-byte ports: **every region
(256 of 256) holds a loop that closes under the digit clock and whose row has no digit byte at all**; 5,636 further
closing loops would tie digit rates, all coincidences (equal digit counts of different digits).

[derivation; agent-inferred, November 2] **Why, and what it costs.** A closing loop pairs two copy edges of one
calculation; its gaps are the rest of `a`, the text between the numbers and the head of `b` in the question, and the
rest of `a`, `+` and the head of `b` in the answer. A copy preserves its digits, so every digit byte cancels from
every true loop, and the loop reads only `κ(text between) = κ(+)`. Under the key law, a region's candidates are the
union of its loops' hyperplanes; each region's union holds its digit-free true loop, so each holds the whole family
of digit rates, and so does their intersection. The fibre is plural in the ten digit bytes' rates, nine directions
beyond the clock's scale. [correction, November 2, the coordinator's] They are not a plural fibre in hnn::keys's
sense but a gauge of the copy menu: moving a digit rate keeps every true loop closed, and no menu separates a key from
its gauge image (`compression::keys`, `fibre_gauge_truth`); keys.rs publishes a fibre that is one gauge orbit at its
gauge-fixed member, and falls back only where it holds several orbits. The coincidental closures would tie the rates
only if they were hypothesized true together, and they are not copies. Physically the copies are indifferent: a clock ticking 1 at `3` and 2 at `7` closes every copy loop.
What the rates change is the readers' discrimination (§16.12: a neighbour one digit away stands one of its rates away).

[correction, November 2] §16.15's location reached the digit clock on the witness's encodings, whose first two
dimensions are a digit sheet set by hand: the grouping came from those encodings, not from the data.

[definition; agent-inferred, November 2; the coordinator's decision, a declared symmetry-breaking convention beside
keys.rs's `S(p₀) = 0`, not a finding] **The published member is the current configuration projected onto the fibre**
in the port metric (independent codec cells: the identity). The loop rows are homogeneous in `κ`, so the fibre is a
linear space `L` with a basis `B`, and `κ_pub = B(BᵀB)⁻¹Bᵀ κ_cur`, exactly; on a direction no row reaches the rate
keeps its current value (deposition changes a constitution only where a covector reached it, and a closing row's
coefficient is zero on every class it cancels). At the first boundary `κ_cur ≡ 1`, so the digits would keep 1 and every
byte the rows pin go to 0, with no class named; at later boundaries `κ_cur` is the clock published before (D1).

**The fibre is computed, not derived, by propagation** (the union a region holds explodes in this chart): `S` opens as
the intersection of the hyperplanes of regions with exactly one loop; a region with a loop whose hyperplane holds `S`
is satisfied; a region with one live loop is forced, `S ← S ∩ H`; to a fixpoint. A region left with several live loops
none holding `S` cuts it into pieces, and the fibre is plural: the current configuration stands, the pieces are
reported, no tie-break. With no region of exactly one loop, that is reported with the loops' distribution, and nothing
is picked.

[measurement, November 2] `the_byte_clock_is_located_by_propagation` (tests.rs, the same 256 regions and menu on per-byte
ports, 2.1 s): **no region has exactly one loop**. Loops a region: one region with 15, every other with 16 or more
(median 315, most 1,833). `S` opens at all 44 bytes and stays there: 2 regions satisfied (each holds a loop whose row
is zero), 254 cutting, none forced, none empty. The propagation has nothing to start from, and nothing is published:
the crib's alignment admits far more candidate copies a region than the one or two true ones, so every region cuts.

[definition; agent-inferred, November 2; the coordinator's decision] **The menu admits only definite edges**: a
maximal equal-class run whose string occurs exactly once in the question and exactly once in the answer, a maximal
unique match. A run that occurs at several places is a plural edge, an unlocated choice, so by hnn::keys's semantics not
a menu edge. Uniqueness is read from the region alone: no key, no length threshold, no named class. Loops pair two
admitted runs as before; a region with fewer than two admitted runs is silent.

[measurement, November 2] `the_byte_clock_is_located_over_the_definite_menu` (tests.rs, the same 256 regions, 0.2 s):
runs a region 53 to 112 (median 76), admitted 1 to 4 (median 3), loops 0 to 5 (median 3); **60 regions with exactly
one loop**, 7 with fewer than two admitted runs; the listener check (each region's own calculation text, never fed
back): both of the first calculation's operand copies are admitted on 188 of 256. The propagation: `S` opens at
dimension 9 from the 60 forcing regions and stands there, 246 satisfied, none cutting, none empty, 10 silent: one
piece. Its published member (`κ ≡ 1` projected): **every digit byte, the space and `+` at 0**, the letters at
fractions between −2/3 and 2/3 (`a` −2/3, `b` 2/3, `c` 1/2, `e` −3/5, …, `q` 1), `?` 83/151, `<` −46/151, `=` 77/151.
Not a digit clock, and not a clock that copies (with every digit at 0 an operand's digits share one clock place).

[measurement, November 2] **Why: most forcing regions force a loop the key does not close.** Of the 60 single-loop
regions, the listener reads 15 whose one loop is the first calculation's two operand copies (a row with no digit byte);
the other 45 pair copies of two calculations (the first operand with the third number's copy in the second calculation,
which stands `2 l_s` ticks further) or a run of the total's line (` 4`). Both are definite edges, and the first kind are
true copies; but a loop closes only between copies of one stationary transport, and these join two. Forcing them pins
the digits' rates to zero. The propagation's premise, that every region's candidates hold the key, fails on those 45:
their one loop excludes it, and the propagation cannot see that (the remaining `S` is not empty).

[definition; agent-inferred, November 2; the coordinator's decision] **Two definite runs pair into a loop only when one
front band holds both answer targets**: their nearest edges in the answer stand fewer than the band's extent apart
(§14.6's band `[f, f + 5)`, `NEAR − 1`). A front's read releases one band under one clock state, so the copies one band
releases are read at one lag, one stationary transport; copies in different bands can stand at different lags (the
second calculation's, `2 l_s` further) and are not looped. The field's own band: no new constant, no key, no class.

[measurement, November 2] With the band: 188 regions with exactly one loop, and **the listener reads every one as the
first calculation's two operand copies** (188 of 188; no false loop forces); the propagation opens `S` at dimension 22
and stands: 188 satisfied, none cutting, none empty, 68 silent. Published (`κ ≡ 1` projected): **every digit byte at
1**, the space and `+` at 0, the bytes no closing row reaches at 1 (`?`, `\n`, `<`, `>`, `=`, `#`, and `q`, which no
syllable holds); the letters at fractions, a consonant at minus its syllable's vowel (`a` −2/3 with `b`, `h`, `n`,
`v`, `z` at 2/3; `e`, `i`, `o` −3/5; `u` −1/2): the crib's words are consonant-vowel syllables, so the rows pin each
syllable's sum, not its letters, and five vowel directions stay in the fibre.

[definition; agent-inferred, November 2] **The pace on the class sheet is built on the host** (`Field::paces`): the
layout's pace family is one rate a class and the unresolved row a paced head; `κ_t = 1 + c_h[u_t]` (a carried face's
mixture by its shares); the return `δc[u] += Σ_(k: u_k = u) δκ_k`, the opening taking nothing; growth copies a turned
head's rates whole; the text head is `hnn-field-v8`. The card still realizes the previous chart's pace (`x⁰`'s rows):
its port and parity follow the coordinator's next go. [November 2] Ported: `pace_rate` (a site's own class's rate or
its carried shares' mixture), `field_paces` without `x⁰`, `field_pace_c_back` one thread a head and a site with exact
adds, the opening's term retired.

[measurement, November 2] **The witness under the published clock fails** (the 252 fronts, the witness's readers, head
3's rates the published `κ − 1` at the material's grain, the unresolved row unreached at 1): faces **35 of 252 at `T =
16`** (the digit clock 213) and **32 of 252 at `T = 128`** (the digit clock 252); codes 15.9 and 18.7 bits. Of the 220
fronts lost at 128, 219 hold ticking letters in their copy's span, one only the unreached bytes (`\n`, `<`, `?`). The
cause is the skin: the copy's skin distance `|σ(receiver) − σ(source)|` is a median of 106 ticks (most 183) against the
digit clock's 1 to 8. The menu's gauge keeps every loop's `τ` closed (a syllable's signed rates sum to zero), but the
skin reads the variation `σ = Σ|κ|`, which a sign does not cancel, so the letters' ±3/5 add up over a question's words
and decay the comb's modes to nothing. A direction that is a gauge of the copy menu is not a gauge of the field: the
skin breaks it, and so does every reader's absolute turn (the unreached bytes at 1).

[definition; agent-inferred, November 2; the coordinator's decision] **A loop closes the transport's whole ratio**, not
only its turn. The field's transport between a receiver and its source is `ζ^Δτ e^(−2π|Δσ|/n)`; its logarithm has a turn
part `Δτ` and a skin part `|Δσ| = Σ_(j,i] |κ|`, and one stationary transport is one complex multiplier for all its
edges, so a loop closes in both (the ratio law: a comparison without its modulus part is as incomplete as one without
its phase part). A loop's row `r` reads both: `Σ r_x κ_x = 0` and `Σ r_x |κ_x| = 0`; copied bytes cancel in both, so the
digits stay unreached. After the turn's propagation, the forced loops' skin rows run to a fixpoint: where one side of a
row is zero on `S` (every byte there pinned at 0), the bytes of its other side are pinned, `S ← S ∩ {κ_x = 0}`; a row
live on both sides is not solved, and is counted.

[measurement, November 2] The skin pins the 25 letters the between-texts hold (all but `q`) in one step, `S` from 22
to 17 dimensions; no forced loop is live on both sides. **Published: every digit byte at 1; every byte of the
between-texts at 0 (the letters, the space, `+`); the unreached bytes at 1 (`?`, `\n`, `<`, `>`, `=`, `#`, `q`); no byte
off 0 and 1.** Under it, the 252 fronts with the witness's readers: **91 of 252 at `T = 16`** (the digit clock 213),
**112 of 252 at `T = 128`** (252); codes 8.1 and 15.5 bits. Every lost front (132 at 16, 140 at 128) holds only unreached
bytes ticking in its copy's span (`\n`, `<`, `?`), no letter; the copy's skin distance is a median of 10 ticks (most
13) against the digit clock's 1 to 8. The unreached bytes, at their current rate of 1, add the question's closing `?`,
the answer's `<<` and a line break to every copy's span: each copy of one calculation is shifted alike, so the loops
still close, but the witness's readers (the anchor's window, the comb's offset and the rest) were set at the digit
clock's absolute turns and skins, and read the shifted ones wrong. Not patched.

[decision; the coordinator's, November 2] The location is what the data supplies, and the unreached bytes keep their
current rate under the declared convention (no closing row reaches them; a rate set by hand would be authored). A
located clock is tested with readers built for it, by the digit-clock witness's own construction set from the
published clock's turns and skins read on the training regions; the bar is unchanged.

[measurement, November 2] The published clock's distances on the menu's 188 located copies (training regions only):
the anchor's distance stands **5 ticks** past the digit clock's on all 188 (the question's `?` and line break, the
answer's `<<`, and the open receiver's unresolved row, each unreached at 1), and the copy's offset from its channel
**1 tick** on all 188 (the open receiver's own rate): constant, since every crib question ends in one `?\n` and every
first calculation opens `<<`. The readers move by them (`witness_field_readers`: the anchor's window back 5/81 of a
turn, the comb's channels by one tick of each period), the comb's sense read on 64 training fronts (64 of 64 copies
right at one sense, 13 at the other). The 252 held fronts under the published clock and those readers:

| T | faces | rows on the source | code (bits) | whole | faces by skin distance 6, 7, …, 13 |
|---|---|---|---|---|---|
| 128 | **252 of 252** | 252 | 0.130 | 64 of 64 | every distance whole |
| 16 | **118 of 252** | 182 | 2.818 | 8 of 64 | 11/14, 18/26, 23/42, 24/44, 25/60, 10/32, 3/22, 4/12 |

The bar holds at 128 and not at 16 (the digit clock's 213). The cause is §16.12's bound, not the readers: every copy
stands 5 ticks further from its source (skin distances 6 to 13 against 1 to 8), and a copy's lead over its neighbour
falls as `T/u²`, so at the temperature the card holds the copy softens at every distance. The unreached bytes cost the
copy its sharpness, not its closure.

[measurement, November 2] **The card realizes the class sheet's pace bit for bit** (`parity-field`, crib13's declaration
at width 32, `K = 2`): under the published clock on the codec's classes (`FIELD_PARITY_CLOCK`, 27 of 44 classes at 0,
each read by its byte), 5 sections equal (faces, covector, learner, held rows, peaks, open return; the rates moving
from the first deposit, `κ` from 0 to 1.010; the withheld section not reached inside the 180 s guard); at the founding,
5 sections and the withheld section equal; with every rate drawn far (`FIELD_PARITY_PACE=8`, `κ` 0.51 to 1.49), 3
sections and the withheld section equal, the run whole. Receipt: `_receipts/law16/parity_class.txt`.

[measurement, November 2] **The coupling reads on the card under the published clock** (`witness-field`, the crib codec
and declaration at `K = 3`, the 515 held operand-digit fronts; the readers transported by the clock's own distances
read on the crib's 4,096 training problems: the anchor's shift is 5 ticks on all 4,096; the comb's one tick in the
host's sense; `FIELD_WITNESS_CLOCK=published`, 8.8 s):

| read | result |
|---|---|
| the witness at `T = 16` | faces 277 of 515, code 2.826 bits (the digit clock's witness: 447, 0.742) |
| (i) the clock's descent | not read: the clock is located by loop closure, not descended |
| (ii) the clock kept, the founding's readers: the readers' descent | head 3 **+0.043**, head 0 +0.008 (under the digit clock: +0.160, −0.0001) |
| (iii) a keyed `2^(−10)` step on the clock and readers | code 36.3 bits; the descent's cosine with the way back +0.034 |
| (iv) `log₂ T`'s descent at the witness with `T = 4` | head 3 raises both (class +1.6·10^14, listener +2.7·10^15); head 0's class lowers (−3.9·10^11), its listener raises (+1.5·10^11) |
| (iv) at the founding | zero at every head and kind |

Under the located clock the readers' descent still points toward the copy on both heads, weaker on head 3 than under
the digit clock (the copy stands 5 ticks further, so its readers' covector is softer, §16.12); the temperature rises
at the copy's head and is silent at the founding, coupled to the rows as before; the basin is still narrow. Receipt:
`_receipts/law16/witness_card_published.txt`.

### 16.17 The diff read against itself

[agent-inferred, November 2] Read adversarially before the run:
- **The card's row carrier.** A contact row is carried on at most twenty limbs (1,280 bits); at the witness's
  temperature of 127 a row's exponents span past it and the card refuses (at 32 a 128-bit sum overflows; at 16 it
  reads). The host's bound is `row_bits`, about 4,100 bits at that temperature. A run's declaration states it: a
  learned temperature that outgrows the card's carrier mid-run refuses with its site and lap, reported, never
  clipped. crib13's largest learned temperatures were 3.91 (class) and 1.28 (listener), under the 32 where the card's
  first carrier refuses. Refusal is not the end state: the carrier widens at a declared crossing (§16.12).
- **The skin's cost.** Off the plain pace a pair's skin is a series read through the exponential's face, one 128-bit
  division a pair and mode: the parity's card time rose about 1.5 times at width 32.
- **The founding's readout at zero** keeps every chart's and pace's covector at zero until the readout moves (§16.9).
- **The paced certificate** reads the faces' l1 bound `2^31` in place of the faces, the same on both realizations.
- **The readings on context parts** are mis-clocked under a digit clock; `FIELD_HELD` keeps them, labelled, and the
  operand rows are read at fronts (`FIELD_PEAKS_OPERAND`).

### 16.18 Failures this could repeat

- An authored routine standing in for learning: the witness is set by hand in tests.rs only; the field names no
  digit, and the digit clock is a material row the deposition moves.
- Text run on its codec's grain as the exception: the clock is the navigator's own; in sound it would tick at
  onsets, in images at edges, in motor at a gait's phase.
- A located cause carried unrepaired: the acceptance no longer reads the mis-clocked context parts (it reads
  fronts); the context read stays in the receipts, labelled with its mis-clock.
- A refusal answered with a larger limit: `K = 3` follows from the law of §16.3, not from a raised budget.
- Bits read as progress, a proxy counted for the release: the witness first passed on its rows (93 of 93) while
  its released bytes failed (33 of 93); its acceptance is now the released byte at every operand front, the code and
  the sibling (§16.11), and the run waits on the temperature the faces need (§16.12), not on the rows.

Owed to #410: the clock is additive over the strand's concatenation, `τ(uv) = τ(u) + τ(v)` shifted, a homomorphism to
the circle (`U = ζ^τ`, `U(a + b) = U(a) U(b)`), and the contact through it depends only on `τ(j) − τ(i)`
(`Re(conj(U_i w_i) U_j w_j) = Re(conj(w_i) w_j ζ^(τ_j − τ_i))`).
