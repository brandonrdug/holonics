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


## 15. Faces are kept whole: a site carries its moment, each mode keeps its own row, a read leaves its echo out, and the release's clock is read

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

### 15.2 Each mode keeps its own face, its own row and its own hold

The contact summed the modes' faces into one number a pair; one weight carried every mode's value; the
row had one denominator; §14.2's hold was the minimum over the class's modes. Each is a reading
collapsed into one number. Measured on the build (§14.9's fixtures): with the minimum hold the cue
fixture coded 2.12 bits, 0.16 without it. One mode at its cone throttled every mode of the pair, and
at the founding, where words stand at random phases, some mode nearly always sits near its cone, so far
copies were never weighed and never learned.

```text
contact  z_ij,m = 2^(−β_i) D_m(|i−j|) Re(conj(w̃_im) w̃_jm) − ⌊log₂ |i−j|⌋       per mode
row      y_i,m = conj(U_im) Σ_a 2^a N_a,m / Σ_a 2^a M_a,m                        §14.11, a row a mode
hold     a far term of mode m carries λ_im λ_jm, its own distance from its own cone
address  a site's class membership is split across each address mode's nearest cone, ½(1 + λ_l) on
         its shell and ½(1 − λ_l) across; a far pair is weighed through c by √(μ_i(c) μ_j(c))
```

- The row is a face: a matrix over the mode and the power of two, the binary places read as its
  coordinates. It crosses into the site's state once a mode, at the declared crossing, its remainder
  carried.
- A mode locked on a plate carries its source far while a bridge mode of the same pair stays near;
  no mode throttles another.
- The address stays the sparse one (`3^b` classes), and the far weight stays continuous across every
  seam (cause 5's repair, now without the throttle): the membership is a partition of unity, and two
  equal words meet at full weight wherever they stand (`Σ_c √(μ(c) μ(c)) = 1`).
- Cost: the pairs met are unchanged; the exponentials are multiplied by the modes a head.

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
- **Text as the exception.** The moment, the rows by mode, the cavity and the clock hold for any strand;
  no numeral is named inside the field.
- **A located cause carried unrepaired.** The units' spelling cause is repaired by spans read at their
  boundaries, not avoided by bytes.
- **A refusal answered with a larger limit.** The rows by mode multiply the exponentials by the modes a
  head; the lap is measured before launch and its deadline fixed from that.

Owners `hnn::tower::field`, `field.cu`, `examples/solenoidal_alpha/complete_language/field_train.rs`
and `tools/gsm8k_variants.py`, with their atlas rows. Owed to #410: the span's face as the difference of
boundary moments (from `moment_closed_form`), the per-mode row's equality with the exact normalized
exponential, and the cavity's removal of the synchronous two-cycle.
