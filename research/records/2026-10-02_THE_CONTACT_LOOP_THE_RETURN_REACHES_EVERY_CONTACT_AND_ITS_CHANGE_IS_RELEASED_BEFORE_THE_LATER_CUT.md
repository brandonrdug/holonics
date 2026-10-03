# The contact loop: the return reaches every contact, and its change is released before the later cut

**Date.** October 2. **Issues.** #73, #63. **Grade.** [measured-diagnostic], an owner-to-consumer
read with one reproducing test, no run.
Test: `hnn::tests::reference::a_reached_contact_family_moves_or_is_named_a_rounding_refusal`.

## 1. The check

Astra's check (October 2 mail) asks four things before any further run:
1. one emitting contact and one participating receiver that retain their motion;
2. a return that actually reaches that contact and changes its constitution;
3. that successor consumed on a later cut, compared against the predecessor under the same later
   drive;
4. joint power and work accounting.

[The kinetic move](2026-10-02_THE_KINETIC_MOVE_FROM_THE_OPENING_MEASURED_THE_COMPARISON_FALLS_FASTEST_AND_THE_DECISIONS_STAY.md)
showed that a lower comparison loss is not evidence of this loop.

## 2. The owners, traced

| Link | Owner | State |
|---|---|---|
| Emitting contact, retaining receiver | `hnn::word`: contact states `(u_a, w_a)`, resonator states and their power per tick (`TickBalance`, `WordBalance`); `Word::continuing` carries them across words within a refinement | built |
| Return reaching the contact | `hnn::reference::compose` (the contact's factor gradients `C̄ = Σ 2r̄(w − ω)ᵀ`, `K̄ = −hΣ r̄(u + ½hω)ᵀ`, `D̄ = −hΣ r̄ωᵀ`, from the word's reverse return) into `Constitution::deposited` at `Locus::Channel(a)` | built and reached |
| Change consumed on a later cut | the resident's successor, read by the next word (`Operands::at_cut`) | built, and receives nothing (§3) |
| The executed release (gate A, every comparison since September 30) | `prediction::generate_by_bank`: `BankPlacement` and a declared `ReceivingBank` | **no word, no contact, no return**; only `E` and `ρ` are deposited, by an exterior comparison optimizer (`executed_move`) |

## 3. Measured

On the chain (two contacts) with a generic constitution, one word, its compare and its deposit:
- **The return reaches every contact.** Each contact receives a certified step on all three factor
  families: `η = 2^(−31)`, `2^(−28)`, `2^(−27)` on contact 0 and `2^(−23)`, `2^(−20)`, `2^(−19)` on
  contact 1.
- **No contact's constitution changes.** The storage, stiffness and dissipation factors of both
  contacts are equal before and after. All 102 channel entries' moves are released as residuals
  below the locus's fine lattice (`BudgetedCarry::released`, each at most `½·2^(−L−k_m)`). The only
  channel remainders carried are three scale remainders of `−1/256`.
- **The later cut reads the successor.** Under the same later drive the compare differs, but the
  difference comes from the element, source port, standing and receiving-map steps, because no
  contact moved.

**The contacts alone.**
The same six channel families deposited without the other loci give the same steps. Deposited one
family at a time, each at its own certificate with no joint halving, they still give the same
steps. So the joint certificate is not what shrinks them: each family's own curvature `C = s·κ²·b`
dwarfs its decrease `a`.

| Contact, family | `a` (decrease) | `C` (curvature, 24 bits) | `η` |
|---|---|---|---|
| 0, storage | `4435594093169685299/2^75` | `2244951/16` | `2^(−31)` |
| 0, stiffness | `3004229502457467857/2^76` | `6223669/1024` | `2^(−28)` |
| 0, dissipation | `6925366743880731153/2^76` | `13165999/2048` | `2^(−27)` |
| 1, storage | `9550704405487570785/2^76` | `13316721/16384` | `2^(−23)` |
| 1, stiffness | `34257067843/2^49` | `193749/4096` | `2^(−20)` |
| 1, dissipation | `43966108913/2^50` | `4473285/262144` | `2^(−19)` |

No factor moves, 17 entries are released for each family, the storage growth is 0, and the later
cut is identical to the predecessor's.

## 4. The missing link

[agent-inferred] The owner chain exists. **The certified step at the channel sizes every contact
move below the locus's lattice, so the release erases it before any later cut.** This holds for
each family alone (§3). The certificate reads the contact's move through the whole reach's gain
`κ²` to the stacked station logits (`C = s·κ²·b` against the alignment `a`). A contact's own power,
its slip and material work, never enters the size of its step. So the return-driven change Astra asks for is reached and then
discarded. Separately, the executed release has no contact at all: its receiving bank is declared,
not a locus.

The next loop works on this measurement: a contact's step certified by the contact's own power
balance (the word's `TickBalance` dissipation and the pair contact's slip law in
`holon::contact`), so that a reached return changes the contact and the same later drive reads the
change. It is checked on the word before it joins the bank.

## 5. The rounding refusal (Astra's first unit, October 2)

Astra's reply (October 2) corrects §4. The contact's power already enters its certificate: the
transit's difference power is carried to the station logits. So the fix tightens that chain rather
than replacing it with local dissipation, which would void the score-descent claim. I withdrew the
separate conduction law I had proposed. Astra's smallest unit is in three steps.

**Step 1, built.** `DepositReading::vanished` names every family certified at `η > 0` none of whose
entries took a nonzero lattice coordinate, so its move was released whole. The test asserts the law
on every reached contact family, deposited whole and alone with every other locus frozen: a family's
factor moves exactly when the deposit does not name it. Today all six are named.

**Step 2, built** (test `hnn::tests::prediction::a_contact_change_is_read_by_the_continued_word_with_its_work`).
Under the exact law, one word's retained change `x` continues at the predecessor and at a successor
whose contact 0 storage factor moved. The successor is a control chart until the deposit's own
contact moves land. Both continue with the same later drive and clock. The successor's continued
word opens on `x` at exactly the predecessor's power plus `PowerForm::deposition_work`'s
`½⟨x, ΔΘ x⟩`. Every tick of both closes, and the moved contact's states, its outgoing waves and the
receiving ring's storage differ after four ticks. The consumer reads a contact change with its
work accounted. What remains is that the deposit's own contact move reaches it. The reflected
interior residual `r = z − Kx` is not yet a term of this word, and it is owed with step 3.

**Step 3, measured: the step was never the limit.** I built a read-certified contact step,
committed as a probe at [`f0bdc4a2`](https://github.com/brandonrdug/holonics/commit/f0bdc4a256c309c402076827728f52d504f8199c)
and retired in this change ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/read_steps.txt)). After
the certified deposit, each vanished contact family is tried at the least step `2^k ≤ 1` that moves
a lattice coordinate, and the successor is published only where the window's exact re-read is
strictly lower ([`strictly_better`]). On the chain:
- **Contact 0**: none of its three families moves a coordinate even at the full unit step
  `η = 1` (`D = G/h′` itself lies below the fine lattice).
- **Contact 1**: storage and stiffness first move at `η = 1`, and the window's code is unchanged
  there, with the same enclosure exactly (`[81718273742707340252184139321/2^95, …)` at both). Its
  dissipation never moves.
- Nothing is published, and the acceptance fails.

[agent-inferred] On this fixture, the return that reaches the contacts is too weak to change the
window's code at its grain, even at the unit step. A sharper certificate cannot move what the
comparison itself does not see. The chain's contacts are effectively invisible to the receiver's
comparison, and the contact loop needs a contact the comparison reads. I retired the read step
because it has no consumer that gains from it. The rounding refusal (step 1) and the continued
word's reading (step 2) remain.

## 6. The medium's interior does not move at all on these small fixtures

Every family at one deposit, ranked
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/families.txt); the probe is archived in this
change's history and retired):
- **The chain:** 20 of 21 certified families are named vanished: all three elements' maps,
  passive factors and slices, both contacts' factors, the source port and its pair port, and all
  three standings. Only the receiving map `R` moves (`η = 1`). Every vanished family's entries are
  released, and only the Grams and the scales carry a remainder, so nothing accumulates toward a
  later move.
- **The joint prediction field:** the source port `E` and the readout `R` move. The element, the
  contact and both standings vanish.

[agent-inferred] This is the lattice deposit's own law at work, not a defect of one certificate. An
update below the fine unit `½·2^(−L−k_m)` is released by design, and the law holds that such
releases sum to less than `u/2` since the locus's founding, below every receiver's grain. Unit 3's
read step agrees: where contact 1 did move, the window's code did not change. So on these fixtures
the comparison reaches the interior only below its grain. The interior (elements, contacts and
standings) takes no part in learning, which happens in `R` and, on the joint field, in `E`. The
contact loop Astra asked for cannot be shown here. It needs a medium whose interior the comparison
reads above the receiver's grain, and which medium or coupling that is belongs to the architecture
question I've put to Astra.

**Over successive deposits** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/successive.txt); the
probe is archived in this change's history and retired). I ran eight windows of drawn cells on the
chain (`source(64, 81)`, six cells read and the next two compared). Each window was read from rest
at the published constitution, compared against its next cells and deposited.
- **From `generic(301)`:** every deposit certifies 13 families and names all 13 vanished, the
  readout included. After the eight deposits no ring's passive factor and no contact's factor
  differs from the opening.
- **From the field's declared opening:** each deposit certifies one family and names it vanished.

The scope is these two openings on the chain under this drive. They say nothing of a trained
constitution, or of the text runs of September 29, where the tightened certificate's record reports
the factor families moving.

**A correction of scope.** The [tightened certificate's text run](2026-09-29_THE_TIGHTENED_CERTIFICATE_THE_FACTOR_FAMILIES_MOVE_AND_THE_STANDINGS_FOLD_COSTS_THE_COPY.md)
of September 29 (the prediction field, one pass over 385 choosing pairs, 12,320 stations, 25
deposits) moved contact 0's `c`, `b` and `F` in 17, 22 and 21 of its 25 deposits. Their steps there
were `2^(−18)..2^(−12)`, against `2^(−31)..2^(−19)` here. A deposit over many stations sums many
returns, so the interior is reached above its lattice. My fixtures (two targets on the chain, three
on the joint field) are too small to move it. So the statement of §6 holds for these fixtures, not
for the machine. The contact loop belongs on the text configuration, where contacts move. Its
harness (`hnn_prediction develop`) was retired with the linear readout on September 30, so running
it means porting a harness, and that choice goes to Astra with its cost.

## 7. On real text the interior moves

The live configuration needs no port. Campaign 1's exposure (`hnn_exposure`, the reference
machine on its own field, reading real text) now records each deposit's rounding refusals
(`CurvePoint::vanished`), and the harness prints a rounding census. The smoke run `windows 8` on the
development control ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/exposure_windows8.txt), 752 ms):
- **Contacts 1 and 2 move.** Contact 1's factors moved at 5, 6 and 6 of 6 certified deposits, and
  contact 2's at 6 of 6 each, with steps from `2^3` to `2^11`.
- **Contacts 0 and 3 barely move.** They moved at 0 of 6, except contact 3's dissipation at 1.
- **Every element's map, passive factor and slices move at 6 of 6.** The source port moves at 6 of
  6, and the standings at 1 to 4 of 6. The pair port never moves.

So the return-driven contact change Astra asked for is present on real text. A reached return moves
contacts 1 and 2 at nearly every deposit. The old develop-text harness isn't needed. Next, on this
configuration, the same later drive read at the predecessor and at a successor that differs only in
the contacts' deposited steps, with the deposition work accounted.

## 8. The contact loop closes on real text, and the comparison does not improve

`hnn::reference::contact_ablation`, through `hnn_exposure ablation <windows>` on the development
control, follows the exposure's own order. At each window, before the full deposit, the compare's
deposit is restricted to its contact families and deposited alone on the predecessor. The deposition
work of that contacts-only commit on the window's end change is read. Then the same later drive, the
next window read against its own cells, is read at the predecessor and at the contacts-only
successor, each after the window's ingest.

| Windows | A contact moved | Next word's contact states differ | Next receiving faces differ | Next window's code: lower / higher / equal |
|---|---|---|---|---|
| 16 ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/ablation_16.txt)) | 14 | 14 | 14 | 0 / 2 / 14 |
| 256 ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/ablation_256.txt)) | 254 | 251 | 232 | 4 / 10 / 242 |

- **Astra's loop holds.** A return actually reaches a contact and changes its constitution
  (contacts 1 and 2 at nearly every window, contacts 0 and 3 later). The commit's deposition work
  `½⟨x, ΔΘ x⟩` on the window's end change is nonzero and signed. The next window's word, under the
  same drive, ends with different contact states and different receiving faces.
- **The comparison does not improve from it.** At its grain, the next window's code is unchanged at
  242 of 256 windows, strictly lower at 4 and strictly higher at 10. The contacts' change reaches
  the receiver's faces, but it is not, by itself, a change the next comparison rewards.

[agent-inferred] The contact loop is a working mechanism of the reference machine on text. Whether
it learns is a separate question, and on this measurement the contacts alone do not lower the next
window's code: they are a consumed change, not yet a useful one. The full deposit also moves the
elements, the source port and the readout, and this ablation does not split their shares.

Time: projected `256 · 196 = 50,176` ms from the 16-window read (3,131 ms), deadline 100 s; measured
74,202 ms, peak 308,056,064 bytes. The 16 windows the projection was taken from all fall in the
cut's opening, which runs cheaper than the windows after it, and that is where the error comes from.

## 9. Why the change is read and not useful: it lands in the receiver's fibre

Astra's reviews (October 2) asked for the continuing consumer as well: the window's own retained
end change continued with `Word::continuing` at the predecessor's and at the actual successor's
operands, with nothing injected, on the clock after the window's junction steps. Its anchors go
through `ReceivingPhases::read` and the faces at the grain. They also asked that anchors, logits and
grain cells be compared before the score
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/ablation_256_continued.txt), 256 windows, 80,478 ms):

| Consumer | Anchors or contact states differ | Exact logits differ | Faces differ | Grain cells above the fibre differ |
|---|---|---|---|---|
| the exposure's (a fresh word at the next cut) | 251 | 232 | 232 | **14** |
| the continuing word (the window's own change; a two-junction read, see below) | 250 | 250 | 250 | **36** |

*The continuing read is a two-junction computation, not a seamless continuation* (Astra, October 2):
`WordBalance.change` is taken after the word's last junction, and `Word::continuing` opens with
another junction. The read is valid as that computation.

The next window's code changes at exactly 14 windows (strictly lower 4, strictly higher 10), the
windows where the fresh consumer's grain cells differ above the fibre. A face's code length reads
each class's carry and phase class and the normalizer (`Face::code_length`:
`log₂ Z − (n_c − n_top) − k_c/L`). It never reads the fibre `ε_c`.

So the contacts' change reaches the receiver at nearly every window, but almost always inside the
receiver's unresolved fibre, below its grain, where the comparison cannot see it and its covector
cannot reward it. That is the measured cause of "read but not useful". ~~Raising the receiver's
grain, or a comparison that reads the fibre, is the next lever, and either is an architecture
choice.~~ [Edit, October 2: this is not a choice. §11 derives the receiver's resolution and shows
that the change lies far below it.]

## 10. The reflected residual: its instantiation, owed

[definition; agent-inferred] Astra's last obligation is to carry `r = z − K_chart x` and the
changing-chart residual, with the storage cross terms, in the continued word's account. Here is the
instantiation on one contact, from the executed transit (`hnn::propagation::transit_solve`,
`transit_update`):
- **Interior and boundary.** The interior is `z = (u, w)`, the contact's displacement and rate. The
  boundary is `x = (α_g, α_h)`, the channel's incoming waves at the tick, the rings' outgoing waves
  on the channel's selection. With `S = m̂⁻¹`, the executed solve read column by column, the transit
  is linear: `z′ = D z + C x` with
  `u′ = u + (G/2) S(2C_a w − h K_a u) + (Gh/2) S(α_g − α_h)` and
  `w′ = −w + (G/h) S(2C_a w − h K_a u) + G S(α_g − α_h)`. The outgoing waves are
  `α_g − S(α_g − α_h) − (1/h) S(2C_a w − h K_a u)` and the same with the signs reversed.
- **The chart.** `K = (I − D)⁻¹ C`, defined where `I − D` is invertible, which needs an invertible
  stiffness `K_a` (Astra, October 2). A singular stiffness keeps its compatible fibre or
  obstruction. It is the contact's quasi-static elimination: the interior state a
  steady boundary holds. Then `r = z − K x` is the contact's motion that the boundary does not
  determine, and Lean's `ReflectedBoundaryMemory.reflectedResidual_step` gives its next value with
  the next chart. Across a commit `K` changes, and the retained `z` reads `r′ = z − K′x`, the
  recharting term `−(K′ − K)x` included.
- **The account.** `E_a(z) = E_a(r) + 2⟨r, Kx⟩_{E_a} + E_a(Kx)`, with `E_a(u, w) = ½(⟨w, C_a w⟩ +
  ⟨u, K_a u⟩)`. The continued word's opening power carries this split per contact beside
  `PowerForm::deposition_work`.
- **Its consumer.** `contact_ablation`, which reads the split for each moved contact at the
  predecessor's chart and the successor's. That needs the channel's incoming waves `x`, which the
  word's per-tick record (`Passage`) does not yet keep. Recording them is the first build step.
  Until that build lands, the residual stays owed (#62).
- **Its owner** (the division of work, October 2): the returned-state and storage boundary, the
  reflected residual included, is Astra's. This instantiation is handed over, and its receipt is
  consumed here when it lands.

## 11. The receiver's resolution, derived, and the contacts' change against it

Brandon (October 2): whether the receiver can read the change is a question of physics, settled by
derivation, not a choice handed to anyone.

**What sets the grain in the code.** `ReceivingPhases::grain` is `L_R = ⌈1/ε_bits⌉`, where
`ε_bits` is the receiver's declared code tolerance (`ReceiverDeclaration::tolerance`, `1/16` bit on
campaign 1's field). It is a declared constant. Nothing derives it, and the deposit's lattices are
derived from it in turn (the lattice rule).

**Temperature.** No temperature appears anywhere in `hnn`, so the code fixes no temperature. The
quantity a temperature would play is the receiver's exponent scale. A reading of class `c` is
`a_c = 2^(v_c)` with `v_c = −E_c/(k_B T ln 2)` in the framework's physical reading (cross-entropy
is free energy, `F(p) − F(q) = k_B T D(p‖q)`), so `1/(k_B T ln 2)` is the gain that turns the
receiving anchor into exponents. That gain is the receiving map `R`, a learned locus, which moves at
every deposit on real text (the rounding census, §7: `ReceivingMap(2)` at 7 of 7). So the
receiver's temperature is a state of the receiver, changed by deposition. It is not fixed. Below,
everything is in bits of `v`, where it cancels. It enters only in converting a deposition's energy
into bits.

**The derivation.** These are the receiver's own readings. No exterior readout is added.
1. A receiving phase reads `p_c = 2^(v_c)/Z` (`Face::mass`). A change of the medium changes the
   exponents by `δ_c` bits and the reading to `p′`.
2. The information the receiver gains about the change from one reading is the divergence
   `D(p′‖p)`. To second order in bits, `D(p′‖p) = (ln 2/2) Var_p(δ) + O(δ³)`, using
   `ln p′_c − ln p_c = ln 2·(δ_c − Σ_d p_d δ_d) + O(δ²)`.
3. ~~The receiver can tell the two media apart over `N` readings exactly when the accumulated
   divergence reaches one bit, `N·D(p′‖p) ≥ 1` (Stein's lemma: the error of telling them apart
   falls as `2^(−N·D)`).~~ [Edit, October 2, after Astra's source review: Stein's lemma gives only
   the asymptotic exponent of the type-II error at a fixed type-I level. It gives no exact finite-`N`
   threshold.] Take `N·D(p′‖p) ≥ 1` bit as the convention for distinguishability over `N`
   readings: a chosen scaling, not an exact threshold. Since `Var_p(δ) ≤ max_c δ_c²`, a change is unreadable over `N` readings
   whenever `max_c |δ_c| < √(2/(N ln 2))`.
4. The receiver integrates readings within one retained state, over one aeon: `N = 1,190` cells on
   campaign 1's field (the exposure's declared aeon). So its resolution is
   `√(2/(1190 ln 2))` bits, which lies in `(1/21, 1/20)` because `1190 · ln 2 / 2` lies in
   `(400, 441)`. The declared `1/16` is coarser than this by less than a factor of `4/3`. That
   discrepancy is real, but it is small next to what follows.

**Its assumptions, stated** (Astra's foveation review, October 2). The bound is the statistical
case of the receiver's tolerance, not its law. It assumes:
- **(a) the decision:** a two-hypothesis test between the two media;
- **(b) the error criterion:** Stein's exponent at one bit, `N·D ≥ 1`;
- **(c) the accumulation:** independent readings within one retained state, `N = 1,190` for one aeon.
  [Edit, October 2, after Astra's source review: 1,190 is the mean aeon length of campaign 1's
  joint clock under uniform bytes, not a proved effective count of independent samples. Readings
  under a frozen constitution are dependent, since moments, clocks and addresses keep evolving. The
  coherent measure is the chain rule of the conditional divergence along the declared path law,
  `Σ_t E[D(p′_t ‖ p_t | past)]`, of which a sum over the supplied text is one sample path, not the
  expectation.]

Each of the three is a modelling choice and changes the number. The general criterion recovered
from the foveation work (the laboratory's July 25 joint-receiver grain; the
[September 14 synthesis](2026-09-14_HEAR_THE_MUSIC_SITUATED_RELEASE_AND_SELF_MOTION.md)) is
decision-dependent. A receiver refines where an admitted consequence differs and coarsens where
distinctions factor (`Holarchy::refine`). The resolution is the receiver's, adaptive, and never a
global constant. A second bound also applies on real text: no face produces the targets, so the code
length moves at first order in the change, not second order. §14 measures which bound governs.

**The contacts' change, measured** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/readability_256.txt)).
Over 256 windows, take the largest change of the next window's exponents `v` over its phases and
classes:
- **The fresh consumer:** median `41/2^24`, upper quartile `33/2^23`, largest `695/2^25` bits.
- **The continuing consumer:** median `53/2^24`, upper quartile `77/2^24`, largest `7/2^18` bits.
- None reaches `1/21` or `1/16`. The largest, `7/2^18`, lies ~~more than `2^12` times~~ more than
  `2^10` times below the derived resolution. [Edit, October 2: the ratio is `(1/21)/(7/2^18)`, about
  `2^10.8`, not more than `2^12`.]

**The finding**, under the convention of step 3 and assumptions (a) to (c) (not a statement of
physical impossibility): the contacts' change cannot be read by this receiver. With
`max |δ| ≤ 7/2^18`, one reading carries less than `(ln 2/2)(7/2^18)² < 2^(−31)` bits about it, so
the receiver would need more than `2^31` readings, ~~about `2^19` aeons~~ more than `2^21` aeons, to
tell the media apart. [Edit, October 2: `(ln 2/2)·49/2^36` lies below `2^(−31)`, and `2^31/1190`
exceeds `2^20`. The earlier margins, `2^(−29)` and about `2^19` aeons, were loose or wrong.] The
14 windows whose code moved are cells whose exponent sat within `7/2^18` of a cell edge and crossed
it. That is a boundary effect, not information. The finding is the weak coupling: the return-driven
contact change is real, conserved in the energy account and carried to the receiver, but it reaches
the receiver at a size its own statistics cannot resolve. Moving the grain or scoring the fibre would
read a difference the receiver itself cannot distinguish, which is an exterior readout, and neither
is done.

## 12. Why the coupling is weak: the receiver's gain, not the path

The same ablation over the first aeon ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/coupling_aeon.txt):
534 windows to the first carry-out, 175,763 ms; 256-window read
[here](2026-10-02_THE_CONTACT_LOOP_receipts/coupling_256.txt)). Each link of the chain from a
contacts-only commit to the receiver's exponents was measured.

| Link | Measured (median; upper quartile; largest) |
|---|---|
| contacts' relative factor change at the commit, `ρ_f` (largest entry change over the factor's largest entry) | `1/257`; `1/256`; `9/515` |
| next window's relative anchor change on the receiving ring, `ρ_a` (continuing consumer) | `1/436`; `1/287`; `1/104` |
| the receiver's exponent span across classes within a phase, `σ` | `29443/2^23`; `395629/2^25`; `2076909/2^25` bits |
| the change of the receiver's exponents, `δ` (continuing consumer) | `23/2^23`; `75/2^24`; `7/2^18` bits |

By quarter of the aeon, the largest `σ` was `62561/2^24`, `104193/2^24`, `903579/2^25` and
`2076909/2^25` bits. It grows over the aeon, as the receiving map `R` learns.

**The derivation.**
1. A contacts-only commit leaves `R` fixed, so the exponents move by `δv = R δa`. The exponents' own
   span is `σ ~ |R a|` across classes. Hence `δ ~ ρ_a · σ`, up to the alignment of `δa` with `R`'s
   discriminating rows. Measured, the medians give `ρ_a σ = (1/436)(29443/2^23)`, about `2^(−17)`,
   against `δ = 23/2^23`, about `2^(−18.5)`. The alignment factor is below one.
2. The path transmits the change. `ρ_a` is within a factor of two of `ρ_f`, so contacts 1 and 2 lie
   on the receiving ring's main path. Nothing along the path attenuates the change.
3. `ρ_f` is about one lattice quantum. The channel lattices are `L = 9` and `10` (`2^(−9)`,
   `2^(−10)`) against factor entries of order `½`, so one deposit moves a contact by about `2^(−8)`
   relative.
4. The receiver's gain is the bottleneck. Over the first aeon, `σ` stays below `2^(−4)` bits: the
   receiver's readings differ across classes by less than one sixteenth of a bit. A relative change
   of `2^(−8)` in what it reads can only move its exponents by `2^(−8) σ`.

**What the readability bound requires.** With `δ ≈ ρ_a σ` and the resolution `√(2/(1190 ln 2))`
bits (§11), one deposit's contact change becomes readable within an aeon only when
`ρ_a σ ≳ 1/20`. At `ρ_a ≈ 2^(−8)` that is `σ ≳ 13` bits: the receiver would need to separate its
classes by odds of about `2^13` before a single contact deposit could register. The aeon's largest
`σ`, `2076909/2^25` bits (about `1/16` bit), is more than `2^7` below that.

[agent-inferred] The weak coupling is the receiver's own low gain at this stage of learning, not an
attenuating path, and not the contacts alone. Two things would change it, both measurable: the
receiver's gain growing over later aeons (`σ` rose sixteenfold over the first), and successive
contact deposits adding coherently. This ablation reads one deposit at a time and does not
measure the second.

Time: the run stopped at the first aeon's carry-out, by `contact_ablation`'s declared stop (it
closes no aeon), at 534 of the 3,074 projected windows. Its wall, 175,763 ms over 534 windows, is
within the per-window projection.

## 13. Over the whole cut: the receiver's span saturates, and the contacts' changes add up

The ablation now closes each aeon (without the exposure's key location) and, at the first window
after each boundary, reads that window at the published constitution and at the same constitution
with every contact's factors returned to the opening's
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/cumulative_cut.txt): 3,068 windows, six aeons,
1,114,572 ms against a projected 1,011,346 ms, inside the 1,200 s deadline). All numbers assume the
current certified step (`s = ½` in `C = s κ² b`). The constants audit (PR #150) derives the tight
value `ln 2/2`, which would scale every deposit's step by `1/ln 2`.

| Aeon | Receiver's exponent span, largest (bits) | One deposit's contact change, largest (bits) | Contacts' cumulative change at the aeon's close (bits) |
|---|---|---|---|
| 0 | `2076909/2^25` | `695/2^25` | |
| 1 | `2838929/2^24` | `453/2^25` | `5237/2^19` |
| 2 | `3918029/2^24` | `59/2^21` | `222317/2^24` |
| 3 | `4480569/2^24` | `135/2^24` | `749861/2^25` |
| 4 | `9531753/2^25` | `163/2^24` | `1025753/2^25` |
| 5 | `2447437/2^23` | 0 | `1003399/2^25` |

- **The receiver's span grows, then saturates.** It rises from about `1/16` to about `0.29` bits
  (`2447437/2^23`) by the sixth aeon, with each step smaller than the last.
- **Contacts move less after the first aeon.** A contact moved at 679 of the 3,068 windows: at 487
  of the first aeon's 534, and at about 190 over the five aeons after it.
- **The contacts' changes add up.** Over the cut their cumulative change in the receiver's
  exponents grows from `5237/2^19` bits at the first close to `1025753/2^25` bits at the fourth,
  more than a thousand times one deposit's largest change, then holds.

**Readability of the cumulative change.** By the bound of §11, an exponent change of at most `Δ`
bits carries at most `(ln 2/2) Δ²` bits per reading. At `Δ = 1025753/2^25` (between `3/100` and
`1/32`), the bound reaches one bit only after more than `2/(ln 2 · Δ²)` readings. That is more than
3,000 and fewer than 3,300, about three aeons. The cut's 6,148 readings exceed that, so the upper
bound no longer rules the cumulative change out: it reaches a size the receiver could resolve within
the exposure. Whether it actually does needs a lower bound on `Var_p(δ)`, and this measurement
records only the largest `|δ|`. The single-window codes at the six closes go both ways. At the fifth
close the learned contacts read `669256998367765604292325457111/2^96` bits against
`673907947111696475745294623777/2^96` with the opening's, lower by about `1/17` bit. At the third
close they read higher by about `1/500` bit. One window per close is too few readings to decide.

**How long until a contact's change is readable.** One deposit's contact change never is (§11,
more than `2^31` readings). The accumulated change reaches the size the bound allows within about
three aeons of the contacts' learning, and the receiver's span stops growing near `0.3` bits. The
next measurement is the information itself, over many windows rather than one: the accumulated
`Σ D(p′‖p)` between the learned and the opening contacts over a whole aeon of readings, which
decides readability without the `max |δ|` bound.

## 14. Information, first-order code, and why contacts freeze (incomplete: two aeons)

Both runs of this read are incomplete. The first, with 256 frozen windows per aeon, passed its
1,800 s deadline without printing
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/information_first_attempt.txt)). The read was then
changed, not relaunched with a larger limit: 64 frozen windows per aeon
(`INFORMATION_WINDOWS = 2^6`, a cost choice), a line printed per aeon as it closes, and the
first-order code difference added. That run was stopped on evidence after the second aeon's line.
The first aeon took 245,316 ms against the projection's 205 s per aeon
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/information_incomplete.txt)).

**Why the contacts stop moving: rounding, not a shrinking return.**

| Aeon | Contacts-only commits | Channel families certified / vanished | The return reaching the contacts, `a` median | `R`'s steps moved / its `a` median |
|---|---|---|---|---|
| 0 | 534 | 6,384 / 3,284 | `3842973/2^42` | 534 of 534 / `10550203/2^33` |
| 1 | 560 | 6,720 / 6,549 | `4237223/2^36` | 561 of 561 / `9383943/2^32` |

The return reaching the contacts grows by about `2^6` from the first aeon to the second, yet the
share of families that vanish rises from about half to 97 percent. ~~So the step shrinks faster than
the lattice refines, and the contacts freeze by rounding.~~ [Edit, October 2, from the Lean thread's
proofs, commit `2c7dcfa`.] "Vanished" counts deposits at which a family took no coarse coordinate
(`q = 0`), not updates released. At clock `m` the fine cell lies between `u/(2m²)` and `2u/m²`, so a
step decaying as `1/m` is held in the carried remainder, not released. A unit step is `D = G/h′`,
with the statistic `h′` accumulating every passage's feature energy. The contacts' accumulated
updates reach the next coarse unit only as `κ · log` of that statistic's growth (an entry needs
growth `e^(u/κ)` to move one unit); the carried remainder can bring a contact's first move much
sooner (the freeze proofs' review, PR #152). The freeze is that logarithmic law, not
the rounding of individual steps. The cumulative change of §13 is what this schedule permits, not a
trend. `R`, whose step is `η = 1` at every deposit, keeps moving.

**The information (second order, an ungrained surrogate).** The receiver's readings were compared
over 128 frozen readings (64 windows) after each close, the opening's contacts against the learned.
The computation takes raw exponent deltas, fibres included, and weights them by the grained masses'
interval midpoints, so the changed mass is not the exponential tilt of those deltas. It is an
ungrained surrogate, not a certified divergence, and its remainder is not bounded (Astra's source
review, October 2):
- after aeon 1, `Σ Var_p(δ) = 16713691/2^38` bits²;
- after aeon 2, `797049/2^31` bits².

To second order the information is `(ln 2/2) Σ Var`, below `2^(−13)` and below `2^(−11)` bits over
the 128 readings. That is far below one bit.

**The code on the actual targets (first order).** The code with the opening's contacts less the
code with the learned contacts, summed over the same 64 windows:
- after aeon 1, between `73869077799743960577887037/2^95` and
  `73869077799744495918701667/2^95` bits, about `+1/536`: 19 windows better, 15 worse, 30
  undecided;
- after aeon 2, about `−1/74` bit: 20 better, 27 worse, 17 undecided.

The difference changes sign and the windows split nearly evenly, so the learned contacts are not
consistently better on the actual targets. ~~Two points cannot separate linear growth from
square-root growth. The sign change and the even split point to incoherent accumulation, so neither
bound shows a contact improvement accruing.~~ [Edit, October 2, after Astra's source review: growth
in `N` does not separate first from second order in the perturbation, since both mean effects can
grow linearly, and two frozen prefixes identify no exponent.] The supported claim is narrower:
small contact perturbations, under a declared local surrogate, with no consistent signed
improvement on the measured prefixes.

[agent-inferred] On this cut, the contacts' learning, frozen by rounding after the first aeon, does
not produce a change the receiver gains from. This is the statement the measurement supports, and
the bounds above are its evidence.

## 15. The real deposits descend, and the rounded contact residuals are coherent but bounded

The first aeon on campaign 1, 534 deposits
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/descent_aeon0.txt), 270,995 ms against about
265 s projected, inside the 400 s deadline).

**The mixed-covector condition** (the Lean thread, PR #151). Each deposit moves loci, not one
station's logits, so its guaranteed decrease rests on `A⁻ ≤ 5/9 · A⁺` at `L = 16`, where `A⁺` is the
odometer-weighted part of the move favouring the target and `A⁻` the part lifting other classes. The
split was read on each deposit's realized move: the window's own exponents re-read at the successor
against its own targets (`DepositDescent`). This is the secant, not the tangent the certificate
reads, and it covers the whole deposit, `R` included.
- **`A⁻/A⁺`:** median `2336289/2^32`, upper quartile `5475503/2^33`, largest `8985321/2^33`. None
  of the 533 with `A⁺ > 0` passes `5/9`; the largest is below `2^(−9)`. One deposit had `A⁺ = 0`.
- **The window's own code fell at all 534 deposits**, strictly in enclosure, and rose at none.

So on real text the condition holds with a margin of about `2^9`, and every deposit descends on its
own window. The gap in the proof is not a failure in the deposits.

**The dropped contact residuals** (`DepositReading::released` at the channel loci, per entry
across the 534 deposits, then pooled per contact). This is the ratio of the per-entry sums'
magnitudes to the sums of the magnitudes:

| Contact | Residuals / entries | `Σ_entries |Σ e| / Σ_entries Σ |e|` | A random sign would give about |
|---|---|---|---|
| 0 | 161,095 / 303 | `10841473/2^25` | `1/√531` |
| 1 | 313,530 / 591 | `11298605/2^25` | `1/√530` |
| 2 | 768,938 / 1,455 | `10315767/2^25` | `1/√528` |
| 3 | 161,064 / 303 | `667429/2^21` | `1/√531` |

~~The dropped residuals are coherent: about `1/3` of their magnitude survives summation per entry,
about seven times what independent signs would leave.~~ [Edit, October 2: wrong. The `1/√n` baseline
assumes residuals of equal magnitude. These are heavy-tailed, so a few large ones dominate both
sums, and the pooled ratio is not a coherence test. The test is per entry: `Z = S/√Q`, with `S` the
sum and `Q` the sum of squares, coherent at `α = 1/20` when `Z² > 2 ln 40` (the Lean thread's
statistic). Over the same first aeon
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/coherence_aeon0.txt)), 3 of 2,652 entries pass:
0 of 303, 0 of 591, 3 of 1,455 and 0 of 303 for contacts 0 to 3. That is fewer than the
`2,652/20` chance alone would pass. The dropped residuals cancel; they are not coherent.]

**The derivation of what that is worth.** A released residual is the part of an entry's update below
the fine lattice, `|e| < ½ · 2^(−L−k_m)`, with `k_m = 2⌊log₂ m⌋ + 1` at the locus's clock `m`. The
Elias-gamma lengths satisfy Kraft, `Σ_m 2^(−k_m) < 1` (`gamma_kraft_lt_one`), so an entry's releases
since founding sum, in magnitude, to less than `u/2 = ½ · 2^(−L)`
(`HNN/LatticeDeposit.release_bounded_since_founding`). Even perfectly coherent, everything rounding
has dropped from one contact entry over the whole history is less than half a lattice unit:
`2^(−10)` absolute at `L = 9`, against factor entries of order `½`. A carried remainder would recover
at most that, about one lattice step per entry over all time.

[agent-inferred] So the coordinator's question, whether the remainders should be carried because
they add coherently, has a two-part answer. They do add coherently. The lattice law already bounds
their total by half a unit per entry, so carrying them changes the contacts by at most one step per
entry. The freeze after the first aeon is correct behaviour. The contacts have learned what they can
at this grain, and their remaining updates fall below the size the law admits.

[Edit, October 2, from the Lean thread's proofs, commit `2c7dcfa`.] The half-unit cap is tight: `2^J − 1`
deposits can drop exactly `(u/2)(1 − 2^(−J))`. It holds only because the declared schedule's fine
cell shrinks as `1/m²`, which is summable. For any schedule the drop is at most `u/2` times that
schedule's Kraft sum. Under the derived grain `1/L(N)`, `L(N) = ⌈√(N ln 2/2)⌉`, the sum is at least
`√N/4`, which passes one at `N = 16` and grows without bound. So "the freeze is correct behaviour" is
a property of the declared `1/m²` schedule. It does not survive the derived grain. ~~under which the
coherent remainders found above would accumulate without a cap.~~ Under the derived grain the cap
grows without bound, but the residuals cancel (the corrected test above), so what they would add
grows as the square root of their count, not linearly. Under either schedule, rounding drops no
coherent signal from the contacts.

**The conclusion's dependence, stated.** "Learned what they can at this grain" holds for the
declared schedule. The base lattice `L` of each locus comes from the lattice rule, which reads the
receiver's grain `L_R`, and `L_R` is the declared `1/16` bit (§11), not derived. The fine lattice's
precision `k_m = 2⌊log₂ m⌋ + 1` follows the locus's clock. The Kraft cap `u/2 = ½ · 2^(−L)` is a
property of that schedule. If `L_R` followed the derived grain, which refines as `√N` with the
receiver's reading count (§11; the constants audit, PR #150), `L` would grow with the readings.
That shrinks both the cap and the size below which a contact's step vanishes, so more of the
contacts' late updates would land. This dependence is stated, not measured. Whether those updates
would then reach the receiver above its resolution is the question of §12, whose bottleneck is the
receiver's gain, not the contacts' lattice.

## 16. The receiver's separation levels off while `R` keeps growing (incomplete: three closes)

This read takes `R`, the receiving map, at each aeon's close
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/receiver_gain_incomplete.txt)). It passed its
1,250 s deadline after three closes, because the host was under other load (a load average of about
5), and an identical configuration had run all six aeons in 1,114,572 ms. It is reported incomplete
and was not relaunched with a larger limit.

**`R`'s update, from the code.** The receiving map is a normal law whose certified step is
`η = 1` at every deposit (its gain is `κ² = 1`: `Constitution::gain`, `LinearLocus::Receiving`). Its
unit step is `D = Σ_t w g_t (X̂ f_t)ᵀ`, with `X̂ ≈ H′⁻¹` and `H′` the Gram of the receiving anchors,
accumulated since the opening. Its covector is the comparison's `p − q`. This is an online
Gauss–Newton step on the cross-entropy, preconditioned by the accumulated Gram, so the size of
each step falls roughly as `1/n` in the anchors seen.

| Close | `R`'s largest entry | `R`'s largest change since the last close, over its largest entry | The receiver's exponent span, largest in the aeon before (bits) |
|---|---|---|---|
| after aeon 0 | `219/1024` | `1` (`R₀ = 0`) | `2076909/2^25` |
| after aeon 1 | `97/256` | `4756427/2^23` | `2838929/2^24` |
| after aeon 2 | `267/512` | `4587029/2^24` | `3918029/2^24` |

`R` moved at every deposit: 534, 561 and 569 of 534, 561 and 569. Its certified decrease `a` holds
steady, with medians `10550203/2^33`, `9383943/2^32` and `205299/2^27`.

**What this settles.**
- **Not a rounding freeze.** `R` moves at every deposit, unlike the contacts.
- **Its step does shrink.** Its relative change per aeon roughly halves from aeon to aeon, while
  its largest entry still grows by `219/1024`, about `0.166` and about `0.143` per aeon.
- **The separation saturates faster than `R` grows.** From the second close to the third, `R`'s
  largest entry grows by `267/512 ÷ 97/256`, about `1.38` times, while the aeon's span grows about
  `1.38` times too. From the first close to the third, `R` grows `2.4` times and the span `3.8`
  times. On three points the separation tracks `R`'s growth, and both slow down.

[agent-inferred] On three closes the leveling-off is the online estimator's own slowing (its step
falls as its Gram accumulates), not a freeze. Whether the level it approaches is the best a
receiver of this form can reach on these anchors is the fitted-oracle comparison: the
cross-entropy-optimal `R` of the same form on the same windows, against `R`'s span at each close.
That comparison has not been run, and it needs the receiving anchors, which the refine does not
publish. It is the next build.

## 17. `R` is far from what a receiver of its own form reaches on the same anchors

**The fitted comparison.** A read-only accessor, `Resident::receiving_inputs`, returns what `R`
reads at a refined window: the kept word's receiving anchors at the phases' epochs, rotated by the
lift as `ReceivingPhases::read` applies `R`. `contact_ablation` collects them with their targets
and `R` at each close. Outside the machine, `receiver_oracle.py` fits the cross-entropy-optimal
receiver of `R`'s form, `v = W z` in bits with `p_c ∝ 2^(v_c)`. It fits on the same readings `R` had
seen by each close, with the ridge `|W|²/2` that `R`'s unit prior carries, then reads both on those
readings and on the next aeon's. The fit runs in floating point as a search outside the machine;
each reported value is the exact dyadic of its float. These are the wave's codes alone, before the
landmark tree is mixed in. Uniform is 8 bits a reading
([run](2026-10-02_THE_CONTACT_LOOP_receipts/receiver_samples_run.txt), three aeons, 1,533,561 ms
inside the 1,550 s deadline; [fit](2026-10-02_THE_CONTACT_LOOP_receipts/receiver_oracle.txt)).

| Close | Readings seen | `R`: mean code / span (bits) | Fitted: mean code / span (bits) | Next aeon: `R` / fitted (bits) |
|---|---|---|---|---|
| 1 | 1,070 | `16769246/2^21` / `11011564/2^27` | `16737089/2^21` / `8820633/2^25` | `16759842/2^21` / `16683173/2^21` (1,122 readings) |
| 2 | 2,192 | `16757695/2^21` / `11600898/2^26` | `16541577/2^21` / `11545267/2^23` | `16746804/2^21` / `16399855/2^21` (1,138) |
| 3 | 3,330 | `16751147/2^21` / `15628272/2^26` | `16266735/2^21` / `10852723/2^22` | `16737913/2^21` / `15911273/2^21` (70) |

- **`R` gains almost nothing.** Its wave code stays within about `1/50` bit of uniform at every
  close.
- **A receiver of the same form does far better on the same anchors.** It reaches about `1/4` bit
  below uniform in-sample at the third close. On the next aeon, which it never saw, it reaches
  `16399855/2^21` against `R`'s `16746804/2^21` after the second close, a gain of about `1/6` bit a
  reading. Its span grows to about `2.6` bits against `R`'s `0.23`.
- **The anchors carry learnable information that `R` does not extract.** The plateau of §12–16 is
  `R`'s learning rule, not the form's limit and not the anchors.

**`R`'s per-aeon law** (the coordinator's check). Over the three closes, `R`'s largest-entry change
in absolute terms is about `219/1024`, `0.215` and `0.142`, with aeons of 534, 561 and 569 windows.
That gives successive ratios of about `1.0` and `0.66`. A recursive least-squares step of size `1/n`
predicts `ln(3/2)/ln 2`, about `0.585`, for the second ratio, and geometric halving predicts `0.5`.
Three points favour the `1/n` law over halving, so the estimator is still climbing slowly, not
stopping. The earlier "halves each aeon" read the change relative to a growing `R` and was
misleading.

**Why `R` is slow: a derivation from its update.** `R`'s normal law steps `D = Σ_t w g_t (X̂ f_t)ᵀ`,
with `X̂ ≈ H′⁻¹` the inverse of its feature Gram (unit prior included) and `g = p − q`. The step's
metric over the classes is the identity. The cross-entropy's own curvature in the classes, the
receiver's Fisher form `diag p − p pᵀ` (the witness's form of
[October 1](2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md)),
is far smaller near a uniform reading: about `1/256` per class direction over 256 classes. A
Gauss–Newton step in the receiver's own metric would therefore be larger by up to the inverse of
that curvature in each class direction. The certificate also caps `η` at `1` (`ηc ≤ 1`, with
`c` the covector's largest entry), and it bounds the curvature by the worst case `½`, not the
reading's own `diag p − p pᵀ`. [agent-inferred] `R` steps with a class metric about two orders of
magnitude too stiff for a near-uniform receiver, so it moves a small fraction of the way the
fitted receiver shows is available. The next build is `R`'s step in its own Fisher metric: the
witness form already owned in `hnn::executed`, with the certificate read on that form (the Lean
thread's `ln 2/2` and the deposit-condition proofs). It is tested by this same fitted comparison.

## 18. The window Fisher certificate: each window descends, the held-out code worsens

**The law tried** (probe archived at
[`3abbfd0e`](https://github.com/brandonrdug/holonics/commit/3abbfd0e2f01ac64a98d4a4dc9177e570fd09e22),
retired in this change). `R`'s certificate read its own Fisher form on the deposit's window instead
of the worst case. A read's code in bits, `f(v) = −v_t + log₂ Σ 2^(v_c)`, has Hessian
`ln 2 (diag p − p pᵀ)`. A logit change `Δ` scales every mass by at most `2^(osc Δ)`. So with
`η · osc ≤ 1`, the curvature along the ray is at most `2 ln 2 · Var_p(Δ)`, which is at most
`(119/80) Var_p̃(Δ) + ¼|Δ^Im|²` with the odometer masses (`p/p̃ ≤ 17/16`). This replaced the receiving
face's moves and covector scale. The Lean thread proves the window theorem (#158).

**Measured.**
- **First aeon** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/fisher_window_aeon0.txt)):
  - `R`'s certified step had median `2048` (`2^0` before) and the receiver's exponent span reached
    `38983915/2^23` bits (`2076909/2^25` before).
  - Every deposit's own window code still fell (534 of 534), with `A⁻/A⁺` at most `2245639/2^23`.
  - The contacts stopped moving: 6,381 of 6,384 channel families vanished.
- **Campaign 1's exposure at `n*`**: with the window certificate
  ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/fisher_window_exposure.txt)) against main built
  apart ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/baseline_exposure.txt)).

| Reading | Main (`R` steps `2^0..2^2`) | Window Fisher certificate (`R` steps `2^7..2^16`) |
|---|---|---|
| held out, combined face − tree | `−5 + 9/16 + ε` bits (the wave helps) | `+123 + 13/16 + ε` bits (the wave hurts) |
| held out, model − PPM-2 | `−200 + 1/16 + ε` bits | `−196 + 7/16 + ε` bits |
| training, combined face − tree | `−23 + 7/16 + ε` bits | `+290 + 10/16 + ε` bits |

The held-out code worsens by more than three and a half bits. The wave turns from a gain into a
loss, and the mixture falls back to the tree.

**The cause.** The window certificate guarantees descent on the window's own readings only. With
steps two thousand times larger, each deposit fits its own window and damages the others: per-window
descent and held-out worsening at once. The held-out code is the gate, and it fails.

**The next law, derived** (the coordinator's reading, checked here). The metric that does not
overfit is the accumulated Fisher, `Σ_i z_i z_iᵀ ⊗ F(p_i)` over every reading so far. Near uniform
it is about `G ⊗ (1/256)(I − 𝟙𝟙ᵀ/256)`, with `G` the Gram `R` already accumulates. The step becomes
`R`'s own `1/n` normal-law step with its class metric corrected: about `2^7` times larger at the
start, not `2^11`, still shrinking as `1/n`. Its certificate is the window theorem applied to all
readings so far. Whether that can be read from stored statistics alone, without keeping the
readings, is the question the build must settle, since retention is never a tape. Its acceptance is
the held-out code: the wave's held-out contribution must improve on main's `−5 + 9/16 + ε` bits.

## 19. The receiving map's step in its class metric: the held-out code improves

**The law** (`hnn::constitution::receiving_class_metric`, applied where the receiving map's
normal-law step is prepared). `R`'s normal law keeps its own feature metric `X̂ ≈ H′⁻¹`, so its step
still shrinks as `1/n`. Its covectors' magnitude parts pass through the inverse of the readings'
mean class Fisher eigenvalue on the zero-sum classes, `λ̄ = mean_t (1 − Σ_c p̃_(t,c)²)/(|A| − 1)`,
held at the power of two at or below `1/λ̄`. That is about `|A|` near a uniform reading, the
near-uniform form of the accumulated Fisher `G ⊗ (1/|A|)(I − 𝟙𝟙ᵀ/|A|)`. The phase parts are left
as they are. The step is certified in the readings' own Fisher form (§18's bound) and capped at the
unit step, `η · max(osc, 1) ≤ 1`. That cap is what separates it from §18's window certificate, which
let `η` run to `2^16`. The accounting test carries the same metric
(`the_budgeted_carry_accounts_for_every_update`).

**Measured: campaign 1's exposure at `n*`**
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/class_metric_exposure.txt), 595,668 ms; main's
[receipt](2026-10-02_THE_CONTACT_LOOP_receipts/baseline_exposure.txt)).

| Reading | Main | Class-metric step |
|---|---|---|
| `R`'s certified steps | `2^0..2^2` | `2^(−1)..2^0` |
| held out, the wave's contribution (combined − tree) | `−5 + 9/16 + ε` bits | `−13 + 9/16 + ε` bits |
| held out, model − PPM-2 | `−200 + 1/16 + ε` bits | `−208 + 0/16 + ε` bits |
| training, the wave's contribution | `−23 + 7/16 + ε` bits | `−115 + 15/16 + ε` bits |
| training, model − PPM-2 | `−607 + 0/16 + ε` bits | `−699 + 8/16 + ε` bits |

**The gate passes.** On the 1,190 held-out cells, scored before their own deposits, the wave's
contribution improves by eight bits and the whole model's code by more than seven and a half bits
against PPM-2. In training the wave's contribution grows about fivefold. This is the first change
in this line that lowers the held-out code.

**What it leaves open.** The scale is the window's mean Fisher eigenvalue, the near-uniform form of
the accumulated Fisher, not the accumulated matrix itself. The certificate over all readings from
stored statistics (the Lean thread's #160: the running sums `A`, `b` and `Σ A_i vec W_i`, with the
drift check `2X · distance ≤ ω` in the row norm) is the exact form of this step. A dense
`A = Σ z zᵀ ⊗ F(p)` would be `(22 · 256)²` entries on campaign 1's field, so the build has to
factor it, by the Kronecker form or by its classes' structure, before it can be kept. The fitted
receiver of §17 still gains more held-out, so the receiver has room left.

## 20. With the class metric: what is left, and what the comparison must read

The same three-aeon samples run, with `R`'s class-metric step at `404f6ce8`
([run](2026-10-02_THE_CONTACT_LOOP_receipts/class_metric_samples_run.txt), 1,255,992 ms inside the
1,700 s deadline). The fitted receiver of `R`'s form is read at two ridges
([fit](2026-10-02_THE_CONTACT_LOOP_receipts/class_metric_oracle.txt)), and the online law is
replayed outside the machine on the same anchors
([replay](2026-10-02_THE_CONTACT_LOOP_receipts/class_metric_online_sim.txt),
`receiver_online_sim.py`). All codes are the wave's alone; uniform is 8 bits.

| Next aeon after close 2 (1,138 readings) | Code (bits) |
|---|---|
| `R` in the machine (class-metric step) | `16176018/2^21` |
| fitted receiver, ridge `1` (`R`'s unit prior in identity units) | `16741083/2^21` |
| fitted receiver, ridge `1/256` (that prior in the class metric's units) | `13144385/2^21` |
| online replay, prior `1`, identity class metric (`R` before §19) | `16746299/2^21` |
| online replay, prior `1`, class metric | `12985815/2^21` |

- **The ridge-1 fit of §17 was the wrong yardstick.** With anchors of size about `1/60`, a unit
  ridge in identity units dominates the data, and the fit barely leaves uniform. The class metric
  puts `R`'s prior at about `1/|A|` in its own units, and at that ridge the fitted receiver reaches
  `13144385/2^21` bits.
- **The law can reach that in one pass.** Replayed online on the same anchors, the class-metric
  update with the unit prior reaches `12985815/2^21` bits on the third aeon, as low as the batch
  fit. With the identity metric it stays at `16746299/2^21`. A smaller prior under the class metric
  diverges (`15309238/2^14` and `15094019/2^14` bits), so the unit prior is what keeps the
  class-metric step stable.
- **`R` in the machine stays near `7.7` bits on the wave alone.** It is not trained on the wave
  alone. Its covector is the comparison's at the combined face (the tree's logits plus the wave's),
  so it learns the wave as a correction to the tree, and the wave alone is not its objective. Its
  objective, the combined face's code on held-out cells, improved by eight bits (§19).

[agent-inferred] The remaining headroom can only be read on `R`'s own objective, the combined face.
The fitted receiver and the replay must add the tree's logits at each reading and fit or update `W`
on top of them. That needs the tree's grain logits exported beside each receiving input, which is
the next build.

## 21. On its own objective `R` is at its form's limit

A read-only accessor, `Resident::receiving_tree_exponents`, reads the landmark tree as the compare
does: `PendingRatio::tree_faces` at each phase's causal address given the window's known targets,
returning its grain exponents `k_c/L`. The refine's kept faces are the wave's alone; the tree
joins only at the compare, which a first attempt missed (it read zero exponents and is discarded).
Each sample now carries the tree's exponents. `receiver_combined.py` scores the combined face,
exponents `tree + W z`, on the next aeon's readings, never fitted on
([run](2026-10-02_THE_CONTACT_LOOP_receipts/combined_samples_run.txt), three aeons with `R`'s
class-metric step, 1,245,532 ms inside the 1,700 s deadline;
[analysis](2026-10-02_THE_CONTACT_LOOP_receipts/combined_fit.txt)).

| Next aeon (readings) | Tree alone | `R` in the machine | Fitted receiver (ridge `1/256`) | Class-metric replay |
|---|---|---|---|---|
| after close 1 (1,122) | `14967487/2^22` | `14899768/2^22` | `14880363/2^22` | `14913780/2^22` |
| after close 2 (1,138) | `13930200/2^22` | `13802783/2^22` | `13827681/2^22` | `13803654/2^22` |
| after close 3 (70) | `13962286/2^22` | `13793218/2^22` | `13764233/2^22` | `13770373/2^22` |

These are bits a reading on the combined face, against about 3.3 to 3.6 bits for the tree alone.
- **`R` matches a fitted receiver of its form.** On the readings it never saw, the machine's `R`
  equals the fitted receiver and the one-pass replay to within about `1/50` bit a reading at every
  close, and after the second close it is the lowest of the three.
- **The wave adds about `1/33` bit a reading to the tree.** After the second close, `R` saves
  `127417/2^22` bits a reading against the tree alone, about 35 bits over the 1,138 readings of
  that aeon.

[agent-inferred] With the class metric, the receiving map is no longer the bottleneck: on its own
objective it reaches what a linear receiver of its form can take from these anchors. The wave's
remaining gain over the tree is limited by what the medium's anchors carry beyond the tree. That
puts the next lever back in the medium's interior (§6, §12–15), whose covectors arrive through `Rᵀ`
and are larger now that `R` is.

## 22. The larger `R` shrinks the interior's certified steps

Each exposure prints every family's certified steps over its 3,072 deposits. Main against the
class-metric step, from the two §19 receipts
([main](2026-10-02_THE_CONTACT_LOOP_receipts/baseline_exposure.txt),
[class metric](2026-10-02_THE_CONTACT_LOOP_receipts/class_metric_exposure.txt)):

| Family | Main: `2^k`, `k` from … to … | Class metric: `2^k`, `k` from … to … |
|---|---|---|
| contact 1, storage / stiffness / dissipation | −13..9 / −10..11 / −11..11 | −15..−2 / −13..1 / −13..0 |
| contact 2, storage / stiffness / dissipation | −14..10 / −10..10 / −11..10 | −15..−3 / −13..0 / −13..0 |
| element 0, map / passive / slices | −4..11 / −8..13 / −10..12 | −10..−1 / −12..2 / −15..−1 |
| element 3, map / passive / slices | −4..12 / −8..11 / −10..9 | −9..1 / −11..−1 / −14..−4 |

Every interior family's largest step falls by `2^8` to `2^11`.

**Why, from the certificate.** An interior family's curvature is `C = s κ² b`, with the gain `κ²`
carrying the readout's certified bound `‖R‖₂²` and the station score's curvature bounded by its
worst case `s = ½` (module header, "The certified step"; `Constitution::power_gain`,
`element_gain`, `source_gain`). The class metric lets `R` grow, so `‖R‖₂²` grows. The interior's
covectors arrive through `Rᵀ` and grow as `‖R‖`, so its unit step grows as `‖R‖`, while its
certified step falls as `1/‖R‖²`. ~~Its realized move falls as `1/‖R‖`: the interior learns more
slowly the better the receiver reads.~~ [Edit, October 2: the same receipts count the deposits at
which each family took a coarse coordinate, and they do not support this. Over the twelve element
families the count rises from 13,528 to 16,513 of 36,864 (element 2's passive part from 1,039 to
2,954); over the twelve contact families it falls from 5,460 to 5,021, with contacts 0 and 3 frozen
at none; the four standings fall from 258 to 59. The steps shrink, but the covector grows with them,
so the realized moves are not uniformly slower. §23 reads what they do to the code.]

[agent-inferred] This is the class-metric defect moved one locus inward. `R`'s own fix read its
curvature in the readings' Fisher form instead of the worst case. The interior needs the same:
the station score's curvature along the interior's actual move, `Var_p` of the station logits'
change, in place of `s ‖R‖₂² b`. That requires the interior step's effect on the station logits,
a tangent pass through the word, which the machine does not have. That is the next build, and its
gate is again the held-out code.

## 23. The anchors carry the clock, not the passage; the past carries more

Three reads on campaign 1 at `7afbb887` (the class-metric step), each against the held-out code.

**The contacts on the refining grain.** §14 traced the contacts' freeze to the declared lattice:
an entry moves one coarse unit only after its statistic grows by `e^(u/κ)`. The derived schedule
is the receiver's confirmable grain `L(N) = ⌈√(N ln 2/2)⌉`, read dyadically
(`HNN/Ratio/Resolution.grainRead_of_refined`). `Reference::with_refining_grain` re-bases every
retained channel after each deposit by the levels `k(N) = ⌈log₂ L(N)⌉` grew, `k(N)` the least `k`
with `2^(2k+1) ≥ N ln 2` (`refining_grain_exponent`, `Resident::refine_contact_grain`,
`Constitution::rebased`). Over the 6,144 readings that is six levels on every contact, `2^(−9)` to
`2^(−15)` (contact 2 from `2^(−10)`) ([exposure](2026-10-02_THE_CONTACT_LOOP_receipts/refining_grain_exposure.txt):
703,768 ms against a projection of 596 s, inside the 720 s deadline).

| Reading | Class metric (§19) | And the refining grain |
|---|---|---|
| contacts 1 and 2, deposits with a coarse move (of 3,072) | 163 to 1,441 | 2,832 to 3,064 |
| contacts 0 and 3 | none | 66 to 752 |
| held out, model − PPM-2 | `−208 + 0/16 + ε` bits | `−209 + 13/16 + ε` bits |
| held out, the wave's contribution | `−13 + 9/16 + ε` bits | `−13 + 6/16 + ε` bits |
| training, model − PPM-2 | `−699 + 8/16 + ε` bits | `−699 + 12/16 + ε` bits |

Every contact moves now, at nearly every deposit for contacts 1 and 2. The held-out code falls by
`3/16` bit over 1,190 cells and the training code rises by `1/4` bit over 4,958: no measurable
change. The freeze was real, and it was not what kept the contacts from helping. Their change lands
where §9 found it, in the receiver's fibre. The refining grain stays an option of the exposure
(`grain refining`), not the declared schedule, because it does not pass the gate.

**What the anchors carry under richer receivers.** The three-aeon samples of §21, regenerated
(1,320,724 ms against 1,256 s projected, inside the 1,400 s deadline), were fitted on each close's
earlier readings and scored on the next aeon's
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/anchors_richer_receivers.txt),
`receiver_nonlinear.py`). Bits a reading on the combined face:

| Next aeon | Tree alone | `R` (§21) | 512 random Fourier features of `z` | 16 nearest anchors mixed in |
|---|---|---|---|---|
| after close 1 | `14967487/2^22` | `14899768/2^22` | `14810578/2^22` | worse than linear (mixing `1/16` chosen) |
| after close 2 | `13930200/2^22` | `13802783/2^22` | `13812315/2^22` | mixing `0` chosen |
| after close 3 (70 readings) | `13962286/2^22` | `13793218/2^22` | `13786855/2^22` | mixing `0` chosen |

A nonlinear receiver gains about `1/50` bit a reading over `R` after the first close, and nothing
after the second. Quadratic features overfit (above the tree alone after close 1), and those fits
were stopped: incomplete. The anchors hold about `1/33` bit a reading beyond the tree for every
receiver tried.

**What the anchors remember** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/anchor_memory.txt),
`anchor_memory.py`; sample `i` is the reading of cell `i`). Readings that share their preceding `j`
cells were compared with pairs at the same time lags:
- for `j` from 1 to 4, their anchors are as far apart as any pair at those lags (`8408164/2^23`,
  `16384342/2^24`, `16623190/2^24`, `16752357/2^24`). Up to `j = 12` no ratio falls below one, and
  only the 17 and 4 pairs at `j = 16` and `24` come closer;
- the anchor's distance at lag 2 is `15816546/2^27` of the overall, at lag 1 `11863886/2^24`. It
  alternates with the window's two phases and drifts slowly. Its linear transport over two readings
  has eigenvalue moduli between `15620423/2^24` and `16342757/2^24`, a memory of some forty cells;
- the residual of that transport, the innovation, is about a quarter of the anchor's variance
  (`15980795/2^26`, `16247760/2^26`), and grouping it by the two cells just entered leaves
  `14302002/2^24` and `15587670/2^24` of it. The cells entered account for about a seventh of a
  quarter.

**What the past carries** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/context_orders.txt),
`context_orders.py`, an exterior yardstick, never a machine part). Prediction by partial matching
over the same cells, its order 2 matching the exposure's to the bit, codes the held-out cells in
`14691963/2^12` bits at order 4, the best order. The tree alone codes them in about
`3718 + 5/16 + ε` bits and the machine in `3705 + 14/16 + ε`. Order 4 is `119 + 0/16 + ε` bits below the
machine, about a tenth of a bit a reading, while in training the tree beats every order. That is a
lower bound on what the past still holds about the held-out cells beyond the machine; a better
model of the past holds more.

[agent-inferred] The receiver is not the limit, and neither is the contacts' freeze. The anchor the
receiver reads is the ring's own transported state, rotated by the clock: it alternates with the
phase, decays over some forty cells, and its innovation is barely a function of the cells that
entered. The machine therefore cannot use the tenth of a bit a reading that recent contexts carry.
The lever is the source passage's entry into the anchor, the moments
`m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E_g(u_k)`: the encoded cell `E_g(u_k)` must dominate the innovation
over the transport's own motion. The next read separates the innovation's parts at their owner:
the term `E_g(u_k)` against the transport `Ĝ_g(τ_g(k))⁻¹`, with the anchors read before the
clock's rotation as well as after it.

## 24. The leaky count, built; recency at the founding duplicates the tree

**The cause of §23, at its owner.** The word opens on the source ring with
`s_g(0) = P_g^(τ_g) m̃_g`, and campaign 1's transport has modulus one, so the open is the whole
passage's phase counts over their population: `M_g[c] ν̂(n)`. Every cell weighs `1/n`, the newest as
much as the first. A cell therefore moves the anchor by about `1/n` of its size, which is what §23
measured. Below modulus one the open weighs a datum `ρ^a / Σ ρ^(a_k)`, but the phases carry a
datum's age only within one turn, so a passage over one turn was refused
(`HnnError::AliasedAges`), and #62 owed "the leaky count".

**The law, built** (`hnn::moment`, "The leaky count"; `SourceMoment::open_with`). A moment opened at
a transport below one also carries its counts decayed by the transport: at each of the ring's
ticks every count is multiplied by `ρ`, and the cell then enters at its phase. A datum `a` ticks old
weighs its transported weight over a passage of any length, because the age is carried by the decay
and not read from the phase. The counts are carried on `2^(−L_ν−m)`, `m = ⌈log₂(1/(1 − ρ))⌉`, each
product read at the nearest point. A carried count then stays within `2^(−L_ν−m−1)/(1 − ρ) ≤
2^(−L_ν−1)` of the exact decayed count, and a count below half a unit leaves the record. [Edit,
October 2, from the Lean thread's proofs (#164): that bound holds on the ingest path; a section
entry adds half a lattice unit; and the normalized read has no general one-chart-unit bound, since a
burst into one phase rounds every count alike. On campaign 1's cut at `ρ₀`, with up to 22 cells
between ring 0's ticks and up to 40 counts held, the read stays within `3/2` chart units of the
exact transported weights, a relative error near `2^(−17)` in anchors of order one, so the
founded result below is the short memory's, not the read's.] The offset
counts decay the same way. The test reads a 400-cell passage of many turns on campaign 1's field
within one population-chart unit of the brute-force transported weights; at modulus one the moment
reads what it read before (the 267 `hnn` tests pass). The record is a quotient sufficient for the
transported open, not a list of cells, and is read only at the modulus it was opened at.

**Campaign 1 at the founding modulus.** `Constitution::founded_transport` founds ring 0 at
`ρ₀ = 10809/2^17` (`ρ₀^5 ≤ 2^(−18)`: period 5, `L_ν = 18`). A datum one tick old weighs about a
twelfth, and ring 0 ticks only at the cells its port selects
([exposure](2026-10-02_THE_CONTACT_LOOP_receipts/leaky_count_exposure.txt): 538,546 ms against
596 s projected, inside the 720 s deadline).

| Reading | Lossless (§19) | Leaky count at `ρ₀` |
|---|---|---|
| held out, model − PPM-2 | `−208 + 0/16 + ε` bits | `−196 + 7/16 + ε` bits (the tree alone's) |
| held out, the wave's contribution | `−13 + 9/16 + ε` bits | `+62 + 14/16 + ε` bits |
| training, the wave's contribution | `−115 + 15/16 + ε` bits | `+237 + 13/16 + ε` bits |
| the receiver's span, first aeon | `32642301/2^24` bits | `16504115/2^21` bits |

The gate fails: the wave raises the code by 63 bits held out and 238 in training, and the
population falls back to the tree. The fitted receiver tells why
([anchors](2026-10-02_THE_CONTACT_LOOP_receipts/leaky_count_anchors.txt); the samples run passed its
1,400 s deadline after two closes and is incomplete). On the second aeon, fitted on the first, the
best ridge of four saves `1102/2^22` bit a reading against the tree alone. The online replay
diverges. The short memory carries nothing the depth-4 landmark tree does not already hold, and the
anchors are large enough (the span quadruples) that `R` pays for every wrong swing. Campaign 1 keeps
the lossless transport. The leaky count is the law for any modulus below one, and the modulus is the
executed comparison's learned locus; the founding's reason (the phase record's one-turn alias) no
longer binds a leaky moment.

**Even the leaky anchors do not separate recent contexts.** Readings sharing their preceding one to
four cells have anchors `9080097/2^23` to `9272217/2^23` as far apart as pairs at the same lags. On
the anchors' shift-invariant spectrum (the 11-point transform's magnitudes, which remove the ring's
rotation) the ratios are `9137415/2^23`, `14441653/2^24`, `14848212/2^24` and `15326368/2^24`. The
lossless anchors' spectrum gives `16621667/2^24` to `16060674/2^24`. The word carries the open from
ring 0 through the contacts to ring 2, and the contacts' attenuation depends on the joint phase
(the openness census in `FieldDeclaration::quarter_turn`), so the same open reaches the receiver
through different transfers.

**Where PPM-4's 119 bits are**
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/context_orders.txt), each aeon's code). Bits per
aeon, PPM order 4 against the tree alone (from the class-metric exposure's course by aeon):

| Aeon | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| PPM-4 | `10301794/2^11` | `16592879/2^12` | `15084394/2^12` | `8678180/2^11` | `9277217/2^11` | `11255845/2^14` |
| tree | `4945 + 10/16 + ε` | `4004 + 8/16 + ε` | `3779 + 3/16 + ε` | `4180 + 15/16 + ε` | `4629 + 8/16 + ε` | `717 + 14/16 + ε` |

The tree codes below PPM-4 in aeons 0, 1 and 3, and above it by about 96, 100 and 31 bits in aeons
2, 4 and 5. Aeon 2 favours order 3 more still (`15031399/2^12`). The gap is the tree's adaptation
to contexts of three and four cells where the passage repeats them, inside the same depth-4
address.

[agent-inferred] The measured headroom is in the landmark tree's estimator on recurring contexts,
not in the wave. The wave's useful content so far is the long-range one (§21, a thirtieth of a bit a
reading), and recency at the founding duplicates the tree. The next loop reads why the depth-4 tree
lags on the aeons whose contexts recur: its estimator at a context seen a few times, against what
its own counts would support. A classical compressor stays an exterior yardstick, never a machine
part.

## 25. The tree's prior mass: KT's half per digit was the bottleneck

**The cause.** The landmark tree emits a cell as its eight odometer digits, and every node holds
binary Krichevsky–Trofimov masses, `(2n_b + 1)/(2n + 2)`: a prior mass of `½` on each digit. A
context seen a few times, always followed by the same cell, still pays `log₂((2n + 2)/(2n + 1))`
on each of its digits, and the stop weight keeps mixing the shallower nodes until the deep node's
evidence outweighs them. That is the lag §24 located in the aeons whose contexts recur. An exterior
replica of the count face (`tree_estimator.py`), at mass `½`, matches the machine's tree aeon by
aeon to within two bits
([replica](2026-10-02_THE_CONTACT_LOOP_receipts/tree_estimator_replica.txt)).

**The law** (`compression::landmark::context`, `LandmarkDeclaration::mass`; the card's kernel
mirrors it). A node's two masses start at `2^(−j)`, so its face is `(2^j n_b + 1)/(2^j n + 2)`, KT at
`j = 1`. Its floor is `1/(2^j n* + 2)`, so the path lattice `M_p` widens by `j − 1` bits (`41` for
campaign 1 at `j = 3`); the exact normalization holds and the test reads the executed faces within
the rule and their certificates (`the_prior_mass_reads_its_masses_and_keeps_the_rule`). [Edit,
October 2: the rule's derivation rests on the path-level floor, now proved at every prior mass
for any stop weights in `[0, 1]`: `priorMass_digit_face_ge`, the floor `1/(2^j n + 2)` on the path
face that `face_bits` reads (#168).] A register's ceiling stays on
KT's half-unit masses and is refused at another mass.

**Where the gain and the cost sit** (the Lean thread's per-node bounds, #166). At rung `j` a node
costs at most `j − 1` bits more than KT, the worst case on balanced counts; a node that only ever
sees one digit value is never worse than KT and pays at most two bits for its first `2^j + 1`
arrivals. The 246 bits below come from skewed, recurring contexts, and one global `j` trades them
against balanced nodes.

**The choice, by the declared stop prior's method** (the September 26 record, §1: development cells
only, the family charged). The family is the dyadic ladder `j = 1..B`, `B = 8` the odometer digits:
at `j = B` a digit's prior mass is `2^(−B) = 1/|A|`, one class's share of the unit cell, where the
ladder ends. The receiver's tree alone, prequential over the cut
([ladder](2026-10-02_THE_CONTACT_LOOP_receipts/prior_mass_ladder.txt), `hnn_exposure prior-mass
ladder`, 1,333 ms):

| `j` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| development (bits, `+ ε`) | `18539 + 6/16` | `18100 + 0/16` | **`17959 + 1/16`** | `18057 + 3/16` | `18284 + 11/16` | `18572 + 6/16` | `18881 + 4/16` | `19190 + 5/16` |
| held out | `3718 + 5/16` | `3548 + 13/16` | `3467 + 8/16` | `3455 + 2/16` | `3487 + 5/16` | `3542 + 7/16` | `3608 + 5/16` | `3680 + 3/16` |

The development cells choose `j = 3`, charged `⌈log₂ 8⌉ = 3` bits. Campaign 1 declares it
(`FieldDeclaration::campaign_one`, coded in the field's description). In the replica a mixture of the
eight masses in each digit tree, the stop mixture's own form, codes 18 bits below the chosen mass over
the cut: a lead, not adopted. On the choosing cut (§26) the same replica's mixture codes
`15466633/2^4` bits on the development cells and `9179687/2^6` held out, against `j = 3`'s
`15503406/2^4` and `9191720/2^6`: about 2,298 and 188 bits less, a quarter and an eighth of a
percent. It would carry eight trees and their joins on host and card for that. A mixture at
each node instead, the masses weighed by each node's own counts, codes worse than the one mass
there (`15521631/2^4` and `9210873/2^6`): a node seen a few times cannot tell the masses apart, and
pays for asking.

**The gate: campaign 1's exposure at `n*`**
([exposure](2026-10-02_THE_CONTACT_LOOP_receipts/prior_mass_exposure.txt), 686,915 ms against
596 s projected, inside the 720 s deadline).

| Reading | KT (§19) | Prior mass `2^(−3)` |
|---|---|---|
| held out, model − PPM-2 | `−208 + 0/16 + ε` bits | **`−453 + 13/16 + ε` bits** |
| held out, the tree alone − PPM-2 | `−196 + 7/16 + ε` | `−447 + 10/16 + ε` |
| held out, the wave's contribution | `−13 + 9/16 + ε` | `−6 + 3/16 + ε` |
| training, model − PPM-2 | `−699 + 8/16 + ε` | `−1239 + 10/16 + ε` |
| training, the wave's contribution | `−115 + 15/16 + ε` | `−74 + 7/16 + ε` |

**The gate passes.** On the 1,190 held-out cells, scored before their deposits, the model's code
falls by about 246 bits, a fifth of a bit a cell, to `3460 + ε` bits: 127 bits below PPM order 4,
the best exterior order (§23). The model codes below PPM-4 in every aeon now
(`4843 + 2/16`, `3859 + 10/16`, `3585 + 15/16`, `4023 + 2/16`, `4376 + 10/16`, `659 + 11/16` bits
against §24's PPM-4 row). The wave still lowers the code on top of the stronger tree, by less.

[agent-inferred] This is the largest single gain in the line, and it came from the receiving
tree's own estimator, not from the wave, the contacts or the receiver. The wave's share is now about
`1/190` bit a held-out cell. The next measurements are the per-digit-tree mixture of prior masses
(the replica's lead) and what the wave's long-range content adds to the stronger tree.

**After the gate.**
- **The card.** Its normal-law mirror read the receiving map's raw samples, while the host steps in
  the class metric (§19), so the GPU suite's generic parity test refused at the deposit from
  `404f6ce8` on. `receiving_metric_samples` now owns the scaling, and the host's step and the card's
  mirror read the same samples: the GPU suite passes 32 of 32 (56 s, alone under the lock), the tree
  kernel's prior mass (`TreeLaw::unit`) included.
- **The stop prior and the depth at the new mass** (the replica, development cells). The stop
  ladder's rungs 1 to 4 code `9195040/2^9`, `9313303/2^9`, `9528051/2^9` and `9731374/2^9` bits: the
  half stays. Depths 3, 4, 5, 6 and 8 code `9293089/2^9`, `9195040/2^9`, `9192629/2^9`,
  `9192086/2^9` and `9191120/2^9`: past depth 4 the gain is at most eight bits over the development
  cells, below what a depth sweep's charge and a deeper tree's storage cost, so depth 4 stays.

## 26. The prior mass transfers; the wave's share is not a matter of memory

**The prior mass on larger, reserve-excluded cuts**
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/prior_mass_transfer.txt); the tree alone, the
receiver's declaration at each rung, about 16 s a pass). The choosing cut (523,215 cells, its last
65,464 held out) chooses `j = 3` again: development `968962 + 14/16 + ε` bits against KT's
`992822 + 7/16 + ε`, held out `143620 + 10/16 + ε` against `145441 + 8/16 + ε`, and `j = 3` is the
least held-out rung too. The validation cut's confirmation pass, KT against `j = 3`, reads
`137529 + 2/16 + ε` and `136046 + 1/16 + ε` bits held out. The gain shrinks with the passage (about
a hundredth of the held-out code at half a million cells against a fifteenth at 6,148), as it
should: a node's counts grow and its prior matters less. The wide cut (`2^20` cells) does not name
the development reserve as excluded, so its read is refused and was not forced.

**The source's memory against the wave's share** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/memory_sweep.txt);
the leaky count at `ρ = 1 − 2^(−k)`, a memory of about `2^k` of ring 0's ticks, campaign 1 at the
prior mass `2^(−3)`, a diagnostic sweep, not a law):

| Memory `2^k` ticks | 4 | 8 | 16 | 32 | 64 | all (lossless) |
|---|---|---|---|---|---|---|
| held out, the wave's contribution (bits, `+ ε`) | `+9 + 3/16` | `+2 + 8/16` | `−2 + 6/16` | `−6 + 5/16` | `−8 + 14/16` | `−6 + 3/16` |
| held out, model − PPM-2 | `−438 + 13/16` | `−444 + 3/16` | `−448 + 1/16` | `−453 + 15/16` | `−454 + 9/16` | `−453 + 13/16` |

`k = 8` passed its 900 s deadline and is incomplete: the leaky record grows with the memory.
Short memories hurt (they repeat the depth-4 tree), and from 32 ticks on the wave's share stays
between six and nine bits held out. The best, 64 ticks, is less than three bits better than the
lossless open. No memory scale gives the wave a share worth a law.

[agent-inferred] Together with §23–24 and campaign 2's letters (the record of September 26: no
phase or lock letter carries information beyond the preceding cells), this locates the medium's
limit on text at this scale. The anchors, phases and locks are driven by the clock and by the
passage's counts; what is specific to the content reaches the receiver through the tree's cell
letters. Campaign 1 keeps the lossless open and the prior mass `2^(−3)`. A larger share for the
medium needs a different entry of the source into the field, not a better receiver or memory.

## 27. How the text enters the field, and what an entry must do to carry what the tree cannot

A derivation from the owners, before any build.

**The entry, as the code runs it.**
- The moment's open on ring 0 (`SourceMoment::encode`, `open_storage`) is
  `s_0(0) = P_0^(τ_0) Σ_c P_0^(−c) (E_0 M̂_0[c] + Σ_δ E_0^(δ) Ĉ_0(δ)[c])`, with `M̂` and `Ĉ` the
  phase-binned cell and pair counts over their populations (or decayed, under the leaky count).
  `E_0` is `2d_0 × |A| = 10 × 256`, so the open is ten numbers, a linear function of the passage's
  frequencies.
- Within the word every stage is linear in the change. The ring element is a Cayley step with fixed
  `K` and `W` (`propagation::element_step`), the transit is a fixed solve from its two ends' waves
  and its state (`transit_solve`), and a declared resonator is a periodic modulation of the
  constitution: linear, time-varying. The contacts' attenuation `exp(−β_a Q)` depends on the
  rings' placements, that is, on the clock. So the anchor at the receiving epoch is
  `v_j = T_j(τ, Θ) s_0(0)`, with `T_j` fixed by the joint phase and the constitution.
- The receiver reads `f = R P_2^(τ_2) v_j` (`ReceivingPhases::read`), linear again.

So the wave's logits are `R P_2^(τ_2) T_j(τ, Θ) P_0^(τ_0) Σ_c P_0^(−c) E_0 M̂_0[c]`: a
clock-indexed linear map, of rank at most ten, of the passage's phase-binned frequencies. §23–26
measured exactly what this form allows. It carries the passage's global statistics (the thirtieth
of a bit a reading at modulus one), it cannot carry the identity of a recent context (§23's
anchors are no closer for shared contexts), a short memory only repeats the depth-4 tree (§24), and
no memory scale lifts its share past nine bits (§26). The clock-indexed transfer gives one content
a different anchor at each joint phase, which a linear readout cannot undo, and campaign 2's phase
and lock letters carry the clock alone.

**What the tree cannot carry.** The tree reads the last `D = 4` cells exactly and nothing older,
except through its counts' slow adaptation, and its contexts share no statistics. What lies
beyond its address, older cells and similarity between contexts, is the field's possible share.

**What an entry must do** [agent-inferred, from the form above].
1. **Time-local over a span longer than the address.** The leaky count gives it (`open_with`), with
   a memory of `2^k ≥ 2^4` ticks so the span reaches past `D` cells.
2. **Read so that the clock cancels.** The common rotation of the joint phase must drop out of what
   the receiver reads. A relative phase does: the parametron's sheet, the side of a node's
   amplitude against its pump's axis (`ring::sheets`, `Objects/Parametron.sheetReading`), reads the
   wave against a clocked reference, and the elementary objects state the same ("relative phase is
   read through the pump; no linear threshold reads it").
3. **Nonlinear, and addressed by the tree.** A sheet is a sign: a nonlinear feature of the span
   that a linear receiver cannot form. Supplied as address letters (a `Feature` beside the cell, the
   enlarged tree's bundle branch), the tree weighs it by its own evidence. The enlarged tree's
   dominance bounds the cost at one bit a dyadic cell plus the features' description
   (`cell_only_dominance_with_feature_charge`), and the module's own law already says it: "the
   wave earns its computation by supplying address letters the tree weights in".

**The first test, before any owner changes.** The information test: on samples whose source has a
memory past the address, read candidate relative-phase sheets from the receiving anchors (each
node's side against a reference node, which the common rotation leaves fixed), add them as letters
to the replica tree, and score the held-out cells. If the letters do not lower the held-out code
beyond their charge, the entry is refused before it is built. Otherwise the build is a sheet
`Feature` read from the word at the receiving epoch, pushed into the address register, with its
consumer stated at the tree: `face(address ⊕ sheets) ≤ face(address) + charge`.

## 28. The sheet letters fail their information test; at scale the depth is the lever

**The information test of §27** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/sheet_letters.txt),
`sheet_letters.py`). Samples with the source at modulus `63/64`, a memory of about 64 ticks (1,407,266
ms against a projection of 1,690 s, inside the 1,800 s deadline). Each anchor's ten relative-phase
sheets, node `k` against node 0's axis, give letters of one to four bits; the bundle tree reads the
letter before the four cells and joins the cell tree in each dyadic cell by evidence. Over the 3,400
cells, at prior mass `2^(−3)`:

| Letters | the cell tree alone | `r = 1` | `r = 2` | `r = 3` | `r = 4` |
|---|---|---|---|---|---|
| sheets (bits) | `12879530/2^10` | `12919249/2^10` | `12926216/2^10` | `12927228/2^10` | `12928635/2^10` |
| fair coins | | `12926740/2^10` | `12933334/2^10` | `12939966/2^10` | `12940214/2^10` |

The sheets code seven to twelve bits below coins of the same width, so they carry that much, and
39 to 48 bits above the cell tree alone, so they do not pay the join. The lossless open's sheets do
the same. Refused, as §27 required, before any owner changed. Reading the anchors' relative
phase does not remove what the clock-indexed transfer did to them, and the field carries no more
than this to read.

**The depth at scale** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/depth_at_scale.txt); the
tree alone on the choosing cut at `2^(−3)`). Development and held-out bits, each `+ ε`:

| `D` | 4 | 5 | 6 | 8 | 10 | 12 | 16 |
|---|---|---|---|---|---|---|---|
| development | `968962 + 14/16` | `937396 + 11/16` | `927520 + 8/16` | `919596 + 14/16` | `917099 + 7/16` | `916559 + 8/16` | `916377 + 0/16` |
| held out | `143620 + 10/16` | `137933 + 14/16` | `136428 + 9/16` | `135327 + 10/16` | `135044 + 0/16` | `134969 + 10/16` | `134954 + 1/16` |

At half a million cells the address's depth is worth about six percent held out, from 4 to 8, and
the code keeps falling to 16, where the September 26 wide cut found it too (its memory cap stopped
the sweep at 6). Campaign 1's `D = 4` stays at `n* = 6,148`, where depths past 4 gain at most eight
development bits (§25). [agent-inferred] With the prior mass making a context seen a few times pay,
the depth a passage supports grows with the passage; at scale it is the tree's next declared value
to choose, by the development cells against its storage, and the field's share stays the few bits
§26 measured until the source enters it otherwise.

## 29. The depth is a storage limit; the field's best linear share at scale

**The depth law.** Raising a tree's maximum depth from `D` to `D + k` costs any fixed pruned tree
exactly `−log₂ w_D` bits for each of its leaves at the old maximum, one bit at the half stop prior
the receiver declares, and changes neither the estimator's charges nor the best fixed codes (Lean,
#170, at any depth). So a deeper tree cannot do worse than the shallower one's bound by more than a
bit a boundary leaf, and the depth's limit reads as storage [inferred, not proved; the measurement
side follows]. Stored where paths part, the arena's nodes bound no depth, and the carriers' widths
admit depths past `2^11` at `n* = 6,148`; the binding limit is the card's kernel path of 64 nodes.
Campaign 1 now declares `D = 63` (`FieldDeclaration::campaign_one`; its widths `M_p = 49`, `W = 37`).
The tree alone at `2^(−3)` ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/depth_law.txt)):

| `D` | 4 | 8 | 16 | 32 | 63 |
|---|---|---|---|---|---|
| standing cut, development (`+ ε`) | `17959 + 1/16` | `17951 + 6/16` | `17951 + 12/16` | `17951 + 12/16` | `17951 + 12/16` |
| standing cut, held out | `3467 + 8/16` | `3456 + 14/16` | `3456 + 9/16` | `3456 + 9/16` | `3456 + 9/16` |
| choosing cut, held out | `143620 + 10/16` | `135327 + 10/16` | `134954 + 1/16` | `134953 + 1/16` | `134953 + 0/16` |

The code saturates by depth 16 on both cuts, and a full pass at depth 63 takes 157 ms against
132 ms at depth 4 on the standing cut.

**The gate** ([exposure](2026-10-02_THE_CONTACT_LOOP_receipts/depth63_exposure.txt), 620,507 ms inside
the 800 s deadline; library tests 925 passed; GPU suite 32 of 32). Held out, model − PPM-2
`−462 + 2/16 + ε` bits (at `D = 4`: `−453 + 13/16 + ε`), the tree alone `−458 + 11/16 + ε`, the
wave `−5 + 7/16 + ε`; training `−1247 + 12/16 + ε`. Eight bits more, as the tree alone predicted.

**The field's best linear share** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/field_ceiling.txt),
`field_ceiling.py`). §27's entry in its best case for a linear receiver: no clock between the source
and the receiver, the passage's cells decayed at `1 − 2^(−k)` a cell, a full `256 × 256` readout
learned online by `R`'s own law with the machine's one-bit cap, on top of the tree's replica (a rank
far above the field's ten).
- On the standing cut every memory from 4 to 256 cells raises the code: the online readout pays
  more to learn than the passage repays.
- On the choosing cut's first 120,000 cells, scoring the last 20,000 after 100,000 of learning, the
  memory of 256 cells lowers the scored cells by `128` bits of `12869625/2^8` (about a quarter of a
  percent, a 156th of a bit a cell) and raises the learning cells by about 1,760 bits; shorter memories
  raise both.

[agent-inferred] On text the tree's own laws carried the line's gains this session: the prior mass
six percent and the depth up to six more at scale. The field's best linear share, even with the
clock removed and a full-rank readout, is a fraction of a percent at a hundred thousand cells,
while the medium's deposits take about half of each window's time (117 of 223 ms at `D = 4`). What
the field would have to supply is not a linear image of the recent passage.

## 30. The urn's base measure: the field carries nothing there; the tree's own root does

The tree keeps every context apart, and each node's prior masses split evenly, the `+1` of
`(2^j n_b + 1)/(2^j n + 2)`. A field could share across contexts through that slot, so it was tested
there before anything was built ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/base_measure.txt)).

**Where the code sits.** By the count of the deepest node on the opened path that has counts
(`leaf_counts.py`, depth 16, `2^(−3)`), the held-out code falls on digits whose leaf has been seen
once (`12307736/2^25` of it, about 37 percent), two or three times (`15063282/2^26`, 22 percent),
four to seven (`10662917/2^26`), eight to fifteen (`12863853/2^27`), sixteen to 63 (`14572158/2^27`)
and more (`12196741/2^28`). The choosing cut splits alike. Most of the remaining code is at sparse
leaves.

**The wave as the base.** The wave's own prediction at each reading (its exponents `W z`, the map
published at the aeon's opening close), split down each digit's dyadic cell, as every node's base
measure (`base_measure.py`, the aeons after the first, 2,260 cells): the even base codes
`15341375/2^11` bits, the wave's base `15289889/2^11`, and a control giving each reading another
reading's base `15285139/2^11`. The gain is a non-even base, any one; the wave's reading-specific
content adds nothing (the control does as well). Refused as a field entry.

**The tree's own root as the base** (`tree_base.py`). The depth-0 node of each digit tree knows the
unconditional split, and a fresh or sparse context should lean on it, not on an even split.

| Base | standing cut, development | held out | choosing cut, development | held out |
|---|---|---|---|---|
| even (the law) | `9191310/2^9` | `14158263/2^12` | `14662032/2^4` | `8637060/2^6` |
| the root's face | `8911997/2^9` | `13872419/2^12` | `14604178/2^4` | `8629383/2^6` |
| the parent's, chained | `9824207/2^9` | `15728167/2^12` | | |
| the root's, mixed with even at ½ | `8933100/2^9` | `13753683/2^12` | `14497403/2^4` | `8551159/2^6` |
| that, one base for the whole digit tree, at grain `1/16` | `8936120/2^9` | `13750868/2^12` | `14500844/2^4` | `8552417/2^6` |

The last row, every node of a digit tree sharing one base read from its root at the receiver's
grain and mixed with the even split at ½, codes about 498 development and 100 held-out bits less on
the standing cut (three percent held out) and 10,074 and 1,322 less on the choosing cut (one
percent). The parent's face chained down the path doubles what the stop weights already mix, and
loses. One shared base keeps every node of a chain under one law, so the storage where paths part
stays exact, and the mixture at ½ keeps each base mass at least a quarter, so the faces' floor moves
by one bit. The grain is the receiver's own, `1/16`; at `1/64` the code is the same to a bit.

[agent-inferred] The field has no share at the base either; the base slot's value is the tree's
own unconditional split, which the tree already holds. The next build is that law in the tree
owner, its oracle and the card's kernel, gated on held-out code, with its Lean counterpart in #62:
the node law then reads its digit tree's root, a state beyond the arrivals reaching the node.

## 31. The root's base, built: held out 99 bits lower

**The law** (`compression::landmark::context::BaseMeasure::Root`, `Topology::kt_based`,
`base_sixteenths`; the card's `tree_kt`). Every node of a digit tree, its root included, splits its
prior masses by one base read from the root's masses before the cell's deposit:
`16π_0 = ⌊16(½ k_root(0) + ¼) + ½⌋` (nearest, ties up), `k_root(0) = (2^j n_0 + 1)/(2^j n + 2)` the
root's face at the even base, and a node's face is `(2^(j+4) n_b + 2·16π_b)/(2^(j+4) n + 32)`. A
level past the last stored one reads the base's split in place of `½`; a digit tree with no root
reads `½`. The floor is `1/(2(2^j n* + 2))` (`face_bits_at`) and `κ` reads `16(2^j n* + 2)`; campaign
1's widths are `M_p = 50`, `W = 37`. The executed tree matches the replica's `shared-g4` mode to
the bit on the standing cut (development `17453 + 5/16 + ε` against `8936120/2^9`, held out
`3357 + 2/16 + ε` against `13750868/2^12`), so the storage where paths part stays exact under the
shared base. The test reads the faces normalized, within the rule and within their certificates of
the oracle (`the_roots_base_keeps_the_rule_and_leans_on_the_unconditional_split`). The Lean
counterpart is in progress on the replica's form; the Rust differs from it only in rounding exact
ties upward (Python rounds them to even) and in reading the base's split at the levels past the last
stored one.

**The gate** ([exposure](2026-10-02_THE_CONTACT_LOOP_receipts/root_base_exposure.txt), 661,783 ms
inside the 800 s deadline; library tests 926 passed; GPU suite 32 of 32). Held out, model − PPM-2
`−560 + 15/16 + ε` bits (with the even base `−462 + 2/16 + ε`), the tree alone `−557 + 4/16 + ε`,
the wave `−3 + 10/16 + ε`; training `−1688 + 15/16 + ε`. The model codes the 1,190 held-out cells
in about `3353 + ε` bits, about 233 below PPM order 4. Campaign 1 declares the root's base
(`ReceiverDeclaration::base`, coded in the field's description).

**The declared values under the root's base** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/root_base_choices.txt)).
- On the standing cut the development cells still choose the prior mass `2^(−3)`
  (`17453 + 5/16 + ε` bits, against `17588 + 10/16` at `2^(−2)` and `17506 + 2/16` at `2^(−4)`).
- On the choosing cut at depth 16 the root's base at `2^(−3)` codes `906302 + 12/16 + ε` development
  and `133631 + 8/16 + ε` held-out bits, against the even base's `916377 + 0/16` and
  `134954 + 1/16`: about one percent less on each, and `2^(−3)` is the least of the three masses
  read there too.
- The stop prior's ladder under the root's base (the replica, depth 16, `2^(−3)`): rungs 1, 2 and 3
  code `8936120/2^9`, `9108226/2^9` and `9360469/2^9` development bits; the half stays.
- The depth's limit depends on the population. At 523,215 cells the widths refuse depth 63 (an
  operand of 132 bits), so the deepest the carriers admit sets it there; at campaign 1's 6,148 cells
  the card's kernel path does.

## 33. The fixed field's share on text, derived and measured

**The derivation, from the owners.** Within campaign 1's library a field reading reaches the
receiver only through the word, and three facts bound what it can be.
1. *Nothing of a word persists.* A word opens from rest except the source storage, and is released
   at its end (`hnn::word`'s header; `Current` holds no wave, guard 16). The resonator's two-state
   motion lives only in its word. So the state retained from one window to the next is the
   moment's counts `M̂, Ĉ` (whole or decayed), the clock `τ` and the constitution `Θ`.
2. *Every stage within a word is linear in the change.* The ring element is a Cayley step with fixed
   `K` and `W`; the transit is a fixed solve; a pump is a periodic modulation of the constitution
   (linear, time-varying); a boost is an indefinite stiffness `b diag(σ) bᵀ` (linear). So a reading
   at a receiving epoch is `T_j(τ, Θ) s(0)`, linear in `(M̂, Ĉ)` for fixed `(τ, Θ)`.
3. *A sheet is the sign of one such projection.* `ring::sheets` reads `Re(z ā) < 0`, the side of a
   linear reading against an axis. A pumped sheet does not hold a state across windows: it is
   recomputed from the counts at every word.

So at a fixed constitution whatever the field supplies is a function of `(M̂, Ĉ, τ)`: global or
decayed frequencies, signs of linear projections of them, and the clock, which is itself a count of
the selected cells. A pumped sheet cannot carry a regime longer than the counts already carry it,
and a boost changes `T_j`, not the linearity. At a fixed `Θ` the field's information about the next
cell beyond the tree is at most `I(x; M̂, Ĉ, τ | address, Θ)`. `Θ` is not fixed in campaign 1's
protocol: every compared window deposits (`reference.rs:3999-4008`, through `Constitution::deposited`
at `reference.rs:1424` to `resident.constitution` at `:1463`), and §7–§8 measure the constitution
moving at nearly every one. Its deposits are formed from each window's own cells, so `Θ` depends on
the passage read so far, not only on its counts, and the adapting field's information is bounded
only by `I(x; M̂, Ĉ, τ, Θ | address)`. This record does not bound the `Θ` term. [Corrected
October 3, after Astra's review: this first stated the bound without `Θ`.]

**The measurement of those fixed forms, in the field's best case** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/regime_letters.txt),
`regime_letters.py`). The strongest state those forms allow, with the clock removed: the signs of the
top one to three principal directions of the passage's decayed counts, found on the development
cells (an exterior search), at memories of 4 to 1,024 cells. The state is the first letter of a
bundle tree whose digit trees read their base from the state's node (the root switched by state),
joined with the cell tree in each dyadic cell; coins of the same width are the control. The cell tree
is campaign 1's law (prior mass `2^(−3)`, the root's base, depth 16).
- On the standing cut no state codes below the cell tree alone on the development cells: the state
  letters cost 11 to 71 bits there (coins 64 to 75), and held out they range from one bit below the
  cell tree to 30 above.
- On the choosing cut's first 200,000 cells (development to 170,000) the cell tree codes
  `11097227/2^5` development and `15474099/2^8` held-out bits. The states cost 68 to 133
  development bits (coins 126 to 137) and save at most `4811/2^8`, about 19 bits of some 60,000,
  held out (the 1,024-cell memory, two signs).

The states carry a few tens of bits over coins, never their join. Together with §21 (linear readout),
§26 (memory), §28 (sheets through the clock), §29 (a clock-free full-rank linear field) and §30 (the
base), this measures the share of the fixed forms of the counts and the clock on text with campaign
1's library: four to nine held-out bits, at about half of each window's compute. It is not a ceiling
on the adapting field: what the deposits carry through `Θ` is not separated by these reads.

[agent-inferred] **The role question, answered from this.** On text the compression is the tree's.
At a fixed constitution, with a state of counts and clock and dynamics linear within a word, the
field cannot add what the tree lacks; whether the deposits' change of `Θ` adds it is not measured
here. To carry a passage-level state it would
need a state that persists across words (the continuing word exists only within a refinement,
`Word::continuing`), and to carry similarity across contexts a nonlinear entry of the content
itself, not of its counts. Both change the retention law's quotient, not a declared value, so
neither is a branch option to gate on campaign 1: each is a design of the field's law with its
Lean counterpart first.

## 34. A latched sheet kept across windows: state beyond the counts, and what it is worth on text

**The law, derived from the library.** The receiving parametron reads its seed "linear, then
threshold" (`ring::lock`): past the bifurcation the in-phase coordinate grows by the Floquet
multiplier and the sheet is its sign. Kept across the window boundary instead of released, the
sheet's amplitude seeds the next window beside the new readout `L_t`, so
`x_(t+1) = μ_w x_t + L_t`, `s = sign x`, with `μ_w` the in-phase multiplier over a window at the
declared pump (`p = 5/8`, the bank's). The library's executed pump has no saturation, so a kept
amplitude grows without bound and the latch becomes absorbing; read at its locked sheet instead
(`x_t` replaced by `s_t`, the lock's unit), the law is `s_(t+1) = sign(a s_t + L_t)`, a recurrent
threshold state. Its hold `a` is the locked unit over the readout's scale, which the library does
not declare, so it is a declared value chosen on the development cells (the ladder `1/2` to `4` in
the readout's spread, charged two bits), as the stop prior and the prior mass were.
- *What it can represent.* A flip-flop: inputs above the hold set or reset it, smaller ones leave
  it. So it can hold a bit for any length, past the depth-63 address and past the counts' memory
  (a span opened by one cell and closed by another). One sheet cannot toggle on a single cell
  (parity is not a threshold of one input and one state) and cannot count.
- *Its ceiling.* At most one bit a sheet a window, and its information about the next cell is at
  most the state's entropy given the address.
- *Its charge.* Supplied as a letter, the bundle tree's join, at most one bit a dyadic cell plus the
  letter's description (`cell_only_dominance_with_feature_charge`); a searched input adds its search.

**Measured** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/latch_letters.txt), `latch_letters.py`;
the state the first letter of a bundle tree joined with the cell tree, as in §28 and §33). Two inputs,
each the field's best case: the top principal readout of the last few cells' counts, and a set/reset
pair of cells searched on the development cells among the 30 most frequent (870 pairs).

| | standing cut, development | held out | 200k choosing cells, development | held out |
|---|---|---|---|---|
| the cell tree alone | `8936120/2^9` | `13750868/2^12` | `11097227/2^5` | `15474099/2^8` |
| fair coins | `8968739/2^9` | `13794089/2^12` | `11101457/2^5` | `15475106/2^8` |
| the readout latch, hold chosen on development | `8941129/2^9` (½) | `13707740/2^12` | `11095951/2^5` (4) | `15465098/2^8` |
| the set/reset latch | `8873843/2^9` | `13741390/2^12` | `11100122/2^5` | `15472984/2^8` |

On campaign 1's cut no latch codes below the cell tree on the development cells except the searched
set/reset pair (`.` sets, space resets), whose 122 development bits shrink to 2 held out, below its
search's ten bits. At 200,000 cells the readout latch at the ladder's top hold saves about 40
development and 35 held-out bits of some 60,000 (a seventeenth of a percent), net of its join.

[agent-inferred] A kept sheet does carry state the counts cannot, and at scale a little of it pays.
On campaign 1 it does not pass the gate, and at half a million cells its share is a few hundredths
of a percent, against a change of the retention law (the receiver's sheet in `Current`) with its
Lean counterpart. It is not built. Persistence through a latched element is measured out on text
with this library: at a fixed constitution the field's share stays the few bits of §33, plus at
most this latch's hundredths of a percent at scale; what the deposits carry through `Θ` is not
measured (§33).

## 35. The parent's base, and the two mixes still chosen

**The parent's base** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/parent_base.txt), `tree_base.py`'s
`halfparent`). Each node's base is its parent's face at the parent's own base, mixed with the even
split at ½, read before the cell's deposit at every level; the root's base is even. The ½ mix keeps
every base mass at least ¼, so the floor halves as under the root's base. Against the root's base:
- the standing cut: development `8981595/2^9` against `8936120/2^9` (89 bits more), held out
  `13769312/2^12` against `13750868/2^12` (four and a half more);
- 200,000 choosing cells: development `11054750/2^5` against `11097227/2^5` (1,327 bits less), held
  out `15377729/2^8` against `15474099/2^8` (376 less, about 0.6 percent).

The parent pays at scale and loses on campaign 1's cut, where a parent seen a few times is a noisier
base than the root. It also costs the storage where paths part its exactness: the levels of a
stored chain share their counts but not their bases (each level's base is the one above it), so a
chain is no longer one node law. Campaign 1 keeps the root's base; the parent's base is the law to
build for a population large enough that its parents carry data, with the chain's per-level bases
stated first.

**The two mixes still chosen.**
- *The stop prior's ½* stays the development cells' choice under the root's base (§32: rungs 1 to 3
  code `8936120/2^9`, `9108226/2^9`, `9360469/2^9`).
- *The base's ½* (the root's weight `w` in `w·root + (1 − w)·even`). On the standing cut the
  development cells code `9039797`, `8936120`, `8861516`, `8849923` and `8878611` (each `/2^9`) at
  `w = ¼, ½, ¾, 7/8, 15/16`, held out `13948911`, `13750868`, `13752616`, `13773893`, `13793982`
  (`/2^12`); at 200,000 choosing cells the development cells code `11167175`, `11097227`,
  `11071232`, `11095318`, `11110583` (`/2^5`) and the held-out cells `15523425`, `15474099`,
  `15467742`, `15505240`, `15540114` (`/2^8`).

The development cells choose `7/8` on one cut and `¾` on the other, and neither choice moves the
held-out code by more than six bits on campaign 1 or 25 at 200,000 cells. The data do not settle the
weight. [agent-inferred] The ½ is the two-face mixture's uniform prior (the even split and the root,
with no evidence between them), the same form as the stop prior's and the join's, and it keeps the
floor one bit from the even base; it stays declared, with that reason, rather than chosen.

## 36. The receiving step's certificate pairs the original covector (Astra's review)

Astra's source review (October 2, the counterexample executed against native code): §19's step
handed the class-metric-scaled samples to `NormalLaw::prepare`, which forms the move `D` and its
alignment `a = Σ_t w ⟨g_t, D f_t⟩` from the same samples, so `a` paired the scaled covector `κg` with
the move. The certified decrease then overstated the original code's by the metric's factor: on a
uniform two-class reading with a unit feature, `κ = 2`, `D = (½, −½)`, the original pairing is `½`,
the scaled one `1`, while the smooth score falls by `log₂(4/3) < ½`. Right, and repaired:
`receiving_fisher_face` now also returns the original comparison's alignment, which replaces the
scaled one, so the metric shapes `D` and the certificate bounds the original code
(`the_receiving_step_pairs_the_original_covector`; Astra's standalone diagnostic
`class_metric_direction_pairs_with_the_original_comparison_covector` joins the suite with the
rebase boundary regression).

**What it changes on campaign 1: nothing measured.** The repaired exposure reads every held-out and
training figure of §31 to the last digit (model − PPM-2 `−560 + 15/16 + ε` held out), and the receiving
map's steps stay `2^(−1)..2^0`
([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/pairing_repair_exposure.txt), 791,782 ms). The step is
held by its unit-step cap `η · max(osc, 1) ≤ 1` below what the corrected certificate admits, so the
§19 gain was certified all along; the overstatement had no consumer on this cut. Every later
section's figures stand.
