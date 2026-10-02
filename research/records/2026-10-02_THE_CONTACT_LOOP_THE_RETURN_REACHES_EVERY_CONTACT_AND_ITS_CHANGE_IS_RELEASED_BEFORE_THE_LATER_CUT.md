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
| the continuing word (the window's own change) | 250 | 250 | 250 | **36** |

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
- **The chart.** `K = (I − D)⁻¹ C`, the contact's quasi-static elimination: the interior state a
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
3. The receiver can tell the two media apart over `N` readings exactly when the accumulated
   divergence reaches one bit, `N·D(p′‖p) ≥ 1` (Stein's lemma: the error of telling them apart
   falls as `2^(−N·D)`). Since `Var_p(δ) ≤ max_c δ_c²`, a change is unreadable over `N` readings
   whenever `max_c |δ_c| < √(2/(N ln 2))`.
4. The receiver integrates readings within one retained state, over one aeon: `N = 1,190` cells on
   campaign 1's field (the exposure's declared aeon). So its resolution is
   `√(2/(1190 ln 2))` bits, which lies in `(1/21, 1/20)` because `1190 · ln 2 / 2` lies in
   `(400, 441)`. The declared `1/16` is coarser than this by less than a factor of `4/3`. That
   discrepancy is real, but it is small next to what follows.

**The contacts' change, measured** ([receipt](2026-10-02_THE_CONTACT_LOOP_receipts/readability_256.txt)).
Over 256 windows, take the largest change of the next window's exponents `v` over its phases and
classes:
- **The fresh consumer:** median `41/2^24`, upper quartile `33/2^23`, largest `695/2^25` bits.
- **The continuing consumer:** median `53/2^24`, upper quartile `77/2^24`, largest `7/2^18` bits.
- None reaches `1/21` or `1/16`. The largest, `7/2^18`, lies ~~more than `2^12` times~~ more than
  `2^10` times below the derived resolution. [Edit, October 2: the ratio is `(1/21)/(7/2^18)`, about
  `2^10.8`, not more than `2^12`.]

**The finding.** The contacts' change cannot physically be read by this receiver. With
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
