# The moment tower learns GSM8K bytes once its modes are passive and its contacts read a ratio

Refs #405 #404. Follows [the node lock reads the located equality](2026-10-23_THE_NODE_LOCK_READS_THE_LOCATED_EQUALITY_AND_CONTEXT_PAST_EIGHT_CHARACTERS_ADDS_NOTHING.md)
and the mathematics thread's [code-length field](https://github.com/brandonrdug/holonics/blob/973033f26f586463541c466053883556247dbf27/research/records/2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md)
(its §2: a selective state-space model takes the conjunction that a count of exact contexts
cannot). Status: [definition; agent-inferred, October 23], built and measured on the host.

## What was built

`hnn::tower` is a byte-grain completed state-space model in exact integers. Each level holds 64
diagonal complex modes (parametrons) driven by the class's located face, read through 256
rectifying contacts; two levels sit on a residual stream, and the byte face is a softmax through the
dyadic exponential navigator. A section of 128 bytes on 8 streams is read forward and its covector
taken by the reverse scan inside the section. Its first and second moments are carried over
sections. Its deposit is certified by rereading the section from its opening states: the step
stands only if the section codes strictly fewer bits, compared exactly as integer products, and a
refused step halves until it is certified or releases to zero. The law, its grains and its adjoint
are in the module's header.

`CellJoin` joins the tower to the route at the route's own grain. At a base-four cell of phase `k`
the tower's face is its byte face summed over the cell's prefix. Its news over the route's face is
`f_d = log₂ t̂(d) − log₂ r̂(d)`, and the joined face is `p̂(d) ∝ r_d 2^(α_k f_d)`, with one weight a
phase, opened at ½ and moved by the lock's Newton step every 1,024 bytes.

## Defects, located by measurement

**The certificate refused at the working rates.** With at most two halvings, rates `2^(−6)` and
`2^(−7)` deposited 2 of 52 sections on 100 problems and none after. Halving until certified or
released learns at `2^(−7)` (100 seen problems: 3.628, 3.092, 2.888 bits a byte over three passes).

**A mode's decay crossed to the margin in three steps.** On 1,000 problems pass one trained. Pass
two refused, first at carriers that were then widened (the release, and the covector, now carried
in `i64`), then between sections 480 and 507 with a contact drive past its 32-bit carrier. The
section readings (`TOWER_SWELL`) showed the first level's largest decay move from |λ| = 0.974 to
0.991 over nine sections while the modes' face grew from 2.5 M to 12.7 M (on `2^(−16)`); the next
section passed the carrier. A Cartesian step of rate `2^(−7)` moves |λ| by up to 0.008 a section,
and the distance from 0.974 to the margin is 0.026: about three sections. Two changes follow from the passive mode:

- the push is scaled by `γ = √(1 − |λ|²)` in the step (it was fixed at founding), so a mode's state
  under any push keeps `|h| ≤ √((1 + |λ|)/(1 − |λ|)) max|Bx| ≤ 2^(13/2) max|Bx|`, and `G_λ` gains
  `−(λ/γ) Σ_t Re(conj(G_h) Bx)`;
- a move is stepped in the chart `(ν, φ) = (ln(1 − |λ|), arg λ)`, so a step changes `1 − |λ|` by the
  factor `e^(±2^(−7))` and the decay approaches the margin geometrically.

**The first level stopped conducting.** With both changes, pass two completed (held-out 2.867 →
2.782 bits a byte), but between the first two rested states 251 of the first level's 256 contacts
changed no weight. Its mode, push and read first moments were at most 3 units on their grains,
against up to 1.4 × 10¹¹ at the second level: no covector reached its modes. The contacts read the
modes' face at its power (some 50 units), so one step of the contacts moved their drive by tens of
units and they went dark. The contacts now read the face as a ratio to its own power,
`r̂ = r/‖r‖_rms`, with adjoint `(∂r̂ − r̂⟨r̂, ∂r̂⟩/d)/‖r‖_rms`. In the run below the first level's
largest mode moment after pass two is 4.6 × 10¹¹.

Each adjoint is checked against the code's measured difference: `the_covector_matches_the_code_difference`
reads only perturbations that keep every contact on its side of its kink, and
`the_move_chart_covector_matches_its_step` checks the chart.

## Measured

Trained online on 1,000 problems of the GSM8K training partition (`train1000`, 519,633 bytes) and
read frozen after each pass on the partition's 747 development problems (397,669 bytes, never
trained on), with width 64, 64 modes, 256 contacts, 2 levels, 8 streams, sections of 128 bytes and
rate `2^(−7)`. Every one of the 507 sections in every pass deposited. Bits a byte:

| pass | train (online) | held out | question | answer prose | answer digits | markup |
|---|---|---|---|---|---|---|
| 1 | 3.188 | 2.828 | 2.924 | 2.755 | 3.512 | 2.202 |
| 2 | 2.740 | 2.687 | 2.791 | 2.593 | 3.478 | 2.066 |
| 3 | 2.628 | 2.628 | 2.726 | 2.535 | 3.443 | 2.012 |
| 4 | 2.566 | 2.591 | 2.690 | 2.489 | 3.463 | 1.987 |
| 5 | 2.525 | 2.577 | 2.681 | 2.475 | 3.370 | 1.990 |
| 6 | 2.493 | 2.554 | 2.655 | 2.457 | 3.338 | 1.968 |
| 7 | 2.467 | 2.531 | 2.632 | 2.434 | 3.290 | 1.971 |

Over seven passes the held-out code falls 10.5%. By region it falls 10.0% on questions, 11.7% on
answer prose, 6.3% on answer digits and 10.5% on markup. The digits rose once (pass 4) while the
whole fell, and the markup holds between 1.97 and 1.99 from pass 4 on. The second level's contacts woke slowly:
the number of its 256 contacts that changed a weight in a pass went 38, 120, 178, 195, 139, 213,
against 256, 225, 216, 183, 177, 184 at the first level.

**Joined to the route.** The route is the 1,000-problem receiving tree with its passage and node
lock (`lock1000` of the previous record), frozen and read on the same 747 problems:

| reading | bits a byte | question | answer prose | answer digits | markup |
|---|---|---|---|---|---|
| route | 1.786 | 1.914 | 1.510 | 2.634 | 1.975 |
| tower after pass 1 | 2.853 | 2.941 | 2.770 | 3.748 | 2.190 |
| joined, after pass 1 | 1.772 | 1.899 | 1.506 | 2.638 | 1.902 |
| tower after pass 7 | 2.531 | 2.631 | 2.433 | 3.289 | 1.970 |
| joined, after pass 7 | 1.754 | 1.885 | 1.491 | 2.604 | 1.851 |

The joined code is 1.8% below the route. Most of the gain is in the markup (−6.3%), where the tower
alone already codes level with the tree (1.970 against 1.975) while coding prose 61% above it. The
weights after the read are 15186, 19432, 12754 and 7187 on `2^(−16)` for the byte's four phases
(0.23, 0.30, 0.19, 0.11). The tree carries the prose and the questions; the tower's state carries
the relation inside a calculation.

**Beside the code-length field.** The mathematics thread read its regions online, in context, on
the training problems: question 1.817, answer prose 1.345, answer digits 2.592, markup 1.844, whole
1.659. The readings here are frozen states on held-out problems, so they are not the same quantity;
the order of the regions agrees (digits highest, prose lowest), and the join moves the markup most.

## Samples

The held-out prompt is the first problem of the dev partition, as in the previous records: "John
volunteers at a shelter twice a month for 3 hours at a time.  How many hours does he volunteer per
year?" Each sample opens at the prompt and releases 400 bytes, each byte drawn exactly from its face
with the same key stream. Nothing is graded against the answer.

The tower alone, after pass 7 (the prompt codes at 2.968 bits a byte):

```text
Jars wangrave for the yers on thaves equal parts = <<5*2=80>>45 owesd 2/1 bats of vaplosie starows ants.
=125s on the fill.
The paills 3al 2 = <<10+3=12>>12 siges * 6 + 5 = <<1+2=4>>8 kess 15 + 2p 2 = <<60-3=26>>26 pooks
#### 30

Jam $4 jefits wall. On total 2*4=<<4/3+1/1=80>>58 everys.
Thereforeer avery neest work.
16 inter that of she total his inte.  each is 1 more.  = <<200-12=15 and dilows ha
```

The tower joined to the route, with the weights above:

```text
Juggloriona has seasnocks. coffee a day down for 1 week
He ate 5 yearting twice as many has left on Lulume?
In thday, who seriors 4 +wards - 10 = 2 peroni earlier erasers does he height sears party are?
Daniela month only which means on the amount he takes in two times?
If Saturdays he 30% often per manufavier  His for a mangoes at a third meat the tem yogether the flies, the trudeliver he two fri
```

The tower writes the answer's form: lines of calculation, well-formed `<<a op b=c>>` markup with
the result repeated after `>>` (`<<10+3=12>>12`, `<<60-3=26>>26`), and a `####` line, with
wrong arithmetic and invented words. The join writes question-shaped lines with more real words.
Neither is readable as an answer.

## On all 6,726 problems

The same tower, trained fresh for two passes on the whole training partition (3,528,168 bytes, 3,445
sections a pass, every one deposited), read on the same 747 held-out problems:

| reading | bits a byte | question | answer prose | answer digits | markup |
|---|---|---|---|---|---|
| tower, pass 1 | 2.517 | 2.631 | 2.422 | 3.144 | 1.941 |
| tower, pass 2 | 2.404 | 2.521 | 2.312 | 2.964 | 1.849 |
| route on all problems (`lockall`) | 1.591 | 1.699 | 1.352 | 2.439 | 1.692 |
| joined | 1.579 | 1.690 | 1.349 | 2.419 | 1.628 |

One pass over all problems codes the held-out problems below seven passes over 1,000 (2.517
against 2.531); the second pass takes them to 2.404, and the online code over the pass (2.408) sits
level with the held-out code, so the tower is not yet fitting its training text more closely than
text it never saw. Joined to the route trained on the same problems, it takes 0.75% off the
route's 1.591, again mostly in the markup (1.692 to 1.628, −3.8%); the join's weights are 11382,
13937, 7497 and 4129 on `2^(−16)`. With seven times the problems the route gained 11% and the
tower 5%, so the tower's share of the joined code shrank.

The tower alone after pass 2:

```text
Jass was 2 years, the yener?
Ell woungles $40/4= <<18/1=4>>8 hours peach $2.50, catanjupba to pets one-the istarjarip can, how much money  Caghet cepeired bard a's wore to the 6 vivery hour than wame 10 to store is colloe has Bennide 12 games. Weartips on one edriting a cruake. If How many soney to duel: 5 lructrom?
Hind yeeds 75% ine doyes 30 shounds five times 20+4 vaced and, bieks dill have Toc
```

Joined to the route on all problems:

```text
Jufflowing once.  How far drinks taller at entir ( the amoas bought some to hours in the conies at a time.  How many hours does each firewolf tour ideallards did Eman plant's considers are per day thers at what is the animals a month n 300 races and twice as many hours at made the third 1. How many double the access hadn't hit head arling hour peanuts - 8 clowns 1/3 less the vowermen hand 200 cars
```

The joined sample carries a phrase of the prompt ("at a time.  How many hours does") inside
question-shaped text. Neither sample is readable.

The first launch planned three passes; its first 96 sections ran at 0.191 s a section against the
0.177 s projected from the 1,000-problem run, so it was stopped at 31.1 s and relaunched at two
passes (projected 1,366 s, deadline 1,450 s, measured 1,204.6 s and 110 MiB: 0.88). The joined
read took 199.5 s and 2.6 GiB, the samples 0.3 s and 11.3 s.

## More passes, width and steps

**Five passes on all problems.** The narrow tower continued from its pass-2 state:

| pass | online code over the pass | held out | question | answer prose | answer digits | markup |
|---|---|---|---|---|---|---|
| 1 | 2.649 | 2.517 | 2.631 | 2.422 | 3.144 | 1.941 |
| 2 | 2.408 | 2.404 | 2.521 | 2.312 | 2.964 | 1.849 |
| 3 | 2.332 | 2.367 | 2.492 | 2.271 | 2.875 | 1.814 |
| 4 | 2.283 | 2.335 | 2.451 | 2.242 | 2.883 | 1.797 |
| 5 | 2.250 | 2.310 | 2.420 | 2.234 | 2.815 | 1.735 |

The held-out gain a pass falls (−0.113, −0.037, −0.032, −0.025), and the online code, level with
the held-out code at pass 2, sits 0.06 below it at pass 5. Joined to the route on all problems
(weights 13204, 15454, 9424, 6995 on `2^(−16)`), the pair reads 1.574 against the route's 1.591
(1.579 at pass 2), the markup 1.578 against 1.692.

**The read's carrier.** The first launch of pass 4 trained all 3,445 sections and then refused in
its held-out read: a read outgrew its 32-bit carrier. The ratio read makes the forward blind to the
read's scale, so each normalized step lengthens the read's material; the second level's largest
`‖r‖_rms` grew from 739 to 1,795 face units over passes 3 and 4. The raw read is now carried in
64 bits before its ratio is taken (`hnn::tower`, "The read's carrier"), and each pass's learner
rests before its held-out read, so a refused read keeps the trained pass. The refused launch lost
its pass 4; the relaunch from pass 3's state is the table's pass 4. The same refusal stopped the
wide probe below in its third held-out read.

**Width and steps.** On 1,000 problems, three passes each:

| tower | held out, passes 1–3 | online code, pass 3 |
|---|---|---|
| narrow (width 64, 64 modes, 256 contacts), sections of 128 bytes | 2.828, 2.687, 2.628 | 2.628 |
| twice as wide (128, 128, 512), the same rate `2^(−7)` | 3.036, 2.914, 2.877 | 2.863 |
| narrow, sections of 64 bytes (twice the deposits a pass) | 2.787, 2.684, 2.658 | 2.569 |

On all 6,726 problems, three passes each on the PC (8 threads each, its own founding keys):

| tower | held out, passes 1–3 |
|---|---|
| narrow, rate `2^(−7)` | 2.500, 2.403, 2.358 |
| twice as wide, rate `2^(−8)` | 2.437, 2.326, (refused in the read) |
| narrow width, four levels, rate `2^(−7)` | 2.616, 2.543, 2.487 |

On 1,000 problems neither width at the narrow's rate nor twice the steps helped by pass 3, and the
shorter sections fit the training text closer than the held-out text. On all problems the wide
tower, its step halved for twice the fan-in (agent-inferred: a normalized step moves each weight by
the rate, so a row's drive moves with its fan-in), codes below the narrow at both passes it read
(−2.5%, −3.2%); the four-level tower codes above it. Width pays once the data does; depth at this
rate does not. The PC's narrow run, founded from other keys, reads within 1% of this host's
(2.500, 2.403, 2.358 against 2.517, 2.404, 2.367).

**The wide tower to six passes, and wider still.** The wide tower's pass-3 training was lost to
the read's refusal; it continued on the PC from its pass-2 state with the 64-bit read:

| pass | online code over the pass | held out | question | answer prose | answer digits | markup |
|---|---|---|---|---|---|---|
| 1 | - | 2.437 | - | - | - | - |
| 2 | - | 2.326 | - | - | - | - |
| 3 | 2.235 | 2.266 | 2.388 | 2.162 | 2.818 | 1.739 |
| 4 | 2.179 | 2.220 | 2.347 | 2.121 | 2.770 | 1.652 |
| 5 | 2.139 | 2.192 | 2.314 | 2.088 | 2.806 | 1.633 |
| 6 | 2.110 | 2.162 | 2.286 | 2.066 | 2.711 | 1.586 |

At pass 5 the wide tower reads 2.192 against the narrow's 2.310 (−5.1%), and its gain a pass
(−0.060, −0.046, −0.028, −0.030) has not turned up. Twice as wide again (256 wide, 256 modes,
1,024 contacts, rate `2^(−9)`, its own founding keys) read 2.537 after one pass, above both the
wide tower's 2.437 and the narrow's 2.500 and above the wide in every region but the markup
(1.940 against 1.973), at 344 ms a section against the wide tower's 97 ms (each alone on the PC,
8 threads). Its certificate halved 56 times in its first 32 sections and twice after section 512.
Width 128 is the working width, and the tower stays on the host's cores (agent-inferred: the wide
tower runs a pass in 5.6 minutes on the PC's processor before the allocator repair below, and the
card is for a width that pays and that the processor cannot carry; width 256 has not paid at one
pass, and its second pass is not measured).

After six passes, from the first held-out question (110 bytes, `John volunteers at a shelter…`),
one draw:

```text
Jayet, has one-live from haves, gear two big solon balk in Millel's nuns, Tom's take won hours, how favid to=<<6/3=4>>4 founds.
#### 20

Milea friend in each dozen for Cando plags he number year. If Ben's spend car drine repances has 5-10 pead. Jenn, he eppitate, who nissonal card togeth, there are week, need need when Distus.  He previfled games, in a cards .7 been the First and a sspus are dryer
```

Two agreeing draws:

```text
The total number of money have a total of 10 dozen each of the second to cardet the curch to the total of the but of the subring $3 on each of the grop to a per for the drice to the resend typles of beads of the colls to sell bead on the number of shower to the play. How many cards to sold to clean white to make third the student for the compalls. If a park the cards $10 and a total of the balls, 
```

Neither recites: the longest runs found in the training text are 13 and 22 bytes (`, there are w`,
`The total number of mo`).

**Passes 7 and 8, and the join on all problems.** The wide tower continued on the PC for a
declared twelve passes. Pass 7 read 2.136 held out (Q 2.256, P 2.036, N 2.702, M 1.594; online
2.081). Pass 8 trained all 3,445 sections (its last 32 at 2.033 online) and rested, and its
held-out read refused: the residual stream `x + W₂v + b₂` outgrew its 32-bit carrier. The second
level's largest contact and return weights had grown from 3.4 and 0.68 at pass 6 to 15.5 and 15.5,
together; the cause is [the moments' stall](#the-moments-stalled) below (agent-inferred for this
tower from the matching signature: its states are on the PC). The receiving tree with its passage,
trained on all 6,726 problems on the PC (`train-modes`, depth 24, horizon `2^13`), reproduces the
container's state exactly (`a2eb835f…`, 0.410 bits a cell, 556 s). Read joined with it, frozen,
on the 747 held-out problems:

| tower | route | tower alone | joined | joined Q | P | N | M |
|---|---|---|---|---|---|---|---|
| wide, pass 6 | 1.591 | 2.158 | 1.559 | 1.679 | 1.339 | 2.399 | 1.490 |
| wide, pass 8 | 1.591 | 2.120 | 1.556 | 1.677 | 1.336 | 2.401 | 1.477 |
| narrow, pass 5 (above) | 1.591 | 2.301 | 1.574 | - | - | - | 1.578 |

(`read-joined` reads the whole held-out text as one stream, so it did not meet the refusal.) The
joined pair gains 2.2% over the route; most of it is markup (1.692 → 1.477) and digits (2.439 →
2.401). From the same question, with the pass-8 tower joined, two agreeing draws:

```text
Mary has 7 more at a time.  How many hours does he volunteer per two dogs as a should be the adults than the discount to and another the largest and for the class had 20 per tickets does he takes him the she ate on her per year the fourth difference in pollywogs are on the time he then the third dog ate a percentage and he can the fourth day and add all her the third of the total number of peanut 
```

and one draw:

```text
Mary the zoo dance any month at He also each foyer read 100 dollars a monthouses until Haroltadpopcorper tested a saves 3 of her brother largest and he made a direction value from all hike. He area, but hrs 1 tagon hold her arson she number of inches at 4 hours does in the time hour at twice as many hours at a sale.  If in Gab hens does he wras as him volleyen profit them more per per shops has 10
```

The agreeing draw is a run of GSM8K's phrases that repeats the question's `How many hours does he
volunteer per`. The longest runs found in the training text
are 28 and 20 bytes (` the total number of peanut `, `twice as many hours `). With the pass-6
tower the samples open on the same bytes (the same keys) and part at byte 78 (one draw) and 215
(agreeing draws).

**Release by agreement.** The samples above draw each class from the face itself. The samplers now
take a declared number `k` of agreeing draws: the class falls where `k` independent draws from one
face agree, so it is drawn from `p_i^k / Σ_j p_j^k`, exactly and with one key a class
(`agreement_face`; atlas `receiver.agreement-release`). At `k = 2` (the collision face) the same
learned faces release mostly words. A greedy left-to-right search of each sample against the
training text finds no copied run longer than 26 bytes (`the total number of the`).

The tower alone after pass 5, one draw:

```text
Jass was 2 years, the yenry per $96:.50 leaves, 30*.8= <<90/2=80>>80 add $2.50.
#### 675

#### 495

Miviled twice the find, the secles, wh bagreten's bill have A feyer juppris, are chools, Fraaddy 5 < 100/4=<<60/2=40>>40 bills, so bicceenelds.
They med number of nowlers asd house throw costs to stores and ande work amounts those in total. Necket to the buiches seandoms bag, how many and the trode 
```

Two agreeing draws:

```text
Saries the total number of the savis to the number of beads, how old a seas to the firss bagreen?
Frikin the the firs need to find how much a total of the pay he feet and to the total number of to hour and to the total number of the accentall his to store seclended to candy to the number of stores per hour to crown cards will have to the speed to the number of the shes for his to deces per to the 
```

Joined to the route after pass 5, one draw a cell:

```text
Jufflowing once.  How far esertrudahoes does he increases B time that costs $80 groups for $8 inches to matermelody lives she had 10 – 3 = <<72-240=180>>180 and are plant.
Hannah) has there than thers at what is the bombed an 8*10=<<23*3=200>>200 more union tricycles per game.
Her ton 1. How many double the access hadn't hit head arling hold 20 miles more needs in length of two now he has the se
```

Two agreeing draws a cell:

```text
Janet shopping out how many hours at a shelter the third and another the third and for the fourth of the fourth flowers he had a total of 2 charge for one apples at a pool holding many hours does he three burger for 3 hours does he will she allowance the number of the third are for 3 hours does he volunteers are a monthleen hours at the total number of the money the last two friends does he volunt
```

The joined release at two draws stays on the prompt's subject (a shelter, hours, volunteering) in
question-shaped clauses that do not form sentences. None of the four is readable. The prompt
(the first held-out question) reads at 3.692 bits a byte under the pass-5 tower against 2.930
under pass 2's, one question against the held-out 2.310.

**Time.** On the PC a section took about 51 ms narrow, 135 ms wide and 82 ms at four levels (8
threads each), against 173–191 ms for the narrow here on 4 cores. The resumed passes 3–5 took
668, 655 and 652 s a pass here; the relaunch's first 256 sections ran at 0.199 s against the
projected 0.191 s while a niced test build shared the cores, and the build was stopped instead of
the run (1306.5 s against 1,354 s projected, deadline 1,400 s: 0.96).

## Speed and receipts

A pass takes 93 to 99 s on the host, including the held-out read. The seven-pass run took 674.3 s
(projected 686 s from its own first pass, deadline 700 s: 0.98) and 94 MiB. An eight-pass launch was
stopped at 37.1 s when its first 128 sections took 20.9 s against the projected 17.6 s; it was
relaunched with one pass fewer and the same rate, not a larger deadline. The joined read took
172.6 s (projected 160 s, deadline 240 s: 1.08) and 792 MiB, almost all of it the route.
The source as committed, rebuilt from clean, releases both samples byte for byte (their output
hashes are in `SAMPLES.tsv`). `bash tools/gate.sh` passes, and the six `hnn::tower` tests pass in
release.

**The section waited on the allocator.** Stack samples of the four workers (gdb, 100 samples
during one narrow pass on 100 problems) found 35 in the allocator, most blocked on the main
arena's lock: the reads' fallible maps collected into vectors that grew by reallocation, and a
chunk that had crossed threads through a thread's cache takes its first owner's lock. Each such
map now collects into one exact allocation (`collect_exact`), the reverse scan sums a section's
outer products over its cells before they reach the gradient (`outer_sum`: integer addition is
associative, so the bits are those of one product a cell), and the workspace builds for the host's
own vector units (`.cargo/config.toml`). The pass (the 100 problems and their held-out read)
went from 12.8–13.2 s to 11.7–12.5 s with the sums, to 7.4–7.9 s with the exact collects and to
5.2–5.3 s built for the host, 2.4 times faster, and every build writes the same state
(`d74b4e78…`). The rows `speed_*` in `RUNS.tsv` hold the reads.

[`RUNS.tsv`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/RUNS.tsv)
and [`SAMPLES.tsv`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/SAMPLES.tsv)
hold every run with its binary, projection, deadline, wall time, peak resident set and hashes;
[`roles.py`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/roles.py)
writes the region of every byte. The tower's founding keys are 1 MiB read from the system's random
source; the samples draw from the 16 KiB key stream of the previous records' samples (hashes in
`SAMPLES.tsv`); the partition is `tools/gsm8k/partition.py`'s.

## The moments stalled

A contact that stops conducting on every byte of a section gets an exactly zero covector, and its
moments decay: `m ← m + release(g − m, 3)`, `v ← v + release(g² − v, 8)`. Released to the nearest
grain, the decay stops where `|g − m| < 2^2` and `|g² − v| < 2^7`, so a silent contact's moments
stay at `|m| ≤ 3` and `v ≤ 127` grains of `2^(−32)`, and its step `2^(−k) m/(√v + 2^(−32))` reads
that remainder as a covector of a quarter of the rate: `3 · 2^(24−7)/12 = 2^15` grains, `2^(−9)` a
section, in the sign of the contact's last covector, for every weight of the contact and its
return. Read from the narrow tower's states on all 6,726 problems (moments with `0 < |m| ≤ 3`,
`v ≤ 127`): none at pass 2, 980 at pass 3, 2,146 at pass 4, 1,994 at pass 5, almost all the weights
of two contacts (the first level's 57th and the second level's 126th). One weight of the first
moved −0.64 (pass 2), −2.45, −9.18, −15.91 (pass 5): `2^15` grains a section, `3,445 · 2^15 =
112,885,760` a pass, exactly. A silent contact's drifted weights meet the residual stream at full
scale once a byte makes it conduct again.

The moment now moves at least one grain toward its input when the rounded release is zero
(`hnn::tower::toward`): a constant input is reached exactly, and a silent contact's moments reach
zero (`m` in three sections, `v` in 127), so its step does too. A moment far from its input moves
by the rounded release as before; near it, by one grain more than before, at most `2^(−32)` bits
a unit (`a_silent_moment_reaches_zero`). The weights that drifted keep their values. Every run
before this fix trained with the stall; the 1,000-problem runs never reached it (no stalled moment
in the narrow tower's seven passes).

## The gated mode

An ungated mode forgets at its founded rate whatever byte arrives, so a level cannot hold a
quantity across bytes it should pass over. The gated mode (`TowerDeclaration::gated`; the law,
its adjoint and its passivity in `hnn::tower`, "The gated mode") keys each mode's decay to the
face it receives: a gate `r_t = 1/(1 + 2^(−q_t))`, `q_t = W_g x_t + b_g`, raises the founded
modulus, `λ_t = |λ|^(2 r_t) λ/|λ|`, and the push stays passive, `γ_t = √(1 − |λ_t|²)`. The gate
founds at zero material, where `r = ½` and the step is the ungated one. It adds 8,320 weights to
132,224 (a 64 × 64 gate and 64 biases at each level) and costs 1.5 times the time a section (130
against 87 ms on 100 problems). Its covector matches the code difference: a slope fitted over 16
steps agrees within 10% at every level's push and at every gate weight whose covector reaches
1/64 bit a unit (`the_gated_covector_matches_the_code_difference`).

On 1,000 problems, three passes each, the narrow tower from the same founding keys:

| tower | held out, passes 1–3 | Q | P | N | M (pass 3) | online, pass 3 | wall s (projected) |
|---|---|---|---|---|---|---|---|
| plain, before the moment fix (above) | 2.828, 2.687, 2.628 | 2.726 | 2.535 | 3.443 | 2.012 | 2.628 | - |
| plain | 2.842, 2.690, 2.647 | 2.745 | 2.565 | 3.423 | 1.999 | 2.638 | 140.7 (156) |
| gated | 2.743, 2.601, 2.542 | 2.656 | 2.442 | 3.366 | 1.872 | 2.509 | 227.8 (233) |

The gate lowers the held-out code by 3.5%, 3.3% and 4.0% a pass; by pass 3 in every region, most
in the markup (6.4%), while at pass 1 its digits read higher (3.680 against 3.449). Its two passes take about the time of the plain tower's three (151.5 s against
140.7 s) and read 2.601 against 2.647; its third reads below the ungated tower's sixth (2.554).
The moment fix moves the plain tower by +0.5%, +0.1% and +0.7%: no moment stalls in these
passes, so this is the one-grain step near arrived moments, within the 0.7% that separates two
founding keys on all problems. Decision (agent-inferred, from this measurement): the gated mode is
the tower's working law from here.

## Not claimed

The tower is classical state-space machinery at the codec's byte classes: ungated, a linear
recurrence of fixed decays (the LRU's); gated, the RG-LRU's selective recurrence. Its nonlinearity
sits between levels and in the gate, not in the state's lock. The join is a geometric mixture of two
faces. Nothing here grades a generation against an answer.

## Owed

- The agreement release `P(c₁ = … = c_k = i | all agree) = p_i^k / Σ_j p_j^k` in Lean (#410).
- The passive mode's bound `|h| ≤ √((1 + |λ|)/(1 − |λ|)) max|Bx|` under the step's `γ`, and the
  certified section's strict descent, in Lean (#410).
- The gated mode's bound under a moving radius, `|h_t| ≤ √((1 + ρ_max)/(1 − ρ_max)) max|Bx|` for
  `ρ_t ≤ ρ_max < 1` and `γ_t = √(1 − ρ_t²)`, and the moment law's arrival (`toward` reaches a
  constant input exactly), in Lean (#410).
