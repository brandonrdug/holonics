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

## Speed and receipts

A pass takes 93 to 99 s on the host, including the held-out read. The seven-pass run took 674.3 s
(projected 686 s from its own first pass, deadline 700 s: 0.98) and 94 MiB. An eight-pass launch was
stopped at 37.1 s when its first 128 sections took 20.9 s against the projected 17.6 s; it was
relaunched with one pass fewer and the same rate, not a larger deadline. The joined read took
172.6 s (projected 160 s, deadline 240 s: 1.08) and 792 MiB, almost all of it the route.
The source as committed, rebuilt from clean, releases both samples byte for byte (their output
hashes are in `SAMPLES.tsv`). `bash tools/gate.sh` passes, and the six `hnn::tower` tests pass in
release.

[`RUNS.tsv`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/RUNS.tsv)
and [`SAMPLES.tsv`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/SAMPLES.tsv)
hold every run with its binary, projection, deadline, wall time, peak resident set and hashes;
[`roles.py`](2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO_receipts/roles.py)
writes the region of every byte. The tower's founding keys are 1 MiB read from the system's random
source; the samples draw from the 16 KiB key stream of the previous records' samples (hashes in
`SAMPLES.tsv`); the partition is `tools/gsm8k/partition.py`'s.

## Not claimed

The tower is classical selective state-space machinery at the codec's byte classes; its
nonlinearity sits between levels, not in the state's lock. The join is a geometric mixture of two
faces. Nothing here grades a generation against an answer.

## Owed

- The passive mode's bound `|h| ≤ √((1 + |λ|)/(1 − |λ|)) max|Bx|` under the step's `γ`, and the
  certified section's strict descent, in Lean (#410).
