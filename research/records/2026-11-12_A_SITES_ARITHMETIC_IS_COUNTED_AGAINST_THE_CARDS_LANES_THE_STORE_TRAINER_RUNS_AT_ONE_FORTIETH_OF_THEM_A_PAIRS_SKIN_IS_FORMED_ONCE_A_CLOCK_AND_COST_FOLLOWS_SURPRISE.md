# A site's arithmetic is counted against the card's lanes: the store's trainer runs at one fortieth of them, a pair's skin is formed once a clock, and cost follows surprise

Refs #404 #407 #410. Status: [measurement, review and design; November 12], by the theory thread
that holds the PC's runs and the engineering. The measurements are one profiled read of the store's
trainer on the card (P49a: 100 sections, alone in its hold) and two count rulers on the host. The
count and the plan are agent-inferred from the kernels' source at `c1c3e5b62`. Nothing here is
built; the first repairs' rates are fixed as G116 before their build is read.

Owners named: the card realization (`crates/holonics-cuda/src/hnn/field.rs`: `run`, `batch`,
`tick_forward`, `tick_back`, `reverse`, `moments`, `blank_clock`, `region_octets`;
`crates/holonics-cuda/kernels/field.cu`: `skin_pair`, `skin_ij`, `pair_base8`, `contact_body`,
`field_exposure`, `field_contact_rows`, `field_contact_columns`, `field_pace_skin_back`,
`turn_dev`, `exp_series_dev`, `field_moment_paced_all`, `field_moment_return_paced_all`,
`field_moment_pace_back_all`, `affine_tiled`), the trainer (`store_train.rs`). Atlas: two
rows enter with this record, `tower.field-engine-count` (the count as a ruler) and
`deposition.cost-follows-surprise` (the lens's law, open); read with them
`tower.field-card-realization`, `tower.field-support-stride` and the lens's rows
`unicity.null-reading`, `birth.reached-covector`, `deposition.joule-ledger`,
`deposition.threshold-regimes`, `fluid.adaptive-conductance`.

Receipts (`..._receipts/`): `engine_count.py`, `engine_count.txt`, `profile_families.py`,
`profile_families.txt`; in the passage record's receipts `store_profile.txt` (the profiled read),
`store_leg1.txt` (the pass's one leg), `g115_run2.txt` (the census the count reads).

## 1. Why this record exists

On November 12 the store's trainer read 10.4 millionths of a second a computed site (G115), and
the report of it projected three hours for the 1 GB prefix and a day for 8 GB with the pass
already ordered. Brandon read that rate the same hour as harsh and its report as complacent. The
guides' method rule of that date followed: a rate is judged against a count of the law's
arithmetic over the lanes the card has, and a long projection is the realization's defect first.
This record makes the count, reads the trainer's own profile against it, and sets the engine's
order. The pass stopped after one leg of 3,000 sections (`store_leg1.txt`: 446.7 ms a section on
the mean, 1.00 batch a section).

## 2. The count

`engine_count.py` reads the declaration by part and a section's census from run 2's receipt
(1,900 sections): 40,741 computed sites a section, 13,158 of them open, 195 regions, and
45,786,666 pair-terms (a pair for each head and tick, the card's own counter): 1,124 a site, 70 a
site, head and tick. It counts multiplications at the width each term's information needs. The
unit is one product of two words of at most 32 bits with its 64-bit sum; a term the realization
forms on a 128-bit word or on a row of five to twenty limbs is counted at the narrow products its
integers need. [agent-inferred, from the kernels' source; every row stands until a measured
kernel replaces it]

| family | unit | products a unit | products a section |
|---|---|---|---|
| a site's maps, forward (words, values, probe, out, the pair contacts' two, the carry's gate, the contacts' return) | site and tick | 45,056 | 7.3e9 |
| their return (an outer and a transposed product a map, the probe read again) | site and tick | 94,208 | 1.5e10 |
| the small site kernels | site and tick | 2,688 | 4.4e8 |
| the paced heads' moments | site | 15,360 | 6.3e8 |
| the face through the encoding and its return | open site | 61,820 | 8.1e8 |
| a blank's clock | open site and later tick | 42,120 | 1.7e9 |
| the contact, forward (lock, score, share, numerators, skin) | pair-term | 95 | 4.4e9 |
| the contact, return (row, column, skin) | pair-term | 187 | 8.6e9 |
| the crowds | site, head and tick | 6,768 | 4.4e9 |

A section needs 4.4e10 narrow products, 1.07 million a computed site, and moves 8.9 GB through the
card's memory where a region's rows stand in one block's shared memory (a region of some two
hundred sites holds 13 KB of words a head).

**Against the card.** The RTX 4080 SUPER's published figures [from training; ceilings, never
measurements] are 10,240 lanes at 2.55 GHz, 2.6e13 lane-steps a second, and 736 GB a second of
memory. At six lane-steps a narrow product (two loads, the product's two halves, the sum and its
carry) the arithmetic floor is 10 ms a section and the memory floor 12 ms: 0.25 and 0.30
millionths of a second a site. The trainer's 425 ms a section is 42 times the arithmetic floor,
35 times the memory floor and 19 times their sum: it spends 255 lane-steps a narrow product.
**The realization stands at about one fortieth of the card's lanes.** Both ceilings are replaced
by measured kernels in the engine's first order (§6, step 0), and the ratio is restated then.

## 3. The profile, by family

`store_profile.txt`: 100 sections of the pass (its sections 2,001 to 2,100), every launch,
transfer and allocation timed alone; the profiled section costs 1.11 of the unprofiled one. A
section is one batch of 493 launches, 300 allocations and 38 copies. Kernels take 0.882 of the
elapsed time, copies 0.028, allocations 0.004, the host between them 0.086; short launches are
0.029 of kernel time. **The cost is wide kernels, never launches, allocations or copies.**

| family | ms a section | share of kernel time | counted products | lane-steps a product |
|---|---|---|---|---|
| the contact (exposure, the row sums on five and six limbs, the return's rows and columns, the paced skin's return, the spread) | 195.9 | 0.473 | 1.7e10 | 295 |
| the paced heads' moments and clocks | 87.2 | 0.211 | 6.3e8 | 3,641 |
| a site's maps | 70.8 | 0.171 | 2.3e10 | 81 |
| the blanks' clocks | 18.2 | 0.044 | 1.7e9 | 285 |
| the small site kernels and the carry circles | 36.4 | 0.088 | 4.4e8 | |
| the faces | 5.9 | 0.014 | 8.1e8 | 188 |

The largest entries: `field_contact_rows` 0.137, `field_pace_skin_back` 0.094, `field_contact_l5`
0.093, `field_contact_columns` 0.079, `field_moment_pace_back_all` 0.053, `field_outer_x32`
0.043, `field_transposed` 0.042, `field_affine_tiled_x32` 0.041,
`field_moment_return_paced_all` 0.040, `field_moment_paced_all` 0.039, `field_exposure` 0.036.

Two readings. The site's maps hold half the count and a sixth of the time: they are the nearest
family to the card (81 lane-steps a product) and still thirteen times the floor. The moments hold
a seventieth of the count and a fifth of the time; the contact holds two fifths of the count and
half the time. The furthest families are the ones that form a pair's quantities.

G115's fit could not see this: a section's sites and pairs keep a near-constant ratio under the
section's bounds (the fit explained 0.641 of the variance), so "the time follows sites" placed no
entry. A profile by entry does.

## 4. What the heaviest entries compute (read at source)

**A pair's skin is formed again for every use.** On a paced head whose pace is not plain,
`skin_ij` calls `skin_pair`: two reads of the clocks' variation `σ` (16 octets each), six reads of
the two sites' addresses (`2π σ = q k + r`), a borrow and a rounding on 128-bit words, and the
exponential's resident face. The value depends on the pair, the head, the mode and the clock
alone. It is formed in `pair_base8` for the lock (eight modes a pair), in `contact_body` for each
numerator's carry (a lane an entry), in `field_contact_rows` for `δp` (eight) and again for the
probe role (a lane an entry, sixteen pairs a chunk), in `field_contact_columns` twice a lane and
receiver (`skin_raw`, then `carried_ij`), and in `field_pace_skin_back`. In warp time a paced pair
pays about 2.5 runs of that sequence over a tick's forward and return, each of some 150
instructions and 9 gathers, where the rest of the row's and the column's return is about 40
instructions and 3 gathers a pair. [agent-inferred from the source: on a paced head the skin is
most of the rows' and the columns' time; G116 (d) tests it by a profile by head before anything
is built] Two of the four heads are paced.

**A turn's phase is summed as a series for every use.** `paced_phase` reads `turn_dev`, which off
a whole clock sums `exp_series_dev`: some twenty steps, each four 128-bit products, two releases
and two quotients. A site and moment mode read 11 near phases and one absolute phase, with 11 near
skins and up to 14 far ones, and the same phases are formed three times a clock
(`field_moment_paced_all`, `field_moment_return_paced_all`, `field_moment_pace_back_all`). Those
three entries are 0.132 of kernel time: about 160,000 lane-steps a thread at the ceiling, against
my count of 95,000 instructions for 13 series a thread. The series' first argument is zero in
every call, so half its products are products by zero.

**The row's sums run on five limbs.** `contact_body` holds a row's mass and numerators as five to
twenty limbs of 64 bits (the row's spread chooses the entry; here five, 0.12 of sections' launches
six), multiplies each term on two limbs and divides once a pair for its share. That is the law as
declared (a row's carrier as wide as its terms' spread); narrowing it is a change of law (§6,
phase 2).

**The site's maps are separate launches a map**, each loading its weights into shared memory and
reading its input again: three maps read one chart (`q`, `v`, the probe), three the other (the
pair contacts' two and the carry's gate), and each return runs an outer and a transposed launch a
map. Read further at source the same day (after G116 was fixed; step 4's subject, its guess fixed
once step 0's yardstick is read):
- *The forward map* (`affine_tiled`, 22.6 ms a profiled section, 80 lane-steps a counted
  product). A block is 256 threads, one a cell (site, output), so it passes 4 sites of a map of
  64 outputs and 2 of a map of 128. The driver's grid is the sites over that count (`affine`:
  10,186 or 20,371 blocks at 40,741 sites), so every block makes one pass and loads the whole map
  for it: a launch reads 41.7 million words of weights for 2.6 million words of input (166.9
  million for a pair contact's map). The kernel's loop already lets a block make many passes; only
  the grid forbids it. A site's carrier bound is then scanned by one thread a site over the
  map's 64 or 128 inputs while the block's other threads wait.
- *The return's transposed product* (`field_transposed`, 17.4 ms). One thread a cell (site,
  input) sums over the outputs with every product on 128-bit words, the weight read from the
  card's memory at the map's stride and the site's covector row read again by each of the row's
  threads. It has no 64-bit path under a bound, where the forward has one.
- *The return's outer product* (`outer`, 22.7 ms; its bound 8.1 ms). One thread an entry and a
  tile of 64 sites reads both operands from the card's memory at their rows' strides, a word a
  site, multiplies on 128-bit words and adds once to the entry.

Each is a realization (the same integers): a block that keeps a map through many passes, the
bound read in parallel or carried from the chart's producer, the return's operands a tile in
shared memory and its products on 64-bit words wherever the bound that is already read proves
them.

## 5. The lens: cost follows surprise (Brandon, November 12, 20:31Z)

[project-postulate, in the agent's words] No one average rate speaks for every byte. Input that
the constitution already codes should come to cost almost nothing, as a path of least mutual loss
between what the network holds and what it receives, and unevenly: with phase transitions, with
landmarks that are locally as compressible as they can be and that induce higher classes of
crossing, with modes learned from unlike material recombining, and with a prediction changing
what it predicted once it is made.

*The objects.* A reading whose surprise is zero constrains nothing (`unicity.null-reading`); the
comparison reaches a chart scaled by the surprise mass (`birth.reached-covector`); no flux is no
dissipation (`deposition.joule-ledger`); a contact's conductance grows where flux crosses and
relaxes where none does (`fluid.adaptive-conductance`); a driven threshold medium snaps, crackles
or pops by its disorder (`deposition.threshold-regimes`). The deposit is linear in the covector
`p − q`, so the law already prices a place by its surprise.

*What the realization does.* Every site is computed forward for four ticks and returned through
every contact. The face covector is `p − 1[class]` on 24 bits (`field_face_covector`), so a row
is zero only where every other class falls under `2^(−25)`: a predicted place pays the same 10
millionths of a second as a surprising one. A flat price a byte is the build's defect, and a rate
is not reported as one mean again: it is stated as the forward a site and the return a unit of
surprise, by slice.

*The test.* `read-store` (P49) counts each slice's compared places by the octave of their code
(counts of counts), on the crossing's state, after 2,001 sections and after 5,001: the share of
places in the near-zero octaves, whether it grows, and whether it grows smoothly or in steps.

*The law it asks for* (not built; its own guess after that read): a place whose covector falls
under a declared grain releases it by partition, the released mass printed as the remainder, and
the return runs on the places that remain. The grain is carried in the learner's state. A zero
row skipped is a realization and keeps every bit; a row released under a grain changes bits and
is law.

*What does not transfer.* Recognition is the face read through the constitution as it stands at
that moment. No table of passages seen enters (a cache, and it would recite). The next section's
price is no reading of learning for the same reason his market gives: the deposit has already
moved what it predicted, and adjacent sections continue the same documents.

## 6. The engine's order

Each step is one attempt with its receipt. A realization keeps every bit and enters the line by
reproducing it (run 2's first 600 sections from run 1's `STATE.101`: lines equal, timings aside,
and `STATE.600` and `MEAN.600` byte for byte), with the card against the host where a kernel
changed, and is timed inside one hold against a control run twice. The section's bounds are law
in the pass line and are not changed.

**Phase 1, realizations.**
0. Two measured yardsticks and a profile by head: a narrow-product kernel at its best (products a
   second) and a sweep of the card's memory (octets a second) replace §2's ceilings; the profile's
   per-head launches are named by head, so a paced head's cost is read beside a still one's.
1. A pair's skin once a clock: formed for each support pair and each crowd edge of a paced head
   by one launch after the clock is set, held at the region block's dense address, and read by
   the lock, the numerators, the rows, the columns and the skin's return. Formed again once for
   a tick's return (the clock is the tick's).
2. A turn's phases and the moments' skins once a clock, kept with the tick's clock and read by
   the moment, its return and the clocks' covector.
3. The phase series on the words its bounds prove (its zero argument dropped, 64-bit products,
   the quotient by a read divisor).
4. A site's maps fused by the chart they read, and a map's outer and transposed products in one
   launch.
5. A batch's launches, allocations and zeroing fused where one follows another on the same grid.

**G116, fixed before any of these is built** (the guess file of the November 11 record on timed
builds, `guess_capacity_44_55.txt`; a profiled section is 467.5 ms, an unprofiled one 420.8):
- (d), the premise's test, read first from step 0's profile by head: the two paced heads hold
  0.78 (0.70 to 0.86) of `field_contact_rows`' time. Under 0.65 the skin is not the rows' cost,
  step 1 is not built and the rows' kernel is read again.
- (a) after step 1 the contact's family reads 130 ms a profiled section (110 to 155), from 195.9;
- (b) after steps 2 and 3 the three paced moment entries with their fill read 18 ms (10 to 25),
  from 54.6;
- (c) after steps 1 to 3 the unprofiled section reads 318 ms, 7.8 millionths of a second a
  computed site (7.2 to 8.6), from 10.3, with one batch a section kept.

At 7.8 the realization stands at 14 times the sum of §2's floors, where it stands at 19 now.
Steps 1 to 3 are about 1.3 times of a distance of about 20, so they earn no pass; they are first
because their two families stand furthest from their count, and each profile names the next
entry.

**Phase 2, laws at declared widths** (each with host and card parity, its atlas row and its Lean
obligation named in #410; none before phase 1's profile):
- cost follows surprise (§5);
- ~~a row's carrier anchored at its peak, its terms released at a declared tolerance with the
  remainder accounted, in place of five to twenty limbs~~ (struck November 13: the November 1
  record's §14.11 retired a carrier at a fixed fraction of its row's peak, since a row is a
  series and no term is released without its remainder; what the limbs can give with every
  bit kept is §9);
- the pair store on its support (`tower.field-support-stride`), a region's rows in one block.

**The pass.** The pass over the 1 GB prefix waits until the engine stands near its count. The bar
told to Brandon is 1 millionth of a second a site before any pass over 8 GB (1.8 times §2's sum
of floors: a guess until step 0's yardsticks replace the ceilings), and by §5 it is restated in
two parts once the dark share is read. Short reads that show writes from held prompts go on.

This replaces the order of builds in the review record of this date (its items 2 and 3 exchange
places, and item 3's subject is this section).

## 7. What this record does not read

The level. No figure here says what the constitution holds; the held reads and the writes by
slice do (P49). The count's rows are from the source and not from a measured kernel; the card's
ceilings are published figures. The skin's and the phase's shares of their entries are counted
from instructions and are G116's subject. Whether the constitution's size or the step's rate
limits the level is not read here.

## 8. The pair kernels' layout was read on copies before any rewrite, and their multiple is the law's (G138, November 13)

After step 6 a section reads 279.4 ms, 6.9 times the bar, and the contact family holds 115.6 ms of
a profiled section in 72 launches (`p57_schedule.txt`). The layout of §6's phase 2 and of the
forecasts (a pair's record in walk order, a region's rows resident in its block, the forward's
entries as one launch and the return's as one) was the next build by G131's rule. Before any
rewrite its mechanisms were read one at a time (`p59_copies.txt`, with `p59_copies.py` and
`g138_lines.py`; the order P59, the guess G138 fixed before the read).

**The instrument.** A copy of each pair entry, generated from the entry's own text with every
substitution counted, launched immediately before its entry on the entry's words, its outputs in
scratch arrays that start as the entry's. One mechanism a copy and a null copy of each entry; the
copies are compiled only under a feature, and with it off the kernels' PTX is main's byte for
byte. One hold of the card: a profiled control, the copies' run, a profiled control, sections
2,001 to 2,100 from run 2's `STATE.1900`; all three print the line's 100 section lines and end on
the line's state and mean. The null copies lower as their entries and give their words (0
differing words over every array). A null copy reads 0.90 to 1.00 of its entry's controls by its
place before the entry alone, so each ratio is given over the controls and, in brackets, over the
null copy.

| mechanism | rows (30.74 ms) | columns (25.65) | forward contact, five limbs (26.39) | skin's return (16.86) | exposure (8.57) |
|---|---|---|---|---|---|
| source rows resident (each load of another site's row reads the warp's own) | 0.881 [0.881] | 0.852 [0.946] | 0.951 [0.982] | 0.888 [0.941] | 0.938 [0.980] |
| a pair's words in walk order | 0.967 [0.967] | | 0.963 [0.994] | 0.945 [1.001] | 0.891 [0.931] |
| the reductions as plain stores | 0.937 [0.937] | | | 0.885 [0.938] | |
| the columns from a record in column order | | 0.565 [0.627] | | | |

The columns from their record read 0.422 on the paced heads and 0.839 on the still ones; the
record was laid by a pass of its own at 14.1 ms a section, outside the copy's time. With each
entry at the product of its copies' ratios and the small entries as they stand, the family reads
91.1 ms from 118.9 in this hold's controls by the ratios over the controls, and 98.7 by the ratios
over the null copies: 0.77 and 0.83 of itself. Summed over the entries and read over the null
copies, resident rows remove at most 6.8 ms a section, walk order 1.9, plain reductions 3.0 and
the columns' record 9.6 before its own cost. Of G138's 17 parts 15 held; the exposure's resident
rows and the family's total missed, both above.

**What it says.** The pair kernels are bound by their arithmetic and their walk, never by where
their words lie. The forecasts by a count of gathers (27.5 ms and under for the family) overstated
what a layout takes, as G120 had read of the rows. In the controls the forward contact at five
limbs lowers to 9,720 instructions with 2,137 multiply-adds, 524 wide ones and 778 spill stores;
the rows to 7,680 instructions with 1,987 and 632 on 128 registers.

**The rule applied** (fixed before the read: the family over 90 ms). The family's form stands and
no layout is built on it. Its multiple is the law's, each part with its record first:
- *the contact's declared widths.* A row's carrier is `row_bits` and its spread: 62 bits of a
  term's face, 62 of its weight, 64 of a value, and the counts, 225 and the spread, so five limbs
  hold a spread of 95 and no row's own spread lowers them. The bits ruler reads a value at 23
  bits, a unit word at 18 and a score at 23 (`p54_word_bits.txt`). The weight is `2^62` or a
  crowd's count times it in every term of the present law (`agent-inferred`, from
  `Field::contact`'s two pushes), a factor the row's one quotient cancels. The record owed
  restates each width from what consumes the word, with §14.11 of the November 1 record kept:
  every term enters the row's sums, no peak is subtracted and nothing is released without its
  remainder. A carrier anchored at a row's peak that released the terms under it to nothing is
  the build that section retired.
- *the pair-terms a site.* A site holds 1,124 pair-terms (70 a head and tick). The level above
  takes the far field of a place into an epoch's word, and the length of a region under it is
  the design record's subject after the opening's comparison is read (G139).

The columns' record is the one mechanism past 5 ms a section. It is carried into the build that
rewrites the support under those two laws, where the forward entry writes it, and is not built as
a step of its own on kernels about to be rewritten (`agent-inferred`).

**The next realization: a site's maps** (G117, fixed before its build; the order P61). The profile
outside the contact is flat except for one family. A site's maps hold 56.3 ms a profiled section
in seven entries and stand at 4.03e11 products a second, where the card's measured yardstick for
a map of their shape reads 1.46e12 with one thread a cell and 5.19e12 with one thread four
outputs of four sites (`p50_step0.txt`). No step has changed them. Read at source: the forward
map holds its weights and four sites' rows in shared memory and is the nearest to the yardstick
(6.9e11 a second on a map of 64 by 64); the transposed map reads every weight and every covector
word from the card's memory once a product and sums in 128 bits; the outer sum reads each word of
a tile of 64 sites once an entry, 4,096 times, and adds each entry's partial by a 128-bit atomic
step once a tile. The build gives the three kinds the yardstick's form with the same integers
(a 64-bit covector as two 32-bit limbs whose sums stand in 64 bits where a tile's magnitudes
prove it). G117 guesses the family at 20 ms (13 to 32) and the section at 0.885 of its control.

## 9. The contact's widths, read from the source and the logs before any record of them orders a build (November 13)

§8 owed a record that restates each width of a contact row. Its premise is read first from what
the tree and the receipts already print.

**What the source holds** (`contact_body` and `SeriesRow` at main 4f1347a6b):
- *The multiplier.* It is `2^62` in every pair's term and in a crowd's value, and a crowd's count
  times it in the crowd's mass (`Field::contact`'s two pushes; `coef_of` at five places in the
  entry). A nearest quotient keeps its bits when its numerator and its divisor lose an even
  common factor `K`: `⌊(|x|K + mK/2)/(mK)⌋ = ⌊(2|x| + m)/(2m)⌋`, and `⌊(|x| + ⌊m/2⌋)/m⌋` differs
  from it only where `2|x| + m` is a multiple of `2m` with `m` odd, which an odd number never
  is. So the currents and the shares at multiplier 1 are the same integers, and the 62 bits are
  the carrier's, not the row's (`agent-inferred`; the lemma is owed to #410 beside the grouped
  row's equality).
- *A value.* Its 64 bits are `fit64`'s. The bits ruler reads a framed value at 23 bits and a
  crowd's prefix at 30 (`p54_word_bits.txt`).
- *The limbs.* The launch takes them from the widest row of the launch, which the host fetches
  once a tick, where §14.11 of the November 1 record says the width is the row's.
- *Once a pair.* The entry reads the exponential's face and forms the coefficient twice (for the
  terms, then for the shares), and forms a crowd's score twice.

With the multiplier gone and a value on one 32-bit limb where its row's read proves it, a row's
fixed part is 131 bits against 225: three limbs hold a spread of 61 where five hold 95. Every
form here keeps every bit, so these are realizations. §8 called the widths a law's subject; that
word was wrong for them and is corrected here. A face's 62 bits and a share's 63 are the law's
and are not touched.

**What the logs already say of the gain.** P59's controls ran the forward entry at five limbs in
351 launches and at six in 49 over 100 sections: 26.39 and 4.02 ms a section, so 7.52 and
8.20 ms a launch. A limb costs 0.68 ms a launch, 9% of the entry (`agent-inferred`: the launches
at six limbs are the ticks whose widest row is wider, and nothing else is known to differ). Two
limbs fewer is about 5 ms a section of the forward entry's 30.4; the narrow numerators and the
once-a-pair forms add a few more. The returns' wide forms rest on a share's 63 bits and on the
covector `dy`, which no ruler has read.

*The copies' ruler set aside* (November 13, P61's first item): `claude/contact-copies` is kept by the
tag `archive/claude/contact-copies` at `74c049cb4`. It is not merged: its copies are the contact's
entries as they stood, bound to asserted substitution counts, and those entries are to be rewritten
under the widths' law, so in the trunk the copies would go stale or hold the rewrite back.

**What follows.** The widths are worth about 10 ms a section of 267, a tenth of the pair family
and not a multiple. They are ordered after the site maps, with the reading of `dy` first. The
pair family's multiple lies in the count of pair-terms alone: which rows are computed, and which
sources a row meets. That is the design record's subject
([§4.8 there](2026-11-13_A_LEVELS_SITES_ARE_THE_EPOCHS_OF_ITS_NEWS_BEGUN_AGAIN_AT_EACH_OPENING_ITS_CLOCK_IS_THE_NEWS_BETWEEN_THEM_A_PLACES_NEWS_IS_READ_AT_ITS_CAVITY_FACE_AND_EACH_NAVIGATOR_KEEPS_ITS_LOCATED_CLOCK.md), G140).

**The ruler build of §8 is kept by tag, not in the trunk.** The contact's copies
(`tools/contact_copies.py`, 74c049cb4, gate 1 passed) are the text of the entries as they stood,
bound to asserted substitution counts. In the trunk the generated header would go stale at the
first change of an entry or hold that change back, so the branch is set aside by tag
(`archive/claude/contact-copies`, by the census tool on the PC, the first item of the order P61).
The tag's commit is owed here in one sentence once the PC reports it.
