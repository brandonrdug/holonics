# The engineering readings of November 20 and the first two realization changes

Receipts for the engineering report's work list (§11 of the report of November 20), read on the PC (RTX 4080 SUPER, the host's 24
threads) against the store line at width 224 (seven face lanes of 32), pumped, laps Y70 and L71. Every figure is a reading; no state
entered the line.

## A2: the arithmetic yardstick at today's declaration (`engine_count_L71.txt`)

`tools/engine_count.py` is the count of November 12 (its receipt's `engine_count.py`) read at today's parts, with the pump's chart
joining the site maps and the carry circles' scans counted as their own family, beside the card's time by family from the trace of 40
sections (A4). Floors at the measured yardsticks of November 12 (5.1914 × 10¹² narrow products a second, 5.7247 × 10¹¹ octets a second):

| family | floor ms a section (products, octets) | card ms a section | over the larger floor |
|---|---|---|---|
| site maps | 91.3, 35.4 | 196.3 | 2.2 |
| contact and crowds | 1.9, 3.4 | 106.1 | 31.5 |
| carry scans | 0.9, 18.1 | 82.1 | 4.5 |
| moments and clocks | 0.3, 0.4 | 38.2 | 104 |
| site kernels, small | 0.05, 1.0 | 24.4 | 24 |
| face and blanks | 2.6, 2.2 | 21.3 | 8.1 |

The section's floor is 157 ms (97 on the products, 60 on the octets) against a lap's mean section of 586 ms: 3.7 times the sum, where
November 12's declaration stood at 17.8. The declaration moved the floor: the face width went from 64 to 224, the contacts from 128 to
1,088 and the carry circles from 32 to 512, so the site maps, whose products grow as the face width times the contacts and circles, now
hold 94% of the products (3.76 million a site and tick). The card's kernels sum to 468 ms a section (2,800 launches); the rest of the
section is the card idle (A4).

## A4: the card's idle time (`trace_idle.txt`, `trace_gaps.txt`, `phases_657099e79.txt`)

Under Nsight Systems the card stood idle 21.9% of the window (40 sections of train-store from Y70's end, build 657099e79). The gaps over
a millisecond, by the activity on either side:

- 63.9 ms a section between the run's last fetch and the next run's material upload: the host's deposit between sections (its parts
  summed to 57.6 ms a section in `STORE_DEPOSIT_PARTS`, eight whole-layout passes over 1,859,961 entries, four of them serial);
- 19.5 ms a section at the batches' edges (three a section): the host packing the next batch's lists (`stage_lists`, 4.5 ms a mark);
- 8.4 ms a section between two fetches at a batch's end.

The groups of a section (the law's regions and the known streams) join on the host in under a millisecond, not the 31 ms the first look
supposed.

## A5: the material's carriers (`carriers_L71.txt`)

On L71's end state, each family's bits (the length of an entry's magnitude). The map families (grain `2^(−24)`: q, v, out, the contacts'
a, b and W, the read, the carry's and the pump's charts, the probe) stand at a median of 18 to 22 bits, 99% at 22 to 25 bits, and their
largest at 23 to 28 bits; the biases and face families (grain `2^(−16)`) at 99% within 12 to 21 bits. Over every entry, 95% stand within
22 bits and 99.9% within 25. So a map's weight is three to four digits of eight bits, never two. A tensor-core realization of the site
maps cuts each weight into four limbs: against four-limb operands a product is sixteen eight-bit products, which at the card's published
dense rate (418 × 10¹² eight-bit operations a second, 2.09 × 10¹⁴ products) is 1.3 × 10¹³ narrow products a second, 2.5 times the
CUDA-core yardstick and 5.4 times the maps' present 2.4 × 10¹²; twice that where the operand is two digits (`agent-inferred` from the
published rate). The maps run at 46% of the CUDA-core yardstick now.

The operands (`pass_carriers_L71.txt`): one host pass of the same state over 240 sites cut from a public text (`docs/THE_ENGINE.md`)
through the line's codec, five places in eleven open, every tick kept. The chart's read stands within 19 bits, the words and values
within 22, the contacts' operands `a`, `b`, `c` within 19 to 23, the carry circles' `q`, `ℓ`, `κb` and `Q` within 20 to 21, the pump's
read within 18, the gates `γ` and `η` (on `2^(−30)`) within 30, and the state within 22 to 26 by the fourth tick. Every carrier the card
keeps a tick is held in a 64-bit word; each fits in 32 bits with room, so the tick's tape (about 68 KB a site and tick at this
declaration, the contacts' operands 26 KB and the carry circles' 37 KB of it, which is what cuts a section into three batches) is twice
as wide as its information (`agent-inferred`: one region of public text; the line's own passages are read before a carrier is narrowed).
A three-digit operand against a four-digit weight is twelve eight-bit products.

## The first change: the deposit in one pass a family (`learner.rs`, `deposit_pass`)

The transfer, the external step and its price, the covector's grains, the moments, the step and its prices, eight passes, are one
parallel pass a family. Every entry reads only its own moments, rate, remainder and covector, and each price's terms meet on their
family's grain and are released once a family, so the chunks give the same bits in any bracketing.

- The tiny fields: `the_deposit_in_one_pass_is_the_serial_passes_bit_for_bit` (four cases, with and without a step before and a carried
  remainder, the families cut every seven entries so the chunks' bracketing is read).
- The line's own state (L71's end, 1,859,961 entries, 65 families): `the_deposit_pass_on_a_lines_state`, every bit equal, the serial
  passes 111 to 117 ms on one thread and the pass 15.5 to 18.2 ms on 24.
- On the card (`dep1.txt`, `dep1.sh`): 24 sections of lap L71 trained from Y70's end reproduce the lap's own lines, every field but the
  timings (`GATE_REPRO sections=24 equal=24 EQUAL`), the transfer and the external price among them.
- One balanced hold of 40 sections each from Y70's end (control, build, build, control): the section 597.7, 578.7, 579.9, 592.9 ms over its
  last 30 sections, so 579.3 against 595.3, 16 ms (2.7%) shorter where the control's own spread is 4.8 ms. In the deposit's parts the
  eight passes summed to 36.6 ms a section in the control and the one pass took 19.5 ms in place (`deposit_pass_ms` 780.6 over 40
  sections), more than its 16 ms alone because the card's driver threads share the host.

## The second change, set aside: the batches' lists packed one batch ahead (`dep2_stage_ahead.patch`)

The host part of a batch's staging (its lists and tables, built from its regions and the declaration alone) was packed on a host thread
one batch ahead, so the card would read a batch while the host built the next one's lists. It kept every bit (`dep2.txt`: the card
crate's suite, 27 passed; the reproduction of L71's 24 sections, EQUAL) and bought nothing: in one balanced hold 580.7, 582.5, 577.6,
578.8 ms, so 580.0 against 579.8. Why, read from its phases: a section is two runs (the law's regions in two batches, the known streams in
one), so only one of its three batches has a batch before it to stand behind; and the other three `stage_lists` marks a section are the
tower's level, whose staging follows its cut (`level_cut`) of the news the card has just returned, a dependency of the card on the host
that no host thread can run ahead of. The batch edges' gap (19.5 ms a section) is the level's cut on the host and the first staging of
each run; its lever is the cut on the card, or a run of the section's two groups as one. The patch is kept as an instruction for that
build, which will need it.

## The card's eight-bit tensor products (`imma_yardstick.cu`)

A yardstick of `mma.sync.aligned.m16n8k32.row.col.s32.s8.s8.s32` with each thread's fragments in registers, beside `dp4a` on the CUDA
cores, alone on the card under the lock (three runs): 1.963 to 1.970 × 10¹⁴ eight-bit products a second on the tensor units (94% of the
card's published dense rate), 4.07 to 4.14 × 10¹³ by `dp4a`. Against the CUDA-core yardstick of November 12 (5.19 × 10¹² narrow products
of 32 bits), a 32-bit product cut into four digits a side is sixteen eight-bit products, so 1.23 × 10¹³ such products a second, 2.4 times.

## The third change: the site maps on the tensor units (`field.cu` `map_tile_tc`, `contact.rs` `affine`, `transposed`, `tc_planes`)

A word under 2,139,062,144 in magnitude is its four signed digits of eight bits; each digit pair's products over 32 terms are one
`mma.sync.m16n8k32.s8.s8.s32`, the four pairs of a place summed in one 32-bit word, the seven places joined on 128 bits before the bias
and the one release. Integer sums with no release between them, so the tile form's integers in any order; a tile with a word past the
digits (or a map of 2¹⁵ terms or more) is summed in the wide form. The weights are cut into digit planes once a launch
(`field_tc_planes`); the forward map's 32-bit sites too, and the transposed map's 64-bit covector is cut as each chunk is staged.

Its variants, each alone on the card at the width-224 line's shapes (10,000 sites; `the_site_maps_at_width_224_on_the_tensor_units`,
`tc_bench_v2.txt`, `tc1_v3.txt`, `tc2_v4.txt`), in µs a launch, the least of 60:

| map | tile form | v2: planes, in place | v3: staged, outputs through shared memory | v4: planes, through shared memory | v5: planes forward, staged transposed, in place |
|---|---|---|---|---|---|
| forward 1088 × 224 | 640 to 649 | 390 | 563 | 497 | 479 (beside gate 1) |
| transposed 1088 × 224 | 660 to 687 | 551 | 534 | 704 | 533 (beside gate 1) |

The forward map at the large shapes stands near its octets: 10,000 sites by 1,088 outputs of 64 bits is 87 MB written a launch, 170 µs at
the card's write rate, where its products at the tensor units' rate take 200. So the next lever on the maps is the width of their
carriers, not their products.

Every variant reads the definitions' integers in all 96 cases of `a_sites_maps_in_the_tile_form_read_the_definitions_integers` (the
wide fallback forced by words past the digits, a refused site, masks, `add`, `accumulate`), every route's outputs equal word for word in
the bench, and v3, v4 and v5 reproduce 24 sections of lap L71 from Y70's end (`GATE_REPRO … EQUAL`). The section, in balanced holds of
40 sections against the merged build (control, build, build, control): v3 586.6 against 604.6 (−18.0; this hold and the earlier ones of
the day ran beside the line's reads, about 90 ms a section slower than alone); v4 492.4 against 510.4 (−18.0, alone); v5 514.1 against
542.9 (−28.8, with gate 1 running on the host beside it, so read as incomplete); v5 again alone (`tc5_v5_drift.txt`): its four runs
drifted 523.1, 487.4, 517.5, 564.3 with the host idle and the card heating from rest, a control spread of 41 ms that resolves nothing. The
hold that decides (`tc6_v5_warmed.txt`, `tc6.sh`): a warm-up of 40 sections not read, then the guide's eight runs in balanced order, the
card at 57 to 58 °C and 2,805 MHz throughout: the control 530.9, 531.8, 531.6, 534.4 (532.2, spread 3.5), the build 512.7, 512.2, 512.6,
512.4 (512.5, spread 0.5), so 19.7 ms (3.7%) shorter. Guesses: v3 30 to 50 ms (missed), v4 25 to 40 (missed), v5 20 to 35 (missed at its
lower edge). The holds of the day before this one had no warm-up; their differences stand inside one hold, their levels do not.

The merged build's trace (`trace_idle_merged.txt`, `engine_count_merged.txt`, `trace_merged.sh`): the card idle 18.1% of the window (21.9%
before the two changes), the kernels 414 ms a section (468 before) over 3,414 launches (the digit planes add about 600), the site maps 156.7
ms a section at 1.7 times their floor (196.3 and 2.2 before), the other families as before within the card's state (the contact 98.6 ms,
the carry scans 74.6, the moments and clocks 36.5).

## The tick's premise: the trained tick does not contract (`tick_residual_L71.txt`)

The hardware record's §8 asks, before any build, whether the trained tick contracts, so that a series could be released at a tolerance and
the return's tape kept once instead of each tick. `the_trained_ticks_residual_by_tick` reads L71's end state with its ticks raised from 4
to 12 over the same 240 sites of public text as the carriers' census: for each tick, the state's step against the state and the chart's
step (the ray every reader reads) against the chart, as sums of squares over the sites.

- The state's step stays at 0.96 to 0.996 of the step before from the fifth tick on: the state grows by a near-constant step, as a held
  source does, and never settles.
- The chart's step falls 1.41, 1.11, 0.75, 0.11, 0.013, 0.0030, 0.0011, 0.00049, 0.00026, 0.00015, 0.00009 of the chart's energy (its
  root: the chart moves 11% at the fourth tick, 5.5% at the fifth, 1.6% at the eighth, 1.0% at the tenth), and the ratio of successive
  steps climbs from 0.11 at the fifth tick to 0.62 at the eleventh. A contraction would hold that ratio under a steady factor; a climb
  toward one is the running mean's harmonic falloff (`tower.field-tick-running-mean`).

So at the built tick's form no tolerance releases the tape: the first link that slips is the tick's form, as §8 says it would be where the
trained tick does not contract, and its candidate is an averaged step with the maps' gains bounded in the lanes' metric, a change of law
read as an arm (`agent-inferred`: one region of public text on one saved state; the line's own passages and the largest gain by power
iteration are the next reads).

## The contact kernels are bound by latency, and lanes alone do not buy it back (`ncu_contact.txt`, `sk1.txt`, `sk1_skin_spread.patch`)

Nsight Compute on one launch each of the merged build, alone on the card: `field_contact_rows` at 35% of the memory system's peak and 33%
of the multiprocessors', `field_contact_l4` at 40% and 52%, `field_contact_columns` at 15% and 39%, `field_pace_skin_back` at 9% and 35%;
L2 hit rates 77 to 94%. None is bound by its bus or its arithmetic: each waits on latency, with its occupancy capped by its registers
(theoretical 33, 50, 58 and 42%; achieved 28, 45, 36 and 27%) at 8 to 10 cycles a issued instruction. So narrowing the gathered values to
32 bits, which halves octets, is not their lever (`agent-inferred` from these sections); the registers a thread holds are (the hardware
record's register-file inequality: a 128-bit sum is four registers).

`field_pace_skin_back` showed 6.09 active lanes of 32 a warp (a lane a support entry, its modes walked in turn). A build that spread its
pairs and crowds over entry and mode lanes (`sk1_skin_spread.patch`; each entry's terms summed over its lanes by shuffles, ring sums, the
same bits: the card suite 28 passed, the 24 sections of L71 reproduced) read 516.1 ms a section against the merged build's 514.0 in a
warmed eight-run hold (spreads 1.9 and 2.0; OBS ran on the card beside it throughout, steady). The guess (5 to 12 ms shorter) missed, and
the patch is set aside with this reading: the kernel's time is not its idle lanes' (its per-row preparation and its 128-bit chains stand
whole on every lane that spreads them).

## What the tick's premise says for the order (`agent-inferred`)

The state's step held at 0.96 to 0.996 of the step before over twelve ticks: the built tick is an integrator, `x^(k+1) = x^k + g(x^k)` with
`g` nearly the same from tick to tick, so its Jacobian stands near the identity in almost every direction and a read of its gains would
find nearly every mode at gain one. The ray settles only because the state grows, by the running mean's `1/k`. Two consequences. The count
of modes of gain one (the formal record's register size, §6.2 of the face-functor record) is not read off this tick: it asks for a tick
that contracts, and only then separates the modes kept by a symmetry or a class from the ones the tick releases. And the tick that
contracts is a store with a finite quality: a leak `λ` on the tick's state, `x^(k+1) = (1 − λ) x^k + g(x^k)`, settles at `g/λ` with
`ρ = 1 − λ` (`store.finite-quality`, the store law of November 11), founded at `λ = 0` (every bit of the built tick) and deposited as a
store's own state, never set as a dial. With it the forward's ticks follow a tolerance, `K = ln(τ/r₀)/ln ρ`, and the return can be the
covector's series at the settled state (the hardware record's §8), which keeps one tick's operands where it keeps four. It changes the
law, so it is built as an arm with its guess fixed first, after the realizations that keep every bit.
