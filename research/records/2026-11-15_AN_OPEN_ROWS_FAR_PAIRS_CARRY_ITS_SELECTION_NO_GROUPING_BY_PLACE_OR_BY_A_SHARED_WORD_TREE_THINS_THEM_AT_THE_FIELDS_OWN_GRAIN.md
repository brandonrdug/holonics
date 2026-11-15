# An open row's far pairs carry its selection: no grouping by place or by a shared word tree thins them at the field's own grain

November 15, the Opus PC thread, with the theory thread's design (#841, atlas `contact.crowd-slip-bound`). Every reading here is on the host
(`Constitution::open_rows`, `open_crowds`, `far_jitter` in `crates/engine/src/ruler.rs`; `athena train complete-language read-open-rows`),
on the sections the line would train next from lap 35's state (`STATE.3000` and its `MEAN.3000`), and no law reads it. Receipts:
[`receipts/2026-11-15_open-rows/`](receipts/2026-11-15_open-rows/).

## 1. Why

The engine's profile on the line's build (#839) puts the contact family at about 286 ms of a 640 ms section. The November 13 ablations had
already found it bound by its count of pair terms, and two realizations of the day changed nothing measurable on the rows. An open row meets
every definite site of its region (§15.9), so open rows hold about 0.69 of a section's pair terms (G140, November 13). The theory thread asked
whether an open row's far pairs can be heard as fewer terms without losing what they carry. Every row keeps its ticks; G140 had held
written rows at their opening, which cut the relays, and that cut is not this one.

## 2. Where an open row's mass lies (T6)

One section of 182 regions, then six (1,140 regions), by slice, head and tick (`t6_shares.txt`).
- An open row puts almost all its mass far: the near field (`|i − j| < NEAR`) holds 0.014 to 0.038 on the still heads and 0.055 to 0.165
  on the paced ones. The rest stands past it.
- Most of it falls outside the row's probed classes. Still head 0 is the exception, with 0.32 to 0.42 inside (a probed class takes a share
  far past its size).
- The still heads are sharp at every octave: on code at tick 3, octaves 5 to 8 (gaps 32 to 511) hold 0.10 to 0.27 of a row's mass each,
  on a Rényi-2 count of 2 to 6 sources, its largest share 0.41 to 0.62 of the octave's.
- The paced heads spread with distance: head 2's Rényi-2 count reads 3.7, 7.1, 13.8, 29.4, 59.4 and 108.5 at octaves 3 to 8, and its
  largest share falls from 0.50 to 0.05.

## 3. Crowds by place (T7) miss

Each octave's crowd of definite sources on a side (`crowd_ranges`) was tested for being heard as one source at a sixteenth of a bit (the
theory thread's band `B_C` over the members' framed words and skins, and beside it the members' own locks, the floor any band reaches), and
split by halves down to members where it failed (`t7_crowds.txt`, `t7_cover.txt`). The theory's guess: on paced heads most crowds at octave 6
and up admit, and open rows' paced pair terms fall by over half.
- Still heads keep every pair (1.000 under the band, 0.990 to 0.997 at the locks' floor).
- Paced head 2 keeps 0.876 on code and 0.984 to 0.993 elsewhere; head 3 keeps 0.997 to 1.000.
- Wider grains under the band, on head 2: 0.72 to 0.93 at a quarter of a bit, 0.42 to 0.63 at one bit, 0.12 to 0.17 at four.

The guess missed: inside one octave of place the members' locks differ too much, because the lock reads a source's word and place is the
wrong coordinate for it (the theory thread's reading of the miss: a crowd must be tight in every coordinate its score depends on).

## 4. Grouping by lock value: the floor of any grouping

For each open row and octave, the fewest intervals of a grain that cover its members' `z` (sorted, greedy), the floor any grouping for that
receiver can reach (`t7_cover.txt`): at a sixteenth of a bit the still heads keep 0.63 to 0.84 and the paced heads 0.33 to 0.60 (head 2 0.33
to 0.42), at a quarter of a bit 0.37 to 0.63 and 0.17 to 0.36. By value the floor falls well under the members.

## 5. The field's own grain

The grain was taken from the field's own temperature: each far pair's `|z(end) − z(mean)|` between lap 35's end and its mean, each at its own
temper (`jitter.txt`). The theory's guess: a median between 1/8 and 1/2 bit on paced heads, higher on still heads, rising with octave.
- Still heads: 1/4 bit at tick 0, 1/2 to 1 bit at tick 3, flat over octaves 2 to 9.
- Paced heads: 1/32 to 1/4 bit overall, falling with distance (head 2 at tick 3: 1/4 bit at octaves 2 to 5, then 1/8, 1/16, 1/32, 1/64 at 6
  to 9), as the skin thins the arriving face.
Scored: the paced range misses (mostly under it), the still heads' being higher holds, and the rise with octave misses (it falls). The bins are
octaves of `|Δz|`, so every figure is good to a factor of two.

## 6. A word tree shared by every receiver keeps the pairs

The candidate the per-receiver floor left: one tree a head and tick, its definite words split by medians along the principal directions of
its open rows' probes (then the words' power), and a crowd heard as one in a tree cell where its members' `z` spread stands within the
octave's own jitter (`tree_grains.txt`, `tree_at_jitter.txt`). The theory's guess, scored as the tree's terms over the per-receiver floor's at
the same grain: head 2 1.2 to 1.6, head 3 1.3 to 2.0, the still heads 1.5 to 2.5; a head over 2.0 keeps its pairs.
- (Read with the tree's directions in integers, the power iteration of `principal_directions`; a first read with float directions gave the
  same figures within 0.001.) The tree leaves 0.90 to 0.98 of the far pairs at the jitter bin's lower edge and 0.84 to 0.95 at its upper.
- Its ratio to the per-receiver floor: 1.66 to 2.38 on the still heads and 1.83 to 2.45 on the paced ones at the lower edge, 2.04 to 3.25 at
  the upper.
Head 2's guess missed, head 3's held at two ticks of four, the still heads' held at the lower edge; by the rule every head keeps its pairs.

## 7. What it says

An open row's far pairs are its selection: what each receiver picks among its region's definite sources, by their words. No grouping by place
thins them at a grain the field's own temperature resolves, and no grouping by words can be shared by the receivers, whose probes span too
many directions. A grouping per receiver would sort each row's own sources, which costs what the pairs cost. So the far pairs stay as the
information they are, and the contact's time is its realization's: octets and arithmetic a pair, and the walk that the November 12
ablation read at about half the rows' time. The level of §4.9 of the November 13 design record groups by place as well, so it serves what is
smooth in place, the superposition the moments carry, and not this selection (the theory thread's reading; its record §12 holds its
side of these readings and its scored guesses). A tile of open receivers over staged source rows is not built: the November 12–13 copies
(P59) read every source row resident at 0.88 of the rows' time and 0.95 of the forward contact's, so source traffic is not what binds.
