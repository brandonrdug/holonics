# The hardware is a traffic network: work rides the lane its shape fits, and each crossing is priced

Refs #404 #76. Status: [the lens, derived and joined to the hardware law; corrected the same day against local closure (§5); agent-inferred, October 31].
Claude (opus). Read beside [the receiver cover](2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md)
(the card carries the current; the host must not reconcile allocated worlds) and
[GPU first](2026-10-27_THE_LEARNER_RUNS_ON_THE_CARD_AND_ITS_WORKLOAD_IS_NEVER_TRADED_FOR_TIME.md).

## 1. The lens

Brandon, October 31 (paraphrased; his words stay outside the repository), on being asked whether a
units founding could run on the host: moving work between the card and the CPU has its own transport
cost, like changing lanes on a highway, and the computational theory should model the machine as a
traffic system. The CPU, the GPU and storage are lanes that each accept certain vehicles, and the
distribution is optimized by routing each vehicle to its lane: the CPU perhaps a mixed lane or a lane
for the fastest single vehicles, the GPU the lanes for wide freight. What he reaches for are pathways
and wavelengths on lattices: distribution.

## 2. The derivation

[agent-inferred] A workload is a current with a shape: its width (how many co-present regions commute,
the hardware law's partition), its depth (the length of its chain of dependencies), and its
branching (how irregular its reads are). A lane is a device with its own capacity for each:
- the card: wide and shallow, uniform reads (the tower's 320 streams × 128 cells × 6 levels, the outer
  sums' tiles); a serial chain on it runs one lane wide;
- the CPU: few, fast, deep lanes; serial chains with irregular reads (a priority queue, a hash map, a
  greedy founding whose every merge changes the counts the next reads);
- storage: the slowest, widest reservoir; what is read once.

A crossing between lanes is a flux through a section, and it is priced as such: its volume (bytes) over
the bus's capacity, plus the synchronization it forces (a lane that must wait). The route of a
workload is chosen by the sum of each segment's time on its lane and the crossings between them,
which is the receiver cover's law read with prices: the card carries the current that is wide, and a
deep, branchy segment rides the CPU when its crossings are small. "The host is forbidden" was the
answer to a measured failure (the learner's wide current carried on eight host threads, October
23–27); it is a case of this law, not the law.

## 3. The two cases read on October 31

- **The units founding** (`hnn::units::Units::found`): one serial greedy chain over pair counts, run
  once; its input is the passage read from storage and its output an 8 KB merge list. Its lane is the
  CPU, and it crosses to the card only as that list.
- **The learner's section** (the every-level credited tower on units): the forward, reverse and outer
  sums are wide and ride the card; each section the gradient crosses to the host (about 9 MB of
  `i128` covector), the host steps the deposit and certifies it, and the material crosses back. In the
  64-section profiles (§25–§28 of the section-edge record) the card's kernels carry about nine tenths
  of the time and the crossings and the host's step the rest: a priced lane change, not the jam.

## 4. Where it joins

- **The hardware law** (CLAUDE.md, "Hardware law"; AGENTS.md alike): to the partition's
  certification add the route's price: each segment on the lane whose width, depth and branching fit
  it, each crossing counted as a flux with its volume and its wait, and the route the least total.
- **The receipts**: a run's receipt names each lane's time and each crossing's volume (the card's
  `TOWER_CARD` and `TOWER_PROFILE` lines carry the card's; the crossings are owed as their own line).
- **Learning stays on the card.** This lens does not move a learner's wide current to the host; it
  lets a deep segment (a founding, a codec, a certificate's exact comparison) ride the lane that fits
  it, with its crossing priced.

## 5. No lane is a partition of the dynamics

Brandon, the same day (paraphrased): a rule that a kind of work is built on the processor is not a
good global rule if the dynamics are flexible enough to work around it; demanding that something work
out on one part of the hardware or the other isolates partials of the dynamics and makes them close
in partitions the transport drew. That worry is right, and it corrects §3–§4.

[agent-inferred] A lane carries a segment of a run; it never owns a part of the law. The route is
chosen per run from the segments' shapes and the crossings' prices, and it may change as the
dynamics change: the units founding rides the CPU on October 31 because it is today one serial
greedy chain run once, not because founding belongs to the CPU, and when founding becomes part of the
learner's own motion (a founding from the reached residual, renewed as the passage is heard) it moves
with that motion onto the card's lanes. A crossing is a price the route pays, never a wall at which a
piece of the dynamics must close: no quantity is required to be complete on one device, and the laws
are stated, tested and certified on the whole run (the host's reference and the card agree bit for
bit wherever a segment runs). The hardware law's partition certifies which co-present regions commute;
it does not license a partition of the mathematics.
