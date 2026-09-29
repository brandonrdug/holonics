# The order repair: order reaches the section on known truth, and text stays at the byte marginal

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
receipts, each read once at the pinned commit `bd06105c` (the
[pins](2026-09-29_THE_ORDER_REPAIR_PINNED_BEFORE_ITS_RUNS.md)); [agent-inferred] for §5.

**What ran.** The build `af5e7de6`, in the owners of recorded failure 4 (`hnn::moment`,
`hnn::prediction`, `hnn::ratio`, `hnn::reference`; Lean `HNN/Prediction`). Order is carried by
residues and relative phases, with no window and no table of pairs:
- the receiving ring's period is a product of pairwise coprime factors, so a datum's residue is its
  joint residue class;
- a refinement's locked data are placed on the same spectrum at their stations' residues and read
  with the request's placement;
- generation locks the stations of largest gap at the grain, ties together;
- learning compares only the unlocked stations of a drawn partition.

```sh
cargo run --release -p holonics --example hnn_prediction -- order2
cargo run --release -p holonics --example hnn_prediction -- order2 pinned
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-order-sections.txt
```

## 1. Acceptance 1, the internal checks: holds

| Run | Refinements | Balances, pairings, commits closed | Energy bound held | Unreached checks (loci) unchanged | Generation refinements, balances closed |
|---|---|---|---|---|---|
| `order2` | 512 | 512, 512, 512 | 512 | 32 of 32 (224) | 1,629, 1,629 |
| `order2 pinned` | 512 | 512, 512, 512 | 512 | 32 of 32 (224) | 256, 256 |
| `text` | 770 | 770, 770, 770 | 770 | 50 of 50 (350) | 74, 74 |

The certified storage growth was 0 at every deposit (its product 1). No locus stepped past the
certificate. `E`'s steps were `2⁻¹⁶..2⁻¹⁴` on the terrain and `2⁻¹⁹..2⁻¹²` on text; `R`'s were
`2⁻²..2⁰`.

## 2. Acceptance 2, the marginal test: passes

The order-2 terrain, `x_t = x_(t−2) + 1 (mod 4)` continuing a request of 40 uniformly drawn cells,
evaluated on 256 fresh requests (2,048 held-out stations). The training read 512 requests.

| Readout | Released | Exact sections | Stations right | By station (of 256) |
|---|---|---|---|---|
| the order repair (`D = 60 = 3·4·5`) | 249 | 39 | **866** | 112, 112, 111, 108, 108, 107, 108, 100 |
| the static marginal (class 0) | — | — | 512 | — |
| the per-station marginal | — | — | 520 | — |
| the September 29 readout (`d = 32`), the control | 89 | 5 | 324 | 50, 44, 37, 45, 45, 34, 35, 34 |

866 is more than 520 and 512: order reaches the section, and the acceptance holds. The September 29
readout on the same draws counts 324, below both marginals: it held 167 of its 256 sections, each
counting no station. The continuation is exact on 39 of 256 sections.

The training code over the compared stations (bits, beside the counts):
- the order repair: `4212 + 1/16 + ε` over 2,244 compared stations, `1 rem 1968/2244` a station;
- the September 29 readout: `8949 + 4/16 + ε` over all 4,096, `2 rem 757/4096` a station.

A uniform guess over the four symbols costs 2 bits.

## 3. Acceptance 3, text: fails

Two passes over the U6 choosing role's 385 pairs (`D = 5·7 = 35`, `m = 32`); the 8 validation
requests F0's rule selects. One section was released, 32 bytes of spaces and `e` with one other letter; seven
were held, every unlocked station plural at the grain `L_R = 16` once no station led. **The output
is illegible**: the released section reads the byte frequencies, and the item fails. The text is
owner-only (`.local/cuts/u6-order-sections.txt`) and was shown in the conversation whole, with
nothing beside it. The training code over the 12,017 compared stations was `95192 + 1/16 + ε` bits,
`7 rem 11073/12017` a station (`7 + 14/16 + ε` at the grain), against `8 + 0/16 + ε` for a flat
face over the 257 classes.

## 4. Time and memory

| Run | Training (projected) | Generation (projected) | Peak resident bytes (projected) |
|---|---|---|---|
| `order2` | 163,224 ms (about 160,000) | 76,611 ms (about 80,000) | 1,204,670,464 (about 1,200,000,000) |
| `order2 pinned` | 69,961 ms (about 75,000) | 7,524 ms (about 10,000) | 357,740,544 (about 400,000,000) |
| `text` | 263,747 ms (about 270,000) | 6,021 ms (at most about 60,000) | 888,221,696 (about 900,000,000) |

No run reached its training stop (540,000 ms) or the resident cap; every run's evidence is
complete.

## 5. What stays open, by its measurement [agent-inferred]

**The terrain.** Every station reads right on about 7 of 16 held-out requests, stations 0 and 1
(112 and 112 of 256) as much as the rest: the locked chain carries what the first two stations
read, and those two read the request's last two cells.
- They read those cells through a sum of every placed datum. With `E` at its declared sign
  sequence, each datum's class image spreads over the ring's `2D = 120` coordinates. A linear
  readout cancels the other data's class differences only when `2D ≥ (n + m − 1)(|A| − 1)`, here
  188.
- The certified step moves `E` by `2⁻¹⁶..2⁻¹⁴` a deposit, so `E` stays at its opening, and `R`
  alone learns.
- Capacity is not the whole limit. At `D = 105 = 3·5·7`, inside the bound, the development read
  counted 228 of 512 at the same training.

The joint residue class is resolved: every datum has its own residue below `D`. It is not
separable by a linear readout of the sum.

**Text.** The request's placement cannot separate its bytes: 256 class differences against 70
coordinates, and requests of 19 to 14,970 bytes. The section's locked neighbours carry the only
order the stations read. After two passes the compared stations code 2/16 of a bit below flat; in
seven of eight sections the lock stopped with every unlocked station plural at the grain. The one
released section reads the byte frequencies.

**The blocker, by its measurement.** The placement superposes the data. On the terrain the request's
last cells read right on 7 of 16 requests (112 of 256 at stations 0 and 1). On text the readout
codes 2/16 below flat and seven of eight sections stop plural. Both follow from one cause: a datum's class is
placed as a spread image that `E`'s certified step does not move, not as an amplitude on its own
residue's modes.

## 6. Owed in #62

- **The placement's linear separability.** For a datum placed at relative phase `r` among data at
  the other relative phases of one ring of `2D` coordinates, with class images `P^r E e_x`, a linear
  readout whose class differences vanish on every other datum's class differences exists iff the
  target's differences lie outside their span. For `E` in general position that requires
  `2D ≥ (n + m − 1)(|A| − 1)`. Measured here, not proved.
- **The lock iteration as the joint section.** Generation with its locked data placed is an
  instance of `HNN/Prediction.jointSection`, whose step re-enters the placed section. A released
  section is not claimed to be a fixed point of re-reading every station with the others locked.
  This is owed with the concrete word's bridge ("Step 4 (#73) owed: the diamond on the concrete
  tick").

Formal-checked in this loop (Lean `HNN/Prediction`):
- `joint_residue_determines_position`;
- `joint_class_not_additive`;
- `placed_at_station`;
- `lock_reads_unique_top`;
- `partition_reading_ignores_compared_targets`.
