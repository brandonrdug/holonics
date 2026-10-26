# The runs behind the record

All runs read the MQAR terrain written by `tools/listener/mqar.py` (the binding bank record's
generator, receipt F) on four cores, every command's threads the host's (rayon's default), one run at
a time. Paths are relative to the run directory; `B` is the release build of
`crates/holonics/examples/solenoidal_alpha.rs` at the record's commit.

## Inputs

| file | how | SHA-256 |
|---|---|---|
| `train4k.cls`, `train4k.marks` | `mqar.py 0 4096` | `e4c25788…0d32f`, `4da247a5…9a43a5` |
| `train16k.cls`, `train16k.marks` | `mqar.py 0 16384` (its first 4,096 passages are `train4k`) | `12cb9654…14cfb3`, `b5a5bb86…69c75` |
| `dev.cls`, `dev.marks` | `mqar.py 1000000 1000`, the held-out set | `c9c696c4…ad658`, `3f03ddaa…d2aa` |
| `keys_tower.bin` | the declared key stream, 1 MiB | `1f748645…22a27a` |
| `foil0.state` | `found-tower-classes 128 keys_tower.bin … 64 32 128 2 gated,turned 7` | `c3ad842d…2edd0` |
| `bankL0.state` | `join-tower-bank foil0.state … level=0` | `d611e628…405d4a` |
| `bankTop.state` | `join-tower-bank foil0.state …` (the record's top level) | `a435f478…c1484` |

## Commands

```text
B complete-language join-tower-bank foil0.state SHA keys_tower.bin SHA bankL0.state level=0
B complete-language train-sections-tower-classes bankL0.state SHA train4k.cls SHA train4k.marks SHA \
    dev.cls SHA dev.marks SHA 64 16 1 bankL0_4k
B complete-language train-sections-tower-classes foil0.state SHA <the same terrain> 64 16 1 foil4k
B complete-language join-tower-bank foil0.state SHA keys_tower.bin SHA bankTop.state
B complete-language train-sections-tower-classes bankTop.state SHA <the same terrain> 64 16 1 bankTop_4k
```

Each ran under `timeout` at its deadline, inside a wrapper that prints `RUN_RECEIPT` (exit, wall,
peak resident set of the child, user time).

## Time

The per-deposit bound before the first level-0 launch was 0.433 s, the largest deposit of 16
passages measured on the banked tower at the top level (`time_bank`, before this record). After the
first run's evidence, the 4,096-passage runs used that run's largest window, 0.60 s a deposit.

| run | projection | deadline | measured wall | ratio | peak resident | outcome |
|---|---|---|---|---|---|---|
| `LEVEL0_16K_STOPPED.txt`: level 0, 16,384 passages | 1,024 × 0.433 s + 2 reads × 6 s = 455 s | 600 s | 158.1 s | — | 336,304 KiB | stopped on evidence at deposit 320: the window from deposit 160 to 192 ran 0.60 s a deposit, past the 0.433 s bound; incomplete |
| `LEVEL0_4K.txt`: level 0, 4,096 passages | 256 × 0.60 s + 12 s = 166 s | 200 s | 137.0 s | 0.83 | 340,820 KiB | complete |
| `FOIL_4K.txt`: the bankless foil | 166 s (the bank's bound) | 200 s | 33.6 s | 0.20 | 70,672 KiB | complete |
| `TOP_4K.txt`: the top level, the same opening | 166 s | 200 s | 107.5 s | 0.65 | 311,728 KiB | complete |
| `TOP_BOTH_BLOCKS_16K_STOPPED.txt`: the top level, key drawn over both blocks | — | — | first pass 400.0 s | — | — | stopped by hand after its first pass, with no wall receipt |

The second run's training set is the first run's first quarter: the first run's windows had already
fallen to 0.001 bits an answer by deposit 256, and the shorter read reaches the held-out count inside
its bound. The bound was not raised.

## The covector fixture

`FIXTURE_FAILED.txt` is the check's largest covector a family under the earlier opening (gate bias 1,
hold 4, join drawn on `2^(−8)`) once the key opened on the face block alone: the gate bias (−20.1 M)
and the hold (7.8 M) on `2^(−32)` bits a unit fall below the reading bar `2^26 = 67.1 M`.
`FIXTURE_SWEEP_1.txt` and `FIXTURE_SWEEP_2.txt` read, for each opening, the weakest bank family's
largest covector over that bar (`min`), and the gate bias's and the hold's. The chosen opening
(`pairs10x37 scale 4 hold 2 bias 0`: the record's passage, the join on `2^(−7)`, `h = 2`, `g = ½`)
reads every family at 3.18 times the bar or more, and the full check passes on it.
