# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs`. Each cloud run ran under
`timeout` at its deadline inside a wrapper that prints `RUN_RECEIPT` (exit, wall, peak resident set
of the child, user time); the passes also ran under an observer (`WATCH` lines) that stops a run when
its mean time a section passes its bound. Paths are relative to the run directory, which is not in
the repository.

## Item 6 on Brandon's PC: four more amended-bank passes (8 threads each)

The binary is `solenoidal_alpha` at `29b76d727` (the key that reads the arrival), built on the PC.
The inputs are the bank record's PC inputs (the GSM8K units `d0973c39…`, training text `050b94f3…`,
held-out text `e5bffe0e…`, prompt `9466544b…`, founding stream `bd71c574ac4d8dca…`, eight 16 KiB
sample streams) and its pass-3 tower `towerA/STATE` (`7a354a60ae66968f…`). The framed prompt is two
newline bytes and the prompt (`e697eca0…9652`). The eleven bank tests passed on the PC binary.

```text
B complete-language join-tower-bank towerA/STATE SHA keys SHA bankA.state level=0
B complete-language train-unit-tower UNITS SHA train SHA dev SHA dev.roles SHA keys SHA 64 64 256 2 8 128 1 7 bankA4 bankA.state SHA
B complete-language train-unit-tower … 64 64 256 2 8 128 1 7 bankA5 bankA4/STATE SHA          # then bankA6, bankA7
B complete-language train-unit-tower … 64 64 256 2 8 128 1 7 foil5 foil4/STATE SHA            # then foil6, foil7
B complete-language sample-unit-tower UNITS SHA STATE SHA prompt|prompt_framed SHA keys_sN SHA 400 OUT [2]
```

The timing read on the amended law was one banked pass from `bankA.state` and one bankless pass from
`foil4/STATE` over the training text's first 300 problems (`train300`, 162,937 bytes,
`15b1aac8f8376361…`), run together: 153.9 and 145.5 ms a section banked, 74.3 and 73.8 bankless.
Each projection is 1,311 sections × the largest window measured on that law before the launch, plus
the held-out read. `/usr/bin/time` is not on the PC; each receipt is the run's `wait4` usage.

| run | projection | deadline | measured wall | ratio | peak resident | state SHA-256 |
|---|---|---|---|---|---|---|
| `bankA.state`, the join | — | — | — | — | — | `fa18c487…6dfa` |
| bankA4, alone | 1,311 × 153.9 ms + 4.48 s = 206.2 s | 207 s | 165.2 s | 0.80 | 383,244 KiB | `5f9f9eee…414c` |
| bankA5 | 206.2 s | 207 s | 183.3 s | 0.89 | about 383,000 KiB | `a0e83c88…718d` |
| bankA6 | 212.8 s | 213 s | 183.1 s | 0.86 | about 383,000 KiB | `4b54c9da…9370` |
| bankA7 | 213.3 s | 214 s | 183.4 s | 0.86 | 465,924 KiB | `1dee7db0…6ea4` |
| foil4, the bank record's run | 104.6 s | 105 s | 104.2 s | 1.00 | 209,948 KiB | `847788e3…6c72` |
| foil5, beside bankA5 | 107.2 s | 108 s | 98.1 s | 0.92 | 209,948–234,384 KiB | `f266c2e6…ddcf` |
| foil6, beside bankA6 | 107.2 s | 108 s | 97.9 s | 0.91 | 209,948–234,384 KiB | `a8139b1c…0e0e` |
| foil7, beside bankA7 | 107.2 s | 108 s | 98.3 s | 0.92 | 234,384 KiB | `6ec58f70…2395` |

Every run certified all 1,311 deposits and none stopped. The banked passes' largest windows were
143.7, 158.9, 159.3 and 157.6 ms; bankA6 and bankA7 were projected on the largest window measured
before their launch. The samples (2.6 s wall at most, 8 at a time) ran between passes. Every report
the PC sent, with every sample, is in `SAMPLES_PC_PASSES.md`.

## Item 6 on the cloud host: the copy read (4 threads)

The state is the bank record's cloud `hjohn/bankA4/STATE` (`0983677b150041db…`, the original pass-3
GSM8K units tower, the amended bank and one pass), read on the GSM8K held-out text (`e5bffe0e…`,
roles `c978b971…`) with the committed units (`d0973c39…`):

```text
B complete-language read-tower-held-cells hjohn/bankA4/STATE SHA dev.txt SHA 8 cellsread/bankA4.tsv units_all/UNITS SHA
B complete-language read-tower-held-cells hjohn/bankA4/STATE SHA dev.txt SHA 8 cellsread/bankA4_unjoined.tsv unjoined units_all/UNITS SHA
python3 -I tools/listener/held_cells.py copy dev.txt dev.roles cellsread/bankA4.tsv cellsread/bankA4_unjoined.tsv
```

## Item 5 on the cloud host: the Holonics text (4 threads)

### Inputs

| file | what | SHA-256 |
|---|---|---|
| `htext2/train.txt`, `dev.txt`, `dev.roles`, `keys_tower.bin` | the bank record's Holonics inputs | `a2b83013…`, `417c5801…`, `32e05937…`, `1f748645…` |
| `hunits/found/UNITS` | 1,015 units founded on `train.txt` | `4f4a2b3a4f198441…` |
| `hunits/train_prose.txt` | the first 524,316 bytes of `train.txt`, its prose part | `273395525e5b046d…` |
| `hunits/train_t.txt` | the first 180,000 bytes of the prose part, for timing reads | `b7409b55da969499…` |
| `hbank/foil_pass1/STATE` | the bank record's bankless pass 8 of the pair tower (prose 3.083) | `72135597c8ac71d4…` |

Binaries: `B1` is `29b76d727` with `read-tower-held-cells` added (`8c817541d5c34474…`), the founding
and passes 1–3; `B2` is `2eb383691`, the same tree committed (`81df78b0aa9cd5aa…`), every later run.
The two differ only by that command.

### Commands

```text
B1 complete-language found-units htext2/train.txt SHA hunits/found
T="hunits/found/UNITS SHA TEXT SHA htext2/dev.txt SHA htext2/dev.roles SHA keys_tower.bin SHA"
B1 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/passN [hunits/pass(N-1)/STATE SHA]      # TEXT = train.txt, N = 1, 2, 3
B2 complete-language join-tower-bank hunits/pass3/STATE SHA keys_tower.bin SHA hunits/bank3.state level=0
B2 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/prose_aN hunits/(pass3|prose_a(N-1))/STATE SHA   # TEXT = train_prose.txt
B2 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/prose_bN hunits/(bank3.state|prose_b(N-1)/STATE) SHA
B2 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/time_bank hunits/bank3.state SHA         # TEXT = train_t.txt
B2 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/time_foil hunits/pass3/STATE SHA
B2 complete-language train-unit-tower $T 64 64 256 2 8 128 1 7 hunits/time_t                                    # from scratch
B2 complete-language train-unit-tower $T 64 64 1024 2 8 128 1 7 hunits/time_c1024                               # from scratch
B2 complete-language read-tower-held-cells STATE SHA htext2/dev.txt SHA 8 cellsread/NAME.tsv [unjoined] [hunits/found/UNITS SHA]
B2 complete-language read-tower-held-cells hbank/foil_pass1/STATE SHA htext2/dev.txt SHA 8 cellsread/byte_foil_pass8.tsv
python3 -I tools/listener/held_cells.py place|spans htext2/train.txt htext2/dev.txt htext2/dev.roles cellsread/{byte_foil_pass8,hunits_pass3,prose_a3,prose_b3,prose_b3_unjoined}.tsv
python3 -I tools/listener/held_cells.py prefix htext2/train.txt htext2/dev.txt htext2/dev.roles cellsread/byte_foil_pass8.tsv
```

### States

| state | SHA-256 |
|---|---|
| `pass1`, `pass2`, `pass3` | `fc63f1c5849c7330…`, `83401851d39af36c…`, `9a26fdfcc9afe797…` |
| `bank3.state`, the bank joined on pass 3 (`O = 0`, `W_k′ = 0`) | `113507d7dd974a76…` |
| `prose_a1`, `a2`, `a3` | `a53bc062eba76d48…`, `8f5a0fad42142782…`, `31f5d75aca50497a…` |
| `prose_b1` … `b7` | `3d3ea11bc0802e91…`, `a5968686e9f39b9a…`, `cf6ba0bd386cda8f…`, `8e58a944ec4cafc9…`, `d2d123555ebfd124…`, `45fb31cb6a40cd53…`, `7e4719bc7956acdd…` |
| `time_t`, `time_foil`, `time_bank`, `time_c1024` | `c7fa8a567c3aaea2…`, `ce1a92311f81338d…`, `5b1d98716ace569e…`, `1c0462323296cb51…` |

The cell files: `bankA4` `7563c5d136a25452…`, `bankA4_unjoined` `373d90df732c5272…`,
`byte_foil_pass8` `71ee2b889f914134…`, `hunits_pass3` `a5d1b59e9d66adcd…`, `prose_a3`
`9d65e0731071df0a…`, `prose_b3` `7b95ecae768fe467…`, `prose_b3_unjoined` `356f8656eb5902a5…`,
`prose_b7` `eb00e3500b106690…`, `prose_b7_unjoined` `d024e211f83f26d2…`.

### Time

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| founding | unmeasured; GSM8K's 3.5 MB founded in 2.9 s | 120 s | 3.0 s | — | 75,096 KiB |
| `time_t`, 256 contacts from scratch | unmeasured, planned at 1–3 min | 180 s | 32.3 s | — | 185,872 KiB |
| passes 1, 2, 3 | 797 × 415 ms (`time_t`'s largest window) + 2.4 s = 333 s | 335 s | 316.7, 301.7, 308.3 s | 0.95, 0.91, 0.93 | 215,104, 223,772, 242,008 KiB |
| `time_foil`, bankless from pass 3 | 77 × 419 ms (pass 3's largest window) + 2.4 s = 34.7 s | 60 s | 31.6 s | 0.91 | 193,468 KiB |
| `time_bank`, banked from `bank3.state` | unmeasured, planned at 1–3 min | 180 s | 63.4 s | — | 336,368 KiB |
| `time_c1024`, 1,024 contacts from scratch | unmeasured, planned at 1–3 min | 180 s | 43.0 s | — | 297,924 KiB |
| `prose_a1`, `a2`, `a3` | 258 × 418.9 ms + 2.4 s = 110.5 s | 111 s | 89.9, 88.1, 88.4 s | 0.81, 0.80, 0.80 | 237,856, 215,112, 207,712 KiB |
| `prose_b1`, `b2`, `b3` | 258 × 817 ms (`time_bank`'s largest window) + 5 s = 215.8 s | 216 s | 164.2, 178.0, 171.0 s | 0.76, 0.82, 0.79 | 325,332, 325,056, 331,460 KiB |
| `prose_b4` … `b7` | 222 × 836.2 ms (the largest window of `b1`–`b3`) + 4.3 s = 189.9 s | 190 s | 183.4, 175.2, 178.2, 174.7 s | 0.97, 0.92, 0.94, 0.92 | 413,680, 333,072, 332,580, 332,928 KiB |
| each cell read | unmeasured, planned at 1–3 min | 120 s | 3.9 s (Holonics), 24.1 s (GSM8K) | — | 29,844, 32,756 KiB |

Two departures from the waiting standard, neither a raised limit:
- `time_foil`'s deadline, 60 s, was set above its projection's upper end (35 s). It completed inside
  the projection.
- The prose passes' section count (258) was projected from the held-out prose's units a byte; the
  prose part took 222 sections, so the first six prose passes ran well under their projections.
  `prose_b4`–`b7` were projected on the measured 222.

Single windows passed their bounds (`prose_a1` 471.4 ms while a parse ran beside it, `prose_b2`
836.2 ms, passes 1–3 up to 420.1 ms); the mean never did, so no run stopped. `prose_b2`'s window
became the bound of `b4`–`b7`, measured before their launch. The prose passes ran one after the other,
four threads each, with the side reads under `nice`.
