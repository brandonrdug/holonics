# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs`. Each run ran under
`timeout` at its deadline inside a wrapper that prints `RUN_RECEIPT` (exit, wall, peak resident set
of the child, user time). Paths are relative to the run directory.

## Item 5: prose (the cloud host, 4 cores, every command on 4 threads)

### Inputs

| file | what | SHA-256 |
|---|---|---|
| `htext2/train.txt` | the mixed Holonics training text: prose, Lean, Rust, then equations (1,789,116 bytes) | `a2b83013…f3e9b1b9` |
| `htext2/dev.txt`, `htext2/dev.roles` | the held-out text and the medium of each byte (48,031 bytes) | `417c5801…8c58d71`, `32e05937…8ebc31` |
| `htext2/MANIFEST.tsv` | medium, split, path, size and SHA-256 of each file, in order | the text record's |
| `keys_tower.bin` | the declared key stream, 1 MiB | `1f748645…22a27a` |
| `hcont2/STATE` | the pair tower at pass 7 (the text record) | `2cb05d8d…bb35df8d` |
| `hbank/STATE0` | `hcont2` with a first-level bank joined, `O = 0` | `47abc751…fb0748` |

### Commands

```text
B complete-language join-tower-bank hcont2/STATE SHA keys_tower.bin SHA hbank/STATE0 level=0
T="htext2/train.txt SHA htext2/dev.txt SHA htext2/dev.roles SHA keys_tower.bin SHA 64 64 256 2 8 128 1 7"
B complete-language train-pair-pumped-tower $T hbank/pass1 hbank/STATE0 SHA          # banked
B complete-language train-pair-pumped-tower $T hbank/foil_pass1 hcont2/STATE SHA     # the foil
B complete-language read-tower-held hbank/pass1/STATE SHA htext2/dev.txt SHA htext2/dev.roles SHA 8
B complete-language read-tower-held hbank/foil_pass1/STATE SHA htext2/dev.txt SHA htext2/dev.roles SHA 8
B complete-language read-tower-held hbank/pass1/STATE SHA htext2/dev.txt SHA htext2/dev.roles SHA 8 unjoined
python3 tools/listener/compressor_given_training.py htext2/MANIFEST.tsv htext2/train.txt htext2/dev.txt htext2/dev.roles 8
```

The passes ran one after the other; the reads and the compressors after both.

### Time

The per-deposit bound for each pass is the largest deposit of its timing read: one pass over the
first 32,768 bytes of the training text, 31 deposits (`TIMING_READS.txt`), 0.786 s banked and 0.541 s
bankless, each taken up to 0.80 and 0.54.

| run | projection | deadline | measured wall | ratio | peak resident | outcome |
|---|---|---|---|---|---|---|
| banked pass (`PASSES.txt`) | 1,747 × 0.80 s + 7 s = 1,405 s | 1,500 s | 1,157.4 s | 0.82 | 386,088 KiB | complete, 1,747 / 1,747 deposits |
| bankless pass | 1,747 × 0.54 s + 5 s = 948 s | 1,000 s | 533.6 s | 0.56 | 182,548 KiB | complete, 1,747 / 1,747 deposits |
| held-out reads (`HELD.txt`) | 7 s each (the passes' own reads) | 60 s | 3.7–6.4 s | — | 21,564–22,648 KiB | complete |
| compressors (`COMPRESSORS.txt`) | not recorded | 250 s | 124.2 s | — | 103,212 KiB | complete |

## Item 6: the subject (Brandon's PC, 8 threads each)

### Inputs

The committed units of the units record (`d0973c39…`), the GSM8K training text (`050b94f3…`), the
held-out text (`e5bffe0e…`), the prompt (`9466544b…`, the first held-out question only), a fresh
1 MiB founding stream (`bd71c574ac4d8dca…`) and eight fresh 16 KiB sample streams. The binary is
`solenoidal_alpha` at `88737d7e9` (`ffbe0039a66e52e7…`).

### Commands

```text
B complete-language train-unit-tower UNITS SHA train SHA dev SHA dev.roles SHA keys SHA 64 64 256 2 8 128 3 7 towerA
B complete-language join-tower-bank towerA/STATE SHA keys SHA bankU.state level=0
B complete-language train-unit-tower UNITS SHA … keys SHA 64 64 256 2 8 128 1 7 bank4 bankU.state SHA
B complete-language train-unit-tower UNITS SHA … keys SHA 64 64 256 2 8 128 1 7 foil4 towerA/STATE SHA
B complete-language sample-unit-tower UNITS SHA bank4/STATE SHA prompt SHA keys_sN SHA 400 OUT [2]
B complete-language sample-unit-tower UNITS SHA foil4/STATE SHA prompt SHA keys_sN SHA 400 OUT [2]
```

### States

| state | SHA-256 |
|---|---|
| `towerA` pass 1, 2, 3 | `8c39724d03ec5a2e…`, `a6823aa1681fb88f…`, `7a354a60ae66968f…` |
| `bankU.state`, the bank joined | `14dbb23c45fac5e7…` |
| `bank4/STATE`, the banked fourth pass | `dbdc8f171e50e3ea…` |
| `foil4/STATE`, the bankless fourth pass | `847788e3f97d646b…` |

### Time

Development reads on 100 problems, 20 sections each: bankless 63.0–63.3 ms a section, with a 2.53 s
held-out read; banked 128.5 ms; the two together 166.4 and 77.4 ms, with held-out reads of 4.85 and
3.15 s. Each run stops itself once its mean section time passes its per-section bound.

| run | projection | deadline | measured wall | ratio | peak resident | outcome |
|---|---|---|---|---|---|---|
| three passes, first launch | 3 × (1,311 × 63.3 ms + 2.53 s) = 256.6 s | 270 s | 63.1 s | — | 216 MB | stopped itself at pass 0, section 992: a 32-section window ran 70.4 ms a section, past its 66.7 ms bound; incomplete |
| three passes | 3 × (1,311 × 70.4 ms + 2.53 s) = 284.5 s | 285 s | 245.1 s | 0.86 | 215,488 KiB | complete; largest window 67.3 ms, mean 60.1 ms |
| banked fourth pass, beside the foil | 1,311 × 166.4 ms + 4.85 s = 223.0 s | 224 s | 193.0 s | 0.87 | 363,912 KiB | complete; largest window 164.7 ms |
| bankless fourth pass, beside the banked | 1,311 × 77.4 ms + 3.15 s = 104.6 s | 105 s | 104.2 s | 1.00 | 209,948 KiB | complete; largest window 79.4 ms |
| 32 samples, 8 at a time | — | — | 6.1 s in all | — | 29.7–33.8 MB each | complete |

The relaunch took the stopped run's largest window as its per-section bound: a measurement taken
before launch, not a raised limit. The deadline came from the same projection.

## Item 6 on the original tower (the cloud host, 4 cores, every command on 4 threads)

### Inputs

The units record's own tower at pass 3 (`2bf016e35a141a4a…`, its pass lines head `PASSES_JOHN.txt`),
its eight 16 KiB sample streams, the units and the prompt above, and the item-5 key stream
`keys_tower.bin` (`1f748645…`) for founding and training. The framed
prompt is the same question after the blank line the training text puts before every question
(`e697eca00b6ca348…`). `train300` is the first 300 training problems (`15b1aac8f8376361…`). Two
binaries: `B0`, `solenoidal_alpha` at `b34006930` (`c5c8eba308de0d44…`), and `B1`, the same with the
amended key (`c7749388027ac1a2…`).

### Commands

```text
B0 complete-language join-tower-bank pass3/STATE SHA keys_tower.bin SHA bankO.state level=0
B0 complete-language train-unit-tower UNITS SHA … keys_tower.bin SHA 64 64 256 2 8 128 1 7 bank4 bankO.state SHA
B1 complete-language join-tower-bank pass3/STATE SHA keys_tower.bin SHA bankA.state level=0
B1 complete-language train-unit-tower UNITS SHA … keys_tower.bin SHA 64 64 256 2 8 128 1 7 bankA4 bankA.state SHA
B0|B1 complete-language sample-unit-tower UNITS SHA STATE SHA prompt|prompt_framed SHA keys_sN SHA 400 OUT [2]
```

The timing reads ran the same pass over `train300`.

### States

| state | SHA-256 |
|---|---|
| `bankO.state`, the antecedent-key bank joined | `bc50a31121652936…` |
| `bank4/STATE`, its pass | `8205e987c9e4ae3b…` |
| `bankA.state`, the amended bank joined (`O = 0`, `W_k′ = 0`) | `90660e440a5a6811…` |
| `bankA4/STATE`, its pass | `0983677b150041db…` |

### Time

| run | projection | deadline | measured wall | ratio | peak resident | outcome |
|---|---|---|---|---|---|---|
| timing read, antecedent key, `train300` | unmeasured, planned at 1–3 min | 180 s | 66.4 s | — | 316,264 KiB | complete; largest window 715.3 ms |
| antecedent-key pass | 1,311 × 715.3 ms + 23.4 s = 961 s | 965 s | 947.8 s | 0.99 | 386,080 KiB | complete |
| amended pass, first launch | 1,311 × 805.9 ms + 23.4 s = 1,080 s | 1,080 s | 53.5 s | — | 368,952 KiB | stopped itself at section 64, mean 815.6 ms past its 805.9 ms bound (a bound read on the antecedent-only law); incomplete |
| timing reads side by side, `train300` | the earlier read, 66.4 s | 180 s each | 72.4 s amended, 68.8 s antecedent-only | 1.09, 1.04 | 331,296 and 318,884 KiB | complete |
| amended pass | 1,311 × 827.5 ms + 25.2 s = 1,110 s | 1,110 s | 1,003.1 s | 0.90 | 393,312 KiB | complete |
| 80 samples, 4 at a time | — | 300 s each | — | — | — | complete |

The amended pass's bound is the largest window measured on the amended law before its launch (the
stopped run's), and its read time is its own timing read's: measurements of the law being run, not a
raised limit.
