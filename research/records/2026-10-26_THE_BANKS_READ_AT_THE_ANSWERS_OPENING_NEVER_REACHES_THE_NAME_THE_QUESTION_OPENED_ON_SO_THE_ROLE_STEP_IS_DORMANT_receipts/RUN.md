# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs`. Every run ran inside a
Python wrapper that kills the child at the deadline and prints its `wait4` usage as `RUN_RECEIPT`
(exit, wall, peak resident set, user time); `/usr/bin/time` is on neither host. Paths are relative
to each host's run directory, which is not in the repository. The traces and requests hold the
GSM8K text's positions and are kept only on the hosts; their SHA-256s are below.

## The inputs

| input | SHA-256 |
|---|---|
| GSM8K units (`UNITS`) | `d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a` |
| training text (`train_all.txt`, 3,528,168 bytes) | `050b94f367625ad2c533bb3af53c730ea6d12e140a080a6a3def9ffdc0de3b95` |
| held-out text (`dev.txt`, 397,669 bytes) | `e5bffe0ea3949a2e8efec1c43120918891867c342a9e9ffd288cc798a8363153` |
| held-out requests, 421 named problems | `86600c2c14b73f08c34c6716f4cd0523d55387b89ac7b686203613fe3c8c5236` |
| training requests, 4,524 named problems | `78528683ac8f67b71c1c0b34cc15e1c92f3b7d871bd1f0d7de93f316bd979d56` |
| the development text, the first 50 held-out problems (26,734 bytes) | `87d3784886fc4da156071d9f6aca4c2f5ead6408e886898555f6f94650ded2b4` |
| its 32 requests | `31c223842bcf35b60672e1f14d118206d2ad11f81a7686368e847fef3f5b0485` |

The bank states. The PC series is the four-pass record's
([receipts](../2026-10-26_THE_BANK_COMPLETES_A_WORD_THE_QUESTION_HOLDS_AND_DOES_NOT_CHOOSE_IT_AND_PROSE_ALONE_STALLS_ABOVE_BZ2_receipts/RUN.md)):
its join of the pass-3 tower on the PC and four amended-bank passes. The cloud pair is the bank
record's cloud join of its own pass-3 tower and its one pass.

| host | state | passes after the join | ρ | reach | SHA-256 |
|---|---|---|---|---|---|
| PC | `bankA.state` | 0 | 1,073,217,792 | 44,017 | `fa18c487279e14b5d0d0746dbd3496535ce1117ca18b6cb00e7abdcce2098dfa` |
| PC | `bankA4/STATE` | 1 | 1,065,535,173 | 2,800 | `5f9f9eeed0b3008e28b35ddfefe2317eb10bb8c8c1dc8187d732ea00355c414c` |
| PC | `bankA5/STATE` | 2 | 1,064,567,945 | 2,504 | `a0e83c883ea2e065b57e6706cdc6320ce7ddd7baccf25a30bfa33f6ce175718d` |
| PC | `bankA6/STATE` | 3 | 1,063,944,589 | 2,344 | `4b54c9da029355636ea9b6c371141c90e6b904bcc18a78372a0e020a22729370` |
| PC | `bankA7/STATE` | 4 | 1,063,687,173 | 2,283 | `1dee7db05633e773c7b9e4e0eda6db1ab54bce979a4014e0a696f35adeb56ea4` |
| cloud | `hjohn/bankA.state` | 0 | 1,073,217,792 | 44,017 | `90660e440a5a6811b70c4fa99e2e4830bd4ed6cce24c27aed2e619e27618f429` |
| cloud | `hjohn/bankA4/STATE` | 1 | 1,065,761,398 | 2,880 | `0983677b150041dba7f3711b7c285ff9684273c1457d621e579434c16403f8ee` |

ρ is on `2^(−30)`. The reach is the number of cells back at which `ρ^L`, carried on `2^(−62)`,
still releases nonzero on `2^(−30)`.

## The commands

```text
python3 -I tools/listener/bank_trace.py requests train_all.txt dev.txt dev.requests
python3 -I tools/listener/bank_trace.py requests train_all.txt train_all.txt train.requests
B complete-language read-tower-bank-trace STATE SHA dev.txt SHA 8 dev.requests SHA OUT UNITS SHA
B complete-language read-tower-bank-trace STATE SHA train_all.txt SHA 8 train.requests SHA OUT UNITS SHA
python3 -I tools/listener/bank_trace.py share train_all.txt dev.txt|train_all.txt OUT
```

The cloud runs used `solenoidal_alpha` at `5cc69bfd5`, which writes the trace at the end; the PC
runs used `97dbb00d4`, which writes each chunk as it finishes (binary SHA-256
`ba78b17709824e1003fe46b931ddada4ea129f14c76f6a08edd681b9dbf75724`, release build 2 min 02 s). The
trace law's cells and reads do not differ between the two.

## The cloud host (4 cores; one run at a time)

| run | projection | deadline | measured wall | ratio | peak resident | trace SHA-256 |
|---|---|---|---|---|---|---|
| development: 50 problems, one stream, one pass | unmeasured, planned at up to 3 min | 180 s | 6.4 s | — | 30,464 KiB | `09f32b584cdf7b6b…` |
| held-out, one pass | 2 rounds × 18,960 cells × 0.624 ms = 23.7 s | 30 s | 23.8 s | 1.00 | 65,924 KiB | `eace23bfdd739d00…` |
| training, one pass | 2 rounds × 167,844 cells × 0.628 ms = 210.8 s | 215 s | **stopped at 215.0 s** | — | 154,856 KiB | none written |
| held-out, the join | 2 rounds × 18,960 × 0.628 ms = 23.8 s | 30 s | 29.5 s | 1.24 | 241,532 KiB | `6dfb04e5d4378ee6…` |

The development read measured 10,223 cells in 6,377 ms, 0.624 ms a cell. The held-out read's chunks
ran 0.617–0.622 ms a cell (11.7–11.8 s each, two rounds of four).

**The training read stopped at its deadline.** Its first round ran 0.623, 0.630, 0.630 and 0.640 ms
a cell against the 0.628 projected; seven of eight chunks finished, and nothing was written, because
`5cc69bfd5` wrote the trace at the end. It was not relaunched with a larger deadline. The next run
changed the partition of what is kept: `97dbb00d4` writes each chunk as it finishes, and the whole
read ran on the PC under its own measured projection.

**The join's held-out read departed from the early-stop rule.** Its projection used the pass-1 rate,
but at the join the reach is 44,017 cells, so each request scans up to 44,017 kept cells rather than
2,880. Its first chunks ran 0.741–0.783 ms a cell against the 0.628 projected, which the rule says
stops the run; it ran on and finished inside its deadline at 29.5 s. Its result stands as measured,
and its rate is the PC's reason for projecting requests separately.

## Brandon's PC (7900X, `RAYON_NUM_THREADS=8`, one run at a time)

The PC first read the held-out text at the join under `timeout 120`: its largest chunk took 4,688 ms
over 18,960 cells, 0.2473 ms a cell. A second read with one request (requests `7931edf1…`) took
4,369 ms for the largest chunk, 0.2304 ms a cell, and gave the request cost: 0.39–0.86 µs a kept
cell, largest 0.864. The training projection at the join adds the requests: 582 requests at most in
a chunk × 44,017 kept cells × 0.864 µs.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| held-out, join | unmeasured | 120 s | 4.8 s | — | 432,376 KiB |
| held-out, passes 1–4 | 18,961 × 0.2473 ms + 0.1 s = 4.8 s | 5 s | 4.5, 4.4, 4.5, 4.5 s | 0.92–0.94 | 95,500, 89,228, 86,044, 84,688 KiB |
| training, join | 167,845 × 0.2332 ms + 582 × 44,017 × 0.864 µs = 39.1 + 22.1 = 61.3 s | 62 s | 50.6 s | 0.83 | 1,062,648 KiB |
| training, passes 1–4 | 167,845 × 0.3012 ms = 50.6 s | 51 s | 39.2, 39.1, 39.1, 39.0 s | 0.77 | 194,760, 181,572, 178,024, 176,604 KiB |

The training passes 1–4 were projected on the largest cost a cell measured before their launch,
the join's 0.3012 ms with its full-reach requests. Every PC run read every request
(`TOWER_BANK_TRACE units=1318 streams=8 skipped=0`; held-out `cells=151684 requests=421`, training
`cells=1342760 requests=4524`).

| trace | SHA-256 |
|---|---|
| held-out, join | `652aa23b8ccb685eb1e0249b9b2ade51bed300128ca2a3f2c7e510f3d96a55cc` |
| held-out, pass 1 | `2af54fc7f62ec931029647475a97d729148eb54b762ea5c44d7a0b3897944b01` |
| held-out, pass 2 | `6ffc400528cf13a6c6304e7fe59b598c6b97d54d5a98739fc34a83ca61eab5b8` |
| held-out, pass 3 | `785fb8c2806cc1c8570b197727578b79cf74c9fb8616c15cbeda5075c526143f` |
| held-out, pass 4 | `96c66466c3daa9da7739f4968145e379dab4999abe1066934fe2c6e88e1c85d9` |
| training, join | `3c5d40006fab636b04ba575a8309d0b340e83ba38de368396d3627f8a5dc1496` |
| training, pass 1 | `362f665e83e20015ebbd9cb6adc49e5db912fe5b96543c9b9bdd04363070f8f3` |
| training, pass 2 | `b2ad7970da05bc7e67c9bb7cce21c71459462e0dd5398f303dcaa49ac4ecd9b8` |
| training, pass 3 | `62dfca48b72db995a0420c63c70e2b687db60fc2bdd274573a9b3be68242dfc6` |
| training, pass 4 | `872ab46c52c4dea725807e10f4bb0582203750d4adbc60ae2aa5d45dcaec3f25` |

The one-request held-out read at the join left trace `a86592bedbc8c24311a1ba1876ddc3b801a2fb91ab23ba7b591bbe59f98d08d4`.
After the reads, the PC worktree's untracked files (only its `.local/btrace/`: the 11 traces, their
logs and share reads, the requests, the runner and the build log) were moved create-new into a run
directory beside the main checkout, where the traces stay with the SHA-256s above; the worktree,
whose only other file was its ignored build target, was removed with `git worktree remove` and
pruned.

The share reads of every trace are in [`SHARES.txt`](SHARES.txt), whole except for the observer's
list of the bytes of the cells the largest address lands on, which is the GSM8K text's. The quarter
lines were read afterwards from the same traces with the observer at `c88e9dcb9`.
