# The read of `lapD8` by the written rules, and the foil's counts

## The read on Brandon's PC

At `e8cf7c86b7fb9bf4a64f5fabddb1be2dbcc73afb`, in a fresh worktree whose own target directory built
the example (`Compiling holonics` from the worktree). Every run went under the run directory's
`wait4` wrapper (`RUN_RECEIPT`), with `RAYON_NUM_THREADS=8` and an 8 GiB memory scope
(`MemoryMax=8G`, `MemorySwapMax=0`), alone on an idle host (load about 2, desktop applications
only).

- Binary `examples/solenoidal_alpha`, SHA-256 `15e044f670c067b9bab1aec1c0d9fb2547f4107079268cf4a52443323ae59760`.
- Key file, 8,388,608 bytes from `/dev/urandom`: `bbe735d7d7c4b48727ec948b622e4a9a8ba267f32dd33928838b15c5ebbac243`.
- Inputs checked by SHA-256: the units `d0973c39…782a`, `role_clock/lapD8/STATE` `70c76578…51c0`,
  the training text `050b94f3…3b95`, the held-out text `e5bffe0e…3153`, and the development slice
  (held-out problems 100 to 227) `0be718d4…5c39`.

```text
B complete-language read-unit-tower-written UNITS SHA role_clock/lapD8/STATE SHA HELD SHA keys.bin SHA 400 AGREE 64 8 OUT
python3 -I tools/gsm8k/written_rules.py dev.txt train_all.txt one two
```

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| build | 119 s | 180 s | 123.1 s | 1.034 | 3,162,480 KiB |
| development read, 128 problems | unmeasured | 180 s | 3.6 s | — | 39,508 KiB |
| one draw, 747 problems | 27.725 s | 30 s | 20.3 s | 0.732 | 41,444 KiB |
| two agreeing draws, 747 problems | 27.725 s | 30 s | 20.9 s | 0.754 | 41,392 KiB |

`r` = 3,568 × 8 / (80,657 + 20,831) = 0.28125 ms a unit a thread; load 58 ms; `D` = 786,972 × `r` / 8
+ 58 = 27,725 ms, rounded up to 30 s; stop line 3,300 ms. The first 64 problems took 1,854 and
1,960 ms. `cmp` of the two `MARKS.tsv` printed nothing (exit 0).

```text
TOWER_WRITTEN_OPEN problems=128 most_calculations=8 window=464 elapsed_ms=58
TOWER_WRITTEN_PROGRESS problems=64 elapsed_ms=1753
TOWER_WRITTEN_PROGRESS problems=128 elapsed_ms=3555
TOWER_WRITTEN problems=128 calculations=426 free_bytes=51340 prompt_units=80657 released_units=20831 most_units_a_problem=2881 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=3568
TOWER_WRITTEN_FILES free_sha256=c852de6f0f53277772a3d43d65f36172f2ecc3018964c2211264460f2aa619e9 marks_sha256=bdc6e260ab118143868f7b8352ca5e9e2d1108fb9b0054c004207c15a5af09c5
RUN_RECEIPT exit=0 wall_s=3.6 peak_rss_kib=39508 user_s=26.9
```

```text
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=41
TOWER_WRITTEN_PROGRESS problems=64 elapsed_ms=1854
TOWER_WRITTEN_PROGRESS problems=128 elapsed_ms=3667
TOWER_WRITTEN_PROGRESS problems=192 elapsed_ms=5565
TOWER_WRITTEN_PROGRESS problems=256 elapsed_ms=7066
TOWER_WRITTEN_PROGRESS problems=320 elapsed_ms=8933
TOWER_WRITTEN_PROGRESS problems=384 elapsed_ms=10459
TOWER_WRITTEN_PROGRESS problems=448 elapsed_ms=12268
TOWER_WRITTEN_PROGRESS problems=512 elapsed_ms=13860
TOWER_WRITTEN_PROGRESS problems=576 elapsed_ms=15592
TOWER_WRITTEN_PROGRESS problems=640 elapsed_ms=17362
TOWER_WRITTEN_PROGRESS problems=704 elapsed_ms=18971
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299695 prompt_units=468588 released_units=121705 most_units_a_problem=4717 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=20279
TOWER_WRITTEN_FILES free_sha256=bbb8f807c1d863beceaf9f6080977a1c6dee6f8f5b5c020accee3befd8fa9d60 marks_sha256=0993896e991b62f844a8aa5816f890ce164382812a93b5beb402155e005fc3d5
RUN_RECEIPT exit=0 wall_s=20.3 peak_rss_kib=41444 user_s=158.8
```

```text
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=43
TOWER_WRITTEN_PROGRESS problems=64 elapsed_ms=1960
TOWER_WRITTEN_PROGRESS problems=128 elapsed_ms=3831
TOWER_WRITTEN_PROGRESS problems=192 elapsed_ms=5476
TOWER_WRITTEN_PROGRESS problems=256 elapsed_ms=7416
TOWER_WRITTEN_PROGRESS problems=320 elapsed_ms=9120
TOWER_WRITTEN_PROGRESS problems=384 elapsed_ms=10829
TOWER_WRITTEN_PROGRESS problems=448 elapsed_ms=12409
TOWER_WRITTEN_PROGRESS problems=512 elapsed_ms=14136
TOWER_WRITTEN_PROGRESS problems=576 elapsed_ms=15971
TOWER_WRITTEN_PROGRESS problems=640 elapsed_ms=17900
TOWER_WRITTEN_PROGRESS problems=704 elapsed_ms=19620
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299808 prompt_units=468588 released_units=119618 most_units_a_problem=4714 agree=2 mark_agree=64 mark_cap=8 elapsed_ms=20837
TOWER_WRITTEN_FILES free_sha256=dc25b32710f28a9f0abbe01e6a36f8853fb9646053fc546998a3c553a204d425 marks_sha256=0993896e991b62f844a8aa5816f890ce164382812a93b5beb402155e005fc3d5
RUN_RECEIPT exit=0 wall_s=20.9 peak_rss_kib=41392 user_s=163.5
```

```text
WRITTEN dir=one problems=747 a_on_problem=167 b_free_calculations=2475 b_free_right=108 c_first_calculations=725 c_from_question=31 b_equals=242/2448 met=225/1572 never_met=17/876 binary +=13/470 -=19/388 *=151/897 /=45/343
WRITTEN dir=two problems=747 a_on_problem=260 b_free_calculations=2402 b_free_right=186 c_first_calculations=698 c_from_question=38 b_equals=242/2448 met=225/1572 never_met=17/876 binary +=13/470 -=19/388 *=151/897 /=45/343
```

The release files hold held-out problem text and stay on the PC, outside the repository.

## The foil's counts, in the container (4 threads)

```text
python3 -I tools/gsm8k/digit_units.py UNITS digit/UNITS
DIGIT_UNITS founded=1062 kept=949 removed=113
```

`digit/UNITS` `186b82ede267df857f1b93e259769d946fecaf07a145c0e352275071c65dd0b4`. The units and
section counts are the `UNIT_READ` and `TOWER_TRAIN` lines of `train-unit-tower` at the recipe
`64 64 256 2 8 128 3 7`, read and stopped at its first section (both lists read the whole training
text into units in 0.6 s):

```text
UNIT_READ units=1318 train_bytes=3528168 train_units=1342760 dev_bytes=397669 dev_units=151684
TOWER_TRAIN material=277542 streams=8 section=128 sections_a_pass=1311 train_bytes=3528168 dev_bytes=397669
UNIT_READ units=1205 train_bytes=3528168 train_units=1535797 dev_bytes=397669 dev_units=173650
TOWER_TRAIN material=262965 streams=8 section=128 sections_a_pass=1499 train_bytes=3528168 dev_bytes=397669
```

On the first 800 training problems (`173c9ac34dcc4d097ea199ddbbf5eaab4f6726951abdb7ddd4d2860869f1f0d0`,
418,797 bytes) the two lists give 155 and 178 sections a pass. The foil's prompt units on all held-out
problems are those of a smoke tower trained one pass on the first 40,000 training bytes and read by
`read-unit-tower-written` (51.8 s on 4 threads; prompts are fixed by the text and the units):

```text
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299634 prompt_units=518610 released_units=142209 most_units_a_problem=4996 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=51847
```

The same smoke on both lists over 16 held-out problems checked the foil end to end: each trained
one pass (4.2 s and 4.1 s), was read by the reader, and was read by the rules with `pair`.
