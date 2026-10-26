# The training-slice read, the heard reads and the rings of the n-grams

## The training-slice read on Brandon's PC

The read fixed in the digit-pieces record §3, in the cause test's run directory, under the `wait4`
wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8`, a memory scope of 8 GiB (`MemoryMax=8G`,
`MemorySwapMax=0`), `timeout 40`, nothing else heavy on the host (load about 1.9). Inputs checked by
full SHA-256 before use:

- binary `solenoidal_alpha` `04232e3d2c4785866fe285a6cf9d84ba422b94ae5e316a3dd655180f0eda70b5`
- committed units `d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a`
- `C`'s `STATE` `84e2bacfc6ea56c49181e4048f21ac32ad502ce67a94a001cd1d2ad9dd1678b4`
- the `lapD8` read's key file `bbe735d7d7c4b48727ec948b622e4a9a8ba267f32dd33928838b15c5ebbac243`
- the training text `050b94f367625ad2c533bb3af53c730ea6d12e140a080a6a3def9ffdc0de3b95`
- the slice `b9a2236637730ef450d69816edd7c64f744e21f2331c683bc9f3651e95ef04b2` (6,730 problems,
  748 taken, 392,606 bytes)
- the rules at `2821b84b0` `68db4494b0ed14ec7cf082f9d1c26f6e259e7604a941794136d014b64e0c5b3c`

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| read `C` on the slice, 748 problems | 33.3 s | 40 s | 12.0 s | 0.360 | 39,652 KiB |

The first 64 problems took 1,028 ms against a stop line of 4,400 ms. Rate: 12.0 s × 8 / (442,909 +
115,949) = 0.1718 ms a unit a thread, within the 0.1765 bound.

```text
TOWER_WRITTEN_OPEN problems=748 most_calculations=7 window=456 elapsed_ms=40
TOWER_WRITTEN problems=748 calculations=2344 free_bytes=300162 prompt_units=442909 released_units=115949 most_units_a_problem=2536 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=11972
TOWER_WRITTEN_FILES free_sha256=93359a569df9d4b02b4b840ac1e9ae36f90c26742450d763dcf39f919821d8d7 marks_sha256=d449dd456d8d595809dde45237b38838b4ef1b325ffba6e98feef8db93c4f001
RUN_RECEIPT exit=0 wall_s=12.0 peak_rss_kib=39652 user_s=94.2
WRITTEN dir=digit/read_C_train9 problems=748 a_on_problem=50 b_free_calculations=1217 b_free_right=41 c_first_calculations=630 c_from_question=23 b_equals=157/2344 met=157/2344 never_met=0/0 binary +=10/434 -=16/402 *=97/814 /=22/345
```

`z` pools 157 / 2,344 and 176 / 1,572: `p` = 333 / 3,916, `z` = (0.06698 − 0.11196) / 0.009093 =
−4.95.

## The heard reads on Brandon's PC

The rules at `09f3683f2` (`written_rules.py`
`4ffae51aed63bf7326dd7df6dd8582f015ca6288a0d05aca5276881d92ca2ff8`), each read under `timeout 60`,
the inputs checked as above and the held-out text `e5bffe0ea3949a2e8efec1c43120918891867c342a9e9ffd288cc798a8363153`.
Every `WRITTEN` line matches the earlier one byte for byte, and each `HEARD` line's bins sum to its
`b_equals` (bin 0 is `never_met`).

```text
python3 -I written_rules_09f3683.py train9.txt train_all.txt heard read_C_train9      (2,069 ms)
WRITTEN dir=digit/read_C_train9 problems=748 a_on_problem=50 b_free_calculations=1217 b_free_right=41 c_first_calculations=630 c_from_question=23 b_equals=157/2344 met=157/2344 never_met=0/0 binary +=10/434 -=16/402 *=97/814 /=22/345
HEARD dir=digit/read_C_train9 0=0/0 1=15/920 2-3=11/345 4-7=11/290 8-15=13/327 16+=107/462

python3 -I written_rules_09f3683.py dev.txt train_all.txt heard read_C read_F          (4,211 ms)
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
HEARD dir=digit/read_C 0=14/876 1=7/239 2-3=11/224 4-7=4/255 8-15=23/326 16+=131/528
WRITTEN dir=digit/read_F problems=747 a_on_problem=38 b_free_calculations=1227 b_free_right=61 c_first_calculations=618 c_from_question=49 b_equals=156/2448 met=131/1572 never_met=25/876 binary +=14/470 -=14/388 *=91/897 /=20/343
HEARD dir=digit/read_F 0=25/876 1=12/239 2-3=3/224 4-7=10/255 8-15=22/326 16+=84/528
```

## The n-grams' heard profile and rings, in the container

The n-gram releases of the written-rules record (`ngram6_out` and `ngram8_out`: `MARKS.tsv`
`b2ff60cf28d8a0b1c6a5f0b3f1da1920fbeb48f65feb7af2e61e71df58b623f4` and
`88a4874a866a965bf1f5eec2c714582a2caa3f44b5292cc7edc475cf0173edab`, `FREE.tsv`
`21e7f5a08870c17d185f5f74cd8e64dd4cf9deb193fb9f907446319b0392fb65` and
`8dffab6a081085126e1ceab72943713d421dca9142a19e61e44a1319fdc6d04a`), read by the rules of this
commit (`heard`, then `rings`; the `WRITTEN` lines are the record's):

```text
HEARD dir=.local/run/written/ngram6_out 0=30/876 1=111/239 2-3=154/224 4-7=223/255 8-15=307/326 16+=523/528
HEARD dir=.local/run/written/ngram8_out 0=34/876 1=206/239 2-3=211/224 4-7=254/255 8-15=326/326 16+=528/528
RINGS dir=.local/run/written/ngram6_out n=312 mod9=24 foil9=37 mod10=232 foil10=80 mod11=15 foil11=26 mod990=4 foil990=2
RINGS dir=.local/run/written/ngram8_out n=312 mod9=22 foil9=35 mod10=237 foil10=82 mod11=21 foil11=25 mod990=8 foil990=1
```

The releases and marks hold held-out problem text and stay outside the repository.

## The smoke of the three unit towers, in the container (4 threads)

The commit's binary (`cdc40104deb6c82d5ff3e108bc8846c0b574a3a0c4976ee8514b35f9270d7949`, built in
the container), the committed units, the first 40,000 training bytes, 16 held-out problems
(9,266 bytes) and a container key stream; one pass, 4 streams, otherwise `C`'s recipe
(`64 64 256 2 4 128 1 7`). The host was building the gate beside it (load about 6), so the times
are a sanity read, not a projection; the PC's development pass fixes the projection.

```text
train-unit-tower
TOWER_PASS pass=0 train_bits_a_byte=3.672 dev_bits_a_byte=3.458 dev_regions Q=2.315 P=3.508 N=2.998 M=3.461 deposits=29/29 pass_ms=5674 elapsed_ms=5711 train_code=149152021594 dev_code=33559587968 grain_bits=20
train-unit-pumped-tower
TOWER_PASS pass=0 train_bits_a_byte=3.634 dev_bits_a_byte=3.418 dev_regions Q=2.014 P=3.378 N=3.014 M=3.424 deposits=29/29 pass_ms=9836 elapsed_ms=9869 train_code=147643927399 dev_code=33174014405 grain_bits=20
train-unit-pair-pumped-tower
TOWER_PASS pass=0 train_bits_a_byte=3.919 dev_bits_a_byte=3.593 dev_regions Q=2.036 P=3.501 N=3.756 M=3.600 deposits=29/29 pass_ms=14641 elapsed_ms=14683 train_code=159197391793 dev_code=34871527555 grain_bits=20
```

Each smoke state was read by `read-unit-tower-written` over the 16 problems (4.7 to 4.9 s each) and
by the rules with `rings`, which ran end to end on all three (`n=4` never-met two-numeral sums and
differences on 16 problems; no reading is drawn from a smoke).
