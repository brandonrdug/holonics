# The capture loop on Brandon's PC

The lines below are the runs' own output, whole, from the PC's run directory; the run paths are
relative to it. Each heavy run ran under the `wait4` wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8`
and its own memory scope (`MemoryMax=8G`, `MemorySwapMax=0`). The per-process load lines are left
out: other programs on the host held about half a core through the run, with one spike near two
cores summed at the level read of `PRC`'s held equals. The load average stood at 0.85 at the build,
7.89 at the training launch (the three development passes had just ended) and 11.26 at the first
written read (the two trainings had just ended). The releases, marks and cells hold held-out problem
text and stay outside the repository. `PRT` and `PRS` were not trained again: their states and reads
are the turned loop's ([TURNS_RUN.md](TURNS_RUN.md)).

The capture these runs measure is retired (the record's §8): its fold is an authored sum. The
receipt is kept as the measurement of that build.

## Build, inputs and the two foundings

Built at `d8dab5ad4` in its own worktree and target directory. Every input matched its digest.
`PRC` is founded with the `captured` law (the rotor modulated, with the navigator and its located
hands), `PRN` with the `numeral` law (the same navigator with no hand).
```text
PROJECTION 124 s (the last builds 117.8 to 123.1 s); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
    Finished `release` profile [optimized] target(s) in 1m 58s
RUN_RECEIPT exit=0 wall_s=118.5 peak_rss_kib=3539380 user_s=194.7
BINARY_SHA256 be18995ee44ff562ae9f19047e10bd96380691d24a067f5d1262562bf454600b RUN/capture/solenoidal_alpha
GIT_LOG d8dab5ad4d430418015e8f3388355870bafaefde brandonrdug@users.noreply.github.com
```

```text
SHA ok UNITS d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
SHA ok digit/keys_tower.bin fcaadc56deeb837ce9e46f2c0d52269022c576bae30facaacea74756a71e9593
SHA ok train_all.txt 050b94f367625ad2c533bb3af53c730ea6d12e140a080a6a3def9ffdc0de3b95
SHA ok dev.txt e5bffe0ea3949a2e8efec1c43120918891867c342a9e9ffd288cc798a8363153
SHA ok digit/dev.roles a7d7ccdccd95b5450cdb6b211ee5a146afea1d76011937041d8517644720c9c1
SHA ok digit/train800.txt 173c9ac34dcc4d097ea199ddbbf5eaab4f6726951abdb7ddd4d2860869f1f0d0
SHA ok written/keys.bin bbe735d7d7c4b48727ec948b622e4a9a8ba267f32dd33928838b15c5ebbac243
SHA ok digit/C/STATE 84e2bacfc6ea56c49181e4048f21ac32ad502ce67a94a001cd1d2ad9dd1678b4
SHA ok pumped/PP/STATE.0 db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b
SHA ok turns/PRT_STATE 26e73cc8cff47e33182d8b49f86ca5db46bda51a9333f7de03bc14c8c0fda128
SHA ok turns/PRT/STATE 3fd266914f9e39a87aa125eea37a2da483f080c4a641f818130c756afef1ec80
SHA places pumped/places_held_equals 6eabb8e6d058583612152142fdfa80fc38f03029ded949821775990bb0d023f9
SHA places pumped/places_held_numerals 81870715e53f9a08dbd2dd8be64823a502713d7761cec8feff37d20c0c3f9b2b
SHA places pumped/places_train_equals a395a9dcf41d6ee0230fd0d71cfe3b6f741fbd239ec2a2aaf45d80409727bb29
SHA places pumped/places_train_numerals 95b456101f08c31c19ddb0141a9e499e03f9335b73a539bc7fc9a4c7aa6dc48f
```

```text
PRC (law captured):
PROJECTION unmeasured (planned at 1 to 3 minutes); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
ROTOR_MENU loops=7204 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=4776 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=36
ROTOR_CLOSURE step=1 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=60
ROTOR_CLOSURE step=2 rows=5210 rank=40 minor_bits=17 torsion=3:2,11:2 carried=33 elapsed_ms=80
ROTOR_CLOSURE step=3 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=101
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=113
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=113
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=113
NAVIGATOR_MENU modulus=9999 width=4 step=1 calculations=16344 operators=4 elapsed_ms=119
NAVIGATOR_HAND byte=* calculations=6287 refused=no_single_line
NAVIGATOR_HAND byte=+ calculations=3815 hand=1 equals=9998
NAVIGATOR_HAND byte=- calculations=3389 hand=9998 equals=9998
NAVIGATOR_HAND byte=/ calculations=2853 refused=no_single_line
NAVIGATOR_EQUALS hand=9998
NAVIGATOR_FOUNDED law=captured level=0 first=7 written=8 hands=+:1,-:9998,=:9998 elapsed_ms=119
ROTOR_FOUNDED step=1 law=captured carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2848599 sha256=aae27e399cb777903ec1ac98146b50ac3a6e0081bcf6b90a3b38759c048e3a80 elapsed_ms=159
RUN_RECEIPT exit=0 wall_s=0.2 peak_rss_kib=45212 user_s=0.1

PRN (law numeral):
PROJECTION unmeasured (planned at 1 to 3 minutes); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
ROTOR_MENU loops=7204 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=4776 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=29
ROTOR_CLOSURE step=1 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=49
ROTOR_CLOSURE step=2 rows=5210 rank=40 minor_bits=17 torsion=3:2,11:2 carried=33 elapsed_ms=65
ROTOR_CLOSURE step=3 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=84
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=97
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=97
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=97
NAVIGATOR_MENU modulus=9999 width=4 step=1 calculations=16344 operators=4 elapsed_ms=103
NAVIGATOR_HAND byte=* calculations=6287 refused=no_single_line
NAVIGATOR_HAND byte=+ calculations=3815 hand=1 equals=9998
NAVIGATOR_HAND byte=- calculations=3389 hand=9998 equals=9998
NAVIGATOR_HAND byte=/ calculations=2853 refused=no_single_line
NAVIGATOR_EQUALS hand=9998
NAVIGATOR_FOUNDED law=numeral level=0 first=7 written=8 hands=none elapsed_ms=103
ROTOR_FOUNDED step=1 law=numeral carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2848578 sha256=4d3dc3ffe1c6dbfb7b89cb1c3abf9b52ed23ab309e3208815746690005cc1c92 elapsed_ms=153
RUN_RECEIPT exit=0 wall_s=0.2 peak_rss_kib=46072 user_s=0.1
```

## The development passes and the projection

`PRC`, `PRN` and `PRT` ran their development passes together. The capture binary on `PRT`'s founded
state reproduced the turned loop's development `STATE.0` bit for bit (`62090aa0…`).
```text
PRC:
TOWER_STATE STATE.0 state_bytes=12539127 state_sha256=efade019969f209d5b3c56dfa6797e170462dd7cd7d6e277ad697cb990901d11
TOWER_PASS pass=0 train_bits_a_byte=2.878 dev_bits_a_byte=2.470 dev_regions Q=1.793 P=2.850 N=1.757 M=2.480 deposits=155/155 pass_ms=23658 elapsed_ms=23678 train_code=1257867603942 dev_code=1029935196241 grain_bits=20
TOWER_DONE state_bytes=12539127 state_sha256=efade019969f209d5b3c56dfa6797e170462dd7cd7d6e277ad697cb990901d11 elapsed_ms=23741
RUN_RECEIPT exit=0 wall_s=23.8 peak_rss_kib=273328 user_s=143.9
PRN:
TOWER_STATE STATE.0 state_bytes=12499707 state_sha256=47d16a690c5c9dec65842b4d7020b4d100e85c66f42a0446a69eae92fca92c0c
TOWER_PASS pass=0 train_bits_a_byte=2.858 dev_bits_a_byte=2.483 dev_regions Q=1.886 P=2.936 N=1.787 M=2.490 deposits=155/155 pass_ms=23081 elapsed_ms=23101 train_code=1249142382297 dev_code=1035116240321 grain_bits=20
TOWER_DONE state_bytes=12499707 state_sha256=47d16a690c5c9dec65842b4d7020b4d100e85c66f42a0446a69eae92fca92c0c elapsed_ms=23167
RUN_RECEIPT exit=0 wall_s=23.2 peak_rss_kib=269944 user_s=140.2
PRT:
TOWER_STATE STATE.0 state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb
TOWER_PASS pass=0 train_bits_a_byte=2.907 dev_bits_a_byte=2.503 dev_regions Q=1.805 P=3.021 N=1.536 M=2.513 deposits=155/155 pass_ms=22820 elapsed_ms=22843 train_code=1270417675348 dev_code=1043744519153 grain_bits=20
TOWER_DONE state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb elapsed_ms=22931
RUN_RECEIPT exit=0 wall_s=23.0 peak_rss_kib=264436 user_s=140.4
```

```text
NUMBER w_PRT_of turns/dev_PRT.first.log: 100.0938 from turns/dev_PRT.first.log pass=0 section=64 ms=3203 evaluations=32
NUMBER w_PRT_of turns/dev_PRT.log: 120.5000 from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32
NUMBER w_PRT_of turns/PRT.log: 113.8750 from turns/PRT.log pass=2 section=448 ms=3644 evaluations=32
NUMBER w_PRT_of capture/dev_PRT.log: 112.7812 from capture/dev_PRT.log pass=0 section=96 ms=3609 evaluations=32
NUMBER w_PRT=120.5000 ms_an_evaluation from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32 (over every full window of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log)
NUMBER eta_PRT=0.090323 from turns/dev_PRT.log pass=0 halvings=14 sections=155 (over every pass of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log)
NUMBER h_PRT=5317 ms from turns/dev_PRT.log pass=0 (over every pass of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log)
NUMBER d_PRC=114.2963 from capture/dev_PRC.log pass=0 section=155 ms=3086 evaluations=27 sections=27 (partial)
NUMBER d_PRC_full_windows_only=112.0625 from capture/dev_PRC.log pass=0 section=128 ms=3586 evaluations=32 (not used)
NUMBER d_PRN=112.2500 from capture/dev_PRN.log pass=0 section=96 ms=3592 evaluations=32
NUMBER d_PRN_full_windows_only=112.2500 from capture/dev_PRN.log pass=0 section=96 ms=3592 evaluations=32 (not used)
NUMBER d_PRT=112.7812 from capture/dev_PRT.log pass=0 section=96 ms=3609 evaluations=32
NUMBER d_PRT_full_windows_only=112.7812 from capture/dev_PRT.log pass=0 section=96 ms=3609 evaluations=32 (not used)
NUMBER w_PRC = w_PRT x max(1, d_PRC/d_PRT) = 120.5000 x max(1, 1.013433) = 122.1187 ms_an_evaluation
NUMBER eta_PRC=max(eta_PRT 0.090323, own 0.264516 from capture/dev_PRC.log pass=0 halvings=41 sections=155)=0.264516
NUMBER h_PRC=max(h_PRT 5317, own 4958 from capture/dev_PRC.log pass=0)=5317 ms
PROJECTION_PRC 3 x (1311 x 1.12 x 122.1187 x (1 + 0.264516) + 5317) + 1000 ms = 697.17 s; DEADLINE 698 s; bound 1.12 x 122.1187 = 136.7730 ms an evaluation
NUMBER w_PRN = w_PRT x max(1, d_PRN/d_PRT) = 120.5000 x max(1, 0.995290) = 120.5000 ms_an_evaluation
NUMBER eta_PRN=max(eta_PRT 0.090323, own 0.167742 from capture/dev_PRN.log pass=0 halvings=26 sections=155)=0.167742
NUMBER h_PRN=max(h_PRT 5317, own 5089 from capture/dev_PRN.log pass=0)=5317 ms
PROJECTION_PRN 3 x (1311 x 1.12 x 120.5000 x (1 + 0.167742) + 5317) + 1000 ms = 636.79 s; DEADLINE 637 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation
```

## Training

```text
PRC: TOWER_STATE STATE.0 state_bytes=12475064 state_sha256=b147f3fc816a89b366f52f7233c99d3a75bfc1213ce7f3e5364e52524c23261b
PRC: TOWER_PASS pass=0 train_bits_a_byte=2.162 dev_bits_a_byte=1.943 dev_regions Q=1.358 P=2.356 N=0.610 M=1.953 deposits=1311/1311 pass_ms=135533 elapsed_ms=135551 train_code=7997653332176 dev_code=810279828094 grain_bits=20
PRC: TOWER_STATE STATE.1 state_bytes=12428129 state_sha256=3c189604b956acc6c35a584f6b181553ca0ceec150e8a8f7ccdaa1f75e7779a1
PRC: TOWER_PASS pass=1 train_bits_a_byte=1.843 dev_bits_a_byte=1.835 dev_regions Q=1.204 P=2.246 N=0.347 M=1.845 deposits=1311/1311 pass_ms=136560 elapsed_ms=272112 train_code=6816626592276 dev_code=764926691882 grain_bits=20
PRC: TOWER_STATE STATE.2 state_bytes=12420797 state_sha256=40b4b3fec23c7c09c11795f407722277a532d19a320dffece43051efcb43b766
PRC: TOWER_PASS pass=2 train_bits_a_byte=1.755 dev_bits_a_byte=1.779 dev_regions Q=1.127 P=2.189 N=0.335 M=1.790 deposits=1311/1311 pass_ms=137094 elapsed_ms=409206 train_code=6489698568398 dev_code=741815257843 grain_bits=20
PRC: TOWER_DONE state_bytes=12420797 state_sha256=40b4b3fec23c7c09c11795f407722277a532d19a320dffece43051efcb43b766 elapsed_ms=409267
PRC: RUN_RECEIPT exit=0 wall_s=409.7 peak_rss_kib=292788 user_s=2459.8
PRN: TOWER_STATE STATE.0 state_bytes=12444819 state_sha256=56e04fc9f8a7c7eace98aa2a846fd591740cb9cc4f45c613dc49c4ac5e8b6878
PRN: TOWER_PASS pass=0 train_bits_a_byte=2.151 dev_bits_a_byte=1.933 dev_regions Q=1.435 P=2.481 N=0.666 M=1.941 deposits=1311/1311 pass_ms=135634 elapsed_ms=135652 train_code=7955216751989 dev_code=806103334279 grain_bits=20
PRN: TOWER_STATE STATE.1 state_bytes=12405344 state_sha256=67733158be949c607ae0eff685924be98b8c5da5b83836ca6f3b2208cca2910f
PRN: TOWER_PASS pass=1 train_bits_a_byte=1.832 dev_bits_a_byte=1.818 dev_regions Q=1.352 P=2.465 N=0.453 M=1.824 deposits=1311/1311 pass_ms=136120 elapsed_ms=271773 train_code=6777919712137 dev_code=757929888369 grain_bits=20
PRN: TOWER_STATE STATE.2 state_bytes=12424758 state_sha256=ef3de575590a2fcf59b3c4de3d89513fc8fb191e83e11fb25a306c2d11e21d62
PRN: TOWER_PASS pass=2 train_bits_a_byte=1.743 dev_bits_a_byte=1.761 dev_regions Q=1.231 P=2.362 N=0.483 M=1.769 deposits=1311/1311 pass_ms=136896 elapsed_ms=408669 train_code=6445862750608 dev_code=734384397170 grain_bits=20
PRN: TOWER_DONE state_bytes=12424758 state_sha256=ef3de575590a2fcf59b3c4de3d89513fc8fb191e83e11fb25a306c2d11e21d62 elapsed_ms=408734
PRN: RUN_RECEIPT exit=0 wall_s=409.1 peak_rss_kib=296372 user_s=2455.5
```

The guard wrote 246 window lines, with no `OVER` and no `GUARD_STOP`. The largest windows were
`PRC` pass 2 section 1248 (3,332 ms against a limit of 4,376.7, 0.761) and `PRN` pass 2 section 320
(3,358 ms against 4,318.7, 0.778). The trainings halved 34 (`PRC`) and 26 (`PRN`) times over 1,311
sections, against the development pass's 41 and 26 over 155, so the projection was high.

## The written reads and the rules

```text
READ_GUARD ok progress 64 by 1705 ms
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=69
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299841 prompt_units=468588 released_units=116140 most_units_a_problem=4703 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17168
TOWER_WRITTEN_FILES free_sha256=c4bea5a5820ab6a0f77500b1efb33eff9869acae99431a8f4b783f978d7d1c0d marks_sha256=405d096350819d80551ceaf3219d77a9cd4d69a11d80b0528b1d0d8f06248789
RUN_RECEIPT exit=0 wall_s=17.2 peak_rss_kib=43252 user_s=135.7
READ_GUARD ok progress 64 by 1754 ms
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=46
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299782 prompt_units=468588 released_units=114433 most_units_a_problem=4705 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17265
TOWER_WRITTEN_FILES free_sha256=f3fa92067336b71b715383b644b147c80dbcbc0a65dce4d4e3612d97ecc28a70 marks_sha256=93fa45a87b170d7fa019e48369130fbe541ad32c219b5123d0dcafd70fab16a9
RUN_RECEIPT exit=0 wall_s=17.3 peak_rss_kib=41920 user_s=135.0
```

```text
RULES rings digit/read_C rotor/read_PP rotor/read_PR turns/read_PRT turns/read_PRS capture/read_PRC capture/read_PRN; DEADLINE 60 s
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
RINGS dir=digit/read_C n=312 mod9=44 foil9=39 mod10=109 foil10=76 mod11=30 foil11=26 mod990=6 foil990=1
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
RINGS dir=rotor/read_PP n=312 mod9=39 foil9=32 mod10=113 foil10=84 mod11=23 foil11=23 mod990=3 foil990=1
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
RINGS dir=rotor/read_PR n=312 mod9=32 foil9=35 mod10=123 foil10=88 mod11=27 foil11=30 mod990=4 foil990=4
WRITTEN dir=turns/read_PRT problems=747 a_on_problem=59 b_free_calculations=1543 b_free_right=58 c_first_calculations=673 c_from_question=19 b_equals=240/2448 met=216/1572 never_met=24/876 binary +=26/470 -=28/388 *=124/897 /=46/343
RINGS dir=turns/read_PRT n=312 mod9=45 foil9=25 mod10=122 foil10=76 mod11=37 foil11=23 mod990=7 foil990=1
WRITTEN dir=turns/read_PRS problems=747 a_on_problem=41 b_free_calculations=1557 b_free_right=69 c_first_calculations=685 c_from_question=34 b_equals=288/2448 met=269/1572 never_met=19/876 binary +=29/470 -=24/388 *=169/897 /=48/343
RINGS dir=turns/read_PRS n=312 mod9=35 foil9=22 mod10=132 foil10=95 mod11=20 foil11=21 mod990=2 foil990=4
WRITTEN dir=capture/read_PRC problems=747 a_on_problem=43 b_free_calculations=1794 b_free_right=138 c_first_calculations=714 c_from_question=46 b_equals=359/2448 met=322/1572 never_met=37/876 binary +=79/470 -=71/388 *=139/897 /=37/343
RINGS dir=capture/read_PRC n=312 mod9=53 foil9=28 mod10=153 foil10=73 mod11=45 foil11=34 mod990=23 foil990=6
WRITTEN dir=capture/read_PRN problems=747 a_on_problem=43 b_free_calculations=1448 b_free_right=58 c_first_calculations=663 c_from_question=28 b_equals=253/2448 met=232/1572 never_met=21/876 binary +=21/470 -=25/388 *=150/897 /=42/343
RINGS dir=capture/read_PRN n=312 mod9=43 foil9=38 mod10=119 foil10=89 mod11=25 foil11=28 mod990=5 foil990=3
RUN_RECEIPT exit=0 wall_s=14.7 peak_rss_kib=62320 user_s=14.5
RULES heard turns/read_PRT capture/read_PRC capture/read_PRN; DEADLINE 60 s
WRITTEN dir=turns/read_PRT (as above)
HEARD dir=turns/read_PRT 0=24/876 1=8/239 2-3=16/224 4-7=9/255 8-15=42/326 16+=141/528
WRITTEN dir=capture/read_PRC (as above)
HEARD dir=capture/read_PRC 0=37/876 1=21/239 2-3=32/224 4-7=30/255 8-15=77/326 16+=162/528
WRITTEN dir=capture/read_PRN (as above)
HEARD dir=capture/read_PRN 0=21/876 1=10/239 2-3=17/224 4-7=18/255 8-15=39/326 16+=148/528
RUN_RECEIPT exit=0 wall_s=6.3 peak_rss_kib=61944 user_s=6.2
RULES pair capture/read_PRC turns/read_PRT; DEADLINE 60 s
PAIRED met_only_a=194 met_only_b=88 met_both=128 never_only_a=28 never_only_b=15 never_both=9
RUN_RECEIPT exit=0 wall_s=4.3 peak_rss_kib=61452 user_s=4.2
RULES pair capture/read_PRC capture/read_PRN; DEADLINE 60 s
PAIRED met_only_a=199 met_only_b=109 met_both=123 never_only_a=29 never_only_b=13 never_both=8
RUN_RECEIPT exit=0 wall_s=4.3 peak_rss_kib=61728 user_s=4.2
RULES pair capture/read_PRN turns/read_PRT; DEADLINE 60 s
PAIRED met_only_a=118 met_only_b=102 met_both=114 never_only_a=16 never_only_b=19 never_both=5
RUN_RECEIPT exit=0 wall_s=4.3 peak_rss_kib=60712 user_s=4.2
```

In the `heard` and pair runs each `WRITTEN` line repeats the rings run's line exactly and is
written "(as above)" or left out.

## The gaps read

```text
RULES gaps digit/read_C rotor/read_PP rotor/read_PR turns/read_PRT turns/read_PRS capture/read_PRC capture/read_PRN; DEADLINE 60 s
GAPS dir=digit/read_C set=all n=2448 right=190 wrong=2258 unfinished=17 not_number=1 unread=0 numbers=2240
GAP_SIZE dir=digit/read_C set=all n=2240 x2=883 x10=1956 tenth=45 opposite_sign=0 smaller=1521 larger=719 digits=1081 foil_digits=769/2200
GAP_RINGS dir=digit/read_C set=all n=2198 mod9=203 foil9=232/2158 mod10=703 foil10=490/2158 mod11=102 foil11=161/2158 mod7=230 foil7=285/2158 mod13=91 foil13=144/2158
GAP_FROM dir=digit/read_C set=all n=2240 heard_result=2211 operand=221 other_operation=107/1909
GAP_WRITES dir=digit/read_C set=all written=2430 distinct=87 top10=1583 commonest=8:474:35
GAP_LENGTH dir=digit/read_C set=all 1=85/485 2=95/1252 3=10/508 4=0/139 5+=0/64
GAPS dir=digit/read_C set=met n=1572 right=176 wrong=1396 unfinished=2 not_number=1 unread=0 numbers=1393
GAP_SIZE dir=digit/read_C set=met n=1393 x2=636 x10=1290 tenth=20 opposite_sign=0 smaller=958 larger=435 digits=699 foil_digits=507/1362
GAP_RINGS dir=digit/read_C set=met n=1386 mod9=111 foil9=132/1355 mod10=426 foil10=270/1355 mod11=50 foil11=93/1355 mod7=126 foil7=181/1355 mod13=35 foil13=88/1355
GAP_FROM dir=digit/read_C set=met n=1393 heard_result=1386 operand=153 other_operation=94/1321
GAP_WRITES dir=digit/read_C set=met written=1569 distinct=62 top10=1183 commonest=8:334:33
GAP_LENGTH dir=digit/read_C set=met 1=80/383 2=90/878 3=6/264 4=0/44 5+=0/3
GAPS dir=digit/read_C set=never n=876 right=14 wrong=862 unfinished=15 not_number=0 unread=0 numbers=847
GAP_SIZE dir=digit/read_C set=never n=847 x2=247 x10=666 tenth=25 opposite_sign=0 smaller=563 larger=284 digits=382 foil_digits=253/842
GAP_RINGS dir=digit/read_C set=never n=812 mod9=92 foil9=89/807 mod10=277 foil10=190/807 mod11=52 foil11=65/807 mod7=104 foil7=114/807 mod13=56 foil13=50/807
GAP_FROM dir=digit/read_C set=never n=847 heard_result=825 operand=68 other_operation=13/588
GAP_WRITES dir=digit/read_C set=never written=861 distinct=71 top10=542 commonest=8:140:2
GAP_LENGTH dir=digit/read_C set=never 1=5/102 2=5/374 3=4/244 4=0/95 5+=0/61
GAPS dir=rotor/read_PP set=all n=2448 right=109 wrong=2339 unfinished=33 not_number=6 unread=0 numbers=2300
GAP_SIZE dir=rotor/read_PP set=all n=2300 x2=1047 x10=2076 tenth=56 opposite_sign=0 smaller=1316 larger=984 digits=1270 foil_digits=850/2267
GAP_RINGS dir=rotor/read_PP set=all n=2256 mod9=161 foil9=198/2221 mod10=651 foil10=471/2221 mod11=121 foil11=178/2221 mod7=252 foil7=281/2221 mod13=89 foil13=146/2221
GAP_FROM dir=rotor/read_PP set=all n=2300 heard_result=2280 operand=130 other_operation=95/1976
GAP_WRITES dir=rotor/read_PP set=all written=2409 distinct=114 top10=1628 commonest=8:716:44
GAP_LENGTH dir=rotor/read_PP set=all 1=64/485 2=38/1252 3=7/508 4=0/139 5+=0/64
GAPS dir=rotor/read_PP set=met n=1572 right=104 wrong=1468 unfinished=3 not_number=2 unread=0 numbers=1463
GAP_SIZE dir=rotor/read_PP set=met n=1463 x2=778 x10=1388 tenth=36 opposite_sign=0 smaller=814 larger=649 digits=871 foil_digits=556/1435
GAP_RINGS dir=rotor/read_PP set=met n=1456 mod9=71 foil9=103/1428 mod10=365 foil10=243/1428 mod11=71 foil11=111/1428 mod7=161 foil7=196/1428 mod13=44 foil13=80/1428
GAP_FROM dir=rotor/read_PP set=met n=1463 heard_result=1461 operand=86 other_operation=85/1390
GAP_WRITES dir=rotor/read_PP set=met written=1567 distinct=78 top10=1143 commonest=8:574:42
GAP_LENGTH dir=rotor/read_PP set=met 1=62/383 2=36/878 3=6/264 4=0/44 5+=0/3
GAPS dir=rotor/read_PP set=never n=876 right=5 wrong=871 unfinished=30 not_number=4 unread=0 numbers=837
GAP_SIZE dir=rotor/read_PP set=never n=837 x2=269 x10=688 tenth=20 opposite_sign=0 smaller=502 larger=335 digits=399 foil_digits=260/830
GAP_RINGS dir=rotor/read_PP set=never n=800 mod9=90 foil9=82/791 mod10=286 foil10=195/791 mod11=50 foil11=68/791 mod7=91 foil7=129/791 mod13=45 foil13=63/791
GAP_FROM dir=rotor/read_PP set=never n=837 heard_result=819 operand=44 other_operation=10/586
GAP_WRITES dir=rotor/read_PP set=never written=842 distinct=99 top10=511 commonest=8:142:2
GAP_LENGTH dir=rotor/read_PP set=never 1=2/102 2=2/374 3=1/244 4=0/95 5+=0/61
GAPS dir=rotor/read_PR set=all n=2448 right=277 wrong=2171 unfinished=0 not_number=9 unread=0 numbers=2162
GAP_SIZE dir=rotor/read_PR set=all n=2162 x2=1181 x10=1998 tenth=80 opposite_sign=0 smaller=1233 larger=929 digits=1362 foil_digits=883/2125
GAP_RINGS dir=rotor/read_PR set=all n=2117 mod9=180 foil9=205/2079 mod10=809 foil10=608/2079 mod11=79 foil11=169/2079 mod7=193 foil7=280/2079 mod13=100 foil13=148/2079
GAP_FROM dir=rotor/read_PR set=all n=2162 heard_result=2155 operand=197 other_operation=74/1827
GAP_WRITES dir=rotor/read_PR set=all written=2439 distinct=88 top10=1540 commonest=8:289:37
GAP_LENGTH dir=rotor/read_PR set=all 1=116/485 2=117/1252 3=42/508 4=1/139 5+=1/64
GAPS dir=rotor/read_PR set=met n=1572 right=259 wrong=1313 unfinished=0 not_number=7 unread=0 numbers=1306
GAP_SIZE dir=rotor/read_PR set=met n=1306 x2=855 x10=1268 tenth=40 opposite_sign=0 smaller=714 larger=592 digits=875 foil_digits=515/1279
GAP_RINGS dir=rotor/read_PR set=met n=1301 mod9=94 foil9=134/1274 mod10=487 foil10=352/1274 mod11=30 foil11=105/1274 mod7=85 foil7=183/1274 mod13=44 foil13=79/1274
GAP_FROM dir=rotor/read_PR set=met n=1306 heard_result=1305 operand=149 other_operation=66/1234
GAP_WRITES dir=rotor/read_PR set=met written=1565 distinct=56 top10=1090 commonest=8:242:35
GAP_LENGTH dir=rotor/read_PR set=met 1=112/383 2=107/878 3=39/264 4=1/44 5+=0/3
GAPS dir=rotor/read_PR set=never n=876 right=18 wrong=858 unfinished=0 not_number=2 unread=0 numbers=856
GAP_SIZE dir=rotor/read_PR set=never n=856 x2=326 x10=730 tenth=40 opposite_sign=0 smaller=519 larger=337 digits=487 foil_digits=311/849
GAP_RINGS dir=rotor/read_PR set=never n=816 mod9=86 foil9=98/808 mod10=322 foil10=245/808 mod11=49 foil11=71/808 mod7=108 foil7=119/808 mod13=56 foil13=62/808
GAP_FROM dir=rotor/read_PR set=never n=856 heard_result=850 operand=48 other_operation=8/593
GAP_WRITES dir=rotor/read_PR set=never written=874 distinct=76 top10=570 commonest=56:88:0
GAP_LENGTH dir=rotor/read_PR set=never 1=4/102 2=10/374 3=3/244 4=0/95 5+=1/61
GAPS dir=turns/read_PRT set=all n=2448 right=240 wrong=2208 unfinished=7 not_number=1 unread=0 numbers=2200
GAP_SIZE dir=turns/read_PRT set=all n=2200 x2=1182 x10=2024 tenth=74 opposite_sign=0 smaller=1003 larger=1197 digits=1444 foil_digits=902/2170
GAP_RINGS dir=turns/read_PRT set=all n=2148 mod9=208 foil9=231/2116 mod10=794 foil10=600/2116 mod11=114 foil11=161/2116 mod7=221 foil7=267/2116 mod13=103 foil13=149/2116
GAP_FROM dir=turns/read_PRT set=all n=2200 heard_result=2164 operand=179 other_operation=63/1869
GAP_WRITES dir=turns/read_PRT set=all written=2440 distinct=138 top10=1209 commonest=8:340:43
GAP_LENGTH dir=turns/read_PRT set=all 1=89/485 2=122/1252 3=26/508 4=3/139 5+=0/64
GAPS dir=turns/read_PRT set=met n=1572 right=216 wrong=1356 unfinished=3 not_number=0 unread=0 numbers=1353
GAP_SIZE dir=turns/read_PRT set=met n=1353 x2=847 x10=1302 tenth=37 opposite_sign=0 smaller=615 larger=738 digits=969 foil_digits=568/1327
GAP_RINGS dir=turns/read_PRT set=met n=1342 mod9=101 foil9=137/1316 mod10=482 foil10=331/1316 mod11=49 foil11=97/1316 mod7=114 foil7=161/1316 mod13=44 foil13=81/1316
GAP_FROM dir=turns/read_PRT set=met n=1353 heard_result=1351 operand=142 other_operation=52/1281
GAP_WRITES dir=turns/read_PRT set=met written=1569 distinct=86 top10=889 commonest=8:264:40
GAP_LENGTH dir=turns/read_PRT set=met 1=82/383 2=110/878 3=23/264 4=1/44 5+=0/3
GAPS dir=turns/read_PRT set=never n=876 right=24 wrong=852 unfinished=4 not_number=1 unread=0 numbers=847
GAP_SIZE dir=turns/read_PRT set=never n=847 x2=335 x10=722 tenth=37 opposite_sign=0 smaller=388 larger=459 digits=475 foil_digits=286/842
GAP_RINGS dir=turns/read_PRT set=never n=806 mod9=107 foil9=87/799 mod10=312 foil10=219/799 mod11=65 foil11=57/799 mod7=107 foil7=103/799 mod13=59 foil13=68/799
GAP_FROM dir=turns/read_PRT set=never n=847 heard_result=813 operand=37 other_operation=11/588
GAP_WRITES dir=turns/read_PRT set=never written=871 distinct=118 top10=436 commonest=8:76:3
GAP_LENGTH dir=turns/read_PRT set=never 1=7/102 2=12/374 3=3/244 4=2/95 5+=0/61
GAPS dir=turns/read_PRS set=all n=2448 right=288 wrong=2160 unfinished=2 not_number=3 unread=0 numbers=2155
GAP_SIZE dir=turns/read_PRS set=all n=2155 x2=1085 x10=1999 tenth=59 opposite_sign=0 smaller=1382 larger=773 digits=1255 foil_digits=831/2110
GAP_RINGS dir=turns/read_PRS set=all n=2110 mod9=166 foil9=240/2065 mod10=792 foil10=555/2065 mod11=77 foil11=165/2065 mod7=196 foil7=276/2065 mod13=77 foil13=141/2065
GAP_FROM dir=turns/read_PRS set=all n=2155 heard_result=2143 operand=278 other_operation=84/1824
GAP_WRITES dir=turns/read_PRS set=all written=2443 distinct=109 top10=1403 commonest=8:397:40
GAP_LENGTH dir=turns/read_PRS set=all 1=107/485 2=127/1252 3=51/508 4=3/139 5+=0/64
GAPS dir=turns/read_PRS set=met n=1572 right=269 wrong=1303 unfinished=0 not_number=0 unread=0 numbers=1303
GAP_SIZE dir=turns/read_PRS set=met n=1303 x2=777 x10=1267 tenth=26 opposite_sign=0 smaller=821 larger=482 digits=817 foil_digits=496/1273
GAP_RINGS dir=turns/read_PRS set=met n=1297 mod9=71 foil9=144/1267 mod10=470 foil10=309/1267 mod11=33 foil11=100/1267 mod7=86 foil7=169/1267 mod13=20 foil13=82/1267
GAP_FROM dir=turns/read_PRS set=met n=1303 heard_result=1302 operand=204 other_operation=77/1232
GAP_WRITES dir=turns/read_PRS set=met written=1572 distinct=58 top10=1090 commonest=8:313:38
GAP_LENGTH dir=turns/read_PRS set=met 1=99/383 2=123/878 3=44/264 4=3/44 5+=0/3
GAPS dir=turns/read_PRS set=never n=876 right=19 wrong=857 unfinished=2 not_number=3 unread=0 numbers=852
GAP_SIZE dir=turns/read_PRS set=never n=852 x2=308 x10=732 tenth=33 opposite_sign=0 smaller=561 larger=291 digits=438 foil_digits=280/846
GAP_RINGS dir=turns/read_PRS set=never n=813 mod9=95 foil9=97/807 mod10=322 foil10=209/807 mod11=44 foil11=69/807 mod7=110 foil7=109/807 mod13=57 foil13=68/807
GAP_FROM dir=turns/read_PRS set=never n=852 heard_result=841 operand=74 other_operation=7/592
GAP_WRITES dir=turns/read_PRS set=never written=871 distinct=99 top10=455 commonest=8:84:2
GAP_LENGTH dir=turns/read_PRS set=never 1=8/102 2=4/374 3=7/244 4=0/95 5+=0/61
GAPS dir=capture/read_PRC set=all n=2448 right=359 wrong=2089 unfinished=14 not_number=0 unread=0 numbers=2075
GAP_SIZE dir=capture/read_PRC set=all n=2075 x2=1029 x10=1868 tenth=86 opposite_sign=0 smaller=1449 larger=626 digits=1277 foil_digits=840/2045
GAP_RINGS dir=capture/read_PRC set=all n=2022 mod9=191 foil9=202/1988 mod10=875 foil10=554/1988 mod11=98 foil11=161/1988 mod7=138 foil7=270/1988 mod13=63 foil13=102/1988
GAP_FROM dir=capture/read_PRC set=all n=2075 heard_result=2059 operand=192 other_operation=80/1764
GAP_WRITES dir=capture/read_PRC set=all written=2434 distinct=116 top10=1313 commonest=5:215:29
GAP_LENGTH dir=capture/read_PRC set=all 1=138/485 2=183/1252 3=38/508 4=0/139 5+=0/64
GAPS dir=capture/read_PRC set=met n=1572 right=322 wrong=1250 unfinished=4 not_number=0 unread=0 numbers=1246
GAP_SIZE dir=capture/read_PRC set=met n=1246 x2=733 x10=1202 tenth=48 opposite_sign=0 smaller=872 larger=374 digits=846 foil_digits=506/1219
GAP_RINGS dir=capture/read_PRC set=met n=1235 mod9=97 foil9=107/1207 mod10=526 foil10=311/1207 mod11=30 foil11=88/1207 mod7=61 foil7=151/1207 mod13=24 foil13=55/1207
GAP_FROM dir=capture/read_PRC set=met n=1246 heard_result=1246 operand=139 other_operation=73/1192
GAP_WRITES dir=capture/read_PRC set=met written=1568 distinct=70 top10=953 commonest=6:166:42
GAP_LENGTH dir=capture/read_PRC set=met 1=129/383 2=162/878 3=31/264 4=0/44 5+=0/3
GAPS dir=capture/read_PRC set=never n=876 right=37 wrong=839 unfinished=10 not_number=0 unread=0 numbers=829
GAP_SIZE dir=capture/read_PRC set=never n=829 x2=296 x10=666 tenth=38 opposite_sign=0 smaller=577 larger=252 digits=431 foil_digits=301/826
GAP_RINGS dir=capture/read_PRC set=never n=787 mod9=94 foil9=91/781 mod10=349 foil10=206/781 mod11=68 foil11=60/781 mod7=77 foil7=105/781 mod13=39 foil13=58/781
GAP_FROM dir=capture/read_PRC set=never n=829 heard_result=813 operand=53 other_operation=7/572
GAP_WRITES dir=capture/read_PRC set=never written=866 distinct=103 top10=425 commonest=5:59:4
GAP_LENGTH dir=capture/read_PRC set=never 1=9/102 2=21/374 3=7/244 4=0/95 5+=0/61
GAPS dir=capture/read_PRN set=all n=2448 right=253 wrong=2195 unfinished=2 not_number=1 unread=0 numbers=2192
GAP_SIZE dir=capture/read_PRN set=all n=2192 x2=1018 x10=2030 tenth=44 opposite_sign=0 smaller=1455 larger=737 digits=1186 foil_digits=797/2163
GAP_RINGS dir=capture/read_PRN set=all n=2146 mod9=171 foil9=214/2116 mod10=781 foil10=579/2116 mod11=78 foil11=150/2116 mod7=201 foil7=300/2116 mod13=73 foil13=104/2116
GAP_FROM dir=capture/read_PRN set=all n=2192 heard_result=2166 operand=288 other_operation=98/1857
GAP_WRITES dir=capture/read_PRN set=all written=2445 distinct=122 top10=1567 commonest=8:612:46
GAP_LENGTH dir=capture/read_PRN set=all 1=110/485 2=96/1252 3=45/508 4=2/139 5+=0/64
GAPS dir=capture/read_PRN set=met n=1572 right=232 wrong=1340 unfinished=1 not_number=1 unread=0 numbers=1338
GAP_SIZE dir=capture/read_PRN set=met n=1338 x2=726 x10=1288 tenth=16 opposite_sign=0 smaller=908 larger=430 digits=769 foil_digits=481/1310
GAP_RINGS dir=capture/read_PRN set=met n=1332 mod9=78 foil9=124/1304 mod10=471 foil10=324/1304 mod11=34 foil11=85/1304 mod7=108 foil7=177/1304 mod13=28 foil13=68/1304
GAP_FROM dir=capture/read_PRN set=met n=1338 heard_result=1338 operand=222 other_operation=89/1267
GAP_WRITES dir=capture/read_PRN set=met written=1570 distinct=67 top10=1142 commonest=8:452:41
GAP_LENGTH dir=capture/read_PRN set=met 1=100/383 2=93/878 3=37/264 4=2/44 5+=0/3
GAPS dir=capture/read_PRN set=never n=876 right=21 wrong=855 unfinished=1 not_number=0 unread=0 numbers=854
GAP_SIZE dir=capture/read_PRN set=never n=854 x2=292 x10=742 tenth=28 opposite_sign=0 smaller=547 larger=307 digits=417 foil_digits=262/850
GAP_RINGS dir=capture/read_PRN set=never n=814 mod9=93 foil9=82/809 mod10=310 foil10=215/809 mod11=44 foil11=65/809 mod7=93 foil7=139/809 mod13=45 foil13=60/809
GAP_FROM dir=capture/read_PRN set=never n=854 heard_result=828 operand=66 other_operation=9/590
GAP_WRITES dir=capture/read_PRN set=never written=875 distinct=110 top10=491 commonest=8:160:5
GAP_LENGTH dir=capture/read_PRN set=never 1=10/102 2=3/374 3=8/244 4=0/95 5+=0/61
RUN_RECEIPT exit=0 wall_s=15.4 peak_rss_kib=61200 user_s=15.4
```

## The level read of `PRC` and `PRN`

Each pair ran the training and held cells together; each probe ran
`python3 -I tools/gsm8k/numeral_rings.py probe KIND train_all.txt OUT_TRAIN dev.txt OUT_HELD 2 64 2000`
under a 300 s deadline. The lines for `PRT` are in [TURNS_RUN.md](TURNS_RUN.md).
```text
at_PRC_train_numerals UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=ce1d2ad7ecdb7cef7dbdca70fae4fd50d7c171cf8fdd39e7a9059afa337a91ef elapsed_ms=6739
at_PRC_train_numerals RUN_RECEIPT exit=0 wall_s=6.8 peak_rss_kib=79664 user_s=52.7
at_PRC_held_numerals UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=52ac169c6edf38fde8dd0be401aa7e6457a550d298ce22f57ffb74113aaab929 elapsed_ms=2753
at_PRC_held_numerals RUN_RECEIPT exit=0 wall_s=2.8 peak_rss_kib=40676 user_s=21.0
at_PRC_train_equals UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=aa66b1338659351ad18ebdadd9c52412bded6bd53a4c0e61debbf1ef22b7f776 elapsed_ms=8086
at_PRC_train_equals RUN_RECEIPT exit=0 wall_s=8.1 peak_rss_kib=39380 user_s=63.8
at_PRC_held_equals UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=2410b3d223244bd525c8edfb44e6210d4061b8cb10128aa3ebec4359e598fb2a elapsed_ms=3519
at_PRC_held_equals RUN_RECEIPT exit=0 wall_s=3.5 peak_rss_kib=37172 user_s=27.3
at_PRN_train_numerals UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=540bf70e60bdeee833c18cf74a0074c28fc361a000cabce7573f46b7e7dc7366 elapsed_ms=6693
at_PRN_train_numerals RUN_RECEIPT exit=0 wall_s=6.7 peak_rss_kib=80428 user_s=52.2
at_PRN_held_numerals UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=640e3d5ea93921291968ed50f5a7eb59dae13175af37ae017c279e17d0c70695 elapsed_ms=2702
at_PRN_held_numerals RUN_RECEIPT exit=0 wall_s=2.7 peak_rss_kib=41128 user_s=20.6
at_PRN_train_equals UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=2b987234d9455ae3545ebbccb18467ea68bac535b2b969b307ffbc048579d125 elapsed_ms=8296
at_PRN_train_equals RUN_RECEIPT exit=0 wall_s=8.3 peak_rss_kib=39664 user_s=65.4
at_PRN_held_equals UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=ab4da1b89e9d08f400352656008af890bf8b9beb56955e037596df4a19baf88d elapsed_ms=3151
at_PRN_held_equals RUN_RECEIPT exit=0 wall_s=3.2 peak_rss_kib=39272 user_s=24.5

=== probe PRC numerals
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=882 energy=627 majority=637 suffix=1530 foil=425
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=2519 energy=1139 majority=3079 suffix=3800 foil=1853
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=985 energy=518 majority=599 suffix=1518 foil=344
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=952 energy=790 majority=827 suffix=1574 foil=538
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=835 energy=477 majority=562 suffix=1491 foil=301
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=1338 energy=189 majority=1772 suffix=3800 foil=558
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=598 energy=514 majority=637 suffix=1530 foil=415
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=1589 energy=1636 majority=3079 suffix=3800 foil=1369
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=583 energy=395 majority=599 suffix=1518 foil=324
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=766 energy=714 majority=827 suffix=1574 foil=573
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=510 energy=422 majority=562 suffix=1491 foil=287
NUMERAL_RINGS cells=capture/at_PRC_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=158 energy=59 majority=1772 suffix=3800 foil=51
RUN_RECEIPT exit=0 wall_s=13.9 peak_rss_kib=323664 user_s=13.7

=== probe PRC equals
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=148 energy=111 majority=143 suffix=620 foil=96
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=343 energy=252 majority=426 suffix=837 foil=172
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=110 energy=89 majority=70 suffix=625 foil=77
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=132 energy=122 majority=138 suffix=628 foil=120
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=99 energy=66 majority=75 suffix=614 foil=63
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=107 energy=26 majority=134 suffix=837 foil=22
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=283 energy=185 majority=134 suffix=676 foil=86
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=571 energy=199 majority=306 suffix=839 foil=136
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=362 energy=164 majority=99 suffix=677 foil=90
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=368 energy=195 majority=141 suffix=673 foil=118
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=341 energy=159 majority=103 suffix=681 foil=72
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=366 energy=76 majority=85 suffix=839 foil=20
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=147 energy=155 majority=92 suffix=615 foil=97
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=330 energy=216 majority=304 suffix=840 foil=139
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=140 energy=110 majority=80 suffix=612 foil=79
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=167 energy=165 majority=133 suffix=627 foil=124
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=111 energy=82 majority=68 suffix=609 foil=58
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=135 energy=42 majority=88 suffix=840 foil=18
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=125 energy=89 majority=143 suffix=620 foil=86
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=308 energy=153 majority=426 suffix=837 foil=195
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=112 energy=57 majority=70 suffix=625 foil=56
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=138 energy=131 majority=138 suffix=628 foil=97
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=96 energy=55 majority=75 suffix=614 foil=59
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=107 energy=19 majority=134 suffix=837 foil=18
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=220 energy=144 majority=134 suffix=676 foil=92
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=473 energy=192 majority=306 suffix=839 foil=158
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=220 energy=109 majority=99 suffix=677 foil=83
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=255 energy=159 majority=141 suffix=673 foil=117
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=222 energy=69 majority=103 suffix=681 foil=61
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=286 energy=46 majority=85 suffix=839 foil=28
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=156 energy=119 majority=92 suffix=615 foil=97
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=367 energy=125 majority=304 suffix=840 foil=140
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=121 energy=71 majority=80 suffix=612 foil=56
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=166 energy=114 majority=133 suffix=627 foil=124
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=100 energy=76 majority=68 suffix=609 foil=66
NUMERAL_RINGS cells=capture/at_PRC_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=152 energy=22 majority=88 suffix=840 foil=16
RUN_RECEIPT exit=0 wall_s=8.1 peak_rss_kib=79840 user_s=8.0

=== probe PRN numerals
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=887 energy=677 majority=637 suffix=1530 foil=414
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=2588 energy=1744 majority=3079 suffix=3800 foil=1866
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=911 energy=563 majority=599 suffix=1518 foil=341
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=1044 energy=771 majority=827 suffix=1574 foil=559
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=783 energy=479 majority=562 suffix=1491 foil=294
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=1041 energy=640 majority=1772 suffix=3800 foil=422
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=754 energy=494 majority=637 suffix=1530 foil=402
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=2089 energy=824 majority=3079 suffix=3800 foil=1676
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=783 energy=285 majority=599 suffix=1518 foil=302
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=944 energy=518 majority=827 suffix=1574 foil=557
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=753 energy=336 majority=562 suffix=1491 foil=301
NUMERAL_RINGS cells=capture/at_PRN_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=689 energy=143 majority=1772 suffix=3800 foil=240
RUN_RECEIPT exit=0 wall_s=13.8 peak_rss_kib=322428 user_s=13.7

=== probe PRN equals
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=122 energy=123 majority=143 suffix=620 foil=100
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=336 energy=219 majority=426 suffix=837 foil=183
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=112 energy=88 majority=70 suffix=625 foil=87
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=133 energy=143 majority=138 suffix=628 foil=125
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=109 energy=89 majority=75 suffix=614 foil=63
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=77 energy=55 majority=134 suffix=837 foil=20
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=289 energy=153 majority=134 suffix=676 foil=86
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=581 energy=215 majority=306 suffix=839 foil=140
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=352 energy=144 majority=99 suffix=677 foil=100
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=369 energy=178 majority=141 suffix=673 foil=111
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=342 energy=135 majority=103 suffix=681 foil=57
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=347 energy=104 majority=85 suffix=839 foil=17
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=167 energy=157 majority=92 suffix=615 foil=110
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=330 energy=215 majority=304 suffix=840 foil=138
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=142 energy=97 majority=80 suffix=612 foil=78
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=151 energy=158 majority=133 suffix=627 foil=132
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=96 energy=91 majority=68 suffix=609 foil=65
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=98 energy=47 majority=88 suffix=840 foil=18
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=141 energy=97 majority=143 suffix=620 foil=103
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=317 energy=238 majority=426 suffix=837 foil=203
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=111 energy=93 majority=70 suffix=625 foil=83
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=168 energy=129 majority=138 suffix=628 foil=109
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=85 energy=47 majority=75 suffix=614 foil=54
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=116 energy=20 majority=134 suffix=837 foil=24
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=218 energy=101 majority=134 suffix=676 foil=109
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=432 energy=200 majority=306 suffix=839 foil=151
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=231 energy=75 majority=99 suffix=677 foil=71
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=240 energy=103 majority=141 suffix=673 foil=120
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=179 energy=64 majority=103 suffix=681 foil=52
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=292 energy=37 majority=85 suffix=839 foil=24
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=148 energy=92 majority=92 suffix=615 foil=94
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=261 energy=110 majority=304 suffix=840 foil=139
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=101 energy=73 majority=80 suffix=612 foil=65
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=136 energy=114 majority=133 suffix=627 foil=119
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=90 energy=77 majority=68 suffix=609 foil=55
NUMERAL_RINGS cells=capture/at_PRN_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=91 energy=12 majority=88 suffix=840 foil=14
RUN_RECEIPT exit=0 wall_s=7.9 peak_rss_kib=79036 user_s=7.9
```

## Time and memory

The wall is the `wait4` receipt's; the ratio is wall over projection.

| run | projection | deadline | wall | ratio | peak RSS KiB |
|---|---|---|---|---|---|
| build | 124 s | 180 s | 118.5 s | 0.956 | 3539380 |
| found PRC | unmeasured, planned 1-3 min | 180 s | 0.2 s | - | 45212 |
| found PRN | unmeasured, planned 1-3 min | 180 s | 0.2 s | - | 46072 |
| dev PRC (three-way) | unmeasured (turns/ took 23.8-24.6 s) | 180 s | 23.8 s | 0.967 vs 24.6 | 273328 |
| dev PRN (three-way) | same | 180 s | 23.2 s | 0.943 vs 24.6 | 269944 |
| dev PRT (three-way) | same | 180 s | 23.0 s | 0.935 vs 24.6 | 264436 |
| train PRC | 697.17 s | 698 s | 409.7 s | 0.588 | 292788 |
| train PRN | 636.79 s | 637 s | 409.1 s | 0.642 | 296372 |
| read PRC | progress 64 by 3.3 s (met at 1.705 s) | 30 s | 17.2 s | - | 43252 |
| read PRN | progress 64 by 3.3 s (met at 1.754 s) | 30 s | 17.3 s | - | 41920 |
| rules rings / heard / pair PRC PRT / pair PRC PRN / pair PRN PRT / gaps | - | 60 s each | 14.7 / 6.3 / 4.3 / 4.3 / 4.3 / 15.4 s | - | 62320 / 61944 / 61452 / 61728 / 60712 / 61200 |
| at PRC train/held numerals | 8.4 s | 30 s | 6.8 / 2.8 s | 0.810 / 0.333 | 79664 / 40676 |
| at PRC train/held equals | 8.4 s | 30 s | 8.1 / 3.5 s | 0.964 / 0.417 | 39380 / 37172 |
| at PRN train/held numerals | 8.4 s | 30 s | 6.7 / 2.7 s | 0.798 / 0.321 | 80428 / 41128 |
| at PRN train/held equals | 8.4 s | 30 s | 8.3 / 3.2 s | 0.988 / 0.381 | 39664 / 39272 |
| probe PRC numerals / equals | - | 300 s | 13.9 / 8.1 s | - | 323664 / 79840 |
| probe PRN numerals / equals | - | 300 s | 13.8 / 7.9 s | - | 322428 / 79036 |
