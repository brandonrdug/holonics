# The first loop and the rotor loop on Brandon's PC

The lines below are the runs' own output, whole, from the PC's run directory; the run paths are
relative to it. Each heavy run ran under the `wait4` wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8`
and its own memory scope (`MemoryMax=8G`, `MemorySwapMax=0`). The per-process load lines are left
out: at each launch other programs on the host held between half a core and a core and a half, and
the load average stood at 12 at the first written read because the two eight-thread trainings had
just ended. The releases, marks and cells hold held-out problem text and stay outside the
repository.

## The first loop: `C`'s rings and level read, `P` and `PP` stopped (§4)

Built at `4da1cb262`. `P` and `PP` ran their development passes and trainings side by side; both
trainings were stopped by the window guard and neither was relaunched. `C`'s level read and probes
follow.

```text
binary sha256 9bb066ec816810092292df33fdef524dd6546d4c8480f8c408a33729a34aef0c
git log -1: 4da1cb262a255492ee5f2d257df2b264ae512d21 brandonrdug@users.noreply.github.com
RUN_RECEIPT exit=0 wall_s=117.8 peak_rss_kib=3207992 user_s=193.6
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
RINGS dir=digit/read_C n=312 mod9=44 foil9=39 mod10=109 foil10=76 mod11=30 foil11=26 mod990=6 foil990=1
WRITTEN dir=digit/read_F problems=747 a_on_problem=38 b_free_calculations=1227 b_free_right=61 c_first_calculations=618 c_from_question=49 b_equals=156/2448 met=131/1572 never_met=25/876 binary +=14/470 -=14/388 *=91/897 /=20/343
RINGS dir=digit/read_F n=312 mod9=38 foil9=35 mod10=123 foil10=81 mod11=27 foil11=28 mod990=5 foil990=4
TOWER_TRAIN material=302502 streams=8 section=128 sections_a_pass=155
windows 2639 2713 2720 2712 ms, then 2279 ms over 27 sections
TOWER_PASS pass=0 train_bits_a_byte=2.888 dev_bits_a_byte=2.479 dev_regions Q=1.948 P=3.045 N=1.812 M=2.485 deposits=155/155 pass_ms=16804 elapsed_ms=16807 train_code=1262379333908 dev_code=1033725258943 grain_bits=20
TOWER_DONE state_bytes=10835718 state_sha256=3ddfc9635ef549ea69385de7ac2704d024bb537f8308d0fe04e8e5c6fcd77563 elapsed_ms=16866
RUN_RECEIPT exit=0 wall_s=17.0 peak_rss_kib=209312 user_s=105.7
TOWER_TRAIN material=335782 streams=8 section=128 sections_a_pass=155
windows 3536 3061 3082 3083 ms, then 2689 ms over 27 sections
TOWER_PASS pass=0 train_bits_a_byte=2.866 dev_bits_a_byte=2.495 dev_regions Q=1.833 P=2.885 N=1.579 M=2.504 deposits=155/155 pass_ms=19232 elapsed_ms=19237 train_code=1252809661339 dev_code=1040197822804 grain_bits=20
TOWER_DONE state_bytes=12640147 state_sha256=2e4c8e758d67674af9c8071a3912d2189f679967b8b07d0b0b511a0ef22acbcb elapsed_ms=19295
RUN_RECEIPT exit=0 wall_s=19.4 peak_rss_kib=259764 user_s=120.8
P: w=85.0 ms a section, h=3744 ms. Projection 3*(1311*1.12*85.0 + 3744) + 1000 = 386.65 s. Deadline 387 s. Window bound 3046.4 ms.
PP: w=110.5 ms a section (from its first window, 3536 ms), h=3786 ms. Projection 3*(1311*1.12*110.5 + 3786) + 1000 = 499.11 s. Deadline 500 s. Window bound 3960.32 ms.
TOWER_TRAIN material=302502 streams=8 section=128 sections_a_pass=1311 train_bytes=3528168 dev_bytes=397669
P: TOWER_SECTION pass=0 section=1184 bits_a_byte=1.912 deposits=1184 halvings=8 elapsed_ms=105308 | window sections=32 ms=3157 bound=3046.4 OVER
P: GUARD_STOP pid=3636866 window pass=0 section=1184 sections=32 ms=3157 bound=3046.4
RUN_RECEIPT exit=-15 wall_s=106.1 peak_rss_kib=232908 user_s=638.2
TOWER_TRAIN material=335782 streams=8 section=128 sections_a_pass=1311 train_bytes=3528168 dev_bytes=397669
TOWER_STATE STATE.0 state_bytes=12512888 state_sha256=db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b
TOWER_PASS pass=0 train_bits_a_byte=2.160 dev_bits_a_byte=1.931 dev_regions Q=1.370 P=2.447 N=0.624 M=1.940 deposits=1311/1311 pass_ms=129628 elapsed_ms=129631 train_code=7989204032235 dev_code=805156744401 grain_bits=20
PP: TOWER_SECTION pass=1 section=1120 bits_a_byte=2.067 deposits=1120 halvings=74 elapsed_ms=222374 | window sections=32 ms=4095 bound=3960.3 OVER
PP: GUARD_STOP pid=3636867 window pass=1 section=1120 sections=32 ms=4095 bound=3960.3
RUN_RECEIPT exit=-15 wall_s=223.1 peak_rss_kib=293676 user_s=1377.6
PLACES kind=numerals text=train_all.txt places=10792 out=pumped/places_train_numerals
PLACES kind=numerals text=dev.txt places=3810 out=pumped/places_held_numerals
PLACES kind=equals text=train_all.txt places=2200 out=pumped/places_train_equals
PLACES kind=equals text=dev.txt places=841 out=pumped/places_held_equals
UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=9587862d82d5964460691d72f8e76726ae7dd4dabe2c69d4caf36784cba48233 elapsed_ms=4973
RUN_RECEIPT exit=0 wall_s=5.0 peak_rss_kib=77952 user_s=38.8
UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=cf3f55157a24bd764c6b6216d248c7414b04b6834369d8ad0b093c4705aea397 elapsed_ms=1958
RUN_RECEIPT exit=0 wall_s=2.0 peak_rss_kib=38936 user_s=14.9
UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=da699af4553f7b6ca994406f937ac2b9621ff405c71d587f2ec1dc3b158fb0a5 elapsed_ms=6137
RUN_RECEIPT exit=0 wall_s=6.2 peak_rss_kib=37044 user_s=48.1
UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=2da5002a362881f8d384b597cdfd8814a96a1f0a27a5f3a90b1b061ee55845d0 elapsed_ms=2348
RUN_RECEIPT exit=0 wall_s=2.4 peak_rss_kib=34456 user_s=18.1
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=1017 energy=621 majority=637 suffix=1530 foil=418
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=2964 energy=1841 majority=3079 suffix=3800 foil=2206
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=991 energy=583 majority=599 suffix=1518 foil=362
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=1064 energy=784 majority=827 suffix=1574 foil=570
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=942 energy=572 majority=562 suffix=1491 foil=312
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=1744 energy=759 majority=1772 suffix=3800 foil=642
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=714 energy=566 majority=637 suffix=1530 foil=502
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=2159 energy=1812 majority=3079 suffix=3800 foil=1725
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=720 energy=554 majority=599 suffix=1518 foil=422
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=895 energy=757 majority=827 suffix=1574 foil=589
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=628 energy=453 majority=562 suffix=1491 foil=334
NUMERAL_RINGS cells=pumped/at_C_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=851 energy=177 majority=1772 suffix=3800 foil=378
RUN_RECEIPT exit=0 wall_s=14.6 peak_rss_kib=325296 user_s=14.4
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=145 energy=111 majority=143 suffix=620 foil=97
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=363 energy=309 majority=426 suffix=837 foil=189
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=123 energy=98 majority=70 suffix=625 foil=83
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=159 energy=158 majority=138 suffix=628 foil=113
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=116 energy=76 majority=75 suffix=614 foil=60
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=167 energy=116 majority=134 suffix=837 foil=33
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=247 energy=133 majority=134 suffix=676 foil=91
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=578 energy=387 majority=306 suffix=839 foil=160
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=287 energy=136 majority=99 suffix=677 foil=92
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=317 energy=167 majority=141 suffix=673 foil=122
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=294 energy=117 majority=103 suffix=681 foil=54
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=442 energy=249 majority=85 suffix=839 foil=29
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=147 energy=148 majority=92 suffix=615 foil=83
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=332 energy=274 majority=304 suffix=840 foil=139
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=133 energy=85 majority=80 suffix=612 foil=68
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=153 energy=158 majority=133 suffix=627 foil=117
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=126 energy=86 majority=68 suffix=609 foil=53
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=156 energy=104 majority=88 suffix=840 foil=28
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=128 energy=70 majority=143 suffix=620 foil=95
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=393 energy=328 majority=426 suffix=837 foil=211
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=117 energy=90 majority=70 suffix=625 foil=79
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=152 energy=113 majority=138 suffix=628 foil=113
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=101 energy=83 majority=75 suffix=614 foil=72
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=199 energy=122 majority=134 suffix=837 foil=45
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=242 energy=160 majority=134 suffix=676 foil=89
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=498 energy=297 majority=306 suffix=839 foil=154
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=261 energy=137 majority=99 suffix=677 foil=87
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=293 energy=132 majority=141 suffix=673 foil=117
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=242 energy=115 majority=103 suffix=681 foil=62
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=403 energy=136 majority=85 suffix=839 foil=34
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=133 energy=87 majority=92 suffix=615 foil=91
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=311 energy=250 majority=304 suffix=840 foil=160
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=102 energy=78 majority=80 suffix=612 foil=64
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=155 energy=115 majority=133 suffix=627 foil=127
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=106 energy=79 majority=68 suffix=609 foil=74
NUMERAL_RINGS cells=pumped/at_C_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=148 energy=90 majority=88 suffix=840 foil=28
RUN_RECEIPT exit=0 wall_s=8.4 peak_rss_kib=79848 user_s=8.3
```

| run | projection | deadline | wall | ratio | peak resident |
|---|---|---|---|---|---|
| build | 126 s | 180 s | 117.8 s | 0.93 | 3,207,992 KiB |
| development `P` | unmeasured (`C` 14.4 s) | 180 s | 17.0 s | | 209,312 KiB |
| development `PP` | unmeasured (`C` 14.4 s) | 180 s | 19.4 s | | 259,764 KiB |
| train `P` | 386.65 s | 387 s | 106.1 s, guard stop | incomplete | 232,908 KiB |
| train `PP` | 499.11 s | 500 s | 223.1 s, guard stop | incomplete | 293,676 KiB |
| `C` at, training numerals | unmeasured | 180 s | 5.0 s | | 77,952 KiB |
| `C` at, held numerals | unmeasured | 180 s | 2.0 s | | 38,936 KiB |
| `C` at, training equals | unmeasured | 180 s | 6.2 s | | 37,044 KiB |
| `C` at, held equals | unmeasured | 180 s | 2.4 s | | 34,456 KiB |
| probe `C` numerals | | 300 s | 14.6 s | | 325,296 KiB |
| probe `C` equals | | 300 s | 8.4 s | | 79,848 KiB |

`P`'s 37 full training windows ran 2,764 to 3,157 ms (mean 88.94 ms a section against `w` = 85.0);
`PP`'s pass 0 ran 40 windows of 2,550 to 3,609 ms (mean 96.55) and its pass 1 35 windows of 2,488 to
4,095 ms (mean 82.81), the stopping window a lone spike among windows of 2.5 to 2.7 s.

## The rotor loop: build, inputs, rotor, development, the changed read, training, reads, rules (§5)

Built at `ecc7daa8a`, in its own worktree and target directory.

```text
=== 1. BUILD (worktree .local/wt/rotor at ecc7daa8a, its own target dir)
LOAD build 2026-10-26T19:33:15Z loadavg=0.89 1.43 1.84
PROJECTION 124 s (last three builds 117.8, 122.9, 123.1 s); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
    Finished `release` profile [optimized] target(s) in 1m 57s
RUN_RECEIPT exit=0 wall_s=117.5 peak_rss_kib=3590068 user_s=194.6
BINARY_SHA256 e5f352c6ff75a65e6a7ec819573d390f9bb9e4be77f021c48b30f6fee7c01b30 RUN/rotor/solenoidal_alpha
GIT_LOG ecc7daa8a165b5f0a224c95bd3c35b9baf4758ba brandonrdug@users.noreply.github.com
=== 2. INPUTS
SHA ok UNITS d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a
SHA ok digit/keys_tower.bin fcaadc56deeb837ce9e46f2c0d52269022c576bae30facaacea74756a71e9593
SHA ok train_all.txt 050b94f367625ad2c533bb3af53c730ea6d12e140a080a6a3def9ffdc0de3b95
SHA ok dev.txt e5bffe0ea3949a2e8efec1c43120918891867c342a9e9ffd288cc798a8363153
SHA ok digit/dev.roles a7d7ccdccd95b5450cdb6b211ee5a146afea1d76011937041d8517644720c9c1
SHA ok digit/train800.txt 173c9ac34dcc4d097ea199ddbbf5eaab4f6726951abdb7ddd4d2860869f1f0d0
SHA ok written/keys.bin bbe735d7d7c4b48727ec948b622e4a9a8ba267f32dd33928838b15c5ebbac243
SHA ok digit/C/STATE 84e2bacfc6ea56c49181e4048f21ac32ad502ce67a94a001cd1d2ad9dd1678b4
SHA ok pumped/PP/STATE.0 db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b
SHA places pumped/places_held_equals 6eabb8e6d058583612152142fdfa80fc38f03029ded949821775990bb0d023f9
SHA places pumped/places_held_numerals 81870715e53f9a08dbd2dd8be64823a502713d7761cec8feff37d20c0c3f9b2b
SHA places pumped/places_train_equals a395a9dcf41d6ee0230fd0d71cfe3b6f741fbd239ec2a2aaf45d80409727bb29
SHA places pumped/places_train_numerals 95b456101f08c31c19ddb0141a9e499e03f9335b73a539bc7fc9a4c7aa6dc48f
=== 3. ROTOR
LOAD found 2026-10-26T19:35:51Z loadavg=2.20 1.92 1.97
PROJECTION unmeasured (planned at 1 to 3 minutes); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
ROTOR_MENU loops=7204 bytes=10 columns=40
ROTOR_CLOSURE step=0 rows=4776 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=36
ROTOR_CLOSURE step=1 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=56
ROTOR_CLOSURE step=2 rows=5210 rank=40 minor_bits=17 torsion=3:2,11:2 carried=33 elapsed_ms=73
ROTOR_CLOSURE step=3 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=92
ROTOR_FOUNDED step=1 carried=3333 units=1318 stepping_units=120 rings=16 levels_stepped=1 bytes=2827894 sha256=5d5a91384629a810bfcf58106902e7e4895a169ac4e01caa4c583b47387f78e8 elapsed_ms=139
RUN_RECEIPT exit=0 wall_s=0.2 peak_rss_kib=40652 user_s=0.1
ROTOR_STATE_SHA256 5d5a91384629a810bfcf58106902e7e4895a169ac4e01caa4c583b47387f78e8
=== 4. DEVELOPMENT PASSES (side by side)
LOAD dev 2026-10-26T19:36:27Z loadavg=1.56 1.80 1.93
-- dev_PP
PROJECTION unmeasured here (pumped/'s PP development pass took 19.4 s); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_SECTION pass=0 section=32 bits_a_byte=3.608 deposits=32 halvings=18 elapsed_ms=3497
TOWER_SECTION pass=0 section=64 bits_a_byte=2.995 deposits=64 halvings=18 elapsed_ms=6640
TOWER_SECTION pass=0 section=96 bits_a_byte=2.640 deposits=96 halvings=18 elapsed_ms=9791
TOWER_SECTION pass=0 section=128 bits_a_byte=2.553 deposits=128 halvings=18 elapsed_ms=12950
TOWER_SECTION pass=0 section=155 bits_a_byte=2.477 deposits=155 halvings=18 elapsed_ms=15586
TOWER_STATE STATE.0 state_bytes=12640147 state_sha256=2e4c8e758d67674af9c8071a3912d2189f679967b8b07d0b0b511a0ef22acbcb
TOWER_PASS pass=0 train_bits_a_byte=2.866 dev_bits_a_byte=2.495 dev_regions Q=1.833 P=2.885 N=1.579 M=2.504 deposits=155/155 pass_ms=20087 elapsed_ms=20090 train_code=1252809661339 dev_code=1040197822804 grain_bits=20
TOWER_DONE state_bytes=12640147 state_sha256=2e4c8e758d67674af9c8071a3912d2189f679967b8b07d0b0b511a0ef22acbcb elapsed_ms=20148
RUN_RECEIPT exit=0 wall_s=20.2 peak_rss_kib=261048 user_s=125.6
-- dev_PR
PROJECTION unmeasured here (pumped/'s PP development pass took 19.4 s); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_SECTION pass=0 section=32 bits_a_byte=3.612 deposits=32 halvings=13 elapsed_ms=3393
TOWER_SECTION pass=0 section=64 bits_a_byte=2.984 deposits=64 halvings=13 elapsed_ms=6539
TOWER_SECTION pass=0 section=96 bits_a_byte=2.648 deposits=96 halvings=13 elapsed_ms=9704
TOWER_SECTION pass=0 section=128 bits_a_byte=2.568 deposits=128 halvings=13 elapsed_ms=12837
TOWER_SECTION pass=0 section=155 bits_a_byte=2.494 deposits=155 halvings=13 elapsed_ms=15501
TOWER_STATE STATE.0 state_bytes=12662664 state_sha256=df9e921759d940b83446b7126213bf844685e9391403a3fbd4b0e6ce8734b260
TOWER_PASS pass=0 train_bits_a_byte=2.872 dev_bits_a_byte=2.506 dev_regions Q=1.867 P=2.894 N=1.721 M=2.515 deposits=155/155 pass_ms=20047 elapsed_ms=20065 train_code=1255440915480 dev_code=1045061546126 grain_bits=20
TOWER_DONE state_bytes=12662664 state_sha256=df9e921759d940b83446b7126213bf844685e9391403a3fbd4b0e6ce8734b260 elapsed_ms=20125
RUN_RECEIPT exit=0 wall_s=20.2 peak_rss_kib=263752 user_s=123.9
=== 5. THE CHANGED READ: w, eta, h, d
NUMBER w_PP=108.8125 ms_an_evaluation from pumped/PP.log pass=0 section=1056 ms=3482 evaluations=32 (over every full window of rotor/dev_PP.log, pumped/dev_PP.log, pumped/PP.log)
NUMBER d_PP=98.7188 from rotor/dev_PP.log pass=0 section=128 ms=3159 evaluations=32
NUMBER d_PR=98.9062 from rotor/dev_PR.log pass=0 section=96 ms=3165 evaluations=32
NUMBER w_PR = w_PP x max(1, d_PR/d_PP) = 108.8125 x max(1, 1.001899) = 109.0192 ms_an_evaluation
NUMBER eta_PP=0.116129 from rotor/dev_PP.log pass=0 halvings=18 sections=155
NUMBER eta_PR=max(eta_PP, own 0.083871 from rotor/dev_PR.log pass=0 halvings=13 sections=155)=0.116129
NUMBER h_PP=4504 ms from rotor/dev_PP.log pass=0
NUMBER h_PR=4564 ms from rotor/dev_PR.log pass=0
PROJECTION_PP 3 x (1311 x 1.12 x 108.8125 x (1 + 0.116129) + 4504) + 1000 ms = 549.49 s; DEADLINE 550 s; bound 1.12 x 108.8125 = 121.8700 ms an evaluation
PROJECTION_PR 3 x (1311 x 1.12 x 109.0192 x (1 + 0.116129) + 4564) + 1000 ms = 550.69 s; DEADLINE 551 s; bound 1.12 x 109.0192 = 122.1015 ms an evaluation
=== 6. TRAINING (side by side, three passes)
LOAD train 2026-10-26T19:37:17Z loadavg=3.59 2.42 2.14
-- PP
PROJECTION_PP 3 x (1311 x 1.12 x 108.8125 x (1 + 0.116129) + 4504) + 1000 ms = 549.49 s; DEADLINE 550 s; bound 1.12 x 108.8125 = 121.8700 ms an evaluation; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_STATE STATE.0 state_bytes=12512888 state_sha256=db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b
TOWER_PASS pass=0 train_bits_a_byte=2.160 dev_bits_a_byte=1.931 dev_regions Q=1.370 P=2.447 N=0.624 M=1.940 deposits=1311/1311 pass_ms=134032 elapsed_ms=134046 train_code=7989204032235 dev_code=805156744401 grain_bits=20
TOWER_STATE STATE.1 state_bytes=12640645 state_sha256=d0526136de37e1cc4881b658f6c4dbdad1ea24950ae86e7947efb45a7621a806
TOWER_PASS pass=1 train_bits_a_byte=1.850 dev_bits_a_byte=1.823 dev_regions Q=1.332 P=2.457 N=0.478 M=1.830 deposits=1311/1311 pass_ms=138964 elapsed_ms=273011 train_code=6841388160634 dev_code=759994637224 grain_bits=20
TOWER_STATE STATE.2 state_bytes=12620809 state_sha256=290d41275849d794656e5df56f04020853010678820b10cc774c416d47ae3cef
TOWER_PASS pass=2 train_bits_a_byte=1.758 dev_bits_a_byte=1.880 dev_regions Q=1.496 P=2.485 N=0.720 M=1.885 deposits=1311/1311 pass_ms=137254 elapsed_ms=410266 train_code=6501375747301 dev_code=783871432605 grain_bits=20
TOWER_DONE state_bytes=12620809 state_sha256=290d41275849d794656e5df56f04020853010678820b10cc774c416d47ae3cef elapsed_ms=410329
RUN_RECEIPT exit=0 wall_s=410.7 peak_rss_kib=293148 user_s=2488.4
-- PR
PROJECTION_PR 3 x (1311 x 1.12 x 109.0192 x (1 + 0.116129) + 4564) + 1000 ms = 550.69 s; DEADLINE 551 s; bound 1.12 x 109.0192 = 122.1015 ms an evaluation; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_STATE STATE.0 state_bytes=12629596 state_sha256=375bd4bde38ea4623cc724bd2789c2ad6f46d85837bae1885d0c005c1b1bdada
TOWER_PASS pass=0 train_bits_a_byte=2.199 dev_bits_a_byte=1.970 dev_regions Q=1.420 P=2.588 N=0.710 M=1.978 deposits=1311/1311 pass_ms=134863 elapsed_ms=134881 train_code=8133511771444 dev_code=821581221755 grain_bits=20
TOWER_STATE STATE.1 state_bytes=12560464 state_sha256=10bdf03bcce35e98a738121eb80c2870e0018195381086ba1aeabcbffb804d28
TOWER_PASS pass=1 train_bits_a_byte=1.861 dev_bits_a_byte=1.843 dev_regions Q=1.264 P=2.393 N=0.564 M=1.852 deposits=1311/1311 pass_ms=136519 elapsed_ms=271401 train_code=6882748134887 dev_code=768509837826 grain_bits=20
TOWER_STATE STATE.2 state_bytes=12553041 state_sha256=f8f0585c786e6f699e05c68cfd7f1102f204a3a2fbcfdb338cad048492a67157
TOWER_PASS pass=2 train_bits_a_byte=1.762 dev_bits_a_byte=1.779 dev_regions Q=1.201 P=2.459 N=0.423 M=1.786 deposits=1311/1311 pass_ms=136236 elapsed_ms=407638 train_code=6518894018981 dev_code=741609540558 grain_bits=20
TOWER_DONE state_bytes=12553041 state_sha256=f8f0585c786e6f699e05c68cfd7f1102f204a3a2fbcfdb338cad048492a67157 elapsed_ms=407703
RUN_RECEIPT exit=0 wall_s=408.1 peak_rss_kib=291368 user_s=2468.7
PP_STATE.0 db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b equals db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b: yes (cmp: identical)
READ log=rotor/PP.log
  w=105.6562 ms_an_evaluation (window pass=2 section=992)
  eta pass=0 halvings=18 sections=1311 eta=0.013730
  eta pass=1 halvings=75 sections=1311 eta=0.057208
  eta pass=2 halvings=38 sections=1311 eta=0.028986
  h pass=0 h=4162 ms
  h pass=1 h=4527 ms
  h pass=2 h=4042 ms
READ log=rotor/PR.log
  w=106.0312 ms_an_evaluation (window pass=2 section=992)
  eta pass=0 halvings=12 sections=1311 eta=0.009153
  eta pass=1 halvings=0 sections=1311 eta=0.000000
  eta pass=2 halvings=0 sections=1311 eta=0.000000
  h pass=0 h=4656 ms
  h pass=1 h=4510 ms
  h pass=2 h=4408 ms
=== 7. WRITTEN READS
-- read_PP
LOAD read_PP 2026-10-26T19:44:26Z loadavg=12.19 11.15 6.52
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=61
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299734 prompt_units=468588 released_units=114167 most_units_a_problem=4708 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17365
TOWER_WRITTEN_FILES free_sha256=19b5a7679ac415240992d60e7abe937015ee238dc1ca1d2e4e3e465f36c7cea2 marks_sha256=3af6d5316d43f75cac81eb23a4cc62482d1aa7695fabd61376ca5c9035a825ad
RUN_RECEIPT exit=0 wall_s=17.4 peak_rss_kib=41728 user_s=134.9
READ_GUARD ok progress 64 by 1705 ms
-- read_PR
LOAD read_PR 2026-10-26T19:44:44Z loadavg=11.35 11.03 6.58
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=45
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299738 prompt_units=468588 released_units=114850 most_units_a_problem=4702 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17069
TOWER_WRITTEN_FILES free_sha256=a2f250e3f01dd3c2d1a0d4bce837cd250af6bb4000a8d400d61bd388c77448ae marks_sha256=14459ed322d401d4e8509b4c7a2a9ab51c3383a8027854417061f696fe635710
RUN_RECEIPT exit=0 wall_s=17.1 peak_rss_kib=40424 user_s=134.1
READ_GUARD ok progress 64 by 1605 ms
=== 8. RULES
RULES rings digit/read_C rotor/read_PP rotor/read_PR; DEADLINE 60 s
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
RINGS dir=digit/read_C n=312 mod9=44 foil9=39 mod10=109 foil10=76 mod11=30 foil11=26 mod990=6 foil990=1
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
RINGS dir=rotor/read_PP n=312 mod9=39 foil9=32 mod10=113 foil10=84 mod11=23 foil11=23 mod990=3 foil990=1
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
RINGS dir=rotor/read_PR n=312 mod9=32 foil9=35 mod10=123 foil10=88 mod11=27 foil11=30 mod990=4 foil990=4
RUN_RECEIPT exit=0 wall_s=6.3 peak_rss_kib=60576 user_s=6.2
RULES heard rotor/read_PP rotor/read_PR; DEADLINE 60 s
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
HEARD dir=rotor/read_PP 0=5/876 1=6/239 2-3=11/224 4-7=2/255 8-15=18/326 16+=67/528
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
HEARD dir=rotor/read_PR 0=18/876 1=9/239 2-3=19/224 4-7=13/255 8-15=39/326 16+=179/528
RUN_RECEIPT exit=0 wall_s=4.6 peak_rss_kib=60640 user_s=4.6
RULES pair rotor/read_PR rotor/read_PP; DEADLINE 60 s
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
PAIRED met_only_a=197 met_only_b=42 met_both=62 never_only_a=16 never_only_b=3 never_both=2
RUN_RECEIPT exit=0 wall_s=5.0 peak_rss_kib=62192 user_s=4.8
RULES pair rotor/read_PR digit/read_C; DEADLINE 60 s
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
PAIRED met_only_a=140 met_only_b=57 met_both=119 never_only_a=15 never_only_b=11 never_both=3
RUN_RECEIPT exit=0 wall_s=5.1 peak_rss_kib=61764 user_s=4.9
RULES pair rotor/read_PP digit/read_C; DEADLINE 60 s
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
PAIRED met_only_a=46 met_only_b=118 met_both=58 never_only_a=5 never_only_b=14 never_both=0
RUN_RECEIPT exit=0 wall_s=4.5 peak_rss_kib=60528 user_s=4.5
```

| run | projection | deadline | wall | ratio | peak resident |
|---|---|---|---|---|---|
| build | 124 s | 180 s | 117.5 s | 0.948 | 3,590,068 KiB |
| `found-unit-rotor-tower` | unmeasured, planned 1–3 min | 180 s | 0.2 s | | 40,652 KiB |
| development `PP` | unmeasured (19.4 s before) | 180 s | 20.2 s | | 261,048 KiB |
| development `PR` | unmeasured (19.4 s before) | 180 s | 20.2 s | | 263,752 KiB |
| train `PP` | 549.49 s | 550 s | 410.7 s | 0.747 | 293,148 KiB |
| train `PR` | 550.69 s | 551 s | 408.1 s | 0.741 | 291,368 KiB |
| written read `PP` | 64 problems by 3.3 s (1.705 s) | 30 s | 17.4 s | | 41,728 KiB |
| written read `PR` | 64 problems by 3.3 s (1.605 s) | 30 s | 17.1 s | | 40,424 KiB |
| rules rings, heard, three pairs | | 60 s each | 6.3, 4.6, 5.0, 5.1, 4.5 s | | ≤ 62,192 KiB |
| `PP` at, training/held numerals | `C`'s largest 6.2 s | 30 s | 6.8 / 3.0 s | 1.10 / 0.48 | 79,636 / 39,192 KiB |
| `PP` at, training/held equals | `C`'s largest 6.2 s | 30 s | 8.5 / 3.6 s | 1.37 / 0.58 | 38,892 / 36,472 KiB |
| `PR` at, training/held numerals | `C`'s largest 6.2 s | 30 s | 6.8 / 2.8 s | 1.10 / 0.45 | 78,096 / 38,560 KiB |
| `PR` at, training/held equals | `C`'s largest 6.2 s | 30 s | 8.3 / 3.3 s | 1.34 / 0.53 | 38,416 / 36,960 KiB |
| probe `PP` numerals / equals | | 300 s | 14.1 / 8.2 s | | 325,740 / 80,228 KiB |
| probe `PR` numerals / equals | | 300 s | 13.6 / 8.0 s | | 325,604 / 80,312 KiB |

`halvings=` restarts at zero each pass, so a pass's first window counts its halvings from zero; `d`
is taken over full windows, as `w` is; `η` is the development passes' (18 halvings over 155
sections), which bounds the training passes' 0.014 to 0.066.

## Every guard line of the two trainings

The guard stopped neither run.

```text
PP: TOWER_SECTION pass=0 section=32 bits_a_byte=3.585 deposits=32 halvings=18 elapsed_ms=3516 | window sections=32 halvings=18 evaluations=50 ms=3516 ms_an_evaluation=70.32 limit=6093.5
PR: TOWER_SECTION pass=0 section=32 bits_a_byte=3.719 deposits=32 halvings=12 elapsed_ms=3337 | window sections=32 halvings=12 evaluations=44 ms=3337 ms_an_evaluation=75.84 limit=5372.5
PP: TOWER_SECTION pass=0 section=64 bits_a_byte=2.949 deposits=64 halvings=18 elapsed_ms=6589 | window sections=32 halvings=0 evaluations=32 ms=3073 ms_an_evaluation=96.03 limit=3899.8
PR: TOWER_SECTION pass=0 section=64 bits_a_byte=2.989 deposits=64 halvings=12 elapsed_ms=6432 | window sections=32 halvings=0 evaluations=32 ms=3095 ms_an_evaluation=96.72 limit=3907.2
PR: TOWER_SECTION pass=0 section=96 bits_a_byte=2.763 deposits=96 halvings=12 elapsed_ms=9554 | window sections=32 halvings=0 evaluations=32 ms=3122 ms_an_evaluation=97.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=96 bits_a_byte=2.718 deposits=96 halvings=18 elapsed_ms=9755 | window sections=32 halvings=0 evaluations=32 ms=3166 ms_an_evaluation=98.94 limit=3899.8
PP: TOWER_SECTION pass=0 section=128 bits_a_byte=2.554 deposits=128 halvings=18 elapsed_ms=12873 | window sections=32 halvings=0 evaluations=32 ms=3118 ms_an_evaluation=97.44 limit=3899.8
PR: TOWER_SECTION pass=0 section=128 bits_a_byte=2.599 deposits=128 halvings=12 elapsed_ms=12708 | window sections=32 halvings=0 evaluations=32 ms=3154 ms_an_evaluation=98.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=160 bits_a_byte=2.481 deposits=160 halvings=18 elapsed_ms=15983 | window sections=32 halvings=0 evaluations=32 ms=3110 ms_an_evaluation=97.19 limit=3899.8
PR: TOWER_SECTION pass=0 section=160 bits_a_byte=2.523 deposits=160 halvings=12 elapsed_ms=15829 | window sections=32 halvings=0 evaluations=32 ms=3121 ms_an_evaluation=97.53 limit=3907.2
PP: TOWER_SECTION pass=0 section=192 bits_a_byte=2.379 deposits=192 halvings=18 elapsed_ms=19104 | window sections=32 halvings=0 evaluations=32 ms=3121 ms_an_evaluation=97.53 limit=3899.8
PR: TOWER_SECTION pass=0 section=192 bits_a_byte=2.417 deposits=192 halvings=12 elapsed_ms=18940 | window sections=32 halvings=0 evaluations=32 ms=3111 ms_an_evaluation=97.22 limit=3907.2
PR: TOWER_SECTION pass=0 section=224 bits_a_byte=2.321 deposits=224 halvings=12 elapsed_ms=22072 | window sections=32 halvings=0 evaluations=32 ms=3132 ms_an_evaluation=97.88 limit=3907.2
PP: TOWER_SECTION pass=0 section=224 bits_a_byte=2.288 deposits=224 halvings=18 elapsed_ms=22234 | window sections=32 halvings=0 evaluations=32 ms=3130 ms_an_evaluation=97.81 limit=3899.8
PP: TOWER_SECTION pass=0 section=256 bits_a_byte=2.341 deposits=256 halvings=18 elapsed_ms=25335 | window sections=32 halvings=0 evaluations=32 ms=3101 ms_an_evaluation=96.91 limit=3899.8
PR: TOWER_SECTION pass=0 section=256 bits_a_byte=2.374 deposits=256 halvings=12 elapsed_ms=25175 | window sections=32 halvings=0 evaluations=32 ms=3103 ms_an_evaluation=96.97 limit=3907.2
PP: TOWER_SECTION pass=0 section=288 bits_a_byte=2.274 deposits=288 halvings=18 elapsed_ms=28495 | window sections=32 halvings=0 evaluations=32 ms=3160 ms_an_evaluation=98.75 limit=3899.8
PR: TOWER_SECTION pass=0 section=288 bits_a_byte=2.307 deposits=288 halvings=12 elapsed_ms=28378 | window sections=32 halvings=0 evaluations=32 ms=3203 ms_an_evaluation=100.09 limit=3907.2
PR: TOWER_SECTION pass=0 section=320 bits_a_byte=2.249 deposits=320 halvings=12 elapsed_ms=31545 | window sections=32 halvings=0 evaluations=32 ms=3167 ms_an_evaluation=98.97 limit=3907.2
PP: TOWER_SECTION pass=0 section=320 bits_a_byte=2.209 deposits=320 halvings=18 elapsed_ms=31650 | window sections=32 halvings=0 evaluations=32 ms=3155 ms_an_evaluation=98.59 limit=3899.8
PP: TOWER_SECTION pass=0 section=352 bits_a_byte=2.224 deposits=352 halvings=18 elapsed_ms=34817 | window sections=32 halvings=0 evaluations=32 ms=3167 ms_an_evaluation=98.97 limit=3899.8
PR: TOWER_SECTION pass=0 section=352 bits_a_byte=2.257 deposits=352 halvings=12 elapsed_ms=34709 | window sections=32 halvings=0 evaluations=32 ms=3164 ms_an_evaluation=98.88 limit=3907.2
PP: TOWER_SECTION pass=0 section=384 bits_a_byte=2.217 deposits=384 halvings=18 elapsed_ms=38066 | window sections=32 halvings=0 evaluations=32 ms=3249 ms_an_evaluation=101.53 limit=3899.8
PR: TOWER_SECTION pass=0 section=384 bits_a_byte=2.250 deposits=384 halvings=12 elapsed_ms=37998 | window sections=32 halvings=0 evaluations=32 ms=3289 ms_an_evaluation=102.78 limit=3907.2
PP: TOWER_SECTION pass=0 section=416 bits_a_byte=2.179 deposits=416 halvings=18 elapsed_ms=41177 | window sections=32 halvings=0 evaluations=32 ms=3111 ms_an_evaluation=97.22 limit=3899.8
PR: TOWER_SECTION pass=0 section=416 bits_a_byte=2.206 deposits=416 halvings=12 elapsed_ms=41152 | window sections=32 halvings=0 evaluations=32 ms=3154 ms_an_evaluation=98.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=448 bits_a_byte=2.163 deposits=448 halvings=18 elapsed_ms=44348 | window sections=32 halvings=0 evaluations=32 ms=3171 ms_an_evaluation=99.09 limit=3899.8
PR: TOWER_SECTION pass=0 section=448 bits_a_byte=2.184 deposits=448 halvings=12 elapsed_ms=44315 | window sections=32 halvings=0 evaluations=32 ms=3163 ms_an_evaluation=98.84 limit=3907.2
PP: TOWER_SECTION pass=0 section=480 bits_a_byte=2.139 deposits=480 halvings=18 elapsed_ms=47525 | window sections=32 halvings=0 evaluations=32 ms=3177 ms_an_evaluation=99.28 limit=3899.8
PR: TOWER_SECTION pass=0 section=480 bits_a_byte=2.172 deposits=480 halvings=12 elapsed_ms=47497 | window sections=32 halvings=0 evaluations=32 ms=3182 ms_an_evaluation=99.44 limit=3907.2
PP: TOWER_SECTION pass=0 section=512 bits_a_byte=2.119 deposits=512 halvings=18 elapsed_ms=50707 | window sections=32 halvings=0 evaluations=32 ms=3182 ms_an_evaluation=99.44 limit=3899.8
PR: TOWER_SECTION pass=0 section=512 bits_a_byte=2.147 deposits=512 halvings=12 elapsed_ms=50713 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=3907.2
PP: TOWER_SECTION pass=0 section=544 bits_a_byte=2.071 deposits=544 halvings=18 elapsed_ms=53834 | window sections=32 halvings=0 evaluations=32 ms=3127 ms_an_evaluation=97.72 limit=3899.8
PR: TOWER_SECTION pass=0 section=544 bits_a_byte=2.110 deposits=544 halvings=12 elapsed_ms=53863 | window sections=32 halvings=0 evaluations=32 ms=3150 ms_an_evaluation=98.44 limit=3907.2
PP: TOWER_SECTION pass=0 section=576 bits_a_byte=2.117 deposits=576 halvings=18 elapsed_ms=56998 | window sections=32 halvings=0 evaluations=32 ms=3164 ms_an_evaluation=98.88 limit=3899.8
PR: TOWER_SECTION pass=0 section=576 bits_a_byte=2.180 deposits=576 halvings=12 elapsed_ms=57088 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3907.2
PP: TOWER_SECTION pass=0 section=608 bits_a_byte=2.067 deposits=608 halvings=18 elapsed_ms=60194 | window sections=32 halvings=0 evaluations=32 ms=3196 ms_an_evaluation=99.88 limit=3899.8
PR: TOWER_SECTION pass=0 section=608 bits_a_byte=2.109 deposits=608 halvings=12 elapsed_ms=60258 | window sections=32 halvings=0 evaluations=32 ms=3170 ms_an_evaluation=99.06 limit=3907.2
PP: TOWER_SECTION pass=0 section=640 bits_a_byte=2.047 deposits=640 halvings=18 elapsed_ms=63368 | window sections=32 halvings=0 evaluations=32 ms=3174 ms_an_evaluation=99.19 limit=3899.8
PR: TOWER_SECTION pass=0 section=640 bits_a_byte=2.084 deposits=640 halvings=12 elapsed_ms=63448 | window sections=32 halvings=0 evaluations=32 ms=3190 ms_an_evaluation=99.69 limit=3907.2
PP: TOWER_SECTION pass=0 section=672 bits_a_byte=2.054 deposits=672 halvings=18 elapsed_ms=66548 | window sections=32 halvings=0 evaluations=32 ms=3180 ms_an_evaluation=99.38 limit=3899.8
PR: TOWER_SECTION pass=0 section=672 bits_a_byte=2.097 deposits=672 halvings=12 elapsed_ms=66666 | window sections=32 halvings=0 evaluations=32 ms=3218 ms_an_evaluation=100.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=704 bits_a_byte=2.037 deposits=704 halvings=18 elapsed_ms=69703 | window sections=32 halvings=0 evaluations=32 ms=3155 ms_an_evaluation=98.59 limit=3899.8
PR: TOWER_SECTION pass=0 section=704 bits_a_byte=2.076 deposits=704 halvings=12 elapsed_ms=69872 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=3907.2
PP: TOWER_SECTION pass=0 section=736 bits_a_byte=2.027 deposits=736 halvings=18 elapsed_ms=72875 | window sections=32 halvings=0 evaluations=32 ms=3172 ms_an_evaluation=99.12 limit=3899.8
PR: TOWER_SECTION pass=0 section=736 bits_a_byte=2.063 deposits=736 halvings=12 elapsed_ms=73037 | window sections=32 halvings=0 evaluations=32 ms=3165 ms_an_evaluation=98.91 limit=3907.2
PP: TOWER_SECTION pass=0 section=768 bits_a_byte=2.020 deposits=768 halvings=18 elapsed_ms=76040 | window sections=32 halvings=0 evaluations=32 ms=3165 ms_an_evaluation=98.91 limit=3899.8
PR: TOWER_SECTION pass=0 section=768 bits_a_byte=2.054 deposits=768 halvings=12 elapsed_ms=76238 | window sections=32 halvings=0 evaluations=32 ms=3201 ms_an_evaluation=100.03 limit=3907.2
PP: TOWER_SECTION pass=0 section=800 bits_a_byte=1.986 deposits=800 halvings=18 elapsed_ms=79225 | window sections=32 halvings=0 evaluations=32 ms=3185 ms_an_evaluation=99.53 limit=3899.8
PR: TOWER_SECTION pass=0 section=800 bits_a_byte=2.029 deposits=800 halvings=12 elapsed_ms=79408 | window sections=32 halvings=0 evaluations=32 ms=3170 ms_an_evaluation=99.06 limit=3907.2
PP: TOWER_SECTION pass=0 section=832 bits_a_byte=1.999 deposits=832 halvings=18 elapsed_ms=82422 | window sections=32 halvings=0 evaluations=32 ms=3197 ms_an_evaluation=99.91 limit=3899.8
PR: TOWER_SECTION pass=0 section=832 bits_a_byte=2.029 deposits=832 halvings=12 elapsed_ms=82610 | window sections=32 halvings=0 evaluations=32 ms=3202 ms_an_evaluation=100.06 limit=3907.2
PP: TOWER_SECTION pass=0 section=864 bits_a_byte=2.001 deposits=864 halvings=18 elapsed_ms=85605 | window sections=32 halvings=0 evaluations=32 ms=3183 ms_an_evaluation=99.47 limit=3899.8
PR: TOWER_SECTION pass=0 section=864 bits_a_byte=2.027 deposits=864 halvings=12 elapsed_ms=85800 | window sections=32 halvings=0 evaluations=32 ms=3190 ms_an_evaluation=99.69 limit=3907.2
PP: TOWER_SECTION pass=0 section=896 bits_a_byte=1.986 deposits=896 halvings=18 elapsed_ms=88751 | window sections=32 halvings=0 evaluations=32 ms=3146 ms_an_evaluation=98.31 limit=3899.8
PR: TOWER_SECTION pass=0 section=896 bits_a_byte=2.024 deposits=896 halvings=12 elapsed_ms=88938 | window sections=32 halvings=0 evaluations=32 ms=3138 ms_an_evaluation=98.06 limit=3907.2
PP: TOWER_SECTION pass=0 section=928 bits_a_byte=2.007 deposits=928 halvings=18 elapsed_ms=91918 | window sections=32 halvings=0 evaluations=32 ms=3167 ms_an_evaluation=98.97 limit=3899.8
PR: TOWER_SECTION pass=0 section=928 bits_a_byte=2.049 deposits=928 halvings=12 elapsed_ms=92124 | window sections=32 halvings=0 evaluations=32 ms=3186 ms_an_evaluation=99.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=960 bits_a_byte=1.978 deposits=960 halvings=18 elapsed_ms=95076 | window sections=32 halvings=0 evaluations=32 ms=3158 ms_an_evaluation=98.69 limit=3899.8
PR: TOWER_SECTION pass=0 section=960 bits_a_byte=2.015 deposits=960 halvings=12 elapsed_ms=95264 | window sections=32 halvings=0 evaluations=32 ms=3140 ms_an_evaluation=98.12 limit=3907.2
PP: TOWER_SECTION pass=0 section=992 bits_a_byte=1.982 deposits=992 halvings=18 elapsed_ms=98313 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=3899.8
PR: TOWER_SECTION pass=0 section=992 bits_a_byte=2.013 deposits=992 halvings=12 elapsed_ms=98485 | window sections=32 halvings=0 evaluations=32 ms=3221 ms_an_evaluation=100.66 limit=3907.2
PP: TOWER_SECTION pass=0 section=1024 bits_a_byte=1.933 deposits=1024 halvings=18 elapsed_ms=101478 | window sections=32 halvings=0 evaluations=32 ms=3165 ms_an_evaluation=98.91 limit=3899.8
PR: TOWER_SECTION pass=0 section=1024 bits_a_byte=1.974 deposits=1024 halvings=12 elapsed_ms=101678 | window sections=32 halvings=0 evaluations=32 ms=3193 ms_an_evaluation=99.78 limit=3907.2
PP: TOWER_SECTION pass=0 section=1056 bits_a_byte=1.940 deposits=1056 halvings=18 elapsed_ms=104607 | window sections=32 halvings=0 evaluations=32 ms=3129 ms_an_evaluation=97.78 limit=3899.8
PR: TOWER_SECTION pass=0 section=1056 bits_a_byte=1.972 deposits=1056 halvings=12 elapsed_ms=104845 | window sections=32 halvings=0 evaluations=32 ms=3167 ms_an_evaluation=98.97 limit=3907.2
PP: TOWER_SECTION pass=0 section=1088 bits_a_byte=1.977 deposits=1088 halvings=18 elapsed_ms=107779 | window sections=32 halvings=0 evaluations=32 ms=3172 ms_an_evaluation=99.12 limit=3899.8
PR: TOWER_SECTION pass=0 section=1088 bits_a_byte=2.017 deposits=1088 halvings=12 elapsed_ms=108038 | window sections=32 halvings=0 evaluations=32 ms=3193 ms_an_evaluation=99.78 limit=3907.2
PP: TOWER_SECTION pass=0 section=1120 bits_a_byte=1.946 deposits=1120 halvings=18 elapsed_ms=110955 | window sections=32 halvings=0 evaluations=32 ms=3176 ms_an_evaluation=99.25 limit=3899.8
PR: TOWER_SECTION pass=0 section=1120 bits_a_byte=1.987 deposits=1120 halvings=12 elapsed_ms=111228 | window sections=32 halvings=0 evaluations=32 ms=3190 ms_an_evaluation=99.69 limit=3907.2
PP: TOWER_SECTION pass=0 section=1152 bits_a_byte=1.958 deposits=1152 halvings=18 elapsed_ms=114164 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=3899.8
PR: TOWER_SECTION pass=0 section=1152 bits_a_byte=1.994 deposits=1152 halvings=12 elapsed_ms=114420 | window sections=32 halvings=0 evaluations=32 ms=3192 ms_an_evaluation=99.75 limit=3907.2
PP: TOWER_SECTION pass=0 section=1184 bits_a_byte=1.917 deposits=1184 halvings=18 elapsed_ms=117344 | window sections=32 halvings=0 evaluations=32 ms=3180 ms_an_evaluation=99.38 limit=3899.8
PR: TOWER_SECTION pass=0 section=1184 bits_a_byte=1.948 deposits=1184 halvings=12 elapsed_ms=117597 | window sections=32 halvings=0 evaluations=32 ms=3177 ms_an_evaluation=99.28 limit=3907.2
PP: TOWER_SECTION pass=0 section=1216 bits_a_byte=1.943 deposits=1216 halvings=18 elapsed_ms=120519 | window sections=32 halvings=0 evaluations=32 ms=3175 ms_an_evaluation=99.22 limit=3899.8
PR: TOWER_SECTION pass=0 section=1216 bits_a_byte=1.978 deposits=1216 halvings=12 elapsed_ms=120818 | window sections=32 halvings=0 evaluations=32 ms=3221 ms_an_evaluation=100.66 limit=3907.2
PP: TOWER_SECTION pass=0 section=1248 bits_a_byte=1.909 deposits=1248 halvings=18 elapsed_ms=123670 | window sections=32 halvings=0 evaluations=32 ms=3151 ms_an_evaluation=98.47 limit=3899.8
PR: TOWER_SECTION pass=0 section=1248 bits_a_byte=1.944 deposits=1248 halvings=12 elapsed_ms=124001 | window sections=32 halvings=0 evaluations=32 ms=3183 ms_an_evaluation=99.47 limit=3907.2
PP: TOWER_SECTION pass=0 section=1280 bits_a_byte=1.930 deposits=1280 halvings=18 elapsed_ms=126827 | window sections=32 halvings=0 evaluations=32 ms=3157 ms_an_evaluation=98.66 limit=3899.8
PR: TOWER_SECTION pass=0 section=1280 bits_a_byte=1.964 deposits=1280 halvings=12 elapsed_ms=127155 | window sections=32 halvings=0 evaluations=32 ms=3154 ms_an_evaluation=98.56 limit=3907.2
PP: TOWER_SECTION pass=0 section=1311 bits_a_byte=1.896 deposits=1311 halvings=18 elapsed_ms=129884 | window sections=31 halvings=0 evaluations=31 ms=3057 ms_an_evaluation=98.61 limit=3778.0
PP: TOWER_STATE STATE.0 state_bytes=12512888 state_sha256=db9644cd6372e877024d55182c5f38d47acdae5531d47e8f844b64ff3761d34b
PR: TOWER_SECTION pass=0 section=1311 bits_a_byte=1.935 deposits=1311 halvings=12 elapsed_ms=130225 | window sections=31 halvings=0 evaluations=31 ms=3070 ms_an_evaluation=99.03 limit=3785.1
PR: TOWER_STATE STATE.0 state_bytes=12629596 state_sha256=375bd4bde38ea4623cc724bd2789c2ad6f46d85837bae1885d0c005c1b1bdada
PP: TOWER_PASS pass=0 train_bits_a_byte=2.160 dev_bits_a_byte=1.931 dev_regions Q=1.370 P=2.447 N=0.624 M=1.940 deposits=1311/1311 pass_ms=134032 elapsed_ms=134046 train_code=7989204032235 dev_code=805156744401 grain_bits=20
PR: TOWER_PASS pass=0 train_bits_a_byte=2.199 dev_bits_a_byte=1.970 dev_regions Q=1.420 P=2.588 N=0.710 M=1.978 deposits=1311/1311 pass_ms=134863 elapsed_ms=134881 train_code=8133511771444 dev_code=821581221755 grain_bits=20
PP: TOWER_SECTION pass=1 section=32 bits_a_byte=1.983 deposits=32 halvings=19 elapsed_ms=137819 | window sections=32 halvings=19 evaluations=51 ms=3773 ms_an_evaluation=73.98 limit=6215.4
PR: TOWER_SECTION pass=1 section=32 bits_a_byte=1.934 deposits=32 halvings=0 elapsed_ms=138052 | window sections=32 halvings=0 evaluations=32 ms=3171 ms_an_evaluation=99.09 limit=3907.2
PP: TOWER_SECTION pass=1 section=64 bits_a_byte=1.916 deposits=64 halvings=19 elapsed_ms=140981 | window sections=32 halvings=0 evaluations=32 ms=3162 ms_an_evaluation=98.81 limit=3899.8
PR: TOWER_SECTION pass=1 section=64 bits_a_byte=1.927 deposits=64 halvings=0 elapsed_ms=141202 | window sections=32 halvings=0 evaluations=32 ms=3150 ms_an_evaluation=98.44 limit=3907.2
PP: TOWER_SECTION pass=1 section=96 bits_a_byte=1.931 deposits=96 halvings=19 elapsed_ms=144134 | window sections=32 halvings=0 evaluations=32 ms=3153 ms_an_evaluation=98.53 limit=3899.8
PR: TOWER_SECTION pass=1 section=96 bits_a_byte=1.943 deposits=96 halvings=0 elapsed_ms=144355 | window sections=32 halvings=0 evaluations=32 ms=3153 ms_an_evaluation=98.53 limit=3907.2
PP: TOWER_SECTION pass=1 section=128 bits_a_byte=1.895 deposits=128 halvings=19 elapsed_ms=147275 | window sections=32 halvings=0 evaluations=32 ms=3141 ms_an_evaluation=98.16 limit=3899.8
PR: TOWER_SECTION pass=1 section=128 bits_a_byte=1.917 deposits=128 halvings=0 elapsed_ms=147507 | window sections=32 halvings=0 evaluations=32 ms=3152 ms_an_evaluation=98.50 limit=3907.2
PP: TOWER_SECTION pass=1 section=160 bits_a_byte=1.903 deposits=160 halvings=19 elapsed_ms=150434 | window sections=32 halvings=0 evaluations=32 ms=3159 ms_an_evaluation=98.72 limit=3899.8
PR: TOWER_SECTION pass=1 section=160 bits_a_byte=1.929 deposits=160 halvings=0 elapsed_ms=150690 | window sections=32 halvings=0 evaluations=32 ms=3183 ms_an_evaluation=99.47 limit=3907.2
PP: TOWER_SECTION pass=1 section=192 bits_a_byte=1.868 deposits=192 halvings=19 elapsed_ms=153635 | window sections=32 halvings=0 evaluations=32 ms=3201 ms_an_evaluation=100.03 limit=3899.8
PR: TOWER_SECTION pass=1 section=192 bits_a_byte=1.912 deposits=192 halvings=0 elapsed_ms=153935 | window sections=32 halvings=0 evaluations=32 ms=3245 ms_an_evaluation=101.41 limit=3907.2
PP: TOWER_SECTION pass=1 section=224 bits_a_byte=1.816 deposits=224 halvings=19 elapsed_ms=156796 | window sections=32 halvings=0 evaluations=32 ms=3161 ms_an_evaluation=98.78 limit=3899.8
PR: TOWER_SECTION pass=1 section=224 bits_a_byte=1.853 deposits=224 halvings=0 elapsed_ms=157113 | window sections=32 halvings=0 evaluations=32 ms=3178 ms_an_evaluation=99.31 limit=3907.2
PP: TOWER_SECTION pass=1 section=256 bits_a_byte=1.915 deposits=256 halvings=19 elapsed_ms=159935 | window sections=32 halvings=0 evaluations=32 ms=3139 ms_an_evaluation=98.09 limit=3899.8
PR: TOWER_SECTION pass=1 section=256 bits_a_byte=1.948 deposits=256 halvings=0 elapsed_ms=160294 | window sections=32 halvings=0 evaluations=32 ms=3181 ms_an_evaluation=99.41 limit=3907.2
PP: TOWER_SECTION pass=1 section=288 bits_a_byte=1.873 deposits=288 halvings=19 elapsed_ms=163133 | window sections=32 halvings=0 evaluations=32 ms=3198 ms_an_evaluation=99.94 limit=3899.8
PR: TOWER_SECTION pass=1 section=288 bits_a_byte=1.908 deposits=288 halvings=0 elapsed_ms=163448 | window sections=32 halvings=0 evaluations=32 ms=3154 ms_an_evaluation=98.56 limit=3907.2
PP: TOWER_SECTION pass=1 section=320 bits_a_byte=1.843 deposits=320 halvings=19 elapsed_ms=166298 | window sections=32 halvings=0 evaluations=32 ms=3165 ms_an_evaluation=98.91 limit=3899.8
PR: TOWER_SECTION pass=1 section=320 bits_a_byte=1.876 deposits=320 halvings=0 elapsed_ms=166679 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=3907.2
PP: TOWER_SECTION pass=1 section=352 bits_a_byte=1.871 deposits=352 halvings=19 elapsed_ms=169523 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=1 section=352 bits_a_byte=1.904 deposits=352 halvings=0 elapsed_ms=169911 | window sections=32 halvings=0 evaluations=32 ms=3232 ms_an_evaluation=101.00 limit=3907.2
PP: TOWER_SECTION pass=1 section=384 bits_a_byte=1.876 deposits=384 halvings=19 elapsed_ms=172765 | window sections=32 halvings=0 evaluations=32 ms=3242 ms_an_evaluation=101.31 limit=3899.8
PR: TOWER_SECTION pass=1 section=384 bits_a_byte=1.909 deposits=384 halvings=0 elapsed_ms=173201 | window sections=32 halvings=0 evaluations=32 ms=3290 ms_an_evaluation=102.81 limit=3907.2
PP: TOWER_SECTION pass=1 section=416 bits_a_byte=1.853 deposits=416 halvings=19 elapsed_ms=176003 | window sections=32 halvings=0 evaluations=32 ms=3238 ms_an_evaluation=101.19 limit=3899.8
PR: TOWER_SECTION pass=1 section=416 bits_a_byte=1.880 deposits=416 halvings=0 elapsed_ms=176440 | window sections=32 halvings=0 evaluations=32 ms=3239 ms_an_evaluation=101.22 limit=3907.2
PP: TOWER_SECTION pass=1 section=448 bits_a_byte=1.858 deposits=448 halvings=19 elapsed_ms=179264 | window sections=32 halvings=0 evaluations=32 ms=3261 ms_an_evaluation=101.91 limit=3899.8
PR: TOWER_SECTION pass=1 section=448 bits_a_byte=1.895 deposits=448 halvings=0 elapsed_ms=179702 | window sections=32 halvings=0 evaluations=32 ms=3262 ms_an_evaluation=101.94 limit=3907.2
PP: TOWER_SECTION pass=1 section=480 bits_a_byte=1.847 deposits=480 halvings=19 elapsed_ms=182531 | window sections=32 halvings=0 evaluations=32 ms=3267 ms_an_evaluation=102.09 limit=3899.8
PR: TOWER_SECTION pass=1 section=480 bits_a_byte=1.878 deposits=480 halvings=0 elapsed_ms=182971 | window sections=32 halvings=0 evaluations=32 ms=3269 ms_an_evaluation=102.16 limit=3907.2
PP: TOWER_SECTION pass=1 section=512 bits_a_byte=1.844 deposits=512 halvings=19 elapsed_ms=185794 | window sections=32 halvings=0 evaluations=32 ms=3263 ms_an_evaluation=101.97 limit=3899.8
PR: TOWER_SECTION pass=1 section=512 bits_a_byte=1.875 deposits=512 halvings=0 elapsed_ms=186209 | window sections=32 halvings=0 evaluations=32 ms=3238 ms_an_evaluation=101.19 limit=3907.2
PP: TOWER_SECTION pass=1 section=544 bits_a_byte=1.802 deposits=544 halvings=19 elapsed_ms=189027 | window sections=32 halvings=0 evaluations=32 ms=3233 ms_an_evaluation=101.03 limit=3899.8
PR: TOWER_SECTION pass=1 section=544 bits_a_byte=1.837 deposits=544 halvings=0 elapsed_ms=189421 | window sections=32 halvings=0 evaluations=32 ms=3212 ms_an_evaluation=100.38 limit=3907.2
PP: TOWER_SECTION pass=1 section=576 bits_a_byte=1.855 deposits=576 halvings=19 elapsed_ms=192257 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=3899.8
PR: TOWER_SECTION pass=1 section=576 bits_a_byte=1.883 deposits=576 halvings=0 elapsed_ms=192658 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=3907.2
PP: TOWER_SECTION pass=1 section=608 bits_a_byte=1.828 deposits=608 halvings=19 elapsed_ms=195482 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=1 section=608 bits_a_byte=1.851 deposits=608 halvings=0 elapsed_ms=195882 | window sections=32 halvings=0 evaluations=32 ms=3224 ms_an_evaluation=100.75 limit=3907.2
PP: TOWER_SECTION pass=1 section=640 bits_a_byte=1.822 deposits=640 halvings=19 elapsed_ms=198674 | window sections=32 halvings=0 evaluations=32 ms=3192 ms_an_evaluation=99.75 limit=3899.8
PR: TOWER_SECTION pass=1 section=640 bits_a_byte=1.847 deposits=640 halvings=0 elapsed_ms=199076 | window sections=32 halvings=0 evaluations=32 ms=3194 ms_an_evaluation=99.81 limit=3907.2
PP: TOWER_SECTION pass=1 section=672 bits_a_byte=1.828 deposits=672 halvings=19 elapsed_ms=201890 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=3899.8
PR: TOWER_SECTION pass=1 section=672 bits_a_byte=1.860 deposits=672 halvings=0 elapsed_ms=202291 | window sections=32 halvings=0 evaluations=32 ms=3215 ms_an_evaluation=100.47 limit=3907.2
PP: TOWER_SECTION pass=1 section=704 bits_a_byte=1.819 deposits=704 halvings=19 elapsed_ms=205155 | window sections=32 halvings=0 evaluations=32 ms=3265 ms_an_evaluation=102.03 limit=3899.8
PR: TOWER_SECTION pass=1 section=704 bits_a_byte=1.848 deposits=704 halvings=0 elapsed_ms=205533 | window sections=32 halvings=0 evaluations=32 ms=3242 ms_an_evaluation=101.31 limit=3907.2
PP: TOWER_SECTION pass=1 section=736 bits_a_byte=1.813 deposits=736 halvings=19 elapsed_ms=208425 | window sections=32 halvings=0 evaluations=32 ms=3270 ms_an_evaluation=102.19 limit=3899.8
PR: TOWER_SECTION pass=1 section=736 bits_a_byte=1.839 deposits=736 halvings=0 elapsed_ms=208821 | window sections=32 halvings=0 evaluations=32 ms=3288 ms_an_evaluation=102.75 limit=3907.2
PP: TOWER_SECTION pass=1 section=768 bits_a_byte=1.822 deposits=768 halvings=19 elapsed_ms=211693 | window sections=32 halvings=0 evaluations=32 ms=3268 ms_an_evaluation=102.12 limit=3899.8
PR: TOWER_SECTION pass=1 section=768 bits_a_byte=1.841 deposits=768 halvings=0 elapsed_ms=212043 | window sections=32 halvings=0 evaluations=32 ms=3222 ms_an_evaluation=100.69 limit=3907.2
PP: TOWER_SECTION pass=1 section=800 bits_a_byte=1.787 deposits=800 halvings=19 elapsed_ms=214904 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=3899.8
PR: TOWER_SECTION pass=1 section=800 bits_a_byte=1.816 deposits=800 halvings=0 elapsed_ms=215254 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=3907.2
PP: TOWER_SECTION pass=1 section=832 bits_a_byte=1.810 deposits=832 halvings=19 elapsed_ms=218096 | window sections=32 halvings=0 evaluations=32 ms=3192 ms_an_evaluation=99.75 limit=3899.8
PR: TOWER_SECTION pass=1 section=832 bits_a_byte=1.826 deposits=832 halvings=0 elapsed_ms=218422 | window sections=32 halvings=0 evaluations=32 ms=3168 ms_an_evaluation=99.00 limit=3907.2
PP: TOWER_SECTION pass=1 section=864 bits_a_byte=1.807 deposits=864 halvings=19 elapsed_ms=221268 | window sections=32 halvings=0 evaluations=32 ms=3172 ms_an_evaluation=99.12 limit=3899.8
PR: TOWER_SECTION pass=1 section=864 bits_a_byte=1.839 deposits=864 halvings=0 elapsed_ms=221633 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=3907.2
PP: TOWER_SECTION pass=1 section=896 bits_a_byte=1.810 deposits=896 halvings=19 elapsed_ms=224471 | window sections=32 halvings=0 evaluations=32 ms=3203 ms_an_evaluation=100.09 limit=3899.8
PR: TOWER_SECTION pass=1 section=896 bits_a_byte=1.844 deposits=896 halvings=0 elapsed_ms=224872 | window sections=32 halvings=0 evaluations=32 ms=3239 ms_an_evaluation=101.22 limit=3907.2
PP: TOWER_SECTION pass=1 section=928 bits_a_byte=1.833 deposits=928 halvings=19 elapsed_ms=227742 | window sections=32 halvings=0 evaluations=32 ms=3271 ms_an_evaluation=102.22 limit=3899.8
PR: TOWER_SECTION pass=1 section=928 bits_a_byte=1.860 deposits=928 halvings=0 elapsed_ms=228114 | window sections=32 halvings=0 evaluations=32 ms=3242 ms_an_evaluation=101.31 limit=3907.2
PP: TOWER_SECTION pass=1 section=960 bits_a_byte=1.800 deposits=960 halvings=19 elapsed_ms=230990 | window sections=32 halvings=0 evaluations=32 ms=3248 ms_an_evaluation=101.50 limit=3899.8
PR: TOWER_SECTION pass=1 section=960 bits_a_byte=1.829 deposits=960 halvings=0 elapsed_ms=231391 | window sections=32 halvings=0 evaluations=32 ms=3277 ms_an_evaluation=102.41 limit=3907.2
PP: TOWER_SECTION pass=1 section=992 bits_a_byte=1.814 deposits=992 halvings=19 elapsed_ms=234203 | window sections=32 halvings=0 evaluations=32 ms=3213 ms_an_evaluation=100.41 limit=3899.8
PR: TOWER_SECTION pass=1 section=992 bits_a_byte=1.833 deposits=992 halvings=0 elapsed_ms=234608 | window sections=32 halvings=0 evaluations=32 ms=3217 ms_an_evaluation=100.53 limit=3907.2
PP: TOWER_SECTION pass=1 section=1024 bits_a_byte=1.768 deposits=1024 halvings=19 elapsed_ms=237398 | window sections=32 halvings=0 evaluations=32 ms=3195 ms_an_evaluation=99.84 limit=3899.8
PR: TOWER_SECTION pass=1 section=1024 bits_a_byte=1.803 deposits=1024 halvings=0 elapsed_ms=237823 | window sections=32 halvings=0 evaluations=32 ms=3215 ms_an_evaluation=100.47 limit=3907.2
PP: TOWER_SECTION pass=1 section=1056 bits_a_byte=1.786 deposits=1056 halvings=19 elapsed_ms=240589 | window sections=32 halvings=0 evaluations=32 ms=3191 ms_an_evaluation=99.72 limit=3899.8
PR: TOWER_SECTION pass=1 section=1056 bits_a_byte=1.811 deposits=1056 halvings=0 elapsed_ms=241054 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=3907.2
PP: TOWER_SECTION pass=1 section=1088 bits_a_byte=1.822 deposits=1088 halvings=19 elapsed_ms=243811 | window sections=32 halvings=0 evaluations=32 ms=3222 ms_an_evaluation=100.69 limit=3899.8
PR: TOWER_SECTION pass=1 section=1088 bits_a_byte=1.846 deposits=1088 halvings=0 elapsed_ms=244301 | window sections=32 halvings=0 evaluations=32 ms=3247 ms_an_evaluation=101.47 limit=3907.2
PR: TOWER_SECTION pass=1 section=1120 bits_a_byte=1.824 deposits=1120 halvings=0 elapsed_ms=247543 | window sections=32 halvings=0 evaluations=32 ms=3242 ms_an_evaluation=101.31 limit=3907.2
PP: TOWER_SECTION pass=1 section=1120 bits_a_byte=2.067 deposits=1120 halvings=74 elapsed_ms=249047 | window sections=32 halvings=55 evaluations=87 ms=5236 ms_an_evaluation=60.18 limit=10602.7
PR: TOWER_SECTION pass=1 section=1152 bits_a_byte=1.838 deposits=1152 halvings=0 elapsed_ms=250771 | window sections=32 halvings=0 evaluations=32 ms=3228 ms_an_evaluation=100.88 limit=3907.2
PP: TOWER_SECTION pass=1 section=1152 bits_a_byte=1.995 deposits=1152 halvings=75 elapsed_ms=252337 | window sections=32 halvings=1 evaluations=33 ms=3290 ms_an_evaluation=99.70 limit=4021.7
PR: TOWER_SECTION pass=1 section=1184 bits_a_byte=1.793 deposits=1184 halvings=0 elapsed_ms=254009 | window sections=32 halvings=0 evaluations=32 ms=3238 ms_an_evaluation=101.19 limit=3907.2
PP: TOWER_SECTION pass=1 section=1184 bits_a_byte=1.836 deposits=1184 halvings=75 elapsed_ms=255562 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=1 section=1216 bits_a_byte=1.822 deposits=1216 halvings=0 elapsed_ms=257239 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=3907.2
PP: TOWER_SECTION pass=1 section=1216 bits_a_byte=1.836 deposits=1216 halvings=75 elapsed_ms=258793 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=3899.8
PR: TOWER_SECTION pass=1 section=1248 bits_a_byte=1.798 deposits=1248 halvings=0 elapsed_ms=260487 | window sections=32 halvings=0 evaluations=32 ms=3248 ms_an_evaluation=101.50 limit=3907.2
PP: TOWER_SECTION pass=1 section=1248 bits_a_byte=1.796 deposits=1248 halvings=75 elapsed_ms=262042 | window sections=32 halvings=0 evaluations=32 ms=3249 ms_an_evaluation=101.53 limit=3899.8
PR: TOWER_SECTION pass=1 section=1280 bits_a_byte=1.817 deposits=1280 halvings=0 elapsed_ms=263744 | window sections=32 halvings=0 evaluations=32 ms=3257 ms_an_evaluation=101.78 limit=3907.2
PP: TOWER_SECTION pass=1 section=1280 bits_a_byte=1.807 deposits=1280 halvings=75 elapsed_ms=265279 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=3899.8
PR: TOWER_SECTION pass=1 section=1311 bits_a_byte=1.796 deposits=1311 halvings=0 elapsed_ms=266891 | window sections=31 halvings=0 evaluations=31 ms=3147 ms_an_evaluation=101.52 limit=3785.1
PR: TOWER_STATE STATE.1 state_bytes=12560464 state_sha256=10bdf03bcce35e98a738121eb80c2870e0018195381086ba1aeabcbffb804d28
PP: TOWER_SECTION pass=1 section=1311 bits_a_byte=1.775 deposits=1311 halvings=75 elapsed_ms=268484 | window sections=31 halvings=0 evaluations=31 ms=3205 ms_an_evaluation=103.39 limit=3778.0
PP: TOWER_STATE STATE.1 state_bytes=12640645 state_sha256=d0526136de37e1cc4881b658f6c4dbdad1ea24950ae86e7947efb45a7621a806
PR: TOWER_PASS pass=1 train_bits_a_byte=1.861 dev_bits_a_byte=1.843 dev_regions Q=1.264 P=2.393 N=0.564 M=1.852 deposits=1311/1311 pass_ms=136519 elapsed_ms=271401 train_code=6882748134887 dev_code=768509837826 grain_bits=20
PP: TOWER_PASS pass=1 train_bits_a_byte=1.850 dev_bits_a_byte=1.823 dev_regions Q=1.332 P=2.457 N=0.478 M=1.830 deposits=1311/1311 pass_ms=138964 elapsed_ms=273011 train_code=6841388160634 dev_code=759994637224 grain_bits=20
PR: TOWER_SECTION pass=2 section=32 bits_a_byte=1.795 deposits=32 halvings=0 elapsed_ms=274630 | window sections=32 halvings=0 evaluations=32 ms=3229 ms_an_evaluation=100.91 limit=3907.2
PP: TOWER_SECTION pass=2 section=32 bits_a_byte=1.925 deposits=32 halvings=15 elapsed_ms=276774 | window sections=32 halvings=15 evaluations=47 ms=3763 ms_an_evaluation=80.06 limit=5727.9
PR: TOWER_SECTION pass=2 section=64 bits_a_byte=1.792 deposits=64 halvings=0 elapsed_ms=277799 | window sections=32 halvings=0 evaluations=32 ms=3169 ms_an_evaluation=99.03 limit=3907.2
PP: TOWER_SECTION pass=2 section=64 bits_a_byte=1.824 deposits=64 halvings=15 elapsed_ms=279986 | window sections=32 halvings=0 evaluations=32 ms=3212 ms_an_evaluation=100.38 limit=3899.8
PR: TOWER_SECTION pass=2 section=96 bits_a_byte=1.810 deposits=96 halvings=0 elapsed_ms=281021 | window sections=32 halvings=0 evaluations=32 ms=3222 ms_an_evaluation=100.69 limit=3907.2
PP: TOWER_SECTION pass=2 section=96 bits_a_byte=1.827 deposits=96 halvings=15 elapsed_ms=283197 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=3899.8
PR: TOWER_SECTION pass=2 section=128 bits_a_byte=1.788 deposits=128 halvings=0 elapsed_ms=284230 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=3907.2
PP: TOWER_SECTION pass=2 section=128 bits_a_byte=1.798 deposits=128 halvings=15 elapsed_ms=286414 | window sections=32 halvings=0 evaluations=32 ms=3217 ms_an_evaluation=100.53 limit=3899.8
PR: TOWER_SECTION pass=2 section=160 bits_a_byte=1.798 deposits=160 halvings=0 elapsed_ms=287432 | window sections=32 halvings=0 evaluations=32 ms=3202 ms_an_evaluation=100.06 limit=3907.2
PP: TOWER_SECTION pass=2 section=160 bits_a_byte=1.795 deposits=160 halvings=15 elapsed_ms=289618 | window sections=32 halvings=0 evaluations=32 ms=3204 ms_an_evaluation=100.12 limit=3899.8
PR: TOWER_SECTION pass=2 section=192 bits_a_byte=1.774 deposits=192 halvings=0 elapsed_ms=290623 | window sections=32 halvings=0 evaluations=32 ms=3191 ms_an_evaluation=99.72 limit=3907.2
PP: TOWER_SECTION pass=2 section=192 bits_a_byte=1.766 deposits=192 halvings=15 elapsed_ms=292804 | window sections=32 halvings=0 evaluations=32 ms=3186 ms_an_evaluation=99.56 limit=3899.8
PR: TOWER_SECTION pass=2 section=224 bits_a_byte=1.722 deposits=224 halvings=0 elapsed_ms=293819 | window sections=32 halvings=0 evaluations=32 ms=3196 ms_an_evaluation=99.88 limit=3907.2
PP: TOWER_SECTION pass=2 section=224 bits_a_byte=1.707 deposits=224 halvings=15 elapsed_ms=296029 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=2 section=256 bits_a_byte=1.829 deposits=256 halvings=0 elapsed_ms=297016 | window sections=32 halvings=0 evaluations=32 ms=3197 ms_an_evaluation=99.91 limit=3907.2
PP: TOWER_SECTION pass=2 section=256 bits_a_byte=1.811 deposits=256 halvings=15 elapsed_ms=299278 | window sections=32 halvings=0 evaluations=32 ms=3249 ms_an_evaluation=101.53 limit=3899.8
PR: TOWER_SECTION pass=2 section=288 bits_a_byte=1.793 deposits=288 halvings=0 elapsed_ms=300222 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=3907.2
PP: TOWER_SECTION pass=2 section=288 bits_a_byte=1.769 deposits=288 halvings=15 elapsed_ms=302477 | window sections=32 halvings=0 evaluations=32 ms=3199 ms_an_evaluation=99.97 limit=3899.8
PR: TOWER_SECTION pass=2 section=320 bits_a_byte=1.760 deposits=320 halvings=0 elapsed_ms=303393 | window sections=32 halvings=0 evaluations=32 ms=3171 ms_an_evaluation=99.09 limit=3907.2
PP: TOWER_SECTION pass=2 section=320 bits_a_byte=1.774 deposits=320 halvings=15 elapsed_ms=305660 | window sections=32 halvings=0 evaluations=32 ms=3183 ms_an_evaluation=99.47 limit=3899.8
PR: TOWER_SECTION pass=2 section=352 bits_a_byte=1.787 deposits=352 halvings=0 elapsed_ms=306597 | window sections=32 halvings=0 evaluations=32 ms=3204 ms_an_evaluation=100.12 limit=3907.2
PP: TOWER_SECTION pass=2 section=352 bits_a_byte=1.779 deposits=352 halvings=15 elapsed_ms=308859 | window sections=32 halvings=0 evaluations=32 ms=3199 ms_an_evaluation=99.97 limit=3899.8
PR: TOWER_SECTION pass=2 section=384 bits_a_byte=1.811 deposits=384 halvings=0 elapsed_ms=309779 | window sections=32 halvings=0 evaluations=32 ms=3182 ms_an_evaluation=99.44 limit=3907.2
PP: TOWER_SECTION pass=2 section=384 bits_a_byte=1.781 deposits=384 halvings=15 elapsed_ms=312028 | window sections=32 halvings=0 evaluations=32 ms=3169 ms_an_evaluation=99.03 limit=3899.8
PR: TOWER_SECTION pass=2 section=416 bits_a_byte=1.778 deposits=416 halvings=0 elapsed_ms=312995 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=3907.2
PP: TOWER_SECTION pass=2 section=416 bits_a_byte=1.748 deposits=416 halvings=15 elapsed_ms=315246 | window sections=32 halvings=0 evaluations=32 ms=3218 ms_an_evaluation=100.56 limit=3899.8
PR: TOWER_SECTION pass=2 section=448 bits_a_byte=1.792 deposits=448 halvings=0 elapsed_ms=316200 | window sections=32 halvings=0 evaluations=32 ms=3205 ms_an_evaluation=100.16 limit=3907.2
PP: TOWER_SECTION pass=2 section=448 bits_a_byte=1.764 deposits=448 halvings=15 elapsed_ms=318458 | window sections=32 halvings=0 evaluations=32 ms=3212 ms_an_evaluation=100.38 limit=3899.8
PR: TOWER_SECTION pass=2 section=480 bits_a_byte=1.778 deposits=480 halvings=0 elapsed_ms=319424 | window sections=32 halvings=0 evaluations=32 ms=3224 ms_an_evaluation=100.75 limit=3907.2
PP: TOWER_SECTION pass=2 section=480 bits_a_byte=1.749 deposits=480 halvings=15 elapsed_ms=321674 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=3899.8
PR: TOWER_SECTION pass=2 section=512 bits_a_byte=1.772 deposits=512 halvings=0 elapsed_ms=322599 | window sections=32 halvings=0 evaluations=32 ms=3175 ms_an_evaluation=99.22 limit=3907.2
PP: TOWER_SECTION pass=2 section=512 bits_a_byte=1.745 deposits=512 halvings=15 elapsed_ms=324876 | window sections=32 halvings=0 evaluations=32 ms=3202 ms_an_evaluation=100.06 limit=3899.8
PR: TOWER_SECTION pass=2 section=544 bits_a_byte=1.733 deposits=544 halvings=0 elapsed_ms=325789 | window sections=32 halvings=0 evaluations=32 ms=3190 ms_an_evaluation=99.69 limit=3907.2
PP: TOWER_SECTION pass=2 section=544 bits_a_byte=1.703 deposits=544 halvings=15 elapsed_ms=328121 | window sections=32 halvings=0 evaluations=32 ms=3245 ms_an_evaluation=101.41 limit=3899.8
PR: TOWER_SECTION pass=2 section=576 bits_a_byte=1.783 deposits=576 halvings=0 elapsed_ms=329006 | window sections=32 halvings=0 evaluations=32 ms=3217 ms_an_evaluation=100.53 limit=3907.2
PP: TOWER_SECTION pass=2 section=576 bits_a_byte=1.747 deposits=576 halvings=15 elapsed_ms=331374 | window sections=32 halvings=0 evaluations=32 ms=3253 ms_an_evaluation=101.66 limit=3899.8
PR: TOWER_SECTION pass=2 section=608 bits_a_byte=1.758 deposits=608 halvings=0 elapsed_ms=332266 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=3907.2
PP: TOWER_SECTION pass=2 section=608 bits_a_byte=1.730 deposits=608 halvings=15 elapsed_ms=334533 | window sections=32 halvings=0 evaluations=32 ms=3159 ms_an_evaluation=98.72 limit=3899.8
PR: TOWER_SECTION pass=2 section=640 bits_a_byte=1.758 deposits=640 halvings=0 elapsed_ms=335470 | window sections=32 halvings=0 evaluations=32 ms=3204 ms_an_evaluation=100.12 limit=3907.2
PP: TOWER_SECTION pass=2 section=640 bits_a_byte=1.726 deposits=640 halvings=15 elapsed_ms=337752 | window sections=32 halvings=0 evaluations=32 ms=3219 ms_an_evaluation=100.59 limit=3899.8
PR: TOWER_SECTION pass=2 section=672 bits_a_byte=1.760 deposits=672 halvings=0 elapsed_ms=338662 | window sections=32 halvings=0 evaluations=32 ms=3192 ms_an_evaluation=99.75 limit=3907.2
PP: TOWER_SECTION pass=2 section=672 bits_a_byte=1.735 deposits=672 halvings=15 elapsed_ms=340921 | window sections=32 halvings=0 evaluations=32 ms=3169 ms_an_evaluation=99.03 limit=3899.8
PR: TOWER_SECTION pass=2 section=704 bits_a_byte=1.751 deposits=704 halvings=0 elapsed_ms=341828 | window sections=32 halvings=0 evaluations=32 ms=3166 ms_an_evaluation=98.94 limit=3907.2
PP: TOWER_SECTION pass=2 section=704 bits_a_byte=1.728 deposits=704 halvings=15 elapsed_ms=344078 | window sections=32 halvings=0 evaluations=32 ms=3157 ms_an_evaluation=98.66 limit=3899.8
PR: TOWER_SECTION pass=2 section=736 bits_a_byte=1.745 deposits=736 halvings=0 elapsed_ms=344994 | window sections=32 halvings=0 evaluations=32 ms=3166 ms_an_evaluation=98.94 limit=3907.2
PP: TOWER_SECTION pass=2 section=736 bits_a_byte=1.724 deposits=736 halvings=15 elapsed_ms=347253 | window sections=32 halvings=0 evaluations=32 ms=3175 ms_an_evaluation=99.22 limit=3899.8
PR: TOWER_SECTION pass=2 section=768 bits_a_byte=1.748 deposits=768 halvings=0 elapsed_ms=348189 | window sections=32 halvings=0 evaluations=32 ms=3195 ms_an_evaluation=99.84 limit=3907.2
PP: TOWER_SECTION pass=2 section=768 bits_a_byte=1.731 deposits=768 halvings=15 elapsed_ms=350433 | window sections=32 halvings=0 evaluations=32 ms=3180 ms_an_evaluation=99.38 limit=3899.8
PR: TOWER_SECTION pass=2 section=800 bits_a_byte=1.731 deposits=800 halvings=0 elapsed_ms=351351 | window sections=32 halvings=0 evaluations=32 ms=3162 ms_an_evaluation=98.81 limit=3907.2
PP: TOWER_SECTION pass=2 section=800 bits_a_byte=1.700 deposits=800 halvings=15 elapsed_ms=353593 | window sections=32 halvings=0 evaluations=32 ms=3160 ms_an_evaluation=98.75 limit=3899.8
PR: TOWER_SECTION pass=2 section=832 bits_a_byte=1.736 deposits=832 halvings=0 elapsed_ms=354519 | window sections=32 halvings=0 evaluations=32 ms=3168 ms_an_evaluation=99.00 limit=3907.2
PP: TOWER_SECTION pass=2 section=832 bits_a_byte=1.718 deposits=832 halvings=15 elapsed_ms=356732 | window sections=32 halvings=0 evaluations=32 ms=3139 ms_an_evaluation=98.09 limit=3899.8
PR: TOWER_SECTION pass=2 section=864 bits_a_byte=1.751 deposits=864 halvings=0 elapsed_ms=357679 | window sections=32 halvings=0 evaluations=32 ms=3160 ms_an_evaluation=98.75 limit=3907.2
PP: TOWER_SECTION pass=2 section=864 bits_a_byte=1.715 deposits=864 halvings=15 elapsed_ms=359906 | window sections=32 halvings=0 evaluations=32 ms=3174 ms_an_evaluation=99.19 limit=3899.8
PR: TOWER_SECTION pass=2 section=896 bits_a_byte=1.765 deposits=896 halvings=0 elapsed_ms=360897 | window sections=32 halvings=0 evaluations=32 ms=3218 ms_an_evaluation=100.56 limit=3907.2
PP: TOWER_SECTION pass=2 section=896 bits_a_byte=1.723 deposits=896 halvings=15 elapsed_ms=363143 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=3899.8
PR: TOWER_SECTION pass=2 section=928 bits_a_byte=1.774 deposits=928 halvings=0 elapsed_ms=364207 | window sections=32 halvings=0 evaluations=32 ms=3310 ms_an_evaluation=103.44 limit=3907.2
PP: TOWER_SECTION pass=2 section=928 bits_a_byte=1.743 deposits=928 halvings=15 elapsed_ms=366407 | window sections=32 halvings=0 evaluations=32 ms=3264 ms_an_evaluation=102.00 limit=3899.8
PR: TOWER_SECTION pass=2 section=960 bits_a_byte=1.741 deposits=960 halvings=0 elapsed_ms=367479 | window sections=32 halvings=0 evaluations=32 ms=3272 ms_an_evaluation=102.25 limit=3907.2
PP: TOWER_SECTION pass=2 section=960 bits_a_byte=1.718 deposits=960 halvings=15 elapsed_ms=369732 | window sections=32 halvings=0 evaluations=32 ms=3325 ms_an_evaluation=103.91 limit=3899.8
PR: TOWER_SECTION pass=2 section=992 bits_a_byte=1.753 deposits=992 halvings=0 elapsed_ms=370872 | window sections=32 halvings=0 evaluations=32 ms=3393 ms_an_evaluation=106.03 limit=3907.2
PP: TOWER_SECTION pass=2 section=992 bits_a_byte=1.727 deposits=992 halvings=15 elapsed_ms=373113 | window sections=32 halvings=0 evaluations=32 ms=3381 ms_an_evaluation=105.66 limit=3899.8
PR: TOWER_SECTION pass=2 section=1024 bits_a_byte=1.715 deposits=1024 halvings=0 elapsed_ms=374243 | window sections=32 halvings=0 evaluations=32 ms=3371 ms_an_evaluation=105.34 limit=3907.2
PP: TOWER_SECTION pass=2 section=1024 bits_a_byte=1.694 deposits=1024 halvings=15 elapsed_ms=376407 | window sections=32 halvings=0 evaluations=32 ms=3294 ms_an_evaluation=102.94 limit=3899.8
PR: TOWER_SECTION pass=2 section=1056 bits_a_byte=1.733 deposits=1056 halvings=0 elapsed_ms=377526 | window sections=32 halvings=0 evaluations=32 ms=3283 ms_an_evaluation=102.59 limit=3907.2
PP: TOWER_SECTION pass=2 section=1056 bits_a_byte=1.711 deposits=1056 halvings=15 elapsed_ms=379623 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=3899.8
PR: TOWER_SECTION pass=2 section=1088 bits_a_byte=1.764 deposits=1088 halvings=0 elapsed_ms=380728 | window sections=32 halvings=0 evaluations=32 ms=3202 ms_an_evaluation=100.06 limit=3907.2
PP: TOWER_SECTION pass=2 section=1088 bits_a_byte=1.738 deposits=1088 halvings=15 elapsed_ms=382848 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=2 section=1120 bits_a_byte=1.751 deposits=1120 halvings=0 elapsed_ms=383981 | window sections=32 halvings=0 evaluations=32 ms=3253 ms_an_evaluation=101.66 limit=3907.2
PP: TOWER_SECTION pass=2 section=1120 bits_a_byte=1.747 deposits=1120 halvings=15 elapsed_ms=386031 | window sections=32 halvings=0 evaluations=32 ms=3183 ms_an_evaluation=99.47 limit=3899.8
PR: TOWER_SECTION pass=2 section=1152 bits_a_byte=1.763 deposits=1152 halvings=0 elapsed_ms=387210 | window sections=32 halvings=0 evaluations=32 ms=3229 ms_an_evaluation=100.91 limit=3907.2
PP: TOWER_SECTION pass=2 section=1152 bits_a_byte=1.755 deposits=1152 halvings=15 elapsed_ms=389256 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=3899.8
PR: TOWER_SECTION pass=2 section=1184 bits_a_byte=1.728 deposits=1184 halvings=0 elapsed_ms=390456 | window sections=32 halvings=0 evaluations=32 ms=3246 ms_an_evaluation=101.44 limit=3907.2
PP: TOWER_SECTION pass=2 section=1184 bits_a_byte=1.715 deposits=1184 halvings=15 elapsed_ms=392462 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=3899.8
PR: TOWER_SECTION pass=2 section=1216 bits_a_byte=1.751 deposits=1216 halvings=0 elapsed_ms=393615 | window sections=32 halvings=0 evaluations=32 ms=3159 ms_an_evaluation=98.72 limit=3907.2
PP: TOWER_SECTION pass=2 section=1216 bits_a_byte=1.740 deposits=1216 halvings=15 elapsed_ms=395642 | window sections=32 halvings=0 evaluations=32 ms=3180 ms_an_evaluation=99.38 limit=3899.8
PR: TOWER_SECTION pass=2 section=1248 bits_a_byte=1.725 deposits=1248 halvings=0 elapsed_ms=396824 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=3907.2
PP: TOWER_SECTION pass=2 section=1248 bits_a_byte=1.717 deposits=1248 halvings=15 elapsed_ms=398861 | window sections=32 halvings=0 evaluations=32 ms=3219 ms_an_evaluation=100.59 limit=3899.8
PR: TOWER_SECTION pass=2 section=1280 bits_a_byte=1.741 deposits=1280 halvings=0 elapsed_ms=400062 | window sections=32 halvings=0 evaluations=32 ms=3238 ms_an_evaluation=101.19 limit=3907.2
PP: TOWER_SECTION pass=2 section=1280 bits_a_byte=1.920 deposits=1280 halvings=38 elapsed_ms=402942 | window sections=32 halvings=23 evaluations=55 ms=4081 ms_an_evaluation=74.20 limit=6702.9
PR: TOWER_SECTION pass=2 section=1311 bits_a_byte=1.726 deposits=1311 halvings=0 elapsed_ms=403230 | window sections=31 halvings=0 evaluations=31 ms=3168 ms_an_evaluation=102.19 limit=3785.1
PR: TOWER_STATE STATE.2 state_bytes=12553041 state_sha256=f8f0585c786e6f699e05c68cfd7f1102f204a3a2fbcfdb338cad048492a67157
PP: TOWER_SECTION pass=2 section=1311 bits_a_byte=1.906 deposits=1311 halvings=38 elapsed_ms=406224 | window sections=31 halvings=0 evaluations=31 ms=3282 ms_an_evaluation=105.87 limit=3778.0
PP: TOWER_STATE STATE.2 state_bytes=12620809 state_sha256=290d41275849d794656e5df56f04020853010678820b10cc774c416d47ae3cef
PR: TOWER_PASS pass=2 train_bits_a_byte=1.762 dev_bits_a_byte=1.779 dev_regions Q=1.201 P=2.459 N=0.423 M=1.786 deposits=1311/1311 pass_ms=136236 elapsed_ms=407638 train_code=6518894018981 dev_code=741609540558 grain_bits=20
PR: TOWER_DONE state_bytes=12553041 state_sha256=f8f0585c786e6f699e05c68cfd7f1102f204a3a2fbcfdb338cad048492a67157 elapsed_ms=407703
PR: RUN_RECEIPT exit=0 wall_s=408.1 peak_rss_kib=291368 user_s=2468.7
PP: TOWER_PASS pass=2 train_bits_a_byte=1.758 dev_bits_a_byte=1.880 dev_regions Q=1.496 P=2.485 N=0.720 M=1.885 deposits=1311/1311 pass_ms=137254 elapsed_ms=410266 train_code=6501375747301 dev_code=783871432605 grain_bits=20
PP: TOWER_DONE state_bytes=12620809 state_sha256=290d41275849d794656e5df56f04020853010678820b10cc774c416d47ae3cef elapsed_ms=410329
PP: RUN_RECEIPT exit=0 wall_s=410.7 peak_rss_kib=293148 user_s=2488.4
```

## The level read of `PP` and `PR`

```text
=== 9. LEVEL READ (pumped/'s four places files; train and held reads of each state and kind together, then the probes)
LOAD at_PP_numerals 2026-10-26T19:45:25Z loadavg=8.10 10.30 6.53
-- at_PP_train_numerals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=088b719ba3e299801e86e8207eee01876f119d3312b826e5a722846f30ecebc5 elapsed_ms=6787
RUN_RECEIPT exit=0 wall_s=6.8 peak_rss_kib=79636 user_s=53.2
-- at_PP_held_numerals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=7c9af5b165b5de2f5a8d34dddfaaa4d9be2dcaf85f43f90f92f38023b9ad34e7 elapsed_ms=2963
RUN_RECEIPT exit=0 wall_s=3.0 peak_rss_kib=39192 user_s=22.6
LOAD at_PP_equals 2026-10-26T19:45:32Z loadavg=8.97 10.44 6.59
-- at_PP_train_equals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=d2bf65d6d3119ab604b82df066eaf1f572b105dfd11ad76586d753fb9bf5db9c elapsed_ms=8488
RUN_RECEIPT exit=0 wall_s=8.5 peak_rss_kib=38892 user_s=66.1
-- at_PP_held_equals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=4da569ccb43d8e86d5e7a5678d84b1d2da95409470420f42512a57e7e4b3905a elapsed_ms=3617
RUN_RECEIPT exit=0 wall_s=3.6 peak_rss_kib=36472 user_s=27.5
LOAD at_PR_numerals 2026-10-26T19:45:41Z loadavg=8.55 10.30 6.59
-- at_PR_train_numerals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=06d3ee1e328511899d78de06f02b47e3b68d68fec6b710d066afa9901a6446de elapsed_ms=6735
RUN_RECEIPT exit=0 wall_s=6.8 peak_rss_kib=78096 user_s=52.7
-- at_PR_held_numerals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=0f4dfc4e617f48ae2fbda5b386f33ed91f7a426abc1b3d0be2158959e5eac787 elapsed_ms=2775
RUN_RECEIPT exit=0 wall_s=2.8 peak_rss_kib=38560 user_s=21.4
LOAD at_PR_equals 2026-10-26T19:45:49Z loadavg=9.67 10.49 6.69
-- at_PR_train_equals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=224d90f8f94da3986d58b6f362f0f98142bb5bd7e21b5425b483c743671a4803 elapsed_ms=8321
RUN_RECEIPT exit=0 wall_s=8.3 peak_rss_kib=38416 user_s=65.2
-- at_PR_held_equals
PROJECTION C's largest took 6.2 s; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=497c597eae6daa885e73365b9dca398ffe0e540dfbc3f238da7a183ebaa6be44 elapsed_ms=3321
RUN_RECEIPT exit=0 wall_s=3.3 peak_rss_kib=36960 user_s=25.8
PROBE PP numerals; DEADLINE 300 s
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=550 energy=367 majority=637 suffix=1530 foil=390
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=1700 energy=1268 majority=3079 suffix=3800 foil=1342
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=621 energy=394 majority=599 suffix=1518 foil=256
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=653 energy=461 majority=827 suffix=1574 foil=480
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=574 energy=346 majority=562 suffix=1491 foil=241
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=611 energy=49 majority=1772 suffix=3800 foil=230
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=480 energy=432 majority=637 suffix=1530 foil=391
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=1461 energy=1519 majority=3079 suffix=3800 foil=1278
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=420 energy=287 majority=599 suffix=1518 foil=245
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=662 energy=522 majority=827 suffix=1574 foil=474
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=449 energy=399 majority=562 suffix=1491 foil=259
NUMERAL_RINGS cells=rotor/at_PP_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=361 energy=126 majority=1772 suffix=3800 foil=213
RUN_RECEIPT exit=0 wall_s=14.1 peak_rss_kib=325740 user_s=13.9
PROBE PP equals; DEADLINE 300 s
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=109 energy=109 majority=143 suffix=620 foil=97
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=298 energy=39 majority=426 suffix=837 foil=179
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=100 energy=67 majority=70 suffix=625 foil=53
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=123 energy=100 majority=138 suffix=628 foil=111
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=70 energy=33 majority=75 suffix=614 foil=57
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=54 energy=16 majority=134 suffix=837 foil=13
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=220 energy=99 majority=134 suffix=676 foil=96
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=507 energy=69 majority=306 suffix=839 foil=137
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=236 energy=67 majority=99 suffix=677 foil=89
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=289 energy=97 majority=141 suffix=673 foil=117
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=211 energy=62 majority=103 suffix=681 foil=60
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=233 energy=7 majority=85 suffix=839 foil=12
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=150 energy=101 majority=92 suffix=615 foil=101
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=255 energy=80 majority=304 suffix=840 foil=113
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=111 energy=73 majority=80 suffix=612 foil=68
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=148 energy=110 majority=133 suffix=627 foil=103
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=98 energy=58 majority=68 suffix=609 foil=60
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=55 energy=19 majority=88 suffix=840 foil=11
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=124 energy=108 majority=143 suffix=620 foil=101
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=302 energy=76 majority=426 suffix=837 foil=194
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=79 energy=73 majority=70 suffix=625 foil=64
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=136 energy=129 majority=138 suffix=628 foil=128
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=57 energy=43 majority=75 suffix=614 foil=57
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=69 energy=15 majority=134 suffix=837 foil=21
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=192 energy=100 majority=134 suffix=676 foil=95
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=345 energy=79 majority=306 suffix=839 foil=129
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=148 energy=82 majority=99 suffix=677 foil=69
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=194 energy=115 majority=141 suffix=673 foil=121
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=112 energy=56 majority=103 suffix=681 foil=65
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=168 energy=17 majority=85 suffix=839 foil=21
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=112 energy=91 majority=92 suffix=615 foil=89
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=250 energy=54 majority=304 suffix=840 foil=118
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=90 energy=61 majority=80 suffix=612 foil=54
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=131 energy=139 majority=133 suffix=627 foil=128
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=84 energy=79 majority=68 suffix=609 foil=64
NUMERAL_RINGS cells=rotor/at_PP_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=65 energy=9 majority=88 suffix=840 foil=15
RUN_RECEIPT exit=0 wall_s=8.2 peak_rss_kib=80228 user_s=8.2
PROBE PR numerals; DEADLINE 300 s
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=788 energy=700 majority=637 suffix=1530 foil=401
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=1040 energy=1825 majority=3079 suffix=3800 foil=789
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=771 energy=816 majority=599 suffix=1518 foil=446
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=887 energy=922 majority=827 suffix=1574 foil=678
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=798 energy=715 majority=562 suffix=1491 foil=277
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=482 energy=1218 majority=1772 suffix=3800 foil=244
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=817 energy=636 majority=637 suffix=1530 foil=449
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=2490 energy=1677 majority=3079 suffix=3800 foil=1912
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=832 energy=486 majority=599 suffix=1518 foil=369
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=930 energy=737 majority=827 suffix=1574 foil=557
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=788 energy=478 majority=562 suffix=1491 foil=287
NUMERAL_RINGS cells=rotor/at_PR_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=1135 energy=293 majority=1772 suffix=3800 foil=444
RUN_RECEIPT exit=0 wall_s=13.6 peak_rss_kib=325604 user_s=13.5
PROBE PR equals; DEADLINE 300 s
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=120 energy=118 majority=143 suffix=620 foil=106
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=182 energy=259 majority=426 suffix=837 foil=134
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=102 energy=95 majority=70 suffix=625 foil=64
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=132 energy=123 majority=138 suffix=628 foil=117
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=83 energy=85 majority=75 suffix=614 foil=62
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=26 energy=12 majority=134 suffix=837 foil=1
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=259 energy=198 majority=134 suffix=676 foil=85
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=458 energy=310 majority=306 suffix=839 foil=95
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=343 energy=196 majority=99 suffix=677 foil=92
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=324 energy=186 majority=141 suffix=673 foil=122
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=321 energy=202 majority=103 suffix=681 foil=56
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=337 energy=228 majority=85 suffix=839 foil=15
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=160 energy=171 majority=92 suffix=615 foil=109
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=323 energy=261 majority=304 suffix=840 foil=145
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=129 energy=134 majority=80 suffix=612 foil=71
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=173 energy=172 majority=133 suffix=627 foil=112
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=102 energy=83 majority=68 suffix=609 foil=67
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=55 energy=34 majority=88 suffix=840 foil=12
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=137 energy=122 majority=143 suffix=620 foil=108
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=363 energy=157 majority=426 suffix=837 foil=200
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=115 energy=81 majority=70 suffix=625 foil=68
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=158 energy=130 majority=138 suffix=628 foil=103
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=99 energy=65 majority=75 suffix=614 foil=63
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=162 energy=51 majority=134 suffix=837 foil=33
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=273 energy=112 majority=134 suffix=676 foil=94
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=533 energy=112 majority=306 suffix=839 foil=150
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=264 energy=70 majority=99 suffix=677 foil=79
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=346 energy=112 majority=141 suffix=673 foil=111
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=267 energy=56 majority=103 suffix=681 foil=54
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=409 energy=85 majority=85 suffix=839 foil=31
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=160 energy=109 majority=92 suffix=615 foil=97
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=349 energy=217 majority=304 suffix=840 foil=150
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=119 energy=82 majority=80 suffix=612 foil=73
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=156 energy=105 majority=133 suffix=627 foil=120
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=102 energy=61 majority=68 suffix=609 foil=60
NUMERAL_RINGS cells=rotor/at_PR_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=149 energy=50 majority=88 suffix=840 foil=23
RUN_RECEIPT exit=0 wall_s=8.0 peak_rss_kib=80312 user_s=7.9
```
