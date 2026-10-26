# The turned loop on Brandon's PC

The lines below are the runs' own output, whole, from the PC's run directory; the run paths are
relative to it. Each heavy run ran under the `wait4` wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8`
and its own memory scope (`MemoryMax=8G`, `MemorySwapMax=0`). The per-process load lines are left
out: at each launch other programs on the host held between a third of a core and a core and a
half, with a spike near two and a half cores summed at the second written read, which still met its
progress line. The load average stood at 9.1 at the training launch (the three development passes
had just ended) and at 14.7 at the first written read (the two trainings had just ended). The
releases, marks and cells hold held-out problem text and stay outside the repository.

## Build, inputs and the two foundings (§6)

Built at `e9dbcca67` in its own worktree and target directory. Every input matched its digest.
`PRT` is founded with the modulated law (the rings turn), `PRS` with the free law (the rings step and
never turn); both found the same rings.
```text
PROJECTION 124 s (the last builds 117.8 to 123.1 s); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
    Finished `release` profile [optimized] target(s) in 2m 01s
RUN_RECEIPT exit=0 wall_s=121.3 peak_rss_kib=3570724 user_s=197.5
BINARY_SHA256 ef81eacd9d90fdd6f696b78bcb7ff1f556cb81d75cccd2761e6ab9976cf374bd RUN/turns/solenoidal_alpha
GIT_LOG e9dbcca6743ab614ce72e152e3f71f95f45a404f brandonrdug@users.noreply.github.com
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
SHA ok rotor/ROTOR_STATE 5d5a91384629a810bfcf58106902e7e4895a169ac4e01caa4c583b47387f78e8
SHA places pumped/places_held_equals 6eabb8e6d058583612152142fdfa80fc38f03029ded949821775990bb0d023f9
SHA places pumped/places_held_numerals 81870715e53f9a08dbd2dd8be64823a502713d7761cec8feff37d20c0c3f9b2b
SHA places pumped/places_train_equals a395a9dcf41d6ee0230fd0d71cfe3b6f741fbd239ec2a2aaf45d80409727bb29
SHA places pumped/places_train_numerals 95b456101f08c31c19ddb0141a9e499e03f9335b73a539bc7fc9a4c7aa6dc48f
```

```text
PRT (law modulated):
PROJECTION unmeasured (planned at 1 to 3 minutes); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
ROTOR_MENU loops=7204 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=4776 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=30
ROTOR_CLOSURE step=1 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=50
ROTOR_CLOSURE step=2 rows=5210 rank=40 minor_bits=17 torsion=3:2,11:2 carried=33 elapsed_ms=68
ROTOR_CLOSURE step=3 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=88
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=100
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=100
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=100
ROTOR_FOUNDED step=1 law=modulated carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2838840 sha256=26e73cc8cff47e33182d8b49f86ca5db46bda51a9333f7de03bc14c8c0fda128 elapsed_ms=151
RUN_RECEIPT exit=0 wall_s=0.2 peak_rss_kib=45844 user_s=0.1

PRS (law free):
PROJECTION unmeasured (planned at 1 to 3 minutes); DEADLINE 180 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
ROTOR_MENU loops=7204 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=4776 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=29
ROTOR_CLOSURE step=1 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=50
ROTOR_CLOSURE step=2 rows=5210 rank=40 minor_bits=17 torsion=3:2,11:2 carried=33 elapsed_ms=67
ROTOR_CLOSURE step=3 rows=5477 rank=40 minor_bits=15 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=87
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=99
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=99
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=99
ROTOR_FOUNDED step=1 law=free carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=0 levels_stepped=1 bytes=2838452 sha256=9165688d276300d8ce53c4ca473deaf8361e267a108e85f123957083e57a2639 elapsed_ms=157
RUN_RECEIPT exit=0 wall_s=0.2 peak_rss_kib=46448 user_s=0.1
```

## The development passes and the changed read

The first launch ran the three development passes together, and `PR` refused at once under the new
binary: the rotor's text had changed to rings `WIDTH:MODULUS` with their steps and turns, so the
rotor loop's `PR` state is in the superseded text. All three were relaunched together, `PR` on the
rotor loop's own binary (`e5f352c6…`), so its evaluation rate is read under the same three-way load.
The relaunch's `PRT` and `PRS` states equal the first launch's bit for bit, and `PR`'s state equals
the rotor loop's development state. The rate `d` is read as the largest window rate with partial
last windows included; with full windows only it is 120.5000, 119.2188 and 119.3125. `η` and `h`
take the larger of each run's two passes, which is the relaunch in every case.
```text
PRT (binary ef81eacd…):
TOWER_SECTION pass=0 section=32 bits_a_byte=3.742 deposits=32 halvings=14 elapsed_ms=3977
TOWER_SECTION pass=0 section=64 bits_a_byte=3.007 deposits=64 halvings=14 elapsed_ms=7636
TOWER_SECTION pass=0 section=96 bits_a_byte=2.656 deposits=96 halvings=14 elapsed_ms=11287
TOWER_SECTION pass=0 section=128 bits_a_byte=2.572 deposits=128 halvings=14 elapsed_ms=15143
TOWER_SECTION pass=0 section=155 bits_a_byte=2.496 deposits=155 halvings=14 elapsed_ms=18359
TOWER_STATE STATE.0 state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb
TOWER_PASS pass=0 train_bits_a_byte=2.907 dev_bits_a_byte=2.503 dev_regions Q=1.805 P=3.021 N=1.536 M=2.513 deposits=155/155 pass_ms=23657 elapsed_ms=23676 train_code=1270417675348 dev_code=1043744519153 grain_bits=20
TOWER_DONE state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb elapsed_ms=23750
RUN_RECEIPT exit=0 wall_s=23.8 peak_rss_kib=267468 user_s=141.1
PRS (binary ef81eacd…):
TOWER_SECTION pass=0 section=32 bits_a_byte=3.618 deposits=32 halvings=27 elapsed_ms=4490
TOWER_SECTION pass=0 section=64 bits_a_byte=2.988 deposits=64 halvings=27 elapsed_ms=8130
TOWER_SECTION pass=0 section=96 bits_a_byte=2.626 deposits=96 halvings=27 elapsed_ms=11784
TOWER_SECTION pass=0 section=128 bits_a_byte=2.562 deposits=128 halvings=27 elapsed_ms=15599
TOWER_SECTION pass=0 section=155 bits_a_byte=2.475 deposits=155 halvings=27 elapsed_ms=18979
TOWER_STATE STATE.0 state_bytes=12677525 state_sha256=4651199b746dc04bcaf8728eaea70466cd2d5c64231481171eb5000c367557ed
TOWER_PASS pass=0 train_bits_a_byte=2.865 dev_bits_a_byte=2.487 dev_regions Q=1.770 P=2.828 N=1.650 M=2.497 deposits=155/155 pass_ms=24452 elapsed_ms=24471 train_code=1252301055357 dev_code=1036790522371 grain_bits=20
TOWER_DONE state_bytes=12677525 state_sha256=4651199b746dc04bcaf8728eaea70466cd2d5c64231481171eb5000c367557ed elapsed_ms=24534
RUN_RECEIPT exit=0 wall_s=24.6 peak_rss_kib=266368 user_s=142.0
PR (binary e5f352c6…):
TOWER_SECTION pass=0 section=32 bits_a_byte=3.612 deposits=32 halvings=13 elapsed_ms=3976
TOWER_SECTION pass=0 section=64 bits_a_byte=2.984 deposits=64 halvings=13 elapsed_ms=7618
TOWER_SECTION pass=0 section=96 bits_a_byte=2.648 deposits=96 halvings=13 elapsed_ms=11244
TOWER_SECTION pass=0 section=128 bits_a_byte=2.568 deposits=128 halvings=13 elapsed_ms=15062
TOWER_SECTION pass=0 section=155 bits_a_byte=2.494 deposits=155 halvings=13 elapsed_ms=18301
TOWER_STATE STATE.0 state_bytes=12662664 state_sha256=df9e921759d940b83446b7126213bf844685e9391403a3fbd4b0e6ce8734b260
TOWER_PASS pass=0 train_bits_a_byte=2.872 dev_bits_a_byte=2.506 dev_regions Q=1.867 P=2.894 N=1.721 M=2.515 deposits=155/155 pass_ms=23610 elapsed_ms=23630 train_code=1255440915480 dev_code=1045061546126 grain_bits=20
TOWER_DONE state_bytes=12662664 state_sha256=df9e921759d940b83446b7126213bf844685e9391403a3fbd4b0e6ce8734b260 elapsed_ms=23703
RUN_RECEIPT exit=0 wall_s=23.8 peak_rss_kib=264924 user_s=139.7
```

The first launch, two together while `PR` refused:

```text
PRT: TOWER_PASS pass=0 train_bits_a_byte=2.907 dev_bits_a_byte=2.503 dev_regions Q=1.805 P=3.021 N=1.536 M=2.513 deposits=155/155 pass_ms=19979 elapsed_ms=19998 train_code=1270417675348 dev_code=1043744519153 grain_bits=20
PRT: RUN_RECEIPT exit=0 wall_s=20.2 peak_rss_kib=265024 user_s=124.0
PRS: TOWER_PASS pass=0 train_bits_a_byte=2.865 dev_bits_a_byte=2.487 dev_regions Q=1.770 P=2.828 N=1.650 M=2.497 deposits=155/155 pass_ms=20409 elapsed_ms=20429 train_code=1252301055357 dev_code=1036790522371 grain_bits=20
PRS: RUN_RECEIPT exit=0 wall_s=20.6 peak_rss_kib=267992 user_s=129.3
PR: alpha error: tower refused: a learner's text is its tower's lines and three of moments
PR: RUN_RECEIPT exit=1 wall_s=0.1 peak_rss_kib=20884 user_s=0.0
```

```text
NUMBER w_PR=119.3125 ms_an_evaluation from turns/dev_PR.log pass=0 section=128 ms=3818 evaluations=32 (over every full window of rotor/dev_PR.log, rotor/PR.log, turns/dev_PR.log; rotor/PR.log's largest is 106.0312)
NUMBER eta_PR=0.083871 from turns/dev_PR.log pass=0 halvings=13 sections=155 (over every pass of rotor/dev_PR.log, turns/dev_PR.log, rotor/PR.log)
NUMBER h_PR=5329 ms from turns/dev_PR.log pass=0 (over every pass of rotor/PR.log, turns/dev_PR.log)
NUMBER d_PRT=120.5000 from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32
NUMBER d_PRS=125.1852 from turns/dev_PRS.log pass=0 section=155 ms=3380 evaluations=27 sections=27 (partial)
NUMBER d_PR=119.9630 from turns/dev_PR.log pass=0 section=155 ms=3239 evaluations=27 sections=27 (partial)
(full windows only: d_PRT 120.5000, d_PRS 119.2188, d_PR 119.3125)
NUMBER w_PRT = w_PR x max(1, d_PRT/d_PR) = 119.3125 x max(1, 1.004477) = 119.8466 ms_an_evaluation
NUMBER eta_PRT=max(eta_PR 0.083871, own 0.090323 from turns/dev_PRT.log pass=0 halvings=14 sections=155)=0.090323
NUMBER h_PRT=max(h_PR 5329, own 5317 from turns/dev_PRT.log pass=0)=5329 ms
PROJECTION_PRT 3 x (1311 x 1.12 x 119.8466 x (1 + 0.090323) + 5329) + 1000 ms = 592.59 s; DEADLINE 593 s; bound 1.12 x 119.8466 = 134.2282 ms an evaluation
NUMBER w_PRS = w_PR x max(1, d_PRS/d_PR) = 119.3125 x max(1, 1.043532) = 124.5064 ms_an_evaluation
NUMBER eta_PRS=max(eta_PR 0.083871, own 0.174194 from turns/dev_PRS.log pass=0 halvings=27 sections=155)=0.174194
NUMBER h_PRS=max(h_PR 5329, own 5492 from turns/dev_PRS.log pass=0)=5492 ms
PROJECTION_PRS 3 x (1311 x 1.12 x 124.5064 x (1 + 0.174194) + 5492) + 1000 ms = 661.46 s; DEADLINE 662 s; bound 1.12 x 124.5064 = 139.4472 ms an evaluation
```

`w_PR` comes from the three-way pass at 119.31, above every two-way window of the rotor loop
(106.03), so the three-way load sets the bound.

## Training, the written reads and the rules
```text
PRT: TOWER_STATE STATE.0 state_bytes=12597083 state_sha256=385cf90b2f8d7732843df555eb4dbff6a4d82ee450497ed01347f64d1ed4f629
PRT: TOWER_PASS pass=0 train_bits_a_byte=2.183 dev_bits_a_byte=1.943 dev_regions Q=1.424 P=2.538 N=0.613 M=1.951 deposits=1311/1311 pass_ms=137595 elapsed_ms=137614 train_code=8072803488287 dev_code=810343006766 grain_bits=20
PRT: TOWER_STATE STATE.1 state_bytes=12547544 state_sha256=7782e43e362edbb73aacc7dd621eff1f72a69951ecfe216d09d8b1b01e155cb2
PRT: TOWER_PASS pass=1 train_bits_a_byte=1.840 dev_bits_a_byte=1.830 dev_regions Q=1.265 P=2.368 N=0.492 M=1.839 deposits=1311/1311 pass_ms=137374 elapsed_ms=274988 train_code=6807401654394 dev_code=763208465902 grain_bits=20
PRT: TOWER_STATE STATE.2 state_bytes=12533456 state_sha256=3fd266914f9e39a87aa125eea37a2da483f080c4a641f818130c756afef1ec80
PRT: TOWER_PASS pass=2 train_bits_a_byte=1.744 dev_bits_a_byte=1.765 dev_regions Q=1.197 P=2.287 N=0.478 M=1.774 deposits=1311/1311 pass_ms=139573 elapsed_ms=414562 train_code=6451651811100 dev_code=736124065026 grain_bits=20
PRT: TOWER_DONE state_bytes=12533456 state_sha256=3fd266914f9e39a87aa125eea37a2da483f080c4a641f818130c756afef1ec80 elapsed_ms=414631
PRT: RUN_RECEIPT exit=0 wall_s=415.0 peak_rss_kib=300824 user_s=2506.0
PRS: TOWER_STATE STATE.0 state_bytes=12569567 state_sha256=80c710bbdffa40f7baa04f1ccecf247a90f9cba8124c5b639b4ddc1af2af5e9b
PRS: TOWER_PASS pass=0 train_bits_a_byte=2.163 dev_bits_a_byte=1.937 dev_regions Q=1.474 P=2.523 N=0.671 M=1.944 deposits=1311/1311 pass_ms=138179 elapsed_ms=138197 train_code=7998996492686 dev_code=807727508734 grain_bits=20
PRS: TOWER_STATE STATE.1 state_bytes=12527219 state_sha256=fea5027180d43403559a4e2637971653fc024c1f91c22288210fa0f3a3c53a6f
PRS: TOWER_PASS pass=1 train_bits_a_byte=1.835 dev_bits_a_byte=1.829 dev_regions Q=1.295 P=2.386 N=0.528 M=1.837 deposits=1311/1311 pass_ms=138078 elapsed_ms=276276 train_code=6787801547150 dev_code=762761628124 grain_bits=20
PRS: TOWER_STATE STATE.2 state_bytes=12535854 state_sha256=aa82c3308de31cf55fa2a21525ead45d17d4bb9a8ce891eb8bf01e270a9b5330
PRS: TOWER_PASS pass=2 train_bits_a_byte=1.747 dev_bits_a_byte=1.772 dev_regions Q=1.221 P=2.340 N=0.478 M=1.780 deposits=1311/1311 pass_ms=139963 elapsed_ms=416239 train_code=6463317753309 dev_code=738966908779 grain_bits=20
PRS: TOWER_DONE state_bytes=12535854 state_sha256=aa82c3308de31cf55fa2a21525ead45d17d4bb9a8ce891eb8bf01e270a9b5330 elapsed_ms=416302
PRS: RUN_RECEIPT exit=0 wall_s=416.7 peak_rss_kib=293036 user_s=2511.0
Windows read (turns/windows.py): PRT w=113.8750 (pass 2 section 448); eta 12/1311=0.009153, 0, 0; h 4616, 4573, 4533 ms. PRS w=116.1875 (pass 2 section 928); eta 21/1311=0.016018, 0, 5/1311=0.003814; h 4580, 4542, 4268 ms.
```

```text
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299733 prompt_units=468588 released_units=117988 most_units_a_problem=4692 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17766
TOWER_WRITTEN_FILES free_sha256=965ac51d372fbc351a8e066e24ef9fa55ca4d598088171d652bfcc450632131e marks_sha256=7d01046d7651786772e1c8ecdc232e32e3d385317b80b7511d6b5742364772c2
RUN_RECEIPT exit=0 wall_s=17.8 peak_rss_kib=41184 user_s=138.7
READ_GUARD ok progress 64 by 1705 ms
PROJECTION progress problems=64 by 3,300 ms; DEADLINE 30 s; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299800 prompt_units=468588 released_units=115382 most_units_a_problem=4697 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17613
TOWER_WRITTEN_FILES free_sha256=5378f7bc74b40e99a4ac9ddc02f76d2f69df3c161673e188c75cad8ab2cde99d marks_sha256=dcadcfe9f7691b580a8a943562f1605dc7dddda5656f50ad7d32758a16cb7c48
RUN_RECEIPT exit=0 wall_s=17.6 peak_rss_kib=42348 user_s=137.6
READ_GUARD ok progress 64 by 1655 ms
```

```text
RULES rings digit/read_C rotor/read_PP rotor/read_PR turns/read_PRT turns/read_PRS; DEADLINE 60 s
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
RUN_RECEIPT exit=0 wall_s=10.5 peak_rss_kib=60192 user_s=10.4
RULES heard rotor/read_PR turns/read_PRT turns/read_PRS; DEADLINE 60 s
WRITTEN dir=rotor/read_PR (as above)
HEARD dir=rotor/read_PR 0=18/876 1=9/239 2-3=19/224 4-7=13/255 8-15=39/326 16+=179/528
WRITTEN dir=turns/read_PRT (as above)
HEARD dir=turns/read_PRT 0=24/876 1=8/239 2-3=16/224 4-7=9/255 8-15=42/326 16+=141/528
WRITTEN dir=turns/read_PRS (as above)
HEARD dir=turns/read_PRS 0=19/876 1=12/239 2-3=20/224 4-7=15/255 8-15=47/326 16+=175/528
RUN_RECEIPT exit=0 wall_s=6.3 peak_rss_kib=60976 user_s=6.3
RULES pair turns/read_PRT turns/read_PRS; DEADLINE 60 s
PAIRED met_only_a=80 met_only_b=133 met_both=136 never_only_a=18 never_only_b=13 never_both=6
RUN_RECEIPT exit=0 wall_s=4.3 peak_rss_kib=60956 user_s=4.2
RULES pair turns/read_PRT rotor/read_PR; DEADLINE 60 s
PAIRED met_only_a=102 met_only_b=145 met_both=114 never_only_a=19 never_only_b=13 never_both=5
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=60412 user_s=4.2
RULES pair turns/read_PRT digit/read_C; DEADLINE 60 s
PAIRED met_only_a=118 met_only_b=78 met_both=98 never_only_a=21 never_only_b=11 never_both=3
RUN_RECEIPT exit=0 wall_s=4.3 peak_rss_kib=60524 user_s=4.3
RULES pair turns/read_PRS rotor/read_PR; DEADLINE 60 s
PAIRED met_only_a=116 met_only_b=106 met_both=153 never_only_a=12 never_only_b=11 never_both=7
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=61956 user_s=4.2
(In each pair file the WRITTEN lines repeat the rings file's lines exactly; I wrote "as above" in their place. Files: RUN/turns/rules_1..6.log.)
```

In each pair file the `WRITTEN` lines repeat the rings file's lines exactly; they are written
"(as above)" in their place.

## Time and memory

The wall is the `wait4` receipt's; the ratio is wall over projection.

| run | projection | deadline | wall | ratio | peak RSS KiB |
|---|---|---|---|---|---|
| build | 124 s | 180 s | 121.3 s | 0.978 | 3570724 |
| found PRT | unmeasured, planned 1-3 min | 180 s | 0.2 s | - | 45844 |
| found PRS | unmeasured, planned 1-3 min | 180 s | 0.2 s | - | 46448 |
| dev PRT, first (two-way) | unmeasured (rotor/'s PR 20.2 s) | 180 s | 20.2 s | 1.00 vs 20.2 | 265024 |
| dev PRS, first (two-way) | same | 180 s | 20.6 s | 1.02 vs 20.2 | 267992 |
| dev PR, first (refused) | same | 180 s | 0.1 s | - | 20884 |
| dev PRT (three-way) | same | 180 s | 23.8 s | 1.18 vs 20.2 | 267468 |
| dev PRS (three-way) | same | 180 s | 24.6 s | 1.22 vs 20.2 | 266368 |
| dev PR (three-way, rotor binary) | same | 180 s | 23.8 s | 1.18 vs 20.2 | 264924 |
| train PRT | 592.59 s | 593 s | 415.0 s | 0.700 | 300824 |
| train PRS | 661.46 s | 662 s | 416.7 s | 0.630 | 293036 |
| read PRT | progress 64 by 3.3 s (met at 1.705 s) | 30 s | 17.8 s | - | 41184 |
| read PRS | progress 64 by 3.3 s (met at 1.655 s) | 30 s | 17.6 s | - | 42348 |
| rules rings / heard / pair PRT PRS / pair PRT PR / pair PRT C / pair PRS PR | - | 60 s each | 10.5 / 6.3 / 4.3 / 4.2 / 4.3 / 4.2 s | - | 60192 / 60976 / 60956 / 60412 / 60524 / 61956 |
| at PRT train/held numerals | rotor/'s largest 8.5 s | 30 s | 7.0 / 2.7 s | 0.82 / 0.32 | 79228 / 40228 |
| at PRT train/held equals | 8.5 s | 30 s | 8.4 / 3.4 s | 0.99 / 0.40 | 38196 / 38244 |
| at PRS train/held numerals | 8.5 s | 30 s | 7.0 / 2.8 s | 0.82 / 0.33 | 78676 / 41120 |
| at PRS train/held equals | 8.5 s | 30 s | 8.4 / 3.6 s | 0.99 / 0.42 | 38952 / 38672 |
| probe PRT numerals / equals | - | 300 s | 13.9 / 8.1 s | - | 325860 / 80180 |
| probe PRS numerals / equals | - | 300 s | 14.1 / 8.1 s | - | 325204 / 79948 |

## Every guard line of the two trainings

The guard is the rotor loop's guard unchanged, with bounds `PRT` 134.2282 and `PRS` 139.4472 ms an
evaluation. No window passed its limit and nothing was stopped.
```text
PRT: TOWER_SECTION pass=0 section=32 bits_a_byte=3.644 deposits=32 halvings=12 elapsed_ms=3441 | window sections=32 halvings=12 evaluations=44 ms=3441 ms_an_evaluation=78.20 limit=5906.0
PRS: TOWER_SECTION pass=0 section=32 bits_a_byte=3.605 deposits=32 halvings=21 elapsed_ms=3778 | window sections=32 halvings=21 evaluations=53 ms=3778 ms_an_evaluation=71.28 limit=7390.7
PRT: TOWER_SECTION pass=0 section=64 bits_a_byte=3.010 deposits=64 halvings=12 elapsed_ms=6609 | window sections=32 halvings=0 evaluations=32 ms=3168 ms_an_evaluation=99.00 limit=4295.3
PRS: TOWER_SECTION pass=0 section=64 bits_a_byte=2.951 deposits=64 halvings=21 elapsed_ms=6953 | window sections=32 halvings=0 evaluations=32 ms=3175 ms_an_evaluation=99.22 limit=4462.3
PRT: TOWER_SECTION pass=0 section=96 bits_a_byte=2.752 deposits=96 halvings=12 elapsed_ms=9816 | window sections=32 halvings=0 evaluations=32 ms=3207 ms_an_evaluation=100.22 limit=4295.3
PRS: TOWER_SECTION pass=0 section=96 bits_a_byte=2.705 deposits=96 halvings=21 elapsed_ms=10153 | window sections=32 halvings=0 evaluations=32 ms=3200 ms_an_evaluation=100.00 limit=4462.3
PRT: TOWER_SECTION pass=0 section=128 bits_a_byte=2.585 deposits=128 halvings=12 elapsed_ms=12993 | window sections=32 halvings=0 evaluations=32 ms=3177 ms_an_evaluation=99.28 limit=4295.3
PRS: TOWER_SECTION pass=0 section=128 bits_a_byte=2.545 deposits=128 halvings=21 elapsed_ms=13325 | window sections=32 halvings=0 evaluations=32 ms=3172 ms_an_evaluation=99.12 limit=4462.3
PRT: TOWER_SECTION pass=0 section=160 bits_a_byte=2.514 deposits=160 halvings=12 elapsed_ms=16166 | window sections=32 halvings=0 evaluations=32 ms=3173 ms_an_evaluation=99.16 limit=4295.3
PRS: TOWER_SECTION pass=0 section=160 bits_a_byte=2.485 deposits=160 halvings=21 elapsed_ms=16522 | window sections=32 halvings=0 evaluations=32 ms=3197 ms_an_evaluation=99.91 limit=4462.3
PRT: TOWER_SECTION pass=0 section=192 bits_a_byte=2.401 deposits=192 halvings=12 elapsed_ms=19394 | window sections=32 halvings=0 evaluations=32 ms=3228 ms_an_evaluation=100.88 limit=4295.3
PRS: TOWER_SECTION pass=0 section=192 bits_a_byte=2.374 deposits=192 halvings=21 elapsed_ms=19802 | window sections=32 halvings=0 evaluations=32 ms=3280 ms_an_evaluation=102.50 limit=4462.3
PRT: TOWER_SECTION pass=0 section=224 bits_a_byte=2.325 deposits=224 halvings=12 elapsed_ms=22638 | window sections=32 halvings=0 evaluations=32 ms=3244 ms_an_evaluation=101.38 limit=4295.3
PRS: TOWER_SECTION pass=0 section=224 bits_a_byte=2.291 deposits=224 halvings=21 elapsed_ms=23087 | window sections=32 halvings=0 evaluations=32 ms=3285 ms_an_evaluation=102.66 limit=4462.3
PRT: TOWER_SECTION pass=0 section=256 bits_a_byte=2.374 deposits=256 halvings=12 elapsed_ms=25838 | window sections=32 halvings=0 evaluations=32 ms=3200 ms_an_evaluation=100.00 limit=4295.3
PRS: TOWER_SECTION pass=0 section=256 bits_a_byte=2.343 deposits=256 halvings=21 elapsed_ms=26284 | window sections=32 halvings=0 evaluations=32 ms=3197 ms_an_evaluation=99.91 limit=4462.3
PRT: TOWER_SECTION pass=0 section=288 bits_a_byte=2.292 deposits=288 halvings=12 elapsed_ms=29030 | window sections=32 halvings=0 evaluations=32 ms=3192 ms_an_evaluation=99.75 limit=4295.3
PRS: TOWER_SECTION pass=0 section=288 bits_a_byte=2.274 deposits=288 halvings=21 elapsed_ms=29483 | window sections=32 halvings=0 evaluations=32 ms=3199 ms_an_evaluation=99.97 limit=4462.3
PRT: TOWER_SECTION pass=0 section=320 bits_a_byte=2.237 deposits=320 halvings=12 elapsed_ms=32265 | window sections=32 halvings=0 evaluations=32 ms=3235 ms_an_evaluation=101.09 limit=4295.3
PRS: TOWER_SECTION pass=0 section=320 bits_a_byte=2.219 deposits=320 halvings=21 elapsed_ms=32797 | window sections=32 halvings=0 evaluations=32 ms=3314 ms_an_evaluation=103.56 limit=4462.3
PRT: TOWER_SECTION pass=0 section=352 bits_a_byte=2.258 deposits=352 halvings=12 elapsed_ms=35474 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=4295.3
PRS: TOWER_SECTION pass=0 section=352 bits_a_byte=2.232 deposits=352 halvings=21 elapsed_ms=35990 | window sections=32 halvings=0 evaluations=32 ms=3193 ms_an_evaluation=99.78 limit=4462.3
PRT: TOWER_SECTION pass=0 section=384 bits_a_byte=2.243 deposits=384 halvings=12 elapsed_ms=38717 | window sections=32 halvings=0 evaluations=32 ms=3243 ms_an_evaluation=101.34 limit=4295.3
PRS: TOWER_SECTION pass=0 section=384 bits_a_byte=2.221 deposits=384 halvings=21 elapsed_ms=39218 | window sections=32 halvings=0 evaluations=32 ms=3228 ms_an_evaluation=100.88 limit=4462.3
PRT: TOWER_SECTION pass=0 section=416 bits_a_byte=2.199 deposits=416 halvings=12 elapsed_ms=42033 | window sections=32 halvings=0 evaluations=32 ms=3316 ms_an_evaluation=103.62 limit=4295.3
PRS: TOWER_SECTION pass=0 section=416 bits_a_byte=2.178 deposits=416 halvings=21 elapsed_ms=42538 | window sections=32 halvings=0 evaluations=32 ms=3320 ms_an_evaluation=103.75 limit=4462.3
PRT: TOWER_SECTION pass=0 section=448 bits_a_byte=2.187 deposits=448 halvings=12 elapsed_ms=45293 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4295.3
PRS: TOWER_SECTION pass=0 section=448 bits_a_byte=2.159 deposits=448 halvings=21 elapsed_ms=45806 | window sections=32 halvings=0 evaluations=32 ms=3268 ms_an_evaluation=102.12 limit=4462.3
PRT: TOWER_SECTION pass=0 section=480 bits_a_byte=2.163 deposits=480 halvings=12 elapsed_ms=48553 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4295.3
PRS: TOWER_SECTION pass=0 section=480 bits_a_byte=2.138 deposits=480 halvings=21 elapsed_ms=49060 | window sections=32 halvings=0 evaluations=32 ms=3254 ms_an_evaluation=101.69 limit=4462.3
PRT: TOWER_SECTION pass=0 section=512 bits_a_byte=2.136 deposits=512 halvings=12 elapsed_ms=51775 | window sections=32 halvings=0 evaluations=32 ms=3222 ms_an_evaluation=100.69 limit=4295.3
PRS: TOWER_SECTION pass=0 section=512 bits_a_byte=2.118 deposits=512 halvings=21 elapsed_ms=52295 | window sections=32 halvings=0 evaluations=32 ms=3235 ms_an_evaluation=101.09 limit=4462.3
PRT: TOWER_SECTION pass=0 section=544 bits_a_byte=2.090 deposits=544 halvings=12 elapsed_ms=55065 | window sections=32 halvings=0 evaluations=32 ms=3290 ms_an_evaluation=102.81 limit=4295.3
PRS: TOWER_SECTION pass=0 section=544 bits_a_byte=2.068 deposits=544 halvings=21 elapsed_ms=55574 | window sections=32 halvings=0 evaluations=32 ms=3279 ms_an_evaluation=102.47 limit=4462.3
PRT: TOWER_SECTION pass=0 section=576 bits_a_byte=2.137 deposits=576 halvings=12 elapsed_ms=58325 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4295.3
PRS: TOWER_SECTION pass=0 section=576 bits_a_byte=2.118 deposits=576 halvings=21 elapsed_ms=58846 | window sections=32 halvings=0 evaluations=32 ms=3272 ms_an_evaluation=102.25 limit=4462.3
PRT: TOWER_SECTION pass=0 section=608 bits_a_byte=2.089 deposits=608 halvings=12 elapsed_ms=61559 | window sections=32 halvings=0 evaluations=32 ms=3234 ms_an_evaluation=101.06 limit=4295.3
PRS: TOWER_SECTION pass=0 section=608 bits_a_byte=2.070 deposits=608 halvings=21 elapsed_ms=62113 | window sections=32 halvings=0 evaluations=32 ms=3267 ms_an_evaluation=102.09 limit=4462.3
PRT: TOWER_SECTION pass=0 section=640 bits_a_byte=2.064 deposits=640 halvings=12 elapsed_ms=64792 | window sections=32 halvings=0 evaluations=32 ms=3233 ms_an_evaluation=101.03 limit=4295.3
PRS: TOWER_SECTION pass=0 section=640 bits_a_byte=2.044 deposits=640 halvings=21 elapsed_ms=65347 | window sections=32 halvings=0 evaluations=32 ms=3234 ms_an_evaluation=101.06 limit=4462.3
PRT: TOWER_SECTION pass=0 section=672 bits_a_byte=2.072 deposits=672 halvings=12 elapsed_ms=67990 | window sections=32 halvings=0 evaluations=32 ms=3198 ms_an_evaluation=99.94 limit=4295.3
PRS: TOWER_SECTION pass=0 section=672 bits_a_byte=2.053 deposits=672 halvings=21 elapsed_ms=68546 | window sections=32 halvings=0 evaluations=32 ms=3199 ms_an_evaluation=99.97 limit=4462.3
PRT: TOWER_SECTION pass=0 section=704 bits_a_byte=2.058 deposits=704 halvings=12 elapsed_ms=71202 | window sections=32 halvings=0 evaluations=32 ms=3212 ms_an_evaluation=100.38 limit=4295.3
PRS: TOWER_SECTION pass=0 section=704 bits_a_byte=2.046 deposits=704 halvings=21 elapsed_ms=71753 | window sections=32 halvings=0 evaluations=32 ms=3207 ms_an_evaluation=100.22 limit=4462.3
PRT: TOWER_SECTION pass=0 section=736 bits_a_byte=2.045 deposits=736 halvings=12 elapsed_ms=74410 | window sections=32 halvings=0 evaluations=32 ms=3208 ms_an_evaluation=100.25 limit=4295.3
PRS: TOWER_SECTION pass=0 section=736 bits_a_byte=2.035 deposits=736 halvings=21 elapsed_ms=74959 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=4462.3
PRT: TOWER_SECTION pass=0 section=768 bits_a_byte=2.030 deposits=768 halvings=12 elapsed_ms=77752 | window sections=32 halvings=0 evaluations=32 ms=3342 ms_an_evaluation=104.44 limit=4295.3
PRS: TOWER_SECTION pass=0 section=768 bits_a_byte=2.018 deposits=768 halvings=21 elapsed_ms=78314 | window sections=32 halvings=0 evaluations=32 ms=3355 ms_an_evaluation=104.84 limit=4462.3
PRT: TOWER_SECTION pass=0 section=800 bits_a_byte=2.003 deposits=800 halvings=12 elapsed_ms=81196 | window sections=32 halvings=0 evaluations=32 ms=3444 ms_an_evaluation=107.62 limit=4295.3
PRS: TOWER_SECTION pass=0 section=800 bits_a_byte=1.999 deposits=800 halvings=21 elapsed_ms=81694 | window sections=32 halvings=0 evaluations=32 ms=3380 ms_an_evaluation=105.62 limit=4462.3
PRT: TOWER_SECTION pass=0 section=832 bits_a_byte=2.010 deposits=832 halvings=12 elapsed_ms=84539 | window sections=32 halvings=0 evaluations=32 ms=3343 ms_an_evaluation=104.47 limit=4295.3
PRS: TOWER_SECTION pass=0 section=832 bits_a_byte=2.004 deposits=832 halvings=21 elapsed_ms=84991 | window sections=32 halvings=0 evaluations=32 ms=3297 ms_an_evaluation=103.03 limit=4462.3
PRT: TOWER_SECTION pass=0 section=864 bits_a_byte=2.019 deposits=864 halvings=12 elapsed_ms=87749 | window sections=32 halvings=0 evaluations=32 ms=3210 ms_an_evaluation=100.31 limit=4295.3
PRS: TOWER_SECTION pass=0 section=864 bits_a_byte=2.002 deposits=864 halvings=21 elapsed_ms=88208 | window sections=32 halvings=0 evaluations=32 ms=3217 ms_an_evaluation=100.53 limit=4462.3
PRT: TOWER_SECTION pass=0 section=896 bits_a_byte=2.007 deposits=896 halvings=12 elapsed_ms=90972 | window sections=32 halvings=0 evaluations=32 ms=3223 ms_an_evaluation=100.72 limit=4295.3
PRS: TOWER_SECTION pass=0 section=896 bits_a_byte=1.989 deposits=896 halvings=21 elapsed_ms=91422 | window sections=32 halvings=0 evaluations=32 ms=3214 ms_an_evaluation=100.44 limit=4462.3
PRT: TOWER_SECTION pass=0 section=928 bits_a_byte=2.027 deposits=928 halvings=12 elapsed_ms=94202 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=4295.3
PRS: TOWER_SECTION pass=0 section=928 bits_a_byte=2.012 deposits=928 halvings=21 elapsed_ms=94638 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=4462.3
PRT: TOWER_SECTION pass=0 section=960 bits_a_byte=1.996 deposits=960 halvings=12 elapsed_ms=97453 | window sections=32 halvings=0 evaluations=32 ms=3251 ms_an_evaluation=101.59 limit=4295.3
PRS: TOWER_SECTION pass=0 section=960 bits_a_byte=1.983 deposits=960 halvings=21 elapsed_ms=97874 | window sections=32 halvings=0 evaluations=32 ms=3236 ms_an_evaluation=101.12 limit=4462.3
PRT: TOWER_SECTION pass=0 section=992 bits_a_byte=1.999 deposits=992 halvings=12 elapsed_ms=100679 | window sections=32 halvings=0 evaluations=32 ms=3226 ms_an_evaluation=100.81 limit=4295.3
PRS: TOWER_SECTION pass=0 section=992 bits_a_byte=1.984 deposits=992 halvings=21 elapsed_ms=101115 | window sections=32 halvings=0 evaluations=32 ms=3241 ms_an_evaluation=101.28 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1024 bits_a_byte=1.946 deposits=1024 halvings=12 elapsed_ms=103937 | window sections=32 halvings=0 evaluations=32 ms=3258 ms_an_evaluation=101.81 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1024 bits_a_byte=1.934 deposits=1024 halvings=21 elapsed_ms=104385 | window sections=32 halvings=0 evaluations=32 ms=3270 ms_an_evaluation=102.19 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1056 bits_a_byte=1.963 deposits=1056 halvings=12 elapsed_ms=107167 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1056 bits_a_byte=1.950 deposits=1056 halvings=21 elapsed_ms=107617 | window sections=32 halvings=0 evaluations=32 ms=3232 ms_an_evaluation=101.00 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1088 bits_a_byte=1.994 deposits=1088 halvings=12 elapsed_ms=110406 | window sections=32 halvings=0 evaluations=32 ms=3239 ms_an_evaluation=101.22 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1088 bits_a_byte=1.981 deposits=1088 halvings=21 elapsed_ms=110858 | window sections=32 halvings=0 evaluations=32 ms=3241 ms_an_evaluation=101.28 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1120 bits_a_byte=1.967 deposits=1120 halvings=12 elapsed_ms=113630 | window sections=32 halvings=0 evaluations=32 ms=3224 ms_an_evaluation=100.75 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1120 bits_a_byte=1.960 deposits=1120 halvings=21 elapsed_ms=114123 | window sections=32 halvings=0 evaluations=32 ms=3265 ms_an_evaluation=102.03 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1152 bits_a_byte=1.974 deposits=1152 halvings=12 elapsed_ms=116839 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1152 bits_a_byte=1.962 deposits=1152 halvings=21 elapsed_ms=117395 | window sections=32 halvings=0 evaluations=32 ms=3272 ms_an_evaluation=102.25 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1184 bits_a_byte=1.924 deposits=1184 halvings=12 elapsed_ms=120055 | window sections=32 halvings=0 evaluations=32 ms=3216 ms_an_evaluation=100.50 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1184 bits_a_byte=1.913 deposits=1184 halvings=21 elapsed_ms=120670 | window sections=32 halvings=0 evaluations=32 ms=3275 ms_an_evaluation=102.34 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1216 bits_a_byte=1.960 deposits=1216 halvings=12 elapsed_ms=123305 | window sections=32 halvings=0 evaluations=32 ms=3250 ms_an_evaluation=101.56 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1216 bits_a_byte=1.947 deposits=1216 halvings=21 elapsed_ms=123928 | window sections=32 halvings=0 evaluations=32 ms=3258 ms_an_evaluation=101.81 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1248 bits_a_byte=1.925 deposits=1248 halvings=12 elapsed_ms=126609 | window sections=32 halvings=0 evaluations=32 ms=3304 ms_an_evaluation=103.25 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1248 bits_a_byte=1.913 deposits=1248 halvings=21 elapsed_ms=127227 | window sections=32 halvings=0 evaluations=32 ms=3299 ms_an_evaluation=103.09 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1280 bits_a_byte=1.942 deposits=1280 halvings=12 elapsed_ms=129834 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=4295.3
PRS: TOWER_SECTION pass=0 section=1280 bits_a_byte=1.932 deposits=1280 halvings=21 elapsed_ms=130453 | window sections=32 halvings=0 evaluations=32 ms=3226 ms_an_evaluation=100.81 limit=4462.3
PRT: TOWER_SECTION pass=0 section=1311 bits_a_byte=1.912 deposits=1311 halvings=12 elapsed_ms=132998 | window sections=31 halvings=0 evaluations=31 ms=3164 ms_an_evaluation=102.06 limit=4161.1
PRT: TOWER_STATE STATE.0 state_bytes=12597083 state_sha256=385cf90b2f8d7732843df555eb4dbff6a4d82ee450497ed01347f64d1ed4f629
PRS: TOWER_SECTION pass=0 section=1311 bits_a_byte=1.904 deposits=1311 halvings=21 elapsed_ms=133617 | window sections=31 halvings=0 evaluations=31 ms=3164 ms_an_evaluation=102.06 limit=4322.9
PRS: TOWER_STATE STATE.0 state_bytes=12569567 state_sha256=80c710bbdffa40f7baa04f1ccecf247a90f9cba8124c5b639b4ddc1af2af5e9b
PRT: TOWER_PASS pass=0 train_bits_a_byte=2.183 dev_bits_a_byte=1.943 dev_regions Q=1.424 P=2.538 N=0.613 M=1.951 deposits=1311/1311 pass_ms=137595 elapsed_ms=137614 train_code=8072803488287 dev_code=810343006766 grain_bits=20
PRS: TOWER_PASS pass=0 train_bits_a_byte=2.163 dev_bits_a_byte=1.937 dev_regions Q=1.474 P=2.523 N=0.671 M=1.944 deposits=1311/1311 pass_ms=138179 elapsed_ms=138197 train_code=7998996492686 dev_code=807727508734 grain_bits=20
PRT: TOWER_SECTION pass=1 section=32 bits_a_byte=1.906 deposits=32 halvings=0 elapsed_ms=140772 | window sections=32 halvings=0 evaluations=32 ms=3158 ms_an_evaluation=98.69 limit=4295.3
PRS: TOWER_SECTION pass=1 section=32 bits_a_byte=1.899 deposits=32 halvings=0 elapsed_ms=141418 | window sections=32 halvings=0 evaluations=32 ms=3221 ms_an_evaluation=100.66 limit=4462.3
PRT: TOWER_SECTION pass=1 section=64 bits_a_byte=1.903 deposits=64 halvings=0 elapsed_ms=144004 | window sections=32 halvings=0 evaluations=32 ms=3232 ms_an_evaluation=101.00 limit=4295.3
PRS: TOWER_SECTION pass=1 section=64 bits_a_byte=1.893 deposits=64 halvings=0 elapsed_ms=144663 | window sections=32 halvings=0 evaluations=32 ms=3245 ms_an_evaluation=101.41 limit=4462.3
PRT: TOWER_SECTION pass=1 section=96 bits_a_byte=1.926 deposits=96 halvings=0 elapsed_ms=147240 | window sections=32 halvings=0 evaluations=32 ms=3236 ms_an_evaluation=101.12 limit=4295.3
PRS: TOWER_SECTION pass=1 section=96 bits_a_byte=1.915 deposits=96 halvings=0 elapsed_ms=147959 | window sections=32 halvings=0 evaluations=32 ms=3296 ms_an_evaluation=103.00 limit=4462.3
PRT: TOWER_SECTION pass=1 section=128 bits_a_byte=1.893 deposits=128 halvings=0 elapsed_ms=150481 | window sections=32 halvings=0 evaluations=32 ms=3241 ms_an_evaluation=101.28 limit=4295.3
PRS: TOWER_SECTION pass=1 section=128 bits_a_byte=1.884 deposits=128 halvings=0 elapsed_ms=151226 | window sections=32 halvings=0 evaluations=32 ms=3267 ms_an_evaluation=102.09 limit=4462.3
PRT: TOWER_SECTION pass=1 section=160 bits_a_byte=1.916 deposits=160 halvings=0 elapsed_ms=153692 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=4295.3
PRS: TOWER_SECTION pass=1 section=160 bits_a_byte=1.901 deposits=160 halvings=0 elapsed_ms=154458 | window sections=32 halvings=0 evaluations=32 ms=3232 ms_an_evaluation=101.00 limit=4462.3
PRT: TOWER_SECTION pass=1 section=192 bits_a_byte=1.879 deposits=192 halvings=0 elapsed_ms=156926 | window sections=32 halvings=0 evaluations=32 ms=3234 ms_an_evaluation=101.06 limit=4295.3
PRS: TOWER_SECTION pass=1 section=192 bits_a_byte=1.872 deposits=192 halvings=0 elapsed_ms=157678 | window sections=32 halvings=0 evaluations=32 ms=3220 ms_an_evaluation=100.62 limit=4462.3
PRT: TOWER_SECTION pass=1 section=224 bits_a_byte=1.825 deposits=224 halvings=0 elapsed_ms=160171 | window sections=32 halvings=0 evaluations=32 ms=3245 ms_an_evaluation=101.41 limit=4295.3
PRS: TOWER_SECTION pass=1 section=224 bits_a_byte=1.817 deposits=224 halvings=0 elapsed_ms=160908 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=4462.3
PRT: TOWER_SECTION pass=1 section=256 bits_a_byte=1.927 deposits=256 halvings=0 elapsed_ms=163423 | window sections=32 halvings=0 evaluations=32 ms=3252 ms_an_evaluation=101.62 limit=4295.3
PRS: TOWER_SECTION pass=1 section=256 bits_a_byte=1.918 deposits=256 halvings=0 elapsed_ms=164164 | window sections=32 halvings=0 evaluations=32 ms=3256 ms_an_evaluation=101.75 limit=4462.3
PRT: TOWER_SECTION pass=1 section=288 bits_a_byte=1.883 deposits=288 halvings=0 elapsed_ms=166673 | window sections=32 halvings=0 evaluations=32 ms=3250 ms_an_evaluation=101.56 limit=4295.3
PRS: TOWER_SECTION pass=1 section=288 bits_a_byte=1.878 deposits=288 halvings=0 elapsed_ms=167442 | window sections=32 halvings=0 evaluations=32 ms=3278 ms_an_evaluation=102.44 limit=4462.3
PRT: TOWER_SECTION pass=1 section=320 bits_a_byte=1.845 deposits=320 halvings=0 elapsed_ms=169937 | window sections=32 halvings=0 evaluations=32 ms=3264 ms_an_evaluation=102.00 limit=4295.3
PRS: TOWER_SECTION pass=1 section=320 bits_a_byte=1.848 deposits=320 halvings=0 elapsed_ms=170703 | window sections=32 halvings=0 evaluations=32 ms=3261 ms_an_evaluation=101.91 limit=4462.3
PRT: TOWER_SECTION pass=1 section=352 bits_a_byte=1.884 deposits=352 halvings=0 elapsed_ms=173188 | window sections=32 halvings=0 evaluations=32 ms=3251 ms_an_evaluation=101.59 limit=4295.3
PRS: TOWER_SECTION pass=1 section=352 bits_a_byte=1.878 deposits=352 halvings=0 elapsed_ms=173964 | window sections=32 halvings=0 evaluations=32 ms=3261 ms_an_evaluation=101.91 limit=4462.3
PRT: TOWER_SECTION pass=1 section=384 bits_a_byte=1.886 deposits=384 halvings=0 elapsed_ms=176413 | window sections=32 halvings=0 evaluations=32 ms=3225 ms_an_evaluation=100.78 limit=4295.3
PRS: TOWER_SECTION pass=1 section=384 bits_a_byte=1.881 deposits=384 halvings=0 elapsed_ms=177254 | window sections=32 halvings=0 evaluations=32 ms=3290 ms_an_evaluation=102.81 limit=4462.3
PRT: TOWER_SECTION pass=1 section=416 bits_a_byte=1.864 deposits=416 halvings=0 elapsed_ms=179613 | window sections=32 halvings=0 evaluations=32 ms=3200 ms_an_evaluation=100.00 limit=4295.3
PRS: TOWER_SECTION pass=1 section=416 bits_a_byte=1.859 deposits=416 halvings=0 elapsed_ms=180465 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=4462.3
PRT: TOWER_SECTION pass=1 section=448 bits_a_byte=1.875 deposits=448 halvings=0 elapsed_ms=182839 | window sections=32 halvings=0 evaluations=32 ms=3226 ms_an_evaluation=100.81 limit=4295.3
PRS: TOWER_SECTION pass=1 section=448 bits_a_byte=1.858 deposits=448 halvings=0 elapsed_ms=183711 | window sections=32 halvings=0 evaluations=32 ms=3246 ms_an_evaluation=101.44 limit=4462.3
PRT: TOWER_SECTION pass=1 section=480 bits_a_byte=1.858 deposits=480 halvings=0 elapsed_ms=186143 | window sections=32 halvings=0 evaluations=32 ms=3304 ms_an_evaluation=103.25 limit=4295.3
PRS: TOWER_SECTION pass=1 section=480 bits_a_byte=1.858 deposits=480 halvings=0 elapsed_ms=186965 | window sections=32 halvings=0 evaluations=32 ms=3254 ms_an_evaluation=101.69 limit=4462.3
PRT: TOWER_SECTION pass=1 section=512 bits_a_byte=1.854 deposits=512 halvings=0 elapsed_ms=189430 | window sections=32 halvings=0 evaluations=32 ms=3287 ms_an_evaluation=102.72 limit=4295.3
PRS: TOWER_SECTION pass=1 section=512 bits_a_byte=1.839 deposits=512 halvings=0 elapsed_ms=190278 | window sections=32 halvings=0 evaluations=32 ms=3313 ms_an_evaluation=103.53 limit=4462.3
PRT: TOWER_SECTION pass=1 section=544 bits_a_byte=1.813 deposits=544 halvings=0 elapsed_ms=192686 | window sections=32 halvings=0 evaluations=32 ms=3256 ms_an_evaluation=101.75 limit=4295.3
PRS: TOWER_SECTION pass=1 section=544 bits_a_byte=1.801 deposits=544 halvings=0 elapsed_ms=193522 | window sections=32 halvings=0 evaluations=32 ms=3244 ms_an_evaluation=101.38 limit=4462.3
PRT: TOWER_SECTION pass=1 section=576 bits_a_byte=1.863 deposits=576 halvings=0 elapsed_ms=195900 | window sections=32 halvings=0 evaluations=32 ms=3214 ms_an_evaluation=100.44 limit=4295.3
PRS: TOWER_SECTION pass=1 section=576 bits_a_byte=1.862 deposits=576 halvings=0 elapsed_ms=196758 | window sections=32 halvings=0 evaluations=32 ms=3236 ms_an_evaluation=101.12 limit=4462.3
PRT: TOWER_SECTION pass=1 section=608 bits_a_byte=1.833 deposits=608 halvings=0 elapsed_ms=199134 | window sections=32 halvings=0 evaluations=32 ms=3234 ms_an_evaluation=101.06 limit=4295.3
PRS: TOWER_SECTION pass=1 section=608 bits_a_byte=1.825 deposits=608 halvings=0 elapsed_ms=200001 | window sections=32 halvings=0 evaluations=32 ms=3243 ms_an_evaluation=101.34 limit=4462.3
PRT: TOWER_SECTION pass=1 section=640 bits_a_byte=1.827 deposits=640 halvings=0 elapsed_ms=202365 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=4295.3
PRS: TOWER_SECTION pass=1 section=640 bits_a_byte=1.825 deposits=640 halvings=0 elapsed_ms=203220 | window sections=32 halvings=0 evaluations=32 ms=3219 ms_an_evaluation=100.59 limit=4462.3
PRT: TOWER_SECTION pass=1 section=672 bits_a_byte=1.836 deposits=672 halvings=0 elapsed_ms=205602 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=4295.3
PRS: TOWER_SECTION pass=1 section=672 bits_a_byte=1.829 deposits=672 halvings=0 elapsed_ms=206515 | window sections=32 halvings=0 evaluations=32 ms=3295 ms_an_evaluation=102.97 limit=4462.3
PRT: TOWER_SECTION pass=1 section=704 bits_a_byte=1.831 deposits=704 halvings=0 elapsed_ms=208885 | window sections=32 halvings=0 evaluations=32 ms=3283 ms_an_evaluation=102.59 limit=4295.3
PRS: TOWER_SECTION pass=1 section=704 bits_a_byte=1.826 deposits=704 halvings=0 elapsed_ms=209801 | window sections=32 halvings=0 evaluations=32 ms=3286 ms_an_evaluation=102.69 limit=4462.3
PRT: TOWER_SECTION pass=1 section=736 bits_a_byte=1.819 deposits=736 halvings=0 elapsed_ms=212132 | window sections=32 halvings=0 evaluations=32 ms=3247 ms_an_evaluation=101.47 limit=4295.3
PRS: TOWER_SECTION pass=1 section=736 bits_a_byte=1.817 deposits=736 halvings=0 elapsed_ms=213061 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4462.3
PRT: TOWER_SECTION pass=1 section=768 bits_a_byte=1.821 deposits=768 halvings=0 elapsed_ms=215336 | window sections=32 halvings=0 evaluations=32 ms=3204 ms_an_evaluation=100.12 limit=4295.3
PRS: TOWER_SECTION pass=1 section=768 bits_a_byte=1.820 deposits=768 halvings=0 elapsed_ms=216347 | window sections=32 halvings=0 evaluations=32 ms=3286 ms_an_evaluation=102.69 limit=4462.3
PRT: TOWER_SECTION pass=1 section=800 bits_a_byte=1.804 deposits=800 halvings=0 elapsed_ms=218591 | window sections=32 halvings=0 evaluations=32 ms=3255 ms_an_evaluation=101.72 limit=4295.3
PRS: TOWER_SECTION pass=1 section=800 bits_a_byte=1.793 deposits=800 halvings=0 elapsed_ms=219601 | window sections=32 halvings=0 evaluations=32 ms=3254 ms_an_evaluation=101.69 limit=4462.3
PRT: TOWER_SECTION pass=1 section=832 bits_a_byte=1.816 deposits=832 halvings=0 elapsed_ms=221831 | window sections=32 halvings=0 evaluations=32 ms=3240 ms_an_evaluation=101.25 limit=4295.3
PRS: TOWER_SECTION pass=1 section=832 bits_a_byte=1.812 deposits=832 halvings=0 elapsed_ms=222858 | window sections=32 halvings=0 evaluations=32 ms=3257 ms_an_evaluation=101.78 limit=4462.3
PRT: TOWER_SECTION pass=1 section=864 bits_a_byte=1.816 deposits=864 halvings=0 elapsed_ms=225129 | window sections=32 halvings=0 evaluations=32 ms=3298 ms_an_evaluation=103.06 limit=4295.3
PRS: TOWER_SECTION pass=1 section=864 bits_a_byte=1.817 deposits=864 halvings=0 elapsed_ms=226163 | window sections=32 halvings=0 evaluations=32 ms=3305 ms_an_evaluation=103.28 limit=4462.3
PRT: TOWER_SECTION pass=1 section=896 bits_a_byte=1.819 deposits=896 halvings=0 elapsed_ms=228384 | window sections=32 halvings=0 evaluations=32 ms=3255 ms_an_evaluation=101.72 limit=4295.3
PRS: TOWER_SECTION pass=1 section=896 bits_a_byte=1.809 deposits=896 halvings=0 elapsed_ms=229417 | window sections=32 halvings=0 evaluations=32 ms=3254 ms_an_evaluation=101.69 limit=4462.3
PRT: TOWER_SECTION pass=1 section=928 bits_a_byte=1.845 deposits=928 halvings=0 elapsed_ms=231636 | window sections=32 halvings=0 evaluations=32 ms=3252 ms_an_evaluation=101.62 limit=4295.3
PRS: TOWER_SECTION pass=1 section=928 bits_a_byte=1.833 deposits=928 halvings=0 elapsed_ms=232687 | window sections=32 halvings=0 evaluations=32 ms=3270 ms_an_evaluation=102.19 limit=4462.3
PRT: TOWER_SECTION pass=1 section=960 bits_a_byte=1.814 deposits=960 halvings=0 elapsed_ms=234956 | window sections=32 halvings=0 evaluations=32 ms=3320 ms_an_evaluation=103.75 limit=4295.3
PRS: TOWER_SECTION pass=1 section=960 bits_a_byte=1.812 deposits=960 halvings=0 elapsed_ms=235985 | window sections=32 halvings=0 evaluations=32 ms=3298 ms_an_evaluation=103.06 limit=4462.3
PRT: TOWER_SECTION pass=1 section=992 bits_a_byte=1.821 deposits=992 halvings=0 elapsed_ms=238193 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=4295.3
PRS: TOWER_SECTION pass=1 section=992 bits_a_byte=1.817 deposits=992 halvings=0 elapsed_ms=239235 | window sections=32 halvings=0 evaluations=32 ms=3250 ms_an_evaluation=101.56 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1024 bits_a_byte=1.771 deposits=1024 halvings=0 elapsed_ms=241400 | window sections=32 halvings=0 evaluations=32 ms=3207 ms_an_evaluation=100.22 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1024 bits_a_byte=1.777 deposits=1024 halvings=0 elapsed_ms=242446 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1056 bits_a_byte=1.792 deposits=1056 halvings=0 elapsed_ms=244613 | window sections=32 halvings=0 evaluations=32 ms=3213 ms_an_evaluation=100.41 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1056 bits_a_byte=1.796 deposits=1056 halvings=0 elapsed_ms=245720 | window sections=32 halvings=0 evaluations=32 ms=3274 ms_an_evaluation=102.31 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1088 bits_a_byte=1.828 deposits=1088 halvings=0 elapsed_ms=247890 | window sections=32 halvings=0 evaluations=32 ms=3277 ms_an_evaluation=102.41 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1088 bits_a_byte=1.827 deposits=1088 halvings=0 elapsed_ms=248950 | window sections=32 halvings=0 evaluations=32 ms=3230 ms_an_evaluation=100.94 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1120 bits_a_byte=1.803 deposits=1120 halvings=0 elapsed_ms=251111 | window sections=32 halvings=0 evaluations=32 ms=3221 ms_an_evaluation=100.66 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1120 bits_a_byte=1.806 deposits=1120 halvings=0 elapsed_ms=252171 | window sections=32 halvings=0 evaluations=32 ms=3221 ms_an_evaluation=100.66 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1152 bits_a_byte=1.820 deposits=1152 halvings=0 elapsed_ms=254386 | window sections=32 halvings=0 evaluations=32 ms=3275 ms_an_evaluation=102.34 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1152 bits_a_byte=1.813 deposits=1152 halvings=0 elapsed_ms=255493 | window sections=32 halvings=0 evaluations=32 ms=3322 ms_an_evaluation=103.81 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1184 bits_a_byte=1.778 deposits=1184 halvings=0 elapsed_ms=257610 | window sections=32 halvings=0 evaluations=32 ms=3224 ms_an_evaluation=100.75 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1184 bits_a_byte=1.774 deposits=1184 halvings=0 elapsed_ms=258752 | window sections=32 halvings=0 evaluations=32 ms=3259 ms_an_evaluation=101.84 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1216 bits_a_byte=1.807 deposits=1216 halvings=0 elapsed_ms=260841 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1216 bits_a_byte=1.801 deposits=1216 halvings=0 elapsed_ms=261996 | window sections=32 halvings=0 evaluations=32 ms=3244 ms_an_evaluation=101.38 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1248 bits_a_byte=1.780 deposits=1248 halvings=0 elapsed_ms=264060 | window sections=32 halvings=0 evaluations=32 ms=3219 ms_an_evaluation=100.59 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1248 bits_a_byte=1.776 deposits=1248 halvings=0 elapsed_ms=265316 | window sections=32 halvings=0 evaluations=32 ms=3320 ms_an_evaluation=103.75 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1280 bits_a_byte=1.804 deposits=1280 halvings=0 elapsed_ms=267309 | window sections=32 halvings=0 evaluations=32 ms=3249 ms_an_evaluation=101.53 limit=4295.3
PRS: TOWER_SECTION pass=1 section=1280 bits_a_byte=1.796 deposits=1280 halvings=0 elapsed_ms=268554 | window sections=32 halvings=0 evaluations=32 ms=3238 ms_an_evaluation=101.19 limit=4462.3
PRT: TOWER_SECTION pass=1 section=1311 bits_a_byte=1.775 deposits=1311 halvings=0 elapsed_ms=270415 | window sections=31 halvings=0 evaluations=31 ms=3106 ms_an_evaluation=100.19 limit=4161.1
PRT: TOWER_STATE STATE.1 state_bytes=12547544 state_sha256=7782e43e362edbb73aacc7dd621eff1f72a69951ecfe216d09d8b1b01e155cb2
PRS: TOWER_SECTION pass=1 section=1311 bits_a_byte=1.775 deposits=1311 halvings=0 elapsed_ms=271734 | window sections=31 halvings=0 evaluations=31 ms=3180 ms_an_evaluation=102.58 limit=4322.9
PRS: TOWER_STATE STATE.1 state_bytes=12527219 state_sha256=fea5027180d43403559a4e2637971653fc024c1f91c22288210fa0f3a3c53a6f
PRT: TOWER_PASS pass=1 train_bits_a_byte=1.840 dev_bits_a_byte=1.830 dev_regions Q=1.265 P=2.368 N=0.492 M=1.839 deposits=1311/1311 pass_ms=137374 elapsed_ms=274988 train_code=6807401654394 dev_code=763208465902 grain_bits=20
PRS: TOWER_PASS pass=1 train_bits_a_byte=1.835 dev_bits_a_byte=1.829 dev_regions Q=1.295 P=2.386 N=0.528 M=1.837 deposits=1311/1311 pass_ms=138078 elapsed_ms=276276 train_code=6787801547150 dev_code=762761628124 grain_bits=20
PRT: TOWER_SECTION pass=2 section=32 bits_a_byte=1.779 deposits=32 halvings=0 elapsed_ms=278285 | window sections=32 halvings=0 evaluations=32 ms=3297 ms_an_evaluation=103.03 limit=4295.3
PRS: TOWER_SECTION pass=2 section=32 bits_a_byte=1.786 deposits=32 halvings=0 elapsed_ms=279531 | window sections=32 halvings=0 evaluations=32 ms=3255 ms_an_evaluation=101.72 limit=4462.3
PRT: TOWER_SECTION pass=2 section=64 bits_a_byte=1.773 deposits=64 halvings=0 elapsed_ms=281571 | window sections=32 halvings=0 evaluations=32 ms=3286 ms_an_evaluation=102.69 limit=4295.3
PRS: TOWER_SECTION pass=2 section=64 bits_a_byte=1.773 deposits=64 halvings=0 elapsed_ms=282793 | window sections=32 halvings=0 evaluations=32 ms=3262 ms_an_evaluation=101.94 limit=4462.3
PRT: TOWER_SECTION pass=2 section=96 bits_a_byte=1.799 deposits=96 halvings=0 elapsed_ms=284842 | window sections=32 halvings=0 evaluations=32 ms=3271 ms_an_evaluation=102.22 limit=4295.3
PRS: TOWER_SECTION pass=2 section=96 bits_a_byte=1.792 deposits=96 halvings=0 elapsed_ms=286085 | window sections=32 halvings=0 evaluations=32 ms=3292 ms_an_evaluation=102.88 limit=4462.3
PRT: TOWER_SECTION pass=2 section=128 bits_a_byte=1.770 deposits=128 halvings=0 elapsed_ms=288153 | window sections=32 halvings=0 evaluations=32 ms=3311 ms_an_evaluation=103.47 limit=4295.3
PRS: TOWER_SECTION pass=2 section=128 bits_a_byte=1.764 deposits=128 halvings=0 elapsed_ms=289378 | window sections=32 halvings=0 evaluations=32 ms=3293 ms_an_evaluation=102.91 limit=4462.3
PRT: TOWER_SECTION pass=2 section=160 bits_a_byte=1.791 deposits=160 halvings=0 elapsed_ms=291367 | window sections=32 halvings=0 evaluations=32 ms=3214 ms_an_evaluation=100.44 limit=4295.3
PRS: TOWER_SECTION pass=2 section=160 bits_a_byte=1.785 deposits=160 halvings=0 elapsed_ms=292643 | window sections=32 halvings=0 evaluations=32 ms=3265 ms_an_evaluation=102.03 limit=4462.3
PRT: TOWER_SECTION pass=2 section=192 bits_a_byte=1.763 deposits=192 halvings=0 elapsed_ms=294603 | window sections=32 halvings=0 evaluations=32 ms=3236 ms_an_evaluation=101.12 limit=4295.3
PRS: TOWER_SECTION pass=2 section=192 bits_a_byte=1.756 deposits=192 halvings=0 elapsed_ms=295941 | window sections=32 halvings=0 evaluations=32 ms=3298 ms_an_evaluation=103.06 limit=4462.3
PRT: TOWER_SECTION pass=2 section=224 bits_a_byte=1.706 deposits=224 halvings=0 elapsed_ms=297863 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4295.3
PRS: TOWER_SECTION pass=2 section=224 bits_a_byte=1.703 deposits=224 halvings=0 elapsed_ms=299218 | window sections=32 halvings=0 evaluations=32 ms=3277 ms_an_evaluation=102.41 limit=4462.3
PRT: TOWER_SECTION pass=2 section=256 bits_a_byte=1.817 deposits=256 halvings=0 elapsed_ms=301123 | window sections=32 halvings=0 evaluations=32 ms=3260 ms_an_evaluation=101.88 limit=4295.3
PRS: TOWER_SECTION pass=2 section=256 bits_a_byte=1.816 deposits=256 halvings=0 elapsed_ms=302476 | window sections=32 halvings=0 evaluations=32 ms=3258 ms_an_evaluation=101.81 limit=4462.3
PRT: TOWER_SECTION pass=2 section=288 bits_a_byte=1.773 deposits=288 halvings=0 elapsed_ms=304345 | window sections=32 halvings=0 evaluations=32 ms=3222 ms_an_evaluation=100.69 limit=4295.3
PRS: TOWER_SECTION pass=2 section=288 bits_a_byte=1.771 deposits=288 halvings=0 elapsed_ms=305843 | window sections=32 halvings=0 evaluations=32 ms=3367 ms_an_evaluation=105.22 limit=4462.3
PRT: TOWER_SECTION pass=2 section=320 bits_a_byte=1.743 deposits=320 halvings=0 elapsed_ms=307783 | window sections=32 halvings=0 evaluations=32 ms=3438 ms_an_evaluation=107.44 limit=4295.3
PRS: TOWER_SECTION pass=2 section=320 bits_a_byte=1.736 deposits=320 halvings=0 elapsed_ms=309203 | window sections=32 halvings=0 evaluations=32 ms=3360 ms_an_evaluation=105.00 limit=4462.3
PRT: TOWER_SECTION pass=2 section=352 bits_a_byte=1.773 deposits=352 halvings=0 elapsed_ms=311111 | window sections=32 halvings=0 evaluations=32 ms=3328 ms_an_evaluation=104.00 limit=4295.3
PRS: TOWER_SECTION pass=2 section=352 bits_a_byte=1.775 deposits=352 halvings=0 elapsed_ms=312585 | window sections=32 halvings=0 evaluations=32 ms=3382 ms_an_evaluation=105.69 limit=4462.3
PRT: TOWER_SECTION pass=2 section=384 bits_a_byte=1.782 deposits=384 halvings=0 elapsed_ms=314508 | window sections=32 halvings=0 evaluations=32 ms=3397 ms_an_evaluation=106.16 limit=4295.3
PRS: TOWER_SECTION pass=2 section=384 bits_a_byte=1.781 deposits=384 halvings=0 elapsed_ms=316008 | window sections=32 halvings=0 evaluations=32 ms=3423 ms_an_evaluation=106.97 limit=4462.3
PRT: TOWER_SECTION pass=2 section=416 bits_a_byte=1.757 deposits=416 halvings=0 elapsed_ms=318012 | window sections=32 halvings=0 evaluations=32 ms=3504 ms_an_evaluation=109.50 limit=4295.3
PRS: TOWER_SECTION pass=2 section=416 bits_a_byte=1.759 deposits=416 halvings=0 elapsed_ms=319515 | window sections=32 halvings=0 evaluations=32 ms=3507 ms_an_evaluation=109.59 limit=4462.3
PRT: TOWER_SECTION pass=2 section=448 bits_a_byte=1.766 deposits=448 halvings=0 elapsed_ms=321656 | window sections=32 halvings=0 evaluations=32 ms=3644 ms_an_evaluation=113.88 limit=4295.3
PRS: TOWER_SECTION pass=2 section=448 bits_a_byte=1.765 deposits=448 halvings=0 elapsed_ms=323057 | window sections=32 halvings=0 evaluations=32 ms=3542 ms_an_evaluation=110.69 limit=4462.3
PRT: TOWER_SECTION pass=2 section=480 bits_a_byte=1.751 deposits=480 halvings=0 elapsed_ms=324929 | window sections=32 halvings=0 evaluations=32 ms=3273 ms_an_evaluation=102.28 limit=4295.3
PRS: TOWER_SECTION pass=2 section=480 bits_a_byte=1.764 deposits=480 halvings=0 elapsed_ms=326371 | window sections=32 halvings=0 evaluations=32 ms=3314 ms_an_evaluation=103.56 limit=4462.3
PRT: TOWER_SECTION pass=2 section=512 bits_a_byte=1.760 deposits=512 halvings=0 elapsed_ms=328252 | window sections=32 halvings=0 evaluations=32 ms=3323 ms_an_evaluation=103.84 limit=4295.3
PRS: TOWER_SECTION pass=2 section=512 bits_a_byte=1.803 deposits=512 halvings=5 elapsed_ms=329846 | window sections=32 halvings=5 evaluations=37 ms=3475 ms_an_evaluation=93.92 limit=5159.5
PRT: TOWER_SECTION pass=2 section=544 bits_a_byte=1.711 deposits=544 halvings=0 elapsed_ms=331496 | window sections=32 halvings=0 evaluations=32 ms=3244 ms_an_evaluation=101.38 limit=4295.3
PRS: TOWER_SECTION pass=2 section=544 bits_a_byte=1.761 deposits=544 halvings=5 elapsed_ms=333135 | window sections=32 halvings=0 evaluations=32 ms=3289 ms_an_evaluation=102.78 limit=4462.3
PRT: TOWER_SECTION pass=2 section=576 bits_a_byte=1.756 deposits=576 halvings=0 elapsed_ms=334774 | window sections=32 halvings=0 evaluations=32 ms=3278 ms_an_evaluation=102.44 limit=4295.3
PRS: TOWER_SECTION pass=2 section=576 bits_a_byte=1.785 deposits=576 halvings=5 elapsed_ms=336419 | window sections=32 halvings=0 evaluations=32 ms=3284 ms_an_evaluation=102.62 limit=4462.3
PRT: TOWER_SECTION pass=2 section=608 bits_a_byte=1.734 deposits=608 halvings=0 elapsed_ms=338019 | window sections=32 halvings=0 evaluations=32 ms=3245 ms_an_evaluation=101.41 limit=4295.3
PRS: TOWER_SECTION pass=2 section=608 bits_a_byte=1.745 deposits=608 halvings=5 elapsed_ms=339678 | window sections=32 halvings=0 evaluations=32 ms=3259 ms_an_evaluation=101.84 limit=4462.3
PRT: TOWER_SECTION pass=2 section=640 bits_a_byte=1.733 deposits=640 halvings=0 elapsed_ms=341251 | window sections=32 halvings=0 evaluations=32 ms=3232 ms_an_evaluation=101.00 limit=4295.3
PRS: TOWER_SECTION pass=2 section=640 bits_a_byte=1.746 deposits=640 halvings=5 elapsed_ms=342915 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=4462.3
PRT: TOWER_SECTION pass=2 section=672 bits_a_byte=1.744 deposits=672 halvings=0 elapsed_ms=344486 | window sections=32 halvings=0 evaluations=32 ms=3235 ms_an_evaluation=101.09 limit=4295.3
PRS: TOWER_SECTION pass=2 section=672 bits_a_byte=1.742 deposits=672 halvings=5 elapsed_ms=346152 | window sections=32 halvings=0 evaluations=32 ms=3237 ms_an_evaluation=101.16 limit=4462.3
PRT: TOWER_SECTION pass=2 section=704 bits_a_byte=1.739 deposits=704 halvings=0 elapsed_ms=347726 | window sections=32 halvings=0 evaluations=32 ms=3240 ms_an_evaluation=101.25 limit=4295.3
PRS: TOWER_SECTION pass=2 section=704 bits_a_byte=1.743 deposits=704 halvings=5 elapsed_ms=349378 | window sections=32 halvings=0 evaluations=32 ms=3226 ms_an_evaluation=100.81 limit=4462.3
PRT: TOWER_SECTION pass=2 section=736 bits_a_byte=1.725 deposits=736 halvings=0 elapsed_ms=350941 | window sections=32 halvings=0 evaluations=32 ms=3215 ms_an_evaluation=100.47 limit=4295.3
PRS: TOWER_SECTION pass=2 section=736 bits_a_byte=1.732 deposits=736 halvings=5 elapsed_ms=352589 | window sections=32 halvings=0 evaluations=32 ms=3211 ms_an_evaluation=100.34 limit=4462.3
PRT: TOWER_SECTION pass=2 section=768 bits_a_byte=1.733 deposits=768 halvings=0 elapsed_ms=354164 | window sections=32 halvings=0 evaluations=32 ms=3223 ms_an_evaluation=100.72 limit=4295.3
PRS: TOWER_SECTION pass=2 section=768 bits_a_byte=1.730 deposits=768 halvings=5 elapsed_ms=355828 | window sections=32 halvings=0 evaluations=32 ms=3239 ms_an_evaluation=101.22 limit=4462.3
PRT: TOWER_SECTION pass=2 section=800 bits_a_byte=1.709 deposits=800 halvings=0 elapsed_ms=357400 | window sections=32 halvings=0 evaluations=32 ms=3236 ms_an_evaluation=101.12 limit=4295.3
PRS: TOWER_SECTION pass=2 section=800 bits_a_byte=1.713 deposits=800 halvings=5 elapsed_ms=359062 | window sections=32 halvings=0 evaluations=32 ms=3234 ms_an_evaluation=101.06 limit=4462.3
PRT: TOWER_SECTION pass=2 section=832 bits_a_byte=1.725 deposits=832 halvings=0 elapsed_ms=360631 | window sections=32 halvings=0 evaluations=32 ms=3231 ms_an_evaluation=100.97 limit=4295.3
PRS: TOWER_SECTION pass=2 section=832 bits_a_byte=1.727 deposits=832 halvings=5 elapsed_ms=362304 | window sections=32 halvings=0 evaluations=32 ms=3242 ms_an_evaluation=101.31 limit=4462.3
PRT: TOWER_SECTION pass=2 section=864 bits_a_byte=1.727 deposits=864 halvings=0 elapsed_ms=363878 | window sections=32 halvings=0 evaluations=32 ms=3247 ms_an_evaluation=101.47 limit=4295.3
PRS: TOWER_SECTION pass=2 section=864 bits_a_byte=1.731 deposits=864 halvings=5 elapsed_ms=365558 | window sections=32 halvings=0 evaluations=32 ms=3254 ms_an_evaluation=101.69 limit=4462.3
PRT: TOWER_SECTION pass=2 section=896 bits_a_byte=1.734 deposits=896 halvings=0 elapsed_ms=367142 | window sections=32 halvings=0 evaluations=32 ms=3264 ms_an_evaluation=102.00 limit=4295.3
PRS: TOWER_SECTION pass=2 section=896 bits_a_byte=1.731 deposits=896 halvings=5 elapsed_ms=368851 | window sections=32 halvings=0 evaluations=32 ms=3293 ms_an_evaluation=102.91 limit=4462.3
PRT: TOWER_SECTION pass=2 section=928 bits_a_byte=1.765 deposits=928 halvings=0 elapsed_ms=370553 | window sections=32 halvings=0 evaluations=32 ms=3411 ms_an_evaluation=106.59 limit=4295.3
PRS: TOWER_SECTION pass=2 section=928 bits_a_byte=1.754 deposits=928 halvings=5 elapsed_ms=372569 | window sections=32 halvings=0 evaluations=32 ms=3718 ms_an_evaluation=116.19 limit=4462.3
PRT: TOWER_SECTION pass=2 section=960 bits_a_byte=1.733 deposits=960 halvings=0 elapsed_ms=374117 | window sections=32 halvings=0 evaluations=32 ms=3564 ms_an_evaluation=111.38 limit=4295.3
PRS: TOWER_SECTION pass=2 section=960 bits_a_byte=1.732 deposits=960 halvings=5 elapsed_ms=375870 | window sections=32 halvings=0 evaluations=32 ms=3301 ms_an_evaluation=103.16 limit=4462.3
PRT: TOWER_SECTION pass=2 section=992 bits_a_byte=1.740 deposits=992 halvings=0 elapsed_ms=377401 | window sections=32 halvings=0 evaluations=32 ms=3284 ms_an_evaluation=102.62 limit=4295.3
PRS: TOWER_SECTION pass=2 section=992 bits_a_byte=1.736 deposits=992 halvings=5 elapsed_ms=379159 | window sections=32 halvings=0 evaluations=32 ms=3289 ms_an_evaluation=102.78 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1024 bits_a_byte=1.697 deposits=1024 halvings=0 elapsed_ms=380664 | window sections=32 halvings=0 evaluations=32 ms=3263 ms_an_evaluation=101.97 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1024 bits_a_byte=1.698 deposits=1024 halvings=5 elapsed_ms=382438 | window sections=32 halvings=0 evaluations=32 ms=3279 ms_an_evaluation=102.47 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1056 bits_a_byte=1.709 deposits=1056 halvings=0 elapsed_ms=383986 | window sections=32 halvings=0 evaluations=32 ms=3322 ms_an_evaluation=103.81 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1056 bits_a_byte=1.716 deposits=1056 halvings=5 elapsed_ms=385813 | window sections=32 halvings=0 evaluations=32 ms=3375 ms_an_evaluation=105.47 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1088 bits_a_byte=1.752 deposits=1088 halvings=0 elapsed_ms=387363 | window sections=32 halvings=0 evaluations=32 ms=3377 ms_an_evaluation=105.53 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1088 bits_a_byte=1.752 deposits=1088 halvings=5 elapsed_ms=389122 | window sections=32 halvings=0 evaluations=32 ms=3309 ms_an_evaluation=103.41 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1120 bits_a_byte=1.725 deposits=1120 halvings=0 elapsed_ms=390572 | window sections=32 halvings=0 evaluations=32 ms=3209 ms_an_evaluation=100.28 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1120 bits_a_byte=1.732 deposits=1120 halvings=5 elapsed_ms=392328 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1152 bits_a_byte=1.743 deposits=1152 halvings=0 elapsed_ms=393778 | window sections=32 halvings=0 evaluations=32 ms=3206 ms_an_evaluation=100.19 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1152 bits_a_byte=1.740 deposits=1152 halvings=5 elapsed_ms=395595 | window sections=32 halvings=0 evaluations=32 ms=3267 ms_an_evaluation=102.09 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1184 bits_a_byte=1.699 deposits=1184 halvings=0 elapsed_ms=397028 | window sections=32 halvings=0 evaluations=32 ms=3250 ms_an_evaluation=101.56 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1184 bits_a_byte=1.704 deposits=1184 halvings=5 elapsed_ms=398888 | window sections=32 halvings=0 evaluations=32 ms=3293 ms_an_evaluation=102.91 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1216 bits_a_byte=1.732 deposits=1216 halvings=0 elapsed_ms=400303 | window sections=32 halvings=0 evaluations=32 ms=3275 ms_an_evaluation=102.34 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1216 bits_a_byte=1.730 deposits=1216 halvings=5 elapsed_ms=402146 | window sections=32 halvings=0 evaluations=32 ms=3258 ms_an_evaluation=101.81 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1248 bits_a_byte=1.707 deposits=1248 halvings=0 elapsed_ms=403575 | window sections=32 halvings=0 evaluations=32 ms=3272 ms_an_evaluation=102.25 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1248 bits_a_byte=1.706 deposits=1248 halvings=5 elapsed_ms=405462 | window sections=32 halvings=0 evaluations=32 ms=3316 ms_an_evaluation=103.62 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1280 bits_a_byte=1.731 deposits=1280 halvings=0 elapsed_ms=406884 | window sections=32 halvings=0 evaluations=32 ms=3309 ms_an_evaluation=103.41 limit=4295.3
PRS: TOWER_SECTION pass=2 section=1280 bits_a_byte=1.725 deposits=1280 halvings=5 elapsed_ms=408758 | window sections=32 halvings=0 evaluations=32 ms=3296 ms_an_evaluation=103.00 limit=4462.3
PRT: TOWER_SECTION pass=2 section=1311 bits_a_byte=1.704 deposits=1311 halvings=0 elapsed_ms=410029 | window sections=31 halvings=0 evaluations=31 ms=3145 ms_an_evaluation=101.45 limit=4161.1
PRT: TOWER_STATE STATE.2 state_bytes=12533456 state_sha256=3fd266914f9e39a87aa125eea37a2da483f080c4a641f818130c756afef1ec80
PRS: TOWER_SECTION pass=2 section=1311 bits_a_byte=1.707 deposits=1311 halvings=5 elapsed_ms=411971 | window sections=31 halvings=0 evaluations=31 ms=3213 ms_an_evaluation=103.65 limit=4322.9
PRS: TOWER_STATE STATE.2 state_bytes=12535854 state_sha256=aa82c3308de31cf55fa2a21525ead45d17d4bb9a8ce891eb8bf01e270a9b5330
PRT: TOWER_PASS pass=2 train_bits_a_byte=1.744 dev_bits_a_byte=1.765 dev_regions Q=1.197 P=2.287 N=0.478 M=1.774 deposits=1311/1311 pass_ms=139573 elapsed_ms=414562 train_code=6451651811100 dev_code=736124065026 grain_bits=20
PRT: TOWER_DONE state_bytes=12533456 state_sha256=3fd266914f9e39a87aa125eea37a2da483f080c4a641f818130c756afef1ec80 elapsed_ms=414631
PRT: RUN_RECEIPT exit=0 wall_s=415.0 peak_rss_kib=300824 user_s=2506.0
PRS: TOWER_PASS pass=2 train_bits_a_byte=1.747 dev_bits_a_byte=1.772 dev_regions Q=1.221 P=2.340 N=0.478 M=1.780 deposits=1311/1311 pass_ms=139963 elapsed_ms=416239 train_code=6463317753309 dev_code=738966908779 grain_bits=20
PRS: TOWER_DONE state_bytes=12535854 state_sha256=aa82c3308de31cf55fa2a21525ead45d17d4bb9a8ce891eb8bf01e270a9b5330 elapsed_ms=416302
PRS: RUN_RECEIPT exit=0 wall_s=416.7 peak_rss_kib=293036 user_s=2511.0
```

## The level read of `PRT` and `PRS`

Each pair ran the training and held cells together; each probe ran
`python3 -I tools/gsm8k/numeral_rings.py probe KIND train_all.txt OUT_TRAIN dev.txt OUT_HELD 2 64 2000`
under a 300 s deadline. The comparison lines for `C`, `PP` and `PR` are in the rotor loop's receipt.
```text
=== at PRT numerals
UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=c3fb39fcd8ca7eb8ab88905a6520dcdc7b446077308dbe0cc879591c0ff57834 elapsed_ms=6935
RUN_RECEIPT exit=0 wall_s=7.0 peak_rss_kib=79228 user_s=53.7
UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=c41733d7c9c0a958f6f6db6e5eae23cbf063102790f5d3954f03a42bb56b0dc5 elapsed_ms=2671
RUN_RECEIPT exit=0 wall_s=2.7 peak_rss_kib=40228 user_s=20.4
=== at PRT equals
UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=d818505122c3538d08b6c38b3d11c7e2c76b50cbb9a0d152b701a71c7890d3f3 elapsed_ms=8423
RUN_RECEIPT exit=0 wall_s=8.4 peak_rss_kib=38196 user_s=66.2
UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=d59ae38404e2e30f22284a0687236c9f8550f7a1f49e22707473b3aaf065ea8b elapsed_ms=3414
RUN_RECEIPT exit=0 wall_s=3.4 peak_rss_kib=38244 user_s=26.2
=== at PRS numerals
UNIT_AT problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=da07feb77ced0c7ee472b0d87902a2b23e808836fdd8aa2de22a9a872f52e972 elapsed_ms=6925
RUN_RECEIPT exit=0 wall_s=7.0 peak_rss_kib=78676 user_s=54.0
UNIT_AT problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=c5a29144ba88d261b41e7e0f0ee12d93ccc0aa771a421b31aae332256175a81a elapsed_ms=2766
RUN_RECEIPT exit=0 wall_s=2.8 peak_rss_kib=41120 user_s=21.3
=== at PRS equals
UNIT_AT problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=262eb9f5103551d6142e694d54c852ab2616510fc7d6841508e84a1dbbf4c6de elapsed_ms=8350
RUN_RECEIPT exit=0 wall_s=8.4 peak_rss_kib=38952 user_s=64.9
UNIT_AT problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=19dd098a0cae5f54bae132bc5a8da334481e57b6ff56eacc6f9ac48739927b73 elapsed_ms=3614
RUN_RECEIPT exit=0 wall_s=3.6 peak_rss_kib=38672 user_s=28.1

=== probe PRT numerals
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=758 energy=799 majority=637 suffix=1530 foil=418
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=1082 energy=1555 majority=3079 suffix=3800 foil=793
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=866 energy=810 majority=599 suffix=1518 foil=351
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=890 energy=930 majority=827 suffix=1574 foil=545
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=771 energy=750 majority=562 suffix=1491 foil=312
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=661 energy=466 majority=1772 suffix=3800 foil=332
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=809 energy=595 majority=637 suffix=1530 foil=390
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=1926 energy=1523 majority=3079 suffix=3800 foil=1531
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=975 energy=472 majority=599 suffix=1518 foil=337
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=992 energy=745 majority=827 suffix=1574 foil=603
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=880 energy=406 majority=562 suffix=1491 foil=330
NUMERAL_RINGS cells=turns/at_PRT_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=764 energy=144 majority=1772 suffix=3800 foil=262
RUN_RECEIPT exit=0 wall_s=13.9 peak_rss_kib=325860 user_s=13.7

=== probe PRT equals
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=114 energy=113 majority=143 suffix=620 foil=85
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=227 energy=280 majority=426 suffix=837 foil=126
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=116 energy=79 majority=70 suffix=625 foil=64
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=135 energy=122 majority=138 suffix=628 foil=110
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=94 energy=64 majority=75 suffix=614 foil=67
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=44 energy=11 majority=134 suffix=837 foil=6
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=235 energy=177 majority=134 suffix=676 foil=91
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=406 energy=366 majority=306 suffix=839 foil=103
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=299 energy=298 majority=99 suffix=677 foil=87
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=350 energy=269 majority=141 suffix=673 foil=129
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=299 energy=300 majority=103 suffix=681 foil=61
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=311 energy=260 majority=85 suffix=839 foil=13
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=133 energy=155 majority=92 suffix=615 foil=96
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=296 energy=281 majority=304 suffix=840 foil=136
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=119 energy=128 majority=80 suffix=612 foil=76
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=152 energy=137 majority=133 suffix=627 foil=116
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=100 energy=86 majority=68 suffix=609 foil=67
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=70 energy=45 majority=88 suffix=840 foil=19
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=151 energy=119 majority=143 suffix=620 foil=102
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=370 energy=220 majority=426 suffix=837 foil=209
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=131 energy=95 majority=70 suffix=625 foil=60
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=162 energy=119 majority=138 suffix=628 foil=121
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=102 energy=63 majority=75 suffix=614 foil=63
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=192 energy=28 majority=134 suffix=837 foil=33
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=275 energy=107 majority=134 suffix=676 foil=106
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=550 energy=188 majority=306 suffix=839 foil=143
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=278 energy=105 majority=99 suffix=677 foil=80
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=325 energy=164 majority=141 suffix=673 foil=122
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=303 energy=104 majority=103 suffix=681 foil=50
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=446 energy=72 majority=85 suffix=839 foil=26
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=143 energy=76 majority=92 suffix=615 foil=92
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=346 energy=183 majority=304 suffix=840 foil=147
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=111 energy=68 majority=80 suffix=612 foil=77
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=162 energy=122 majority=133 suffix=627 foil=119
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=104 energy=76 majority=68 suffix=609 foil=63
NUMERAL_RINGS cells=turns/at_PRT_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=167 energy=19 majority=88 suffix=840 foil=24
RUN_RECEIPT exit=0 wall_s=8.1 peak_rss_kib=80180 user_s=8.1

=== probe PRS numerals
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=9 held=3810 train=10792 modes=602 energy=815 majority=637 suffix=1530 foil=325
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=10 held=3810 train=10792 modes=2205 energy=2640 majority=3079 suffix=3800 foil=1701
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=11 held=3810 train=10792 modes=642 energy=603 majority=599 suffix=1518 foil=302
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=7 held=3810 train=10792 modes=789 energy=890 majority=827 suffix=1574 foil=547
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=13 held=3810 train=10792 modes=704 energy=560 majority=562 suffix=1491 foil=294
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=0 mod=100 held=3810 train=10792 modes=362 energy=878 majority=1772 suffix=3800 foil=115
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=9 held=3810 train=10792 modes=773 energy=483 majority=637 suffix=1530 foil=473
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=10 held=3810 train=10792 modes=1521 energy=1277 majority=3079 suffix=3800 foil=1247
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=11 held=3810 train=10792 modes=688 energy=542 majority=599 suffix=1518 foil=381
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=7 held=3810 train=10792 modes=763 energy=515 majority=827 suffix=1574 foil=572
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=13 held=3810 train=10792 modes=669 energy=447 majority=562 suffix=1491 foil=346
NUMERAL_RINGS cells=turns/at_PRS_held_numerals kind=numerals label=numeral level=1 mod=100 held=3810 train=10792 modes=411 energy=90 majority=1772 suffix=3800 foil=162
RUN_RECEIPT exit=0 wall_s=14.1 peak_rss_kib=325204 user_s=13.9

=== probe PRS equals
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=9 held=841 train=2200 modes=135 energy=159 majority=143 suffix=620 foil=109
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=10 held=841 train=2200 modes=348 energy=330 majority=426 suffix=837 foil=170
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=11 held=841 train=2200 modes=121 energy=105 majority=70 suffix=625 foil=76
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=7 held=841 train=2200 modes=152 energy=136 majority=138 suffix=628 foil=119
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=13 held=841 train=2200 modes=104 energy=99 majority=75 suffix=614 foil=64
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=0 mod=100 held=841 train=2200 modes=108 energy=86 majority=134 suffix=837 foil=20
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=9 held=841 train=2200 modes=267 energy=248 majority=134 suffix=676 foil=97
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=10 held=841 train=2200 modes=550 energy=349 majority=306 suffix=839 foil=136
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=11 held=841 train=2200 modes=312 energy=182 majority=99 suffix=677 foil=94
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=7 held=841 train=2200 modes=345 energy=214 majority=141 suffix=673 foil=121
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=13 held=841 train=2200 modes=322 energy=188 majority=103 suffix=681 foil=60
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=0 mod=100 held=841 train=2200 modes=375 energy=161 majority=85 suffix=839 foil=26
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=9 held=841 train=2200 modes=176 energy=154 majority=92 suffix=615 foil=122
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=10 held=841 train=2200 modes=309 energy=244 majority=304 suffix=840 foil=127
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=11 held=841 train=2200 modes=126 energy=108 majority=80 suffix=612 foil=75
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=7 held=841 train=2200 modes=145 energy=157 majority=133 suffix=627 foil=135
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=13 held=841 train=2200 modes=102 energy=94 majority=68 suffix=609 foil=64
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=0 mod=100 held=841 train=2200 modes=105 energy=68 majority=88 suffix=840 foil=21
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=9 held=841 train=2200 modes=146 energy=114 majority=143 suffix=620 foil=97
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=10 held=841 train=2200 modes=392 energy=264 majority=426 suffix=837 foil=212
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=11 held=841 train=2200 modes=112 energy=84 majority=70 suffix=625 foil=82
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=7 held=841 train=2200 modes=144 energy=126 majority=138 suffix=628 foil=115
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=13 held=841 train=2200 modes=101 energy=49 majority=75 suffix=614 foil=62
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=a level=1 mod=100 held=841 train=2200 modes=168 energy=33 majority=134 suffix=837 foil=26
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=9 held=841 train=2200 modes=280 energy=110 majority=134 suffix=676 foil=98
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=10 held=841 train=2200 modes=592 energy=218 majority=306 suffix=839 foil=153
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=11 held=841 train=2200 modes=283 energy=103 majority=99 suffix=677 foil=90
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=7 held=841 train=2200 modes=333 energy=108 majority=141 suffix=673 foil=112
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=13 held=841 train=2200 modes=297 energy=90 majority=103 suffix=681 foil=64
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=b level=1 mod=100 held=841 train=2200 modes=453 energy=36 majority=85 suffix=839 foil=30
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=9 held=841 train=2200 modes=143 energy=98 majority=92 suffix=615 foil=98
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=10 held=841 train=2200 modes=337 energy=210 majority=304 suffix=840 foil=156
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=11 held=841 train=2200 modes=113 energy=73 majority=80 suffix=612 foil=66
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=7 held=841 train=2200 modes=175 energy=125 majority=133 suffix=627 foil=131
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=13 held=841 train=2200 modes=110 energy=75 majority=68 suffix=609 foil=66
NUMERAL_RINGS cells=turns/at_PRS_held_equals kind=equals label=result level=1 mod=100 held=841 train=2200 modes=147 energy=17 majority=88 suffix=840 foil=23
RUN_RECEIPT exit=0 wall_s=8.1 peak_rss_kib=79948 user_s=8.1
```
