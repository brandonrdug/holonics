# The strands loop on Brandon's PC

The lines below are the runs' own output from the PC's run directory; the run paths are relative to
it (`RUN` is the run directory, `strands/`, `turns/`, `capture/` and `rotor/` its loops). Each heavy
run ran under the `wait4` wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8` and its own memory scope
(`MemoryMax=8G`, `MemorySwapMax=0`). The per-process load lines are left out: other programs on the
host held between a third of a core and about one core summed at every launch. The load average
stood at 11.9 at the training launch (the three development passes had just ended) and 9 to 11 at
the reads (the trainings had just ended). The releases, marks and cells hold held-out problem text
and stay outside the repository. `PRT` and `PRS` were not trained again: their states and reads are
the turned loop's ([TURNS_RUN.md](../2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING_receipts/TURNS_RUN.md)).

## Build and inputs

Built at `bd1b9d936` in its own worktree and target directory. All eleven pinned inputs matched
their digests (`UNITS d0973c39`, `digit/keys_tower.bin fcaadc56`, `train_all.txt 050b94f3`,
`dev.txt e5bffe0e`, `digit/dev.roles a7d7ccdc`, `digit/train800.txt 173c9ac3`, `written/keys.bin
bbe735d7`, `digit/C/STATE 84e2bacf`, `pumped/PP/STATE.0 db9644cd`, `turns/PRT_STATE 26e73cc8`,
`turns/PRT/STATE 3fd26691`).
```text
PROJECTION 122 s (the last builds 121.3 and 118.5 s); DEADLINE 180 s
RUN_RECEIPT exit=0 wall_s=126.1 peak_rss_kib=3552032 user_s=208.5
BINARY_SHA256 12d9386f23e3e47ee6204c4dd583f3de7b30b5302d0c5bfa346cd92de2ac4c02 RUN/strands/solenoidal_alpha
GIT_LOG bd1b9d9362905ad806bd1bed27454466c9a4818a brandonrdug@users.noreply.github.com
```

## The locator on the training partition (`locate-strands train_all.txt … 4`)

Projection 59 s, deadline 120 s.
```text
STRANDS_MENU stretches=26988 groups=437 period=4
STRANDS_HAND context=<*=> stretches=6287 hand=1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=6287 hand=1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=6287 hand=-1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=6287 hand=-1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=3815 hand=1,1 step=1 rank=40 carried=3333 torsion=3:1,11:1,101:1
STRANDS_HAND context=<+=> stretches=3815 hand=1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=3815 hand=-1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=3815 hand=-1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_FIRST context=<+=> stretches=3815 hand=1,1 bytes=0123456789
STRANDS_RING length=1 step=0 modulus=9 multiplier=1 primes=3:9 turns=0,1,2,3,4,5,6,7,8,0
STRANDS_RING length=2 step=1 modulus=99 multiplier=10 primes=3:9,11:11 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_RING length=3 step=1 modulus=999 multiplier=10 primes=3:27,37:37 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_RING length=4 step=1 modulus=9999 multiplier=10 primes=3:9,11:11,101:101 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_UNCARRIED context==-=\x0a stretches=2 hand=1,-1 rank=8 touched=28
STRANDS_UNCARRIED context=\x0a*+* stretches=1 hand=-1,1 rank=4 touched=16
STRANDS_UNCARRIED context=\x20++. stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=\x20+=\x0a stretches=1 hand=1,1 rank=4 touched=16
STRANDS_UNCARRIED context=\x20-/\x20 stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=\x20-=\x0a stretches=1 hand=1,-1 rank=4 touched=16
STRANDS_UNCARRIED context=\x20-=. stretches=1 hand=1,-1 rank=4 touched=12
STRANDS_UNCARRIED context=\x20.*. stretches=1 hand=1,-1 rank=4 touched=12
STRANDS_UNCARRIED context=\x20::, stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=$\x0a*= stretches=1 hand=1,1 rank=4 touched=8
STRANDS_UNCARRIED context=(+=) stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=+++- stretches=1 hand=1,-1 rank=4 touched=16
STRANDS_UNCARRIED context=++/+ stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=++/= stretches=1 hand=1,1 rank=4 touched=8
STRANDS_UNCARRIED context=.=\x0a\x20 stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=/++/ stretches=1 hand=1,-1 rank=4 touched=8
STRANDS_UNCARRIED context=<**+ stretches=1 hand=1,1 rank=4 touched=12
STRANDS_UNCARRIED context=</++ stretches=1 hand=-1,1 rank=4 touched=8
STRANDS_UNCARRIED context==+=\x0a stretches=1 hand=1,1 rank=4 touched=20
STRANDS_CLOSING groups=6 stretches=7368 uncarried=19
STRANDS_GROUP context=<+=> hand=1,1 stretches=3815 rows=3715 beyond=100 digits=8481
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3389 rows=3327 beyond=62 digits=6784
STRANDS_GROUP context=<-=. hand=1,-1 stretches=57 rows=57 beyond=0 digits=131
STRANDS_GROUP context=<+=. hand=1,1 stretches=48 rows=48 beyond=0 digits=107
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=37 rows=37 beyond=0 digits=78
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=22 rows=22 beyond=0 digits=32
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=3715/3715,digits=8419,symbolic=true <-=>:closed=3327/3327,digits=6715,symbolic=true elapsed_ms=539
STRANDS_STREAM_START events=331032 keyed=\x20+-.<=> closed=76 digits=2983 elapsed_ms=565
STRANDS_ASCENT round=1 byte=\x20 key=0,2,3:plus closed=5946 digits=13323 elapsed_ms=1976
STRANDS_ASCENT round=1 byte=. key=1,2,3:kept closed=5946 digits=13323 elapsed_ms=3303
STRANDS_ASCENT round=1 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=4623
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=5950
STRANDS_ASCENT round=1 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=7271
STRANDS_ASCENT round=1 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=8598
STRANDS_ASCENT round=1 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=9950
STRANDS_ASCENT round=2 byte=\x20 key=0,2,3:plus closed=7206 digits=15480 elapsed_ms=11403
STRANDS_ASCENT round=2 byte=. key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=12721
STRANDS_ASCENT round=2 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=14027
STRANDS_ASCENT round=2 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=15323
STRANDS_ASCENT round=2 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=16675
STRANDS_ASCENT round=2 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=18055
STRANDS_ASCENT round=2 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=19439
STRANDS_STREAM context=<+=> rows=3715 closed=3715 digits=8419/8481
STRANDS_STREAM context=<-=> rows=3327 closed=3327 digits=6715/6784
STRANDS_STREAM context=<-=. rows=57 closed=57 digits=130/131
STRANDS_STREAM context=<+=. rows=48 closed=48 digits=106/107
STRANDS_STREAM context=\x20+=\x20 rows=37 closed=37 digits=78/78
STRANDS_STREAM context=\x20-=\x20 rows=22 closed=22 digits=32/32
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=19447
RUN_RECEIPT exit=0 wall_s=19.5 peak_rss_kib=42920 user_s=150.1
```

## The two foundings (`found-unit-rotor-tower … 64 64 256 2 7 4 strands|strands-still`)

Deadline 79.5 s each (the locate's 19.5 s plus 60). Each founding runs the locator again; its
`STRANDS_` lines are the locate's above, byte for byte apart from `elapsed_ms` (checked by `diff`).
The lines that differ:
```text
PRK (law strands):
ROTOR_MENU loops=7368 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=6368 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=434
ROTOR_CLOSURE step=1 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=457
ROTOR_CLOSURE step=2 rows=6764 rank=40 minor_bits=19 torsion=3:2,11:2 carried=33 elapsed_ms=478
ROTOR_CLOSURE step=3 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=503
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=519
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=519
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=519
STRANDS_ASCENT (rounds 1 and 2, the locate's bytes and keys) elapsed_ms=2130 3518 4889 6262 7628 8989 10374 / 11818 13189 14539 15905 17265 18617 19998
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=20006
STRANDS_FOUNDED level=0 first=7 written=12 rings=9:1,99:10,999:10,9999:10 laws=turned,stepped,held comparison=0,1:1,1 keys=\x20=0,2,3:plus +=0,2,-1:flipped -=0,2,-1:kept <=0,2,3:kept ==1,3,3:plus
ROTOR_FOUNDED step=1 law=strands carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2848622 sha256=9110c668883bf5834ed201ee0038e39fc94a853ab6b0f87791f40c64675f594d elapsed_ms=20067
RUN_RECEIPT exit=0 wall_s=20.1 peak_rss_kib=56728 user_s=152.7

PRI (law strands-still):
ROTOR_MENU loops=7368 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=6368 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=407
ROTOR_CLOSURE step=1 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=431
ROTOR_CLOSURE step=2 rows=6764 rank=40 minor_bits=19 torsion=3:2,11:2 carried=33 elapsed_ms=452
ROTOR_CLOSURE step=3 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=474
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=490
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=490
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=490
STRANDS_ASCENT (rounds 1 and 2, the locate's bytes and keys) elapsed_ms=2117 3468 4821 6170 7515 8862 10217 / 11645 13081 14440 15775 17135 18485 19855
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=19862
STRANDS_FOUNDED level=0 first=7 written=12 rings=9:1,99:10,999:10,9999:10 laws=turned,stepped,held comparison=0,1:1,1 keys=none
ROTOR_FOUNDED step=1 law=strands-still carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2848565 sha256=69b42a82600df9533f2c292e190b4eecd26fa1fae9837e8c3f7f4f6688b4ef88 elapsed_ms=19919
RUN_RECEIPT exit=0 wall_s=19.9 peak_rss_kib=55848 user_s=153.1
```

## The development passes, side by side (`digit/train800.txt`, `64 64 256 2 8 128 1 7`)

Deadline 180 s each; all three on the strands binary. `PRT`'s pass writes the same state as the
capture loop's development pass, bit for bit (`62090aa0…`).
```text
PRK FROM 9110c668883bf5834ed201ee0038e39fc94a853ab6b0f87791f40c64675f594d
PRK: TOWER_STATE STATE.0 state_bytes=12447627 state_sha256=d86dbb2197d9b333d2588bf4fd81013d1cb0aef21ed012e27856cd1478efea63
PRK: TOWER_PASS pass=0 train_bits_a_byte=2.880 dev_bits_a_byte=2.490 dev_regions Q=1.853 P=2.835 N=1.858 M=2.499 deposits=155/155 pass_ms=23905 elapsed_ms=23928 train_code=1258896879145 dev_code=1038127494353 grain_bits=20
PRK: TOWER_DONE state_bytes=12447627 state_sha256=d86dbb2197d9b333d2588bf4fd81013d1cb0aef21ed012e27856cd1478efea63 elapsed_ms=23997
PRK: RUN_RECEIPT exit=0 wall_s=24.1 peak_rss_kib=267676 user_s=143.2
PRI FROM 69b42a82600df9533f2c292e190b4eecd26fa1fae9837e8c3f7f4f6688b4ef88
PRI: TOWER_STATE STATE.0 state_bytes=12455130 state_sha256=1817ce2893319b8c0e416dcfc9405dafca6fa152acc80ca8107d1b4d27ced917
PRI: TOWER_PASS pass=0 train_bits_a_byte=2.878 dev_bits_a_byte=2.462 dev_regions Q=1.804 P=2.987 N=1.512 M=2.471 deposits=155/155 pass_ms=23764 elapsed_ms=23787 train_code=1257922832800 dev_code=1026757259817 grain_bits=20
PRI: TOWER_DONE state_bytes=12455130 state_sha256=1817ce2893319b8c0e416dcfc9405dafca6fa152acc80ca8107d1b4d27ced917 elapsed_ms=23847
PRI: RUN_RECEIPT exit=0 wall_s=23.9 peak_rss_kib=268760 user_s=144.2
PRT FROM turns/PRT_STATE 26e73cc8cff47e33182d8b49f86ca5db46bda51a9333f7de03bc14c8c0fda128
PRT: TOWER_STATE STATE.0 state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb
PRT: TOWER_PASS pass=0 train_bits_a_byte=2.907 dev_bits_a_byte=2.503 dev_regions Q=1.805 P=3.021 N=1.536 M=2.513 deposits=155/155 pass_ms=23403 elapsed_ms=23426 train_code=1270417675348 dev_code=1043744519153 grain_bits=20
PRT: TOWER_DONE state_bytes=12714129 state_sha256=62090aa05a89bd2868d7d49d6da0534ad9c0dbf98a25a9b85e1e7a03918fd3fb elapsed_ms=23514
PRT: RUN_RECEIPT exit=0 wall_s=23.7 peak_rss_kib=265472 user_s=142.4
```
Their windows (`section: sections halvings evaluations ms rate`):
```text
PRK 32: 32 27 59 4580 77.6271 | 64: 32 0 32 3665 114.5312 | 96: 32 0 32 3785 118.2812 | 128: 32 0 32 3676 114.8750 | 155: 27 0 27 3067 113.5926 | eta 27/155=0.174194 | h 5155 ms
PRI 32: 32 27 59 4531 76.7966 | 64: 32 0 32 3667 114.5938 | 96: 32 0 32 3735 116.7188 | 128: 32 0 32 3656 114.2500 | 155: 27 0 27 3021 111.8889 | eta 0.174194 | h 5177 ms
PRT 32: 32 14 46 4095 89.0217 | 64: 32 0 32 3699 115.5938 | 96: 32 0 32 3749 117.1562 | 128: 32 0 32 3680 115.0000 | 155: 27 0 27 3076 113.9259 | eta 14/155=0.090323 | h 5127 ms
```

## The projection

`w_PRT` is the largest full-window rate over every measured `PRT` pass, `d` each tower's largest
window rate in the side-by-side passes, `η` the largest halvings a section and `h` the largest
held-out read.
```text
NUMBER w_PRT_of turns/dev_PRT.first.log: 100.0938 from turns/dev_PRT.first.log pass=0 section=64 ms=3203 evaluations=32
NUMBER w_PRT_of turns/dev_PRT.log: 120.5000 from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32
NUMBER w_PRT_of turns/PRT.log: 113.8750 from turns/PRT.log pass=2 section=448 ms=3644 evaluations=32
NUMBER w_PRT_of capture/dev_PRT.log: 112.7812 from capture/dev_PRT.log pass=0 section=96 ms=3609 evaluations=32
NUMBER w_PRT_of strands/dev_PRT.log: 117.1562 from strands/dev_PRT.log pass=0 section=96 ms=3749 evaluations=32
NUMBER w_PRT=120.5000 ms_an_evaluation from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32
NUMBER eta_PRT=0.090323 from turns/dev_PRT.log pass=0 halvings=14 sections=155
NUMBER h_PRT=5317 ms from turns/dev_PRT.log pass=0
NUMBER d_PRK=118.2812 from strands/dev_PRK.log pass=0 section=96 ms=3785 evaluations=32
NUMBER d_PRI=116.7188 from strands/dev_PRI.log pass=0 section=96 ms=3735 evaluations=32
NUMBER d_PRT=117.1562 from strands/dev_PRT.log pass=0 section=96 ms=3749 evaluations=32
NUMBER w_PRK = w_PRT x max(1, d_PRK/d_PRT) = 120.5000 x max(1, 1.009603) = 121.6571 ms_an_evaluation
NUMBER eta_PRK=max(eta_PRT 0.090323, own 0.174194 from strands/dev_PRK.log pass=0 halvings=27 sections=155)=0.174194
NUMBER h_PRK=max(h_PRT 5317, own 5155 from strands/dev_PRK.log pass=0)=5317 ms
PROJECTION_PRK 3 x (1311 x 1.12 x 121.6571 x (1 + 0.174194) + 5317) + 1000 ms = 646.20 s; DEADLINE 647 s; bound 1.12 x 121.6571 = 136.2560 ms an evaluation
NUMBER w_PRI = w_PRT x max(1, d_PRI/d_PRT) = 120.5000 x max(1, 0.996266) = 120.5000 ms_an_evaluation
NUMBER eta_PRI=max(eta_PRT 0.090323, own 0.174194 from strands/dev_PRI.log pass=0 halvings=27 sections=155)=0.174194
NUMBER h_PRI=max(h_PRT 5317, own 5177 from strands/dev_PRI.log pass=0)=5317 ms
PROJECTION_PRI 3 x (1311 x 1.12 x 120.5000 x (1 + 0.174194) + 5317) + 1000 ms = 640.21 s; DEADLINE 641 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation
```

## The training (`train_all.txt`, `dev.txt`, `64 64 256 2 8 128 3 7`), `PRK` and `PRI` together

The guard stopped neither; no window passed its limit. Each guard line is written compactly with
every number kept: `RUN pass section bits_a_byte halvings elapsed_ms | window_sections
window_halvings evaluations ms ms_an_evaluation limit` (the line in full is `RUN: TOWER_SECTION
pass=P section=S bits_a_byte=B deposits=S halvings=H elapsed_ms=T | window sections=n halvings=h
evaluations=E ms=d ms_an_evaluation=r limit=L`); the other lines are whole.
```text
PRK 0 32 3.744 16 3585 | 32 16 48 3585 74.69 6540.3
PRI 0 32 3.573 42 4544 | 32 42 74 4544 61.41 9987.0
PRK 0 64 3.063 16 6900 | 32 0 32 3315 103.59 4360.2
PRI 0 64 2.954 43 7913 | 32 1 33 3369 102.09 4453.7
PRK 0 96 2.766 16 10219 | 32 0 32 3319 103.72 4360.2
PRI 0 96 2.701 43 11244 | 32 0 32 3331 104.09 4318.7
PRK 0 128 2.581 16 13540 | 32 0 32 3321 103.78 4360.2
PRI 0 128 2.537 43 14590 | 32 0 32 3346 104.56 4318.7
PRK 0 160 2.500 16 16786 | 32 0 32 3246 101.44 4360.2
PRI 0 160 2.468 43 17828 | 32 0 32 3238 101.19 4318.7
PRK 0 192 2.396 16 20104 | 32 0 32 3318 103.69 4360.2
PRI 0 192 2.362 43 21161 | 32 0 32 3333 104.16 4318.7
PRK 0 224 2.313 16 23352 | 32 0 32 3248 101.50 4360.2
PRI 0 224 2.280 43 24401 | 32 0 32 3240 101.25 4318.7
PRK 0 256 2.368 16 26618 | 32 0 32 3266 102.06 4360.2
PRI 0 256 2.330 43 27697 | 32 0 32 3296 103.00 4318.7
PRK 0 288 2.288 16 29931 | 32 0 32 3313 103.53 4360.2
PRI 0 288 2.262 43 30953 | 32 0 32 3256 101.75 4318.7
PRK 0 320 2.243 16 33177 | 32 0 32 3246 101.44 4360.2
PRI 0 320 2.199 43 34217 | 32 0 32 3264 102.00 4318.7
PRK 0 352 2.253 16 36471 | 32 0 32 3294 102.94 4360.2
PRI 0 352 2.217 43 37432 | 32 0 32 3215 100.47 4318.7
PRK 0 384 2.256 16 39676 | 32 0 32 3205 100.16 4360.2
PRI 0 384 2.211 43 40635 | 32 0 32 3203 100.09 4318.7
PRK 0 416 2.207 16 42881 | 32 0 32 3205 100.16 4360.2
PRI 0 416 2.173 43 43830 | 32 0 32 3195 99.84 4318.7
PRK 0 448 2.190 16 46101 | 32 0 32 3220 100.62 4360.2
PRI 0 448 2.154 43 47052 | 32 0 32 3222 100.69 4318.7
PRK 0 480 2.172 16 49302 | 32 0 32 3201 100.03 4360.2
PRI 0 480 2.135 43 50244 | 32 0 32 3192 99.75 4318.7
PRK 0 512 2.145 16 52514 | 32 0 32 3212 100.38 4360.2
PRI 0 512 2.109 43 53472 | 32 0 32 3228 100.88 4318.7
PRK 0 544 2.100 16 55749 | 32 0 32 3235 101.09 4360.2
PRI 0 544 2.066 43 56692 | 32 0 32 3220 100.62 4318.7
PRK 0 576 2.151 16 58946 | 32 0 32 3197 99.91 4360.2
PRI 0 576 2.124 43 59900 | 32 0 32 3208 100.25 4318.7
PRK 0 608 2.093 16 62155 | 32 0 32 3209 100.28 4360.2
PRI 0 608 2.064 43 63112 | 32 0 32 3212 100.38 4318.7
PRK 0 640 2.079 16 65361 | 32 0 32 3206 100.19 4360.2
PRI 0 640 2.048 43 66319 | 32 0 32 3207 100.22 4318.7
PRK 0 672 2.084 16 68564 | 32 0 32 3203 100.09 4360.2
PRI 0 672 2.057 43 69523 | 32 0 32 3204 100.12 4318.7
PRK 0 704 2.072 16 71775 | 32 0 32 3211 100.34 4360.2
PRI 0 704 2.043 43 72728 | 32 0 32 3205 100.16 4318.7
PRK 0 736 2.064 16 75012 | 32 0 32 3237 101.16 4360.2
PRI 0 736 2.039 43 75963 | 32 0 32 3235 101.09 4318.7
PRK 0 768 2.047 16 78292 | 32 0 32 3280 102.50 4360.2
PRI 0 768 2.031 43 79236 | 32 0 32 3273 102.28 4318.7
PRK 0 800 2.026 16 81552 | 32 0 32 3260 101.88 4360.2
PRI 0 800 2.003 43 82487 | 32 0 32 3251 101.59 4318.7
PRK 0 832 2.033 16 84738 | 32 0 32 3186 99.56 4360.2
PRI 0 832 2.008 43 85706 | 32 0 32 3219 100.59 4318.7
PRK 0 864 2.025 16 87941 | 32 0 32 3203 100.09 4360.2
PRI 0 864 2.010 43 88939 | 32 0 32 3233 101.03 4318.7
PRK 0 896 2.019 16 91178 | 32 0 32 3237 101.16 4360.2
PRI 0 896 1.996 43 92199 | 32 0 32 3260 101.88 4318.7
PRK 0 928 2.047 16 94437 | 32 0 32 3259 101.84 4360.2
PRI 0 928 2.025 43 95504 | 32 0 32 3305 103.28 4318.7
PRK 0 960 2.010 16 97758 | 32 0 32 3321 103.78 4360.2
PRI 0 960 1.995 43 98786 | 32 0 32 3282 102.56 4318.7
PRK 0 992 2.017 16 101042 | 32 0 32 3284 102.62 4360.2
PRI 0 992 1.994 43 102059 | 32 0 32 3273 102.28 4318.7
PRK 0 1024 1.959 16 104312 | 32 0 32 3270 102.19 4360.2
PRI 0 1024 1.945 43 105339 | 32 0 32 3280 102.50 4318.7
PRK 0 1056 1.973 16 107584 | 32 0 32 3272 102.25 4360.2
PRI 0 1056 1.949 43 108600 | 32 0 32 3261 101.91 4318.7
PRK 0 1088 2.010 16 110820 | 32 0 32 3236 101.12 4360.2
PRI 0 1088 1.993 43 111844 | 32 0 32 3244 101.38 4318.7
PRK 0 1120 1.982 16 114059 | 32 0 32 3239 101.22 4360.2
PRI 0 1120 1.962 43 115091 | 32 0 32 3247 101.47 4318.7
PRK 0 1152 1.988 16 117346 | 32 0 32 3287 102.72 4360.2
PRI 0 1152 1.970 43 118397 | 32 0 32 3306 103.31 4318.7
PRK 0 1184 1.939 16 120625 | 32 0 32 3279 102.47 4360.2
PRI 0 1184 1.920 43 121661 | 32 0 32 3264 102.00 4318.7
PRK 0 1216 1.973 16 123833 | 32 0 32 3208 100.25 4360.2
PRI 0 1216 1.953 43 124891 | 32 0 32 3230 100.94 4318.7
PRK 0 1248 1.938 16 127030 | 32 0 32 3197 99.91 4360.2
PRI 0 1248 1.920 43 128159 | 32 0 32 3268 102.12 4318.7
PRK 0 1280 1.960 16 130298 | 32 0 32 3268 102.12 4360.2
PRI 0 1280 1.944 43 131438 | 32 0 32 3279 102.47 4318.7
PRK 0 1311 1.924 16 133410 | 31 0 31 3112 100.39 4223.9
PRK: TOWER_STATE STATE.0 state_bytes=12447430 state_sha256=a853a7e17655e70e745716cbdd14841bdeb90fec2763223d751b0b243eab6706
PRI 0 1311 1.905 43 134626 | 31 0 31 3188 102.84 4183.8
PRI: TOWER_STATE STATE.0 state_bytes=12384519 state_sha256=ef5983602b8e3401522356ff07923a70f9e2991b50c68f1900cab6b49033f62b
PRK: TOWER_PASS pass=0 train_bits_a_byte=2.195 dev_bits_a_byte=1.961 dev_regions Q=1.406 P=2.504 N=0.662 M=1.969 deposits=1311/1311 pass_ms=137825 elapsed_ms=137843 train_code=8120056293627 dev_code=817714326682 grain_bits=20
PRI: TOWER_PASS pass=0 train_bits_a_byte=2.162 dev_bits_a_byte=1.948 dev_regions Q=1.422 P=2.513 N=0.607 M=1.956 deposits=1311/1311 pass_ms=139099 elapsed_ms=139118 train_code=7996309784806 dev_code=812345286200 grain_bits=20
PRK 1 32 1.930 0 141144 | 32 0 32 3301 103.16 4360.2
PRI 1 32 1.904 0 142395 | 32 0 32 3277 102.41 4318.7
PRK 1 64 1.920 0 144365 | 32 0 32 3221 100.66 4360.2
PRI 1 64 1.897 0 145588 | 32 0 32 3193 99.78 4318.7
PRK 1 96 1.945 0 147620 | 32 0 32 3255 101.72 4360.2
PRI 1 96 1.923 0 148816 | 32 0 32 3228 100.88 4318.7
PRK 1 128 1.908 0 150882 | 32 0 32 3262 101.94 4360.2
PRI 1 128 1.892 0 152039 | 32 0 32 3223 100.72 4318.7
PRK 1 160 1.921 0 154119 | 32 0 32 3237 101.16 4360.2
PRI 1 160 1.904 0 155305 | 32 0 32 3266 102.06 4318.7
PRK 1 192 1.894 0 157417 | 32 0 32 3298 103.06 4360.2
PRI 1 192 1.879 0 158617 | 32 0 32 3312 103.50 4318.7
PRK 1 224 1.840 0 160735 | 32 0 32 3318 103.69 4360.2
PRI 1 224 1.820 0 161859 | 32 0 32 3242 101.31 4318.7
PRK 1 256 1.938 0 163975 | 32 0 32 3240 101.25 4360.2
PRI 1 256 1.927 0 165107 | 32 0 32 3248 101.50 4318.7
PRK 1 288 1.898 0 167243 | 32 0 32 3268 102.12 4360.2
PRI 1 288 1.884 0 168302 | 32 0 32 3195 99.84 4318.7
PRK 1 320 1.863 0 170428 | 32 0 32 3185 99.53 4360.2
PRI 1 320 1.854 0 171463 | 32 0 32 3161 98.78 4318.7
PRK 1 352 1.895 0 173590 | 32 0 32 3162 98.81 4360.2
PRI 1 352 1.880 0 174653 | 32 0 32 3190 99.69 4318.7
PRK 1 384 1.906 0 176779 | 32 0 32 3189 99.66 4360.2
PRI 1 384 1.888 0 177889 | 32 0 32 3236 101.12 4318.7
PRK 1 416 1.875 0 179987 | 32 0 32 3208 100.25 4360.2
PRI 1 416 1.862 0 181113 | 32 0 32 3224 100.75 4318.7
PRK 1 448 1.885 0 183221 | 32 0 32 3234 101.06 4360.2
PRI 1 448 1.867 0 184338 | 32 0 32 3225 100.78 4318.7
PRK 1 480 1.875 0 186429 | 32 0 32 3208 100.25 4360.2
PRI 1 480 1.857 0 187533 | 32 0 32 3195 99.84 4318.7
PRK 1 512 1.869 0 189646 | 32 0 32 3217 100.53 4360.2
PRI 1 512 1.847 0 190745 | 32 0 32 3212 100.38 4318.7
PRK 1 544 1.825 0 192824 | 32 0 32 3178 99.31 4360.2
PRI 1 544 1.807 0 193911 | 32 0 32 3166 98.94 4318.7
PRK 1 576 1.883 0 196031 | 32 0 32 3207 100.22 4360.2
PRI 1 576 1.869 0 197150 | 32 0 32 3239 101.22 4318.7
PRK 1 608 1.847 0 199243 | 32 0 32 3212 100.38 4360.2
PRI 1 608 1.829 0 200370 | 32 0 32 3220 100.62 4318.7
PRK 1 640 1.845 0 202484 | 32 0 32 3241 101.28 4360.2
PRI 1 640 1.828 0 203593 | 32 0 32 3223 100.72 4318.7
PRK 1 672 1.851 0 205699 | 32 0 32 3215 100.47 4360.2
PRI 1 672 1.838 0 206812 | 32 0 32 3219 100.59 4318.7
PRK 1 704 1.844 0 208912 | 32 0 32 3213 100.41 4360.2
PRI 1 704 1.843 0 210021 | 32 0 32 3209 100.28 4318.7
PRK 1 736 1.842 0 212129 | 32 0 32 3217 100.53 4360.2
PRI 1 736 2.331 29 214244 | 32 29 61 4223 69.23 8232.6
PRK 1 768 1.837 0 215330 | 32 0 32 3201 100.03 4360.2
PRI 1 768 2.049 29 217442 | 32 0 32 3198 99.94 4318.7
PRK 1 800 1.814 0 218470 | 32 0 32 3140 98.12 4360.2
PRI 1 800 1.915 29 220597 | 32 0 32 3155 98.59 4318.7
PRK 1 832 1.824 0 221654 | 32 0 32 3184 99.50 4360.2
PRI 1 832 1.898 29 223758 | 32 0 32 3161 98.78 4318.7
PRK 1 864 1.828 0 224845 | 32 0 32 3191 99.72 4360.2
PRI 1 864 1.872 29 227033 | 32 0 32 3275 102.34 4318.7
PRK 1 896 1.836 0 228096 | 32 0 32 3251 101.59 4360.2
PRI 1 896 1.856 29 230221 | 32 0 32 3188 99.62 4318.7
PRK 1 928 1.857 0 231285 | 32 0 32 3189 99.66 4360.2
PRI 1 928 1.876 29 233368 | 32 0 32 3147 98.34 4318.7
PRK 1 960 1.835 0 234444 | 32 0 32 3159 98.72 4360.2
PRI 1 960 1.843 29 236513 | 32 0 32 3145 98.28 4318.7
PRK 1 992 1.831 0 237562 | 32 0 32 3118 97.44 4360.2
PRI 1 992 1.838 29 239635 | 32 0 32 3122 97.56 4318.7
PRK 1 1024 1.790 0 240670 | 32 0 32 3108 97.12 4360.2
PRI 1 1024 1.795 29 242756 | 32 0 32 3121 97.53 4318.7
PRK 1 1056 1.820 0 243774 | 32 0 32 3104 97.00 4360.2
PRI 1 1056 1.806 29 245932 | 32 0 32 3176 99.25 4318.7
PRK 1 1088 1.843 0 247007 | 32 0 32 3233 101.03 4360.2
PRI 1 1088 1.837 29 249262 | 32 0 32 3330 104.06 4318.7
PRK 1 1120 1.826 0 250295 | 32 0 32 3288 102.75 4360.2
PRI 1 1120 1.815 29 252527 | 32 0 32 3265 102.03 4318.7
PRK 1 1152 1.835 0 253514 | 32 0 32 3219 100.59 4360.2
PRI 1 1152 1.825 29 255743 | 32 0 32 3216 100.50 4318.7
PRK 1 1184 1.797 0 256671 | 32 0 32 3157 98.66 4360.2
PRI 1 1184 1.779 29 259015 | 32 0 32 3272 102.25 4318.7
PRK 1 1216 1.822 0 259894 | 32 0 32 3223 100.72 4360.2
PRI 1 1216 1.813 29 262142 | 32 0 32 3127 97.72 4318.7
PRK 1 1248 1.798 0 263016 | 32 0 32 3122 97.56 4360.2
PRI 1 1248 1.779 29 265346 | 32 0 32 3204 100.12 4318.7
PRK 1 1280 1.817 0 266207 | 32 0 32 3191 99.72 4360.2
PRI 1 1280 1.802 29 268526 | 32 0 32 3180 99.38 4318.7
PRK 1 1311 1.792 0 269274 | 31 0 31 3067 98.94 4223.9
PRK: TOWER_STATE STATE.1 state_bytes=12379616 state_sha256=d275d2c0369d5ec5d88f81ff217887b3a24308b54ea4dcdcf0ea732afe51e819
PRI 1 1311 1.774 29 271695 | 31 0 31 3169 102.23 4183.8
PRI: TOWER_STATE STATE.1 state_bytes=12481209 state_sha256=7d01e0a122aefae41a22a1600f8e136a8576f5d7c6fd74c7ce9ecc7d47113f6f
PRK: TOWER_PASS pass=1 train_bits_a_byte=1.856 dev_bits_a_byte=1.837 dev_regions Q=1.306 P=2.343 N=0.570 M=1.845 deposits=1311/1311 pass_ms=135753 elapsed_ms=273596 train_code=6865475176791 dev_code=766059832832 grain_bits=20
PRI: TOWER_PASS pass=1 train_bits_a_byte=1.868 dev_bits_a_byte=1.828 dev_regions Q=1.297 P=2.408 N=0.434 M=1.836 deposits=1311/1311 pass_ms=136841 elapsed_ms=275960 train_code=6910517362266 dev_code=762368542565 grain_bits=20
PRK 2 32 1.798 0 276792 | 32 0 32 3196 99.88 4360.2
PRI 2 32 1.779 0 279073 | 32 0 32 3113 97.28 4318.7
PRK 2 64 1.796 0 279897 | 32 0 32 3105 97.03 4360.2
PRI 2 64 1.772 0 282167 | 32 0 32 3094 96.69 4318.7
PRK 2 96 1.814 0 283005 | 32 0 32 3108 97.12 4360.2
PRI 2 96 1.799 0 285341 | 32 0 32 3174 99.19 4318.7
PRK 2 128 1.789 0 286174 | 32 0 32 3169 99.03 4360.2
PRI 2 128 1.774 0 288508 | 32 0 32 3167 98.97 4318.7
PRK 2 160 1.802 0 289373 | 32 0 32 3199 99.97 4360.2
PRI 2 160 1.793 0 291690 | 32 0 32 3182 99.44 4318.7
PRK 2 192 1.776 0 292534 | 32 0 32 3161 98.78 4360.2
PRI 2 192 1.766 0 294862 | 32 0 32 3172 99.12 4318.7
PRK 2 224 1.717 0 295653 | 32 0 32 3119 97.47 4360.2
PRI 2 224 1.710 0 297997 | 32 0 32 3135 97.97 4318.7
PRK 2 256 1.828 0 298780 | 32 0 32 3127 97.72 4360.2
PRI 2 256 1.819 0 301165 | 32 0 32 3168 99.00 4318.7
PRK 2 288 1.786 0 301901 | 32 0 32 3121 97.53 4360.2
PRI 2 288 1.776 0 304348 | 32 0 32 3183 99.47 4318.7
PRK 2 320 1.757 0 305050 | 32 0 32 3149 98.41 4360.2
PRI 2 320 1.755 0 307508 | 32 0 32 3160 98.75 4318.7
PRK 2 352 1.793 0 308198 | 32 0 32 3148 98.38 4360.2
PRI 2 352 1.776 0 310670 | 32 0 32 3162 98.81 4318.7
PRK 2 384 1.801 0 311384 | 32 0 32 3186 99.56 4360.2
PRI 2 384 1.787 0 313851 | 32 0 32 3181 99.41 4318.7
PRK 2 416 1.770 0 314544 | 32 0 32 3160 98.75 4360.2
PRI 2 416 1.760 0 317000 | 32 0 32 3149 98.41 4318.7
PRK 2 448 1.782 0 317689 | 32 0 32 3145 98.28 4360.2
PRI 2 448 1.781 0 320167 | 32 0 32 3167 98.97 4318.7
PRK 2 480 1.773 0 320791 | 32 0 32 3102 96.94 4360.2
PRI 2 480 1.765 0 323238 | 32 0 32 3071 95.97 4318.7
PRK 2 512 1.769 0 323903 | 32 0 32 3112 97.25 4360.2
PRI 2 512 1.762 0 326452 | 32 0 32 3214 100.44 4318.7
PRK 2 544 1.728 0 327060 | 32 0 32 3157 98.66 4360.2
PRI 2 544 1.720 0 329691 | 32 0 32 3239 101.22 4318.7
PRK 2 576 1.785 0 330293 | 32 0 32 3233 101.03 4360.2
PRI 2 576 1.776 0 332874 | 32 0 32 3183 99.47 4318.7
PRK 2 608 1.753 0 333446 | 32 0 32 3153 98.53 4360.2
PRI 2 608 1.746 0 335993 | 32 0 32 3119 97.47 4318.7
PRK 2 640 1.751 0 336590 | 32 0 32 3144 98.25 4360.2
PRI 2 640 1.751 0 339179 | 32 0 32 3186 99.56 4318.7
PRK 2 672 1.761 0 339781 | 32 0 32 3191 99.72 4360.2
PRI 2 672 1.760 0 342338 | 32 0 32 3159 98.72 4318.7
PRK 2 704 1.759 0 342933 | 32 0 32 3152 98.50 4360.2
PRI 2 704 1.755 0 345473 | 32 0 32 3135 97.97 4318.7
PRK 2 736 1.748 0 346080 | 32 0 32 3147 98.34 4360.2
PRI 2 736 1.765 0 348601 | 32 0 32 3128 97.75 4318.7
PRK 2 768 1.750 0 349214 | 32 0 32 3134 97.94 4360.2
PRI 2 768 1.768 0 351766 | 32 0 32 3165 98.91 4318.7
PRK 2 800 1.731 0 352355 | 32 0 32 3141 98.16 4360.2
PRI 2 800 1.752 0 354958 | 32 0 32 3192 99.75 4318.7
PRK 2 832 1.746 0 355552 | 32 0 32 3197 99.91 4360.2
PRI 2 832 1.760 0 358137 | 32 0 32 3179 99.34 4318.7
PRK 2 864 1.745 0 358719 | 32 0 32 3167 98.97 4360.2
PRI 2 864 1.763 0 361254 | 32 0 32 3117 97.41 4318.7
PRK 2 896 1.750 0 361798 | 32 0 32 3079 96.22 4360.2
PRI 2 896 1.771 0 364342 | 32 0 32 3088 96.50 4318.7
PRK 2 928 1.773 0 364881 | 32 0 32 3083 96.34 4360.2
PRI 2 928 1.799 0 367455 | 32 0 32 3113 97.28 4318.7
PRK 2 960 1.752 0 368007 | 32 0 32 3126 97.69 4360.2
PRI 2 960 1.762 0 370575 | 32 0 32 3120 97.50 4318.7
PRK 2 992 1.751 0 371135 | 32 0 32 3128 97.75 4360.2
PRI 2 992 1.772 0 373693 | 32 0 32 3118 97.44 4318.7
PRK 2 1024 1.709 0 374245 | 32 0 32 3110 97.19 4360.2
PRI 2 1024 1.737 0 376840 | 32 0 32 3147 98.34 4318.7
PRK 2 1056 1.745 0 377411 | 32 0 32 3166 98.94 4360.2
PRI 2 1056 1.744 0 379976 | 32 0 32 3136 98.00 4318.7
PRK 2 1088 1.768 0 380507 | 32 0 32 3096 96.75 4360.2
PRI 2 1088 1.784 0 383055 | 32 0 32 3079 96.22 4318.7
PRK 2 1120 1.754 0 383588 | 32 0 32 3081 96.28 4360.2
PRI 2 1120 1.770 0 386168 | 32 0 32 3113 97.28 4318.7
PRK 2 1152 1.759 0 386706 | 32 0 32 3118 97.44 4360.2
PRI 2 1152 1.776 0 389264 | 32 0 32 3096 96.75 4318.7
PRK 2 1184 1.729 0 389796 | 32 0 32 3090 96.56 4360.2
PRI 2 1184 1.731 0 392352 | 32 0 32 3088 96.50 4318.7
PRK 2 1216 1.754 0 392897 | 32 0 32 3101 96.91 4360.2
PRI 2 1216 1.768 0 395474 | 32 0 32 3122 97.56 4318.7
PRK 2 1248 1.721 0 396001 | 32 0 32 3104 97.00 4360.2
PRI 2 1248 1.739 0 398634 | 32 0 32 3160 98.75 4318.7
PRK 2 1280 1.746 0 399141 | 32 0 32 3140 98.12 4360.2
PRI 2 1280 1.757 0 401788 | 32 0 32 3154 98.56 4318.7
PRK 2 1311 1.725 0 402174 | 31 0 31 3033 97.84 4223.9
PRK: TOWER_STATE STATE.2 state_bytes=12360080 state_sha256=01feb781d096d4e3c05fa625d520e9d81908a11bac415d9bb5e7f08b904a52c1
PRI 2 1311 1.732 0 404926 | 31 0 31 3138 101.23 4183.8
PRI: TOWER_STATE STATE.2 state_bytes=12362151 state_sha256=9992ecc863746226b9be92cf4cd9d849d31dcc7db017cca85bda74c08ea19546
PRK: TOWER_PASS pass=2 train_bits_a_byte=1.762 dev_bits_a_byte=1.782 dev_regions Q=1.246 P=2.357 N=0.499 M=1.790 deposits=1311/1311 pass_ms=132723 elapsed_ms=406320 train_code=6517430744646 dev_code=742964337477 grain_bits=20
PRK: TOWER_DONE state_bytes=12360080 state_sha256=01feb781d096d4e3c05fa625d520e9d81908a11bac415d9bb5e7f08b904a52c1 elapsed_ms=406379
PRK: RUN_RECEIPT exit=0 wall_s=406.8 peak_rss_kib=294868 user_s=2435.9
PRI: TOWER_PASS pass=2 train_bits_a_byte=1.764 dev_bits_a_byte=1.797 dev_regions Q=1.268 P=2.396 N=0.414 M=1.805 deposits=1311/1311 pass_ms=132825 elapsed_ms=408786 train_code=6525161314055 dev_code=749171314075 grain_bits=20
PRI: TOWER_DONE state_bytes=12362151 state_sha256=9992ecc863746226b9be92cf4cd9d849d31dcc7db017cca85bda74c08ea19546 elapsed_ms=408862
PRI: RUN_RECEIPT exit=0 wall_s=409.3 peak_rss_kib=308604 user_s=2448.3
```

## The written reads (`read-unit-tower-written … written/keys.bin 400 1 64 8`, `dev.txt`)

Deadline 30 s each, with the stop line at 3,300 ms for 64 problems (the turned loop's read took
17.8 s).
```text
PRK FROM strands/PRK/STATE 01feb781d096d4e3c05fa625d520e9d81908a11bac415d9bb5e7f08b904a52c1
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=61
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299741 prompt_units=468588 released_units=115310 most_units_a_problem=4699 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=16808
TOWER_WRITTEN_FILES free_sha256=c05b99e5cebffbf987fd8c6500dc81368df20f5c7984616549bd463971644177 marks_sha256=20d2ae7a1688fd39511a7469a59c4243853ebb95d0d19cba800d0dcd93288dbf
RUN_RECEIPT exit=0 wall_s=16.8 peak_rss_kib=42776 user_s=132.0
READ_GUARD ok progress 64 by 1605 ms
PRI FROM strands/PRI/STATE 9992ecc863746226b9be92cf4cd9d849d31dcc7db017cca85bda74c08ea19546
TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=45
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299736 prompt_units=468588 released_units=115060 most_units_a_problem=4701 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=16735
TOWER_WRITTEN_FILES free_sha256=0e23ec1f197b754008820bd34fc90572ada70337d9ddaa5a7c320001004b95eb marks_sha256=5e8fabb32372863530743ad5d41633f679e4a3337623e7e4c3e95cd33609d7f4
RUN_RECEIPT exit=0 wall_s=16.8 peak_rss_kib=46796 user_s=132.2
READ_GUARD ok progress 64 by 1555 ms
```

## The rules (`tools/gsm8k/written_rules.py`, `dev.txt` held, `train_all.txt`)

`timeout 60` each. The seven `WRITTEN` lines are the same in every rules run.
```text
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
WRITTEN dir=turns/read_PRT problems=747 a_on_problem=59 b_free_calculations=1543 b_free_right=58 c_first_calculations=673 c_from_question=19 b_equals=240/2448 met=216/1572 never_met=24/876 binary +=26/470 -=28/388 *=124/897 /=46/343
WRITTEN dir=turns/read_PRS problems=747 a_on_problem=41 b_free_calculations=1557 b_free_right=69 c_first_calculations=685 c_from_question=34 b_equals=288/2448 met=269/1572 never_met=19/876 binary +=29/470 -=24/388 *=169/897 /=48/343
WRITTEN dir=strands/read_PRK problems=747 a_on_problem=49 b_free_calculations=1586 b_free_right=72 c_first_calculations=697 c_from_question=33 b_equals=230/2448 met=214/1572 never_met=16/876 binary +=24/470 -=20/388 *=138/897 /=32/343
WRITTEN dir=strands/read_PRI problems=747 a_on_problem=40 b_free_calculations=1332 b_free_right=64 c_first_calculations=660 c_from_question=28 b_equals=214/2448 met=192/1572 never_met=22/876 binary +=24/470 -=23/388 *=111/897 /=36/343
RINGS dir=digit/read_C n=312 mod9=44 foil9=39 mod10=109 foil10=76 mod11=30 foil11=26 mod990=6 foil990=1
RINGS dir=rotor/read_PP n=312 mod9=39 foil9=32 mod10=113 foil10=84 mod11=23 foil11=23 mod990=3 foil990=1
RINGS dir=rotor/read_PR n=312 mod9=32 foil9=35 mod10=123 foil10=88 mod11=27 foil11=30 mod990=4 foil990=4
RINGS dir=turns/read_PRT n=312 mod9=45 foil9=25 mod10=122 foil10=76 mod11=37 foil11=23 mod990=7 foil990=1
RINGS dir=turns/read_PRS n=312 mod9=35 foil9=22 mod10=132 foil10=95 mod11=20 foil11=21 mod990=2 foil990=4
RINGS dir=strands/read_PRK n=312 mod9=40 foil9=34 mod10=133 foil10=86 mod11=33 foil11=24 mod990=4 foil990=1
RINGS dir=strands/read_PRI n=312 mod9=50 foil9=33 mod10=128 foil10=92 mod11=21 foil11=26 mod990=3 foil990=2
HEARD dir=turns/read_PRT 0=24/876 1=8/239 2-3=16/224 4-7=9/255 8-15=42/326 16+=141/528
HEARD dir=strands/read_PRK 0=16/876 1=10/239 2-3=12/224 4-7=8/255 8-15=42/326 16+=142/528
HEARD dir=strands/read_PRI 0=22/876 1=11/239 2-3=16/224 4-7=10/255 8-15=25/326 16+=130/528
pair PRK PRT: PAIRED met_only_a=93 met_only_b=95 met_both=121 never_only_a=14 never_only_b=22 never_both=2
pair PRK PRI: PAIRED met_only_a=97 met_only_b=75 met_both=117 never_only_a=9 never_only_b=15 never_both=7
pair PRI PRT: PAIRED met_only_a=84 met_only_b=108 met_both=108 never_only_a=17 never_only_b=19 never_both=5
```
The gaps read, every set of every release:
```text
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
GAPS dir=strands/read_PRK set=all n=2448 right=230 wrong=2218 unfinished=7 not_number=0 unread=0 numbers=2211
GAP_SIZE dir=strands/read_PRK set=all n=2211 x2=1085 x10=2017 tenth=54 opposite_sign=0 smaller=1447 larger=764 digits=1279 foil_digits=865/2173
GAP_RINGS dir=strands/read_PRK set=all n=2161 mod9=219 foil9=257/2123 mod10=799 foil10=584/2123 mod11=100 foil11=158/2123 mod7=186 foil7=294/2123 mod13=102 foil13=124/2123
GAP_FROM dir=strands/read_PRK set=all n=2211 heard_result=2207 operand=227 other_operation=74/1878
GAP_WRITES dir=strands/read_PRK set=all written=2441 distinct=96 top10=1565 commonest=8:334:33
GAP_LENGTH dir=strands/read_PRK set=all 1=107/485 2=94/1252 3=29/508 4=0/139 5+=0/64
GAPS dir=strands/read_PRK set=met n=1572 right=214 wrong=1358 unfinished=4 not_number=0 unread=0 numbers=1354
GAP_SIZE dir=strands/read_PRK set=met n=1354 x2=792 x10=1302 tenth=31 opposite_sign=0 smaller=858 larger=496 digits=880 foil_digits=534/1321
GAP_RINGS dir=strands/read_PRK set=met n=1345 mod9=124 foil9=150/1312 mod10=484 foil10=327/1312 mod11=35 foil11=95/1312 mod7=101 foil7=192/1312 mod13=47 foil13=80/1312
GAP_FROM dir=strands/read_PRK set=met n=1354 heard_result=1354 operand=166 other_operation=69/1286
GAP_WRITES dir=strands/read_PRK set=met written=1568 distinct=66 top10=1115 commonest=8:227:31
GAP_LENGTH dir=strands/read_PRK set=met 1=100/383 2=89/878 3=25/264 4=0/44 5+=0/3
GAPS dir=strands/read_PRK set=never n=876 right=16 wrong=860 unfinished=3 not_number=0 unread=0 numbers=857
GAP_SIZE dir=strands/read_PRK set=never n=857 x2=293 x10=715 tenth=23 opposite_sign=0 smaller=589 larger=268 digits=399 foil_digits=285/852
GAP_RINGS dir=strands/read_PRK set=never n=816 mod9=95 foil9=85/811 mod10=315 foil10=214/811 mod11=65 foil11=59/811 mod7=85 foil7=106/811 mod13=55 foil13=61/811
GAP_FROM dir=strands/read_PRK set=never n=857 heard_result=853 operand=61 other_operation=5/592
GAP_WRITES dir=strands/read_PRK set=never written=873 distinct=79 top10=537 commonest=150:120:4
GAP_LENGTH dir=strands/read_PRK set=never 1=7/102 2=5/374 3=4/244 4=0/95 5+=0/61
GAPS dir=strands/read_PRI set=all n=2448 right=214 wrong=2234 unfinished=12 not_number=2 unread=0 numbers=2220
GAP_SIZE dir=strands/read_PRI set=all n=2220 x2=1139 x10=2048 tenth=53 opposite_sign=0 smaller=1314 larger=906 digits=1332 foil_digits=846/2188
GAP_RINGS dir=strands/read_PRI set=all n=2175 mod9=195 foil9=245/2143 mod10=802 foil10=615/2143 mod11=86 foil11=148/2143 mod7=200 foil7=274/2143 mod13=69 foil13=115/2143
GAP_FROM dir=strands/read_PRI set=all n=2220 heard_result=2186 operand=210 other_operation=88/1895
GAP_WRITES dir=strands/read_PRI set=all written=2434 distinct=95 top10=1632 commonest=8:488:45
GAP_LENGTH dir=strands/read_PRI set=all 1=104/485 2=84/1252 3=23/508 4=3/139 5+=0/64
GAPS dir=strands/read_PRI set=met n=1572 right=192 wrong=1380 unfinished=1 not_number=1 unread=0 numbers=1378
GAP_SIZE dir=strands/read_PRI set=met n=1378 x2=835 x10=1342 tenth=24 opposite_sign=0 smaller=861 larger=517 digits=903 foil_digits=546/1352
GAP_RINGS dir=strands/read_PRI set=met n=1372 mod9=106 foil9=149/1346 mod10=491 foil10=361/1346 mod11=34 foil11=79/1346 mod7=99 foil7=160/1346 mod13=27 foil13=83/1346
GAP_FROM dir=strands/read_PRI set=met n=1378 heard_result=1372 operand=160 other_operation=78/1307
GAP_WRITES dir=strands/read_PRI set=met written=1570 distinct=61 top10=1176 commonest=8:380:41
GAP_LENGTH dir=strands/read_PRI set=met 1=94/383 2=80/878 3=16/264 4=2/44 5+=0/3
GAPS dir=strands/read_PRI set=never n=876 right=22 wrong=854 unfinished=11 not_number=1 unread=0 numbers=842
GAP_SIZE dir=strands/read_PRI set=never n=842 x2=304 x10=706 tenth=29 opposite_sign=0 smaller=453 larger=389 digits=429 foil_digits=251/839
GAP_RINGS dir=strands/read_PRI set=never n=803 mod9=89 foil9=93/800 mod10=311 foil10=241/800 mod11=52 foil11=57/800 mod7=101 foil7=119/800 mod13=42 foil13=59/800
GAP_FROM dir=strands/read_PRI set=never n=842 heard_result=814 operand=50 other_operation=10/588
GAP_WRITES dir=strands/read_PRI set=never written=864 distinct=86 top10=524 commonest=8:108:4
GAP_LENGTH dir=strands/read_PRI set=never 1=10/102 2=4/374 3=7/244 4=1/95 5+=0/61
```
Rules receipts: rings `exit=0 wall_s=16.9 peak_rss_kib=62084`; heard `7.0 s, 60552`; the three pairs
`4.8, 4.7, 4.6 s`, about `61000`; gaps `16.3 s, 61592`.

## The level read (`read-unit-at`, then `tools/gsm8k/numeral_rings.py probe … 2 64`)

The level cells at the held and training places of each final state (`dev.txt` held, `train_all.txt`
training), 2 levels of 64 modes:
```text
UNIT_AT PRK held equals: problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=2057884b6a3917be8d8efb28ccced9f596868acf777e647dfc267d26cfa81ca7 elapsed_ms=3576 (wall_s=3.6 peak_rss_kib=40432)
UNIT_AT PRK held numerals: problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=fe9ecf8cd99dad3039c0392d9f93c435251893f40007db3fbfb53835ecffc332 elapsed_ms=2739 (wall_s=2.8 peak_rss_kib=41272)
UNIT_AT PRK train equals: problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=bedf1af83958736ff4c2e04b47b19c8b72af2a01461f9f84f20a808c364575e2 elapsed_ms=8126 (wall_s=8.2 peak_rss_kib=39196)
UNIT_AT PRK train numerals: problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=747015f6c9f7b56f4b51efbc266c3d239b84c5de90e8f23456951a894654e75c elapsed_ms=6685 (wall_s=6.7 peak_rss_kib=81232)
UNIT_AT PRI held equals: problems=747 places=841 levels=2 modes=64 bytes=1725732 sha256=0da975179f9f73c658e7c60cfed190e0f867ec6556e2e6d85c21f3155976b482 elapsed_ms=3436 (wall_s=3.5 peak_rss_kib=38548)
UNIT_AT PRI held numerals: problems=747 places=3810 levels=2 modes=64 bytes=7818120 sha256=59efb1dbd1dc70eff6d61afde3639e26d3050769d4e422b6609863dbac54444f elapsed_ms=2819 (wall_s=2.8 peak_rss_kib=40952)
UNIT_AT PRI train equals: problems=6730 places=2200 levels=2 modes=64 bytes=4514400 sha256=56c7f91ea327ebfd23dd29b1d5562925e8f8b24f29c185b29824d5fffae3ace5 elapsed_ms=8196 (wall_s=8.2 peak_rss_kib=38920)
UNIT_AT PRI train numerals: problems=6730 places=10792 levels=2 modes=64 bytes=22145184 sha256=0f404cd4d8c484bda87a66f33b9a7bfd686da033638788bce11face09c4015e7 elapsed_ms=6689 (wall_s=6.7 peak_rss_kib=81524)
```
The probe, written compactly: each entry is `label level mod: modes energy majority suffix foil`, the
fields of one line `NUMERAL_RINGS cells=strands/at_X_held_KIND kind=KIND label=L level=V mod=M
held=H train=T modes=.. energy=.. majority=.. suffix=.. foil=..`; the equals have held 841 and
training 2200 places, the numerals 3810 and 10792.
```text
PRK numerals (wall_s=13.9 peak_rss_kib=323228)
numeral 0 9: 1052 739 637 1530 443 | 0 10: 2599 886 3079 3800 1953 | 0 11: 992 534 599 1518 360 | 0 7: 1068 697 827 1574 549 | 0 13: 851 498 562 1491 306 | 0 100: 1160 101 1772 3800 437
numeral 1 9: 611 492 637 1530 443 | 1 10: 1701 1614 3079 3800 1467 | 1 11: 598 454 599 1518 291 | 1 7: 830 653 827 1574 549 | 1 13: 539 442 562 1491 320 | 1 100: 343 86 1772 3800 168
PRI numerals (wall_s=13.5 peak_rss_kib=322064)
numeral 0 9: 681 691 637 1530 494 | 0 10: 1575 1286 3079 3800 1234 | 0 11: 625 565 599 1518 454 | 0 7: 716 633 827 1574 688 | 0 13: 649 513 562 1491 357 | 0 100: 711 280 1772 3800 432
numeral 1 9: 643 411 637 1530 448 | 1 10: 987 349 3079 3800 765 | 1 11: 593 486 599 1518 307 | 1 7: 787 518 827 1574 522 | 1 13: 511 243 562 1491 289 | 1 100: 223 69 1772 3800 73
PRK equals (wall_s=8.2 peak_rss_kib=79552)
a 0 9: 138 112 143 620 91 | a 0 10: 335 286 426 837 177 | a 0 11: 119 99 70 625 66 | a 0 7: 130 153 138 628 122 | a 0 13: 111 96 75 614 57 | a 0 100: 126 80 134 837 22
b 0 9: 272 277 134 676 93 | b 0 10: 570 445 306 839 150 | b 0 11: 316 265 99 677 103 | b 0 7: 325 276 141 673 118 | b 0 13: 304 252 103 681 60 | b 0 100: 419 371 85 839 29
result 0 9: 146 138 92 615 97 | result 0 10: 312 272 304 840 137 | result 0 11: 136 133 80 612 70 | result 0 7: 132 156 133 627 118 | result 0 13: 100 109 68 609 68 | result 0 100: 124 128 88 840 22
a 1 9: 146 119 143 620 94 | a 1 10: 317 230 426 837 194 | a 1 11: 107 79 70 625 76 | a 1 7: 125 119 138 628 114 | a 1 13: 93 51 75 614 59 | a 1 100: 115 11 134 837 26
b 1 9: 211 117 134 676 103 | b 1 10: 501 99 306 839 168 | b 1 11: 223 75 99 677 60 | b 1 7: 252 114 141 673 112 | b 1 13: 207 65 103 681 48 | b 1 100: 301 38 85 839 32
result 1 9: 126 91 92 615 92 | result 1 10: 273 74 304 840 138 | result 1 11: 102 81 80 612 70 | result 1 7: 149 123 133 627 125 | result 1 13: 106 65 68 609 65 | result 1 100: 108 6 88 840 17
PRI equals (wall_s=8.1 peak_rss_kib=79300)
a 0 9: 81 81 143 620 84 | a 0 10: 203 60 426 837 126 | a 0 11: 97 102 70 625 61 | a 0 7: 124 113 138 628 108 | a 0 13: 103 89 75 614 66 | a 0 100: 18 19 134 837 1
b 0 9: 239 228 134 676 102 | b 0 10: 343 302 306 839 88 | b 0 11: 261 264 99 677 105 | b 0 7: 316 288 141 673 132 | b 0 13: 291 313 103 681 65 | b 0 100: 240 256 85 839 9
result 0 9: 121 118 92 615 92 | result 0 10: 266 163 304 840 127 | result 0 11: 122 106 80 612 67 | result 0 7: 161 126 133 627 115 | result 0 13: 82 79 68 609 70 | result 0 100: 60 37 88 840 13
a 1 9: 143 110 143 620 81 | a 1 10: 321 253 426 837 201 | a 1 11: 105 68 70 625 88 | a 1 7: 126 110 138 628 123 | a 1 13: 106 57 75 614 64 | a 1 100: 105 17 134 837 23
b 1 9: 242 108 134 676 101 | b 1 10: 453 220 306 839 129 | b 1 11: 257 88 99 677 97 | b 1 7: 268 166 141 673 109 | b 1 13: 254 85 103 681 63 | b 1 100: 318 34 85 839 22
result 1 9: 156 104 92 615 111 | result 1 10: 309 198 304 840 145 | result 1 11: 110 67 80 612 68 | result 1 7: 146 123 133 627 132 | result 1 13: 98 61 68 609 67 | result 1 100: 110 13 88 840 13
```

## Per-run receipts

| Run | Projection (s) | Deadline (s) | Wall (s) | Wall / projection | Peak resident (KiB) |
|---|---|---|---|---|---|
| release build | 122 | 180 | 126.1 | 1.034 | 3552032 |
| locate (training partition) | 59 | 120 | 19.5 | 0.331 | 42920 |
| found `PRK` | 19.5 | 79.5 | 20.1 | 1.031 | 56728 |
| found `PRI` | 19.5 | 79.5 | 19.9 | 1.021 | 55848 |
| development passes (three) | — | — | 24.1, 23.9, 23.7 | — | — |
| train `PRK` | 646.20 | 647 | 406.8 | 0.630 | 294868 |
| train `PRI` | 640.21 | 641 | 409.3 | 0.639 | 308604 |
| written reads | — | — | 16.8 | — | — |
| rules, level cells, probes | unprojected, each under a minute | — | as listed above | — | as listed above |
