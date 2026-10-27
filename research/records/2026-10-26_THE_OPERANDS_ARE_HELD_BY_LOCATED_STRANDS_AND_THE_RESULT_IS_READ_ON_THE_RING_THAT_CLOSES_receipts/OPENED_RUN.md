# The opened loop on Brandon's PC

The lines below are the runs' own output, from the PC's run directory; the run paths are relative to
it. Each heavy run ran under the `wait4` wrapper (`RUN_RECEIPT`), `RAYON_NUM_THREADS=8` and its own
memory scope (`MemoryMax=8G`, `MemorySwapMax=0`). The per-process load lines are left out: the load
average ran from 1.5 at the build to 16.5 at the first written read (the three 8-thread trainings
had just ended), and other programs on the host held a third to two thirds of a core throughout.
The run's own summaries are left out too; the record's §8 reads these lines. The releases, marks
and cells hold held-out problem text and stay outside the repository.

## Build, inputs, the three foundings, the development passes and the projection

```text

STEP 1 BUILD (opened/build.sha, opened/build.log)
BINARY_SHA256 eeb84f1875f8bea5af64f62ba703fb33cd6f9992cbb1844c6223937b189c4ac6 RUN/opened/solenoidal_alpha
GIT_LOG 7e7d89842702af5789232d9143f763be57b42182 brandonrdug@users.noreply.github.com
RUN_RECEIPT exit=0 wall_s=118.2 peak_rss_kib=3496568 user_s=193.0

STEP 2 INPUTS (opened/inputs.log): all eleven match
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

STEP 3 FOUNDING PRA (opened/found_PRA.log, whole; lines 1-71 equal PRK's apart from elapsed_ms, only STRANDS_FOUNDED and ROTOR_FOUNDED differ)
PROJECTION 20.1 s (PRK's founding wall); DEADLINE 80 s (its wall + 60 s); RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
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
ROTOR_MENU loops=7368 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=6368 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=397
ROTOR_CLOSURE step=1 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=416
ROTOR_CLOSURE step=2 rows=6764 rank=40 minor_bits=19 torsion=3:2,11:2 carried=33 elapsed_ms=434
ROTOR_CLOSURE step=3 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=453
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=468
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=468
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=468
STRANDS_GROUP context=<+=> hand=1,1 stretches=3815 rows=3715 beyond=100 digits=8481
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3389 rows=3327 beyond=62 digits=6784
STRANDS_GROUP context=<-=. hand=1,-1 stretches=57 rows=57 beyond=0 digits=131
STRANDS_GROUP context=<+=. hand=1,1 stretches=48 rows=48 beyond=0 digits=107
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=37 rows=37 beyond=0 digits=78
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=22 rows=22 beyond=0 digits=32
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=3715/3715,digits=8419,symbolic=true <-=>:closed=3327/3327,digits=6715,symbolic=true elapsed_ms=600
STRANDS_STREAM_START events=331032 keyed=\x20+-.<=> closed=76 digits=2983 elapsed_ms=627
STRANDS_ASCENT round=1 byte=\x20 key=0,2,3:plus closed=5946 digits=13323 elapsed_ms=1965
STRANDS_ASCENT round=1 byte=. key=1,2,3:kept closed=5946 digits=13323 elapsed_ms=3257
STRANDS_ASCENT round=1 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=4541
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=5834
STRANDS_ASCENT round=1 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=7125
STRANDS_ASCENT round=1 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=8422
STRANDS_ASCENT round=1 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=9719
STRANDS_ASCENT round=2 byte=\x20 key=0,2,3:plus closed=7206 digits=15480 elapsed_ms=11082
STRANDS_ASCENT round=2 byte=. key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=12384
STRANDS_ASCENT round=2 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=13673
STRANDS_ASCENT round=2 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=14930
STRANDS_ASCENT round=2 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=16201
STRANDS_ASCENT round=2 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=17474
STRANDS_ASCENT round=2 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=18770
STRANDS_STREAM context=<+=> rows=3715 closed=3715 digits=8419/8481
STRANDS_STREAM context=<-=> rows=3327 closed=3327 digits=6715/6784
STRANDS_STREAM context=<-=. rows=57 closed=57 digits=130/131
STRANDS_STREAM context=<+=. rows=48 closed=48 digits=106/107
STRANDS_STREAM context=\x20+=\x20 rows=37 closed=37 digits=78/78
STRANDS_STREAM context=\x20-=\x20 rows=22 closed=22 digits=32/32
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=18778
STRANDS_FOUNDED level=0 parts=24 opened=true rings=9:1,99:10,999:10,9999:10 laws=turned,stepped,held comparison=0,1:1,1 keys=\x20=0,2,3:plus +=0,2,-1:flipped -=0,2,-1:kept <=0,2,3:kept ==1,3,3:plus
ROTOR_FOUNDED step=1 law=strands-opened carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2916069 sha256=ea26aeb047fae4eff70e552c22e79cb94fbe29b3f7e0c782855613b9ed32d3ce elapsed_ms=18840
RUN_RECEIPT exit=0 wall_s=18.9 peak_rss_kib=57704 user_s=145.0

STEP 3 FOUNDING PRJ (opened/found_PRJ.log, whole; lines 1-71 equal PRK's apart from elapsed_ms, only STRANDS_FOUNDED and ROTOR_FOUNDED differ)
PROJECTION 20.1 s (PRK's founding wall); DEADLINE 80 s (its wall + 60 s); RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
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
ROTOR_MENU loops=7368 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=6368 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=347
ROTOR_CLOSURE step=1 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=367
ROTOR_CLOSURE step=2 rows=6764 rank=40 minor_bits=19 torsion=3:2,11:2 carried=33 elapsed_ms=385
ROTOR_CLOSURE step=3 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=405
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=419
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=419
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=419
STRANDS_GROUP context=<+=> hand=1,1 stretches=3815 rows=3715 beyond=100 digits=8481
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3389 rows=3327 beyond=62 digits=6784
STRANDS_GROUP context=<-=. hand=1,-1 stretches=57 rows=57 beyond=0 digits=131
STRANDS_GROUP context=<+=. hand=1,1 stretches=48 rows=48 beyond=0 digits=107
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=37 rows=37 beyond=0 digits=78
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=22 rows=22 beyond=0 digits=32
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=3715/3715,digits=8419,symbolic=true <-=>:closed=3327/3327,digits=6715,symbolic=true elapsed_ms=547
STRANDS_STREAM_START events=331032 keyed=\x20+-.<=> closed=76 digits=2983 elapsed_ms=573
STRANDS_ASCENT round=1 byte=\x20 key=0,2,3:plus closed=5946 digits=13323 elapsed_ms=1899
STRANDS_ASCENT round=1 byte=. key=1,2,3:kept closed=5946 digits=13323 elapsed_ms=3177
STRANDS_ASCENT round=1 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=4433
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=5692
STRANDS_ASCENT round=1 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=6965
STRANDS_ASCENT round=1 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=8222
STRANDS_ASCENT round=1 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=9496
STRANDS_ASCENT round=2 byte=\x20 key=0,2,3:plus closed=7206 digits=15480 elapsed_ms=10836
STRANDS_ASCENT round=2 byte=. key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=12098
STRANDS_ASCENT round=2 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=13357
STRANDS_ASCENT round=2 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=14609
STRANDS_ASCENT round=2 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=15867
STRANDS_ASCENT round=2 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=17132
STRANDS_ASCENT round=2 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=18409
STRANDS_STREAM context=<+=> rows=3715 closed=3715 digits=8419/8481
STRANDS_STREAM context=<-=> rows=3327 closed=3327 digits=6715/6784
STRANDS_STREAM context=<-=. rows=57 closed=57 digits=130/131
STRANDS_STREAM context=<+=. rows=48 closed=48 digits=106/107
STRANDS_STREAM context=\x20+=\x20 rows=37 closed=37 digits=78/78
STRANDS_STREAM context=\x20-=\x20 rows=22 closed=22 digits=32/32
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=18416
STRANDS_FOUNDED level=0 parts=24 opened=false rings=9:1,99:10,999:10,9999:10 laws=turned,stepped,held comparison=0,1:1,1 keys=\x20=0,2,3:plus +=0,2,-1:flipped -=0,2,-1:kept <=0,2,3:kept ==1,3,3:plus
ROTOR_FOUNDED step=1 law=strands carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2922348 sha256=ef4b90f6ffff4057a619664b12a38448cb2b6f8049bf3b5d47e04e192e4e7e07 elapsed_ms=18476
RUN_RECEIPT exit=0 wall_s=18.5 peak_rss_kib=56936 user_s=141.9

STEP 3 FOUNDING PRE (opened/found_PRE.log, whole; lines 1-71 equal PRK's apart from elapsed_ms, only STRANDS_FOUNDED and ROTOR_FOUNDED differ)
PROJECTION 20.1 s (PRK's founding wall); DEADLINE 80 s (its wall + 60 s); RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
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
ROTOR_MENU loops=7368 bytes=10 period=4 columns=40
ROTOR_CLOSURE step=0 rows=6368 rank=40 minor_bits=24 torsion=3:4 carried=3 elapsed_ms=380
ROTOR_CLOSURE step=1 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=402
ROTOR_CLOSURE step=2 rows=6764 rank=40 minor_bits=19 torsion=3:2,11:2 carried=33 elapsed_ms=419
ROTOR_CLOSURE step=3 rows=7010 rank=40 minor_bits=14 torsion=3:1,11:1,101:1 carried=3333 elapsed_ms=439
ROTOR_KEY prime=3 fall=1 modulus=9 width=1 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,0 elapsed_ms=454
ROTOR_KEY prime=11 fall=1 modulus=11 width=2 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,9,8,7,6,5,4,3,2 elapsed_ms=454
ROTOR_KEY prime=101 fall=1 modulus=101 width=4 bytes=0123456789 turns=0,1,2,3,4,5,6,7,8,9/0,10,20,30,40,50,60,70,80,90/0,100,99,98,97,96,95,94,93,92/0,91,81,71,61,51,41,31,21,11 elapsed_ms=454
STRANDS_GROUP context=<+=> hand=1,1 stretches=3815 rows=3715 beyond=100 digits=8481
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3389 rows=3327 beyond=62 digits=6784
STRANDS_GROUP context=<-=. hand=1,-1 stretches=57 rows=57 beyond=0 digits=131
STRANDS_GROUP context=<+=. hand=1,1 stretches=48 rows=48 beyond=0 digits=107
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=37 rows=37 beyond=0 digits=78
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=22 rows=22 beyond=0 digits=32
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=3715/3715,digits=8419,symbolic=true <-=>:closed=3327/3327,digits=6715,symbolic=true elapsed_ms=588
STRANDS_STREAM_START events=331032 keyed=\x20+-.<=> closed=76 digits=2983 elapsed_ms=614
STRANDS_ASCENT round=1 byte=\x20 key=0,2,3:plus closed=5946 digits=13323 elapsed_ms=1961
STRANDS_ASCENT round=1 byte=. key=1,2,3:kept closed=5946 digits=13323 elapsed_ms=3253
STRANDS_ASCENT round=1 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=4544
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=5833
STRANDS_ASCENT round=1 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=7146
STRANDS_ASCENT round=1 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=8427
STRANDS_ASCENT round=1 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=9728
STRANDS_ASCENT round=2 byte=\x20 key=0,2,3:plus closed=7206 digits=15480 elapsed_ms=11076
STRANDS_ASCENT round=2 byte=. key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=12354
STRANDS_ASCENT round=2 byte=< key=0,2,3:kept closed=7206 digits=15480 elapsed_ms=13622
STRANDS_ASCENT round=2 byte=> key=1,2,3:kept closed=7206 digits=15480 elapsed_ms=14897
STRANDS_ASCENT round=2 byte=+ key=0,2,-1:flipped closed=7206 digits=15480 elapsed_ms=16173
STRANDS_ASCENT round=2 byte=- key=0,2,-1:kept closed=7206 digits=15480 elapsed_ms=17455
STRANDS_ASCENT round=2 byte== key=1,3,3:plus closed=7206 digits=15480 elapsed_ms=18751
STRANDS_STREAM context=<+=> rows=3715 closed=3715 digits=8419/8481
STRANDS_STREAM context=<-=> rows=3327 closed=3327 digits=6715/6784
STRANDS_STREAM context=<-=. rows=57 closed=57 digits=130/131
STRANDS_STREAM context=<+=. rows=48 closed=48 digits=106/107
STRANDS_STREAM context=\x20+=\x20 rows=37 closed=37 digits=78/78
STRANDS_STREAM context=\x20-=\x20 rows=22 closed=22 digits=32/32
STRANDS_CLOSED groups=2 closed=7042 rows=7042 elapsed_ms=18759
STRANDS_FOUNDED level=0 parts=24 opened=true rings=9:1,99:10,999:10,9999:10 laws=turned,stepped,held comparison=0,1:1,1 keys=none
ROTOR_FOUNDED step=1 law=strands-still-opened carried=3333 rings=9:1,11:2,101:4 moving=7 still=57 primes=3,11,101 units=1318 stepping_units=120 turning_units=113 levels_stepped=1 bytes=2916012 sha256=38d201b90f57e195660986ed3452cce9403a2009ab869ec854924b762f0095c3 elapsed_ms=18828
RUN_RECEIPT exit=0 wall_s=18.8 peak_rss_kib=56944 user_s=145.0

STEP 4 DEVELOPMENT PASSES, PRA PRJ PRE together (TOWER_PASS, TOWER_STATE, TOWER_DONE, RUN_RECEIPT)
PRA: TOWER_STATE STATE.0 state_bytes=13191366 state_sha256=12e6023f0f3adc7907a230f4fd59006c75016d49581329df28ac91d9886e00b4
PRA: TOWER_PASS pass=0 train_bits_a_byte=2.899 dev_bits_a_byte=2.529 dev_regions Q=1.828 P=2.907 N=1.601 M=2.540 deposits=155/155 pass_ms=22957 elapsed_ms=22977 train_code=1267153199501 dev_code=1054598860200 grain_bits=20
PRA: TOWER_DONE state_bytes=13191366 state_sha256=12e6023f0f3adc7907a230f4fd59006c75016d49581329df28ac91d9886e00b4 elapsed_ms=23045
PRA: RUN_RECEIPT exit=0 wall_s=23.1 peak_rss_kib=272300 user_s=144.3
PRJ: TOWER_STATE STATE.0 state_bytes=13151397 state_sha256=513a0f95077e9121ba5c9e09bb752a5cad8008f1a049038834738ee6a781be29
PRJ: TOWER_PASS pass=0 train_bits_a_byte=2.870 dev_bits_a_byte=2.511 dev_regions Q=1.851 P=2.830 N=1.681 M=2.521 deposits=155/155 pass_ms=23036 elapsed_ms=23057 train_code=1254530128887 dev_code=1047009203433 grain_bits=20
PRJ: TOWER_DONE state_bytes=13151397 state_sha256=513a0f95077e9121ba5c9e09bb752a5cad8008f1a049038834738ee6a781be29 elapsed_ms=23117
PRJ: RUN_RECEIPT exit=0 wall_s=23.2 peak_rss_kib=274360 user_s=144.8
PRE: TOWER_STATE STATE.0 state_bytes=12928677 state_sha256=213642ee2b3b5bcd11b4105287ad42b1e30c5f3f5d2abdbbd59f4516817955a3
PRE: TOWER_PASS pass=0 train_bits_a_byte=2.858 dev_bits_a_byte=2.494 dev_regions Q=1.795 P=2.908 N=1.459 M=2.505 deposits=155/155 pass_ms=22596 elapsed_ms=22622 train_code=1249154736088 dev_code=1039993499406 grain_bits=20
PRE: TOWER_DONE state_bytes=12928677 state_sha256=213642ee2b3b5bcd11b4105287ad42b1e30c5f3f5d2abdbbd59f4516817955a3 elapsed_ms=22721
PRE: RUN_RECEIPT exit=0 wall_s=22.8 peak_rss_kib=276400 user_s=142.5

Development windows (rotor/windows.py)
READ log=opened/dev_PRA.log
  window pass=0 section=32 sections=32 halvings=27 evaluations=59 ms=4392 ms_an_evaluation=74.4407
  window pass=0 section=64 sections=32 halvings=0 evaluations=32 ms=3539 ms_an_evaluation=110.5938
  window pass=0 section=96 sections=32 halvings=0 evaluations=32 ms=3561 ms_an_evaluation=111.2812
  window pass=0 section=128 sections=32 halvings=0 evaluations=32 ms=3587 ms_an_evaluation=112.0938
  window pass=0 section=155 sections=27 halvings=0 evaluations=27 ms=2942 ms_an_evaluation=108.9630
  w=112.0938 ms_an_evaluation (window pass=0 section=128)
  eta pass=0 halvings=27 sections=155 eta=0.174194
  h pass=0 h=4956 ms
READ log=opened/dev_PRJ.log
  window pass=0 section=32 sections=32 halvings=28 evaluations=60 ms=4449 ms_an_evaluation=74.1500
  window pass=0 section=64 sections=32 halvings=0 evaluations=32 ms=3535 ms_an_evaluation=110.4688
  window pass=0 section=96 sections=32 halvings=0 evaluations=32 ms=3558 ms_an_evaluation=111.1875
  window pass=0 section=128 sections=32 halvings=0 evaluations=32 ms=3609 ms_an_evaluation=112.7812
  window pass=0 section=155 sections=27 halvings=0 evaluations=27 ms=2952 ms_an_evaluation=109.3333
  w=112.7812 ms_an_evaluation (window pass=0 section=128)
  eta pass=0 halvings=28 sections=155 eta=0.180645
  h pass=0 h=4954 ms
READ log=opened/dev_PRE.log
  window pass=0 section=32 sections=32 halvings=19 evaluations=51 ms=4090 ms_an_evaluation=80.1961
  window pass=0 section=64 sections=32 halvings=0 evaluations=32 ms=3528 ms_an_evaluation=110.2500
  window pass=0 section=96 sections=32 halvings=0 evaluations=32 ms=3570 ms_an_evaluation=111.5625
  window pass=0 section=128 sections=32 halvings=0 evaluations=32 ms=3602 ms_an_evaluation=112.5625
  window pass=0 section=155 sections=27 halvings=0 evaluations=27 ms=2906 ms_an_evaluation=107.6296
  w=112.5625 ms_an_evaluation (window pass=0 section=128)
  eta pass=0 halvings=19 sections=155 eta=0.122581
  h pass=0 h=4926 ms

STEP 5 PROJECTION (opened/project.log, whole)
NUMBER w_PRT_of turns/dev_PRT.first.log: 100.0938 from turns/dev_PRT.first.log pass=0 section=64 ms=3203 evaluations=32
NUMBER w_PRT_of turns/dev_PRT.log: 120.5000 from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32
NUMBER w_PRT_of turns/PRT.log: 113.8750 from turns/PRT.log pass=2 section=448 ms=3644 evaluations=32
NUMBER w_PRT_of capture/dev_PRT.log: 112.7812 from capture/dev_PRT.log pass=0 section=96 ms=3609 evaluations=32
NUMBER w_PRT_of strands/dev_PRT.log: 117.1562 from strands/dev_PRT.log pass=0 section=96 ms=3749 evaluations=32
NUMBER w_PRT=120.5000 ms_an_evaluation from turns/dev_PRT.log pass=0 section=128 ms=3856 evaluations=32 (over every full window of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log, strands/dev_PRT.log)
NUMBER eta_PRT=0.090323 from turns/dev_PRT.log pass=0 halvings=14 sections=155 (over every pass of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log, strands/dev_PRT.log)
NUMBER h_PRT=5317 ms from turns/dev_PRT.log pass=0 (over every pass of turns/dev_PRT.first.log, turns/dev_PRT.log, turns/PRT.log, capture/dev_PRT.log, strands/dev_PRT.log)
NUMBER d_PRA=112.0938 from opened/dev_PRA.log pass=0 section=128 ms=3587 evaluations=32
NUMBER d_PRA_full_windows_only=112.0938 from opened/dev_PRA.log pass=0 section=128 ms=3587 evaluations=32 (not used)
NUMBER d_PRJ=112.7812 from opened/dev_PRJ.log pass=0 section=128 ms=3609 evaluations=32
NUMBER d_PRJ_full_windows_only=112.7812 from opened/dev_PRJ.log pass=0 section=128 ms=3609 evaluations=32 (not used)
NUMBER d_PRE=112.5625 from opened/dev_PRE.log pass=0 section=128 ms=3602 evaluations=32
NUMBER d_PRE_full_windows_only=112.5625 from opened/dev_PRE.log pass=0 section=128 ms=3602 evaluations=32 (not used)
NUMBER d_PRT=117.1562 from strands/dev_PRT.log pass=0 section=96 ms=3749 evaluations=32
NUMBER d_PRT_full_windows_only=117.1562 from strands/dev_PRT.log pass=0 section=96 ms=3749 evaluations=32 (not used)
NUMBER w_PRA = w_PRT x max(1, d_PRA/d_PRT) = 120.5000 x max(1, 0.956788) = 120.5000 ms_an_evaluation
NUMBER eta_PRA=max(eta_PRT 0.090323, own 0.174194 from opened/dev_PRA.log pass=0 halvings=27 sections=155)=0.174194
NUMBER h_PRA=max(h_PRT 5317, own 4956 from opened/dev_PRA.log pass=0)=5317 ms
PROJECTION_PRA 3 x (1311 x 1.12 x 120.5000 x (1 + 0.174194) + 5317) + 1000 ms = 640.21 s; DEADLINE 641 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation
NUMBER w_PRJ = w_PRT x max(1, d_PRJ/d_PRT) = 120.5000 x max(1, 0.962657) = 120.5000 ms_an_evaluation
NUMBER eta_PRJ=max(eta_PRT 0.090323, own 0.180645 from opened/dev_PRJ.log pass=0 halvings=28 sections=155)=0.180645
NUMBER h_PRJ=max(h_PRT 5317, own 4954 from opened/dev_PRJ.log pass=0)=5317 ms
PROJECTION_PRJ 3 x (1311 x 1.12 x 120.5000 x (1 + 0.180645) + 5317) + 1000 ms = 643.63 s; DEADLINE 644 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation
NUMBER w_PRE = w_PRT x max(1, d_PRE/d_PRT) = 120.5000 x max(1, 0.960790) = 120.5000 ms_an_evaluation
NUMBER eta_PRE=max(eta_PRT 0.090323, own 0.122581 from opened/dev_PRE.log pass=0 halvings=19 sections=155)=0.122581
NUMBER h_PRE=max(h_PRT 5317, own 4926 from opened/dev_PRE.log pass=0)=5317 ms
PROJECTION_PRE 3 x (1311 x 1.12 x 120.5000 x (1 + 0.122581) + 5317) + 1000 ms = 612.81 s; DEADLINE 613 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation

TABLE (projection, deadline, measured wall, ratio, peak resident)
run | projection | deadline | wall | ratio | peak RSS KiB | exit
build | 127 s | 180 s | 118.2 s | 0.931 | 3496568 | 0
found PRA | 20.1 s (PRK's founding wall) | 80 s | 18.9 s | 0.940 | 57704 | 0
found PRJ | 20.1 s (PRK's founding wall) | 80 s | 18.5 s | 0.920 | 56936 | 0
found PRE | 20.1 s (PRK's founding wall) | 80 s | 18.8 s | 0.935 | 56944 | 0
dev PRA | 24.1 s (strands/ three-way 23.7-24.1 s) | 180 s | 23.1 s | 0.959 | 272300 | 0
dev PRJ | 24.1 s (strands/ three-way 23.7-24.1 s) | 180 s | 23.2 s | 0.963 | 274360 | 0
dev PRE | 24.1 s (strands/ three-way 23.7-24.1 s) | 180 s | 22.8 s | 0.946 | 276400 | 0
train PRA | 640.21 s | 641 s | 452.6 s | 0.707 | 316756 | 0
train PRJ | 643.63 s | 644 s | 454.7 s | 0.706 | 310144 | 0
train PRE | 612.81 s | 613 s | 452.2 s | 0.738 | 316164 | 0
read PRA | problems=64 by 3.3 s (strands/ reads 16.8 s) | 30 s | 17.1 s | 1.018 | 42436 | 0
read PRJ | problems=64 by 3.3 s (strands/ reads 16.8 s) | 30 s | 17.1 s | 1.018 | 43508 | 0
read PRE | problems=64 by 3.3 s (strands/ reads 16.8 s) | 30 s | 16.9 s | 1.006 | 44408 | 0
rules rings | unmeasured (strands/ 16.9 s) | 60 s | 20.6 s | n/a | 60852 | 0
rules heard | unmeasured (strands/ 7.0 s) | 60 s | 10.3 s | n/a | 62120 | 0
rules pair PRA PRE | unmeasured (strands/ 4.6-4.8 s) | 60 s | 4.2 s | n/a | 60944 | 0
rules pair PRA PRJ | unmeasured (strands/ 4.6-4.8 s) | 60 s | 4.2 s | n/a | 61280 | 0
rules pair PRA PRT | unmeasured (strands/ 4.6-4.8 s) | 60 s | 4.2 s | n/a | 61088 | 0
rules pair PRA PRK | unmeasured (strands/ 4.6-4.8 s) | 60 s | 4.2 s | n/a | 61832 | 0
rules gaps | unmeasured (strands/ 16.3 s) | 60 s | 21.8 s | n/a | 61384 | 0
pair-modes PRA founded | seconds (strands/reads/ 0.1 s) | 120 s | 0.1 s | n/a | 27296 | 0
pair-modes PRA final | seconds (strands/reads/ 0.1 s) | 120 s | 0.1 s | n/a | 38848 | 0
pair-modes PRJ founded | seconds (strands/reads/ 0.1 s) | 120 s | 0.0 s | n/a | 26076 | 0
pair-modes PRJ final | seconds (strands/reads/ 0.1 s) | 120 s | 0.1 s | n/a | 40592 | 0
pair-modes PRE founded | seconds (strands/reads/ 0.1 s) | 120 s | 0.0 s | n/a | 25256 | 0
pair-modes PRE final | seconds (strands/reads/ 0.1 s) | 120 s | 0.1 s | n/a | 39352 | 0

```
## The three trainings (`PRA`, `PRJ`, `PRE` together, three passes each) and every guard line

```text

Training lines (TOWER_PASS, TOWER_STATE, TOWER_DONE, RUN_RECEIPT)
PRA: PROJECTION_PRA 3 x (1311 x 1.12 x 120.5000 x (1 + 0.174194) + 5317) + 1000 ms = 640.21 s; DEADLINE 641 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
PRA: TOWER_STATE STATE.0 state_bytes=13071805 state_sha256=252288073c0f094217d58a37010b6d8a7e46bc7445e3da9bf5878f100c590d74
PRA: TOWER_PASS pass=0 train_bits_a_byte=2.208 dev_bits_a_byte=1.986 dev_regions Q=1.390 P=2.484 N=0.832 M=1.995 deposits=1311/1311 pass_ms=151301 elapsed_ms=151318 train_code=8168657171540 dev_code=828134718541 grain_bits=20
PRA: TOWER_STATE STATE.1 state_bytes=12993968 state_sha256=2bc266d93fa593e469920e333a79fe487c4c0f399eee86f0d5672b7fb1f8d0fb
PRA: TOWER_PASS pass=1 train_bits_a_byte=1.884 dev_bits_a_byte=1.867 dev_regions Q=1.256 P=2.365 N=0.540 M=1.877 deposits=1311/1311 pass_ms=150305 elapsed_ms=301624 train_code=6967582779783 dev_code=778568018359 grain_bits=20
PRA: TOWER_STATE STATE.2 state_bytes=12987067 state_sha256=5728ba0a1ac786e37d7d672d0946b7c7ae43f73ad60039c41730ef19ac217520
PRA: TOWER_PASS pass=2 train_bits_a_byte=1.793 dev_bits_a_byte=1.824 dev_regions Q=1.222 P=2.382 N=0.457 M=1.833 deposits=1311/1311 pass_ms=150484 elapsed_ms=452109 train_code=6632599178514 dev_code=760427673615 grain_bits=20
PRA: TOWER_DONE state_bytes=12987067 state_sha256=5728ba0a1ac786e37d7d672d0946b7c7ae43f73ad60039c41730ef19ac217520 elapsed_ms=452175
PRA: RUN_RECEIPT exit=0 wall_s=452.6 peak_rss_kib=316756 user_s=2754.1
PRJ: PROJECTION_PRJ 3 x (1311 x 1.12 x 120.5000 x (1 + 0.180645) + 5317) + 1000 ms = 643.63 s; DEADLINE 644 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
PRJ: TOWER_STATE STATE.0 state_bytes=13129215 state_sha256=3f0471d457d28f6e69c7fe5c4e2ab0cab3af3eb6045e3d90612a8edaffd6d54a
PRJ: TOWER_PASS pass=0 train_bits_a_byte=2.212 dev_bits_a_byte=1.986 dev_regions Q=1.385 P=2.472 N=0.756 M=1.995 deposits=1311/1311 pass_ms=152201 elapsed_ms=152218 train_code=8182747894185 dev_code=827900799425 grain_bits=20
PRJ: TOWER_STATE STATE.1 state_bytes=13047303 state_sha256=4f658f556ff95413cfbe1800362bf6c4df6a93b9124031a7153be3bb10bf9b07
PRJ: TOWER_PASS pass=1 train_bits_a_byte=1.882 dev_bits_a_byte=1.868 dev_regions Q=1.283 P=2.386 N=0.669 M=1.877 deposits=1311/1311 pass_ms=150967 elapsed_ms=303186 train_code=6960328507052 dev_code=778970600149 grain_bits=20
PRJ: TOWER_STATE STATE.2 state_bytes=13068501 state_sha256=5c1f4c1f484e5108e57aeaa0316928c34d15bf1e243e8e37f306257c118da927
PRJ: TOWER_PASS pass=2 train_bits_a_byte=1.807 dev_bits_a_byte=1.810 dev_regions Q=1.233 P=2.378 N=0.485 M=1.819 deposits=1311/1311 pass_ms=151026 elapsed_ms=454212 train_code=6684342628318 dev_code=754855957063 grain_bits=20
PRJ: TOWER_DONE state_bytes=13068501 state_sha256=5c1f4c1f484e5108e57aeaa0316928c34d15bf1e243e8e37f306257c118da927 elapsed_ms=454284
PRJ: RUN_RECEIPT exit=0 wall_s=454.7 peak_rss_kib=310144 user_s=2750.3
PRE: PROJECTION_PRE 3 x (1311 x 1.12 x 120.5000 x (1 + 0.122581) + 5317) + 1000 ms = 612.81 s; DEADLINE 613 s; bound 1.12 x 120.5000 = 134.9600 ms an evaluation; RAYON_NUM_THREADS=8; MemoryMax=8G MemorySwapMax=0
PRE: TOWER_STATE STATE.0 state_bytes=12913339 state_sha256=85b0ca027b0c6630700d7266f03226cdb325aecc630257b6234b47cee5a78a7e
PRE: TOWER_PASS pass=0 train_bits_a_byte=2.193 dev_bits_a_byte=1.959 dev_regions Q=1.485 P=2.508 N=0.730 M=1.965 deposits=1311/1311 pass_ms=150941 elapsed_ms=150959 train_code=8112715764345 dev_code=816631765644 grain_bits=20
PRE: TOWER_STATE STATE.1 state_bytes=12851214 state_sha256=f5b72795698e9963745d718a03de2aca4df6a470418249c059c390689b7eb908
PRE: TOWER_PASS pass=1 train_bits_a_byte=1.856 dev_bits_a_byte=1.833 dev_regions Q=1.298 P=2.373 N=0.613 M=1.841 deposits=1311/1311 pass_ms=150223 elapsed_ms=301183 train_code=6866102796542 dev_code=764334478662 grain_bits=20
PRE: TOWER_STATE STATE.2 state_bytes=12868751 state_sha256=8d5262faa914e68853d704bb6cbee445fda91ee7d86ce576415be6c0f867a870
PRE: TOWER_PASS pass=2 train_bits_a_byte=1.773 dev_bits_a_byte=1.785 dev_regions Q=1.243 P=2.353 N=0.513 M=1.793 deposits=1311/1311 pass_ms=150517 elapsed_ms=451701 train_code=6557766417723 dev_code=744381352953 grain_bits=20
PRE: TOWER_DONE state_bytes=12868751 state_sha256=8d5262faa914e68853d704bb6cbee445fda91ee7d86ce576415be6c0f867a870 elapsed_ms=451792
PRE: RUN_RECEIPT exit=0 wall_s=452.2 peak_rss_kib=316164 user_s=2745.8

Training windows (rotor/windows.py, summary)
READ log=opened/PRA.log
  w=114.4062 ms_an_evaluation (window pass=0 section=160)
  eta pass=0 halvings=38 sections=1311 eta=0.028986
  eta pass=1 halvings=0 sections=1311 eta=0.000000
  eta pass=2 halvings=0 sections=1311 eta=0.000000
  h pass=0 h=5103 ms
  h pass=1 h=5018 ms
  h pass=2 h=4919 ms
READ log=opened/PRJ.log
  w=114.9375 ms_an_evaluation (window pass=0 section=224)
  eta pass=0 halvings=27 sections=1311 eta=0.020595
  eta pass=1 halvings=0 sections=1311 eta=0.000000
  eta pass=2 halvings=0 sections=1311 eta=0.000000
  h pass=0 h=5188 ms
  h pass=1 h=5005 ms
  h pass=2 h=4261 ms
READ log=opened/PRE.log
  w=115.0312 ms_an_evaluation (window pass=0 section=160)
  eta pass=0 halvings=25 sections=1311 eta=0.019069
  eta pass=1 halvings=0 sections=1311 eta=0.000000
  eta pass=2 halvings=0 sections=1311 eta=0.000000
  h pass=0 h=5082 ms
  h pass=1 h=5083 ms
  h pass=2 h=5017 ms

PRJ 0 32 3.680 27 4390 | 32 27 59 4390 74.41 7962.6
PRE 0 32 3.622 25 4327 | 32 25 57 4327 75.91 7692.7
PRA 0 32 3.590 37 4760 | 32 37 69 4760 68.99 9312.2
PRJ 0 64 3.115 27 7953 | 32 0 32 3563 111.34 4318.7
PRE 0 64 2.993 25 7892 | 32 0 32 3565 111.41 4318.7
PRA 0 64 3.095 38 8370 | 32 1 33 3610 109.39 4453.7
PRJ 0 96 2.775 27 11514 | 32 0 32 3561 111.28 4318.7
PRE 0 96 2.746 25 11453 | 32 0 32 3561 111.28 4318.7
PRA 0 96 2.764 38 11924 | 32 0 32 3554 111.06 4318.7
PRE 0 128 2.589 25 15035 | 32 0 32 3582 111.94 4318.7
PRA 0 128 2.592 38 15514 | 32 0 32 3590 112.19 4318.7
PRJ 0 128 2.593 27 15132 | 32 0 32 3618 113.06 4318.7
PRJ 0 160 2.522 27 18803 | 32 0 32 3671 114.72 4318.7
PRE 0 160 2.515 25 18716 | 32 0 32 3681 115.03 4318.7
PRA 0 160 2.512 38 19175 | 32 0 32 3661 114.41 4318.7
PRJ 0 192 2.422 27 22434 | 32 0 32 3631 113.47 4318.7
PRE 0 192 2.409 25 22352 | 32 0 32 3636 113.62 4318.7
PRA 0 192 2.414 38 22802 | 32 0 32 3627 113.34 4318.7
PRJ 0 224 2.331 27 26112 | 32 0 32 3678 114.94 4318.7
PRE 0 224 2.329 25 25974 | 32 0 32 3622 113.19 4318.7
PRA 0 224 2.327 38 26406 | 32 0 32 3604 112.62 4318.7
PRJ 0 256 2.387 27 29624 | 32 0 32 3512 109.75 4318.7
PRE 0 256 2.375 25 29514 | 32 0 32 3540 110.62 4318.7
PRA 0 256 2.373 38 29906 | 32 0 32 3500 109.38 4318.7
PRE 0 288 2.309 25 33033 | 32 0 32 3519 109.97 4318.7
PRA 0 288 2.307 38 33436 | 32 0 32 3530 110.31 4318.7
PRJ 0 288 2.319 27 33195 | 32 0 32 3571 111.59 4318.7
PRE 0 320 2.244 25 36542 | 32 0 32 3509 109.66 4318.7
PRA 0 320 2.254 38 36946 | 32 0 32 3510 109.69 4318.7
PRJ 0 320 2.262 27 36758 | 32 0 32 3563 111.34 4318.7
PRE 0 352 2.264 25 40098 | 32 0 32 3556 111.12 4318.7
PRA 0 352 2.259 38 40464 | 32 0 32 3518 109.94 4318.7
PRJ 0 352 2.278 27 40288 | 32 0 32 3530 110.31 4318.7
PRE 0 384 2.264 25 43596 | 32 0 32 3498 109.31 4318.7
PRA 0 384 2.257 38 43957 | 32 0 32 3493 109.16 4318.7
PRJ 0 384 2.271 27 43787 | 32 0 32 3499 109.34 4318.7
PRA 0 416 2.212 38 47452 | 32 0 32 3495 109.22 4318.7
PRJ 0 416 2.222 27 47360 | 32 0 32 3573 111.66 4318.7
PRE 0 416 2.218 25 47151 | 32 0 32 3555 111.09 4318.7
PRA 0 448 2.204 38 50952 | 32 0 32 3500 109.38 4318.7
PRJ 0 448 2.202 27 50902 | 32 0 32 3542 110.69 4318.7
PRE 0 448 2.199 25 50669 | 32 0 32 3518 109.94 4318.7
PRA 0 480 2.180 38 54426 | 32 0 32 3474 108.56 4318.7
PRJ 0 480 2.182 27 54464 | 32 0 32 3562 111.31 4318.7
PRE 0 480 2.173 25 54151 | 32 0 32 3482 108.81 4318.7
PRA 0 512 2.152 38 57962 | 32 0 32 3536 110.50 4318.7
PRJ 0 512 2.155 27 58051 | 32 0 32 3587 112.09 4318.7
PRE 0 512 2.148 25 57676 | 32 0 32 3525 110.16 4318.7
PRA 0 544 2.109 38 61529 | 32 0 32 3567 111.47 4318.7
PRJ 0 544 2.116 27 61616 | 32 0 32 3565 111.41 4318.7
PRE 0 544 2.109 25 61227 | 32 0 32 3551 110.97 4318.7
PRA 0 576 2.160 38 65110 | 32 0 32 3581 111.91 4318.7
PRE 0 576 2.153 25 64737 | 32 0 32 3510 109.69 4318.7
PRJ 0 576 2.162 27 65207 | 32 0 32 3591 112.22 4318.7
PRA 0 608 2.108 38 68607 | 32 0 32 3497 109.28 4318.7
PRE 0 608 2.104 25 68269 | 32 0 32 3532 110.38 4318.7
PRJ 0 608 2.106 27 68754 | 32 0 32 3547 110.84 4318.7
PRA 0 640 2.086 38 72147 | 32 0 32 3540 110.62 4318.7
PRE 0 640 2.082 25 71790 | 32 0 32 3521 110.03 4318.7
PRJ 0 640 2.092 27 72295 | 32 0 32 3541 110.66 4318.7
PRA 0 672 2.093 38 75664 | 32 0 32 3517 109.91 4318.7
PRE 0 672 2.082 25 75333 | 32 0 32 3543 110.72 4318.7
PRJ 0 672 2.098 27 75807 | 32 0 32 3512 109.75 4318.7
PRA 0 704 2.087 38 79186 | 32 0 32 3522 110.06 4318.7
PRE 0 704 2.073 25 78850 | 32 0 32 3517 109.91 4318.7
PRJ 0 704 2.089 27 79309 | 32 0 32 3502 109.44 4318.7
PRE 0 736 2.063 25 82460 | 32 0 32 3610 112.81 4318.7
PRA 0 736 2.071 38 82790 | 32 0 32 3604 112.62 4318.7
PRJ 0 736 2.082 27 82912 | 32 0 32 3603 112.59 4318.7
PRE 0 768 2.056 25 85989 | 32 0 32 3529 110.28 4318.7
PRA 0 768 2.073 38 86289 | 32 0 32 3499 109.34 4318.7
PRJ 0 768 2.065 27 86485 | 32 0 32 3573 111.66 4318.7
PRE 0 800 2.021 25 89507 | 32 0 32 3518 109.94 4318.7
PRA 0 800 2.044 38 89795 | 32 0 32 3506 109.56 4318.7
PRJ 0 800 2.035 27 90009 | 32 0 32 3524 110.12 4318.7
PRE 0 832 2.028 25 93050 | 32 0 32 3543 110.72 4318.7
PRA 0 832 2.041 38 93341 | 32 0 32 3546 110.81 4318.7
PRJ 0 832 2.044 27 93534 | 32 0 32 3525 110.16 4318.7
PRE 0 864 2.028 25 96566 | 32 0 32 3516 109.88 4318.7
PRA 0 864 2.045 38 96851 | 32 0 32 3510 109.69 4318.7
PRJ 0 864 2.036 27 97100 | 32 0 32 3566 111.44 4318.7
PRE 0 896 2.018 25 100053 | 32 0 32 3487 108.97 4318.7
PRA 0 896 2.029 38 100343 | 32 0 32 3492 109.12 4318.7
PRJ 0 896 2.035 27 100657 | 32 0 32 3557 111.16 4318.7
PRE 0 928 2.049 25 103608 | 32 0 32 3555 111.09 4318.7
PRA 0 928 2.061 38 103900 | 32 0 32 3557 111.16 4318.7
PRJ 0 928 2.061 27 104237 | 32 0 32 3580 111.88 4318.7
PRE 0 960 2.008 25 107106 | 32 0 32 3498 109.31 4318.7
PRA 0 960 2.028 38 107443 | 32 0 32 3543 110.72 4318.7
PRJ 0 960 2.029 27 107786 | 32 0 32 3549 110.91 4318.7
PRE 0 992 2.009 25 110670 | 32 0 32 3564 111.38 4318.7
PRA 0 992 2.027 38 110961 | 32 0 32 3518 109.94 4318.7
PRJ 0 992 2.033 27 111333 | 32 0 32 3547 110.84 4318.7
PRA 0 1024 1.975 38 114474 | 32 0 32 3513 109.78 4318.7
PRE 0 1024 1.967 25 114210 | 32 0 32 3540 110.62 4318.7
PRJ 0 1024 1.983 27 114922 | 32 0 32 3589 112.16 4318.7
PRA 0 1056 1.983 38 117978 | 32 0 32 3504 109.50 4318.7
PRE 0 1056 1.963 25 117715 | 32 0 32 3505 109.53 4318.7
PRJ 0 1056 1.999 27 118482 | 32 0 32 3560 111.25 4318.7
PRA 0 1088 2.023 38 121506 | 32 0 32 3528 110.25 4318.7
PRE 0 1088 2.003 25 121216 | 32 0 32 3501 109.41 4318.7
PRJ 0 1088 2.046 27 122088 | 32 0 32 3606 112.69 4318.7
PRA 0 1120 1.999 38 125077 | 32 0 32 3571 111.59 4318.7
PRE 0 1120 1.975 25 124788 | 32 0 32 3572 111.62 4318.7
PRJ 0 1120 2.019 27 125672 | 32 0 32 3584 112.00 4318.7
PRA 0 1152 2.009 38 128606 | 32 0 32 3529 110.28 4318.7
PRE 0 1152 1.988 25 128309 | 32 0 32 3521 110.03 4318.7
PRJ 0 1152 2.009 27 129198 | 32 0 32 3526 110.19 4318.7
PRA 0 1184 1.971 38 132106 | 32 0 32 3500 109.38 4318.7
PRE 0 1184 1.944 25 131830 | 32 0 32 3521 110.03 4318.7
PRJ 0 1184 1.965 27 132765 | 32 0 32 3567 111.47 4318.7
PRA 0 1216 2.040 38 135641 | 32 0 32 3535 110.47 4318.7
PRE 0 1216 1.973 25 135350 | 32 0 32 3520 110.00 4318.7
PRJ 0 1216 1.990 27 136309 | 32 0 32 3544 110.75 4318.7
PRA 0 1248 2.011 38 139178 | 32 0 32 3537 110.53 4318.7
PRE 0 1248 1.948 25 138886 | 32 0 32 3536 110.50 4318.7
PRJ 0 1248 1.963 27 139890 | 32 0 32 3581 111.91 4318.7
PRA 0 1280 2.012 38 142714 | 32 0 32 3536 110.50 4318.7
PRE 0 1280 1.957 25 142399 | 32 0 32 3513 109.78 4318.7
PRJ 0 1280 1.980 27 143462 | 32 0 32 3572 111.62 4318.7
PRA 0 1311 1.960 38 146215 | 31 0 31 3501 112.94 4183.8
PRE 0 1311 1.921 25 145877 | 31 0 31 3478 112.19 4183.8
PRE: TOWER_STATE STATE.0 state_bytes=12913339 state_sha256=85b0ca027b0c6630700d7266f03226cdb325aecc630257b6234b47cee5a78a7e
PRA: TOWER_STATE STATE.0 state_bytes=13071805 state_sha256=252288073c0f094217d58a37010b6d8a7e46bc7445e3da9bf5878f100c590d74
PRJ 0 1311 1.939 27 147030 | 31 0 31 3568 115.10 4183.8
PRJ: TOWER_STATE STATE.0 state_bytes=13129215 state_sha256=3f0471d457d28f6e69c7fe5c4e2ab0cab3af3eb6045e3d90612a8edaffd6d54a
PRE: TOWER_PASS pass=0 train_bits_a_byte=2.193 dev_bits_a_byte=1.959 dev_regions Q=1.485 P=2.508 N=0.730 M=1.965 deposits=1311/1311 pass_ms=150941 elapsed_ms=150959 train_code=8112715764345 dev_code=816631765644 grain_bits=20
PRA: TOWER_PASS pass=0 train_bits_a_byte=2.208 dev_bits_a_byte=1.986 dev_regions Q=1.390 P=2.484 N=0.832 M=1.995 deposits=1311/1311 pass_ms=151301 elapsed_ms=151318 train_code=8168657171540 dev_code=828134718541 grain_bits=20
PRJ: TOWER_PASS pass=0 train_bits_a_byte=2.212 dev_bits_a_byte=1.986 dev_regions Q=1.385 P=2.472 N=0.756 M=1.995 deposits=1311/1311 pass_ms=152201 elapsed_ms=152218 train_code=8182747894185 dev_code=827900799425 grain_bits=20
PRE 1 32 1.920 0 154487 | 32 0 32 3528 110.25 4318.7
PRA 1 32 1.948 0 154837 | 32 0 32 3519 109.97 4318.7
PRJ 1 32 1.946 0 155769 | 32 0 32 3551 110.97 4318.7
PRE 1 64 1.912 0 158015 | 32 0 32 3528 110.25 4318.7
PRA 1 64 1.936 0 158380 | 32 0 32 3543 110.72 4318.7
PRJ 1 64 1.932 0 159287 | 32 0 32 3518 109.94 4318.7
PRE 1 96 1.938 0 161542 | 32 0 32 3527 110.22 4318.7
PRA 1 96 1.959 0 161907 | 32 0 32 3527 110.22 4318.7
PRJ 1 96 1.963 0 162806 | 32 0 32 3519 109.97 4318.7
PRE 1 128 1.906 0 165053 | 32 0 32 3511 109.72 4318.7
PRA 1 128 1.932 0 165447 | 32 0 32 3540 110.62 4318.7
PRJ 1 128 1.931 0 166384 | 32 0 32 3578 111.81 4318.7
PRE 1 160 1.926 0 168616 | 32 0 32 3563 111.34 4318.7
PRA 1 160 1.947 0 169016 | 32 0 32 3569 111.53 4318.7
PRJ 1 160 1.946 0 169943 | 32 0 32 3559 111.22 4318.7
PRE 1 192 1.888 0 172140 | 32 0 32 3524 110.12 4318.7
PRA 1 192 1.913 0 172539 | 32 0 32 3523 110.09 4318.7
PRJ 1 192 1.916 0 173505 | 32 0 32 3562 111.31 4318.7
PRE 1 224 1.831 0 175648 | 32 0 32 3508 109.62 4318.7
PRA 1 224 1.864 0 176043 | 32 0 32 3504 109.50 4318.7
PRJ 1 224 1.866 0 177080 | 32 0 32 3575 111.72 4318.7
PRE 1 256 1.930 0 179139 | 32 0 32 3491 109.09 4318.7
PRA 1 256 1.966 0 179542 | 32 0 32 3499 109.34 4318.7
PRJ 1 256 1.961 0 180650 | 32 0 32 3570 111.56 4318.7
PRE 1 288 1.895 0 182677 | 32 0 32 3538 110.56 4318.7
PRA 1 288 1.919 0 183060 | 32 0 32 3518 109.94 4318.7
PRJ 1 288 1.922 0 184213 | 32 0 32 3563 111.34 4318.7
PRE 1 320 1.865 0 186226 | 32 0 32 3549 110.91 4318.7
PRA 1 320 1.893 0 186613 | 32 0 32 3553 111.03 4318.7
PRJ 1 320 1.891 0 187773 | 32 0 32 3560 111.25 4318.7
PRA 1 352 1.922 0 190196 | 32 0 32 3583 111.97 4318.7
PRE 1 352 1.896 0 189805 | 32 0 32 3579 111.84 4318.7
PRJ 1 352 1.917 0 191360 | 32 0 32 3587 112.09 4318.7
PRA 1 384 1.931 0 193711 | 32 0 32 3515 109.84 4318.7
PRE 1 384 1.901 0 193316 | 32 0 32 3511 109.72 4318.7
PRJ 1 384 1.928 0 194900 | 32 0 32 3540 110.62 4318.7
PRA 1 416 1.905 0 197247 | 32 0 32 3536 110.50 4318.7
PRE 1 416 1.880 0 196836 | 32 0 32 3520 110.00 4318.7
PRJ 1 416 1.943 0 198431 | 32 0 32 3531 110.34 4318.7
PRA 1 448 1.911 0 200785 | 32 0 32 3538 110.56 4318.7
PRE 1 448 1.881 0 200363 | 32 0 32 3527 110.22 4318.7
PRJ 1 448 1.931 0 201991 | 32 0 32 3560 111.25 4318.7
PRE 1 480 1.867 0 203921 | 32 0 32 3558 111.19 4318.7
PRA 1 480 1.895 0 204384 | 32 0 32 3599 112.47 4318.7
PRJ 1 480 1.905 0 205576 | 32 0 32 3585 112.03 4318.7
PRE 1 512 1.862 0 207515 | 32 0 32 3594 112.31 4318.7
PRA 1 512 1.892 0 207956 | 32 0 32 3572 111.62 4318.7
PRJ 1 512 1.893 0 209162 | 32 0 32 3586 112.06 4318.7
PRE 1 544 1.820 0 211123 | 32 0 32 3608 112.75 4318.7
PRA 1 544 1.849 0 211579 | 32 0 32 3623 113.22 4318.7
PRJ 1 544 1.850 0 212769 | 32 0 32 3607 112.72 4318.7
PRE 1 576 1.907 0 214681 | 32 0 32 3558 111.19 4318.7
PRA 1 576 1.907 0 215132 | 32 0 32 3553 111.03 4318.7
PRJ 1 576 1.902 0 216284 | 32 0 32 3515 109.84 4318.7
PRE 1 608 1.893 0 218217 | 32 0 32 3536 110.50 4318.7
PRA 1 608 1.873 0 218667 | 32 0 32 3535 110.47 4318.7
PRJ 1 608 1.867 0 219822 | 32 0 32 3538 110.56 4318.7
PRA 1 640 1.870 0 222238 | 32 0 32 3571 111.59 4318.7
PRE 1 640 1.869 0 221794 | 32 0 32 3577 111.78 4318.7
PRJ 1 640 1.869 0 223392 | 32 0 32 3570 111.56 4318.7
PRA 1 672 1.880 0 225774 | 32 0 32 3536 110.50 4318.7
PRE 1 672 1.865 0 225323 | 32 0 32 3529 110.28 4318.7
PRJ 1 672 1.869 0 226915 | 32 0 32 3523 110.09 4318.7
PRA 1 704 1.879 0 229298 | 32 0 32 3524 110.12 4318.7
PRE 1 704 1.853 0 228864 | 32 0 32 3541 110.66 4318.7
PRJ 1 704 1.867 0 230463 | 32 0 32 3548 110.88 4318.7
PRE 1 736 1.842 0 232430 | 32 0 32 3566 111.44 4318.7
PRA 1 736 1.865 0 232881 | 32 0 32 3583 111.97 4318.7
PRJ 1 736 1.857 0 234031 | 32 0 32 3568 111.50 4318.7
PRE 1 768 1.841 0 235968 | 32 0 32 3538 110.56 4318.7
PRA 1 768 1.873 0 236419 | 32 0 32 3538 110.56 4318.7
PRJ 1 768 1.856 0 237566 | 32 0 32 3535 110.47 4318.7
PRE 1 800 1.812 0 239517 | 32 0 32 3549 110.91 4318.7
PRA 1 800 1.846 0 239957 | 32 0 32 3538 110.56 4318.7
PRJ 1 800 1.839 0 241110 | 32 0 32 3544 110.75 4318.7
PRE 1 832 1.826 0 243041 | 32 0 32 3524 110.12 4318.7
PRA 1 832 1.862 0 243507 | 32 0 32 3550 110.94 4318.7
PRJ 1 832 1.858 0 244645 | 32 0 32 3535 110.47 4318.7
PRE 1 864 1.829 0 246542 | 32 0 32 3501 109.41 4318.7
PRA 1 864 1.863 0 247041 | 32 0 32 3534 110.44 4318.7
PRJ 1 864 1.851 0 248219 | 32 0 32 3574 111.69 4318.7
PRE 1 896 1.830 0 250042 | 32 0 32 3500 109.38 4318.7
PRA 1 896 1.864 0 250551 | 32 0 32 3510 109.69 4318.7
PRJ 1 896 1.862 0 251772 | 32 0 32 3553 111.03 4318.7
PRE 1 928 1.855 0 253617 | 32 0 32 3575 111.72 4318.7
PRA 1 928 1.890 0 254136 | 32 0 32 3585 112.03 4318.7
PRJ 1 928 1.887 0 255418 | 32 0 32 3646 113.94 4318.7
PRE 1 960 1.828 0 257142 | 32 0 32 3525 110.16 4318.7
PRA 1 960 1.863 0 257655 | 32 0 32 3519 109.97 4318.7
PRJ 1 960 1.855 0 258957 | 32 0 32 3539 110.59 4318.7
PRE 1 992 1.836 0 260654 | 32 0 32 3512 109.75 4318.7
PRA 1 992 1.866 0 261214 | 32 0 32 3559 111.22 4318.7
PRJ 1 992 1.860 0 262525 | 32 0 32 3568 111.50 4318.7
PRE 1 1024 1.792 0 264237 | 32 0 32 3583 111.97 4318.7
PRA 1 1024 1.826 0 264802 | 32 0 32 3588 112.12 4318.7
PRJ 1 1024 1.818 0 266124 | 32 0 32 3599 112.47 4318.7
PRE 1 1056 1.803 0 267817 | 32 0 32 3580 111.88 4318.7
PRA 1 1056 1.838 0 268400 | 32 0 32 3598 112.44 4318.7
PRJ 1 1056 1.838 0 269742 | 32 0 32 3618 113.06 4318.7
PRE 1 1088 1.843 0 271357 | 32 0 32 3540 110.62 4318.7
PRA 1 1088 1.880 0 271947 | 32 0 32 3547 110.84 4318.7
PRJ 1 1088 1.882 0 273285 | 32 0 32 3543 110.72 4318.7
PRE 1 1120 1.823 0 274938 | 32 0 32 3581 111.91 4318.7
PRA 1 1120 1.853 0 275531 | 32 0 32 3584 112.00 4318.7
PRJ 1 1120 1.857 0 276871 | 32 0 32 3586 112.06 4318.7
PRE 1 1152 1.830 0 278473 | 32 0 32 3535 110.47 4318.7
PRA 1 1152 1.867 0 279067 | 32 0 32 3536 110.50 4318.7
PRJ 1 1152 1.860 0 280408 | 32 0 32 3537 110.53 4318.7
PRE 1 1184 1.791 0 282021 | 32 0 32 3548 110.88 4318.7
PRA 1 1184 1.830 0 282610 | 32 0 32 3543 110.72 4318.7
PRJ 1 1184 1.820 0 283964 | 32 0 32 3556 111.12 4318.7
PRE 1 1216 1.818 0 285577 | 32 0 32 3556 111.12 4318.7
PRA 1 1216 1.856 0 286130 | 32 0 32 3520 110.00 4318.7
PRJ 1 1216 1.852 0 287486 | 32 0 32 3522 110.06 4318.7
PRE 1 1248 1.799 0 289110 | 32 0 32 3533 110.41 4318.7
PRA 1 1248 1.828 0 289618 | 32 0 32 3488 109.00 4318.7
PRJ 1 1248 1.828 0 291069 | 32 0 32 3583 111.97 4318.7
PRE 1 1280 1.815 0 292668 | 32 0 32 3558 111.19 4318.7
PRA 1 1280 1.849 0 293121 | 32 0 32 3503 109.47 4318.7
PRJ 1 1280 1.843 0 294588 | 32 0 32 3519 109.97 4318.7
PRE 1 1311 1.791 0 296100 | 31 0 31 3432 110.71 4183.8
PRE: TOWER_STATE STATE.1 state_bytes=12851214 state_sha256=f5b72795698e9963745d718a03de2aca4df6a470418249c059c390689b7eb908
PRA 1 1311 1.826 0 296606 | 31 0 31 3485 112.42 4183.8
PRA: TOWER_STATE STATE.1 state_bytes=12993968 state_sha256=2bc266d93fa593e469920e333a79fe487c4c0f399eee86f0d5672b7fb1f8d0fb
PRJ 1 1311 1.813 0 298181 | 31 0 31 3593 115.90 4183.8
PRJ: TOWER_STATE STATE.1 state_bytes=13047303 state_sha256=4f658f556ff95413cfbe1800362bf6c4df6a93b9124031a7153be3bb10bf9b07
PRE: TOWER_PASS pass=1 train_bits_a_byte=1.856 dev_bits_a_byte=1.833 dev_regions Q=1.298 P=2.373 N=0.613 M=1.841 deposits=1311/1311 pass_ms=150223 elapsed_ms=301183 train_code=6866102796542 dev_code=764334478662 grain_bits=20
PRA: TOWER_PASS pass=1 train_bits_a_byte=1.884 dev_bits_a_byte=1.867 dev_regions Q=1.256 P=2.365 N=0.540 M=1.877 deposits=1311/1311 pass_ms=150305 elapsed_ms=301624 train_code=6967582779783 dev_code=778568018359 grain_bits=20
PRJ: TOWER_PASS pass=1 train_bits_a_byte=1.882 dev_bits_a_byte=1.868 dev_regions Q=1.283 P=2.386 N=0.669 M=1.877 deposits=1311/1311 pass_ms=150967 elapsed_ms=303186 train_code=6960328507052 dev_code=778970600149 grain_bits=20
PRE 2 32 1.792 0 304762 | 32 0 32 3579 111.84 4318.7
PRA 2 32 1.834 0 305210 | 32 0 32 3586 112.06 4318.7
PRJ 2 32 1.825 0 306749 | 32 0 32 3563 111.34 4318.7
PRE 2 64 1.786 0 308360 | 32 0 32 3598 112.44 4318.7
PRA 2 64 1.818 0 308789 | 32 0 32 3579 111.84 4318.7
PRJ 2 64 1.946 0 310296 | 32 0 32 3547 110.84 4318.7
PRA 2 96 1.846 0 312319 | 32 0 32 3530 110.31 4318.7
PRE 2 96 1.816 0 311913 | 32 0 32 3553 111.03 4318.7
PRJ 2 96 1.996 0 313847 | 32 0 32 3551 110.97 4318.7
PRA 2 128 1.823 0 315873 | 32 0 32 3554 111.06 4318.7
PRE 2 128 1.789 0 315444 | 32 0 32 3531 110.34 4318.7
PRJ 2 128 1.863 0 317415 | 32 0 32 3568 111.50 4318.7
PRE 2 160 1.802 0 319045 | 32 0 32 3601 112.53 4318.7
PRA 2 160 1.841 0 319471 | 32 0 32 3598 112.44 4318.7
PRJ 2 160 1.861 0 320988 | 32 0 32 3573 111.66 4318.7
PRE 2 192 1.770 0 322565 | 32 0 32 3520 110.00 4318.7
PRA 2 192 1.806 0 323015 | 32 0 32 3544 110.75 4318.7
PRJ 2 192 1.815 0 324570 | 32 0 32 3582 111.94 4318.7
PRE 2 224 1.726 0 326176 | 32 0 32 3611 112.84 4318.7
PRA 2 224 1.750 0 326621 | 32 0 32 3606 112.69 4318.7
PRJ 2 224 1.764 0 328170 | 32 0 32 3600 112.50 4318.7
PRE 2 256 1.827 0 329742 | 32 0 32 3566 111.44 4318.7
PRA 2 256 1.869 0 330195 | 32 0 32 3574 111.69 4318.7
PRJ 2 256 1.866 0 331779 | 32 0 32 3609 112.78 4318.7
PRE 2 288 1.788 0 333305 | 32 0 32 3563 111.34 4318.7
PRA 2 288 1.821 0 333705 | 32 0 32 3510 109.69 4318.7
PRJ 2 288 1.819 0 335349 | 32 0 32 3570 111.56 4318.7
PRE 2 320 1.765 0 336845 | 32 0 32 3540 110.62 4318.7
PRA 2 320 1.791 0 337233 | 32 0 32 3528 110.25 4318.7
PRJ 2 320 1.784 0 338942 | 32 0 32 3593 112.28 4318.7
PRA 2 352 1.820 0 340870 | 32 0 32 3637 113.66 4318.7
PRE 2 352 1.798 0 340431 | 32 0 32 3586 112.06 4318.7
PRJ 2 352 1.809 0 342554 | 32 0 32 3612 112.88 4318.7
PRA 2 384 1.833 0 344394 | 32 0 32 3524 110.12 4318.7
PRE 2 384 1.802 0 343983 | 32 0 32 3552 111.00 4318.7
PRJ 2 384 1.827 0 346089 | 32 0 32 3535 110.47 4318.7
PRA 2 416 1.809 0 347908 | 32 0 32 3514 109.81 4318.7
PRE 2 416 1.779 0 347509 | 32 0 32 3526 110.19 4318.7
PRJ 2 416 1.803 0 349629 | 32 0 32 3540 110.62 4318.7
PRE 2 448 1.806 0 351055 | 32 0 32 3546 110.81 4318.7
PRA 2 448 1.812 0 351462 | 32 0 32 3554 111.06 4318.7
PRJ 2 448 1.805 0 353211 | 32 0 32 3582 111.94 4318.7
PRE 2 480 1.805 0 354574 | 32 0 32 3519 109.97 4318.7
PRA 2 480 1.801 0 355027 | 32 0 32 3565 111.41 4318.7
PRJ 2 480 1.798 0 356771 | 32 0 32 3560 111.25 4318.7
PRE 2 512 1.805 0 358129 | 32 0 32 3555 111.09 4318.7
PRA 2 512 1.798 0 358568 | 32 0 32 3541 110.66 4318.7
PRJ 2 512 1.794 0 360378 | 32 0 32 3607 112.72 4318.7
PRE 2 544 1.745 0 361745 | 32 0 32 3616 113.00 4318.7
PRA 2 544 1.759 0 362130 | 32 0 32 3562 111.31 4318.7
PRJ 2 544 1.751 0 363988 | 32 0 32 3610 112.81 4318.7
PRE 2 576 1.798 0 365246 | 32 0 32 3501 109.41 4318.7
PRA 2 576 1.808 0 365648 | 32 0 32 3518 109.94 4318.7
PRJ 2 576 1.801 0 367569 | 32 0 32 3581 111.91 4318.7
PRE 2 608 1.764 0 368792 | 32 0 32 3546 110.81 4318.7
PRA 2 608 1.781 0 369168 | 32 0 32 3520 110.00 4318.7
PRJ 2 608 1.774 0 371151 | 32 0 32 3582 111.94 4318.7
PRE 2 640 1.757 0 372371 | 32 0 32 3579 111.84 4318.7
PRA 2 640 1.786 0 372742 | 32 0 32 3574 111.69 4318.7
PRJ 2 640 1.784 0 374750 | 32 0 32 3599 112.47 4318.7
PRE 2 672 1.763 0 375904 | 32 0 32 3533 110.41 4318.7
PRA 2 672 1.793 0 376272 | 32 0 32 3530 110.31 4318.7
PRJ 2 672 1.782 0 378278 | 32 0 32 3528 110.25 4318.7
PRA 2 704 1.788 0 379799 | 32 0 32 3527 110.22 4318.7
PRE 2 704 1.760 0 379444 | 32 0 32 3540 110.62 4318.7
PRJ 2 704 1.778 0 381832 | 32 0 32 3554 111.06 4318.7
PRA 2 736 1.777 0 383411 | 32 0 32 3612 112.88 4318.7
PRE 2 736 1.754 0 383016 | 32 0 32 3572 111.62 4318.7
PRJ 2 736 1.772 0 385397 | 32 0 32 3565 111.41 4318.7
PRA 2 768 1.789 0 386916 | 32 0 32 3505 109.53 4318.7
PRE 2 768 1.761 0 386537 | 32 0 32 3521 110.03 4318.7
PRJ 2 768 1.781 0 388954 | 32 0 32 3557 111.16 4318.7
PRA 2 800 1.763 0 390445 | 32 0 32 3529 110.28 4318.7
PRE 2 800 1.729 0 390086 | 32 0 32 3549 110.91 4318.7
PRJ 2 800 1.752 0 392515 | 32 0 32 3561 111.28 4318.7
PRE 2 832 1.740 0 393648 | 32 0 32 3562 111.31 4318.7
PRA 2 832 1.774 0 394009 | 32 0 32 3564 111.38 4318.7
PRJ 2 832 1.776 0 396089 | 32 0 32 3574 111.69 4318.7
PRE 2 864 1.747 0 397168 | 32 0 32 3520 110.00 4318.7
PRA 2 864 1.779 0 397562 | 32 0 32 3553 111.03 4318.7
PRJ 2 864 1.775 0 399655 | 32 0 32 3566 111.44 4318.7
PRE 2 896 1.754 0 400676 | 32 0 32 3508 109.62 4318.7
PRA 2 896 1.780 0 401072 | 32 0 32 3510 109.69 4318.7
PRJ 2 896 1.777 0 403265 | 32 0 32 3610 112.81 4318.7
PRE 2 928 1.775 0 404244 | 32 0 32 3568 111.50 4318.7
PRA 2 928 1.806 0 404648 | 32 0 32 3576 111.75 4318.7
PRJ 2 928 1.803 0 406865 | 32 0 32 3600 112.50 4318.7
PRE 2 960 1.751 0 407772 | 32 0 32 3528 110.25 4318.7
PRA 2 960 1.777 0 408177 | 32 0 32 3529 110.28 4318.7
PRJ 2 960 1.779 0 410413 | 32 0 32 3548 110.88 4318.7
PRE 2 992 1.760 0 411285 | 32 0 32 3513 109.78 4318.7
PRA 2 992 1.780 0 411690 | 32 0 32 3513 109.78 4318.7
PRJ 2 992 1.782 0 413942 | 32 0 32 3529 110.28 4318.7
PRE 2 1024 1.803 0 414781 | 32 0 32 3496 109.25 4318.7
PRA 2 1024 1.753 0 415188 | 32 0 32 3498 109.31 4318.7
PRJ 2 1024 1.744 0 417486 | 32 0 32 3544 110.75 4318.7
PRE 2 1056 1.811 0 418305 | 32 0 32 3524 110.12 4318.7
PRA 2 1056 1.763 0 418752 | 32 0 32 3564 111.38 4318.7
PRJ 2 1056 1.767 0 421004 | 32 0 32 3518 109.94 4318.7
PRE 2 1088 1.802 0 421832 | 32 0 32 3527 110.22 4318.7
PRA 2 1088 1.799 0 422286 | 32 0 32 3534 110.44 4318.7
PRJ 2 1088 1.940 0 424539 | 32 0 32 3535 110.47 4318.7
PRE 2 1120 1.770 0 425410 | 32 0 32 3578 111.81 4318.7
PRA 2 1120 1.779 0 425866 | 32 0 32 3580 111.88 4318.7
PRJ 2 1120 1.897 0 428118 | 32 0 32 3579 111.84 4318.7
PRE 2 1152 1.777 0 428946 | 32 0 32 3536 110.50 4318.7
PRA 2 1152 1.792 0 429417 | 32 0 32 3551 110.97 4318.7
PRJ 2 1152 1.837 0 431662 | 32 0 32 3544 110.75 4318.7
PRA 2 1184 1.756 0 432960 | 32 0 32 3543 110.72 4318.7
PRE 2 1184 1.732 0 432490 | 32 0 32 3544 110.75 4318.7
PRJ 2 1184 1.777 0 435186 | 32 0 32 3524 110.12 4318.7
PRA 2 1216 1.783 0 436482 | 32 0 32 3522 110.06 4318.7
PRE 2 1216 1.764 0 436019 | 32 0 32 3529 110.28 4318.7
PRJ 2 1216 1.791 0 438730 | 32 0 32 3544 110.75 4318.7
PRE 2 1248 1.735 0 439554 | 32 0 32 3535 110.47 4318.7
PRA 2 1248 1.753 0 440023 | 32 0 32 3541 110.66 4318.7
PRJ 2 1248 1.767 0 442339 | 32 0 32 3609 112.78 4318.7
PRE 2 1280 1.756 0 443170 | 32 0 32 3616 113.00 4318.7
PRA 2 1280 1.776 0 443652 | 32 0 32 3629 113.41 4318.7
PRJ 2 1280 1.781 0 445943 | 32 0 32 3604 112.62 4318.7
PRE 2 1311 1.732 0 446684 | 31 0 31 3514 113.35 4183.8
PRE: TOWER_STATE STATE.2 state_bytes=12868751 state_sha256=8d5262faa914e68853d704bb6cbee445fda91ee7d86ce576415be6c0f867a870
PRA 2 1311 1.759 0 447190 | 31 0 31 3538 114.13 4183.8
PRA: TOWER_STATE STATE.2 state_bytes=12987067 state_sha256=5728ba0a1ac786e37d7d672d0946b7c7ae43f73ad60039c41730ef19ac217520
PRJ 2 1311 1.752 0 449951 | 31 0 31 4008 129.29 4183.8
PRJ: TOWER_STATE STATE.2 state_bytes=13068501 state_sha256=5c1f4c1f484e5108e57aeaa0316928c34d15bf1e243e8e37f306257c118da927
PRE: TOWER_PASS pass=2 train_bits_a_byte=1.773 dev_bits_a_byte=1.785 dev_regions Q=1.243 P=2.353 N=0.513 M=1.793 deposits=1311/1311 pass_ms=150517 elapsed_ms=451701 train_code=6557766417723 dev_code=744381352953 grain_bits=20
PRE: TOWER_DONE state_bytes=12868751 state_sha256=8d5262faa914e68853d704bb6cbee445fda91ee7d86ce576415be6c0f867a870 elapsed_ms=451792
PRE: RUN_RECEIPT exit=0 wall_s=452.2 peak_rss_kib=316164 user_s=2745.8
PRA: TOWER_PASS pass=2 train_bits_a_byte=1.793 dev_bits_a_byte=1.824 dev_regions Q=1.222 P=2.382 N=0.457 M=1.833 deposits=1311/1311 pass_ms=150484 elapsed_ms=452109 train_code=6632599178514 dev_code=760427673615 grain_bits=20
PRA: TOWER_DONE state_bytes=12987067 state_sha256=5728ba0a1ac786e37d7d672d0946b7c7ae43f73ad60039c41730ef19ac217520 elapsed_ms=452175
PRA: RUN_RECEIPT exit=0 wall_s=452.6 peak_rss_kib=316756 user_s=2754.1
PRJ: TOWER_PASS pass=2 train_bits_a_byte=1.807 dev_bits_a_byte=1.810 dev_regions Q=1.233 P=2.378 N=0.485 M=1.819 deposits=1311/1311 pass_ms=151026 elapsed_ms=454212 train_code=6684342628318 dev_code=754855957063 grain_bits=20
PRJ: TOWER_DONE state_bytes=13068501 state_sha256=5c1f4c1f484e5108e57aeaa0316928c34d15bf1e243e8e37f306257c118da927 elapsed_ms=454284
PRJ: RUN_RECEIPT exit=0 wall_s=454.7 peak_rss_kib=310144 user_s=2750.3
```
## The reads at the equals, the rules, and where the contacts' bilinear weight sits

```text

STEP 7 READS (read-unit-tower-written, one after the other; TOWER_WRITTEN_PROGRESS problems=64 at 1580, 1581, 1582 ms)
PRA: TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=48
PRA: TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299827 prompt_units=468588 released_units=114430 most_units_a_problem=4712 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17049
PRA: TOWER_WRITTEN_FILES free_sha256=af9b24d620658a4b27cfa0d93f6989f65449fb84cb92010e7d108686d988696b marks_sha256=faaab34e0000f14e7dcab3732620cd39e179c02642f4534601bdf839dcdfdf99
PRA: RUN_RECEIPT exit=0 wall_s=17.1 peak_rss_kib=42436 user_s=133.6
PRA: READ_GUARD ok progress 64 by 1604 ms
PRJ: TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=48
PRJ: TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299840 prompt_units=468588 released_units=112171 most_units_a_problem=4694 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=17043
PRJ: TOWER_WRITTEN_FILES free_sha256=636ccdbc638116fe64f0868b0aeda099a60b3c6f172c3c66f83a7740d298982d marks_sha256=fc958c3d6698ec748ee15552f479dcd0c7c8e845b46c90052a1a0b31c6a75625
PRJ: RUN_RECEIPT exit=0 wall_s=17.1 peak_rss_kib=43508 user_s=132.3
PRJ: READ_GUARD ok progress 64 by 1653 ms
PRE: TOWER_WRITTEN_OPEN problems=747 most_calculations=9 window=472 elapsed_ms=48
PRE: TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299728 prompt_units=468588 released_units=114082 most_units_a_problem=4692 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=16839
PRE: TOWER_WRITTEN_FILES free_sha256=73960033b2427a92d6f1ad1d77e56c76397837a475ae82811a260c68c9af6a56 marks_sha256=6d822dc68765d4815d110867050e20f4a7d5ab8a38dfaa5c1c3a70f02b1d67cc
PRE: RUN_RECEIPT exit=0 wall_s=16.9 peak_rss_kib=44408 user_s=132.6
PRE: READ_GUARD ok progress 64 by 1603 ms

STEP 8 RULES (opened worktree's tools/gsm8k/written_rules.py; rules_1 to rules_6 whole; gaps in part 4)
RULES rings digit/read_C rotor/read_PP rotor/read_PR turns/read_PRT turns/read_PRS strands/read_PRK strands/read_PRI opened/read_PRA opened/read_PRJ opened/read_PRE; DEADLINE 60 s
WRITTEN dir=digit/read_C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
RINGS dir=digit/read_C n=312 mod9=44 foil9=39 mod10=109 foil10=76 mod11=30 foil11=26 mod990=6 foil990=1 lead_length=25 foil_lead_length=16
WRITTEN dir=rotor/read_PP problems=747 a_on_problem=41 b_free_calculations=1085 b_free_right=44 c_first_calculations=649 c_from_question=42 b_equals=109/2448 met=104/1572 never_met=5/876 binary +=14/470 -=11/388 *=63/897 /=16/343
RINGS dir=rotor/read_PP n=312 mod9=39 foil9=32 mod10=113 foil10=84 mod11=23 foil11=23 mod990=3 foil990=1 lead_length=15 foil_lead_length=14
WRITTEN dir=rotor/read_PR problems=747 a_on_problem=59 b_free_calculations=1679 b_free_right=113 c_first_calculations=706 c_from_question=32 b_equals=277/2448 met=259/1572 never_met=18/876 binary +=26/470 -=26/388 *=158/897 /=52/343
RINGS dir=rotor/read_PR n=312 mod9=32 foil9=35 mod10=123 foil10=88 mod11=27 foil11=30 mod990=4 foil990=4 lead_length=34 foil_lead_length=24
WRITTEN dir=turns/read_PRT problems=747 a_on_problem=59 b_free_calculations=1543 b_free_right=58 c_first_calculations=673 c_from_question=19 b_equals=240/2448 met=216/1572 never_met=24/876 binary +=26/470 -=28/388 *=124/897 /=46/343
RINGS dir=turns/read_PRT n=312 mod9=45 foil9=25 mod10=122 foil10=76 mod11=37 foil11=23 mod990=7 foil990=1 lead_length=32 foil_lead_length=21
WRITTEN dir=turns/read_PRS problems=747 a_on_problem=41 b_free_calculations=1557 b_free_right=69 c_first_calculations=685 c_from_question=34 b_equals=288/2448 met=269/1572 never_met=19/876 binary +=29/470 -=24/388 *=169/897 /=48/343
RINGS dir=turns/read_PRS n=312 mod9=35 foil9=22 mod10=132 foil10=95 mod11=20 foil11=21 mod990=2 foil990=4 lead_length=28 foil_lead_length=19
WRITTEN dir=strands/read_PRK problems=747 a_on_problem=49 b_free_calculations=1586 b_free_right=72 c_first_calculations=697 c_from_question=33 b_equals=230/2448 met=214/1572 never_met=16/876 binary +=24/470 -=20/388 *=138/897 /=32/343
RINGS dir=strands/read_PRK n=312 mod9=40 foil9=34 mod10=133 foil10=86 mod11=33 foil11=24 mod990=4 foil990=1 lead_length=25 foil_lead_length=24
WRITTEN dir=strands/read_PRI problems=747 a_on_problem=40 b_free_calculations=1332 b_free_right=64 c_first_calculations=660 c_from_question=28 b_equals=214/2448 met=192/1572 never_met=22/876 binary +=24/470 -=23/388 *=111/897 /=36/343
RINGS dir=strands/read_PRI n=312 mod9=50 foil9=33 mod10=128 foil10=92 mod11=21 foil11=26 mod990=3 foil990=2 lead_length=30 foil_lead_length=24
WRITTEN dir=opened/read_PRA problems=747 a_on_problem=50 b_free_calculations=1300 b_free_right=50 c_first_calculations=666 c_from_question=23 b_equals=286/2448 met=268/1572 never_met=18/876 binary +=36/470 -=32/388 *=156/897 /=47/343
RINGS dir=opened/read_PRA n=312 mod9=33 foil9=32 mod10=122 foil10=91 mod11=25 foil11=29 mod990=3 foil990=3 lead_length=38 foil_lead_length=28
WRITTEN dir=opened/read_PRJ problems=747 a_on_problem=48 b_free_calculations=1272 b_free_right=41 c_first_calculations=658 c_from_question=21 b_equals=233/2448 met=214/1572 never_met=19/876 binary +=31/470 -=25/388 *=140/897 /=29/343
RINGS dir=opened/read_PRJ n=312 mod9=42 foil9=39 mod10=123 foil10=78 mod11=34 foil11=29 mod990=9 foil990=3 lead_length=43 foil_lead_length=28
WRITTEN dir=opened/read_PRE problems=747 a_on_problem=60 b_free_calculations=1153 b_free_right=77 c_first_calculations=635 c_from_question=38 b_equals=245/2448 met=219/1572 never_met=26/876 binary +=25/470 -=26/388 *=124/897 /=48/343
RINGS dir=opened/read_PRE n=312 mod9=40 foil9=29 mod10=128 foil10=84 mod11=30 foil11=28 mod990=8 foil990=2 lead_length=32 foil_lead_length=27
RUN_RECEIPT exit=0 wall_s=20.6 peak_rss_kib=60852 user_s=20.5

RULES heard turns/read_PRT strands/read_PRK opened/read_PRA opened/read_PRJ opened/read_PRE; DEADLINE 60 s
(its WRITTEN lines repeat those above, verbatim)
HEARD dir=turns/read_PRT 0=24/876 1=8/239 2-3=16/224 4-7=9/255 8-15=42/326 16+=141/528
HEARD dir=strands/read_PRK 0=16/876 1=10/239 2-3=12/224 4-7=8/255 8-15=42/326 16+=142/528
HEARD dir=opened/read_PRA 0=18/876 1=14/239 2-3=23/224 4-7=15/255 8-15=40/326 16+=176/528
HEARD dir=opened/read_PRJ 0=19/876 1=10/239 2-3=14/224 4-7=14/255 8-15=32/326 16+=144/528
HEARD dir=opened/read_PRE 0=26/876 1=12/239 2-3=13/224 4-7=10/255 8-15=39/326 16+=145/528
RUN_RECEIPT exit=0 wall_s=10.3 peak_rss_kib=62120 user_s=10.3

RULES pair opened/read_PRA opened/read_PRE; DEADLINE 60 s
PAIRED met_only_a=145 met_only_b=96 met_both=123 never_only_a=11 never_only_b=19 never_both=7
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=60944 user_s=4.2

RULES pair opened/read_PRA opened/read_PRJ; DEADLINE 60 s
PAIRED met_only_a=137 met_only_b=83 met_both=131 never_only_a=13 never_only_b=14 never_both=5
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=61280 user_s=4.2

RULES pair opened/read_PRA turns/read_PRT; DEADLINE 60 s
PAIRED met_only_a=142 met_only_b=90 met_both=126 never_only_a=16 never_only_b=22 never_both=2
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=61088 user_s=4.2

RULES pair opened/read_PRA strands/read_PRK; DEADLINE 60 s
PAIRED met_only_a=133 met_only_b=79 met_both=135 never_only_a=12 never_only_b=10 never_both=6
RUN_RECEIPT exit=0 wall_s=4.2 peak_rss_kib=61832 user_s=4.2
(each pair log also carries its two WRITTEN lines, verbatim as above)

STEP 9 PAIR MODES (read-tower-pair-modes, founded then final state, each whole)
## PRA founded (opened/PRA_STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=57 0:16 1:15 2:16 3:15 4:13 5:13 6:14 7:17 8:15 9:15 10:12 11:14 12:15 13:15 14:15 15:14 16:15 17:13 18:16 19:15 20:16 21:16 22:16 23:16 24:15 25:15 26:18 27:14 28:13 29:13 30:13 31:12 32:15 33:12 34:19 35:15 36:13 37:16 38:13 39:15 40:17 41:14 42:16 43:16 44:16 45:14 46:16 47:18 48:17 49:15 50:13 51:15 52:15 53:14 54:15 55:16 56:13 57:12 58:16 59:14 60:16 61:12 62:16 63:19 64:12 65:12 66:12 67:12 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=53 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0 64:0 65:0 66:0 67:0 68:250 69:250 70:250 71:250 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=101 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,250,0,0,0,0,0,0,0;0,0,0,0,0,0,250,0,0,0,0,0,0;0,0,0,0,0,0,0,250,0,0,0,0,0;0,0,0,0,0,0,0,0,250,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:250/250000 99:250/250000 999:250/250000 9999:250/250000
TOWER_PAIR_MODES level=1 drive=first whole_bits=57 0:16 1:14 2:14 3:18 4:17 5:16 6:15 7:17 8:15 9:17 10:18 11:14 12:18 13:12 14:14 15:13 16:14 17:15 18:16 19:13 20:16 21:18 22:17 23:16 24:17 25:15 26:16 27:18 28:16 29:14 30:15 31:15 32:15 33:16 34:18 35:15 36:16 37:17 38:13 39:13 40:15 41:16 42:16 43:15 44:16 45:16 46:15 47:17 48:14 49:17 50:18 51:16 52:16 53:19 54:14 55:18 56:15 57:15 58:15 59:14 60:15 61:17 62:17 63:19
TOWER_PAIR_MODES level=1 drive=second whole_bits=0 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0
RUN_RECEIPT exit=0 wall_s=0.1 peak_rss_kib=27296 user_s=0.0
## PRA final (opened/PRA/STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=64 0:5 1:7 2:5 3:6 4:7 5:6 6:5 7:6 8:11 9:9 10:7 11:8 12:5 13:4 14:12 15:6 16:10 17:16 18:21 19:14 20:9 21:10 22:7 23:7 24:16 25:25 26:14 27:8 28:12 29:8 30:7 31:7 32:27 33:24 34:17 35:15 36:8 37:16 38:11 39:14 40:46 41:18 42:28 43:12 44:15 45:16 46:14 47:15 48:49 49:35 50:22 51:25 52:14 53:16 54:14 55:18 56:41 57:30 58:26 59:24 60:23 61:25 62:19 63:22 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=64 0:5 1:7 2:6 3:5 4:7 5:7 6:5 7:7 8:13 9:9 10:7 11:9 12:5 13:5 14:11 15:5 16:11 17:18 18:20 19:12 20:9 21:12 22:7 23:7 24:15 25:28 26:13 27:9 28:12 29:9 30:6 31:8 32:26 33:25 34:17 35:18 36:8 37:18 38:10 39:14 40:42 41:18 42:25 43:14 44:13 45:16 46:14 47:15 48:39 49:30 50:20 51:21 52:15 53:17 54:14 55:18 56:53 57:28 58:26 59:22 60:25 61:26 62:20 63:21 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=119 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 998,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:0/0 99:0/0 999:0/0 9999:0/0
TOWER_PAIR_MODES level=1 drive=first whole_bits=63 0:8 1:5 2:8 3:10 4:7 5:9 6:6 7:8 8:12 9:6 10:18 11:7 12:6 13:10 14:8 15:14 16:13 17:19 18:33 19:12 20:8 21:15 22:15 23:10 24:6 25:21 26:10 27:10 28:9 29:13 30:10 31:12 32:2 33:17 34:10 35:16 36:13 37:16 38:15 39:14 40:22 41:95 42:28 43:13 44:16 45:26 46:18 47:16 48:21 49:29 50:14 51:20 52:15 53:12 54:21 55:15 56:2 57:17 58:27 59:30 60:18 61:24 62:18 63:21
TOWER_PAIR_MODES level=1 drive=second whole_bits=63 0:11 1:8 2:12 3:10 4:11 5:9 6:10 7:7 8:13 9:9 10:19 11:10 12:8 13:10 14:10 15:13 16:13 17:16 18:22 19:13 20:9 21:16 22:12 23:9 24:9 25:21 26:12 27:13 28:10 29:13 30:9 31:12 32:12 33:17 34:13 35:15 36:15 37:14 38:14 39:11 40:24 41:89 42:23 43:12 44:16 45:25 46:14 47:14 48:24 49:28 50:16 51:15 52:15 53:16 54:15 55:18 56:8 57:20 58:20 59:23 60:17 61:18 62:19 63:21
RUN_RECEIPT exit=0 wall_s=0.1 peak_rss_kib=38848 user_s=0.1
## PRJ founded (opened/PRJ_STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=57 0:17 1:16 2:16 3:15 4:14 5:14 6:14 7:18 8:16 9:17 10:13 11:15 12:16 13:15 14:16 15:15 16:15 17:14 18:17 19:15 20:16 21:17 22:17 23:17 24:16 25:15 26:19 27:14 28:14 29:14 30:13 31:13 32:16 33:13 34:20 35:15 36:14 37:17 38:14 39:16 40:18 41:14 42:16 43:17 44:17 45:15 46:17 47:19 48:19 49:16 50:14 51:16 52:16 53:15 54:15 55:17 56:14 57:13 58:17 59:16 60:17 61:13 62:16 63:19 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=0 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=0 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:0/0 99:0/0 999:0/0 9999:0/0
TOWER_PAIR_MODES level=1 drive=first whole_bits=57 0:16 1:14 2:14 3:18 4:17 5:16 6:15 7:17 8:15 9:17 10:18 11:14 12:18 13:12 14:14 15:13 16:14 17:15 18:16 19:13 20:16 21:18 22:17 23:16 24:17 25:15 26:16 27:18 28:16 29:14 30:15 31:15 32:15 33:16 34:18 35:15 36:16 37:17 38:13 39:13 40:15 41:16 42:16 43:15 44:16 45:16 46:15 47:17 48:14 49:17 50:18 51:16 52:16 53:19 54:14 55:18 56:15 57:15 58:15 59:14 60:15 61:17 62:17 63:19
TOWER_PAIR_MODES level=1 drive=second whole_bits=0 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0
RUN_RECEIPT exit=0 wall_s=0.0 peak_rss_kib=26076 user_s=0.0
## PRJ final (opened/PRJ/STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=64 0:9 1:4 2:5 3:6 4:5 5:8 6:7 7:4 8:12 9:17 10:7 11:15 12:12 13:4 14:12 15:7 16:20 17:13 18:14 19:9 20:8 21:8 22:8 23:4 24:15 25:15 26:20 27:14 28:9 29:10 30:10 31:8 32:16 33:27 34:13 35:13 36:13 37:16 38:13 39:14 40:48 41:36 42:16 43:17 44:16 45:14 46:16 47:19 48:29 49:31 50:27 51:20 52:18 53:18 54:12 55:22 56:24 57:26 58:31 59:27 60:30 61:18 62:20 63:21 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=64 0:10 1:5 2:6 3:6 4:5 5:7 6:7 7:4 8:12 9:15 10:8 11:14 12:13 13:5 14:13 15:9 16:20 17:15 18:16 19:9 20:9 21:9 22:8 23:5 24:16 25:19 26:16 27:16 28:9 29:9 30:10 31:8 32:14 33:28 34:15 35:17 36:15 37:16 38:12 39:14 40:28 41:31 42:20 43:15 44:18 45:14 46:17 47:19 48:26 49:22 50:25 51:19 52:19 53:18 54:14 55:22 56:31 57:34 58:30 59:24 60:29 61:22 62:21 63:19 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=119 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 998,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:0/0 99:0/0 999:0/0 9999:0/0
TOWER_PAIR_MODES level=1 drive=first whole_bits=63 0:3 1:2 2:9 3:7 4:13 5:10 6:11 7:11 8:6 9:6 10:11 11:14 12:13 13:8 14:10 15:9 16:26 17:34 18:6 19:18 20:7 21:10 22:9 23:14 24:12 25:8 26:18 27:14 28:12 29:8 30:9 31:14 32:1 33:26 34:21 35:28 36:12 37:14 38:21 39:15 40:5 41:43 42:27 43:16 44:18 45:14 46:16 47:26 48:10 49:15 50:27 51:19 52:25 53:25 54:17 55:26 56:14 57:24 58:24 59:27 60:18 61:32 62:21 63:15
TOWER_PAIR_MODES level=1 drive=second whole_bits=63 0:9 1:8 2:9 3:12 4:12 5:9 6:9 7:10 8:9 9:11 10:11 11:11 12:13 13:9 14:8 15:8 16:25 17:36 18:10 19:19 20:11 21:11 22:8 23:12 24:11 25:9 26:18 27:13 28:11 29:8 30:8 31:12 32:5 33:23 34:20 35:24 36:12 37:11 38:17 39:15 40:7 41:42 42:24 43:14 44:18 45:13 46:17 47:21 48:11 49:13 50:26 51:20 52:24 53:21 54:17 55:30 56:16 57:30 58:23 59:24 60:16 61:27 62:21 63:18
RUN_RECEIPT exit=0 wall_s=0.1 peak_rss_kib=40592 user_s=0.1
## PRE founded (opened/PRE_STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=57 0:16 1:15 2:16 3:15 4:13 5:13 6:14 7:17 8:15 9:15 10:12 11:14 12:15 13:15 14:15 15:14 16:15 17:13 18:16 19:15 20:16 21:16 22:16 23:16 24:15 25:15 26:18 27:14 28:13 29:13 30:13 31:12 32:15 33:12 34:19 35:15 36:13 37:16 38:13 39:15 40:17 41:14 42:16 43:16 44:16 45:14 46:16 47:18 48:17 49:15 50:13 51:15 52:15 53:14 54:15 55:16 56:13 57:12 58:16 59:14 60:16 61:12 62:16 63:19 64:12 65:12 66:12 67:12 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=53 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0 64:0 65:0 66:0 67:0 68:250 69:250 70:250 71:250 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=101 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,250,0,0,0,0,0,0,0;0,0,0,0,0,0,250,0,0,0,0,0,0;0,0,0,0,0,0,0,250,0,0,0,0,0;0,0,0,0,0,0,0,0,250,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:250/250000 99:250/250000 999:250/250000 9999:250/250000
TOWER_PAIR_MODES level=1 drive=first whole_bits=57 0:16 1:14 2:14 3:18 4:17 5:16 6:15 7:17 8:15 9:17 10:18 11:14 12:18 13:12 14:14 15:13 16:14 17:15 18:16 19:13 20:16 21:18 22:17 23:16 24:17 25:15 26:16 27:18 28:16 29:14 30:15 31:15 32:15 33:16 34:18 35:15 36:16 37:17 38:13 39:13 40:15 41:16 42:16 43:15 44:16 45:16 46:15 47:17 48:14 49:17 50:18 51:16 52:16 53:19 54:14 55:18 56:15 57:15 58:15 59:14 60:15 61:17 62:17 63:19
TOWER_PAIR_MODES level=1 drive=second whole_bits=0 0:0 1:0 2:0 3:0 4:0 5:0 6:0 7:0 8:0 9:0 10:0 11:0 12:0 13:0 14:0 15:0 16:0 17:0 18:0 19:0 20:0 21:0 22:0 23:0 24:0 25:0 26:0 27:0 28:0 29:0 30:0 31:0 32:0 33:0 34:0 35:0 36:0 37:0 38:0 39:0 40:0 41:0 42:0 43:0 44:0 45:0 46:0 47:0 48:0 49:0 50:0 51:0 52:0 53:0 54:0 55:0 56:0 57:0 58:0 59:0 60:0 61:0 62:0 63:0
RUN_RECEIPT exit=0 wall_s=0.0 peak_rss_kib=25256 user_s=0.0
## PRE final (opened/PRE/STATE)
TOWER_PAIR_MODES level=0 drive=first whole_bits=64 0:4 1:6 2:9 3:7 4:5 5:6 6:3 7:7 8:7 9:10 10:10 11:10 12:12 13:6 14:4 15:8 16:13 17:11 18:18 19:14 20:14 21:8 22:7 23:9 24:11 25:12 26:12 27:10 28:11 29:10 30:15 31:7 32:10 33:15 34:21 35:17 36:12 37:17 38:15 39:13 40:19 41:24 42:18 43:21 44:16 45:17 46:14 47:18 48:75 49:39 50:19 51:18 52:21 53:10 54:20 55:14 56:56 57:26 58:35 59:19 60:20 61:20 62:21 63:21 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_MODES level=0 drive=second whole_bits=64 0:5 1:6 2:9 3:9 4:7 5:7 6:3 7:8 8:7 9:13 10:10 11:9 12:14 13:7 14:5 15:8 16:13 17:12 18:14 19:12 20:15 21:9 22:8 23:10 24:12 25:12 26:12 27:12 28:15 29:11 30:17 31:8 32:12 33:14 34:19 35:17 36:12 37:18 38:16 39:13 40:20 41:23 42:20 43:20 44:16 45:15 46:17 47:21 48:63 49:34 50:18 51:18 52:21 53:10 54:22 55:17 56:44 57:22 58:37 59:19 60:24 61:20 62:21 63:18 64:0 65:0 66:0 67:0 68:0 69:0 70:0 71:0 72:0 73:0 74:0 75:0
TOWER_PAIR_STRANDS level=0 whole_bits=119 groups=modes,turned9,turned99,turned999,turned9999,stepped9,stepped99,stepped999,stepped9999,held9,held99,held999,held9999 999,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,0,0,0,0,0,0,0,0
TOWER_PAIR_COMPARISON level=0 (ring:thousandths/millionths) 9:0/0 99:0/0 999:0/0 9999:0/0
TOWER_PAIR_MODES level=1 drive=first whole_bits=64 0:10 1:3 2:7 3:7 4:9 5:9 6:9 7:7 8:2 9:7 10:9 11:19 12:9 13:16 14:6 15:12 16:19 17:18 18:10 19:10 20:5 21:12 22:16 23:5 24:2 25:7 26:17 27:13 28:4 29:12 30:10 31:12 32:16 33:15 34:37 35:15 36:13 37:17 38:13 39:11 40:82 41:38 42:11 43:18 44:16 45:18 46:16 47:22 48:22 49:36 50:21 51:16 52:21 53:13 54:20 55:14 56:9 57:20 58:24 59:25 60:18 61:16 62:18 63:28
TOWER_PAIR_MODES level=1 drive=second whole_bits=64 0:13 1:7 2:9 3:9 4:9 5:7 6:10 7:6 8:5 9:9 10:10 11:19 12:11 13:18 14:9 15:11 16:19 17:18 18:13 19:10 20:7 21:12 22:13 23:7 24:5 25:7 26:16 27:13 28:8 29:12 30:11 31:15 32:16 33:14 34:37 35:15 36:15 37:15 38:13 39:11 40:59 41:34 42:13 43:15 44:17 45:17 46:15 47:19 48:32 49:32 50:19 51:16 52:21 53:15 54:19 55:18 56:12 57:18 58:24 59:23 60:16 61:16 62:18 63:31
RUN_RECEIPT exit=0 wall_s=0.1 peak_rss_kib=39352 user_s=0.1
```
## The gaps: how wrong the wrong values are, and what they are written from

```text

tower | within x2 | within x10 | leading digit (foil) | leading digit and length (foil) | last digit, mod10 (foil) | heard result
C | 39% | 87% | 10% (13%) | 5% (4%) | 32% (23%) | 99%
PP | 46% | 90% | 9% (10%) | 5% (4%) | 29% (21%) | 99%
PR | 55% | 92% | 12% (12%) | 9% (6%) | 38% (29%) | 100%
PRT | 54% | 92% | 14% (14%) | 10% (6%) | 37% (28%) | 98%
PRS | 50% | 93% | 10% (12%) | 7% (5%) | 38% (27%) | 99%
PRK | 49% | 91% | 12% (14%) | 8% (6%) | 37% (28%) | 100%
PRI | 51% | 92% | 12% (12%) | 8% (5%) | 37% (29%) | 98%
PRA | 52% | 91% | 12% (14%) | 9% (5%) | 39% (29%) | 97%
PRJ | 53% | 91% | 14% (14%) | 11% (6%) | 36% (27%) | 100%
PRE | 50% | 92% | 12% (13%) | 7% (5%) | 38% (29%) | 99%

STEP 8 GAPS (opened/rules_7.log, whole apart from its ten WRITTEN lines, which repeat part 3's verbatim)
RULES gaps digit/read_C rotor/read_PP rotor/read_PR turns/read_PRT turns/read_PRS strands/read_PRK strands/read_PRI opened/read_PRA opened/read_PRJ opened/read_PRE; DEADLINE 60 s
GAPS dir=digit/read_C set=all n=2448 right=190 wrong=2258 unfinished=17 not_number=1 unread=0 numbers=2240
GAP_SIZE dir=digit/read_C set=all n=2240 x2=883 x10=1956 tenth=45 opposite_sign=0 smaller=1521 larger=719 digits=1081 foil_digits=769/2200
GAP_LEAD dir=digit/read_C set=all n=2197 lead=223 foil_lead=285/2157 lead_length=109 foil_lead_length=92/2157 one_digit=550 foil_one_digit=341/2157
GAP_RINGS dir=digit/read_C set=all n=2198 mod9=203 foil9=232/2158 mod10=703 foil10=490/2158 mod11=102 foil11=161/2158 mod7=230 foil7=285/2158 mod13=91 foil13=144/2158
GAP_FROM dir=digit/read_C set=all n=2240 heard_result=2211 operand=221 other_operation=107/1909
GAP_WRITES dir=digit/read_C set=all written=2430 distinct=87 top10=1583 commonest=8:474:35
GAP_LENGTH dir=digit/read_C set=all 1=85/485 2=95/1252 3=10/508 4=0/139 5+=0/64
GAPS dir=digit/read_C set=met n=1572 right=176 wrong=1396 unfinished=2 not_number=1 unread=0 numbers=1393
GAP_SIZE dir=digit/read_C set=met n=1393 x2=636 x10=1290 tenth=20 opposite_sign=0 smaller=958 larger=435 digits=699 foil_digits=507/1362
GAP_LEAD dir=digit/read_C set=met n=1385 lead=101 foil_lead=148/1354 lead_length=47 foil_lead_length=58/1354 one_digit=426 foil_one_digit=269/1354
GAP_RINGS dir=digit/read_C set=met n=1386 mod9=111 foil9=132/1355 mod10=426 foil10=270/1355 mod11=50 foil11=93/1355 mod7=126 foil7=181/1355 mod13=35 foil13=88/1355
GAP_FROM dir=digit/read_C set=met n=1393 heard_result=1386 operand=153 other_operation=94/1321
GAP_WRITES dir=digit/read_C set=met written=1569 distinct=62 top10=1183 commonest=8:334:33
GAP_LENGTH dir=digit/read_C set=met 1=80/383 2=90/878 3=6/264 4=0/44 5+=0/3
GAPS dir=digit/read_C set=never n=876 right=14 wrong=862 unfinished=15 not_number=0 unread=0 numbers=847
GAP_SIZE dir=digit/read_C set=never n=847 x2=247 x10=666 tenth=25 opposite_sign=0 smaller=563 larger=284 digits=382 foil_digits=253/842
GAP_LEAD dir=digit/read_C set=never n=812 lead=122 foil_lead=127/807 lead_length=62 foil_lead_length=37/807 one_digit=124 foil_one_digit=63/807
GAP_RINGS dir=digit/read_C set=never n=812 mod9=92 foil9=89/807 mod10=277 foil10=190/807 mod11=52 foil11=65/807 mod7=104 foil7=114/807 mod13=56 foil13=50/807
GAP_FROM dir=digit/read_C set=never n=847 heard_result=825 operand=68 other_operation=13/588
GAP_WRITES dir=digit/read_C set=never written=861 distinct=71 top10=542 commonest=8:140:2
GAP_LENGTH dir=digit/read_C set=never 1=5/102 2=5/374 3=4/244 4=0/95 5+=0/61
GAPS dir=rotor/read_PP set=all n=2448 right=109 wrong=2339 unfinished=33 not_number=6 unread=0 numbers=2300
GAP_SIZE dir=rotor/read_PP set=all n=2300 x2=1047 x10=2076 tenth=56 opposite_sign=0 smaller=1316 larger=984 digits=1270 foil_digits=850/2267
GAP_LEAD dir=rotor/read_PP set=all n=2256 lead=206 foil_lead=229/2221 lead_length=119 foil_lead_length=92/2221 one_digit=613 foil_one_digit=333/2221
GAP_RINGS dir=rotor/read_PP set=all n=2256 mod9=161 foil9=198/2221 mod10=651 foil10=471/2221 mod11=121 foil11=178/2221 mod7=252 foil7=281/2221 mod13=89 foil13=146/2221
GAP_FROM dir=rotor/read_PP set=all n=2300 heard_result=2280 operand=130 other_operation=95/1976
GAP_WRITES dir=rotor/read_PP set=all written=2409 distinct=114 top10=1628 commonest=8:716:44
GAP_LENGTH dir=rotor/read_PP set=all 1=64/485 2=38/1252 3=7/508 4=0/139 5+=0/64
GAPS dir=rotor/read_PP set=met n=1572 right=104 wrong=1468 unfinished=3 not_number=2 unread=0 numbers=1463
GAP_SIZE dir=rotor/read_PP set=met n=1463 x2=778 x10=1388 tenth=36 opposite_sign=0 smaller=814 larger=649 digits=871 foil_digits=556/1435
GAP_LEAD dir=rotor/read_PP set=met n=1456 lead=114 foil_lead=129/1428 lead_length=72 foil_lead_length=56/1428 one_digit=486 foil_one_digit=276/1428
GAP_RINGS dir=rotor/read_PP set=met n=1456 mod9=71 foil9=103/1428 mod10=365 foil10=243/1428 mod11=71 foil11=111/1428 mod7=161 foil7=196/1428 mod13=44 foil13=80/1428
GAP_FROM dir=rotor/read_PP set=met n=1463 heard_result=1461 operand=86 other_operation=85/1390
GAP_WRITES dir=rotor/read_PP set=met written=1567 distinct=78 top10=1143 commonest=8:574:42
GAP_LENGTH dir=rotor/read_PP set=met 1=62/383 2=36/878 3=6/264 4=0/44 5+=0/3
GAPS dir=rotor/read_PP set=never n=876 right=5 wrong=871 unfinished=30 not_number=4 unread=0 numbers=837
GAP_SIZE dir=rotor/read_PP set=never n=837 x2=269 x10=688 tenth=20 opposite_sign=0 smaller=502 larger=335 digits=399 foil_digits=260/830
GAP_LEAD dir=rotor/read_PP set=never n=800 lead=92 foil_lead=100/791 lead_length=47 foil_lead_length=28/791 one_digit=127 foil_one_digit=51/791
GAP_RINGS dir=rotor/read_PP set=never n=800 mod9=90 foil9=82/791 mod10=286 foil10=195/791 mod11=50 foil11=68/791 mod7=91 foil7=129/791 mod13=45 foil13=63/791
GAP_FROM dir=rotor/read_PP set=never n=837 heard_result=819 operand=44 other_operation=10/586
GAP_WRITES dir=rotor/read_PP set=never written=842 distinct=99 top10=511 commonest=8:142:2
GAP_LENGTH dir=rotor/read_PP set=never 1=2/102 2=2/374 3=1/244 4=0/95 5+=0/61
GAPS dir=rotor/read_PR set=all n=2448 right=277 wrong=2171 unfinished=0 not_number=9 unread=0 numbers=2162
GAP_SIZE dir=rotor/read_PR set=all n=2162 x2=1181 x10=1998 tenth=80 opposite_sign=0 smaller=1233 larger=929 digits=1362 foil_digits=883/2125
GAP_LEAD dir=rotor/read_PR set=all n=2117 lead=252 foil_lead=255/2079 lead_length=196 foil_lead_length=122/2079 one_digit=690 foil_one_digit=352/2079
GAP_RINGS dir=rotor/read_PR set=all n=2117 mod9=180 foil9=205/2079 mod10=809 foil10=608/2079 mod11=79 foil11=169/2079 mod7=193 foil7=280/2079 mod13=100 foil13=148/2079
GAP_FROM dir=rotor/read_PR set=all n=2162 heard_result=2155 operand=197 other_operation=74/1827
GAP_WRITES dir=rotor/read_PR set=all written=2439 distinct=88 top10=1540 commonest=8:289:37
GAP_LENGTH dir=rotor/read_PR set=all 1=116/485 2=117/1252 3=42/508 4=1/139 5+=1/64
GAPS dir=rotor/read_PR set=met n=1572 right=259 wrong=1313 unfinished=0 not_number=7 unread=0 numbers=1306
GAP_SIZE dir=rotor/read_PR set=met n=1306 x2=855 x10=1268 tenth=40 opposite_sign=0 smaller=714 larger=592 digits=875 foil_digits=515/1279
GAP_LEAD dir=rotor/read_PR set=met n=1301 lead=155 foil_lead=141/1274 lead_length=127 foil_lead_length=63/1274 one_digit=534 foil_one_digit=262/1274
GAP_RINGS dir=rotor/read_PR set=met n=1301 mod9=94 foil9=134/1274 mod10=487 foil10=352/1274 mod11=30 foil11=105/1274 mod7=85 foil7=183/1274 mod13=44 foil13=79/1274
GAP_FROM dir=rotor/read_PR set=met n=1306 heard_result=1305 operand=149 other_operation=66/1234
GAP_WRITES dir=rotor/read_PR set=met written=1565 distinct=56 top10=1090 commonest=8:242:35
GAP_LENGTH dir=rotor/read_PR set=met 1=112/383 2=107/878 3=39/264 4=1/44 5+=0/3
GAPS dir=rotor/read_PR set=never n=876 right=18 wrong=858 unfinished=0 not_number=2 unread=0 numbers=856
GAP_SIZE dir=rotor/read_PR set=never n=856 x2=326 x10=730 tenth=40 opposite_sign=0 smaller=519 larger=337 digits=487 foil_digits=311/849
GAP_LEAD dir=rotor/read_PR set=never n=816 lead=97 foil_lead=111/808 lead_length=69 foil_lead_length=41/808 one_digit=156 foil_one_digit=67/808
GAP_RINGS dir=rotor/read_PR set=never n=816 mod9=86 foil9=98/808 mod10=322 foil10=245/808 mod11=49 foil11=71/808 mod7=108 foil7=119/808 mod13=56 foil13=62/808
GAP_FROM dir=rotor/read_PR set=never n=856 heard_result=850 operand=48 other_operation=8/593
GAP_WRITES dir=rotor/read_PR set=never written=874 distinct=76 top10=570 commonest=56:88:0
GAP_LENGTH dir=rotor/read_PR set=never 1=4/102 2=10/374 3=3/244 4=0/95 5+=1/61
GAPS dir=turns/read_PRT set=all n=2448 right=240 wrong=2208 unfinished=7 not_number=1 unread=0 numbers=2200
GAP_SIZE dir=turns/read_PRT set=all n=2200 x2=1182 x10=2024 tenth=74 opposite_sign=0 smaller=1003 larger=1197 digits=1444 foil_digits=902/2170
GAP_LEAD dir=turns/read_PRT set=all n=2148 lead=299 foil_lead=300/2116 lead_length=225 foil_lead_length=126/2116 one_digit=703 foil_one_digit=351/2116
GAP_RINGS dir=turns/read_PRT set=all n=2148 mod9=208 foil9=231/2116 mod10=794 foil10=600/2116 mod11=114 foil11=161/2116 mod7=221 foil7=267/2116 mod13=103 foil13=149/2116
GAP_FROM dir=turns/read_PRT set=all n=2200 heard_result=2164 operand=179 other_operation=63/1869
GAP_WRITES dir=turns/read_PRT set=all written=2440 distinct=138 top10=1209 commonest=8:340:43
GAP_LENGTH dir=turns/read_PRT set=all 1=89/485 2=122/1252 3=26/508 4=3/139 5+=0/64
GAPS dir=turns/read_PRT set=met n=1572 right=216 wrong=1356 unfinished=3 not_number=0 unread=0 numbers=1353
GAP_SIZE dir=turns/read_PRT set=met n=1353 x2=847 x10=1302 tenth=37 opposite_sign=0 smaller=615 larger=738 digits=969 foil_digits=568/1327
GAP_LEAD dir=turns/read_PRT set=met n=1342 lead=168 foil_lead=166/1316 lead_length=143 foil_lead_length=75/1316 one_digit=560 foil_one_digit=263/1316
GAP_RINGS dir=turns/read_PRT set=met n=1342 mod9=101 foil9=137/1316 mod10=482 foil10=331/1316 mod11=49 foil11=97/1316 mod7=114 foil7=161/1316 mod13=44 foil13=81/1316
GAP_FROM dir=turns/read_PRT set=met n=1353 heard_result=1351 operand=142 other_operation=52/1281
GAP_WRITES dir=turns/read_PRT set=met written=1569 distinct=86 top10=889 commonest=8:264:40
GAP_LENGTH dir=turns/read_PRT set=met 1=82/383 2=110/878 3=23/264 4=1/44 5+=0/3
GAPS dir=turns/read_PRT set=never n=876 right=24 wrong=852 unfinished=4 not_number=1 unread=0 numbers=847
GAP_SIZE dir=turns/read_PRT set=never n=847 x2=335 x10=722 tenth=37 opposite_sign=0 smaller=388 larger=459 digits=475 foil_digits=286/842
GAP_LEAD dir=turns/read_PRT set=never n=806 lead=131 foil_lead=123/799 lead_length=82 foil_lead_length=40/799 one_digit=143 foil_one_digit=56/799
GAP_RINGS dir=turns/read_PRT set=never n=806 mod9=107 foil9=87/799 mod10=312 foil10=219/799 mod11=65 foil11=57/799 mod7=107 foil7=103/799 mod13=59 foil13=68/799
GAP_FROM dir=turns/read_PRT set=never n=847 heard_result=813 operand=37 other_operation=11/588
GAP_WRITES dir=turns/read_PRT set=never written=871 distinct=118 top10=436 commonest=8:76:3
GAP_LENGTH dir=turns/read_PRT set=never 1=7/102 2=12/374 3=3/244 4=2/95 5+=0/61
GAPS dir=turns/read_PRS set=all n=2448 right=288 wrong=2160 unfinished=2 not_number=3 unread=0 numbers=2155
GAP_SIZE dir=turns/read_PRS set=all n=2155 x2=1085 x10=1999 tenth=59 opposite_sign=0 smaller=1382 larger=773 digits=1255 foil_digits=831/2110
GAP_LEAD dir=turns/read_PRS set=all n=2110 lead=201 foil_lead=252/2065 lead_length=138 foil_lead_length=97/2065 one_digit=689 foil_one_digit=356/2065
GAP_RINGS dir=turns/read_PRS set=all n=2110 mod9=166 foil9=240/2065 mod10=792 foil10=555/2065 mod11=77 foil11=165/2065 mod7=196 foil7=276/2065 mod13=77 foil13=141/2065
GAP_FROM dir=turns/read_PRS set=all n=2155 heard_result=2143 operand=278 other_operation=84/1824
GAP_WRITES dir=turns/read_PRS set=all written=2443 distinct=109 top10=1403 commonest=8:397:40
GAP_LENGTH dir=turns/read_PRS set=all 1=107/485 2=127/1252 3=51/508 4=3/139 5+=0/64
GAPS dir=turns/read_PRS set=met n=1572 right=269 wrong=1303 unfinished=0 not_number=0 unread=0 numbers=1303
GAP_SIZE dir=turns/read_PRS set=met n=1303 x2=777 x10=1267 tenth=26 opposite_sign=0 smaller=821 larger=482 digits=817 foil_digits=496/1273
GAP_LEAD dir=turns/read_PRS set=met n=1297 lead=103 foil_lead=135/1267 lead_length=78 foil_lead_length=50/1267 one_digit=545 foil_one_digit=265/1267
GAP_RINGS dir=turns/read_PRS set=met n=1297 mod9=71 foil9=144/1267 mod10=470 foil10=309/1267 mod11=33 foil11=100/1267 mod7=86 foil7=169/1267 mod13=20 foil13=82/1267
GAP_FROM dir=turns/read_PRS set=met n=1303 heard_result=1302 operand=204 other_operation=77/1232
GAP_WRITES dir=turns/read_PRS set=met written=1572 distinct=58 top10=1090 commonest=8:313:38
GAP_LENGTH dir=turns/read_PRS set=met 1=99/383 2=123/878 3=44/264 4=3/44 5+=0/3
GAPS dir=turns/read_PRS set=never n=876 right=19 wrong=857 unfinished=2 not_number=3 unread=0 numbers=852
GAP_SIZE dir=turns/read_PRS set=never n=852 x2=308 x10=732 tenth=33 opposite_sign=0 smaller=561 larger=291 digits=438 foil_digits=280/846
GAP_LEAD dir=turns/read_PRS set=never n=813 lead=98 foil_lead=107/807 lead_length=60 foil_lead_length=34/807 one_digit=144 foil_one_digit=54/807
GAP_RINGS dir=turns/read_PRS set=never n=813 mod9=95 foil9=97/807 mod10=322 foil10=209/807 mod11=44 foil11=69/807 mod7=110 foil7=109/807 mod13=57 foil13=68/807
GAP_FROM dir=turns/read_PRS set=never n=852 heard_result=841 operand=74 other_operation=7/592
GAP_WRITES dir=turns/read_PRS set=never written=871 distinct=99 top10=455 commonest=8:84:2
GAP_LENGTH dir=turns/read_PRS set=never 1=8/102 2=4/374 3=7/244 4=0/95 5+=0/61
GAPS dir=strands/read_PRK set=all n=2448 right=230 wrong=2218 unfinished=7 not_number=0 unread=0 numbers=2211
GAP_SIZE dir=strands/read_PRK set=all n=2211 x2=1085 x10=2017 tenth=54 opposite_sign=0 smaller=1447 larger=764 digits=1279 foil_digits=865/2173
GAP_LEAD dir=strands/read_PRK set=all n=2161 lead=253 foil_lead=292/2123 lead_length=165 foil_lead_length=124/2123 one_digit=668 foil_one_digit=385/2123
GAP_RINGS dir=strands/read_PRK set=all n=2161 mod9=219 foil9=257/2123 mod10=799 foil10=584/2123 mod11=100 foil11=158/2123 mod7=186 foil7=294/2123 mod13=102 foil13=124/2123
GAP_FROM dir=strands/read_PRK set=all n=2211 heard_result=2207 operand=227 other_operation=74/1878
GAP_WRITES dir=strands/read_PRK set=all written=2441 distinct=96 top10=1565 commonest=8:334:33
GAP_LENGTH dir=strands/read_PRK set=all 1=107/485 2=94/1252 3=29/508 4=0/139 5+=0/64
GAPS dir=strands/read_PRK set=met n=1572 right=214 wrong=1358 unfinished=4 not_number=0 unread=0 numbers=1354
GAP_SIZE dir=strands/read_PRK set=met n=1354 x2=792 x10=1302 tenth=31 opposite_sign=0 smaller=858 larger=496 digits=880 foil_digits=534/1321
GAP_LEAD dir=strands/read_PRK set=met n=1345 lead=140 foil_lead=160/1312 lead_length=106 foil_lead_length=66/1312 one_digit=525 foil_one_digit=264/1312
GAP_RINGS dir=strands/read_PRK set=met n=1345 mod9=124 foil9=150/1312 mod10=484 foil10=327/1312 mod11=35 foil11=95/1312 mod7=101 foil7=192/1312 mod13=47 foil13=80/1312
GAP_FROM dir=strands/read_PRK set=met n=1354 heard_result=1354 operand=166 other_operation=69/1286
GAP_WRITES dir=strands/read_PRK set=met written=1568 distinct=66 top10=1115 commonest=8:227:31
GAP_LENGTH dir=strands/read_PRK set=met 1=100/383 2=89/878 3=25/264 4=0/44 5+=0/3
GAPS dir=strands/read_PRK set=never n=876 right=16 wrong=860 unfinished=3 not_number=0 unread=0 numbers=857
GAP_SIZE dir=strands/read_PRK set=never n=857 x2=293 x10=715 tenth=23 opposite_sign=0 smaller=589 larger=268 digits=399 foil_digits=285/852
GAP_LEAD dir=strands/read_PRK set=never n=816 lead=113 foil_lead=129/811 lead_length=59 foil_lead_length=47/811 one_digit=143 foil_one_digit=74/811
GAP_RINGS dir=strands/read_PRK set=never n=816 mod9=95 foil9=85/811 mod10=315 foil10=214/811 mod11=65 foil11=59/811 mod7=85 foil7=106/811 mod13=55 foil13=61/811
GAP_FROM dir=strands/read_PRK set=never n=857 heard_result=853 operand=61 other_operation=5/592
GAP_WRITES dir=strands/read_PRK set=never written=873 distinct=79 top10=537 commonest=150:120:4
GAP_LENGTH dir=strands/read_PRK set=never 1=7/102 2=5/374 3=4/244 4=0/95 5+=0/61
GAPS dir=strands/read_PRI set=all n=2448 right=214 wrong=2234 unfinished=12 not_number=2 unread=0 numbers=2220
GAP_SIZE dir=strands/read_PRI set=all n=2220 x2=1139 x10=2048 tenth=53 opposite_sign=0 smaller=1314 larger=906 digits=1332 foil_digits=846/2188
GAP_LEAD dir=strands/read_PRI set=all n=2174 lead=255 foil_lead=267/2141 lead_length=182 foil_lead_length=111/2141 one_digit=722 foil_one_digit=404/2141
GAP_RINGS dir=strands/read_PRI set=all n=2175 mod9=195 foil9=245/2143 mod10=802 foil10=615/2143 mod11=86 foil11=148/2143 mod7=200 foil7=274/2143 mod13=69 foil13=115/2143
GAP_FROM dir=strands/read_PRI set=all n=2220 heard_result=2186 operand=210 other_operation=88/1895
GAP_WRITES dir=strands/read_PRI set=all written=2434 distinct=95 top10=1632 commonest=8:488:45
GAP_LENGTH dir=strands/read_PRI set=all 1=104/485 2=84/1252 3=23/508 4=3/139 5+=0/64
GAPS dir=strands/read_PRI set=met n=1572 right=192 wrong=1380 unfinished=1 not_number=1 unread=0 numbers=1378
GAP_SIZE dir=strands/read_PRI set=met n=1378 x2=835 x10=1342 tenth=24 opposite_sign=0 smaller=861 larger=517 digits=903 foil_digits=546/1352
GAP_LEAD dir=strands/read_PRI set=met n=1371 lead=129 foil_lead=147/1345 lead_length=110 foil_lead_length=62/1345 one_digit=587 foil_one_digit=314/1345
GAP_RINGS dir=strands/read_PRI set=met n=1372 mod9=106 foil9=149/1346 mod10=491 foil10=361/1346 mod11=34 foil11=79/1346 mod7=99 foil7=160/1346 mod13=27 foil13=83/1346
GAP_FROM dir=strands/read_PRI set=met n=1378 heard_result=1372 operand=160 other_operation=78/1307
GAP_WRITES dir=strands/read_PRI set=met written=1570 distinct=61 top10=1176 commonest=8:380:41
GAP_LENGTH dir=strands/read_PRI set=met 1=94/383 2=80/878 3=16/264 4=2/44 5+=0/3
GAPS dir=strands/read_PRI set=never n=876 right=22 wrong=854 unfinished=11 not_number=1 unread=0 numbers=842
GAP_SIZE dir=strands/read_PRI set=never n=842 x2=304 x10=706 tenth=29 opposite_sign=0 smaller=453 larger=389 digits=429 foil_digits=251/839
GAP_LEAD dir=strands/read_PRI set=never n=803 lead=126 foil_lead=117/799 lead_length=72 foil_lead_length=34/799 one_digit=135 foil_one_digit=64/799
GAP_RINGS dir=strands/read_PRI set=never n=803 mod9=89 foil9=93/800 mod10=311 foil10=241/800 mod11=52 foil11=57/800 mod7=101 foil7=119/800 mod13=42 foil13=59/800
GAP_FROM dir=strands/read_PRI set=never n=842 heard_result=814 operand=50 other_operation=10/588
GAP_WRITES dir=strands/read_PRI set=never written=864 distinct=86 top10=524 commonest=8:108:4
GAP_LENGTH dir=strands/read_PRI set=never 1=10/102 2=4/374 3=7/244 4=1/95 5+=0/61
GAPS dir=opened/read_PRA set=all n=2448 right=286 wrong=2162 unfinished=21 not_number=6 unread=0 numbers=2135
GAP_SIZE dir=opened/read_PRA set=all n=2135 x2=1104 x10=1952 tenth=70 opposite_sign=0 smaller=1196 larger=939 digits=1254 foil_digits=784/2101
GAP_LEAD dir=opened/read_PRA set=all n=2085 lead=257 foil_lead=293/2045 lead_length=185 foil_lead_length=108/2045 one_digit=669 foil_one_digit=345/2045
GAP_RINGS dir=opened/read_PRA set=all n=2085 mod9=168 foil9=198/2045 mod10=807 foil10=588/2045 mod11=79 foil11=158/2045 mod7=170 foil7=267/2045 mod13=76 foil13=134/2045
GAP_FROM dir=opened/read_PRA set=all n=2135 heard_result=2081 operand=189 other_operation=83/1807
GAP_WRITES dir=opened/read_PRA set=all written=2421 distinct=132 top10=1553 commonest=8:315:39
GAP_LENGTH dir=opened/read_PRA set=all 1=123/485 2=125/1252 3=35/508 4=3/139 5+=0/64
GAPS dir=opened/read_PRA set=met n=1572 right=268 wrong=1304 unfinished=4 not_number=2 unread=0 numbers=1298
GAP_SIZE dir=opened/read_PRA set=met n=1298 x2=804 x10=1258 tenth=31 opposite_sign=0 smaller=750 larger=548 digits=843 foil_digits=489/1268
GAP_LEAD dir=opened/read_PRA set=met n=1291 lead=127 foil_lead=158/1261 lead_length=108 foil_lead_length=65/1261 one_digit=529 foil_one_digit=267/1261
GAP_RINGS dir=opened/read_PRA set=met n=1291 mod9=81 foil9=118/1261 mod10=494 foil10=335/1261 mod11=26 foil11=91/1261 mod7=84 foil7=174/1261 mod13=23 foil13=75/1261
GAP_FROM dir=opened/read_PRA set=met n=1298 heard_result=1288 operand=134 other_operation=73/1228
GAP_WRITES dir=opened/read_PRA set=met written=1566 distinct=70 top10=1162 commonest=8:239:35
GAP_LENGTH dir=opened/read_PRA set=met 1=115/383 2=121/878 3=29/264 4=3/44 5+=0/3
GAPS dir=opened/read_PRA set=never n=876 right=18 wrong=858 unfinished=17 not_number=4 unread=0 numbers=837
GAP_SIZE dir=opened/read_PRA set=never n=837 x2=300 x10=694 tenth=39 opposite_sign=0 smaller=446 larger=391 digits=411 foil_digits=259/833
GAP_LEAD dir=opened/read_PRA set=never n=794 lead=130 foil_lead=141/785 lead_length=77 foil_lead_length=38/785 one_digit=140 foil_one_digit=55/785
GAP_RINGS dir=opened/read_PRA set=never n=794 mod9=87 foil9=74/785 mod10=313 foil10=223/785 mod11=53 foil11=59/785 mod7=86 foil7=112/785 mod13=53 foil13=63/785
GAP_FROM dir=opened/read_PRA set=never n=837 heard_result=793 operand=55 other_operation=10/579
GAP_WRITES dir=opened/read_PRA set=never written=855 distinct=117 top10=457 commonest=150:91:2
GAP_LENGTH dir=opened/read_PRA set=never 1=8/102 2=4/374 3=6/244 4=0/95 5+=0/61
GAPS dir=opened/read_PRJ set=all n=2448 right=233 wrong=2215 unfinished=2 not_number=3 unread=0 numbers=2210
GAP_SIZE dir=opened/read_PRJ set=all n=2210 x2=1182 x10=2010 tenth=76 opposite_sign=0 smaller=1241 larger=969 digits=1394 foil_digits=921/2177
GAP_LEAD dir=opened/read_PRJ set=all n=2138 lead=306 foil_lead=292/2101 lead_length=235 foil_lead_length=126/2101 one_digit=748 foil_one_digit=403/2101
GAP_RINGS dir=opened/read_PRJ set=all n=2138 mod9=202 foil9=237/2101 mod10=768 foil10=568/2101 mod11=100 foil11=157/2101 mod7=209 foil7=259/2101 mod13=80 foil13=131/2101
GAP_FROM dir=opened/read_PRJ set=all n=2210 heard_result=2201 operand=165 other_operation=71/1870
GAP_WRITES dir=opened/read_PRJ set=all written=2443 distinct=124 top10=1356 commonest=8:389:40
GAP_LENGTH dir=opened/read_PRJ set=all 1=69/485 2=115/1252 3=41/508 4=8/139 5+=0/64
GAPS dir=opened/read_PRJ set=met n=1572 right=214 wrong=1358 unfinished=0 not_number=2 unread=0 numbers=1356
GAP_SIZE dir=opened/read_PRJ set=met n=1356 x2=850 x10=1299 tenth=37 opposite_sign=0 smaller=746 larger=610 digits=934 foil_digits=580/1332
GAP_LEAD dir=opened/read_PRJ set=met n=1338 lead=169 foil_lead=153/1314 lead_length=145 foil_lead_length=65/1314 one_digit=603 foil_one_digit=303/1314
GAP_RINGS dir=opened/read_PRJ set=met n=1338 mod9=107 foil9=125/1314 mod10=455 foil10=317/1314 mod11=41 foil11=95/1314 mod7=106 foil7=151/1314 mod13=33 foil13=83/1314
GAP_FROM dir=opened/read_PRJ set=met n=1356 heard_result=1355 operand=116 other_operation=64/1280
GAP_WRITES dir=opened/read_PRJ set=met written=1570 distinct=77 top10=999 commonest=8:306:38
GAP_LENGTH dir=opened/read_PRJ set=met 1=65/383 2=109/878 3=35/264 4=5/44 5+=0/3
GAPS dir=opened/read_PRJ set=never n=876 right=19 wrong=857 unfinished=2 not_number=1 unread=0 numbers=854
GAP_SIZE dir=opened/read_PRJ set=never n=854 x2=332 x10=711 tenth=39 opposite_sign=0 smaller=495 larger=359 digits=460 foil_digits=296/846
GAP_LEAD dir=opened/read_PRJ set=never n=800 lead=137 foil_lead=133/788 lead_length=90 foil_lead_length=47/788 one_digit=145 foil_one_digit=74/788
GAP_RINGS dir=opened/read_PRJ set=never n=800 mod9=95 foil9=95/788 mod10=313 foil10=224/788 mod11=59 foil11=69/788 mod7=103 foil7=109/788 mod13=47 foil13=60/788
GAP_FROM dir=opened/read_PRJ set=never n=854 heard_result=846 operand=49 other_operation=7/590
GAP_WRITES dir=opened/read_PRJ set=never written=873 distinct=110 top10=433 commonest=8:83:2
GAP_LENGTH dir=opened/read_PRJ set=never 1=4/102 2=6/374 3=6/244 4=3/95 5+=0/61
GAPS dir=opened/read_PRE set=all n=2448 right=245 wrong=2203 unfinished=3 not_number=1 unread=0 numbers=2199
GAP_SIZE dir=opened/read_PRE set=all n=2199 x2=1089 x10=2030 tenth=49 opposite_sign=0 smaller=1489 larger=710 digits=1290 foil_digits=829/2160
GAP_LEAD dir=opened/read_PRE set=all n=2151 lead=255 foil_lead=276/2112 lead_length=159 foil_lead_length=101/2112 one_digit=703 foil_one_digit=374/2112
GAP_RINGS dir=opened/read_PRE set=all n=2151 mod9=197 foil9=230/2112 mod10=812 foil10=604/2112 mod11=89 foil11=147/2112 mod7=190 foil7=291/2112 mod13=83 foil13=120/2112
GAP_FROM dir=opened/read_PRE set=all n=2199 heard_result=2179 operand=209 other_operation=98/1872
GAP_WRITES dir=opened/read_PRE set=all written=2444 distinct=137 top10=1543 commonest=8:502:42
GAP_LENGTH dir=opened/read_PRE set=all 1=110/485 2=105/1252 3=26/508 4=2/139 5+=2/64
GAPS dir=opened/read_PRE set=met n=1572 right=219 wrong=1353 unfinished=0 not_number=1 unread=0 numbers=1352
GAP_SIZE dir=opened/read_PRE set=met n=1352 x2=783 x10=1316 tenth=19 opposite_sign=0 smaller=937 larger=415 digits=851 foil_digits=524/1324
GAP_LEAD dir=opened/read_PRE set=met n=1344 lead=121 foil_lead=143/1316 lead_length=87 foil_lead_length=54/1316 one_digit=564 foil_one_digit=288/1316
GAP_RINGS dir=opened/read_PRE set=met n=1344 mod9=100 foil9=128/1316 mod10=493 foil10=325/1316 mod11=39 foil11=92/1316 mod7=90 foil7=174/1316 mod13=32 foil13=57/1316
GAP_FROM dir=opened/read_PRE set=met n=1352 heard_result=1351 operand=155 other_operation=88/1285
GAP_WRITES dir=opened/read_PRE set=met written=1571 distinct=77 top10=1133 commonest=8:386:36
GAP_LENGTH dir=opened/read_PRE set=met 1=99/383 2=94/878 3=24/264 4=2/44 5+=0/3
GAPS dir=opened/read_PRE set=never n=876 right=26 wrong=850 unfinished=3 not_number=0 unread=0 numbers=847
GAP_SIZE dir=opened/read_PRE set=never n=847 x2=306 x10=714 tenth=30 opposite_sign=0 smaller=552 larger=295 digits=439 foil_digits=280/840
GAP_LEAD dir=opened/read_PRE set=never n=807 lead=134 foil_lead=122/799 lead_length=72 foil_lead_length=35/799 one_digit=139 foil_one_digit=60/799
GAP_RINGS dir=opened/read_PRE set=never n=807 mod9=97 foil9=96/799 mod10=319 foil10=227/799 mod11=50 foil11=60/799 mod7=100 foil7=126/799 mod13=51 foil13=55/799
GAP_FROM dir=opened/read_PRE set=never n=847 heard_result=828 operand=54 other_operation=10/587
GAP_WRITES dir=opened/read_PRE set=never written=873 distinct=124 top10=490 commonest=150:141:2
GAP_LENGTH dir=opened/read_PRE set=never 1=11/102 2=11/374 3=2/244 4=0/95 5+=2/61
RUN_RECEIPT exit=0 wall_s=21.8 peak_rss_kib=61384 user_s=21.7

```
