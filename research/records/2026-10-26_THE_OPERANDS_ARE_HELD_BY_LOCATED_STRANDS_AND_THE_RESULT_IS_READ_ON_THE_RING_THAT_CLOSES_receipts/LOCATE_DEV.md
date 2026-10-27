# The locator's development read on a local training text

The locator's own lines, whole, from `locate-strands` on a local copy of the GSM8K training
problems (3,925,837 bytes; not the PC's training partition), built without link-time optimization
on four threads. The text and its digest stay outside the repository; the lines hold counts, byte
contexts and keys only.

```text
PROJECTION menu and stages 1-2 about 2 s (measured), stream about 14 s a keyed byte a round on 4 threads (measured) times about 7 bytes times 2 rounds = 196 s, composed keys faster; DEADLINE 300 s; RAYON_NUM_THREADS=4
STRANDS_MENU stretches=30018 groups=457 period=4
STRANDS_HAND context=<*=> stretches=7041 hand=1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=7041 hand=1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=7041 hand=-1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<*=> stretches=7041 hand=-1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=4266 hand=1,1 step=1 rank=40 carried=3333 torsion=3:1,11:1,101:1
STRANDS_HAND context=<+=> stretches=4266 hand=1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=4266 hand=-1,1 step=0 rank=40 carried=1 torsion=none
STRANDS_HAND context=<+=> stretches=4266 hand=-1,-1 step=0 rank=40 carried=1 torsion=none
STRANDS_FIRST context=<+=> stretches=4266 hand=1,1 bytes=0123456789
STRANDS_RING length=1 step=0 modulus=9 multiplier=1 primes=3:9 turns=0,1,2,3,4,5,6,7,8,0
STRANDS_RING length=2 step=1 modulus=99 multiplier=10 primes=3:9,11:11 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_RING length=3 step=1 modulus=999 multiplier=10 primes=3:27,37:37 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_RING length=4 step=1 modulus=9999 multiplier=10 primes=3:9,11:11,101:101 turns=0,1,2,3,4,5,6,7,8,9
STRANDS_UNCARRIED context==-=\x0a stretches=3 hand=1,-1 rank=12 touched=32
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
STRANDS_CLOSING groups=6 stretches=8217 uncarried=18
STRANDS_GROUP context=<+=> hand=1,1 stretches=4266 rows=4150 beyond=116 digits=9448
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3764 rows=3694 beyond=70 digits=7537
STRANDS_GROUP context=<-=. hand=1,-1 stretches=61 rows=61 beyond=0 digits=139
STRANDS_GROUP context=<+=. hand=1,1 stretches=59 rows=59 beyond=0 digits=137
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=39 rows=39 beyond=0 digits=81
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=28 rows=28 beyond=0 digits=40
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=4150/4150,digits=9378,symbolic=true <-=>:closed=3694/3694,digits=7461,symbolic=true elapsed_ms=1582
STRANDS_STREAM_START events=368700 keyed=\x20+-.<=> closed=82 digits=3303 elapsed_ms=1645
STRANDS_ASCENT round=1 byte=\x20 key=0,2,3:plus closed=6658 digits=14888 elapsed_ms=6489
STRANDS_ASCENT round=1 byte=. key=1,2,3:kept closed=6658 digits=14888 elapsed_ms=10960
STRANDS_ASCENT round=1 byte=< key=0,2,3:kept closed=8031 digits=17234 elapsed_ms=15586
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=8031 digits=17234 elapsed_ms=20075
STRANDS_ASCENT round=1 byte=+ key=0,2,-1:flipped closed=8031 digits=17234 elapsed_ms=24461
STRANDS_ASCENT round=1 byte=- key=0,2,-1:kept closed=8031 digits=17234 elapsed_ms=28863
STRANDS_ASCENT round=1 byte== key=1,3,3:plus closed=8031 digits=17234 elapsed_ms=33187
STRANDS_ASCENT round=2 byte=\x20 key=0,2,3:plus closed=8031 digits=17234 elapsed_ms=38042
STRANDS_ASCENT round=2 byte=. key=1,2,3:kept closed=8031 digits=17234 elapsed_ms=42497
STRANDS_ASCENT round=2 byte=< key=0,2,3:kept closed=8031 digits=17234 elapsed_ms=46973
STRANDS_ASCENT round=2 byte=> key=1,2,3:kept closed=8031 digits=17234 elapsed_ms=51636
STRANDS_ASCENT round=2 byte=+ key=0,2,-1:flipped closed=8031 digits=17234 elapsed_ms=55941
STRANDS_ASCENT round=2 byte=- key=0,2,-1:kept closed=8031 digits=17234 elapsed_ms=60393
STRANDS_ASCENT round=2 byte== key=1,3,3:plus closed=8031 digits=17234 elapsed_ms=65025
STRANDS_STREAM context=<+=> rows=4150 closed=4150 digits=9378/9448
STRANDS_STREAM context=<-=> rows=3694 closed=3694 digits=7461/7537
STRANDS_STREAM context=<-=. rows=61 closed=61 digits=138/139
STRANDS_STREAM context=<+=. rows=59 closed=59 digits=136/137
STRANDS_STREAM context=\x20+=\x20 rows=39 closed=39 digits=81/81
STRANDS_STREAM context=\x20-=\x20 rows=28 closed=28 digits=40/40
STRANDS_CLOSED groups=2 closed=7844 rows=7844 elapsed_ms=65038
RUN exit=0 wall_ms=65073
```
