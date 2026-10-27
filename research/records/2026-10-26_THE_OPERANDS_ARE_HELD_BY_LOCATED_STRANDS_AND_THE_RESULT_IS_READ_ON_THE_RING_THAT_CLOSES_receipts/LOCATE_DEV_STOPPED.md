# The locator's first development read, stopped early

GPT-6's bookkeeping question (the record's §3 cites this read). The same local copy of the GSM8K
training problems as [LOCATE_DEV.md](LOCATE_DEV.md) (3,925,837 bytes; not the PC's training
partition). The binary was built at 00:31 UTC on October 27 from the worktree before the refusal of
groups their own rows do not carry was written; that source state was never committed (the locator
first committed is the later one). Built without link-time optimization; four threads.

- Command: `RAYON_NUM_THREADS=4 timeout 240 target/release/examples/solenoidal_alpha complete-language
  locate-strands dev_train.txt SHA256 4`, its output to a log.
- Declared before launch: projection unmeasured, planned at 1 to 3 minutes plus the stream's keyed
  bytes; deadline 240 s (the first line of the log).
- Launched 00:34:28 UTC; stopped by hand at 00:36:13 UTC, about 105 s into its 240 s deadline, so
  it was stopped early on evidence, not past its deadline. Its exit status was not recorded.
- The evidence: 24 groups were admitted as closing, 18 of them of one to three calculations, and
  they pulled 15 bytes into the keyed set. The stream's first round had spent 98.7 s on 7 of the
  15 keyed bytes, about 14 s a byte: about 210 s a round, about 420 s for two, past the deadline.
- The next read changed the law: groups whose own rows do not carry their closure are refused
  (`STRANDS_UNCARRIED`). It declared a new projection from the measured rate (196 s) with a
  deadline of 300 s, and ran in 65.073 s ([LOCATE_DEV.md](LOCATE_DEV.md)). No launch of this law
  was repeated with a changed limit.

The log, whole:
```text
PROJECTION unmeasured, planned 1 to 3 minutes plus the stream's keyed spaces; DEADLINE 240 s; RAYON_NUM_THREADS=4
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
STRANDS_CLOSING groups=24 stretches=8237
STRANDS_GROUP context=<+=> hand=1,1 stretches=4266 rows=4150 beyond=116 digits=9448
STRANDS_GROUP context=<-=> hand=1,-1 stretches=3764 rows=3694 beyond=70 digits=7537
STRANDS_GROUP context=<-=. hand=1,-1 stretches=61 rows=61 beyond=0 digits=139
STRANDS_GROUP context=<+=. hand=1,1 stretches=59 rows=59 beyond=0 digits=137
STRANDS_GROUP context=\x20+=\x20 hand=1,1 stretches=39 rows=39 beyond=0 digits=81
STRANDS_GROUP context=\x20-=\x20 hand=1,-1 stretches=28 rows=28 beyond=0 digits=40
STRANDS_GROUP context==-=\x0a hand=1,-1 stretches=3 rows=3 beyond=0 digits=6
STRANDS_GROUP context=\x20++. hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=\x20+=\x0a hand=1,1 stretches=1 rows=1 beyond=0 digits=2
STRANDS_GROUP context=\x20-/\x20 hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=\x20-=\x0a hand=1,-1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=\x20-=. hand=1,-1 stretches=1 rows=1 beyond=0 digits=2
STRANDS_GROUP context=\x20.*. hand=1,-1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=\x20::, hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=$\x0a*= hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=(+=) hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=+++- hand=1,-1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=++/+ hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=++/= hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=.=\x0a\x20 hand=1,1 stretches=1 rows=1 beyond=0 digits=2
STRANDS_GROUP context=/++/ hand=1,-1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=<**+ hand=1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context=</++ hand=-1,1 stretches=1 rows=1 beyond=0 digits=1
STRANDS_GROUP context==+=\x0a hand=1,1 stretches=1 rows=1 beyond=0 digits=2
STRANDS_LOCATED stage=1 laws=turned,stepped,held comparison=0,1:1,1 keys=+=0,2,-1:flipped -=0,2,-1:kept ==1,3,3:plus changes=7 <+=>:closed=4150/4150,digits=9378,symbolic=true <-=>:closed=3694/3694,digits=7461,symbolic=true elapsed_ms=1481
STRANDS_LOCATED stage=2 context=\x20-/\x20 keys=/=-1,3,3:kept closed=1/1 digits=1 elapsed_ms=1482
STRANDS_LOCATED stage=2 context=\x20.*. keys=*=1,2,3:kept .=1,1,3:kept closed=1/1 digits=1 elapsed_ms=1486
STRANDS_LOCATED stage=2 context=\x20::, keys=:=1,1,3:flipped closed=1/1 digits=1 elapsed_ms=1486
STRANDS_LOCATED stage=2 context=$\x0a*= keys=\x0a=-1,2,3:flipped closed=0/1 digits=1 elapsed_ms=1486
STRANDS_STREAM_START events=1237515 keyed=\x0a\x20$()*+,-./:<=> closed=80 digits=3687 elapsed_ms=1571
STRANDS_ASCENT round=1 byte=\x20 key=0,1,-2:plus closed=6665 digits=14877 elapsed_ms=16149
STRANDS_ASCENT round=1 byte=$ key=0,0,3:kept closed=6930 digits=15415 elapsed_ms=30431
STRANDS_ASCENT round=1 byte=( key=0,2,3:kept closed=6931 digits=15416 elapsed_ms=45290
STRANDS_ASCENT round=1 byte=) key=1,2,3:kept closed=6931 digits=15416 elapsed_ms=59244
STRANDS_ASCENT round=1 byte=, key=0,2,3:kept closed=6931 digits=15417 elapsed_ms=73047
STRANDS_ASCENT round=1 byte=< key=0,-3,3:kept closed=8040 digits=17248 elapsed_ms=86488
STRANDS_ASCENT round=1 byte=> key=1,2,3:kept closed=8040 digits=17248 elapsed_ms=100277
```
