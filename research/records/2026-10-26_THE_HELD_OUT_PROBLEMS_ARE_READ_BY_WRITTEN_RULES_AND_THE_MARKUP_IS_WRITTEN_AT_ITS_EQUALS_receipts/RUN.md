# The written-rule reads: the container's development reads and baselines

In the container (4 threads, `RAYON_NUM_THREADS=4`), at the tree that adds this record. None of
these reads is about the tower's state `lapD8/STATE`: the development state is `covsmoke/two.state`
(`9,558,150` bytes, the two-clock smoke state trained on a 162,937-byte slice), read only to check
the reader and measure its cost. The releases (`FREE.tsv`, `MARKS.tsv`) hold held-out problem text
and stay outside the repository; their SHA-256 are below.

Inputs: the held-out text `e5bffe0e…3153` (747 problems), the training text `050b94f3…3b95`
(3,528,168 bytes), the committed units `d0973c39…782a`, a key file of 8,388,608 bytes from
`/dev/urandom`.

```text
B complete-language read-unit-tower-written UNITS SHA two.state SHA HELD SHA keys.bin SHA 400 1 64 8 OUT
python3 -I tools/gsm8k/ngram_release.py train.txt dev.txt ORDER 400 1 64 24 OUT
python3 -I tools/gsm8k/written_rules.py dev.txt train.txt reference devall2 ngram6 ngram8
```

## The reader on the development state

| read | problems | guard | measured wall | units moved | ms a unit a thread |
|---|---|---|---|---|---|
| the first 16 | 16 | 900 s | 2.09 s | 14,398 | 0.581 |
| problems 100 to 227 | 128 | 300 s | 12.87 s | 100,263 | 0.513 |
| all | 747 | 150 s | 73.35 s | 582,085 | 0.504 |
| all, counted | 747 | 90 s | 75.38 s | 468,588 prompt + 113,497 released | 0.518 |
| the first 16, memory | 16 | 10 s | 2.15 s | 11,910 prompt + 2,488 released | peak 30,548 KiB |

The first read was unmeasured; its 900 s guard was above the three minutes the standard plans for
an unmeasured run, and the later guards came from the 0.581 ms rate (the whole read projected at
about 78 s). The two whole reads wrote the same files. Every 64-problem window of the whole reads
took 5.3 to 7.7 s; the first took 7,658 and 7,435 ms.

```text
TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299767 prompt_units=468588 released_units=113497 most_units_a_problem=4720 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=75375
TOWER_WRITTEN_FILES free_sha256=226057cdfafac6791bd13e13416c3029b9d89998f2cb17ef8f50b5468ffee79b marks_sha256=4995038c53c33558f9027daadf9a2d10dd066146b4b19b67ef968acbaed2dca1
```

## The rules on the references, the development read and the n-grams

```text
WRITTEN dir=reference problems=747 a_on_problem=743 b_free_calculations=2448 b_free_right=2448 c_first_calculations=740 c_from_question=566
WRITTEN dir=devall2 problems=747 a_on_problem=50 b_free_calculations=1401 b_free_right=80 c_first_calculations=668 c_from_question=42 b_equals=218/2448 met=205/1572 never_met=13/876 binary +=28/470 -=27/388 *=115/897 /=36/343
WRITTEN dir=ngram6 problems=747 a_on_problem=64 b_free_calculations=986 b_free_right=570 c_first_calculations=533 c_from_question=20 b_equals=1348/2448 met=1318/1572 never_met=30/876 binary +=250/470 -=198/388 *=631/897 /=217/343
WRITTEN dir=ngram8 problems=747 a_on_problem=77 b_free_calculations=1155 b_free_right=981 c_first_calculations=585 c_from_question=20 b_equals=1559/2448 met=1525/1572 never_met=34/876 binary +=294/470 -=230/388 *=710/897 /=252/343
```

The rules read the four in 7.8 s. The n-gram releases were written under 240 s and 300 s guards
and were not timed. Their files:

```text
21e7f5a08870c17d185f5f74cd8e64dd4cf9deb193fb9f907446319b0392fb65  ngram6/FREE.tsv
b2ff60cf28d8a0b1c6a5f0b3f1da1920fbeb48f65feb7af2e61e71df58b623f4  ngram6/MARKS.tsv
8dffab6a081085126e1ceab72943713d421dca9142a19e61e44a1319fdc6d04a  ngram8/FREE.tsv
88a4874a866a965bf1f5eec2c714582a2caa3f44b5292cc7edc475cf0173edab  ngram8/MARKS.tsv
```
