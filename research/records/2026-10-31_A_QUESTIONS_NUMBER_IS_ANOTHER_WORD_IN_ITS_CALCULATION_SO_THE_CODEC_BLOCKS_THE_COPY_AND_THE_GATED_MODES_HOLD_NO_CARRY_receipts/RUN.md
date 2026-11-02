# Receipts: the review's counts

Exterior counts on GSM8K's public training split (`train.jsonl`, SHA-256
`17f347dc51477c50d4efb83959dbb7c56297aba886e5544ee2aaed3024813465`, 7,473 problems), run on the
cloud host on October 31 at 23:55 UTC. Nothing here entered a machine. Each count ran in under 30 s.

The committed units (`d0973c39…782a`, 1,062 merges), the first 1,500 problems:

```text
WELD problems=1500 with_calculation=1479 first_calc_all_from_question_numerals=790 operands_the_question_writes=2287 same_word=552 question_word_digits_only=974
```

The same read under a founding of no merges (`founded-units-v1 0`, the passage's bytes):

```text
WELD problems=1500 with_calculation=1479 first_calc_all_from_question_numerals=790 operands_the_question_writes=2287 same_word=2287 question_word_digits_only=2287
```

The training split's calculations:

```text
CALCULATIONS problems=7473 calculations=23716 distinct=10772 written_once=8084 binary=18664 sums=4325 differences=3825 products=7212 quotients=3302 result_digits={0: 80, 1: 4729, 2: 11665, 3: 5139, 4: 1476, 5: 441, 6: 150, 7: 27, 8: 4, 9: 4, 10: 1}
```

`weld.py UNITS TRAIN_JSONL 1500` and `calculations.py TRAIN_JSONL` reproduce them.
