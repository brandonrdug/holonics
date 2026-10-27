# The two checks of §2

Both run in the container (`python3 -I`), exact integer arithmetic, no input.

`strands.py`: the strands with the keys of §2 over every `x, y < 1000` and both hands; for each
positive result below `10^4`, every digit is the tenth of ring `len(z)`'s conjugate comparison
face and the ring closes at the end. `None` counts the calculations with a result that is not
positive or has more than four digits; `nines` the results of all nines, their ring's zero.

```text
{None: 500501, 'ok': 1496496, 'nines': 3003}
```

`check.py`: for every result `1 ≤ S < 10^6` but the all-nines numerals, the size (the largest
ring of width 1 to 6 whose face `S/(10^w − 1)` lies outside the first tenth) is `len(S)`, and
`S` is written digit by digit from ring `len(S)`'s conjugate face from `H = −S`, closing at its
end.

```text
checked 999993 bad_size 0 bad_write 0 all_nines_skipped 5
```

Wall time: `check.py` 19.8 s, `strands.py` 3.1 s.
