# Receipts: the store line's level by lap, its travel, and the cooling read's guesses

For [the companion record of the audit](../../2026-11-18_COOLING_WAS_MEASURED_ON_NOVEMBER_4_AND_RETIRED_THE_LINES_LEVEL_IS_TRADED_BY_ITS_MIX_AN_OPEN_PLACE_IS_NEVER_A_SOURCE_AND_A_CHANGE_TO_A_LINE_RUNS_BESIDE_A_CONTROL.md).
Host readings only, one Python process each, made from the store line's own run directory (its read files `out_P{n}/cavity.tsv` and its
saved states `lap{n}/STATE.*`, `MEAN.*`). No card was used, no state was changed and no run was touched. The private files stay under
`.local/`; the numbers here are sums over the held passage and over the states' material.

## `held_levels.py`, `levels.tsv`

`python3 -I held_levels.py LINE_DIR` prints `levels.tsv`: for every lap 1 to 95 the held code in nats a place, one place open (the five
text slices, 100,508 places; the arithmetic and word-problem slices from lap 71) and every place of a run open at once (the text
slices' 3,717 whole-mask places).

Fits over the text slices' one-place code (least squares over the laps named; the scatter is the residuals' deviation):

| laps | first to last | fall a lap, thousandths of a nat | scatter between laps, thousandths |
|---|---|---|---|
| 1 to 10 | 0.9671 to 0.8754 | 9.68 | 4.88 |
| 10 to 20 | 0.8754 to 0.8310 | 4.20 | 4.10 |
| 20 to 30 | 0.8310 to 0.8109 | 2.00 | 2.11 |
| 30 to 40 | 0.8109 to 0.7954 | 1.44 | 1.45 |
| 40 to 50 | 0.7954 to 0.7845 | 0.93 | 1.33 |
| 50 to 60 | 0.7845 to 0.7777 | 0.55 | 1.42 |
| 60 to 70 | 0.7777 to 0.7734 | 0.47 | 1.19 |
| 71 to 94 | 0.8249 to 0.8256 | 0.26 | 3.44 |
| 78 to 94 | 0.8388 to 0.8256 | 0.71 | 1.76 |

Lap 95 (arithmetic taken out of the store, 6,000 sections) against lap 94: text 0.8256 to 0.8157, word problems 0.7652 to 0.7385, held
arithmetic 1.5737 to 1.7571.

## The states' travel (read 03:00 UTC, November 18)

Material lines 3, 6 and 7 of a saved state (the field's, the level's, the glue's), in grains of `2^(−24)`. `rms` is over a block's
entries; a move is the difference of two saved states; the cosine is between one lap's move and the next lap's.

| block | laps | rms of the entries | rms move, lap to lap (end states) | move over rms | cosine | rms move of the saved means | their cosine |
|---|---|---|---|---|---|---|---|
| field | 20 to 22 | 3,858,863 | 89,085 then 84,921 | 0.022 | +0.079 | 77,769 | +0.201 |
| level | 20 to 22 | 2,912,423 | 125,307 then 123,686 | 0.042 | −0.046 | 113,495 | +0.040 |
| glue | 20 to 22 | 1,342,114 | 150,472 then 148,200 | 0.110 | −0.181 | 134,001 | −0.101 |
| field | 40 to 42 | 4,047,761 | 80,468 then 80,621 | 0.020 | −0.067 | 71,055 | +0.054 |
| level | 40 to 42 | 3,242,851 | 120,987 then 120,777 | 0.037 | −0.098 | 109,623 | −0.022 |
| glue | 40 to 42 | 1,586,950 | 148,675 then 149,256 | 0.094 | −0.214 | 134,959 | −0.154 |
| field | 60 to 62 | 4,242,355 | 77,783 then 81,888 | 0.019 | −0.102 | 72,146 | −0.025 |
| level | 60 to 62 | 3,529,416 | 117,322 then 126,388 | 0.036 | −0.105 | 111,402 | −0.034 |
| glue | 60 to 62 | 1,799,244 | 149,194 then 152,900 | 0.085 | −0.208 | 136,874 | −0.147 |
| field | 68 to 70 | 4,318,745 | 78,202 then 77,015 | 0.018 | −0.149 | 68,366 | −0.028 |
| level | 68 to 70 | 3,633,312 | 119,047 then 119,454 | 0.033 | −0.124 | 107,688 | −0.043 |
| glue | 68 to 70 | 1,873,668 | 151,341 then 150,188 | 0.080 | −0.220 | 136,245 | −0.154 |
| field | 80 to 82 | 4,378,181 | 92,905 then 90,759 | 0.021 | +0.238 | 85,217 | +0.359 |
| level | 80 to 82 | 3,795,449 | 136,089 then 130,525 | 0.034 | +0.189 | 123,354 | +0.286 |
| glue | 80 to 82 | 1,972,557 | 150,324 then 148,701 | 0.075 | −0.064 | 136,855 | +0.019 |
| field | 92 to 94 | 4,510,627 | 81,190 then 78,346 | 0.017 | +0.034 | 72,212 | +0.107 |
| level | 92 to 94 | 3,931,574 | 121,575 then 120,191 | 0.031 | −0.004 | 111,908 | +0.044 |
| glue | 92 to 94 | 2,071,310 | 147,157 then 145,523 | 0.070 | −0.175 | 132,123 | −0.106 |

Inside a lap (successive saves, 1,000 sections apart, over two laps): the field's moves are 53,000 to 58,000 grains rms with cosines
−0.30, −0.21, −0.28, −0.19, −0.27 around lap 69 and −0.18, −0.24, −0.14, −0.27, −0.16 around lap 93; the glue's 96,000 to 103,000 with
cosines −0.15 to −0.18. The field's move over 1,000, 2,000, 3,000 and 6,000 sections is 58,274, 67,220, 78,202 and 101,261 grains
(a free walk would give 1, 1.41, 1.73 and 2.45 of the first). Over many laps the field moved 569,407 grains from lap 50 to lap 70 and
1,167,638 from lap 30 to lap 70, about 28,000 a lap in one direction beside about 72,000 a lap of jitter; its rms grew from 3.86 to 4.51
million grains from lap 22 to lap 94, the level's from 2.91 to 3.93, the glue's from 1.34 to 2.07.

The first audit's `receipts/2026-11-18_audit/travel.py` reads the same travel family by family.

## The cooling read's guesses (fixed 2026-11-18T03:19Z, before any such run exists)

The read: from the store line's lap 70 end state (`STATE.3000`, the store of November 12, the binary that ran lap 70), three arms of
one lap of 3,000 sections each, the learner's rate word set to 12 (the control), 14 and 16 and every other byte of the state kept; each
arm read by `read-cavity` at its `MEAN.3000`. Premise read first: the floor of a constant step was 0.032 to 0.053 nats a place at
`2^(−11)` on the field of November 4 and cooling released 0.043 at once; on November 11 lap ends stood 0.0055 to 0.0107 over their
means.

- G-A1, the control at rate 12: held text, one place open, 0.7710 to 0.7750 (the line's own next lap on the old store); whole masks
  2.206 to 2.218.
- G-A2, rate 14: one-place code under the control's by 0.006 to 0.016 nats a place; whole masks under by 0.003 to 0.015.
- G-A3, rate 16: one-place code under the control's by 0.007 to 0.020, and no more than 0.006 under rate 14's.
- G-A4, travel: the field's rms move over the lap at rate 14 is 0.20 to 0.35 of the control's.
- A fall under 0.004 at both cooler rates says the standing spread is not what holds this line's level, and the form is.

Projection: an arm is one lap (1,536 s at lap 70) and its read (223 s); three arms about 90 minutes of card, each lap under
`.local/gpu.lock`, stop bound 2,400,000 ms and deadline 2,700 s a lap, 1,200 s a read, as chain 18 ran lap 70.
