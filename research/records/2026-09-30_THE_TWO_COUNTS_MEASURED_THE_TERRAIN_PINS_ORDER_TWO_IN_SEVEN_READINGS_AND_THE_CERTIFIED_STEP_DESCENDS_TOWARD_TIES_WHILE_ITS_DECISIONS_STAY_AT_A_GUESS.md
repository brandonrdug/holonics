# The two counts measured: the terrain pins order-2 in seven readings, and the certified step descends the comparison toward ties while its decisions stay at a guess

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6, step 1, loop 1a). **Grade.**
[measured] for every count, curve, table and section below (the pinned runs under the
[pin](2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md), `fb52c27a`, at the build `0093a3c2`);
[proved-derived] where a count follows from a terrain's law (the pin §2); [agent-inferred] where
marked. No learning law changed: the machine is the modulus record's (`6dc1e5ae`).

**Occasion.** THE_REBUILD U6 step 1, loop 1a: measurement only. The
[modulus record](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_MEASURED_THE_MODULUS_STAYS_BELOW_ONE_AND_ORDER_TWO_TRAINING_LEARNS_THE_LAG_ONE_COPY.md)
left order-2 at 0 whole sections after 1,024 rule steps against a family the
[unicity record](2026-09-30_UNICITY_THE_READINGS_LEAVE_ONE_KEY_AND_THE_HELIXS_CELLS_ARE_THE_FAREY_SEQUENCE.md)
§5 can pin in 7 readings. This loop read the two counts on the same passage, and the two candidate
causes (D1, the step's descent; D2, the comparison's operating point) on every move.

The computational object is the helical pair interaction; the receiving bank's rings are complex
parametrons, read through the executed comparison. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touched **faces and
placement** (the stations read), **the cell holonomy** (the executed growth the comparison reads) and
**the tube** (the span's transport, its modulus); the helix, the pair and the tower thread stayed
attached and unchanged.

## 0. The recorded failures this loop could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **1, an authored routine standing in for learning.** The key family was computed by the harness
  from the terrain's pairs and printed; nothing of it reached `executed_move`, the opening or the
  release (`executed counts` and the train mode's `ideal_information` read `terrain_pairs` only).
  The training comparison read the terrain's targets as its declared input, as in every prior loop.
- **6, seen material graded as unseen.** The seeds `2_026_093_031`–`039` appear in no ref, commit or
  artifact before the pin. Order-2's 64 validation requests share no content with its 128 training
  requests (checked exactly). The alternation's and the line's request spaces have 16 members: all
  64 validation requests of each equal a training request (the pin §2 derived it; the counts
  confirm it), so those two terrains are regressions and no count of theirs is a transfer. The final
  confirmation (`2_026_093_033`, `036`, `039`) was read by no run. The one 64-request validation set
  per terrain is reused across both openings and every checkpoint: a comparable diagnostic
  trajectory, not independent confirmations (Astra's review, the pin §4).
- **7, bits read as progress.** The ideal listener's information is reported in bits, apart from `F`
  (nats), and is never equated with a descent.
- **9, a refusal answered with a larger limit.** The validation reads of the alternation and the line
  passed their deadline during their last constitution (`m16`) and were stopped by the outer guard;
  they are reported incomplete (§2) and were not rerun. The projection for the validation reads was
  wrong (§7).
- **11, the programming language.** The family is lags on the passage's clock and maps of `ℤ/4`; its
  survivors are coset products over the map's arguments (Lean `Population.survivors_product`).

## 1. `n*_terrain`: the terrain's counts on the machine's own passage

Every observation's survivors, ratio and code are in `counts_<terrain>_curve.txt`; the logs in
`counts_<terrain>_log.txt`. Both units: `k` observations are `⌊k/8⌋` requests plus `k mod 8`
stations.

| Terrain, family | Survivors at the request boundaries 0–5 | `n*_terrain` (nonconstant validation) | With the constant validation requests | The syntactic class | Code at the end (bits) | Constant training requests' observations carry |
|---|---|---|---|---|---|---|
| order-2, global | 10240, 1, 1, 1, 1, 1 | **7 observations (0 requests plus 7 stations)** | 7 | one key `(2, a ↦ a + 1)`, fixed from observation 7 | `log₂ 10240 = 11 + log₂ 5` ∈ `[3410/256, 3411/256)` | no constant request (0 of 128) |
| alternation, global | 10240, 2560, 320, 80, 80, 20 | **33 observations (4 requests plus 1 station)** | 33 | 20 keys `(2k, id)`, `k ∈ [1, 20]`, fixed from observation 33: one observational class, never one key | `log₂ 512 = 9` | `log₂ 4 = 2` bits (35 of 128 requests constant) |
| line, global | 10240, 2560, 640, 10, 10, 10 | **20 observations (2 requests plus 4 stations)** | 20 | 10 keys `(4k, id)`, `k ∈ [1, 10]`, fixed from observation 20: the global family **does not empty** on the actual passage (the tested result; the pin §2's derivation holds) | `log₂ 1024 = 10` | `log₂ 16 = 4` bits (35 of 128 constant) |
| line, `H` | `40 · 4^(128 − r)` at boundary `r` | **not reached** in 1,024 observations (128 requests plus 0 stations) | not reached | every lag survives (40), each request's translation pinned by its first station | `log₂(4^128) = 256` | 70 bits (2 at each constant request's first station) |

- **The ideal listener's curve** (every informative observation; every other ratio is 1):
  - order-2: `4, 160/29, 29/3, 12, 2, 1, 2` at observations 1–7 (survivors 10240, 2560, 464, 48, 4, 2,
    2, 1). Unicity at exactly `clog₄ 10240 = 7`. [measured, development seed `2_026_093_041`, the
    counts' development read] On another passage the one key was isolated at 6 observations: the
    pigeonhole bound (Lean `Unicity.clog_classes_le_of_separating`) bounds the readings that separate
    **every** pair of keys, not the readings that isolate one key along one passage, where a ratio can
    exceed the alphabet (here `12` and `10`).
  - the alternation: `4` at observation 1 (request 0 is constant: it fixes `f(1) = 1` at every lag),
    `8` at 9, `4` at 18, `4` at 33.
  - the line (global): `4` at 1, `4` at 9, `8/3` at 17, `6` at 18, `4` at 20.
  - the line in `H`: `4` at the first station of every request (its translation), `1` elsewhere: 16
    bits on every batch, for ever; no lag ever dies (every lag fits `x_t − x_(t−ℓ) = sℓ`).
- **The certificates** (the survivor lists at `n*_terrain`): order-2 `ℓ 2 f [1 2 3 0]`, no unobserved
  argument; the alternation `ℓ 2k f [0 1 2 3]`, `k ∈ [1, 20]`, every one but `ℓ 2` a lag alias, no
  unobserved argument; the line `ℓ 4k f [0 1 2 3]`, `k ∈ [1, 10]`, every one an alias (the line's law
  is no global key), no unobserved argument. At the passage's end every validation request of each
  terrain has one admitted continuation in the global family (order-2 64 of 64; the alternation 46
  nonconstant and 18 constant; the line 48 and 16); in `H`, none (25 distinct continuations each).
- **`H` given the request's own first station** (the pin §2's side reading): stations 1–7 of every
  nonconstant validation request are unique at 0 observations: the lag is irrelevant once a line
  request's translation is read.
- **Each move's batch** (the D1 reading): the ideal listener takes all its information on move 0's
  batch (order-2 `10240`, `[3410/256, 3411/256)` bits; the alternation `512`, 9 bits; the line `1024`,
  10 bits) and **0 bits on every later batch** (ratio 1 on moves 1–15); in `H`, `65536` (16 bits) on
  every batch.

## 2. `n*_machine`: the validation reads

Each constitution generated every validation request from the open section; no refused certificate
anywhere. Whole sections are counted nonconstant / constant apart (the success rule reads the
nonconstant ones).

| Order-2 (64 nonconstant, 0 constant) | `ρ` | Released / held | Whole | Success | Stations right (of 512) | By station | First lock at station 0 or 1 | First lock right | Reaching the termination |
|---|---|---|---|---|---|---|---|---|---|
| lossless | 1 | 0 / 64 | 0 | no | 121 | 18 15 13 14 18 10 15 18 | 0 | 0 | 11 |
| opening | `102837/131072` | 57 / 7 | 0 | no | 100 | 4 6 14 12 14 19 23 8 | 1 | 12 | 9 |
| m1 | `1651293/2097152` | 64 / 0 | 0 | no | 101 | 15 10 9 9 6 20 18 14 | 3 | 6 | 1 |
| m2 | `413757/524288` | 61 / 3 | 0 | no | 98 | 11 12 12 17 13 11 9 13 | 4 | 4 | 8 |
| m4 | `1668721/2097152` | 64 / 0 | 0 | no | 110 | 13 9 19 17 16 12 13 11 | 2 | 8 | 0 |
| m8 | `1689365/2097152` | 64 / 0 | 0 | no | 135 | 15 16 12 14 16 11 26 25 | 17 | 16 | 0 |
| m16 | `1718363/2097152` | 64 / 0 | **0** | no | 130 | 16 14 14 14 16 15 19 22 | 10 | 12 | 0 |

| Alternation (46 nonconstant, 18 constant) | `ρ` | Released / held | Whole: nonconstant, constant | Success | Stations right (of 512) | By station | First lock at station 0 or 1 | First lock right |
|---|---|---|---|---|---|---|---|---|
| lossless | 1 | 3 / 61 | 0, 3 | no | 219 | 37 24 31 26 27 23 27 24 | 0 | 3 |
| opening | `102837/131072` | 62 / 2 | 0, 3 | no | 127 | 26 23 17 22 10 10 11 8 | 6 | 8 |
| m1 | `1648223/2097152` | 58 / 6 | 0, 3 | no | 206 | 26 29 43 23 33 21 22 9 | 9 | 14 |
| m2 | `1653133/2097152` | 62 / 2 | 3, 16 | no | 290 | 37 41 31 41 31 41 27 41 | 25 | 41 |
| m4 | `1660929/2097152` | 56 / 8 | 3, 3 | no | 282 | 40 47 35 49 24 47 16 24 | 25 | 45 |
| m8 | `1670183/2097152` | 64 / 0 | **6, 18** | no | 259 | 34 40 29 32 29 38 26 31 | 24 | 33 |
| m16 | — | **not read: the read passed its deadline and was stopped by the guard** | | | | | | |

| Line (48 nonconstant, 16 constant) | `ρ` | Released / held | Whole: nonconstant, constant | Success | Stations right (of 512) | By station | First lock at station 0 or 1 | First lock right |
|---|---|---|---|---|---|---|---|---|
| lossless | 1 | 3 / 61 | 0, 3 | no | 147 | 17 18 20 15 17 22 20 18 | 0 | 3 |
| opening | `102837/131072` | 58 / 6 | 0, 3 | no | 103 | 16 21 12 24 10 7 8 5 | 3 | 5 |
| m1 | `823681/1048576` | 53 / 11 | 0, 3 | no | 111 | 15 11 9 20 22 20 3 11 | 3 | 5 |
| m2 | `1650223/2097152` | 59 / 5 | 0, 5 | no | 123 | 29 17 12 17 9 13 19 7 | 3 | 11 |
| m4 | `1659061/2097152` | 59 / 5 | 0, 8 | no | 132 | 18 10 23 19 21 8 16 17 | 8 | 8 |
| m8 | `837935/1048576` | 63 / 1 | **0, 14** | no | 210 | 33 22 26 35 35 16 25 18 | 11 | 19 |
| m16 | — | **not read: the read passed its deadline and was stopped by the guard** | | | | | | |

Terminations: the alternation 0, 0, 23, 2, 0, 0; the line 14, 4, 11, 5, 7, 1 (lossless to m8).

- **`n*_machine`** [measured]: the success rule holds at no checkpoint read on any terrain.
  Order-2: **`n*_machine > 128` training requests (1,024 observations: 128 requests plus 0 stations)**, a lower bound: all seven constitutions were read inside the deadline and none released a whole section of 64. The alternation and the line: `n*_machine > 64` training requests (512 observations)
  as far as the pinned validation read reached (m8); their m16 reads are incomplete.
- **Against `n*_terrain`**: order-2's `n*_terrain` is 7 observations (0 requests plus 7 stations) and its `n*_machine` exceeds 1,024 observations (128 requests plus 0 stations): the ratio exceeds `1024/7 = 146 rem 2`. The alternation: `n*_terrain` = 33 observations against
  `n*_machine` above 512; the line: 20 against above 512.
- **Beside it, the training passage's own reading** (each fresh batch released by the constitution
  before its move; 8 requests, not the validation set): order-2 released 0 whole sections on every one
  of its 16 batches (stations right between 8 and 23 of 64); the alternation between 0 and 5 whole a
  batch (moves 11–15: 4, 5, 3, 2, 4); the line between 0 and 3.
- **What the releases are.** The alternation's m8 releases its 18 constant requests whole and 6 of
  its 46 alternating ones (`2 1 2 1 2 1 2 1`, `3 1 3 1 3 1 0 1` one station short, `0 0 2 2 2 2 2 2`
  for `0 1 0 1 0 1 0 1`). The line's m8 releases 14 of 16 constant requests whole and no line with a
  nonzero slope. Order-2's m16 releases all 64 sections, none whole; its sections follow order-2's law at 77 of 384 of their own stations (a guess reads 96) and none throughout; 243 of 448 adjacent station pairs are equal (the opening's 91 of 399); m8's classes run to class 0 (405 of 512 stations) and m16's are `222 / 142 / 86 / 62`. The released sections' shapes, every constitution read:

**Order-2.**

| Constitution | Adjacent stations equal | Stations following the law among the section's own | Sections following it throughout | Classes 0 / 1 / 2 / 3 / termination |
|---|---|---|---|---|
| lossless | 0 of 0 | 0 of 0 | 0 | 0 / 0 / 0 / 0 / 0 |
| opening | 91 of 399 | 14 of 342 | 0 | 82 / 180 / 44 / 143 / 7 |
| m1 | 288 of 448 | 34 of 384 | 0 | 16 / 160 / 59 / 276 / 1 |
| m2 | 225 of 427 | 49 of 366 | 0 | 37 / 177 / 82 / 185 / 7 |
| m4 | 244 of 448 | 57 of 384 | 0 | 48 / 75 / 115 / 274 / 0 |
| m8 | 321 of 448 | 51 of 384 | 0 | 405 / 58 / 27 / 22 / 0 |
| m16 | 243 of 448 | 77 of 384 | 0 | 222 / 142 / 86 / 62 / 0 |

**The alternation.**

| Constitution | Adjacent stations equal | Stations following the law among the section's own | Sections following it throughout | Classes 0 / 1 / 2 / 3 / termination |
|---|---|---|---|---|
| lossless | 21 of 21 | 18 of 18 | 3 | 0 / 0 / 0 / 24 / 0 |
| opening | 110 of 434 | 254 of 372 | 13 | 94 / 180 / 65 / 157 / 0 |
| m1 | 167 of 406 | 184 of 348 | 5 | 47 / 130 / 44 / 197 / 46 |
| m2 | 276 of 434 | 343 of 372 | 43 | 162 / 128 / 10 / 196 / 0 |
| m4 | 206 of 392 | 265 of 336 | 17 | 120 / 90 / 17 / 221 / 0 |
| m8 | 341 of 448 | 335 of 384 | 34 | 239 / 55 / 172 / 46 / 0 |

**The line.**

| Constitution | Adjacent stations equal | Stations following the law among the section's own | Sections following it throughout | Classes 0 / 1 / 2 / 3 / termination |
|---|---|---|---|---|
| lossless | 21 of 21 | 18 of 18 | 3 | 0 / 0 / 0 / 24 / 0 |
| opening | 78 of 406 | 105 of 348 | 3 | 103 / 169 / 44 / 144 / 4 |
| m1 | 252 of 371 | 191 of 318 | 3 | 0 / 168 / 18 / 238 / 0 |
| m2 | 205 of 413 | 145 of 354 | 5 | 6 / 186 / 84 / 196 / 0 |
| m4 | 316 of 413 | 248 of 354 | 25 | 16 / 115 / 257 / 78 / 6 |
| m8 | 336 of 441 | 264 of 378 | 17 | 286 / 23 / 147 / 48 / 0 |

The first 16 released sections of each terrain's last read checkpoint (every section of every read
constitution is in `validation_<terrain>_sections.txt`):

**Order-2, m16 (after 16 moves, 128 training requests).**

| Last four request cells | Target | Released | Lock order |
|---|---|---|---|
| 2 2 2 0 | 3 1 0 2 1 3 2 0 | 0 0 1 0 2 2 2 2 | 0 4 5 6 1 7 3 2 |
| 0 2 0 3 | 1 0 2 1 3 2 0 3 | 1 3 2 1 0 0 2 3 | 2 7 6 1 4 5 3 0 |
| 0 3 3 3 | 0 0 1 1 2 2 3 3 | 1 1 1 3 3 3 1 1 | 3 4 5 6 0 2 1 7 |
| 3 0 1 3 | 2 0 3 1 0 2 1 3 | 0 0 1 0 0 0 2 0 | 7 6 5 4 3 1 2 0 |
| 1 0 1 0 | 2 1 3 2 0 3 1 0 | 0 0 1 0 0 0 1 0 | 1 7 0 5 6 3 4 2 |
| 1 2 2 0 | 3 1 0 2 1 3 2 0 | 0 0 0 2 2 2 3 1 | 4 3 1 5 2 0 6 7 |
| 1 1 2 2 | 3 3 0 0 1 1 2 2 | 2 1 1 1 1 1 1 1 | 0 5 2 3 4 6 7 1 |
| 3 2 1 3 | 2 0 3 1 0 2 1 3 | 0 0 0 0 0 0 2 1 | 6 7 5 4 3 2 1 0 |
| 0 0 2 3 | 3 0 0 1 1 2 2 3 | 3 1 0 0 2 3 2 0 | 7 6 3 4 1 2 5 0 |
| 3 3 0 1 | 1 2 2 3 3 0 0 1 | 0 0 0 1 0 0 0 1 | 0 1 4 2 3 6 7 5 |
| 3 0 0 0 | 1 1 2 2 3 3 0 0 | 2 2 3 3 1 1 0 0 | 7 5 6 2 1 3 4 0 |
| 3 2 1 3 | 2 0 3 1 0 2 1 3 | 0 0 0 0 0 0 2 1 | 6 7 5 4 3 2 1 0 |
| 0 0 3 0 | 0 1 1 2 2 3 3 0 | 1 0 0 0 1 0 0 1 | 6 4 5 7 3 2 1 0 |
| 3 1 0 2 | 1 3 2 0 3 1 0 2 | 2 2 2 3 1 1 1 1 | 7 0 1 2 5 6 4 3 |
| 3 1 1 0 | 2 1 3 2 0 3 1 0 | 0 0 0 0 1 2 2 2 | 7 0 3 2 5 4 1 6 |
| 0 2 2 2 | 3 3 0 0 1 1 2 2 | 0 0 1 0 0 0 2 0 | 7 6 5 4 3 1 2 0 |

**The alternation, m8 (its last checkpoint read).**

| Last four request cells | Target | Released | Lock order |
|---|---|---|---|
| 3 3 3 3 (constant request) | 3 3 3 3 3 3 3 3 | 3 3 3 3 3 3 3 3 | 3 4 5 2 0 6 7 1 |
| 3 1 3 1 | 3 1 3 1 3 1 3 1 | 3 1 3 1 3 1 0 1 | 1 3 5 7 6 4 0 2 |
| 0 1 0 1 | 0 1 0 1 0 1 0 1 | 0 0 2 2 2 2 2 2 | 7 6 5 4 3 2 0 1 |
| 1 0 1 0 | 1 0 1 0 1 0 1 0 | 0 0 2 2 2 2 2 2 | 6 7 5 4 3 2 0 1 |
| 2 1 2 1 | 2 1 2 1 2 1 2 1 | 2 1 2 1 2 1 2 1 | 1 3 5 7 6 4 2 0 |
| 2 2 2 2 (constant request) | 2 2 2 2 2 2 2 2 | 2 2 2 2 2 2 2 2 | 0 1 2 3 4 5 6 7 |
| 0 2 0 2 | 0 2 0 2 0 2 0 2 | 0 2 2 2 2 2 2 2 | 3 7 6 5 4 2 1 0 |
| 3 0 3 0 | 3 0 3 0 3 0 3 0 | 2 2 2 2 2 2 2 2 | 7 6 5 4 3 2 1 0 |
| 1 1 1 1 (constant request) | 1 1 1 1 1 1 1 1 | 1 1 1 1 1 1 1 1 | 0 1 2 3 4 5 6 7 |
| 1 0 1 0 | 1 0 1 0 1 0 1 0 | 0 0 2 2 2 2 2 2 | 6 7 5 4 3 2 0 1 |
| 2 3 2 3 | 2 3 2 3 2 3 2 3 | 0 0 0 0 0 0 0 0 | 6 7 5 4 3 2 1 0 |
| 0 0 0 0 (constant request) | 0 0 0 0 0 0 0 0 | 0 0 0 0 0 0 0 0 | 0 1 2 3 4 5 6 7 |
| 3 0 3 0 | 3 0 3 0 3 0 3 0 | 2 2 2 2 2 2 2 2 | 7 6 5 4 3 2 1 0 |
| 2 3 2 3 | 2 3 2 3 2 3 2 3 | 0 0 0 0 0 0 0 0 | 6 7 5 4 3 2 1 0 |
| 0 0 0 0 (constant request) | 0 0 0 0 0 0 0 0 | 0 0 0 0 0 0 0 0 | 0 1 2 3 4 5 6 7 |
| 0 0 0 0 (constant request) | 0 0 0 0 0 0 0 0 | 0 0 0 0 0 0 0 0 | 0 1 2 3 4 5 6 7 |

**The line, m8 (its last checkpoint read).**

| Last four request cells | Target | Released | Lock order |
|---|---|---|---|
| 2 0 2 0 | 2 0 2 0 2 0 2 0 | 0 0 0 0 0 2 1 0 | 6 5 3 2 4 1 0 7 |
| 2 2 2 2 (constant request) | 2 2 2 2 2 2 2 2 | 2 2 2 2 2 2 2 2 | 0 1 2 3 4 5 6 7 |
| 3 1 3 1 | 3 1 3 1 3 1 3 1 | 0 0 0 0 0 2 1 2 | 5 6 7 4 3 2 1 0 |
| 0 1 2 3 | 0 1 2 3 0 1 2 3 | 0 0 0 0 0 2 2 2 | 7 6 5 3 4 2 1 0 |
| 2 2 2 2 (constant request) | 2 2 2 2 2 2 2 2 | 2 2 2 2 2 2 2 2 | 0 1 2 3 4 5 6 7 |
| 0 2 0 2 | 0 2 0 2 0 2 0 2 | 0 0 0 0 0 0 2 1 | 7 6 4 0 3 5 2 1 |
| 3 2 1 0 | 3 2 1 0 3 2 1 0 | 0 0 0 0 0 0 2 2 | 6 0 1 2 3 4 5 7 |
| 0 2 0 2 | 0 2 0 2 0 2 0 2 | 0 0 0 0 0 0 2 1 | 7 6 4 0 3 5 2 1 |
| 1 2 3 0 | 1 2 3 0 1 2 3 0 | 0 0 0 0 0 0 2 2 | 6 2 7 3 4 1 0 5 |
| 0 0 0 0 (constant request) | 0 0 0 0 0 0 0 0 | 0 0 0 0 0 0 0 0 | 1 3 5 7 6 0 4 2 |
| 2 1 0 3 | 2 1 0 3 2 1 0 3 | 0 0 0 0 0 0 0 0 | 2 3 4 5 6 7 1 0 |
| 2 2 2 2 (constant request) | 2 2 2 2 2 2 2 2 | 2 2 2 2 2 2 2 2 | 0 1 2 3 4 5 6 7 |
| 0 1 2 3 | 0 1 2 3 0 1 2 3 | 0 0 0 0 0 2 2 2 | 7 6 5 3 4 2 1 0 |
| 0 1 2 3 | 0 1 2 3 0 1 2 3 | 0 0 0 0 0 2 2 2 | 7 6 5 3 4 2 1 0 |
| 0 3 2 1 | 0 3 2 1 0 3 2 1 | 0 0 0 0 0 0 0 2 | 7 5 6 4 3 2 1 0 |
| 0 3 2 1 | 0 3 2 1 0 3 2 1 | 0 0 0 0 0 0 0 2 | 7 5 6 4 3 2 1 0 |

## 3. D1, the step's descent, per move

All values exact: `F` and the descents are cells `[a, a + 1)` at `2^(−12)` nats written `·/4096`;
the ratio of the measured to the predicted descent is bracketed exactly at `2^(−8)` (its lower end the
measured lower end over the predicted upper end). "Predicted" is the certificate `−Σ sup Df_α[δ]`;
the leading branches' `−Σ sign⟨ĝ, Δz⟩` equals it on every move but order-2's move 5 (where it is
`[37456, 37457)/4096`, above the certificate's `[37279, 37280)/4096`, as the receipts' law requires).
Both are exact enclosures of first-order quantities and approximate as predictions of the finite
change; the measured is exact. Full lines in `train_<terrain>_log.txt`; `two_counts_tables.py`
tabulates them.

**Order-2.**

| Move | `F(θ)` ·/4096 | Trials (halvings) | `η` | `‖ΔE‖_∞` | `Δρ` | Predicted, the certificate ·/4096 | Measured ·/4096 | Measured over predicted ·/256 | Trajectory changed | Open section w→r, r→w | Batch before: released, whole, right |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | `[812812, 812835)` | 1 (0) | `1/8` | `325237/2097152` | `5901/2097152` | `[703669, 703670)` | `[194373, 194416)` | `[70, 71)` | 8 of 8 | 10, 9 | 5, 0, 8 |
| 1 | `[719882, 719903)` | 1 (0) | `1/16` | `106871/1048576` | `3735/2097152` | `[526908, 526909)` | `[277399, 277440)` | `[134, 135)` | 7 of 8 | 5, 7 | 8, 0, 17 |
| 2 | `[435692, 435712)` | 1 (0) | `1/2` | `612623/2097152` | `11347/2097152` | `[338773, 338774)` | `[29944, 29984)` | `[22, 23)` | 8 of 8 | 5, 6 | 8, 0, 16 |
| 3 | `[401037, 401059)` | 2 (1) | `1/8` | `25575/524288` | `1173/1048576` | `[105598, 105599)` | `[43380, 43422)` | `[105, 106)` | 8 of 8 | 4, 0 | 7, 0, 9 |
| 4 | `[388804, 388825)` | 1 (0) | `1/4` | `19875/262144` | `6545/2097152` | `[248623, 248624)` | `[65274, 65316)` | `[67, 68)` | 6 of 8 | 5, 1 | 7, 0, 14 |
| 5 | `[261500, 261519)` | 3 (2) | `1/8` | `6117/262144` | `505/524288` | `[37279, 37280)` (leading `[37456, 37457)`) | `[10129, 10167)` | `[69, 70)` | 5 of 8 | 4, 2 | 8, 0, 23 |
| 6 | `[336786, 336808)` | 2 (1) | `1/2` | `47607/1048576` | `1063/1048576` | `[115512, 115513)` | `[13435, 13478)` | `[29, 30)` | 8 of 8 | 5, 6 | 8, 0, 9 |
| 7 | `[295164, 295185)` | 1 (0) | `1/2` | `31493/524288` | `9953/2097152` | `[153146, 153147)` | `[54787, 54826)` | `[91, 92)` | 8 of 8 | 8, 5 | 8, 0, 18 |
| 8 | `[298287, 298308)` | 1 (0) | `1/2` | `140129/2097152` | `5869/2097152` | `[252030, 252031)` | `[13444, 13483)` | `[13, 14)` | 8 of 8 | 12, 6 | 8, 0, 13 |
| 9 | `[295516, 295537)` | 1 (0) | `1/4` | `53785/1048576` | `9109/2097152` | `[208636, 208637)` | `[66721, 66761)` | `[81, 82)` | 8 of 8 | 10, 9 | 8, 0, 17 |
| 10 | `[234373, 234392)` | 2 (1) | `1/2` | `45337/1048576` | `779/1048576` | `[103727, 103728)` | `[32878, 32917)` | `[81, 82)` | 8 of 8 | 5, 6 | 8, 0, 19 |
| 11 | `[198138, 198159)` | 3 (2) | `1/4` | `3855/262144` | `2807/2097152` | `[40323, 40324)` | `[15734, 15775)` | `[99, 101)` | 8 of 8 | 4, 5 | 8, 0, 14 |
| 12 | `[193741, 193760)` | 2 (1) | `1/2` | `67039/2097152` | `787/524288` | `[54847, 54848)` | `[24810, 24850)` | `[115, 116)` | 8 of 8 | 5, 5 | 8, 0, 17 |
| 13 | `[169459, 169480)` | 2 (1) | `1/4` | `45337/2097152` | `149/131072` | `[56329, 56330)` | `[16200, 16240)` | `[73, 74)` | 8 of 8 | 5, 6 | 8, 0, 13 |
| 14 | `[166772, 166793)` | 3 (2) | `1/2` | `9881/524288` | `195/262144` | `[40958, 40959)` | `[5253, 5293)` | `[32, 34)` | 8 of 8 | 7, 3 | 8, 0, 15 |
| 15 | `[181729, 181749)` | 3 (2) | `1/4` | `28745/2097152` | `2563/2097152` | `[43615, 43616)` | `[30193, 30232)` | `[177, 178)` | 8 of 8 | 4, 7 | 8, 0, 15 |

**The alternation (a regression).**

| Move | `F(θ)` ·/4096 | Trials (halvings) | `η` | `‖ΔE‖_∞` | `Δρ` | Predicted, the certificate ·/4096 | Measured ·/4096 | Measured over predicted ·/256 | Trajectory changed | Open section w→r, r→w | Batch before: released, whole, right |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | `[815349, 815368)` | 1 (0) | `1/16` | `207647/1048576` | `2831/2097152` | `[668174, 668175)` | `[284453, 284488)` | `[108, 109)` | 8 of 8 | 3, 8 | 8, 0, 15 |
| 1 | `[488897, 488914)` | 1 (0) | `1/8` | `282057/2097152` | `2455/1048576` | `[309394, 309395)` | `[36365, 36398)` | `[30, 31)` | 7 of 8 | 11, 6 | 7, 0, 24 |
| 2 | `[324555, 324568)` | 1 (0) | `1/4` | `200143/2097152` | `745/262144` | `[210502, 210503)` | `[57763, 57788)` | `[70, 71)` | 8 of 8 | 8, 7 | 8, 3, 44 |
| 3 | `[326554, 326568)` | 2 (1) | `1/4` | `121705/1048576` | `459/524288` | `[148708, 148709)` | `[37774, 37801)` | `[65, 66)` | 7 of 8 | 14, 5 | 7, 0, 31 |
| 4 | `[357068, 357085)` | 1 (0) | `1/8` | `50277/262144` | `3847/2097152` | `[220555, 220556)` | `[77288, 77317)` | `[89, 90)` | 8 of 8 | 12, 9 | 7, 0, 27 |
| 5 | `[232857, 232871)` | 1 (0) | `1/2` | `280503/1048576` | `197/2097152` | `[223878, 223879)` | `[35802, 35829)` | `[40, 41)` | 6 of 8 | 9, 5 | 7, 1, 32 |
| 6 | `[348251, 348265)` | 1 (0) | `1/4` | `19855/262144` | `-2283/2097152` | `[305307, 305308)` | `[134858, 134885)` | `[113, 114)` | 8 of 8 | 5, 12 | 8, 1, 30 |
| 7 | `[230235, 230253)` | 1 (0) | `1/2` | `23531/262144` | `7493/2097152` | `[167995, 167996)` | `[57481, 57512)` | `[87, 88)` | 8 of 8 | 12, 4 | 8, 0, 20 |
| 8 | `[267298, 267313)` | 1 (0) | `1/8` | `85553/2097152` | `-515/1048576` | `[227486, 227487)` | `[80583, 80610)` | `[90, 91)` | 6 of 8 | 13, 6 | 8, 3, 27 |
| 9 | `[184408, 184419)` | 1 (0) | `1/2` | `132851/2097152` | `7553/2097152` | `[122743, 122744)` | `[80920, 80938)` | `[168, 169)` | 5 of 8 | 7, 9 | 8, 3, 41 |
| 10 | `[242795, 242810)` | 3 (2) | `1/8` | `48151/2097152` | `-375/1048576` | `[59176, 59177)` | `[56198, 56227)` | `[243, 244)` | 7 of 8 | 3, 4 | 8, 0, 24 |
| 11 | `[147729, 147737)` | 1 (0) | `1` | `174233/2097152` | `115/2097152` | `[107318, 107319)` | `[73520, 73535)` | `[175, 176)` | 7 of 8 | 10, 7 | 8, 4, 45 |
| 12 | `[101106, 101115)` | 1 (0) | `1/2` | `67791/2097152` | `2353/524288` | `[53992, 53993)` | `[30048, 30065)` | `[142, 143)` | 3 of 8 | 4, 3 | 8, 5, 47 |
| 13 | `[136725, 136737)` | 1 (0) | `1/4` | `27235/1048576` | `5807/2097152` | `[68774, 68775)` | `[29474, 29497)` | `[109, 110)` | 5 of 8 | 8, 2 | 8, 3, 38 |
| 14 | `[104870, 104883)` | 3 (2) | `1/4` | `12543/1048576` | `5023/2097152` | `[23192, 23193)` | `[3475, 3499)` | `[38, 39)` | 4 of 8 | 0, 5 | 8, 2, 35 |
| 15 | `[91472, 91484)` | 1 (0) | `1/4` | `6937/262144` | `159/1048576` | `[59279, 59280)` | `[30022, 30042)` | `[129, 130)` | 4 of 8 | 9, 4 | 8, 4, 52 |

**The line (a regression).**

| Move | `F(θ)` ·/4096 | Trials (halvings) | `η` | `‖ΔE‖_∞` | `Δρ` | Predicted, the certificate ·/4096 | Measured ·/4096 | Measured over predicted ·/256 | Trajectory changed | Open section w→r, r→w | Batch before: released, whole, right |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | `[656561, 656578)` | 1 (0) | `1/16` | `228077/2097152` | `985/1048576` | `[603309, 603310)` | `[283124, 283154)` | `[120, 121)` | 7 of 8 | 2, 9 | 8, 1, 19 |
| 1 | `[595408, 595428)` | 1 (0) | `1/16` | `41833/524288` | `2861/2097152` | `[300416, 300417)` | `[161866, 161904)` | `[137, 138)` | 7 of 8 | 11, 2 | 6, 1, 13 |
| 2 | `[424098, 424117)` | 1 (0) | `1/8` | `14881/131072` | `3525/2097152` | `[247746, 247747)` | `[61187, 61220)` | `[63, 64)` | 8 of 8 | 17, 1 | 7, 0, 13 |
| 3 | `[402661, 402677)` | 1 (0) | `1/8` | `21517/262144` | `5313/2097152` | `[351117, 351118)` | `[112449, 112481)` | `[81, 83)` | 5 of 8 | 4, 6 | 8, 2, 30 |
| 4 | `[229590, 229604)` | 2 (1) | `1/4` | `70071/2097152` | `5993/2097152` | `[79360, 79361)` | `[4430, 4458)` | `[14, 15)` | 3 of 8 | 7, 6 | 8, 3, 31 |
| 5 | `[284938, 284956)` | 2 (1) | `1/4` | `252589/2097152` | `119/1048576` | `[111458, 111459)` | `[41700, 41736)` | `[95, 96)` | 6 of 8 | 4, 6 | 8, 1, 22 |
| 6 | `[169420, 169433)` | 1 (0) | `1/2` | `44729/524288` | `2233/2097152` | `[158764, 158765)` | `[62352, 62374)` | `[100, 101)` | 6 of 8 | 16, 5 | 8, 2, 36 |
| 7 | `[379492, 379510)` | 1 (0) | `1/2` | `144993/1048576` | `8345/2097152` | `[251069, 251070)` | `[119345, 119380)` | `[121, 122)` | 8 of 8 | 13, 7 | 8, 0, 23 |
| 8 | `[304253, 304273)` | 1 (0) | `1/4` | `140547/2097152` | `431/262144` | `[258805, 258806)` | `[9227, 9265)` | `[9, 10)` | 8 of 8 | 21, 8 | 8, 0, 16 |
| 9 | `[213132, 213148)` | 2 (1) | `1/2` | `41125/1048576` | `2637/2097152` | `[62803, 62804)` | `[15762, 15793)` | `[64, 65)` | 7 of 8 | 8, 4 | 8, 2, 30 |
| 10 | `[219715, 219732)` | 1 (0) | `1/2` | `126813/2097152` | `907/2097152` | `[110460, 110461)` | `[21320, 21352)` | `[49, 50)` | 8 of 8 | 6, 2 | 8, 1, 26 |
| 11 | `[157560, 157572)` | 1 (0) | `1` | `145465/2097152` | `22465/2097152` | `[125591, 125592)` | `[7422, 7443)` | `[15, 16)` | 8 of 8 | 7, 5 | 8, 3, 36 |
| 12 | `[212222, 212238)` | 1 (0) | `1/4` | `17437/524288` | `5115/2097152` | `[113080, 113081)` | `[31204, 31237)` | `[70, 71)` | 7 of 8 | 1, 11 | 8, 1, 23 |
| 13 | `[163914, 163929)` | 1 (0) | `1/2` | `125055/2097152` | `9399/2097152` | `[80497, 80498)` | `[61594, 61620)` | `[195, 196)` | 8 of 8 | 11, 1 | 8, 2, 28 |
| 14 | `[157571, 157584)` | 2 (1) | `1/2` | `56459/2097152` | `7489/2097152` | `[60549, 60550)` | `[22539, 22564)` | `[95, 96)` | 7 of 8 | 4, 3 | 8, 2, 31 |
| 15 | `[161183, 161200)` | 1 (0) | `1` | `18473/262144` | `1689/2097152` | `[89700, 89701)` | `[9378, 9409)` | `[26, 27)` | 8 of 8 | 13, 6 | 8, 1, 22 |

**D1 read across the three trainings (48 moves).**
- **Every move adopted** (48 of 48), no move refused; **no prediction zero or below the grain** (the
  grain, `F(θ)`'s enclosure width, lies between `126/65536` and `345/65536` nats, inside
  `(2^(−10), 2^(−7))`; the least predicted descent is `[23192, 23193)/4096` nats, above `2²`).
- **The derivative is right in sign**: the measured descent is positive and the leading branches'
  prediction agrees in sign on 48 of 48.
- **The first order over-predicts the finite change**: measured over predicted lies between `[9, 10)/256`
  and `[243, 244)/256`; it is at least `1/8` on 13 of 16 order-2 moves (not on moves 2, 6, 8), 15 of 16
  alternation moves (not move 1), 12 of 16 line moves (not 4, 8, 11, 15). The successor's trajectory
  (its lock order) changes in at least 3 of the 8 requests on every move, and in all 8 on 13 of
  order-2's 16 moves, so the measured `C(θ) − C(θ + δ)` includes a changed trajectory the first order
  does not see. Every one of the 22 halvings was a `NotBelow` refusal (the carried successor's `F` not
  strictly below by disjoint enclosures: the step overshot); no trial was refused by the first order,
  the entry bound, admission, a Floquet certificate or the constitution's guards, and no read release
  refused a certificate.
- **Feasibility is never active**: the ladder's start is set by the first-order zero `F⁻/(−slope⁺)` on
  every move (never the entry scale); the passive bound is never active; no trial is refused by the
  entry bound (`E`'s largest entry at most `405339/524288`, below `4/5`, against the bound 8);
  halvings (a trial refused `NotBelow`) on 9 of 16 order-2 moves, 3 alternation and 4 line moves. The
  carry staged 605 entries with a nonzero lattice quotient on most moves (484 or 483 on the rest), with
  `‖ΔE‖_∞` between `3855/262144` and `612623/2097152`.
- **The step moves decisions, both ways**: at the open section of the batch, order-2's moves sent 98
  stations wrong→right and 83 right→wrong over the 16 moves; the alternation 128 and 96; the line
  145 and 82.
- **The ideal listener** takes its whole code on move 0's batch and nothing after (§1), while `F`
  keeps falling on later batches: order-2's `F` at each fresh batch falls from `[812812, 812835)/4096`
  to `[181729, 181749)/4096` at move 15.

## 4. D2, the comparison's operating point, per move

At the open section (the one context every constitution reads alike: all 8 stations of each of the 8
requests) — the class gap `γ = ln a_t − ln a_r` and the target's threshold margin `ln a_t`, in nats at
`2^(−8)`. The full strata (every refinement and the open section; right, wrong-confident,
wrong-not-eligible; constant and nonconstant; signs, sums, extremes, derivatives) are the `D2` lines of
`train_<terrain>_log.txt`.

**Order-2.**

| Move | Right | Wrong (all confident) | Mean `|γ|` of the right ·/256 (lower end) | Mean `|γ|` of the wrong ·/256 | Mean target margin of the wrong ·/256 (lower end) | The wrong terms' derivative: descending, rising (zero, below grain) |
|---|---|---|---|---|---|---|
| 0 | 11 | 53 (53) | 244 | `[227, 228)` | 124 | 39, 14 (0, 0) |
| 1 | 14 | 50 (50) | 63 | `[176, 177)` | 192 | 37, 13 (0, 0) |
| 2 | 14 | 50 (50) | 44 | `[149, 150)` | 147 | 43, 7 (0, 0) |
| 3 | 4 | 60 (60) | 98 | `[118, 119)` | 152 | 47, 13 (0, 0) |
| 4 | 8 | 56 (56) | 50 | `[127, 128)` | 167 | 39, 17 (0, 0) |
| 5 | 12 | 52 (52) | 55 | `[102, 103)` | 134 | 40, 12 (0, 0) |
| 6 | 12 | 52 (52) | 27 | `[107, 108)` | 133 | 36, 16 (0, 0) |
| 7 | 15 | 49 (49) | 38 | `[116, 117)` | 151 | 39, 10 (0, 0) |
| 8 | 11 | 53 (53) | 31 | `[95, 96)` | 170 | 38, 15 (0, 0) |
| 9 | 14 | 50 (50) | 40 | `[97, 98)` | 188 | 41, 9 (0, 0) |
| 10 | 11 | 53 (53) | 42 | `[88, 89)` | 161 | 42, 11 (0, 0) |
| 11 | 9 | 55 (55) | 25 | `[68, 69)` | 195 | 35, 20 (0, 0) |
| 12 | 12 | 52 (52) | 46 | `[68, 69)` | 187 | 37, 15 (0, 0) |
| 13 | 14 | 50 (50) | 22 | `[60, 61)` | 203 | 30, 20 (0, 0) |
| 14 | 11 | 53 (53) | 33 | `[65, 66)` | 193 | 37, 16 (0, 0) |
| 15 | 16 | 48 (48) | 26 | `[75, 76)` | 194 | 30, 18 (0, 0) |

**The alternation.**

| Move | Right | Wrong (all confident) | Mean `|γ|` of the right ·/256 (lower end) | Mean `|γ|` of the wrong ·/256 | Mean target margin of the wrong ·/256 (lower end) | The wrong terms' derivative: descending, rising (zero, below grain) |
|---|---|---|---|---|---|---|
| 0 | 27 | 37 (37) | 160 | `[297, 298)` | 185 | 27, 10 (0, 0) |
| 1 | 20 | 44 (44) | 136 | `[152, 153)` | 279 | 32, 12 (0, 0) |
| 2 | 33 | 31 (31) | 166 | `[153, 154)` | 254 | 26, 5 (0, 0) |
| 3 | 26 | 38 (38) | 89 | `[123, 124)` | 186 | 29, 9 (0, 0) |
| 4 | 31 | 33 (33) | 86 | `[125, 126)` | 197 | 25, 8 (0, 0) |
| 5 | 33 | 31 (31) | 81 | `[136, 137)` | 155 | 29, 2 (0, 0) |
| 6 | 39 | 25 (25) | 109 | `[130, 131)` | 203 | 18, 7 (0, 0) |
| 7 | 26 | 38 (38) | 63 | `[117, 118)` | 238 | 31, 7 (0, 0) |
| 8 | 31 | 33 (33) | 101 | `[88, 89)` | 311 | 20, 13 (0, 0) |
| 9 | 43 | 21 (21) | 147 | `[104, 105)` | 182 | 17, 4 (0, 0) |
| 10 | 30 | 34 (34) | 70 | `[117, 118)` | 186 | 23, 11 (0, 0) |
| 11 | 42 | 22 (22) | 139 | `[84, 85)` | 172 | 18, 4 (0, 0) |
| 12 | 48 | 16 (16) | 176 | `[58, 59)` | 247 | 8, 8 (0, 0) |
| 13 | 36 | 28 (28) | 134 | `[70, 71)` | 198 | 22, 6 (0, 0) |
| 14 | 43 | 21 (21) | 92 | `[68, 69)` | 225 | 17, 4 (0, 0) |
| 15 | 39 | 25 (25) | 109 | `[52, 54)` | 182 | 20, 5 (0, 0) |

**The line.**

| Move | Right | Wrong (all confident) | Mean `|γ|` of the right ·/256 (lower end) | Mean `|γ|` of the wrong ·/256 | Mean target margin of the wrong ·/256 (lower end) | The wrong terms' derivative: descending, rising (zero, below grain) |
|---|---|---|---|---|---|---|
| 0 | 32 | 32 (32) | 233 | `[268, 269)` | 194 | 23, 9 (0, 0) |
| 1 | 15 | 49 (49) | 146 | `[193, 194)` | 204 | 39, 10 (0, 0) |
| 2 | 17 | 47 (47) | 80 | `[121, 122)` | 247 | 38, 9 (0, 0) |
| 3 | 26 | 38 (38) | 106 | `[141, 142)` | 198 | 30, 8 (0, 0) |
| 4 | 27 | 37 (37) | 111 | `[152, 153)` | 162 | 29, 8 (0, 0) |
| 5 | 18 | 46 (46) | 62 | `[139, 140)` | 152 | 36, 10 (0, 0) |
| 6 | 26 | 38 (38) | 65 | `[109, 110)` | 195 | 31, 7 (0, 0) |
| 7 | 17 | 47 (47) | 51 | `[115, 116)` | 166 | 39, 8 (0, 0) |
| 8 | 14 | 50 (50) | 27 | `[59, 60)` | 158 | 45, 5 (0, 0) |
| 9 | 25 | 39 (39) | 80 | `[85, 86)` | 136 | 21, 18 (0, 0) |
| 10 | 23 | 41 (41) | 68 | `[81, 82)` | 142 | 34, 7 (0, 0) |
| 11 | 37 | 27 (27) | 205 | `[62, 63)` | 153 | 20, 7 (0, 0) |
| 12 | 29 | 35 (35) | 46 | `[71, 72)` | 112 | 24, 11 (0, 0) |
| 13 | 28 | 36 (36) | 101 | `[75, 76)` | 90 | 31, 5 (0, 0) |
| 14 | 36 | 28 (28) | 72 | `[104, 105)` | 80 | 19, 9 (0, 0) |
| 15 | 22 | 42 (42) | 35 | `[76, 77)` | 87 | 33, 9 (0, 0) |

**D2 read across the three trainings.**
- **Every wrong decision at the open section is confident** (eligible: its top's flip and lock both
  certified, so the release would lock the wrong class) on every move of every terrain; over every
  refinement, 3,474 of order-2's 3,512 wrong decisions, 2,278 of the alternation's 2,298 and 2,730 of
  the line's 2,763. The wrong decisions' targets are past threshold too (their margins' mean lower end
  between 80/256 and 311/256 nats): every candidate locks, and the comparison is read far past
  threshold, where a lock is already decided.
- **`F`'s support is the wrong decisions**: order-2's terms of `F` over the 16 moves are 3,512 wrong
  decisions and 16 right ones (right decisions whose threshold failed); the alternation 2,298 and 7;
  the line 2,763 and 9. A right decision leaves `F` (its hinge is zero) and nothing holds its margin.
- **The derivative is not saturated**: of order-2's 3,528 terms, 1 has a derivative exactly zero, none
  below its grain, 2,690 descend and 837 rise along the carried move; the alternation and the line
  alike (none zero or below grain among their wrong terms).
- **The contrasts shrink toward ties, right and wrong alike**: order-2's wrong decisions' mean `|γ|`
  at the open section falls from `[227, 228)/256` to `[75, 76)/256` nats and the right decisions'
  from 244/256 to 26/256, while the right decisions stay at 4 to 16 of 64 (a guess among 4 classes
  reads 16) and the wrong at 48 to 60. The alternation's wrong mean `|γ|` falls from `[297, 298)/256`
  to `[52, 54)/256` as its right decisions rise from 27 to between 36 and 48 of 64 (its constant
  requests and some alternating ones), its right decisions' mean gap from 160/256 to 109/256; the line's from `[268, 269)/256` to `[76, 77)/256` with its right
  decisions between 14 and 37.

## 5. The prediction and the falsifiers, read as written

The pin §7 predicted [agent-inferred] that the dominant cause is an unsuitable objective read through
D2 (`F = Σ (f)_+` is zero on the tie manifold, so the certified descent shrinks the wrong decisions'
gaps instead of flipping them), not a step too small (D1).
- **D1's bullet, "every adopted move's measured descent is positive and at least 1/8 of the
  certificate's; signs agree on every move; no prediction zero or below the grain; the entry bound
  refuses no trial"**: holds except "at least 1/8" on order-2's moves 2, 6 and 8 (3 of 16).
- **The ideal listener's bullet** (at least 13 bits on move 0's batch, 0 after): holds.
- **D2's bullet** (the wrong decisions' mean `|γ|` at the open section falls by at least half from
  move 0 to 15, while their count at moves 12–15 is at least 3/4 of moves 0–3; wrong→right flips at
  most twice right→wrong): holds on order-2 (`[227, 228)` to `[75, 76)`; 203 against 213; 98 against
  83).
- **The counts' bullet**: `n*_terrain` on order-2 is 7 (at most 24: holds); the line's global family
  keeps exactly the 10 keys `(4k, id)` (holds); the success rule holds nowhere read (holds as far as
  read; order-2 read at all seven constitutions).

The falsifiers:
1. Measured below 1/8 of the certificate or opposite in sign on a majority of adopted order-2 moves:
   **does not fire** (3 of 16 below 1/8, none opposite).
2. A majority of order-2 moves refused, zero, below the grain or bound by the entry bound: **does not
   fire** (none).
3. The wrong decisions' mean `|γ|` does not fall by half: **does not fire**.
4. The wrong decisions fall below 3/4 of their early count, or wrong→right exceeds twice
   right→wrong: **does not fire on order-2** (on the alternation, a regression, the wrong decisions
   at moves 12–15 are 90 against 150 at moves 0–3: below 3/4 there).
5. The success rule holds for order-2 at some checkpoint: **does not fire** (0 whole of 64 at every constitution, m16 included).
6. `n*_terrain` on order-2 above 24 observations: **does not fire** (7).
7. A resource bound reached: **fires** on the validation reads of the alternation and the line (both
   stopped by the outer guard during m16); order-2's validation read completed inside its deadline (2,374,491 ms).

## 6. What the measurement motivates [agent-inferred; no loop 1b is designed here]

- **Not the step's size, not the derivative, not feasibility, not the grain, not a saturated
  derivative.** The certified step descends `F` on every move, in the predicted direction, with no
  bound active and no term's derivative vanishing.
- **The objective and the operating point, together.** The machine's executed comparison is read far
  past threshold (every wrong decision already locked and eligible), and its declared composition
  `F = Σ (f)_+` has no term for a decision once it is right and is zero on ties: the descent it
  certifies spends itself shrinking every contrast, right and wrong, while the decisions stay at the
  level of a guess on order-2. The measurement motivates, as 1b's subject, a comparison whose descent
  must move decisions (one that keeps a margin on the right ones and is not minimized on ties), read
  where a reading carries information about the key.
- **The two counts' gap is the listener's, not the step's.** The ideal listener hears order-2's key
  in 7 readings, on the first batch, and then hears nothing; the machine's step keeps descending on
  batches that carry no new key information. Elimination (the survivors' coset product) reaches the
  class at the data's rate; the executed comparison's descent does not reach it.
- **Kept attached**: the adaptable operands left out (the bank's members, the pumps, the other
  families) and the release's order (the first lock lands on a request-reading station in at most 25
  of 64 validation sections) were not read here.

## 7. Time and memory

| Run | Measured ms | Projection / deadline | Peak resident bytes |
|---|---|---|---|
| counts: order-2, alternation, line | 2,954; 5; 25 (as the pipeline timed them) | 1,000–120,000 / 600,000 | 4,775,936; 4,018,176; 4,763,648 |
| training, order-2, 16 moves | 6,903,740 | 5,300,000–9,000,000 / 9,000,000 | 247,791,616 |
| training, alternation, 16 moves | 4,720,949 | 4,000,000–9,000,000 / 9,000,000 | 232,947,712 |
| training, line, 16 moves | 5,050,727 | 4,000,000–9,000,000 / 9,000,000 | 239,828,992 |
| validation, order-2, 7 × 64 | 2,374,491 | 900,000–2,700,000 / 2,700,000 | 70,225,920 |
| validation, alternation, 7 × 64 | **stopped at 2,760,020** (m8 written at 2,605,156, inside the deadline; m16 unread) | 900,000–2,700,000 / 2,700,000 | not printed |
| validation, line, 7 × 64 | **stopped at 2,760,007** (m8 written at 2,497,650; m16 unread) | 900,000–2,700,000 / 2,700,000 | not printed |

The partition rule read the development move first (`2_026_093_041`, three at once on 8 threads:
the slowest 393,874 ms, `393874 · 16 · 5/4 = 7877480 ≤ 9000000`), so the pipelines ran at once, each
on 8 threads. The trainings met their projections. **The validation reads' projection was wrong**: it
scaled the previous confirmation's rate (about 1,951 ms a request on 24 threads) by at most 3, while
the six constitutions each read took 2,605,156 ms for 384 request reads on the alternation and
2,497,650 ms on the line, on 8 threads under three-way contention (a trained constitution releases
through up to 8 refinements, where the lossless opening holds after one); and the harness read the
constitutions in the order lossless, opening, m1 … m16, so the one past the deadline was the last
checkpoint. Order-2's read, alone on its pool after the other two stopped, finished inside it. The per-constitution times were not printed (the clock
started after the parallel generation; a defect of the harness's receipt, not of the reads).

## 8. Owed in #62

"The two counts" (September 30; the pin `fb52c27a`, the modes `0093a3c2`; receipt-only fields in
`hnn::executed`, held by `the_moves_receipts_read_its_certificate`):
1. **The lag-map family's survivors as a coset product**: for the family `[1, L] × (ℤ/q → ℤ/q)` read
   by the emitter `f(x_(t−ℓ))`, `#S_k = Σ_(ℓ alive) q^(u_ℓ(k))` (an instance of
   `Population.survivors_product` over the map's arguments), and `H`'s count
   `Σ_ℓ Π_r #C_(ℓ,r)` with its reset.
2. **The line's global aliases**: on every line passage over `ℤ/4` the keys `(4k, id)` survive every
   reading (`x_t − x_(t−4k) = 4ks ≡ 0`); every lag survives in `H`; a fresh request has no unique `H`
   continuation. The alternation's even-lag class `(2k, id)`.
3. **The pigeonhole bound's scope**: `clog_|C| |K|` bounds the readings that separate every pair of
   keys (`Unicity.clog_classes_le_of_separating`), not the readings that isolate one key on one
   passage (measured at 6 below 7 on a development passage): the per-passage statement, and the
   expected form under a key law.
4. **The executed comparison's tie manifold**: `F = Σ (f)_+` with `f = max(max_x ln(a_x/a_t), −ln a_t)`
   is zero on every candidate tie above threshold, where `predicates_release_the_section`'s hypothesis
   (`f < 0` strictly) fails; `F = 0` does not imply the class predicate. The statement, and the
   composition's missing margin term for a right decision.
5. **The first order across a trajectory change**: the certified first order bounds the directional
   derivative at a fixed trajectory; the measured `C(θ) − C(θ + δ)` crosses changed lock orders (most
   requests on most moves). The domain on which the first order is a prediction (the trajectory's
   constancy region) is owed.

## 9. Commits and gates

- `fb52c27a`: the pin (with Astra's three clarifications folded in before any run).
- `0093a3c2`: the modes (`executed counts`; D1, D2 and the checkpoints in `executed train`; the
  constant split and the success rule in `executed evaluate`), the receipt-only fields in
  `hnn::executed`, the test `the_moves_receipts_read_its_certificate`.
- This record's commit: the record and its receipts (`2026-09-30_THE_TWO_COUNTS_receipts/`, synthetic
  terrain only): the pipeline that ran (`pinned_runs.sh`) and its exit lines (`runs_<terrain>.txt`);
  every run's log; every observation's curve (`counts_<terrain>_curve.txt`); the constitution after
  moves 1, 2, 4, 8 and 16 (`E_<terrain>.txt.m<k>`; each training's final write was byte-identical to
  its `.m16` and is not kept); every validation section read; the development reads the record cites
  (`development/`: the order-2 counts on `2_026_093_041` and the three timing moves); and
  `two_counts_tables.py`, which tabulates D1, D2 and the sections' shapes from the logs
  (`python3 two_counts_tables.py <receipts>` and `… shapes`).

Gates at `0093a3c2`: `cargo check --workspace --all-targets` clean; `cargo test -p holonics --lib` 976
passed (975 before, plus the receipts test). No Lean changed, so `tools/lean_check.sh` was not run; no
card run.
