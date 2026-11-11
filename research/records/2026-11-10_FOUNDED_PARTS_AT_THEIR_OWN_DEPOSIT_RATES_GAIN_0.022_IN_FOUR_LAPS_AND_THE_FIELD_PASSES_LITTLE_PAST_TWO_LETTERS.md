# Founded parts at their own deposit rates gain 0.022 in four laps, and the field passes little past two letters

Status (2026-11-10; §6 added 2026-11-11, 04:00 UTC): measurement. §6 carries the line to lap 11, corrects a score that compared unequal laps, and replaces the rule's threshold of 1/2 by a derived one, which is under test and unread. These are theory's orders of November 10, from 18:30 to 21:34, on the 64-contact lane field:
- a deposit rate per founded part;
- the field's transmission by joint;
- the keyed read by octave;
- contacts by fours;
- the significant-digit read;
- a projection of growth routes.

The training law lives on the local branch `claude/v14-face-line`: 01bd3b362 with the contacts growth and the part rates. The lane line trains with that tree's binaries. The readers are on main (PRs #644, #648 and #651). Refs #73, #406.

## 1. A deposit rate per founded part

[definition; theory, November 10 19:05; claude/v14-face-line 0b2ba0bad] A part is a family of entries founded together. There
are 15 parts:
- the new contacts' `W` columns;
- their `a` rows (with their biases);
- their `b` rows (with their biases);
- each lane-2 family: `enc`, `before`, `after`, `q`, `v`, `probe`, `out`, `moment_face`, `read`, the face biases, and the `a` and `b` columns.

The founding's own entries stay at 2^-12. A part steps at its own rate, carried in the learner's state (a trailing `parts` line, no run switch). After each lap, from the saved states, c is the cosine between the part's last two lap displacements:
- above 1/2, the part's rate goes one octave faster;
- below 1/2, one slower, never under 2^-12;
- at exactly 1/2, it rests.

The opening, from the four laps already run, put the contact set's three parts and the lane's `enc`, `before` and `after` at 2^-9, and every other part at 2^-12. With every part at 2^-12, the build reproduces the plain lap's section lines bit for bit. Card parity holds for faces and covectors, and no kernel changed. `tools/part_rates.py` moves the rates between laps.

[measurement; RTX 4080 SUPER under `.local/gpu.lock`] Four laps from the 64-contact lap 4 (ct4: held joint 1.8043, references' locked code on HELD128 0.5694), against the plain rate from the same state:

| Lap | Held joint, part rates | Held joint, plain | Locked code, part rates | Locked code, plain |
| --- | --- | --- | --- | --- |
| 1 | 1.7943 | 1.7971 | 0.5555 | 0.5620 |
| 2 | 1.7855 | 1.7917 | 0.5520 | 0.5597 |
| 3 | 1.7727 | 1.7858 | 0.5428 | 0.5574 |
| 4 | 1.7622 | 1.7838 | 0.5305 | 0.5534 |

- **Against the guesses.** After four laps the part rates are 0.022 under on the held joint and 0.023 under on the locked code. Theory guessed at least 0.03 and 0.02, with under 0.01 meaning travel does not bind. Travel binds: the locked-code guess holds, and the held-joint guess falls short.
- **The contact parts' rates.** Each update sets the rate for the next lap. The three contact parts rose to 2^-8 after lap 1 (c 0.51–0.53). Their cosines then fell (0.34, then about 0), and they stepped down to 2^-9, 2^-10 and 2^-11.
- **The lane's rates.** Its `enc`, `before` and `after` went 2^-8, 2^-7 (c 0.60), 2^-8 (c 0.45) and 2^-9 (c 0.19). Its face biases went 2^-12, 2^-11, 2^-10 and 2^-9 (c 0.73–0.77). Every other part held at 2^-12.
- **The plain line.** It falls a steady 0.002–0.007 a lap (ct9 1.7751), so laps stay a lever (theory, 20:39). Both arms run on.

## 2. The field's transmission by joint

[measurement; `transmission-field`, held 0–31, ct8] The read takes the code at a place when only its nearest answer letters are written.
- **With the void around the window,** the field reads 16.4 nats at d = 0. The void tells it the answer has ended, so this regime is not the count table's.
- **With the rest of the answer open** (lengths given, only the window written, one target per region):
  - Sharing a region between targets leaked up to 0.32 nats at spacing 12, and 0.06 at spacing 64.
  - The full read takes 185 s.

| Row (nats a place) | ct8 | Text count table |
| --- | --- | --- |
| left, d = 0..4 | 3.214, 2.678, 2.239, 2.069, 2.040 | 3.481, 2.710, 1.898, 1.423, 1.224 |
| passed by each added left letter | 0.536, 0.439, 0.169, 0.029 | 0.71, 0.73, 0.51, 0.23 |
| both sides, d = 1..4 | 1.939, 1.299, 1.139, 1.091 | 1.564, 0.569, 0.419, 0.397 |
| splits (3,1), (1,3), (2,1), (1,2) | 1.435, 1.489, 1.548, 1.601 | 0.690, 0.714, 0.923, 0.938 |

- **Against G12** (theory: full gain at d = 1 and 2, under half the text's at d = 3). It fails at d = 1 and 2, where the field reaches 75% and 60% of the text's gain. It holds at d = 3, at 33%.
- **The joint lags most.** Both-sides context falls furthest short, 0.73 behind the text at two letters each side.
- **Why the joint lags.** This fits the pair contact's form. Within a tick, contact `e` multiplies a site's own `a` by one mate's `b`: the site before for an even `e`, the one after for an odd `e` (`Field::tick`, `strand_mate`). The contacts then add into the face, so a cell of left × place × right forms only across ticks.
- **The part-rate arm.** rt2 is within 0.02 of ct8 on every row.

## 3. The keyed read by octave

[measurement; `order-field` on ct6, claude/v14-face-line debae3b1b] This is the keyed order given held's lengths. Its total reproduces 1.677 nats a letter (2.420 bits).

Each octave j holds the answer positions in [2^j, 2^(j+1)). When an octave is read, these are already written:
- the question;
- every earlier octave;
- the earlier-keyed places of its own octave;
- the near voids at the end.

| Positions | 1 | 2–3 | 4–7 | 8–15 | 16–31 | 32–63 | 64–127 | 128–255 | 256–511 | 512–1,023 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Places | 32 | 64 | 128 | 256 | 503 | 981 | 1,856 | 2,362 | 2,138 | 440 |
| Nats a letter | 0.717 | 0.100 | 0.176 | 0.845 | 1.664 | 1.676 | 1.865 | 1.851 | 1.640 | 1.374 |

The code's octaves are position ranges, not the stride classes that G18 assumed, so G18's five numbers do not map onto them.

## 4. Contacts by fours, and the significant digits

[measurement]
- **Any count in fours.** `Field::contacted` takes any added count that keeps f/2 even. Its test adds 4, 12, 8 and 20, and refuses an odd step.
- **Tiling.** Every f from 68 to 168 tiles on the main line's declaration (width 64, two lanes). f 172 is the first refused: the pair-return map needs 50,080 shared bytes against 49,152.
- **Card parity at f 68.** Faces and covectors are equal. Learner texts are equal after sections 2–4. Section 1 reads clocks unequal, as on every laned field.

[measurement; G21, ct8 copies, `tools/round_state.py`, `joint-field`] Every stored material number is rounded to its leading s significant binary digits (nearest, sign kept, zero kept). The unrounded copy reads 1.783804, which is ct8's own figure.

| s | 8 | 4 | 2 | 1 |
| --- | --- | --- | --- | --- |
| Held joint change (theory's guess) | +0.0002 (+0.0005) | +0.018 (+0.006) | +0.197 (+0.06) | +1.322 (+0.5) |

- **At s = 4.** The change falls between theory's two lines: under 0.01 would mean the further digits are baggage, and 0.03 or more that they carry law.
- **By part at s = 4.** The faces' families give +0.005, the contacts' +0.006 and the heads' +0.004.
- **On the card.** Every number is an i32 at a 2^-16 or 2^-24 grain, one grain per family, with no per-number exponent. The mean significant bits are 16.7 for faces, 20.1 for contacts, 17.8 for lanes and 19.2 for heads.

## 5. The growth routes, projected

[measurement; host layout, no run] The base is the main line (width 64, f 64, material 63,606, 1,104 s a lap, card peak 8.4 GB). A lap's time is calibrated as T = 653 s + 0.0165 s × the width terms + 0.0037 s × 3·f·dw on three measured points.
- **Contacts.**
  - f 68 to 168 run as built.
  - A lap at f 128 projects to about 1,150 s.
- **Lane and face width.**
  - At twice the material they project to 1,570–1,780 s a lap.
  - Neither runs as built: the 128-wide lift needs about 66 KiB of shared memory against 48.
- **Card memory.** It stays near 8.5 GB of the 10.5 GB budget on every route.
- **Levels.** A v14 field can grow one level.
- **Sizing.** Growth is not sized in doublings (Brandon, 21:04, through theory): degrees of freedom add along a branch.

## 6. Laps 5 to 11, the score at equal laps, and the rule's threshold (November 11)

### 6.1 The line

[measurement; RTX 4080 SUPER under `.local/gpu.lock`; design's relays of November 11, 02:24 to 03:55 UTC; the locked code is the references' on HELD128 by one instrument for both lines] Both lines start from the same state (ct4). The plain line was stopped after its sixth lap; the part-rate line runs on.

| Lap from ct4 | Held joint, part rates | Held joint, plain | Locked code, part rates | Locked code, plain |
| --- | --- | --- | --- | --- |
| 4 | 1.7622 | 1.7838 | 0.5305 | 0.5534 |
| 5 | 1.7544 | 1.7751 | 0.5252 | 0.5491 |
| 6 | 1.7524 | 1.7748 | 0.5215 | 0.5455 |
| 7 | 1.7506 | | 0.5210 | |
| 8 | 1.7459 | | 0.5198 | |
| 9 | 1.7472 | | | |
| 10 | 1.7428 | | | |
| 11 | 1.7421 | | | |

- **Against the guess of November 10, at equal laps.** At the sixth lap the part rates are 0.0224 under on the held joint (guessed 0.03 or more: missed) and 0.0240 under on the locked code (guessed 0.02 or more: held). At the fourth lap the gaps were 0.0216 and 0.0229. The gap was made in the first four laps and has been level since.
- **[corrected 03:52 UTC] A score withdrawn.** At 02:57 and 02:59 theory scored lap 8 of the part-rate line against the plain line's last state and read 0.029 and 0.0257 under. That state is the plain line's sixth lap, so those figures compared eight laps with six. They are withdrawn.
- **Where the rates went.** By lap 8 every part was back at the floor 2^-12 except the lane's face biases, which reached it at lap 10. Laps 5 to 11 moved the held joint by −0.0078, −0.0020, −0.0019, −0.0047, +0.0014, −0.0044 and −0.0006.
- **The rise at lap 9** (+0.0014) is inside what a lap's reading moves by without a cause (about 0.003: theory's estimate, unmeasured). Ruled at 02:57: the line runs on, with a stop rule of a rise above 0.004 in one lap or two rises in a row, the eighth lap's state then standing as the best.

**G41** (fixed 02:57 UTC; laps 10 to 12 at the floor). The three laps together move the held joint by −0.003 (held from −0.008 to +0.002), and no lap rises more than 0.004. Within 0.002 of zero: at the floor the line has stalled and the lever is the law. −0.006 or under: the part rates left a slope that the floor rate follows. So far: −0.0044 and −0.0006; lap 12 is unread.

### 6.2 The cosine of two lap displacements, derived

[derived; checked by a simulation, `cos_rate.py`; atlas `deposition.lap-cosine-drift-over-noise`] Take one part with entries `x`. Over lap `t` the deposits displace it by `d_t = −η (g_t + ξ_t)`: `g_t` is the lap's mean covector at the lap's opening state, and `ξ_t` is what the lap's sections add around that mean, with zero mean, covariance `Σ`, and no relation between laps. Near the state the code is quadratic with curvature `H`, so `g_{t+1} = g_t + H d_t`. Then, to first order in the ratio of the two expectations,

```
E⟨d_t, d_{t+1}⟩ = η² ( |g|² − η (gᵀHg + tr HΣ) )
E|d_t|²        = η² ( |g|² + tr Σ )

c(η) = c_s − η H̄,     c_s = |g|² / (|g|² + tr Σ),     H̄ = (gᵀHg + tr HΣ) / (|g|² + tr Σ)

E[fall of the code over a lap] = (|g|² + tr Σ) ( η c_s − ½ η² H̄ )
```

- **`η` is the rate of the earlier lap of the pair.** The later lap's rate scales `d_{t+1}` and cancels in the cosine.
- **The expected fall is greatest at `η* = c_s / H̄`, which is where `c = 0`.** At `2η*` the expected fall is zero and `c = −c_s`. A part at rest (its mean drift gone, its state wandering under the lap's noise) reads `c = −ηH̄/2`.
- **What `c_s` is.** It is the drift's share of the displacement's power: the part's own ratio of what a lap repeats to what a lap scatters.
- **Hypotheses.** A quadratic code over two laps; lap noise unrelated between laps; many entries a part, so that the cosine sits near the ratio of the expectations; the other parts' motion entering only through `g` and `Σ`.
- **The check.** On a noisy quadratic of 400 entries (`c_s` 0.545, `H̄` 1.926, `η*` 0.283) the cosine reads −0.002 at `η*` and the fall is greatest there (171.6 against a predicted 171.7); at `0.2` the cosine reads 0.193 against a predicted 0.160, and at `0.6` the code rises (`cos_rate.log.txt`).

[measurement; the eleven `FIELD_PART_RATE` logs, `part_rate_cosines.txt`] The line's own cosines follow the form. For the lane's `enc`, `before` and `after`, with the earlier lap of each pair at octave `k` above the floor:

| Laps of the pair | 0, 1 | 1, 2 | 2, 3 | 3, 4 | 4, 5 | 5, 6 | 6, 7 | 7, 8 | 8, 9 to 10, 11 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Octave of the earlier lap | 0 | 3 | 4 | 5 | 4 | 3 | 2 | 1 | 0 |
| `c` (`enc`) | 0.68 | 0.60 | 0.45 | 0.19 | 0.17 | 0.19 | 0.21 | 0.31 | 0.29 to 0.33 |

- **The fall with the rate.** The first four cosines fall as the earlier lap's rate rises. Writing `h = h₀ 2^k`, the three differences give `h₀` of 0.012, 0.019 and 0.016.
- **The drift's share fell.** At the same octave 4 the cosine read 0.45 for laps 2 and 3 and 0.17 for laps 4 and 5: `c_s` went from about 0.70 to about 0.32 as the first laps took the part's coarse drift. It has held near 0.32 since.
- **What the 1/2 rule did.** It reads `c < 1/2` as too fast. By the law that holds only when `c_s < 1/2 + h`, which is true of every part whose drift is under half of its displacement's power, at any rate. The rule lowered the lane's three families from octave 5 to the floor over laps 4 to 8 while their cosines stayed between 0.17 and 0.33. With `c_s` 0.32 and `h₀` 0.016 their best octave is 4 (`2^k = c_s/h₀ = 20`), where the law puts `c` at 0.06.
- **Other parts.** The lane's `v` reads `h₀` near 0.08 and `c_s` near 0.38 (best octave 2). Its `out` reads `h₀` near 0.2 from one difference (octave 0 or 1). Its face biases are the least determined: few entries, an `ε` of 0.15, and differences that put `h₀` anywhere from 0.003 to 0.065; they open at octave 3. The new contacts' `W` is at rest (0 ± 0.07), and their `a` and `b` rows read 0.02 to 0.13 at the floor with `h₀` near 0.03 from one difference (octave 1). The lane's `a` and `b` columns read −0.16 to −0.30 and −0.04 to −0.24 at the floor: by the law they want less than the floor allows. That is noted and nothing is ordered on it, because a rate under 2^-12 changes the founding's own grain and needs a build.
- **[withdrawn]** Theory's reading of 02:57, that the cosine does not depend on the rate because drift and noise scale with it alike, left out the curvature term. A part at rest reads `−ηH̄/2`, which does depend on the rate.

### 6.3 The zero-seeking rule

[definition; theory, November 11 03:54 UTC; a host script between laps, no kernel and no trainer change] The rule moves each part toward the octave whose expected fall is greatest. With octave steps and `u = η/η*`, the fall goes as `2u − u²`, so an octave is the best of its neighbours when `2/3 ≤ u ≤ 4/3`. In terms of the cosine `ĉ` that the part would read at its present octave, and `h = h₀ 2^k`:

```
faster one octave   iff  ĉ >  h/2 + ε
slower one octave   iff  ĉ < −h/4 − ε     (never under the floor)
rest                otherwise
```

- **The reads.** From four saved states, `c′` and `c` are the last two cosines, whose earlier laps ran at octaves `k_a` and `k_b`. Where `k_a ≠ k_b`, `h₀ = (c′ − c)/(2^{k_b} − 2^{k_a})`, kept where positive and zero otherwise. At the present octave `k`, `ĉ = c + h₀ (2^{k_b} − 2^k)`.
- **The noise of a cosine.** `ε² = Σ_i d1_i² d2_i² / (|d1|² |d2|²)`, the variance of the cosine of two displacements with those magnitudes and unrelated signs.
- **Bits.** The rule changes what the state carries (the `parts` line), so it is a change of law, on the line it is tested on. Design built it as `part_rates.py trend` with every term an integer released at 2^-40 and a tie at the grain resting.
- **Against the lessons.** The octaves the test opens at are read from the line's own logs by the law above, one read, and the rule then moves them. No rate is tuned to a held reading: the rule reads displacements of the training state only.

[measurement; design's dry run on the states of laps 6 to 9, host only, 03:55 UTC] At the floor the rule reads the contacts' `a` and `b` rows faster (0.052 and 0.062 against `ε` 0.02) and their `W` at rest (−0.011); the lane's `enc`, `before` and `after` faster (0.30); `q`, `v`, `probe`, `out` and `moment_face` faster (0.12 to 0.31); `read` at rest (−0.046); the face biases faster (0.31 at octave 1, `ε` 0.15); and the lane's `a` and `b` columns at rest on the floor (−0.25 and −0.23).

**G43** (fixed 03:52 UTC, unread; the eleven logs and lap 10's held joint were read before fixing). Three laps from the ninth lap's state under the zero-seeking rule, beside laps 10 to 12 at the floor, opened at octaves 4 for the lane's `enc`, `before` and `after`, 3 for its face biases, 2 for its `v`, 1 for the contacts' `a` and `b` rows, and 0 elsewhere:
- (a) the cosines of `enc`, `before` and `after` read from two laps both at octave 4 are 0.06 (held from −0.05 to 0.15);
- (b) `v` from two laps at octave 2 reads 0.0 (±0.12), and the face biases from two laps at octave 3 read 0.2 (0.05 to 0.3);
- (c) the held joint at lap 12 is 0.004 under the floor line's (0.000 to 0.009), and no lap rises more than 0.004.

The rule that reads it: (a) at 0.2 or more means the cosine does not fall with the rate as the first four laps say, and the zero rule has no ground. (a) held retires the 1/2 rule for the zero rule on later lines. (c) alone decides nothing, because 0.004 is within two laps' noise. The carry's laps (G30′) keep the 1/2 rule, so that they are read beside laps 5 to 8, and they go first if their build is ready.

## Receipts

Device: RTX 4080 SUPER under `.local/gpu.lock`, the two arms' stages and the reads interleaved.

| Run | Projection | Deadline | Wall | Peak RSS |
| --- | --- | --- | --- | --- |
| rate laps rt1–rt4 | 1,214 s | 1,575 s (outer) | 1,116, 997, 1,105, 1,057 s | 0.82–0.83 GB |
| plain laps ct5–ct8 | 1,155 s | 1,520 s (outer) | 1,134, 1,136, 1,129, 1,120 s | 0.82–0.87 GB |
| references' reads | 120 s | 150 s | 111–119 s | 2.3–2.4 GB |
| open transmission (32 problems) | 190 s | 238 s | 185 s | 0.38 GB |
| octave read | 60 s | 75 s | 55 s | 0.57 GB |
| joint-field reads (G21) | 10 s | 12.5 s | 2.4 s each | — |
| rate laps rt5–rt11 (§6) | 1,214 s | 1,575 s (outer) | lap 7: 1,070 s; the others are in design's logs | not relayed |

The scripts are in `*_receipts/`, with the machine root replaced by `${HOLONICS_ROOT}`:
- `rate_lap.sh`, `chain_rate.sh` and `after_rate.sh`;
- `main_run2.sh`;
- `transmission.sh` and `transmission_open.sh`;
- `octave.sh`, `g21.sh` and `visit_held.sh`;
- `PROJECTION.rate.txt`.
- `part_rate_cosines.txt`: every part's cosine and octaves by lap, laps 1 to 11 (numbers only);
- `cos_rate.py` and `cos_rate.log.txt`: the check of §6.2 on a noisy quadratic (host, a second of one core);
- the guesses G41 and G43 as fixed, the scores and the correction, with their times, are in `guess_capacity_33_43.txt` in the receipts of [the two-surface record](2026-11-11_THE_HOST_AND_THE_CARD_ARE_ONE_SURFACE_WORK_IS_PLACED_BY_RATE_AND_WIDTH_THE_SURFACES_MEET_AT_CARRIES_AND_COST_IS_OWED_AT_MERGES.md).
