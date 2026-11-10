# Founded parts at their own deposit rates gain 0.022 in four laps, and the field passes little past two letters

Status (2026-11-10): measurement. These are theory's orders of November 10, from 18:30 to 21:34, on the 64-contact lane field:
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

The scripts are in `*_receipts/`, with the machine root replaced by `${HOLONICS_ROOT}`:
- `rate_lap.sh`, `chain_rate.sh` and `after_rate.sh`;
- `main_run2.sh`;
- `transmission.sh` and `transmission_open.sh`;
- `octave.sh`, `g21.sh` and `visit_held.sh`;
- `PROJECTION.rate.txt`.
