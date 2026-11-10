# Point re-draws rest at the faces' own entropy, and the faces already hold what the ring, reach and pair censuses add

Status (2026-11-10): measurement and decision. This record covers the night's reads of the November 6 face field
(hnn-field-v14) at lap 26 (width 32), and the lane field grown from it (width 64, laps 27–32).
- The code is on `claude/exchange-walk`, from e9efbed13 to d5b0bb2dd, and is now on the line.
- Everything ran on the RTX 4080 SUPER under `.local/gpu.lock`.
- Numbers only: the released passages and the references stay under `.local/`.

Refs #73, #406.

## 1. The moves navigate each answer region to a neutral rest

Each region starts from the keyed locks given held's lengths. Two moves then work on it:
- an **exchange** moves letters between places and keeps the letter counts;
- a **re-draw** changes a place's letter to its face's top letter, so the counts drift. It is proposed where a place's surprise
  over its face entropy, `v = c_t(x_t) − H(f_t)`, exceeds a nat, the largest first, and only where the bare price
  `ln f(top) − ln f(x_t)` is at least a nat.

Every pass is certified (`Field::certified_passes`):
- one re-read keeps the claims whose attributed fall passes `h = 1` nat;
- the kept set's whole fall must then pass `h` times the kept count;
- the weaker half is undone until it holds.

A region stops at neutrality, where its code is at or under its faces' summed entropy, or at rest, where a whole cycle of passes
keeps nothing.

[measurement] Code in nats a letter on held, under the field's own faces:

| State | Problems | Locks | Exchanges to rest | Then re-draws | Entropy at the end | Stops |
| --- | --- | --- | --- | --- | --- | --- |
| lap 26 | 0–31 | 2.140 | 1.369 | not run | 1.112 | all 32 at rest |
| lap 26 | 0–127 | 2.188 | 1.277 | 0.966 | 1.005 | 119 neutral, 9 at rest |
| lap 32 (lane) | 0–31 | 1.946 | 1.198 | 0.755 | 0.768 | 25 neutral, 7 at rest |
| reference, lap 26 | 0–31 | 0.565 | (given) | (given) | 0.578 | neutral |

- The exchanges alone are slow when one move stands per pass. The certified walk at one move a pass (`cert26b`) had 19 of 32
  regions at rest after 5,690 s. The parallel settle brought all 32 to rest in 370 s.
- On lap 26's held 0–31, the 128-problem run's re-draws end at 0.942. Lap 32's end at 0.755 on the same problems, with lower
  entropy.
- The released passages are still local soup at both laps: words and brackets shaped like Python, with no working lines. This is
  read by eye, not counted.
- The rest and the reference are both neutral points of the same faces. The reference sits about 0.4 nats a letter lower, and the
  certified single-place moves do not travel from one to the other.

## 2. Where the excess sits at rest

[measurement; the state charge census, `charge-field`, lap 26, held 0–31] Each state is read locked, every face once with its
place alone open.
- The excess is the code less the summed face entropy.
- The root charge is `Σ_a N(a) ln(N(a) / Σ_t f_t(a))`.
- The last column is the share of the places with `v > 1` that sit in runs of three or more.

| State | Code | Entropy | Excess | Root charge (share of excess) | `v > 1` | `v > 2` | In runs of 3+ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| the exchanges' rest | 1.369 | 1.112 | 2,255 nats | 812 (0.36) | 0.180 | 0.111 | 0.19 |
| the keyed locks | 2.140 | 1.307 | 7,297 nats | 897 (0.12) | 0.303 | 0.215 | 0.31 |
| the reference | 0.565 | 0.578 | −117 nats | 532 | 0.066 | 0.042 | 0.25 |

At rest the excess is mostly isolated wrong letters: 871 of the 1,581 places with `v > 1` stand alone. The point re-draws act
on exactly these, which is why they reach neutrality.

## 3. The ring census and the ring tilts

[measurement; `ring-census-field`, lap 26, every place locked] The census reads five ring residues of the reference's letters
before each place: backticks mod 2, `(` less `)` mod 3, `[` less `]` mod 3, and double and single quotes mod 2.

For each ring, U is what the residue adds to the face, in nats a letter: `Σ N ln(N/F)` over (residue, letter), less the same
with the residue pooled. It is printed beside its plug-in bias. That bias is estimated by Miller–Madow: the number of nonzero
cells, less the residue cells and the letter cells, plus one, over twice the places.

| Ring | held (43,342 places) | TRAIN even (454,234) | TRAIN odd (460,982) |
| --- | --- | --- | --- |
| backtick | +0.0005 | +0.0000 | +0.0000 |
| `( )` | +0.0058 | +0.0073 | +0.0070 |
| `[ ]` | +0.0029 | +0.0030 | +0.0030 |
| double quote | +0.0007 | +0.0008 | +0.0007 |
| single quote | +0.0006 | +0.0040 | +0.0039 |

- The faces already carry the fence and quote parities. The bracket and paren depths are the largest residues, still under
  0.008 nats a letter.
- **The spread census (`ring26s`, every 6th problem across TRAIN) is incomplete.** It hit its 2,550 s deadline with no tables
  (rc 124). Its projection counted batches of 32 problems at the first sample's 15 s. The spread's batches carry about 10,000
  places against 4,000–5,000, at 1.1–2.3 ms a place, and a host build contended for six minutes. It was not relaunched.
- The ring tilts (`redraw-ring-field`) tilt every face by `ln(N/F)` of its ring residues, pooling TRAIN's two sets and dropping
  cells under 2,000 sites. The re-draws then ran on lap 26's held 0–31. The tilts were taken from the first-sample census
  (labelled `ringtilt26f`).

  | Read on held 0–31 | Tilted | Untilted (the 128-problem run) |
  | --- | --- | --- |
  | `[ ]` counts balanced | 15 | 13 |
  | `( )` counts balanced | 11 | 12 |
  | backticks even | 26 | 25 |
  | double quotes even | 18 | 18 |
  | single quotes even | 18 | 18 |

  Both release at the faces' entropy, and the closure counts are within noise. The two codes are read under different faces, so
  they are not compared.

## 4. The reach censuses

[measurement; `reach-census-field`, lap 26, every other place locked] At each answer place `t` and each offset `d`, the census
takes the letter at `t + d` (question letters and the void included) against the letter at `t`. It reports U less its bias, in
nats a letter, as in §3.

| Offset | held (43,342) | TRAIN even (675,553) | TRAIN odd (668,383) |
| --- | --- | --- | --- |
| ±1 | +0.027 | +0.014 | +0.015 |
| ±2 | +0.020 | +0.011 | +0.011 |
| ±4 | +0.012 | +0.0065 | +0.0065 |
| ±8 | +0.004 | +0.0024 | +0.0024 |
| ±16 | −0.001 | +0.0003 | +0.0003 |
| ±64 and beyond | about −0.005 | about −0.0012 | about −0.0012 |

The faces read nearly all that any single far letter says about the letter. The rest sits within four letters. The small
negative tail shows the bias estimate correcting too far where cells are sparse: about 0.001 on TRAIN, and 0.005 on held.

[measurement; `reach2-field`, the same offsets on census 2b's charge set, the lap's own partly open states] On TRAIN even and
odd the far letter adds about 0.005 nats a letter within two letters, and about 0.002 flat out to ±256. Held reads about 0.03 at
every offset. That held value is not trusted: 128 problems let a far letter partly name its problem, a clustering the bias
estimate does not see.

## 5. The pair read

[measurement; `pair-field`, lap 26] For each letter of at least 2,000 sites in TRAIN even's phase census, the read takes two
clouds over the readout chart (width 32):
- the count cloud, `μ_N = LN/n`, `Σ_N = QN/n − μ_N μ_Nᵀ`;
- the face cloud, `μ_F = LF/F`, `Σ_F = QF/F − μ_F μ_Fᵀ`.

The faces are tilted by `exp(s · tilt)`, with `tilt = ln N(r; μ_N, Σ_N) − ln N(r; μ_F, Σ_F) + ln(n/F)`. That gives 77 letters,
none singular.

| Step `s` | TRAIN odd code (775,197 sites) | Change | Held joint (own) |
| --- | --- | --- | --- |
| 0 | 2.868 | — | 1.892 |
| 1/4 | 3.587 | +0.719 | 3.562 |
| 1/2 | 4.337 | +1.469 | 5.735 |
| 1 | 5.672 | +2.804 | 9.969 |

- The tilt moves every face far off.
- No unit or sign error was found in the forms: `pair_form` and `pair_tilted` were traced, and the host test passes.
- agent-inferred: the 32-wide chart's quadratic forms swing over tens of nats, so second-order clouds are not a density ratio
  the faces can take. Their constants alone reach 3.3 bits.

[decision; d5b0bb2dd] The first run (`pair26`) never reached its check: check_ref stopped at its 900 s deadline (rc 124) inside
the tilts. `pair_tilts` inverted each width-32 covariance by Gauss–Jordan over `BigRational`, which reduces a gcd at every term.
- Each cloud is now carried as the integral matrix `S = wQ − LLᵀ = w²Σ`.
- One fraction-free elimination reads both what the tilt needs: `Σ⁻¹ = w² adj S / det S`, and
  `log det Σ = log det S − 2·dw·log w`.
- The elimination is the library's own. `ExactRatMatrix::inverse`'s Montante–Bareiss loop is factored into
  `fraction_free_gauss_jordan`, and its new reader `holonics::ratio::linear::integral_adjugate` returns `adj A` and `det A`.
- Measured: 24 s on four host threads, with the letters' constants unchanged bit for bit.

## 6. The lane laps

[measurement] The lane field grows width 32 to 64 with `lanes = 2` and trains under `lane2.sh`'s law, without the bare clock.
Every value below is read with the bare clock, as the plain held joint (`FIELD_JOINT_NATS` own, nats a place, 43,470 places):

| Lap | 26 | 27 | 28 | 29 | 30 | 31 | 32 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| lane, width 64 | 1.8923 | 1.8820 | 1.8697 | 1.8598 | 1.8545 | 1.8468 | 1.8453 |
| change | | −0.0102 | −0.0123 | −0.0099 | −0.0053 | −0.0076 | −0.0016 |
| width 32, no lane (control) | 1.8923 | 1.8970 | 1.8937 | | | | |

The width, not the clock, moves the plateau, and the descent is slowing. Laps 33–43 run in one-lap segments, each followed by
its reads (`lane_lap.sh`).

## 7. What this decides

[decision; agent-inferred]
- **No census-derived tilt enters the line.** The faces are read with the rest of the reference locked. They then carry nearly
  all that the ring residues (at most 0.008 nats a letter), the letters at any offset (at most 0.015) and the chart's
  second-order clouds can add.
- **The gap is not in the faces' reading of a given context.** It lies between the neutral rest the moves reach (0.75–0.97
  nats a letter) and the reference's neutral point on the same faces (0.565). Neither the moves nor the tilts carry a region
  from one to the other.
- Lessons this keeps:
  - code under the field's own faces is not progress: the released passages are still soup at 0.755;
  - the spread ring census was reported incomplete and not relaunched with a larger deadline;
  - the pair read's stall was repaired in the library's owner, not with a second elimination.

## Receipts

Device: RTX 4080 SUPER under `.local/gpu.lock`. Host threads: as each script declares (8 for the card reads; the tilts' timing
ran on 4). A "guard" is a defect bound, not a projection: those runs stop at rest or neutrality.

| Run | Projection | Deadline | Wall | Measured / projected | Peak RSS |
| --- | --- | --- | --- | --- | --- |
| settle, 128 held (`redraw26_128`) | guard | guard | 3,503 s | — | 2.52 GB |
| re-draws, 128 held | guard | guard | 539 s | — | 2.35 GB |
| charge census (`charge26b`) | 105 s | 131 s | 46 s | 0.44 | 0.77 GB |
| ring census, spread (`ring26s`) | 2,040 s | 2,550 s | 2,550 s, rc 124 (incomplete) | ≥ 1.25 | 2.80 GB |
| ring tilts (`ringtilt26f`) | guard | guard | 143 s | — | 0.78 GB |
| reach, held | — | 300 s | 113 s | — | 1.03 GB |
| reach, TRAIN even | 1,600 s | 2,000 s | 1,764 s | 1.10 | 2.88 GB |
| reach, TRAIN odd | 1,600 s | 2,000 s | 1,699 s | 1.06 | 2.45 GB |
| reach on 2b's charge set | 1,161 s | 1,451 s | 231 s | 0.20 | 0.74 GB |
| pair read, first (`pair26`) | 1,151 s | check 900 s | 900 s, rc 124 (incomplete) | — | 0.47 GB |
| pair read (`pair26b`) | 1,151 s | 1,438 s | 589 s | 0.51 | 0.76 GB |
| lane lap 32 | 1,700 s (bound) | 2,060 s | 1,123 s | 0.66 | 0.85 GB |
| lap 32's settle and re-draws | guard | guard | 421 s and 184 s | — | 0.74 and 0.77 GB |

Scripts are in `*_receipts/`, with the machine root replaced by `${HOLONICS_ROOT}`:
- the run scripts: `ring.sh`, `reach.sh`, `reach2.sh`, `pair.sh`, `redraw.sh`, `ringtilt.sh`, `charge.sh` and `lane_lap.sh`;
- the reading scripts: `reach_bias.py` (U beside its bias) and `ringclose.py` (the closure counts).
