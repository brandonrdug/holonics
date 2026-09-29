# The tightened certificate: the factor families move, and the standings' fold costs the copy

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [measured] for the runs
(§3), each run once under the [pins](2026-09-29_THE_TIGHTENED_CERTIFICATE_PINNED_BEFORE_ITS_RUNS.md)
(`22bae4be`) at the build `dab65944`, and for the development diagnostic (§4); [proved-derived;
formal-checked] for the Lean statements (§2); [agent-inferred] for the choices named as such.

## 1. The lessons it answers

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **Failure 5, an uncertified step.** Both tightenings are proved bounds that replace looser ones
  (§2); each family keeps its own `ηC ≤ a` and `ηc ≤ 1`, and the storage growth stays certified at
  every commit. Every check held on every run. What the runs expose is a jump the certificate never
  covered: a standing crossing its fold (§4, the open #62 item).
- **Failure 9, a larger limit.** No limit moved: not `ηc ≤ 1`, the storage search, the entry bound
  or any run's bound. Each pinned run ran once within its bound. The diagnostic of §4 read only
  development seeds, and repeated no pinned run.
- **Lesson 3, a located cause repaired in its owner.** The loose bounds stood in `hnn::constitution`
  and `holon::deposition`, and are sharpened there. The new cause is located in the same owner (the
  standing's certificate) by measurement.
- **Failure 7, bits read as progress.** Text's training code is shorter by about 380 bits (§3). It
  is reported beside the families' motion, and it is not the loop's acceptance.
- **Failure 6, seen as unseen.** The moiré's six windows are its training windows: stability, not
  transfer.

## 2. The certificate

The pin's §1 states it, and the owner's module header states it whole ("The tightened
certificate"). In short:
- **The joint moves, not the count `B`.** Each family keeps its own curvature `C = ½·κ²·b`. The
  families together hold `½ (Σ η_ℓ m_ℓ)² ≤ Σ η_ℓ a_ℓ`, with `m_ℓ = √(κ²_ℓ b_ℓ)` at its dyadic
  ceiling: the cross terms are bounded by Cauchy–Schwarz on the joint ray.
- **The readout's spectral bound, not its Schur test.** `‖R‖₂` and its unit step's norm are read by
  their Gram certificate: exact inertia on the integer Gram of a dyadic face, plus the face's
  entrywise error.

The Lean statements are in `Holon/Deposition` §9, with `#print axioms` in `Framework/HolonObject`
(propext, Classical.choice and Quot.sound only):
- `joint_move_triangle`: `s‖Σ η_ℓ u_ℓ‖² ≤ s (Σ η_ℓ m_ℓ)²` for `η ≥ 0`, `‖u_ℓ‖ ≤ m_ℓ`;
- `joint_step_descends`: the joint certificate descends by `½ Σ η a`. It is proved through
  `certified_step_descends`, with the joint term apportioned to the families by their decreases,
  `C_ℓ = s (Σ η m)² a_ℓ / (η_ℓ Σ η a)`;
- `gram_certificate_bound` and `adjoint_gram_certificate_bound`: a certified `μ I − G ⪰ 0` on
  either side's Gram bounds the map;
- `entrywise_error_bound`: `‖E v‖² ≤ m n ε² ‖v‖²` for entries within `ε`.

## 3. The runs

Each process ran once, on the host, in release, sequentially, within its pinned bound. The cuts'
sha256 are `c6e51a35…0816` (the passage) and `39621d52…7fbc` (the standing cut).

**Acceptance 1 held on every run.** Every balance, pairing and commit closed. Every unreached locus
was unchanged at every deposit, and the committed energy bound held at every refinement's commit.
On the prediction field every learned map's largest entry stayed at most 8. The exposure's tick and
word balances closed.

**Text, training only (acceptance 2): passes.** One pass over the 385 choosing pairs, 25 deposits,
no generation and no validation read:

| Reading | The tightened certificate | The previous certificate (`05efc278`) |
|---|---|---|
| checks | 385 of 385 each; 25 of 25 unreached (175 loci) | the same |
| energy bound | 385 of 385 commits | 385 of 385 |
| factor families moved | **7 of 15**: every one of the 7 in the diamond | **3 of 15** |
| deposits that moved each | `f₀` 24, slices₀ 23, `q₀` 24, `q₁` 24, `c₀` 17, `b₀` 22, `F₀` 21 of 25 | `f₀` 12, `q₀` 19, `q₁` 17 of 25; slices₀, `c₀`, `b₀`, `F₀` none |
| `k` at `R` / `E` / `W_c` | `0` / `−16..−11` / `−13..−7` | `−2..0` / `−19..−14` / `−16..−11` |
| `k` at `f` / slices / `q₀` / `q₁` | `−12..−7` / `−15..−10` / `−9..−3` / `−13..−6` | `−17..−10` / `−19..−13` / `−13..−7` / `−17..−11` |
| `k` at `c` / `b` / `F` | `−18..−12` / `−15..−8` / `−15..−8` | `−23..−16` / `−19..−12` / `−19..−12` |
| largest entries | `R` 1787/1024, `c₀` 2049/2048, `f₀` 513/1024, `b₀`, `F₀` 1025/2048, `W_c` 23/2048, `q₀` 29/2048, `q₁` 13/1024 | `R` 1405/1024, `W_c` 1/2048, `q₀`, `q₁` 1/2048, the rest at founding |
| storage `ε_k` / product | `0..1/16` / in `[19/16, 20/16)` | `0` / 1 |
| training code, 12,320 stations | `96843 + 15/16 + ε` | `97224 + 1/16 + ε` |
| training releases at width zero | 23 (362 held) | 14 (371 held) |
| training, peak | 146,312 ms (projected 130,000–300,000), 681,570,304 bytes | 125,425 ms, 645,259,264 bytes |

- Each factor family's least and largest steps rose by `2³` to `2⁵`.
- The training code is shorter by more than `380 + 1/16` and less than `380 + 2/16` bits.
- The previous certificate's readings reproduce its own receipt (`97224 + 1/16 + ε`).
- Under the previous certificate `f₀` also moved, which its receipt, reading only the largest entry,
  did not see.

**The moiré and the copy (acceptance 4).**

| Run | Exact | Stations | Factor families moved | Largest `R`, `W_c` | `k`: `R` / `E` / `W_c` / factor families | `∏(1+ε_k)` | Training, peak |
|---|---|---|---|---|---|---|---|
| moiré `K = 4` | **5 of 6** (was 6 of 6) | 47 of 48 | 5 (`f₀`, `f₁`, `q₀`, `q₁`, `q₂`) | 7673/2048; 27/2048 | `0` / `−14..−12` / `−11..−7` / `−17..−7` | 1 | 114,530 ms, 498,520,064 bytes |
| moiré `K = 8` | 6 of 6 | 48 of 48 | 1 (`q₂`) | 7667/2048; 1/256 | `0..1` / `−16..−13` / `−12..−7` / `−18..−8` | 1 | 259,033 ms, 617,488,384 bytes |
| copy | **128 of 256** (was 256 of 256) | 1,749 of 2,048 | 6 (`f₀` 93, slices₀ 31, `q₀` 95, `q₁` 95, `b₀` 1, `F₀` 1 of 96) | 3879/1024; 147/2048 | `0` / `−11..−10` / `−8..−7` / `−15..−4` | 257/256 | 219,163 ms and 7,712 ms evaluation, 403,570,688 bytes |

- The moiré's unreached checks read 64 loci at `K = 4` and none at `K = 8` (the diamond covers the
  field).
- The copy released 235 of its 256 sections at width zero.
- Every run finished inside its projection.

The change is named in §4.

**The standing cut's held-out code (acceptance 3).** The residue chart on the host, 3,074 windows,
complete:

| Reading | `γ_U = 1` | The linear half | Both halves | The tightened certificate |
|---|---|---|---|---|
| held out, the field's face | `5459 + 13/16 + ε` | `5462 + 4/16 + ε` | `5472 + 3/16 + ε` | `5469 + 13/16 + ε` |
| held out, the tree alone | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` |
| held out, the field's part | `−17 + 10/16 + ε` | `−14 + 1/16 + ε` | `−5 + 15/16 + ε` | `−7 + 9/16 + ε` |
| development, the field's face | `13069 + 5/16 + ε` | `13068 + 7/16 + ε` | `13070 + 8/16 + ε` | `13069 + 2/16 + ε` |
| `Kt` | `19992 + 3/16 + ε` | `19991 + 12/16 + ε` | `19997 + 12/16 + ε` | `19993 + 15/16 + ε` |

The held-out code:
- is shorter than both halves' by more than `2 + 5/16` and less than `2 + 7/16` bits;
- is longer than the linear half's by more than `7 + 8/16` and less than `7 + 10/16`;
- is longer than the old step's by more than `9 + 15/16` and less than `10 + 1/16`.

The rest of the exposure:
- 9,222 tick balances and 3,074 word balances closed, with 6 aeon boundaries and 4 key locations;
- the certified steps: the factor families `2⁻³³..2¹³`, `W_c` `2⁻⁵..2¹³`, `E` `2⁻¹¹..2⁹`, `R`
  `2⁰..2²`;
- the storage growth: `ε_k` from 0 to `1/8` in one deposit, with the product over 3,072 deposits
  between `2¹⁹` and `2²⁰` (against `2⁸..2⁹`). Every growth is certified at its commit;
- 437,990 ms, below the projection's lower end of 480,000; peak 403,464,192 bytes.

## 4. The mechanism: the standings cross their fold

[measured; development seeds only] The copy's development read (seeds 11 and 12: 128 requests
trained, 32 read) and the moiré's (seeds 13 and 14: 512 windows at `K = 4`) were read under switches
in a scratch build of `22bae4be`. The switches undo one tightening or hold one family fixed; they
are never committed.

| Variant | Copy, development | Moiré `K = 4`, development |
|---|---|---|
| the tightened certificate | 16 of 32 (209 of 256 stations) | 4 of 6 (39 of 48) |
| the previous certificate (`05efc278`) | 32 of 32 | (not read) |
| the spectral readout only (the count `B` kept) | 32 of 32 | |
| the joint moves only (the Schur readout kept) | 32 of 32 | |
| **the standings held** | **32 of 32** (`W_c` still reaches 13/1024) | **6 of 6** (48 of 48) |
| the contrast ports held | 19 of 32 | |
| the passive factor held | 16 of 32 | |
| every factor family held (`W_c` free) | 32 of 32 | |
| only `R` and `E` step | 32 of 32 | |

Holding the standings alone restores both reads under the full tightened certificate. Holding `W_c`
or the passive factor does not.

The element reads a standing only through its sheet classes `σ_ρ(q) = sign(Δ_ρ)`, `Δ = L q`,
`sign 0 = +1` (Lean `HNN/Normal.{standing_deposit, sheetClass_locally_constant,
sheet_fold_witness}`), and the standings are founded at `q = 0`, on the fold.
- The standing's certificate holds in its lock chart, which reads the contrast's move as the
  classes' tangent.
- A step that carries some `Δ_ρ` across zero instead flips the slice's sign in the element: the
  operator jumps by `2A_ρ`, and no curvature bounds the jump (the open #62 item "the standing's
  fold").
- Under the previous certificate the standings stayed within one lattice unit of their founding on
  text (`1/2048`). Now `q₀` steps at `2⁻⁷..2⁻⁴` on the copy, both standings move at 95 of its 96
  deposits, and `q₀` reaches `29/2048` on text.

So the fold crossings are now frequent, and they cost the copy half its sections and the moiré at
`K = 4` one station.

## 5. Verdict

- **Every check holds on every run** (acceptance 1), and the certificate descends by its proved
  statements.
- **The factor families move** (acceptance 2 passes). On text all 7 factor families in the diamond
  move, against 3 under the previous certificate, with their steps raised by `2³` to `2⁵`. The storage
  bound stays enforced (product in `[19/16, 20/16)` on text).
- **The standing cut's held-out code** is `5469 + 13/16 + ε`: about `2 + 6/16` bits shorter than both
  halves' and still about 10 bits longer than the old step's.
- **The moiré holds at `K = 8`; at `K = 4` it reads 5 of 6, and the copy reads 128 of 256.** The
  change is named by measurement: the standings' fold crossings.
- **The next loop's subject is the standing's fold, in `hnn::constitution`.** [agent-inferred] The
  law it needs is that a standing's certified step stays in its sheet cell, `η |(L D)_ρ| ≤ |Δ_ρ|`
  wherever the move points toward zero, so that the lock chart's certificate holds on the whole ray.
  A class crossing is then a separate, discrete move: the score is compared at both classes, and the
  crossing is taken only where that comparison certifies it. Its acceptance is the copy's and the
  moiré's development reads, 32 of 32 and 6 of 6, under the tightened certificate with the standings
  stepping.

## 6. Owed in #62

"The tightened certificate" (September 29):
1. The inertia decision as a Lean statement. The elimination of `ratio::linear::inertia` is a chain
   of congruences, so `negative = 0` on `μ I − G` gives `μ I − G ⪰ 0` (Sylvester). The Gram
   certificate and the storage certificate both rest on it.
2. The joint halving's end. Whenever `s (Σ η m)² > Σ η a`, some family's halving gains
   `½ η (s m (2 Σ η m − ½ η m) − a) > 0`, and the halving ends (argued in `hnn::constitution`'s
   header).
3. The readout's composition into the gains: `‖R + ηD‖₂ ≤ ‖R‖₂ + η‖D‖₂`, each norm read by
   `gram_certificate_bound` and `entrywise_error_bound` on its face, composed into `κ²` over the
   stations. It joins the open composition over ticks.
4. The standing's fold (carried from the factor families' record, item 4), now measured:
   - the certified step's ray must stay in the sheet cell;
   - a class crossing needs its own comparison.

## 7. Gates

- `cargo check --workspace --all-targets` is clean.
- `cargo test -p holonics --lib`: 926 passed, including three new tests:
  - the spectral norm is certified and sharpens the Schur test;
  - the root ceiling bounds the root closely;
  - the joint certificate reads the moves, not the count.

  The every-family test now reads each family's own curvature and the joint certificate.
- The GPU suite, alone on the card under the lock: 32 passed in 44 s.
- `bash tools/lean_check.sh Holonics HolonicsResearch`: built, no `sorry`.
