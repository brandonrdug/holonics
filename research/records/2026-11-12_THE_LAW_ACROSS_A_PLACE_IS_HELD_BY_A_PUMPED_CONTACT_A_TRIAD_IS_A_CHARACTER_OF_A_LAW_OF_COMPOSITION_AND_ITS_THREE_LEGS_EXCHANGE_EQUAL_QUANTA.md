# The law across a place is held by a pumped contact: a triad is a character of a law of composition, and its three legs exchange equal quanta

November 12, 2026, from 09:40 UTC. The founding that G101's second branch sends the line to, for the
joint law of two letters each side. It recovers what the repository holds, derives the object (the
triad: a place's projection times its two strand mates'), its gauge, its founding and its build, and
fixes G102, the guess of the ruler that sizes it, before the ruler reads. The founding's own guess is
fixed after the ruler's read and the build's gates. Refs #404.

## 1. The question, in its region

[measured; the PC's reads]

- **The release** (G101, the first 32 held problems' 8,760 places). te2 less rt25: the keyed write
  −0.0215 nats a place, the settle's rest −0.0544, the re-draw's end +0.0015, the reference answers
  −0.0052. The circles' gain reaches the held passage and the settle and does not reach the write.
- **G91** placed the release's failure on the field's lack: the joint law of two letters each side.
- **The transmission at te2's mean** (`g99_te2_reads.txt`, the same 32 problems). Both sides, the
  field against the joint table on the same 32 problems (over all their places; the chain record's
  receipts, `both3.py`):

  | Letters each side | Places | The field | The joint table | The field lacks |
  |---|---|---|---|---|
  | 1 | 8,696 | 1.843 | 1.564 | 0.279 |
  | 2 | 8,632 | 1.170 | 0.569 | 0.601 |
  | 3 | 8,568 | 0.997 | 0.419 | 0.578 |
  | 4 | 8,504 | 0.957 | 0.397 | 0.560 |

  The uneven splits read (3,1) 1.318, (1,3) 1.366, (2,1) 1.458 and (1,2) 1.470 against the table's
  0.690, 0.714, 0.923 and 0.938.
- **The three-body part** (the leaky grip record 2.3, all 128 held problems, 43,470 places). At two
  letters each side the best reader built from pair terms alone, fitted on TRAIN, reads 1.030 and
  the joint table 0.576: 0.455 nats a place is the part no pair contact holds, at any rank. At one
  letter each side the same part is 0.478 (2.117 against 1.640).

So of the field's lack at two letters each side, 0.601 on the first 32, up to 0.455 is three-body law
that no pair contact holds (read on all 128); and the field's 1.170 stands over the pair reader's
1.030 as well, so it lacks pair law there too (a reading across two regions: the pair reader is
unread on the first 32 alone).

## 2. Recovered

- `code.pair-contact-conditional` (information): pair terms give `P(x|L,R) ∝ e^f(L,x) e^g(x,R)`;
  the quotient of functions on `L × x × R` by pair terms has dimension `(n_L−1)(B−1)(n_R−1)`;
  parity is its plainest case.
- The leaky grip record, section 3 and item 4.4: within a tick the plain contact gives an open place
  a left term plus a right term; a term in left, place and right together forms only across ticks.
  Item 4.4 names the two forms the machine may hold it in: a word of contacts through the place, or
  **a pumped contact**, whose relative phase no linear reading holds
  (`parametron.no-linear-relative-phase`). Item 4.3: at one tick no count of contacts holds the
  closure (the fitted pair reader is the one-tick form at unlimited rank).
- `winding.circulant-inertia` (geometry): a circulant is diagonalized by the characters
  `ω^(jk)`. `ns.triad-skew-cancellation` and `coupling.holonic-torus-flow-triads` (targets): a closed
  Fourier triad `p + q + k = 0` exchanges energy among its three legs and the exchanged faces
  cancel. `ns.calibrated-triadic-face`: the triad's face is bounded trilinearly. `ns.helicity-linking-form`:
  the pair form reads zero on the Borromean rings.
- `contact.carried-product`, `contact.carry-coupling-through-the-leak` (objects): the circles, the
  line's last founding; `tower.field-growth-by-contacts`: added columns founded at zero, so a grown
  field is the trained field bit for bit.
- The source (`crates/holonics/src/hnn/tower/field.rs`, `tick` and `tick_return`): the plain
  contact `c_e(t) = release(a_e(t) b_e(s(t)), FACE_BITS)` with `s(t)` the strand mate, `t − 1` at an
  even `e` and `t + 1` at an odd one, none past the region's ends; its reverse
  `δa_t = conj(b_s) δc_t`, `δb_s = conj(a_t) δc_t`, each released at the face's grain; the return
  `x_t ← x_t + release(W c_t + w_b 2^M, M)` on the material's grain `M`.

Nothing in the tree reads a place with both of its strand mates in one product: the carry's terms of
three sites lie on one side of the place (the record of raised rates, section 8.5).

## 3. The object: the triad

[derivation; agent-inferred] At a place `t` with both strand mates in the region, triad `k` is

```text
α(t) = A r̂(t) + α_b,   β(t) = B r̂(t) + β_b,   γ(t) = G r̂(t) + γ_b       (complex, one row pair a triad)
p_k(t) = release(α_k(t) β_k(t − 1), FACE_BITS)
c_k(t) = release(p_k(t) γ_k(t + 1), FACE_BITS)
x_t ← x_t + release(W c_t + W_T c^T_t + w_b 2^M, M)
```

with `r̂` the pair chart the plain contacts read (the read after the heads) and `c^T_t = 0` where a
mate is missing, at a region's two ends. One sum is released once: at `J = 0` triads the second
term is empty and every bit is as now.

It is one object read three ways.

1. **A word of two contacts through the place** (`cell.word-holonomy`): the left mate's contact with
   the place, then the place's with the right mate, composed at the place. Its phase is the sum of
   the three legs' phases.
2. **The mates' contact pumped by the place**: the pair contact between `t − 1` and `t + 1`, whose
   coupling is modulated by the place's own read. This is item 4.4's pumped contact, and the
   parametron's reading: the relative phase of the two mates is even under the half-turn and enters
   only through the pump (`parametron.no-linear-relative-phase`).
3. **The junction's three** (Brandon's lens of November 11, 22:27: a junction of `n` ends holds a
   three and one for each pair of ends): at a place and its two strand mates, the plain contacts
   are the pairs and the triad is the three.

Charts. Three-wave mixing (a pump, a signal and an idler; the parametron is its degenerate case);
the Navier–Stokes triad `k + p + q = 0`; Milnor's triple linking, where the Borromean rings have
every pair number zero and a triple number ±1.

### 3.1 A triad is a character of a law of composition

[proved-standard] On `ℤ/n`, write `χ_k(m) = ω^(km)`, `ω = e^(2πi/n)`. Then

```text
[x = L + R] = (1/n) Σ_k χ_k(x) χ̄_k(L) χ̄_k(R).
```

Each term is a complex triad `u_k(L) w_k(x) v_k(R)`, and the terms for `k` and `n − k` are
conjugate, so the real parts of `⌊n/2⌋ + 1` complex triads hold the law exactly. With `L` and `R`
fair and independent, `x` is independent of `L` alone and of `R` alone, so every pair term reads
nothing: the whole of the information sits in the three-body part. An abelian law of composition is
diagonalized by characters, and a character is a triad: this is why the triad is complex, why its
phase adds across its legs, and why pair contacts cannot hold the part.

[measured; host, a drawn law] The ruler `cap_t.py` (section 5) on `x = L + R mod 8`, six left and six
right contexts, a fifth of the letters redrawn (floor 0.8043 nats): no triads 1.7858, one 1.2764, two
0.8518, four 0.7952, eight 0.7957 (`cap_t_synth.log.txt`). Four triads hold it whole.

Text is not a group, and its three-body part is not a character sum of small rank. How much of it a
count of triads holds is the ruler's question (section 5).

### 3.2 The kernel: the legs exchange equal quanta

[proved-derived] The return `W_T c^T` is unchanged under

```text
(α_k, β_k, γ_k) → (λ α_k, μ β_k, ν γ_k),   λ, μ, ν ∈ ℂˣ,   with the return's columns w_k read through (λ μ ν)⁻¹,
```

where `α_k` is triad `k`'s two rows of `A` with their biases and `w_k` its two columns of `W_T`.
Releases aside, each triad has six real directions of gauge that no receiver distinguishes; U4 counts
a complex triad's `3·(2D + 2) + 2D = 518` entries (at `D = 64`) as 512 net of them. Differentiating
the invariance at the identity gives, for any loss `ℓ` read through the return,

```text
Re⟨α_k, ∇_α ℓ⟩ = Re⟨β_k, ∇_β ℓ⟩ = Re⟨γ_k, ∇_γ ℓ⟩ = Re⟨w_k, ∇_w ℓ⟩
```

and, from the phase rotations, the same equality of each leg's turn. So under a step at equal rates `r` the
differences `‖α_k‖² − ‖w_k‖²`, `‖β_k‖² − ‖w_k‖²` and `‖γ_k‖² − ‖w_k‖²` are conserved to first order:
each leg gains the same squared norm, the Manley–Rowe relation of three-wave mixing (each wave gains
or loses the same count of quanta). At unequal rates the conserved quantity is `‖α_k‖²/r_α − ‖w_k‖²/r_w`:
one leg grows faster than the others for no reason in the law. [ruling] The triad's parts train at
one rate.

Founded with `W_T = 0`, the conserved difference is the drawn rows' own norm, so under a step at one
rate, as `w_k` opens, the three legs open with it, each by what `w_k` gains. At founding only `W_T`
moves at first order (`∇_α ℓ = 0` while `W_T = 0`), as the growth by contacts' new columns do.

[derivation; agent-inferred, November 12, from the learner's source] The field's learner does not
step at one rate an entry. It deposits `((m ≪ grain) ≫ rate)/(⌊√v⌋ + 1)` (`deposit_step` in
`hnn/tower.rs`, the field's learner in `hnn/tower/field.rs`), so entry `i` steps at `2^(−rate)/s_i`
with `s_i = ⌊√v_i⌋ + 1`, and the form a step keeps at first order is `Σ_i s_i θ_i²` over a leg's
entries less the same over `w_k`'s. The first moment's lag enters only at second order: each past
covector pairs equally with the state it was read at, and the state has moved since by a few steps,
each of the rate's order. The divisors do not stand. The legs' second moments open at the pair
drives' and decay at `2^(−8)` a step while their covectors are zero, and they then follow their own
covectors' squares. So over a lap the learner keeps no form of the legs' norms. Its step does not
keep the differences of plain squared norms either, so equal gains of the legs are not a prediction
for it. What the gauge still gives the learner at every state is the scale identity on its
covectors: the four families' covectors pair equally with their own values. The six real directions
of each triad's gauge are travel that no receiver reads, as a lane's scale is (`state_travel.py
scale`). The part's one octave stands: the divisors are each entry's own, read from what reached it,
where an octave between the legs would be a rate set by hand.

### 3.3 Which triad

Two forms were weighed.

- (i) **The plain mates' triad**, above: three new charts and a return, 518 entries a complex triad.
- (ii) **The circles' triad**, `T(t) = a(t) Qm_left(t) Qm_right(t)`: the place's chart times the two
  circles' arriving carries, look-back about ten places at te2; a new chart and return only, 258
  entries, with `Q` shared with each circle's own face.

[derivation; agent-inferred] (i) is chosen. Within a tick the heads run before the contacts
(`tick`: the heads, `out` added to `x`, the read `r̂`, then the contacts), so each mate's read
already carries its near field at the first tick: the plain triad meets the second ring across the
place, letters `−2` and `+2`, in one tick and without the circles. It is the junction's own three,
the plain contact's form with one operand more (its card realization follows the plain contact's
kernel, with no scan), and it leaves the circles' line one law. (ii) stays a later founding if the
triad's reach reads short at three to five letters each side.

## 4. The founding and its build

[definition; agent-inferred]

- **Declaration.** A count `J` of complex triads, a word of the declaration's head line, never a run
  switch: `J = 0` writes `hnn-field-v14` or `hnn-field-v14e` exactly as now; `J > 0` writes
  `hnn-field-v14f` with `J` after `C`.
- **Layout**, after every other family and present only where `J > 0`: `triad`, `6J` rows of `D` on
  the material's grain (rows `0..2J` are `A`, `2J..4J` are `B`, `4J..6J` are `G`; within each, row `k`
  the real part and row `J + k` the imaginary part of triad `k`); `triad_bias`, `6J` on the face's
  grain; `w_triad`, `D × 2J` on the material's grain, the return, with no bias of its own.
- **Founding** (`grow-triad-field`): `A`, `B` and `G` drawn as the growth by contacts draws `a` and
  `b` (uniform on `±√(3/D)` on the material's grain), the biases and `W_T` at zero. The grown field
  is the trained field bit for bit. The learner's moments open as a growth in contacts opens a new
  contact's: the first at zero, the second at the mean of the counterparts' old second moments (`A`,
  `B` and `G` at the pair drives', the biases at the drives' biases', `W_T` at `W`'s). So a triad's
  first step is its covector over its counterpart's scale, the step a trained entry takes, and never
  the largest normalized step of a fresh entry [agent-inferred, from the growth in contacts' law].
- **Parts.** One part, `triad`: the three charts, their biases and the return, appended after the
  parts the line has and written only where `J > 0`. A part is a family of entries that steps at
  one rate, and the gauge (section 3.2) makes the triad's charts and return one such family, so the
  one rate holds by the part and needs no rule beside it.
- **At `J = 0`** every line the build prints is the line as now: the parts lines and the section
  parts print the parts the field writes, so a reproduction compares like with like.
- **Reverse**, by the product rule through the producing operands, each product released at the
  face's grain as the plain contact's are: with `u = δc_k(t) = (W_Tᵀ δx_t)_k`,

  ```text
  δγ_k(t + 1) = conj(p_k(t)) u,   δp = conj(γ_k(t + 1)) u,
  δα_k(t) = conj(β_k(t − 1)) δp,   δβ_k(t − 1) = conj(α_k(t)) δp,
  ```

  `Σ_t δx_t c^T_tᵀ` into `W_T`; the three charts' covectors into `A`, `B`, `G` and their biases, and
  their transposed reads into the read's covector beside the plain contacts' and the circles'. Each
  site's `β` is read by one place (the one after it) and its `γ` by one (the one before), so each
  covector is one term, and the reverse has no order to choose.
- **The card** realizes the forward per site beside the plain contact and the reverse by the same
  rule, the return's two blocks summed whole before its release; host against card parity first.
- **Tests of the law** beside the field's: at `J = 0` the head line, the layout and every face as
  now; a grown field reads every face of its source bit for bit; the quarter-turn gauge
  `(α_k, β_k) → (i α_k, −i β_k)`, exact on integers, leaves every face bit for bit; the reverse
  against the code's change along a direction, as the contacts' and the circles' tests read it; no
  triad and no covector at a region's two ends.
- **The line.** The build enters the line by reproducing it: one lap at `J = 0` from the line's last
  saved state, whose section lines, timings aside, and states equal the line's own lap's. Then the
  triads are founded on the circle line's newest end and trained beside the circle line's own lap on
  the same sections. G103 names them: the build reproduces te4's lap from te3's end with no triads,
  the triads are founded on te4's end, and the founding's first lap pairs with te5.

What it could repeat, checked against the lessons: no authored routine (the triad's charts are
located by deposition from the passage); no cache (a triad is a contact, a store charged by the flux
reaching it and read through a port; it holds no table and shares every projection across places);
no width as a dial (`J` from the ruler's partition or the plain contacts' count, in fours); nothing
modality-specific (a place between two strand mates is the same in a row of an image, a frame of
sound or a joint of a motor chain); no located cause carried unrepaired (the circles' failure at the
write is not the triad's subject; the release's lack of the joint law is).

## 5. The ruler and G102

[definition] The ruler `cap_t.py` (receipts) is the pair tables of `cap_g.py` plus `R` complex
triads with free factors over the contexts,

```text
Q(x | L, R) ∝ exp(a(L, x) + b(x, R) + Σ_j Re(u_j(L) w_j(x) v_j(R))),
```

fitted together by conditional likelihood on TRAIN from `cap_g.py`'s start and schedule, read on
HELD128 at the contexts seen in TRAIN, the best held step taken. At `R = 0` it is `cap_g.py` step
for step, its own reproduction. With free factors over the two-letter contexts it reads what `R`
one-tick triads can hold of the law at two letters each side; the field's triads read the mates'
near field through the heads, which reach farther, and through learned charts, which hold less. The share `s(R) = (1.0304 − h(R))/(1.0304 − 0.5758)`
is the fraction of the three-body part held.

[guess, fixed before the read; the guess file] G102: `s` = 0.13, 0.20, 0.28 and 0.37 at 8, 16, 32
and 64 triads, the gain a doubling roughly level, from the shape of the circles' ruler (G81), with
nothing yet read of this part's spectrum. The rule sizes the founding: `s(64)` under 0.15 sends the
next loop to form (ii) or the word across ticks, with no triad founded by count (the chord record's
section 3, item 2); a doubling whose gain falls under half the one before binds a partition, and `J`
is the count before it; otherwise `J = 16`, the plain contacts' count toward each mate, and the
founding's own laps size what follows, as G83 did for the circles.

[measurement; the guess file, G102 scored] The ruler read 1.0304 nats a place with no triad, then
0.7559, 0.6916, 0.6550 and 0.6317 at 8, 16, 32 and 64 triads, so `s` = 0.604, 0.745, 0.826 and 0.877.
Every share stood over its guessed range, and the gain a doubling fell (0.141, 0.081 and 0.051) where
the guess had it level. The part left over, `1 − s`, falls to 0.64 to 0.71 of itself a doubling,
about `R^(−0.56)`: at two letters each side a few characters hold most of the three-body part, as
section 3.1 says a law of composition is held (the drawn law by its four). From 16 triads on, the
free factors fit TRAIN past what holds, so each share is its count's best held read; the 8 triads
were still falling when their budget ended. No doubling's gain fell under half the one before
(0.081 against 0.071, then 0.051 against 0.040), so the rule's third branch fires: **`J = 16`**,
8,288 entries.

## 6. Navigators, terrain, kernel, cokernel, landmarks

The navigators are the place and its two strand mates, each a chart of its read; the terrain is the
passage. The kernel is section 3.2's gauge and, at a rank `J`, every difference of three-body law
the `J` characters do not see; the cokernel is the three-body part left over, read by the ruler as
`1 − s(J)` of 0.455 at two letters each side. A landmark is a place where the three legs' phases
lock, so that `arg α + arg β + arg γ` stands still across the places that share a closure.

## 7. What does not transfer

- Phase matching in crystals, nonlinear media and pump depletion: only the trilinear form, its
  gauge and its equal exchange are taken.
- The Navier–Stokes cascade: only that a closed triad exchanges among its legs.
- Milnor's invariant as computed: nothing in the machine computes a link invariant.
- Characters as an authored basis: no Fourier basis is given to the field; its triads are located,
  and the cyclic law is the ruler's control only.
- The ruler. Its free factors over contexts are a table on the host, an instrument that measures
  what triads could hold, never machinery.

## 8. Owed

- The build (section 4) at `J = 16` with its parity, the reproduction lap, the founding's guess and
  its first lap: done (PRs #701 and #702; G105, section 9).
- Lean, for #410: the character decomposition of the cyclic law (3.1), and the triad's gauge
  identity with its conserved differences under a step at equal rates (3.2, written with the build
  as `HNN/TriadGauge`; its box ticked from the PC).
- The check of the built object (G107, section 9) and the founding it sends the line to.

## 9. The first lap (G105) and the check of the built object (G107)

November 12, 12:15 to 12:51 UTC. tt1 is one lap from TT0 (te4's end with the triads founded and
`W_T` at zero), at eight times on the triad part and the base on every other part, on te5's
sections. It was read at its lap mean beside te5's. G105 was fixed before it trained and scored after,
misses included, in the guess file.

- The held joint stands 0.0025 nats a place under te5's over the held passage's 43,470 places, where
  the derivation put 0.006. By quarter of open sites the gain is none in quarter 1 and 0.003 in each
  of quarters 2 to 4. The derivation put the most in quarter 2 and the least in quarter 4.
- The transmission rows cover the first 32 held problems' 8,760 places, sorted by how many written
  letters stand within two places of the open place.
  - With none or one, the gain is 0.001 to 0.002.
  - With two, it is the most: 0.0080 with both mates alone written (both sides at d = 1), 0.0071 with
    two on the left, and 0.0076 for the split (2,1).
  - With more, it is less: 0.0056, 0.0027 and 0.0029 for both sides at d = 2, 3 and 4.
- The return's charge, `W_T`'s rms over the plain contacts' columns of `W`, is 0.060. The circles'
  first raised lap (tp1) was charged to 0.0615 and bought about twice as much a unit of charge (0.078
  against 0.042 nats a place).

[measurement; the reading agent-inferred] The triads hold a law of the place and two written
letters near it. Across the place it is the object of section 3. On one side it acts through each
mate's read of its own near field (3.3). Its increment falls where more letters are written, since
the field's other parts hold the near law there. At both sides d = 2 the field lacks 0.556 nats a
place against the joint table, and the triads bought 0.0056 of it, about a hundredth. So no second
lap trains on this founding. A first reading, at 12:45, was that the legs read context rather than
letters. It was withdrawn at 12:51, before any further read, because the rows with none or one near
letter count against it.

G107, fixed before its read, checks whether that law is the triads' own. It cuts the return `W_T`
from tt1's lap mean, and the triad build reads the cut state as it read tt1's, row by row.
- If the rows with two near letters rise at least two and a half times as much as the rows with one
  (the guess is four), and both mates' row rises at least 0.004, then the object is the theory's and
  its reach is short. The circles' triad (ii) is the next founding, by a derivation fixed first.
- If they rise less than one and a half times as much, or both mates' row under 0.002, then the
  legs are given their mates' letters before any founding.

## Receipts

In [`…_receipts/`](2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT_A_TRIAD_IS_A_CHARACTER_OF_A_LAW_OF_COMPOSITION_AND_ITS_THREE_LEGS_EXCHANGE_EQUAL_QUANTA_receipts/README.md):
`cap_t.py`, its control `cap_t_synth.log.txt`, its gradient check `cap_t_fd.py` and
`cap_t_fd.log.txt`, and G102's six runs `cap_t_2_0.log.txt` to `cap_t_2_64.log.txt` and
`cap_t_2_0_repeat.log.txt`; the build's gates `g105_triad_gates.txt`, `g105_te4r_lines.txt`,
`g105_te4_reads_bin_triad.txt` and `g105_grow_triad.txt`; tt1's `g105_tt1_dev.txt`,
`g105_tt1_lines.txt` and `g105_tt1_reads.txt`, with the charge's ruler `charge_t.py`. G102 and
G105, fixed and scored, and G106 and G107, fixed, are in `guess_capacity_44_55.txt` in the receipts of
[the record of the places](2026-11-11_THE_PLACES_THE_FIELD_GIVES_PUSH_AGAINST_THE_PLACES_IT_MISSES_THE_DEPOSIT_IS_THEIR_DIFFERENCE_AND_TWO_BUILDS_ARE_TIMED_ONLY_INSIDE_ONE_HOLD_OF_THE_CARD.md).
