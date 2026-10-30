# The pair contact is raced before its split founds where the body grows

Refs #404 #408. Status: [the race's contact law and its acceptance fixed before the race; the split's design
and acceptance fixed before its build, its host built and the card equal to it on the RTX 4080 SUPER
(§7), its certificate priced after the first measurement (§4); agent-inferred, October 30].
Claude (opus), design lead. Read beside
[the radix record §2](2026-10-29_A_VALUE_IS_A_RADIX_MOVE_THE_FREE_ENERGY_IS_THE_CODE_THAT_FOUNDS_AND_POLARITY_IS_THE_ONE_REVERSIBLE_NEGATION.md#2-the-boundary-free-energy-is-the-two-part-code-and-it-founds-prunes-and-recharts),
which states the split this record builds toward, and
[the body's growth](2026-10-29_THE_BODY_GROWS_BY_COPIES_WHOSE_PARTS_SUM_TO_WHAT_IT_LEARNED_SO_IT_RESTARTS_WIDER_ON_THE_SAME_FACES.md).
Computational object: the helical pair interaction, here the pair contact between two drives read
off the same face. Of the winding guide's six objects it touches the pair (the contact); the helix,
faces and placement, cell holonomy, tube and tower thread stay as the tower has them. Owners it
joins: `ContactLaw::Pair` (`hnn::tower`), the class race's routes (`tower_classes`), the card's
parity (`tower_pass parity … pair`).

## 1. Why the race's contact law is measured first

[agent-inferred, October 30] The radix record's split is a founding of the pair contact
`v = (W_a r̂ + b_a) ⊙ (W_b r̂ + b_b)`: two copies carrying half the return each, perturbed by
`±ε(u, w)`, found the coordinate `φ_t = (uᵀ r̂_t)(wᵀ r̂_t)`, with score `g_e = uᵀ M_e w`,
`M_e = Σ_t δv_(e,t) r̂_t r̂_tᵀ`. A rectifying contact has no such form: its second derivative lives
on its kink. Every race since October 27 runs rectifying contacts, so the split has no law to grow on
in the race until the pair contact holds its place there. The pair contact has been carried by the
host and the card since October 24 and has never been raced at the race's declaration.

The comparison is clean by construction. The pair contact's second drive opens at zero material and
unit bias and draws no key (`Tower::found_on`), so a four-level pair tower founded on the race's
keys has the rectifying four-level tower's encoding, modes, reads and first drives draw for draw,
and its contacts open one-sided, `v = W_a r̂ + b_a`: the rectifier without its kink. The control is
the four-level tower of October 27 (46 laps on the RTX 4080 SUPER), whose keys are a byte prefix of
the race's (the packets record §7).

## 2. The route

`train-two-ladder-pair-tower-classes` is `train-two-ladder-tower-classes` with every contact the
pair contact (`tower_classes::train_pair_realized`); its card parity is
`tower_pass parity … pair`, the four-level declaration founded with pair contacts. Nothing else
differs.

## 3. Acceptance, fixed before the race

1. **The card is the host.** `tower_pass parity` at the race's four-level declaration with `pair`
   (width 64, modes 128, contacts 256, four levels, 24 streams, 32 sections of 128), every face,
   gradient entry and learner equal.
2. **The race.** One hour on the card, the same passage, keys, width, modes, contacts, levels,
   streams, section and rate as the four-level tower. The claim: the mean of its held-out readings
   over its hour's last five laps is no higher than the rectifying tower's mean over the same laps.
   A single lap is not the claim: both towers' readings rise for one lap by up to 0.02 (the
   rectifier at laps 25 and 34). Each lap's card time is reported beside the bits, and the readings
   at the quarter marks.
3. Short of the claim, the pair contact does not carry the race at this declaration; the split waits
   on a contact law it can grow on, and the next item in the order (the `{−1, 0, 1}` collapse,
   radix record §3) goes first.

## 4. The founded split, designed before it is built

[agent-inferred, October 30] The radix record's split founds a coordinate, and a founding needs a
coordinate the passage does not yet reach. The body holds one for every contact when its contact
field is widened by two: each contact's drives and biases repeated (contact `o` and its copy
`o + f`, copy-major as the growth map lays copies), its return column split into two parts that sum
to it. That is the growth map restricted to the contact family, so the face is the old face exactly.
The two copies read the same drives and take the same covector, up to the return split's one-unit
remainder, so their difference is a coordinate with `a = 0`: dormant, and free by the code (radix
record §2, `ΔF = 0`). The split founds that difference. The capacity is spent once; which
differences are founded, and when, is the code's decision, section by section. Pruning a founded
pair back to its mean and growing the field again when no dormant pair is left are the reverse test
and the growth map, owed after this build.

**The copies' moments.** Each copy's drive row and bias take half the old covector (their return is
`c/2`), so they carry `m/2` and `v/4`; each return part takes the old covector whole, so it carries
`m` and `v`. Every copy opens on the old normalized step.

**The direction, carried and turned.** Each dormant pair carries a unit direction `v_e` on the read
`r̂` it shares (width `d` entries on `2^(−16)`), opened at the contact's own first drive row,
normalized. Each section turns it by one product, `v_e ← M_e v_e / ‖M_e v_e‖`, with
`M_e = Σ_t δv_(e,t) r̂_t r̂_tᵀ` and `δv_e` the pair's covector at its product (the two copies'
covectors summed: the old contact's). `M_e` is symmetric, so its top singular pair is its
eigenvector of largest `|λ|`, with `u = w = v_e` and the sign carried by the score. The product is
one outer sum in the reverse's tiles, `Σ_t (δv_(e,t) y_(e,t)) r̂_t` with `y = v_eᵀ r̂`, beside the
contact's own `Σ_t δa r̂_t`.

**The test, on the section after the direction was turned.** The direction a section tests was
formed from the sections before it, so the score carries no selection: under a passage the tower
already codes, it is a sum with mean zero. With `φ_t = y_t²`:

```text
g = Σ_t δv_t φ_t                 (bits per unit of θ; nats are ln 2 · g)
σ = ln²2 · Σ_t (δv_t φ_t)²       (the score's sampled Fisher in nats, the square of the covector already formed)
τ = d²/4                         (θ = ε_a ε_b, each a component of a contact row founded with variance 2/d)
K                                (the dormant pairs at the section)
found  ⇔  (ln 2 · g)² / (τ + σ) > ln(1 + σ/τ) + 2 ln K
```

The price has two parts: the coordinate's own code, `½ ln(1 + σ/τ)`, and its address, `ln K`.
The machine chooses which of `K` dormant pairs to found, so the interior's description names that
pair, and the two-part code charges the choice. Without the address, a body of 1,536 dormant pairs
would test each against the single-coordinate price and found by chance wherever one of them
crossed it (agent-inferred, October 30, found while writing the test of acceptance 3).

`σ` is the empirical Fisher of the score: the read's own Fisher along the contact is not formed,
because the contact's output reaches the read through every level above it, and the score's squares
estimate it without bias under the tower's own face. `ln 2` and `ln(1 + σ/τ)` are exact enclosures
(`ratio::algebraic::ln_enclosure`); a pair founds only when the enclosures separate, so a tie is
refused, as the test refuses chance. The second drive opens at zero material, so its row has no
founded scale of its own; it is the first drive's family opened at its center, and its components
take the first drive's variance (agent-inferred).

**The split's map.** A founded pair opens its coordinate at the posterior mean,
`θ̂ = −ln 2 · g / (τ + σ)`, with `ε = √|θ̂|` on the material's grain:

```text
W_a[o] += ε v,  W_a[o+f] −= ε v,   W_b[o] += sgn(θ̂) ε v,  W_b[o+f] −= sgn(θ̂) ε v
⇒  ½c(a + δa)(b + δb) + ½c(a − δa)(b − δb) = c(ab + θ̂ φ)
```

The face moves by `c θ̂ φ`, second order in `ε` and downhill by the score, with a predicted fit
change of `−(ln 2 · g)²/(2(τ + σ))` nats. A founded pair carries no direction afterwards: its copies
are two contacts learning on their own.

**The certificate pays the price, on the line the reread measured** (agent-inferred, October 30,
after the first measurement, §7). The test above only proposes; the reread decides. After the
section's step deposits, the deposited tower with the founded split is read again over the section.
That reading is the section's exact code at `θ̂`, so with `g` the line's slope at zero, its change
`Δ` fixes the curvature the line actually has, `H = 2(Δ − g θ̂)/θ̂²`, where `σ` was only the
squares' estimate. The split deposits only if the code falls by more than the coordinate's Laplace
price, `(½ τ θ² + ½ ln(1 + σ′/τ) + ln K)/ln 2` bits with `σ′ = max(σ, ln 2 · H, 0)` (the larger
reading; the price grows with it). A bare "fewer bits" would admit a coordinate that lowers the code
by less than its own description. Refused, and when the measured line is bounded below under the
prior (`τ + ln 2 · H > 0`), its mode `θ* = −ln 2 · g/(τ + ln 2 · H)` is read once more under the
same price. Only a section where a pair founds pays these readings.

**One founding a section**: of the pairs the test admits, the one with the largest surplus of fit
over price. The address `ln K` already charges the choice. Several founded together share the face,
their predictions do not add, and one reread cannot read their lines apart (measured: §7).

**On the card.** The reverse forms, per level and dormant pair, `y = v·r̂`, the score's sum and its
squares, and the turned sum. The host decides the founding and maps the split, as it decides the
step; the card's material is the host's after each deposit. Realized (agent-inferred, October 30):
`tower_reverse_contacts` keeps each contact's covector `δv` at its product beside its drives' when
the split read is asked, and `tower_split_read`, one block a dormant pair of a level, reads every
stream's cells a chunk of the block at a time (one thread a cell for `y`, `φ`, the score term and
the turned weight `δv y`; then the turned sum's outputs in `256/W` groups of the chunk's cells).
A score term at or past `2^48` is refused on both sides: below it, the squares of fewer than `2^31`
cells sum in 128 bits, so neither side's carrier decides.

## 5. Acceptance of the split, fixed before the build

1. **Same face.** On the host, the contact field widened by two reads the old faces class by class
   over a passage, and the learner's moments are lifted as stated, on rectifying-free towers with
   pair contacts; a tower with participation or a passage, whose joins also drive the first drive,
   is refused until their lift is stated.
2. **The direction turns to the top.** On a tiny tower, turned repeatedly on one fixed section,
   the carried direction becomes a fixed point of the turn (up to its sign, within a few units of
   its grain), and its score `vᵀM v` is at least as large in magnitude as that of the opening
   direction and of every basis direction.
3. **The test refuses where no news reaches the pair.** A pair whose covectors are zero over the
   section (a face that equals every target at its grain) or that the passage does not reach founds
   nothing and keeps its direction. On a passage whose targets are scrambled against what the tower
   reads, the foundings a section admits are reported beside the count of tests: a reading, since
   the two-part code is a Laplace evidence and admits chance at a rate its price sets, not none.
4. **The founding is predicted.** On a tiny tower over a mixed passage, every pair the test founds
   is reported with its predicted fit change and the reread's measured change; the claim is that
   the certificate admits more foundings than it refuses, and every admitted one lowers the code.
5. **The card is the host.** The card's score, squares and turned sums equal the host's at the
   race's declaration with paired pair contacts, in the parity, every entry.
6. **The race.** Only if the pair race's claim (§3) holds: one hour of the four-level pair tower
   widened to paired contacts, founding active, beside one hour of the same tower with founding
   refused (the copies dormant throughout; it also measures what the doubled return alone does).
   The claim: the founding race's mean held-out reading over its last five laps is below the
   dormant race's over the same laps. Each lap's card time is reported, and the founding count per
   level.

## 6. The recorded failures these choices could repeat

- *Bits read as progress*: the claim is fixed against the control founded on the same draws, at the
  same laps, over five laps rather than one.
- *A located cause carried unrepaired into a new consumer*: the split is not built onto a contact
  law the race has not measured.
- *A design thought in the programming language*: the contact is the pair interaction of two drives
  on one face, the helical pair's contact, not a gating unit added for capacity.
- *A refusal answered with a larger limit*: the race keeps the hour and the lap rule.
- *An uncertified deposition step*: a founding deposits only through the section's reread.
- *Seen material graded as unseen*: the direction a section tests was turned on the sections before
  it, so the score is not selected on the data it is read on.
- *An authored routine standing in for learning*: the split's place, direction and size come from
  the passage's own covectors through the code; nothing names where the body should grow.

## 7. Receipts

**§3 acceptance 1, the pair contact on the card** (October 30, RTX 4080 SUPER, head `3b7b15869`, alone
on the card). `tower_pass parity` at the race's four-level declaration with `pair`, 24 streams, 32
sections of 128: 98,304 faces, 12,718,112 gradient entries and every learner equal, none unequal.
Host 14,042 ms, card 4,729 ms (181 forwards in 3,743 ms, 64 reverses in 413 ms); wall 24.1 s against a
600 s deadline, peak resident set 1,580,380 KiB. Acceptance 1 holds.

**The split on the host** (October 30, the cloud container's host, unit tests only; no learning run).
`cargo test -p holonics --lib hnn::tower::split`: 4 of 4 pass.

- Acceptance 1: the tiny pair tower, ungated, gated, and gated with turned modes, widened by two,
  reads the old faces and keeps the old state over the 40-class passage; drive entries carry `m/2`,
  `v/4`, return parts `m`, `v`; the rectifier and the linear foil are refused; the directions'
  text form reads back.
- Acceptance 2: after 64 turns on one section every direction is a fixed point of the turn within
  4 units of `2^(−16)` up to its sign, and its score is no smaller than the opening direction's or
  any basis direction's, at every level and pair.
- Acceptance 3: a zero score founds nothing and keeps the direction. A score of 4 bits against
  squares of 4 founds alone and is refused among two dormant pairs (the address).
- Acceptance 4, read on a passage of four streams whose low bit is the parity of the two high bits
  before it (the conjunction a single quadratic direction carries), the tiny pair tower taught 8
  sections, then paired for 24: one section proposed a founding. Its test predicted the code would
  fall 8.58 bits; the reread at `θ̂ = −0.957` measured a fall of 0.79, under the coordinate's price,
  and the line's mode `θ* ≈ −0.43` measured a rise of 0.10. Refused, 1 of 1. Before the price and the
  single founding, the same section had founded three pairs predicted to lower the code by 20.9 bits
  together; their reread raised it by 1.44, and the bare certificate refused them. Founded alone, the
  best of the three lowered it by 0.79, which the bare certificate admitted.

What it measured: the squares' curvature and the slope at zero do not describe the line at this
tower's scale. The measured line is not the test's quadratic (both readings lie off any parabola
through zero with slope `g`). The tiny tower's prior precision is `τ = 4`, so `θ̂` is near one and the
founding is far from the local regime; at the race's width 64, `τ = 1,024`. The claim of
acceptance 4 (the certificate admits more than it refuses) is not met on this passage.

**§5 acceptance 5, the split on the card** (October 30, RTX 4080 SUPER, head `e9e6ce65c`, alone on the
card). `tower_pass parity … split` at the race's four-level declaration with paired pair contacts
(512 contacts, 1,024 dormant copies), 24 streams, 32 sections of 128, host and card learners founding
in lockstep: 98,304 faces, 19,075,104 gradient entries and every learner equal; on every section the
split reads (score, squares, turned sums), the foundings and the carried directions equal, none
unequal; 5 foundings admitted over the 32 sections. The card formed the split read in 1,024 blocks
(one per dormant pair of a level) of 256 threads. Host 22,826 ms, card 7,666 ms (265 forwards in
5,740 ms, 64 reverses in 620 ms); wall 43.8 s against a 600 s deadline, peak resident set
2,020,612 KiB. The build reported no `nvcc` or `ptxas` error. Acceptance 5 holds. The race
(acceptance 6) is owed, only if §3's claim holds.
