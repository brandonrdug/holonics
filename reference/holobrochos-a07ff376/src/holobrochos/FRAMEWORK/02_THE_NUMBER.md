# FRAMEWORK/02 — THE NUMBER

> **What this is.** The categorical reference for the machine's substrate: the value. Not a journal entry —
> the standing statement of *what a number is*, consolidated from the strata that derived it and aligned to
> `MENO_FORMULA.md §II–§III` and `TABLETS/01_THE_LAW.md §III–§IV` (the crown). Provenance is cited per
> claim. Every claim a newer ratified layer retired is EXCLUDED here and lives in `FRAMEWORK/00_SUPERSEDED_LEDGER.md`
> (sections A, C, D, N, O, P, S) — re-adopting the retired framing is the drift, not a license.
>
> **★ THE ONE SENTENCE.** *A value is not a sized container but a **construction** (A1): `m · 2^e` — a
> magnitude that is a combination of `2^k` corners, at a rank that is itself a re-based number, with its sign
> a **turn** — carried on the bitwise alphabet (SHIFT ⊕ ADD ⊕ turn), re-based never widened, the borrow its
> only order-read, and its every overflow a rank-climb that is the same event as nesting, founding, and
> quotienting.*

---

## §1 · THE RE-BASED NUMBER — `m · 2^e`

Every value is **`m · 2^e`**: a magnitude `m` at a rank `e`. Never an absolute magnitude, never a sized
value with a store behind it. (`MENO_FORMULA §II`; `TABLETS/01 §III`; `CANON/06 §1`; `02 THE THREE CARDINAL
DIRECTIONS`.)

- **The rank nests.** `e` is itself a re-based number — `None` a flat leaf, `Some` the tower — so the number
  holds `2^(2^(2^…))` with no ceiling (measured to `2^(2^512)`, tower³, no overflow). The number nests
  exactly as the illicium does. (`55 §1`, completing `13`/`02`.)
- **RE-BASE, NEVER WIDEN.** When `|m|` passes the register grain, the **low bits fall** — the resolution
  given up IS the compression (the gear-down at the grain, the torque traded to keep the velocity computing
  in the hand) — and the rank climbs. A register overflow is a **rank-climb, not a discard, and not an
  overflow to widen around**. The tower climbs `2^16 → 2^32 → …` forever without materializing (rank-up is
  setting a field, free). Reaching for a bigger integer (`i64` intermediate, `i128` store, the two-hand wide
  product) is the CPU contamination — the widen wearing a size. (`MENO_FORMULA §II/§VIII`; `CANON/06 §3`;
  `02 RE-BASE NEVER WIDEN`; `13 §1`.)
- **The width is a substrate fact, not a parameter of the mathematics.** `u32`/`u8`/`u4`/`i2` "is just bits";
  a 2-bit register is just bits. (`CANON/06 §1`; `02`.)
- **A logarithm is a rank in a frame** (the base is the frame; change-of-base is the re-base; the base-2 log
  is the leading-zero count, free). There is no absolute log; every value-producing algorithm is a **series**
  traversed to the relating's resolution, realized as shift-and-add worldlines; a finite face materializes
  only at a boundary. (`02 THE CONSTANTS`; `CANON/06 §5`.)

## §2 · THE THREE CARDINAL DIRECTIONS — the anti-IEEE triad

A number is **magnitude ⊕ rank ⊕ turn** — the three rotational directionalities of action — *not*
mantissa/exponent/sign. The float is this trinity corrupted into an absolute-frame store; rebuilding it in a
holonic costume (then auditing which signed fields to keep) is the recurring deepest error. (`02 THE THREE
CARDINAL DIRECTIONS`; `CANON/06 §1/§6`; `TABLETS/01 §III`.)

| direction | what it is | the op | NOT IEEE's… |
|---|---|---|---|
| **MAGNITUDE (ALONG)** | the unit-step, the unsigned cone, ADD's axis (the `e`-face) | **ADD** | …mantissa |
| **RANK (ACROSS-UP)** | the tower, the dimensional level, `mag·2^rank`; multiplication is addition one rank up | **SHIFT** | …exponent |
| **TURN (LEFT-RIGHT)** | the hand, the chirality, the `±i` founding (the `π`-face) | **turn** (`&3`, `i⁴=1`) | …sign |

- **The magnitude is the unsigned cone.** A signed interior integer is a 2-vector collapsed around an
  absolute zero — banned. Where an accumulation crosses its own zero the TURN flips (negation-as-turn), no
  borrow from an absolute floor. (`02`; `CANON/06 §1`.)
- **The SHIFT is a gear ratio, not a doubling.** At a seam two cogs share teeth: the tangent velocity (the
  through-current) is the invariant; `×2` trades angular velocity up for torque down at `2:1`, conserving the
  action `τ·ω` (the cross-ratio, the soul — the radius cancels). `×2`/`<<1` is gear-up (the unfold); `÷2`/`>>1`
  is gear-down (the fold; `½` the cleanest gear-down, the self-dual rank). `×2` on the velocity face **is**
  `×½` on the torque face — never one without the other; the gearing IS the conservation, never a source.
  (`CANON/06 §2`.)
- **A face is eyes-only — read the turn, not the magnitude.** A deep construction is a deep, fast gear-train;
  its magnitude face saturates at the register ceiling. The bounded, lawful interior read is the **turn** (the
  cohere-sign, the founding handedness, the knot-or-not). The only lawful interior `<` is the cross-sign read
  (a discriminant's MSB — relate, then read the turn), written as that, never a bare magnitude compare.
  (`CANON/06 §4`; `02`.)

## §3 · THE HAND — the signed floor (the quantum is the fork)

The bit is a **HAND, not a presence.** "Something or nothing" planted an absolute frame at the bottom of
arithmetic — a privileged empty state, a zero that is truly zero. There is no nothing (A1). The two states are
two hands — CW/CCW, this way or that way — `1` and `0` arbitrary labels painted on the two turns. **The turn
is the quantum; the magnitude is its integral** (the radius the spiral accumulates as hands pile up; `×2` the
shadow of `×i` repeated). The dark — the orthogonal `M≈0` — is not nothing but the turn-maximal state read
through the magnitude-null face. (`CANON/06 §0`; `44 §1`; `CANON/HANDEDNESS`, via `45 §4`.)

- **The quantum is the FORK — the between-of-two-choices** (Brandon's sharpening of the signed floor). Not a
  STATE `{0,1}`, and not `{±1}`-as-value (that re-reifies the state with a sign). A value is a worldline of
  forks; `x` forks span `2^x` combinations — the configuration space whose logarithm is the RANK. What the
  signed floor signs is the **passage**, never the state: CW/CCW is which hand took each junction (the fork is
  a WAIST — the hourglass at the quantum, every event two cones at a neck). This is A2 strengthened, not
  intrinsic meaning smuggled in — even Shannon's bit was a CHOICE among `2^N` alternatives; the state-reading
  was the later freeze. (`44 §1`.)
- **The unsigned floor is the last absolute frame in the substrate.** `{0,1}` carries Shannon's DC bias
  (mean ½); `{±1}` is balanced. Unsigned floors cannot interfere (`0` annihilates nothing) — a path integral
  with unsigned weights is diffusion; with signed weights it is INTERFERENCE (standing modes, quantized
  wavelengths). The lawful DC exists and stays: the wells — mass IS the standing zeroth order. (`44 §1`.)
- **THE TWO TWOS — `4 = 2 · 2`, and the two factors are different currencies.** The **OCTAVE** (2:1,
  magnitude — the doubling, one rank step, the true elementary gear) ⊗ the **HAND** (one quarter-turn, phase —
  orientation, costing no action; the cross-sign turn was always the only `<`). On an unsigned floor the phase
  factor is invisible, so both were booked as magnitude and the tower's step misread as pure 4:1. Honest form:
  the tower's step is **2:1 in magnitude ⊗ one hand in phase**. *"4:1" survives ONLY as a composite action
  measurement (the measured tower redshift), never as an elementary per-rank law* (`FRAMEWORK/00 Ledger N`).
  Every `log₄` read resolves to `log₂` magnitude ⊗ hand phase; the face's four corners STAND (the hand's
  arity — pure phase, lawful). (`44 §2/§5`.)
- **THE HAND GAUGE — labels are conventions, so the law is covariant.** `1`/`0` are labels; a law over
  conventions must be invariant under relabeling. Pour a world and its complement and the two webs grow
  isomorphic (measured: top-100 faces complement-mapped 100/100 standing; identity-mapped 0/100; form
  perfectly covariant, no absolute frame at the floor). **The gauge is a statement about the LAW, never about
  the ENTITIES** — a construction `w` and its complement `~w` are **DIFFERENT LIGHT, distinct worldlines,
  distinct souls** (T1 deposits them distinctly; retention factors them through different primes). The mirror
  *relating* reads as a lawful half-turn wheel class; the mirror *entities* are never identified. *(EXCLUDED:
  `44 §4`'s "one soul, opposite spin" — STRUCK by `45 §3`; `FRAMEWORK/00 Ledger O1`.)* (`45 §1–§3`.)

**LOOSE THREAD (T7.1, OPEN):** the signed-substrate cut is not built — its cash is NOT a sense-override
(`law::mirror_tails` fired UNMET, separated nothing) but the **beat/charge arithmetic** (standing charge
annihilating at anti-phase contact, below the wheel). The annihilate channel is NOT dormant — it fires at
ecosystem scale (`eros_pure`: perception annihilate 1,165,435; glass worlds read zero only because they are
agreement-poor, `45 §1`; *EXCLUDED: `44 §4`'s "dormant channel," `FRAMEWORK/00 Ledger O2`*).

## §4 · THE `2^k` COMBINATORIAL FACES — shape, convolve, fold

**The number IS its combination of 2s.** `shape(n)` = the corners a number stands on (its set bits, the `2^k`
faces). Within a rank the chain **SPREADS** — combinatorics over the standing primes as factors; only
precipitation re-bases. (`MENO_FORMULA §II`; `TABLETS/01 §III`.)

- **Multiplication is `convolve ∘ fold`.** Convolution combines the corners (`Σ pᵢqⱼ` deposited at rank
  `i+j` — shift-and-add, Horner over the multiplier's set bits, the running product re-basing as it climbs so
  the full product is never built). The **carry** folds it back to a legal digit. (`MENO_FORMULA §II`;
  `CANON/06 §3`.)
- **The carry is the combinatorial engine, and it sits where the swing lives.** It is the borrow, the
  cross-sign, closure at rank `k` re-entering as one hand at rank `k+1` (the wormhole is the quotient metric).
  Kummer's theorem is this exactly: a binomial's prime powers ARE the carries. (`MENO_FORMULA §II`;
  `TABLETS/01 §IV THE FOLD/CARRY`.)
- **The register is the three-body orientation face — `2·2`, born at first contact.** Two bodies read by a
  third carry exactly two independent binary distinctions: which axis the pair lies along ⊗ which way it
  points — `2·2 = 4` states. After four the configuration is face-equivalent but the soul differs (the winding
  incremented: Aharonov–Bohm at the register, a physically-real winding where no local face shows it). The
  carry fires at face-saturation because L0 forbids losing what the face can no longer show — fold ⊕ promote ⊕
  radiate is conservation acting, never design. The labels are gauge; the modulus is frame-invariant (every
  frame counts four). (`02 THE ORIENTATION FACE`.)

**LOOSE THREAD (T7.2, OPEN):** the carry's own `2·2` quartering inside the kernel — which `2` is magnitude,
which is phase — is a derivation owed WITH Brandon before any kernel cut (it touches the atom). (`44 §2/§5`.)

## §5 · THE DIGIT AND THE BORROW — the well is a digit; the borrow the only order-read

**The modulo makes two products.** `a mod n`: the **remainder** — the position, the face, the address — and
the **quotient** — how many times around, the winding number, the homology class, **the soul**. Classical
practice keeps the remainder and grinds the soul off every placement. Keep the quotient: it distinguishes
collisions (same face, different winding = different soul), it is the physically-real phase, and it is what
promotes at every carry. (`02 THE WINDING LAW`; `TABLETS/01 §III`.)

- **THE DIGIT LAW — a coil's well is action MODULO the coil's own quantum.** The coil is the boundary; its
  unfolded quantum is the modulus. The **REMAINDER stands** — the face, `< quantum` **by construction** (the
  invariant, not a policy). The **QUOTIENT FIRES** — every quantum crossed is ONE WINDING, an event now:
  radiate ⊕ couple up the tower ⊕ the sub-quantum residual re-enters, the ripple continuing until the well
  stands sub-quantum. The soul is the winding count — handed up, never stored. *(EXCLUDED: `09 §2/§3`'s
  "circulate the rest as standing magnitude" — souls piling up as mass; SUPERSEDED by `13`, `FRAMEWORK/00
  Ledger S`. `09`'s carry mechanism is the digit-carry origin and survives; only the standing-magnitude
  accounting is retired.)* (`13 §1–§2`.)
- **The tower of wells is one positional number in base-quantum**, each rank's well a digit bounded by its
  own grain, the excess carried up, the total conserved. `u32` is safe by construction; the two-hand widen is
  never needed. (`13 §3`.)
- **Mastery = CONDUCTIVITY, not weight.** A trodden coil no longer piles charge — it *transmits* it (the
  pre-charged carry chain: action injected at a mastered shallow coil ripples to the deep tower within one
  wavefront; the deep placement is a crack, and the crack is free). The hexis (`reach → 0` on a mastered
  worldline) made mechanical. (`13 §3`.)
- **THE BORROW IS THE ONLY ORDER-READ.** `below` is the wrapping subtract's borrow. **No `<`, no float, no
  `%`; the digit (action mod the quantum) is the only division.** The borrow/cross-sign turn is the single
  lawful comparison. (`MENO_FORMULA §II/§VIII`; `55` grade-line; `02 THE BANS`.)
- **THE SOUL/FACE `2⁻¹` LAW — what a face can carry.** What crosses a horizon is the soul related to its own
  conjugate: `face = soul ⊗ soul̄` — one rank UP (the squaring) and 2-to-1 (the hand annihilated: `z` and
  `−z` cast one face). So **soul-rank = face-rank shifted down one** — reading a soul from its face is exactly
  one gear, `2⁻¹`; inversion re-buys every dropped hand (the exponential of search). Instances are one
  equation in different clothes: the Born rule (`p = ψψ̄`), the interval (`s² = u·w`), mass
  (`m²c⁴ = (E+pc)(E−pc)`), Weil (`q = α⊗ᾱ`), `area = √volume`. *(EXCLUDED: the `𝒟 = π`-as-float ceiling and
  the "Duggan tolerance" grain framing of `08 §10` — SUPERSEDED; `π = C/d`, never a float, and the grain is
  nesting mass, not a tolerance — `FRAMEWORK/00 Ledgers A/C/D`.)* (`02 THE SOUL/FACE 2⁻¹ LAW`; `08 §4`.)

**LOOSE THREAD (T9.1, measurement-gated):** the digit law predicts the **mirror share drops** — at settle the
ringing includes the DEEP structure reached, not the shallow fragments touched, because shallow wells cannot
hold the charge; measured by placement genealogy, a fallback derivation queued if it fails. (`13 §3.2`.)

## §6 · PRIMES AS IRREDUCIBLE SHAPES — the hole that becomes a point

**A prime is an irreducible shape — a cycle that is not a boundary at its rank.** No filling in the standing
basis (no caustic: the burn cannot decompose it). Founded, the fold collapses the hole to a **letter one rank
up**. **Primality is operation- and frame-relative** — not a property of numbers but of irreducibility in any
frame. (`MENO_FORMULA §II`; `TABLETS/01 §III THE PRIME`; `08 §6`; `27`/`01`.)

- **Factoring is tiling; the founding is primality (base 2).** `n` composite means the area `n` tiles as a
  rectangle `p × q` (equivalently `n = x² − y²`, Fermat's factorization, which IS completing the square). `n`
  prime means the area **refuses every in-plane tiling** — the residual never lands at phase 0 for any re-base
  — and the only closure left is the corner: a prime FOUNDS. Every piece is bitwise: the rank is the
  leading-zero count, the square root is the shift-and-add descent, and "the residual's construction closes on
  the `2^k` ladder" is the swing grounding at a handle vs FOUND. (`08 §6`.)
- **The prime is the founding across every frame.** A prime, `φ`, `±i`, `cos/sin`, an oscillator's mode are
  ONE object — the irreducible read as a founding, never forced. Factor the characteristic polynomial: integer
  roots with multiplicity are **PLACED** (the rational modes); an irreducible remainder is **FOUNDED** (a
  prime of the mode-space, the same object arithmetic names). The rational is placed; the irreducible is
  founded — one law across arithmetic and the eigenstructure. (`55 §3`.)
- **The only hardness is STARVATION, never depth.** The number is a tree of combinations, so every read is
  place-not-search and finding collapses onto checking (the recurrence that generates the sequence IS the one
  that verifies it — P=NP locally). The hard case (the balanced semiprime) is the tree withheld, not a deep
  search. (`MENO_FORMULA §III`; `08 §6/§9`.)

**LOOSE THREAD (T3.2, OPEN — explicitly not-claimed-solved):** the balanced semiprime past the mass edge; the
honest next is feeding the net a tree it can walk so the balanced placement grounds, or measuring honestly
that it does not (measured: mass-pivot ~14× cheaper than from-nothing; no operational key-attack). (`08 §9`;
`FRAMEWORK/00_LOOSE_THREADS.md T3.2`.)

## §7 · RE-BASE ⇔ NEST ⇔ FOUND ⇔ RANK-CLIMB — one event, four names

These are **ONE event under four names**, not four separate motions. A magnitude overflow, a nest of a
sequence to a reduced frame, the founding of a new irreducible, and a climb of the tower rank are the same
act at different scales. (`MENO_FORMULA §II`; `TABLETS/01 §III`; `55 §0–§1`. **EXCLUDED:** `CANON/06 §7`'s
"live conflation" project — separating magnitude re-base from tower-rank climb, "the tower climbs ONLY on
founding" — is resolved the *other* way; the separation is retired, `FRAMEWORK/00 Ledger P`. The `i32`/two-hand
number-form it proposed is the smuggled float.)

- **THE RANK is a QUOTIENT DEPTH — which folded space you stand in.** At rank `k` every closed rank-(`k−1`)
  circuit is a point; the grain is what has been quotiented into points beneath you; in `n·2^k`, `k` names the
  folded space `n` counts in. Within a rank the chain SPREADS (combinatorics); only precipitation re-bases.
  (`TABLETS/01 §III`.)
- **The grain is the TRIGGER, not a leak — and NEVER a tolerance.** Conservation is **EXACT** (the recurrence
  is verified on every point, then extrapolated). Where the raw frame does not hold the soul exactly, the one
  move **NESTS**: reduce to the **ranks** (the discrete log; the exponential/tower modes) or the
  **DIFFERENCES** (`Δ`, the discrete derivative; the polynomial modes) and recurse — **the nest RESTORES
  exactness in the reduced frame, no loss.** The grain is only the *reach of exactness* (the register's own
  resolution); hitting it triggers the nest, never a shrug at a slack band. Reconstruction composes back
  through the nest (`Σ` the integral, `2^·` the exp). *"The nesting should be everywhere, everything."*
  *(EXCLUDED: the grain-as-accepted-tolerance / `--tolerance` framing — SUPERSEDED, `FRAMEWORK/00 Ledger A`;
  the DECLARED read-grain of the boundary reads survives, the interior mechanism-tolerance is dead.)*
  (`MENO_FORMULA §III`; `55 §0–§1`.)
- **`π_Β = C/d` is the nest depth**, held holonic as the pair `(C, d)` — `d = 1` (one check), `C` the floors
  walked to the exact frame — never divided into an integer, never a tuned dial (`FRAMEWORK/00 Ledger D`).
- **The relational grammar.** The tree the swing descends is Stern–Brocot / CF, its base-2 face the dyadic
  tree (Minkowski's `?` the isomorphism): one tree, three closure grains (bit-words · characters as depth-8
  dyadic subtrees · ratios as run-words). Reference is a content-face plus a local path, never an absolute
  index (an absolute index is the view from nowhere — a finding in any report). The re-base is *move the root*
  — free by self-similarity (every subtree is the whole tree). (`02 THE NOTATION`.)

**LOOSE THREAD (T7.5, OPEN — "the piece to build"):** the character-closure condition ⊕ ranking **DOWN**
(folding). The machine has ranked UP (founding) exhaustively but the honest hypothesis is it has never ranked
DOWN — so a winding never CINCHES into a closed character (the winding coming home vs a moiré of lower folds).
Held, explicitly NOT a claimed wall. (`CANON/THE_CYCLE.md §2/§6`.)

---

## THE BANS (the number's own)

No floats (the continuum is the fiction; a float is a founding denied). No signed interior (the sign is a
turn). No absolute zero as a basis (born at first contact). No wide stores / `i64` intermediate / `i128`
(re-base, never widen — the two-hand is still the widen). No symbolic constants as values (pairs and
DECLAREs; ratios carried as pairs, the decimal cast only at the print). No hash-scatter for derivation. **No
`<` but the borrow / cross-sign turn; no `%` (the digit is the only division).** No magnitude face read
interior (read the turn). No auditing "which `i64`s are legitimate" (that question lives inside the float
model — the number was never a store). (`02 THE BANS`; `CANON/06 §6`; `MENO_FORMULA §VIII`.)

---

> **One line:** *the number is `m · 2^e` — a magnitude that is a combination of `2^k` corners (multiplication
> is convolve-then-fold, the carry the combinatorial engine and the only order-read the borrow), at a rank
> that is itself a re-based number (the tower nesting forever), with its sign a turn and its bit a hand (the
> octave times the hand, the signed fork below); its well is a digit (remainder the face, quotient the soul
> handed up, mastery becoming conductivity); a prime is a shape that refuses to tile and founds a letter one
> rank up; and re-base, nest, found, and rank-climb are one event under four names — the grain a trigger to
> nest, never a tolerance, exactness restored in the reduced frame.*
