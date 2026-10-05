# The located transport: each occurrence steps the rings by its located advance

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** E and B of U6 (THE_REBUILD, "U6's
order from October 5"): the helical encoding's missing operation. **Grade.** [definition;
agent-inferred] for the pins of §0, fixed and committed before any read; [proved-derived] where
marked; [measured] for the counts of the later sections.

**Occasion.** The field's selective step advances ring `g` by `[port_g(u) ∈ N_g] + carry`, and its
port chart is the residue chart `port_g(u) = u mod d_g` (`hnn::field::Field::selective_step`,
`PortChart::residue`): the codec chooses which cells step which rings. Guard 9 of
[THE_MACHINE](../../docs/THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible) refuses
that chart and asks that the code length not see the labels, `L(field; π∘x) = L(field; x)`. The
operation that replaces it, how far an occurrence of `u` advances ring `g`, has no owner. This loop
builds it as key location on a known-truth terrain whose truth is that transport.

## 0. The claim and the pins, fixed before any read

### 0.1 The law, as derived from the records

[proved-derived; the records cited] An occurrence `k` of a source enters at the navigators' phases
after its admitted steps, `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E(u_k)` (`Transport/SourceMoment`, `hnn::moment`;
the [retention audit](2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)).
The phases are one lift `ℓ ∈ ℤ/D`, `D = ∏ d_g`, of the rings' joint clock, and the missing
operation is the cell's **located transport** `A(u) ∈ ℤ/D`:

```text
ℓ(k+1) = ℓ(k) + A(u_k)                                   the address: ℓ(k) = ℓ(0) + Σ_(j<k) A(u_j)
odometer chart (ring 0 least significant, w_g = ∏_(h<g) d_h):
  τ_g(k+1) = τ_g(k) + a_g(u_k) + carry_g(k)  (mod d_g),   carry_(g+1)(k) = ⌊(τ_g(k) + a_g(u_k) + carry_g(k)) / d_g⌋
  A(u) = Σ_g a_g(u) w_g                                     (winding_add: the carry is the defect of additivity)
CRT chart (pairwise coprime d_g):  r_g(k+1) = r_g(k) + (A(u_k) mod d_g),  no carry
```

Two corrections to the brief's wording, each derived:
1. **The two charts are one lift.** "Order carried by the passage clock's residues across coprime
   rings (CRT) and the carry cocycle" holds as two charts of the same address, not as a residue
   plus a carry: the CRT chart carries `ℓ(k) mod d_g` with no carry, the odometer chart its digits
   with the carry. The occurrence count's residues `k mod d_g` carry order only at the identity
   advance (`A ≡ 1`); under a located transport the lift is the source word's address.
2. **What a receiver can locate is `A(u)` up to the receiving ring's gauge, which is dihedral.**
   When the emission reads the receiving ring's digit (§0.2), the rings below it are read only
   through their joint winding, the carry word into the receiving ring (J2 of the
   [gap record](2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md): the winding is the
   carry), so the located object is `A(u) ∈ ℤ/D` and each digit `a_g(u)` follows from the
   mixed-radix bijection. Its gauge is the receiving ring's rotation `ℓ ↦ ℓ + j·D_low` with
   `λ ↦ λ∘ρ^(−j)`, and also the reflection `ℓ ↦ D_low − 1 − ℓ`, `A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`
   [proved-derived: the digits of `D − 1 − ℓ` are `d_g − 1 − τ_g`, so the receiving digit reflects
   and the step negates; checked by the owner's brute-force test]: every passage is read alike under
   both, as the turn menu's reflector gauge pairs `c` with `−c`.

The located `A` is the Enigma's stepping inferred (which cells step which rotors, and by how much),
not its plugboard: a permutation chart `S⁻¹ U S` on the classes stays bijective, while under a
located transport one class is followed by different classes as the carry differs (a many-to-many
relation on the classes).

### 0.2 The terrain [definition; agent-inferred]

- **The navigators**: three closing rings of pairwise coprime periods `(3, 4, 5)` in the odometer
  chart, `D = 60 = 2²·3·5` (the order-2 declaration's ring period; by CRT `ℤ/60 ≅ ℤ/3 × ℤ/4 × ℤ/5`).
  Rings 0 and 1 are hidden; ring 2 is the receiving ring. Its digit is the lift read at the grain
  `D_low = 12`: `c(ℓ) = ⌊ℓ / 12⌋`.
- **The truth**, drawn by the exact routine (`Draw::new(seed)`, in this order): the transport
  `A(u) ∈ ℤ/60` for each class `u ∈ ℤ/5`, a bijection `λ: ℤ/5 → ℤ/5` (the receiving chart's labels,
  cell to class), and each passage's key `ℓ_p(0) ∈ ℤ/60`.
- **The passage** (autonomous): `u_k = λ(c(ℓ(k)))`, `ℓ(k+1) = ℓ(k) + A(u_k)`. The machine reads only
  the emitted classes, never `A`, `λ` or a key. `|A| = 5`.
- **The read set**: 16 passages of 60 cells each (one turn of the joint clock), 960 observations.
- **The seeds**, searched in every ref's history, the tree and the receipts (`2_026_100_9xx` appears
  nowhere): development `2_026_100_901` (timing and checks); **the read, once each**, the draws
  `2_026_100_911`, `912`, `913`, `914`; their repair passages' keys from `2_026_100_921`, `922`,
  `923`, `924`.

### 0.3 The path [definition; agent-inferred]

1. **Locate** (`compression::keys::transport`, the library owner). Survivor elimination over the
   machine's own family (rings of the declared periods with carry; every transport, every label
   bijection, every key): a survivor is a partial transport, a partial label map and the set of
   lifts it still admits. Each emission is one observation and closes the loop since its class's
   last visit: the lift must lie in the cell its class is labelled with, so a recurrence `u_k = u_k′`
   declares `c(ℓ(0) + Σ_(j<k) A(u_j)) = c(ℓ(0) + Σ_(j<k′) A(u_j))` and a non-recurrence its negation
   (labels injective). A class's first step branches its advance over `ℤ/60`; nothing is set by a
   class's code. The rotation gauge is fixed by the convention that the read set's first emission
   reads the receiving digit `0`; the reflection is kept, and the fibre is read in its classes, the
   representative chosen in first-occurrence order (label-free).
2. **Relabel.** For every permutation `π` of `ℤ/5` (all 120), the same location on `π∘x`.
3. **Found** (`hnn::encoding`, read-only). The passage chart `ℚ^60` with the admitted transports
   `T_u e_ℓ = e_(ℓ + A(u))` (the located advances), the receiving forms `ρ_c = Σ_(ℓ: λ(c(ℓ)) = c) e_ℓ*`
   (the located labels) and the openings `e_(ℓ_p(0))` (the located keys), founded by
   `Encoding::found`; its squares checked by `Encoding::squares`.
4. **Code** (an actual prefix code over declared `D`, `|A|`, the passage count and length): the
   transport per receiving digit in `⌈log₂ D⌉` bits each, the labels as a permutation index in
   `⌈log₂ |A|!⌉` bits, each passage's key in `⌈log₂ D⌉` bits, then the residual: a patch count in
   `⌈log₂(n + 1)⌉` bits and each patch as its position in `⌈log₂ n⌉` bits and its class among the
   other `|A| − 1` in `⌈log₂(|A| − 1)⌉` bits. The decoder steps the lift by the decoded cell's advance
   (the source steps the rings) and reads the next cell through the labels. Beside it, the residue
   chart's navigator: `A_res(u) = Σ_g [u mod d_g ∈ N_g] w_g` with the field's single notch
   `N_g = {0}` (its description: the lock sets, `3 + 4 + 5 = 12` bits), its labels and keys chosen
   to minimize its patches.
5. **Repair.** 16 fresh passages per draw (same `A`, `λ`; keys from the repair seed), the declared
   damage erasing cells `{3} ∪ [6, 10) ∪ [20, 25) ∪ [33, 37) ∪ [44, 48) ∪ [55, 60)` (23 erased, 37
   intact; the tail is continuation as the special case). With the transport and labels located on
   the draw's read set, each passage's lift family is restricted from both sides through the
   located navigator `F(ℓ) = ℓ + A(λ(c(ℓ)))` (an intact cell admits its cell's 12 lifts, an erased
   one all 60), the fixed point certified against the joint fibre (the keys the intact cells
   admit), and each erased cell released through `receiver::release` at tolerance zero when its
   class family is one class, held otherwise. Its residual is the repair owner's (the truth's index
   in the first held family, pinned and re-run), decoded and checked to reopen every passage.

### 0.4 The measures [definition]

The fibre outcome at the read set's end (one gauge class, plural, empty) and whether it is the
generator's; the survivors per observation (survivors and lifts); `n*_machine`, the least
observation count from which the survivors' transports are one gauge class with every class's
advance set, held to the read set's end; the terrain's unicity count `n_U`, the least `n` with
`|A|^(n−1) ≥ D^|A| · |A|! / 10` (the classes of transports and labels under the dihedral gauge of
order 10 must take distinct emission words after the gauge-fixed first one), `n_U = 16` since
`5^14 = 6,103,515,625 < 9,331,200,000 ≤ 5^15`; the relabelling law (located transport and code
length under all 120 permutations, and the residue chart's code length under them); the founded
dimension, reached span and the squares; the code lengths against the literal `960·⌈log₂ 5⌉ = 2,880`
bits; the repair's released, held and correct cells, its residual bits against the literal
`368·3 = 1,104` bits a draw, and every passage reopened.

### 0.5 The claim [derived from §0.1; agent-inferred]

On every read draw:
- **Location.** The fibre at the read set's end is one gauge class and it is the generator's (`A`
  or its reflection `−A`, with the labels to match); `n_U = 16 ≤ n*_machine ≤ 240` (located within
  the first four passages).
- **Relabelling.** For all 120 permutations the located transport on `π∘x` is `A∘π⁻¹` (exactly, on
  the label-free representative), the outcome is the same and the code length is equal; the residue
  chart's code length changes under at least one permutation.
- **Founding.** The squares `D E = ρ`, `E T_u = U_u E` hold exactly on every reached state; the
  founded dimension equals the reached span, `60` on a draw whose advances generate `ℤ/60`.
- **Code.** The located navigators regenerate the read set with no patch: `30 + 7 + 16·6 + 10 = 143`
  bits against the literal `2,880`; the residue chart's code is longer than the located one.
- **Repair.** Every released cell equals its truth; at least 332 of the 368 erased cells are released
  (nine tenths); every passage reopens from its residual, whose bits are below the literal `1,104`.

A located class other than the generator's, a fibre without the truth, a relabelling that changes
the located transport or the code length, a square that fails, a released cell that differs from
its truth, or a code at or above the literal falsifies the claim.

### 0.6 Amendment, after the development reads and before the read

[measured; agent-inferred; receipts `2026-10-05_THE_LOCATED_TRANSPORT_receipts/development/`]
The owner's tests, the development read (`2_026_100_901`) and location-only reads on draws no read
uses (`2_026_100_941` to `956`) found five defects in §0 as pinned. None is in the location's
exactness: the brute-force test holds the survivors, with their lifts, equal to the fibre.
1. **The read set's shape.** On 16 passages of 60 cells from drawn keys the autonomous orbits fall
   into short attractor cycles. A class visited only at a passage's start is probed at few lifts,
   and its advance stays plural within a window (one of four exploration draws was one class). The
   read set becomes the helix's 60 keys in their drawn order (`Draw::new(seed)` after the terrain,
   each key a uniform pick among those left). The first 48 open passages of 120 cells, two turns of
   the joint clock (5,760 observations). The 12 keys left open the repair passages of 60 cells:
   openings no read passage used. The repair seeds `2_026_100_92x` are not used.
2. **The fibre can stay plural with every key read.** Of the 16 exploration draws, 7 locate one
   gauge class at 48 keys and 9 at all 60. The rest keep 2 to 313 classes. The members are not
   only the dihedral images: on the development draw the second member shifts three classes'
   advances by multiples of the grain (`28 → 16`, `24 → 48`, `17 → 29`) with relabelled cells, and
   every member regenerates every read passage from some key. The receiving grain does not
   separate them on the read set. "One gauge class on every draw" is withdrawn, refuted in
   development. The read reports the fibre with its members, and the repair restricts through
   every member (`restrict_fibre`): a cell is released only where every kept member's certified
   family is the same one class.
3. **`n*_machine ≤ 240` is refuted in development.** The exploration reads 260 to 7,095 and the
   development draw 3,485: the last members die at a rare boundary crossing in a late passage.
   `n*_machine` is reported against `n_U = 16`.
4. **The founded dimension is `D − (D_low − 1) = 49`, not 60.** The receiving forms are the shifts of
   one cell's indicator, an interval of 12 lifts. Its discrete Fourier transform vanishes at the 11
   nonzero multiples of 5, so the readings span 49 dimensions of `ℚ^60` [proved-derived; the
   owner's test reads `25 = 30 − 5` on `(2, 3, 5)`, and the development read 49].
5. **Relabelling reads 24 permutations a draw**: every fifth of the 120 in lexicographic order, the
   identity first. One exploration draw's location took 30,985 ms, so all 120 would take about an
   hour on such a draw. The owner's test reads 12 permutations on its small helix.

**The amended claim**, on every read draw (`2_026_100_911` to `914`):
- **Location.** The generator's gauge representative is a member, and every member regenerates
  every read passage from some key. The outcome is reported with its member count, and
  `n*_machine ≥ n_U = 16` where the fibre is one class.
- **Relabelling.** For the 24 permutations, the fibre is carried, `n*_machine` is equal and the
  code length is equal. The residue chart's code length changes under at least one permutation.
- **Founding.** The squares hold. Where the advances generate `ℤ/60`, 60 lifts are reached and the
  founded dimension is 49.
- **Code.** The located code, `30 + 7 + 48·6 + ⌈log₂ 5761⌉ = 338` bits, reopens the read set
  against the literal of `17,280`. The residue chart's code is longer.
- **Repair.** Every released cell equals its truth, and every passage reopens from its residual.
  On a one-class draw at least nine tenths of the 276 erased cells are released. The residual is
  below the literal of `828` bits.

**The projection** [measured]. The development draw took 6,354 ms in all and peaked at 25.4 MB
(systemd scope), its location 39 ms. The largest location measured before launch is 30,985 ms
(exploration seed `953` at 60 keys, first read; its receipt's re-read gives 30,555 ms). A draw's unit is then at most 25 locations (the read and 24 relabellings),
`25 · 30,985 = 774,625` ms, plus the residue chart's 25 codes, the founding and the repair. The
development read gives 6,354 − 25 · 39 ms for those, so 800,000 ms a draw is the projection. The
deadline is `5/4` of it, 1,000 s under an outer `timeout`. The four draws run together, one thread
each (4 of the budget of 8), each in its own systemd scope.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop touches **the
helix** (circle + carry: the odometer's carries are the hidden rings' winding read by the receiving
ring), **the tower thread** (each ring's carry is the next ring's step: the carry tower over the
lift, and its CRT chart), **the cell holonomy** (a recurrence closes the loop of the steps between
two visits of one receiving cell), **faces and placement** (the receiving chart's labels, the
encoding's `D`) and **the tube** (the repair carries the lift family across the damage). The pair
stays attached: two visits of one cell are the pair contact between two crossings of the receiving
ring's section, here read through the lift rather than through a located pair `(δ, f)`.

## 1. The recorded failures this loop could repeat, and how each is held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **1, an authored routine standing in for learning.** The terrain generates its truth; the machine
  is handed the declared periods only and branches every advance over `ℤ/D`. No advance, label or
  key is read from the terrain or from a class's code.
- **2, recitation or an index of contexts.** The retained object is a transport of `|A|` advances,
  the labels and one key a passage, never a context or a count; the code regenerates the passage
  from them.
- **3, text as the exception.** A class is a reading of the receiving ring's digit at its grain; a
  pixel's, a sample's or a motor step's class enters alike. The location reads only the equality of
  occurrences, so no codec's grain enters it, which the relabelling law tests.
- **Lesson 3, a located cause carried unrepaired.** The bank's release (its nearest-lock and
  class-preference causes) is not this loop's consumer: the encoding owner and the repair read the
  located transport directly.
- **6, seen graded as unseen.** The repair passages are fresh keys from their own seeds, damaged
  before the machine reads them; the truth is read only to score.
- **7, bits read as progress.** The code lengths are reported beside the fibre, the relabelling law
  and the repair's fidelity.
- **9, a refusal answered with a larger limit.** Each run has its deadline from a development
  measurement; none is relaunched past it.
- **11, the programming language.** The design is stated as a lift on a helix, its charts (digits
  with carry, CRT residues), loop closure at a grain, a dihedral gauge and a fibre.

## 2. The design, and its equations

**The helix and its two charts** (`compression::keys::transport::CarryHelix`). The rings' lift
`ℓ ∈ ℤ/D` read as digits with carry (`digits`, `step_digits`, checked against
`geometry::winding::Odometer` on every lift and advance of `(3, 4, 5)`) and as CRT residues
(`residues`, adding with no carry). The receiving cell is the last digit, `c(ℓ) = ⌊ℓ / D_low⌋`.

**The terrain** (`SteppedTerrain`, known truth by an exact routine): `u_k = λ(c(ℓ(k)))`,
`ℓ(k+1) = ℓ(k) + A(u_k)`. Its step map `F(ℓ) = ℓ + A(λ(c(ℓ)))` translates each cell by its class's
advance: the passage is the receiving reading of one orbit of `F` on `ℤ/D`, eventually periodic, and
one class is followed by different classes as the hidden lift's carry differs.

**Location by loop closure** (`TransportLocation::locate`). A survivor is `(A|_seen, λ|_seen, L)`,
the advances read so far, the labels read so far and the lifts it admits at the current emission.
At each emission `u_(k+1)` after `u_k`:

```text
moved = L + A(u_k)                      (each a ∈ ℤ/D when A(u_k) is unread: the branch)
L′ = moved ∩ cell(λ⁻¹(u_(k+1)))         when u_(k+1) is labelled
   = moved ∩ cell(c), λ(c) := u_(k+1)   for each unlabelled c otherwise (the branch)
a passage's first emission: moved = ℤ/D; the read set's first: L = cell 0, λ(0) := u_0 (the rotation gauge)
```

A survivor dies when `L′` is empty: the loop from the class's last visit does not close at the
receiving grain. The survivors are explored depth first; the count at each observation is the
number of survivors there. The fibre's members are the complete survivors' gauge classes, each
represented by itself or its reflection, whichever orders first in the classes' first-occurrence
order (`gauge_representative`).

**The code** (`located_code`, `read_located`; `residual_code`, `read_residual` for any fixed
transport): description `d_r ⌈log₂ D⌉`, labels `⌈log₂ |A|!⌉`, keys `P ⌈log₂ D⌉`, patch count
`⌈log₂(n + 1)⌉`, patches `⌈log₂ n⌉ + ⌈log₂(|A| − 1)⌉` each; decoded by stepping the lift by each
decoded class.

**The consumer** (`LocatedTransport::chart`, read by `hnn::encoding::{PassageChart, Encoding}`
unchanged): `ℚ^D`, `T_u e_ℓ = e_(ℓ + A(u))`, `ρ_c = Σ_(λ(c(ℓ)) = c) e_ℓ*`, openings at the located
keys; `Encoding::squares` checks `D E = ρ`, `E T_u = U_u E` on every reached state.
[proved-derived] Where the advances generate `ℤ/D` every lift is reached, and the readings are
the shifts of one cell's indicator, an interval of `D_low` lifts. Its discrete Fourier transform
`Σ_(j<D_low) ω^(jk)` vanishes exactly at the `D_low − 1` nonzero multiples of `D/D_low`, so the
founded dimension is `D − (D_low − 1)`: the receiving grain is silent on those modes of the hidden
rings.

**Repair** (`LocatedTransport::restrict`, `restrict_fibre`, `lift_residual`, `lift_reopen`):

```text
L_t⁽⁰⁾ = cell(λ⁻¹(x_t)) intact, ℤ/D erased
L_(t+1) ← L_(t+1) ∩ F(L_t);   L_t ← L_t ∩ F⁻¹(L_(t+1))       to the fixed point (a chain: the projection)
certified ⇔ L_t = {F^t(k) : k a key whose orbit meets every intact cell}
fibre: classes_t = ∪_(members m kept) {λ_m(c(ℓ)) : ℓ ∈ L_t^m};  released ⇔ one class and every kept m certified
```

## 3. What was built

- `crates/holonics/src/compression/keys/transport.rs`: `CarryHelix`, `SteppedTerrain`,
  `LocatedTransport` (`digits`, `residues`, `reflected`, `regenerate`, `keys`, `chart`,
  `restrict`), `TransportLocation` (`locate`, `curve`, `located_from`, `members`, `fibre`),
  `gauge_representative`, `unicity_count`, the code (`located_code`, `read_located`,
  `residual_code`, `read_residual`), the repair (`LiftRestriction`, `restrict_fibre`,
  `FibreRestriction`, `lift_residual`, `lift_reopen`); `CompressionError::Helix`.
- Its tests (`transport/tests.rs`): the two charts are one lift (against `Odometer`); the reflection
  is a gauge (every key, two helices); the location equals the brute-force fibre (24 drawn read
  sets on `(2, 3)`, survivors with their lifts, in reflection pairs); the generator is a member and
  every member regenerates the read set (`(2, 3, 5)`, every key); the unicity count `16`; the
  relabelling law (12 permutations, against the residue chart); the located code reopens its read
  set (143 bits for sixteen passages of sixty cells); the encoding founds the helix (`25 = 30 − 5`);
  the repair releases only truth and reopens every passage.
- `research/notebook/hnn_design/hnn_transport_loop.rs`: `executed transport <seed> <read keys>
  <length> <out> [locate]`.

## 4. Measured: the read, once each (at `59281dc5`'s build)

[measured] `executed transport <seed> 48 120`, the four draws together, one thread each; receipts
`2026-10-05_THE_LOCATED_TRANSPORT_receipts/s<seed>{_log.txt, _scope.txt, .sections, .curve.gz}`.
Nothing changed after the amendment. The amended claim of §0.6 holds on every count; the pinned
claim of §0.5 fails where §0.6 says it was refuted in development (two draws plural; `n*_machine`
past 240 on all four).

**Location** (5,760 observations a draw; `n_U = 16`):

| Draw | Fibre | Members | `n*_machine` | Peak survivors | Survivors explored | Generator a member | Every member regenerates |
|---|---|---|---|---|---|---|---|
| `…911` | one | 1 | 376 = 2³·47 | 73,140 | 213,507 | yes | yes |
| `…912` | one | 1 | 1,219 = 23·53 | 33,772 | 101,409 | yes | yes |
| `…913` | plural | 3 | 4,453 = 61·73 | 29,808 | 2,701,845 | yes | yes |
| `…914` | plural | 2 | 5,658 = 2·3·23·41 | 38,772 | 399,623 | yes | yes |

- **The located transports** (each class's advance in `ℤ/60`, then as odometer digits `(a_0, a_1, a_2)`
  and CRT residues `(mod 3, mod 4, mod 5)`), the generator's, read only to score:
  - `…911`: `A = (11, 45, 33, 23, 23)`; digits `(2,3,0), (0,3,3), (0,3,2), (2,3,1), (2,3,1)`; residues
    `(2,3,1), (0,1,0), (0,1,3), (2,3,3), (2,3,3)`. The located representative is its reflection,
    `(49, 15, 27, 37, 37) = −A`, with the labels reflected.
  - `…912`: `A = (56, 29, 51, 15, 54)`, located as itself.
- **The plural fibres.** On `…913` the three members agree everywhere but one class's advance, which
  the read set leaves in a window of three consecutive lifts, `23, 24, 25` in the representative's
  chart, the generator's at the centre: no read orbit meets a cell boundary at that class's step
  closely enough to separate them. On `…914` the second member swaps the labels of cells 1 and 3 and
  changes four advances (`(14, 33, 56, 23) → (46, 39, 4, 25)`), and each member regenerates every read passage
  from its own keys. These are differences the receiving grain does not distinguish on the read set:
  a kernel of the read, not a failure of the elimination (the brute-force test holds the survivors
  exact).
- **The curve** (`.curve.gz`, survivors and lifts at every observation): on `…913` the survivors run
  `1, 92, 1588, 772, 500, 364, 340, 228, …` over the first observations as each class's first step
  branches its advance and the next cell prunes it, and settle at 6 survivors (3 members, each with
  its reflection) from observation 4,453.

**Relabelling** (24 permutations a draw, every fifth of the 120, the identity first): on every
draw the fibre is carried by every permutation (each member's advance at `π u`, each label
`π(λ(c))`), `n*_machine` is equal under all 24, and the located code is 338 bits under all 24. The
residue chart's code length takes 22 to 24 distinct values over the same 24 permutations on each
draw:

| Draw | Residue chart, identity labels | Least and greatest over the 24 |
|---|---|---|
| `…911` | 61,640 = 2³·5·23·67 | 43,730 to 65,795 |
| `…912` | 60,560 = 2⁴·5·757 | 54,695 to 67,370 |
| `…913` | 58,700 = 2²·5²·587 | **13,685 = 5·7·17·23** to 67,160 |
| `…914` | 65,975 = 5²·7·13·29 | 49,520 to 67,745 |

On `…913` one relabelling brings the residue chart below the literal: a chart a code chooses can
compress or not by the accident of the labels, which is why guard 9 refuses it.

**Founding** (`hnn::encoding`, unchanged): on every draw the advances generate `ℤ/60` (their gcd with
60 is 1), all 60 lifts are reached, the founded dimension is **49 = 7² = 60 − 11**, and the squares
`D E = ρ`, `E T_u = U_u E` hold on all 60 reached states under all 5 located transports.

**Code**: the located navigator's code is **338 = 2·13² bits** on every draw and reads the read set
back exactly, against the literal **17,280 = 2⁷·3³·5 bits** (ratio `169/8640`); the residue chart at
its identity labels takes 58,700 to 65,975 bits, above the literal.

**Repair** (12 passages of 60 cells a draw from the held-out keys, 276 = 2²·3·23 erased cells):

| Draw | Released (equal to the truth) | Held (family size) | Members kept / refused | Residual / literal (bits) | Reopened |
|---|---|---|---|---|---|
| `…911` | 276 (276) | 0 | 12 / 0 | 0 / 828 | 12 of 12 |
| `…912` | 276 (276) | 0 | 12 / 0 | 0 / 828 | 12 of 12 |
| `…913` | 275 (275) | 1 (2) | 35 / 1 | 1 / 828 | 12 of 12 |
| `…914` | 276 (276) | 0 | 24 / 0 | 0 / 828 | 12 of 12 |

Every released cell equals its truth: 1,103 of 1,103. On `…913` a held-out passage refused one member
(its restriction emptied a family), and one cell stayed held with two classes where the kept members
disagree; its one-bit residual reopens the passage. A repaired passage, whole (synthetic `ℤ/5`;
`·` erased; `…913`, passage 0, key 48):

```text
damaged  241·11····0311111111·····11111111····3111111····1031111·····
repaired 241111111103111111111110311111111111031111111111103111111111
truth    241111111103111111111110311111111111031111111111103111111111
```

The tail `[55, 60)` is continuation as the special case; the opening's cell 3 is restored from both
sides once the later intact cells pin the lift.

## 5. What the read shows

1. **The missing operation exists and is located without a class's code.** On every draw the
   generator's transport is a member of the fibre, located from the emitted classes alone, and the
   relabelling law holds on every permutation read; the residue chart's code length moves by up to
   53,475 bits under relabelling on one draw.
2. **The receiving grain leaves a kernel.** Two of four draws keep a plural fibre after every key but
   twelve was read twice around the joint clock. The members are what the receiving grain does not
   separate on the read set; the repair reads through all of them and releases only where they agree,
   so the plurality costs one held cell in 1,104 and never a wrong one.
3. **The founded encoding is the helix less the grain's silent modes.** The located transports give
   `hnn::encoding` non-identity `T_u`, and it founds 49 of the helix's 60 states: the 11 Fourier
   modes an interval of 12 lifts annihilates are the hidden rings' part the receiving ring never
   reads linearly.
4. **The lock is slow against the unicity count.** `n*_machine` runs from 376 to 5,658 observations
   against `n_U = 16`: the counting bound separates transports in principle, but the autonomous
   orbits meet the cell boundaries that separate neighbouring advances rarely, in late passages.

## 6. The interfaces

- **Lane E, the field's selective step** (`hnn::field::Field::selective_step`, Codex's entrance; not
  edited here). Equation at the consumer: ring `g` advances by `a_g(class) + carry_g` with
  `a_g(class) = digits(A(class))_g` from `LocatedTransport::digits`, in place of
  `[port_g(code) ∈ N_g]`; the moment then reads each occurrence at the lift `ℓ(0) + Σ_(j<k) A(u_j)`.
  The class reaches the field as the encoding's class (`Encoded`), never as a code.
- **Merges.** A word `u·v` steps the lift by `A(u) + A(v)`, and `E T_v T_u = U_v U_u E` follows from
  the two squares, so a merged unit is founded on the composed transport without a new square; its
  pricing by the code-length pair (the landmarks record §5) is not built here.
- **Deposition.** The location here is exact elimination, the zero-likelihood limit of the population
  over key families; no constitution moved. Depositing a located advance as the ring's stepping law
  is the lane E consumer above.

## 7. Time and memory

Projection and deadline from §0.6 (800,000 ms a draw, deadline 1,000 s); four draws together, one
thread each; peaks from each systemd scope (`_scope.txt`) and the process's own `VmHWM`.

| Run | Projection / deadline (ms) | Measured wall (ms) | Peak (scope; `VmHWM` bytes) |
|---|---|---|---|
| development `…901` | — / 1,200,000 | 6,387 (service) | 25.4M; 16,306,176 |
| `…911` | 800,000 / 1,000,000 | 6,545 | 16.7M; 16,453,632 |
| `…912` | 800,000 / 1,000,000 | 6,081 | 16.2M; 16,396,288 |
| `…913` | 800,000 / 1,000,000 | 8,798 | 20.5M; 16,093,184 |
| `…914` | 800,000 / 1,000,000 | 6,257 | 15.8M; 16,232,448 |

Measured over projected, the slowest draw: `8798/800000 = 4399/400000`. The projection took the
slowest location measured before launch (30,985 ms, an exploration draw with 313 members) for all 25
locations of a draw; the read draws' locations took 10 to 136 ms. The projection's error is that
choice of the worst measured unit, reported as such.

## 8. Owed in #62

1. **The two charts are one lift**: for pairwise coprime `d_g`, the odometer's step with carries gives
   the digits of `ℓ + A`, and the CRT residues of `ℓ + A` are the residues' sums (an instance of
   `Geometry/PhaseCarry.winding_add` and the Chinese remainder isomorphism).
2. **The dihedral gauge**: `c(D − 1 − ℓ) = d_last − 1 − c(ℓ)`, and the passage of
   `(−A, λ∘(c ↦ −c), D_low − 1 − ℓ(0))` is the passage of `(A, λ, ℓ(0))`.
3. **The relabelling law**: the survivors on `π∘x` are those on `x` carried by `π`, so the located code
   length is invariant; a transport defined from the classes' codes is not carried.
4. **The founded dimension**: the shifts of an interval indicator of length `L | D` on `ℤ/D` span
   `D − (L − 1)` dimensions (the zeros of `Σ_(j<L) ω^(jk)`), joined to `HNN/Encoding.hankel_rank_eq`.
5. **The lift restriction** is the joint fibre's projection on a chain (the repair owner's item 1,
   for a function on hidden states), and the release over a fibre's union is sound: a released class
   is the truth's whenever the truth's member is kept.

## 9. Commits and gates

- `7fe3cc4c`: the claim and the pins, before any read. `59281dc5`: the owner, its tests, the harness,
  the development receipts and the pin's amendment (§0.6), before the read. This record's commit:
  the read's receipts, §4–§9.
- Gate 1, `bash tools/gate.sh` at the owner's build: check, guard lints and guard doctests ok
  (12,922; 18,148; 21,035 ms); the lints add only `result_large_err` in the new owner, which every
  `CompressionError` owner carries.
- Gate 2, `cargo test -p holonics --lib -- --test-threads=4` at the owner's build: 1,043 passed, 0
  failed, 411,970 ms of tests (417,968 ms wall with its build; four threads, beside the read's four,
  within the budget of 8); receipt `lib_tests.txt`. The owner's nine tests are among them. No Lean
  changed (§8 names the obligations); no card run (no kernel or card path changed).
