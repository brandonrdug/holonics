# Located keys become the source port's pair component: the machine locates order-2 in 16 readings, and the bank's release does not consume the key

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lane.** B of U6 (THE_REBUILD, "U6's order
from October 5"), the library spine's S2. **Grade.** [measured] for every count and section below
(the runs of `research/records/2026-10-05_LOCATED_KEYS_receipts/runs.sh`, at this record's commit);
[proved-derived] where marked; [agent-inferred] for the design choices.

**Occasion.** Learning is locating keys by loop closure (CLAUDE.md, "Keys and navigation"). The U6
learner (`hnn::executed`) moved `E` by certified gradient moves and never called `hnn::keys`; on
order-2 the terrain pins the rule in 7 readings while the machine read 1,024 and released 0 of 128
whole sections (the [two counts](2026-09-30_THE_TWO_COUNTS_MEASURED_THE_TERRAIN_PINS_ORDER_TWO_IN_SEVEN_READINGS_AND_THE_CERTIFIED_STEP_DESCENDS_TOWARD_TIES_WHILE_ITS_DECISIONS_STAY_AT_A_GUESS.md);
one flip costs `34037/4096` nats, which a strictly monotone descent cannot cross,
[refit record](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
§9). `hnn::keys` already held the Bombe (menu edges from crib pairs, candidates with plugboard
images, the rotor gauge, publication, re-keying), but the located plugboard map was consumed by
nothing. This loop joins key location to deposition and reads both counts.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touched **the helix**
(the source ring's clock: a distance is a residue of it, the turn a winding of its rotor), **the
pair** (the torus of two crossings `δ` ticks apart, its address the located turn) and **faces and
placement** (the plugboard's images, the source port's columns); the cell holonomy (the loop's sum
of turns), the tube (the request and its section, one span within one turn) and the tower thread
stayed attached and unchanged.

## 0. The recorded failures this loop could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **1, an authored routine standing in for learning.** No distance, map or turn is declared: the
  menu reads every distance of the span and every turn of the ring, and the survivors decide. The
  terrain's rule enters nothing but the passage it generates; the deposit reads only the located
  pair and the declared prior.
- **2, recitation or an index of contexts.** The retained object is the located map on the menu's
  classes (four pairs) and one distance, never a context or a count: the deposit's samples weigh one
  per located class, however often it was seen, and a second deposit of the same key is refused.
- **3, text as the exception.** An edge is two ticks of the source ring's clock and a class map; a
  pixel at its scan tick, a sample at its sample tick and a motor screw at its step enter alike. The
  port must hold one class of the exterior chart (refused otherwise, typed): a codec whose classes
  share a port (bytes mod 60) is refused, not special-cased.
- **5, an uncertified deposition.** The step is `holon::deposition::CertifiedStep` on the slip's
  exact quadratic, adopted only when `CertifiedStep::holds` and the slip falls by the certified
  decrease.
- **6, seen graded as unseen.** The crib is the training passage's seen cells (each request and the
  stations already read as the comparison's declared input); the development reads used seeds
  `2_026_093_041` (located) and `042` (released), the validation set `2_026_093_032` is the pinned
  reused one, and the final confirmation (`2_026_093_033`, `036`, `039`) was read by no run.
- **9, a refusal answered with a larger limit.** Every run met its deadline; none was relaunched.
- **11, the programming language.** The design is stated in turns of the ring's rotor, cosets of
  `⟨c⟩`, cycles of the located map and the transport's spectrum (§5).

## 1. The loop in the objects

- **Holarchy.** The order-2 field is the Holarchy of three parametron rings of period
  `60 = 2²·3·5` joined by two pair contacts in a chain `0 — 1 — 2`; ring 0 is the source and the
  receiving ring. The ring graph is a tree, so the sheet law `∏_(ij ∈ ℓ) σ_i σ_j s_ij = 1` over the
  ring contacts has no closed loop to close: every assignment of sheets survives. The closed loops
  this terrain offers are the passage's own: a pair contact between two crossings of ring 0's
  section `δ` ticks apart, its stage a turn of the ring's rotor.
- **Aeon, epoch, cycle.** A request and its section are one span of ring 0's clock within one turn
  (`n + m = 48 < 60`). Each station is a crossing of the receiving ring's section: one epoch, one
  observation. The located map is a **cycle** of four classes: it is heard when its own cycle
  closes (the [unicity record](2026-09-30_UNICITY_THE_READINGS_LEAVE_ONE_KEY_AND_THE_HELIXS_CELLS_ARE_THE_FAREY_SEQUENCE.md)
  §3), which on the training passage happens at observation 4.
- **Swing.** The located turn `c = 15` is a quarter turn of the rotor (elliptic). The reflector
  machine's stage `ρ^(−m) F ρ^m` is a half-turn, and two of them compose into the turn
  `2(m₁ − m₂)`: only even turns, so on `ℤ/60` no composition of reflected returns reaches `15`. The
  stationary stage family is therefore the rotor's turns themselves (§2). The free transport over
  the distance, `P²`, is a turn of order `30` (§5).
- **Keys.** The key is the distance `δ`, the turn `c` and the plugboard images `S` at the menu's
  ports, up to the rotor gauge `S ↦ ρ^k ∘ S` (and the reflector's, `(c, S) ↦ (−c, F ∘ S)`). Its
  gauge-invariant reading, the one the future reads, is the located map `f = S⁻¹ ρ^c S`.
- **Deposition.** `Θ′|_U = Θ|_U + η Γ_U` with `U` the located classes' columns of the source port,
  `Γ_U` the normal law's unit step on the pair contact's slip, `η` the certified step.
- **Receiver and receipt.** The release is the receiving ring's reception at the request boundary
  (`hnn::prediction::generate_by_bank`, lane C's owner, unchanged); its receipt here is one reading
  per station, read against the terrain's target by the harness only.

## 2. The design, and its equations

**The menu over the span's distances** (`hnn::keys::station_pairs`, the boundary adapter). Each
seen station `t` of a passage is one observation, read against every earlier cell of its passage
at every distance `δ ∈ [1, min(t, d − 1)]`: the edge `port(x_(t−δ)) → port(x_t)`. No distance is
selected.

**The turn machine** (`compression::keys::TurnMenu`, the library owner). An edge `u → v` reads
`S(v) = S(u) + c`, `c ∈ ℤ/d`, `S` injective on the menu's ports. A closed walk closes exactly when
its turns sum to zero, `Σ_(uv ∈ ℓ) ±c ≡ 0 (mod d)`: the cell holonomy of a `ℤ/d` connection, whose
multiplicative chart at `d = 2` with per-contact turns `s_ij` is the sheet law
`∏ σ_i σ_j s_ij = 1`. [proved-derived; Lean owed, #62] With the menu relation `R`:

```text
R a partial injection                       (two consequences or two antecedents of one port fail)
every cycle of R has length ord(c) = d/gcd(c, d);   every path of p edges has p < ord(c)
cycles take whole cosets of ⟨c⟩; the paths' runs pack into the cosets left (ord(c) slots each)
published map = R  when R permutes its menu ports   (a consequence never read stays plural)
```

The owner's test holds the surviving turns equal to the brute-force fibre of `compression::Menu`
(every injective image, every edge read by `Edge::holds`) on 240 drawn menus, and every published
map equal to the survivors' common reading.

**Pair location** (`hnn::keys::PairLocation`): one turn menu a distance; a distance with no edge is
unread, not a survivor; the pair is **located** when exactly one read distance survives with its map
published (`LocatedPair { offset, map, cycle, turns }`). Several surviving distances that publish
one map are one map class (an alias class), never a key.

**The deposit** (`hnn::executed::pair_deposit`). For the located `(δ, f)`, with `U = P^δ` the ring's
transport over the distance and `B` the declared prior (the opening's `E₀`):

```text
Δ_y = U B e_y − (E − B) e_(f(y))                 the pair contact's slip at each located class
Q = Σ_y ⟨Δ_y | Δ_y⟩,   ∂Q/∂(E e_(f(y))) = −2Δ_y          DQ = 2J*Δ (atlas contact.dq)
samples (e_(f(y)), Δ_y, 1) through the source port's normal law: unit step D
Q(η) = Q − η a + ½ η² C,  a = 2Σ⟨Δ_y, D e_(f(y))⟩,  C = 2Σ|D e_(f(y))|²   (exact: Q is quadratic)
η = CertifiedStep::certify(a, C, c): the largest 2^k with ηC ≤ a, ηc ≤ 1
consumer:  (E − B) T = U B   on the menu's classes   (T e_y = e_(f(y)))
```

In the release's storage a continuation that fits the key carries, at its antecedent's placement
`P^(a+δ)`, the antecedent's prior image a second time: `P^a (E − B) e_(f(y)) = P^(a+δ) B e_y`.

## 3. What was built

- `crates/holonics/src/compression/keys/turns.rs`: `TurnMenu`, `TurnReading`, the law above, and its
  tests (brute force against `Menu`; a failed menu stays failed; a 4-cycle on `ℤ/60` keeps exactly
  the turns `15 = 3·5` and `45 = 3²·5`).
- `crates/holonics/src/hnn/keys.rs`: `PairReading`, `station_pairs`, `PairLocation`,
  `PairSurvivors`, `LocatedPair` (the use of the library owner); tests in `hnn/tests/keys.rs`
  (order-2 located at distance 2 with its 4-cycle and turns `4, 12` on a ring of period 16; the
  alternation's aliases kept plural; the menu reads exactly its passage).
- `crates/holonics/src/hnn/executed.rs`: `pair_deposit`, `PairDeposit`; tests in
  `hnn/tests/executed.rs` (the slip closes, the certified step is `2` with decrease the whole slip,
  the consumer holds exactly, unreached classes keep their prior, a second deposit is refused, a
  port holding two classes is refused).
- `research/notebook/hnn_design/hnn_keys_loop.rs`: `executed keys` (the survivors at every
  observation, the counts, the deposit on both openings, the states) and `executed keys-probe` (the
  representation probe of §4, mounted with `with_ports`, never a deposition).
- Atlas: `hnn.turn-menu-fibre`, `hnn.pair-location`, `hnn.pair-deposit`, `hnn.pair-intertwiner-order`.

## 4. Measured

**Readings to lock** (the machine's own count, on the two counts' training passages, in the same
unit as `n*_terrain`: observations, each a station; `executed keys`):

| Terrain (seed) | The machine | `n*_terrain` (the two counts §1) | What survives |
|---|---|---|---|
| order-2 (`2_026_093_031`) | **located from 16 observations (2 requests plus 0 stations)** to the passage's end; distance 2's map published at observation 4 | 7 | `δ = 2`, `f = (0 1 2 3)`, the turns `15, 45` |
| alternation (`2_026_093_034`) | one map class from 39 observations (4 requests plus 7 stations); never one key | 33 (the observational class) | the 23 even distances `2 … 46`, each the identity |
| line (`2_026_093_037`) | one map class from 24 observations (3 requests plus 0 stations); never one key | 20 (the global family) | the 11 distances `4, 8, …, 44`, each the identity |

- Order-2: `16/7 = 2 rem 2` of the terrain's count, against the gradient learner's `n*_machine > 1024`
  (`1024/16 = 2⁶`). The survivors per observation run `40, 24, 9, 3, 3, 2, 3, 3, 3, …, 2, 1`: the
  true distance publishes its map at observation 4, and the distances `46` and `47`, which only
  stations 6 and 7 of a request reach, die last (at observations 15 and 16). On the development
  seed `2_026_093_041` the lock also falls at 16.
- The family is the machine's, not the reference's (`[1, 40] × ℤ/4^(ℤ/4)`, `10240 = 2¹¹·5` keys):
  distances to `47` and only maps that embed in one turn's cycles. Within `[1, 40]` alone order-2
  would lock at observation 5.
- The alternation and the line keep exactly the reference's alias classes (`(2k, id)`, `(4k, id)`),
  extended to the distances `41–47`; each class predicts every continuation of its terrain.

**The deposit** (order-2, at observation 16, on both openings): slip `120 = 2³·3·5 → 0`; the
certified step `η = 2` (`a = 120`, `C = 60`, `c = 1/2`, certified decrease `120`); the consumer
`(E − B) T = U B` holds exactly; largest entry 1; storage growth 0; the state's exact bits
`385320`.

**The release** (lane C's owner, unchanged; validation `2_026_093_032`, 64 nonconstant requests,
512 stations; `executed evaluate`):

| State | Released / held | Whole | Stations right | By station | First lock right | ms |
|---|---|---|---|---|---|---|
| lossless opening | 0 / 64 | 0 | 121 | 18 15 13 14 18 10 15 18 | 0 | 11801 |
| founded opening | 57 / 7 | 0 | 100 | 4 6 14 12 14 19 23 8 | 12 | 190828 |
| keys on the lossless opening | 21 / 43 | 0 | 102 | 19 16 15 15 9 10 12 6 | 5 | 65518 |
| keys on the founded opening | 64 / 0 | **0** | 131 | 13 11 15 13 16 20 19 24 | 25 | 201146 |
| probe: placement and pair (founded) | 43 / 21 | 0 | 120 | 19 9 14 1 8 4 25 40 | **48** | 113193 |

The two openings read exactly the two counts' lines (121 and 100 stations, the same by-station
counts). No state releases a whole section: the acceptance THE_REBUILD set for 1b (strictly more
whole sections than both openings) does not hold. The keys on the founded opening release 49 of 64
sections constant (419 of 448 adjacent stations equal, mostly class 3) and follow order-2's law at
40 of 512 stations.

**The representation probe** (`executed keys-probe`, never a deposition). The located plugboard as
the source port's placement with the pair component, `E e_x = s P^(S(x)) (e_0 + e_(δ−c))` with
`S(y) = 15y` (gauge-fixed at the least port) and `δ − c ≡ 47`: every located class carries the same
material, and `E T = P^c E` and `(E − E_S) T = P^δ E_S` both hold. At the declared unit `s = 1/2`
the unreached termination's prior column carries 60 times a located column's square norm, and on 8
development requests every section reaches the termination (0 right). At `s = 4` (a square norm near
the prior's, a probe value, not a law) the **first lock is right on 48 of 64** validation requests
(the founded opening: 12) and station 7 on 40, but 43 sections are constant: each later lock repeats
its locked neighbour.

## 5. The walls, by their measurements

1. **The release reads the nearest placed datum, not the located pair** [measured]. Under the
   bank's lock iteration the station whose gap is largest locks first, and every later station takes
   the class that continues its locked neighbour at distance 1 (419 of 448 adjacent stations equal
   for the deposited state; 406 of 448 for the probe). The pair component at distance 2 is outweighed:
   each datum enters the station's storage at its transported weight `ρ^|τ_j − τ_k|`, so the nearest
   lock dominates, and a candidate's own column's resonance power decides between classes (the
   class preference gate A met: 3 3 3 3 3 3 3 3). With the classes balanced (the probe), the first
   lock follows the key on 48 of 64 requests: the key is read where nothing is locked yet, and lost
   at the first re-entry.
2. **The ring's transport over the distance cannot carry order-2's cycle** [proved-derived]. A
   source port that reads the rule through the free transport alone needs `E T = P^δ E`. `E` maps
   `T`'s eigenvectors to `P^δ`'s with the same eigenvalue or to zero; `T` is a 4-cycle (eigenvalues
   `1, i, −1, −i`) and `P²` on `ℤ/60` has order `30`, its spectrum the 30th roots of unity, which
   hold `±1` and not `±i` (`4 ∤ 30`). So `E e_0 = E e_2` and `E e_1 = E e_3`: two pairs of classes
   merge. In general `E` is injective on a `k`-cycle only if `k | d/gcd(δ, d)`; order-2 at `d = 60`,
   `δ = 2` needs `8 | 60`. The located turn `c = 15` of order 4 does intertwine (`E e_x = P^(S(x)) w`
   gives `E T = P^c E`), but the release's placement reads the transport `P^δ`, not `c`.

## 6. The interfaces B needs

- **From lane A, the lock.** `Lock { sheet ∈ {+1, −1}, amplitude enclosure, certificate } |
  Unresolved` carries a half-turn; the located turn is a quarter turn (`c = 15` on `ℤ/60`, class
  `1` of `ℤ/4`). B needs the lock's phase class at the turn's grain beside the sheet: the locked
  member's quarter class `j ∈ ℤ/4` (the bank's members `i^j`, whose lock pattern names a line's
  class), or the class in `ℤ/d_g`, with the certificate. B then reads `s_ij` at a pair of stations as
  the difference of their locked classes, and the same `TurnMenu` closes on locks instead of on the
  terrain's cells: the key-lock claim, not made here.
- **From lane C, the release.** Equation at the consumer: on a located pair `(δ, f)` and a placed
  antecedent, the released class at `t` is `f(class at t − δ)`. The release must read each open
  station's pair contact with its located antecedent (through the source port's pair component, or
  the constitution's pair port `E^(δ)` placed for each candidate, which `BankPlacement` does not do:
  its pair term is the request's alone), and compare candidates on equal material (the gain over
  the class's own column read alone), so that the fit, not the nearest lock or a class's own
  resonance, decides the lock. `FieldMaterial` would expose the located pairs `(δ, f)` beside the
  source port.

## 7. Time and memory

Thread budget 8 (`RAYON_NUM_THREADS=8`) on every release read.

| Run | Projection / deadline | Measured ms | Peak resident bytes |
|---|---|---|---|
| keys, development (16 requests) | — / 120,000 (first read) | 500 | 146,665,472 |
| release, development (8 requests × 4 states) | — / 600,000 (first read) | 50,959 | 134,631,424 |
| probe release, development (8 × 4) | 51,000 / 600,000 | 28,799 | 142,614,528 |
| keys, the three training passages (128 requests each) | 4,000 / 120,000 each | 491; 52; 46 | 147,898,368; 31,944,704; 31,817,728 |
| release, validation (64 requests × 5 states) | 505,000 (upper 631,250) / 660,000 | 583,237 | 145,838,080 |

The validation projection took each state's development time a request on seed `2_026_093_042`
(the lossless states `1,498/8` and `1,484/8` ms, the founded opening `23,527/8`, the keys on it
`23,889/8`, the probe `12,716/8`) times 64, summed, and `5/4` of it as the upper end; measured over
projected is `583237/505000` (1 rem `78237/505000`), inside the upper end.

## 8. Owed in #62

1. **The turn menu's fibre**: for a menu of edges `S(v) = S(u) + c` on `ℤ/d` with injective `S`, the
   surviving `c` are exactly those whose order equals every cycle's length, exceeds every path's
   edge count, and admits the coset packing; the published relation is the survivors' common
   reading. Its `d = 2` per-contact chart is the sheet law.
2. **The intertwiner's order**: `E T = P^δ E` with `T` a `k`-cycle and `E` injective on it implies
   `k | d/gcd(δ, d)`.
3. **The pair deposit**: the slip's exact quadratic along the normal law's unit step, its certified
   step as an instance of `Holon/Deposition.certified_step_descends`, and the consumer
   `(E − B) T = P^δ B` at zero slip.

## 9. Commits and gates

- This record's commit: the owners of §3, the record, its receipts
  (`2026-10-05_LOCATED_KEYS_receipts/`: `runs.sh`, every log and curve, the validation sections, the
  three states; `development/`).
- Gates: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib` on
  `compression::keys`, `hnn::tests::keys` and the two deposit tests. No Lean changed; no card run.
- `hnn::executed`'s own move (`Trial`, `ExecutedMove`, the ladder) retires under S2 once B's
  acceptance reads; it is not deleted in this commit (its tests sit in `hnn/tests/prediction.rs`
  and `lock_face.rs`, and 157 notebook references in `hnn_executed_loop.rs` and `hnn_loop_1c.rs`).
