# The helical code is how Holons, Holarchies, epochs and aeons encode

**Date.** October 8. **Issues.** #63, #73, #62. **Grade.** Definition and lens record. The proved
parts name their Lean owners, and the owed parts are listed in §5. The definition lives in the
[elementary objects](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode).

## 1. The lens

Brandon, October 8: screw words into resonating code lengths about helices along flux patterns, the
encoding technique of the double helix, independent of any organism. Intersecting partitions along
strings, and knots intertwining and crossing. The Enigma's wire matching and the Bombe, the retina
and the lens. "The helical code object would be what I'm trying to do with Holons, Holarchies,
Epochs, and Aeons … please perfect it and please raise this to such critical importance."

[definition] It is raised: the helical code is the critical object of the rebuild. It changes the
forward plan's order, because the encoding of every Holon is stated through it: the HNN's source
placement, its receivers' frames, its decoders' kernels, and its aeons' conserved charges.

## 2. The object

[definition] A helical code is the composition of five objects. The guide states it with each
proved part's hypotheses:
1. a **strand** on a navigator's helix, with face `m = Σ_k Ĝ(τ(k))⁻¹E(u_k)`, whose repeats
   resonate when their period is whole turns;
2. a **pairing** by a fixed-point-free involution `σ` through helical pair contacts, read backward:
   the reflection of the dihedral group `⟨S, U | U² = 1, USU = S⁻¹⟩` of the screw `S` and the dyad
   half-turn `U`, lifted by `σ`;
3. **frames**: receivers' residue partitions, read together with the whole winding and the epoch
   (an interval between section arrivals, across which a residue recurs). The dihedral group acts
   simply transitively on a duplex's frames;
4. a **decoder** with its declared channel. The pairing is an inner repetition code that locates
   single-strand defects. The receiver's quotient is the outer code: its kernel is fixed by the
   admitted future, and the placement is designed to put likely defects' reached differences in
   it. Coordinated substitutions outside the kernel are the residual;
5. a **topology**: the linking number of closed strands, split as twist plus writhe and changed
   only by crossings.

Its roles: the Holon is the addressed current, the Holarchy the paired and nested duplex, the epoch
a frame cell, and the aeon the passage whose charge on closed strands is the linking number.

## 3. What is already proved, and under which hypotheses (owners)

Epime read the owners' exact scope on October 8; this section states it.

[formal-checked] `Transport/HelicalPairInteraction`:
- the phase transport `S⁻ᵈPSᵈ` (rotor stepping and the helix step), with its period and carry laws;
- `reflectedReturn A F = A⁻¹FA`, involutive at each fixed frame when `F` is
  (`reflectedReturn_involutive`; a stepping machine also evolves its frame), and without fixed
  points when `F` has none (`reflectedReturn_no_fixed_point`): the Enigma's two properties;
- `boundary_involution_reciprocal` and `menu_loop_closure`: the Bombe's loop closure;
- `lock_iff_zero_power`: on a pair face of positive weight with null-definite material, the
  integer rates `q, p` read zero power exactly when `q v_a = p v_b`. This is a synchronization of
  velocities. Complementarity read as zero slip needs the consumer's declared embedding of letters
  into contact velocities (§5).

[formal-checked] `Aeon/Clock/CarryWord`: the carry word as the epoch reading of two clocks. It never
recurs exactly at an irrational rate (`never_locks_iff_irrational`), so the code's placement can be
kept from resonating with itself.

[formal-checked; conditional] `Foundation/TopologicalReceiver`. The linking number of a crossing
family under a declared direction:
- it is symmetric (`linkingNumber_comm`);
- it is unmoved by the viewing side and by positive rescaling (`linkingTotal_neg_direction`,
  `linkingTotal_smul_direction`);
- it is an integer under `HalvesAgree` (`linking_is_an_integer`).

`HalvesAgree` and invariance under admissible projections (`LinkingIsProjectionInvariant`) are open
`Prop`s. No current crate reads the linking number. The retired Rust owner checked both half-sums at
every reading and tested declared directions
(`13f8c734:crates/holonics-cuda/src/topological_receiver.rs`: `linking_number`, with its half-sums;
`linking_under_directions`). The Lean module's docstring still describes that owner as present,
and its repin goes with the module's queue check. The projected writhe is not
projection invariant (`projectedWrithe_is_not_projection_invariant`), and it is not the ribbon
writhe that `Lk = Tw + Wr` needs. The Reidemeister colouring laws are local Swing transports, and a
full-turn phase forgets the writhe (`Geometry/HolonicUnknotting`). Topological conservation alone
supplies no stored-energy or access theorem.

[formal-checked] The meet of coprime frames already has owners:
- `HNN/Prediction.joint_residue_determines_position`: two addresses below the product with equal
  residues are equal;
- `Geometry/PairResonance.diagonal_step_generates_the_coprime_torus`;
- `HNN/Prediction.joint_class_not_additive`: a joint class is not a sum of per-factor functions.

The meet is unique only modulo the product of the periods. The absolute position needs the whole
winding, and on class-dependent steps the actual source-to-clock relation.

[built] The HNN's source moments are the strand's face (`SourceMoment`). The located transport
reads residues and carries (`compression::keys::transport`, `CarryHelix`), and the HNN's encoding
squares (`hnn/encoding.rs`) are its conduct. The compression kernel is the greatest
navigator-invariant blind subgroup (`Foundation/CausalRelevance`).

## 4. The laws specified; the module being prepared

[definition; specified, not yet on disk] `Transport/HelicalCode` will state, building on the owners
above, laws it does not duplicate:
- the complement-reverse anti-automorphism and its involution;
- the fixed words of a fixed-point-free pairing have even length and correspond to their first
  halves;
- the pairing read through every frame is a fixed-point-free involution;
- one crossing change moves the signed crossing sum by exactly 2, so the linking number moves by 1.

A worker is preparing the module without a compiler. Its frozen source goes to the sole queue for
the Lean check before any claim. Its second part states the perfected laws:
- **resonance on a strand:** `(1 − Ĝ⁻ᵖ) m_{Np} = (1 − Ĝ⁻ᴺᵖ) m_p` in any ring, so `Ĝᵖ = 1` gives
  `m_{Np} = N·m_p`;
- **the partner's face:** for an additive carrier involution `J` with `J E = E σ` and
  `JĜJ = Ĝ⁻¹`, under the declared uniform tick with constant openings `α, β`:
  `m_β(σ̄(u)) = JĜⁿ⁻¹⁺ᵅ⁺ᵝ m_α(u)`, an involution. Epime's composition read found that the two maps
  need this equivariant join: the phase transport conjugates at a fixed phase, while placement acts
  on a carrier. The recurrence carrier `q = Ĝⁿ⁻¹ f` reads the same join as `JĜ⁻⁽ⁿ⁻¹⁾` in the
  ending frame. Epime's finite witness, with ticks `(0, 2)`, shows the uniform-tick hypothesis is
  needed. Letter-selected screws need `J S_a J = S_{σ(a)}⁻¹`, and then `J F′_k J = F_n⁻¹ F_{n−k}`;
- **the dihedral pairing:**
  - on the index line, the half-turn `k ↦ c−k` inverts the shift;
  - the half-turns of `⟨S, U⟩` are the `SʲU`;
  - on the `2p` frames of a duplex, the group acts simply transitively;
- **four letters:**
  - the fixed-point-free involutions of a four-element set, with the identity, are a Klein group
    acting regularly;
  - every substitution has one type, and the pairing preserves it;
- **the inner code:** single-strand substitutions at contacts with intact partners slip exactly
  those contacts, and each repair has two members;
- **the duplex passage:** on a ribbon, flipping a core self-crossing flips two inter-strand
  crossings of equal sign, so the signed sum moves by 4 and `Lk` by 2.

## 5. Owed

1. `Lk = Tw + Wr` (Călugăreanu–White–Fuller), first for polygonal ribbons, with the ribbon writhe
   as the core's Gauss sum (#62). The closure law `ΔLk = Lk − (Tw₀ + Wr₀) = ΔTw + ΔWr`
   (supercoiling as the closure remainder; `Wr₀ = 0` for a planar relaxed core) consumes it.
2. Projection invariance of `Lk` and `HalvesAgree` (the open `Prop`s of `TopologicalReceiver`), so
   that conservation without crossings is a theorem.
3. The energy split between twist and writhe as a constitutive law, with its buckling threshold (#62).
4. **The consumer.** It is not a separate subsystem: it is the paired chart and lift on the existing
   native path `LocatedTransport::reflected`/`reflect_key` → `PassageChart` → `Encoding::squares`
   → `Encoded`/`SourceMoment` (Epime's read). It adds:
   - the two strand contact ports, `v₋ = v₊ ∘ σ` with `v₊` injective on the admitted contact
     alphabet;
   - the declared reversed incidence `k ↔ n−1−k`. The offset-chain repair support handles its
     certified forest, but a constant offset is not this cyclic gluing;
   - the lift `B` where `σ` descends through the founded fibre. Otherwise the duplex is paired
     before that quotient.

   [agent-inferred; read from the owner] **Where the pairing sits on the native path.**
   - `LocatedTransport::reflected` (`A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`, `reflect_key`) is the dihedral
     **gauge** of the receiving chart. It is the mirror chart that regenerates the same passage, an
     ambiguity of location kept in each fibre. It is not the pairing.
   - The pairing reverses the passage. Its navigator is the dyad-conjugated inverse of the strand's
     step: `F′ = R∘F⁻¹∘R` with `F(ℓ) = ℓ + A(λ(c(ℓ)))` and `R` the gauge's reflection. This is
     `USU = S⁻¹` on the navigator, with complemented labels `σ∘λ`.
   - With class-dependent advances, `F⁻¹` is keyed by the arrival's class, not the emission's. The
     partner's advance at its position `k` is the strand's advance at position `n−2−k`, so the
     partner is not a located transport of the same form. This is the reversed relation the native
     path must declare.
   - Where `F` is not injective, the reversal has a preimage fibre. The paired strand's actual lifts
     resolve it: each strand is the other's key.
   - The labels enter no chart (the relabelling law), so `σ` acts only on the boundary decoder.
   - Each transport `T_c` is a cyclic shift, a permutation matrix, so `T_c⁻¹ = T_cᵀ`. The partner's
     chart is therefore the adjoint chart: the antiparallel complementary strand is the adjoint
     passage. It runs in reversed order with transposed transports, the same shape as the learning
     covector's return through the producing operands.

   [agent-inferred] **The chart.** On a rotation carrier the dyad is conjugation: `BUB = U⁻¹` for
   `U` multiplication by a unit `ζ`. So complements embed as conjugates off the real axis, and a
   letter on the axis would be its own complement. For four letters, the vertices `±2 ± i` of a
   rectangle in `ℤ[i]` have exactly the Klein symmetry: conjugation is `σ`, and negation and
   `−conj` are the other two types. The square `±1 ± i` would add a quarter-turn merging the types.
   The turn is a Pythagorean unit such as `ζ = (3+4i)/5`. Its angle is irrational, since the only
   roots of unity in `ℚ(i)` are `±1, ±i`, so it never locks and stays exact. In space, the same
   chart is the dyad `diag(1, −1, −1)` about `x`, the helix about `z`, and the letters at
   `(±2, ±1, 0)`.

   **Its two invariants** (Epime's read):
   1. pairing, placement and receiver transport commute, with `Encoding::squares` and the admitted
      successor quotient keeping every separator;
   2. under the declared channel, the actual antecedent lies in the compatible repair family, and
      release requires the receiver's quotient to be constant over that whole family.

   With `s` unmarked slipped contacts the family is factored into `s` binary choices, `2^s` words.
   Storing the factors does not make an arbitrary receiver's class image cheap. The round trip
   `decode(read_R(pair(place(u)))) = class_R(u)` holds for template-assisted single-strand repairs
   and coordinated in-kernel defects. Ambiguous families are held or refused. Coordinated
   out-of-kernel changes are the declared residual, for which the equation guarantees nothing.
   The source moment's coordinates stay bounded while its exact count bits grow, and neither it nor
   the CRT recovers a whole word past its admitted capacity. The decoder, fibre, clock and carry
   residuals are kept. A grain split is not a corruption witness.

   **The first consumer, step 1** (`agent-inferred`; designed from a read-only survey of the
   native path at `f12fb506c`, for review before any build). It is one file beside the located
   transport, `compression/keys/duplex.rs`. It consumes `LocatedTransport`, `PairContact`/`pair_lock`,
   `Encoding::{found, encode, readout}` and `width_over_readings` → `LawfulOptions::assemble` →
   `release`. It founds no subsystem. The terms it adds, each stated as its equation at the consumer:
   - `LocatedTransport::lifts(key, u)`: `ℓ₀ = key mod D`, `ℓ_{k+1} = ℓ_k + A(u_k) mod D`. These
     are the driven lifts that the private `driven_patches` already steps.
   - `Pairing::new(σ)`: refused unless `σ∘σ = id` and `σ(a) ≠ a` for every class. Its
     complement-reverse is `σ̄(w)_k = σ(w_{n−1−k})`, with `σ̄∘σ̄ = id` and
     `σ̄(vw) = σ̄(w)σ̄(v)`.
   - **The partner, paired before the quotient.** Its lifts are `ℓ′_k = R(ℓ_{n−1−k})`, with `R`
     the gauge's reflection (`reflect_key`). Since `reflected` is `R∘F∘R` and regenerates the same
     passage, the partner is that mirror chart read in reverse, with complemented labels. Two
     equations are checked at the consumer, using the existing `step` and `emit`:
     `lt.reflected().step(ℓ′_{k+1}) = ℓ′_k`, and `σ(lt.reflected().emit(ℓ′_k)) = σ̄(u)_k`. No
     `F⁻¹` is needed while the duplex is formed from the actual strand. Each strand is the
     other's key.
   - **Contacts.** A declared injective chart `v₊` of the classes into `ℚ³`, with `v₋ = v₊∘σ`.
     The slip `s_k = v₊(u_k) − v₋(p_{n−1−k})` is read through `PairContact` at unit rates, and
     the lock through `pair_lock(pair, 1, 1)`. The law is
     `slipped = {k : p_{n−1−k} ≠ σ(u_k)}`.
   - **The receiver's class** is `class_R(u) = (E e_{ℓ_k})_k`, the founded encoding's reading of
     the placed lifts. `E` is the receiver's own quotient (`ker E ∩ R = ⋂_w ker(ρ T_w)`), not an
     authored table. A substitution at `i` shifts every later lift by
     `Δ = A(u′_i) − A(u_i)`. It is absorbed exactly when `E(e_{ℓ_k+Δ} − e_{ℓ_k}) = 0` for every
     later `k`, which is the designed-placement law (item 5) on this carrier. On most helices
     that blind subgroup is trivial, so nothing is absorbed. That is the receiver's honest
     kernel, never enlarged.
   - **Repair and release.** The repair family is factored per slipped contact,
     `{u′_k, σ(p′_{n−1−k})}`, and a template frame collapses each factor. Release requires the
     class to be constant over the whole family: zero width through `width_over_readings` at
     tolerance zero. Otherwise the decoder holds, naming the contacts and the classes.
   - `CarryHelix::of_residues(r)`: the unique `ℓ < D` with `residues(ℓ) = r` (the Lean owner is
     `joint_residue_determines_position`). The absolute position keeps the carry from
     `step_digits`.

   **The three boundary charts**, each with `σ` as its own half-turn. Each is a known-truth
   `SteppedTerrain` over the chart's alphabet. Placement uses the terrain's truth transport, so
   location's cost of `D^|A|` is not spent; location is a separate, built capability.
   - Text bytes in base four, two bits a digit, with `σ(x) = 3 − x` (bit complement) and the
     rectangle chart `v₊ ∈ {(±2, ±1, 0)}`, where `σ` is the dyad `diag(1, −1, −1)`.
   - Twelve pitch classes, with `σ(x) = x + 6 mod 12` (the tritone).
   - Eight signed amplitude levels, with `σ(x) = 7 − x` (phase inversion).

   Byte passages themselves stay refused on the located route (`Unencoded`); the text chart is
   their base-four boundary chart. The acceptance reads exact counts on unseen keys and words:
   located slips, released and held families, absorbed and residual coordinated substitutions
   against truth, and CRT recovery.

   **Deferred to later steps, named.**
   - Step 2: the partner's face on the HNN carrier, `m(σ̄u) = B U⁻⁽ⁿ⁻¹⁾ m(u)`, which needs a
     located moment chart (`PassageChart::moment` admits ticks 0 to 2 only).
   - Step 3: the linking reading of a closed duplex and its crossing changes. No current crate
     reads the linking number, and the retired owner is at `13f8c734`.

5. **The designed-placement law** (Epime's typed form over `Foundation/CausalRelevance`'s additive
   carrier). `q(P(T_{i,v}u)) = q(P(u))` iff `δ_{i,v}(u) = P(T_{i,v}u) − P(u) ∈ K`, for every admitted
   background `u`. The type `v` is a substitution operator, and the kernel holds its reached
   difference. The law is owed to #62 with the consumer, and its types and hypotheses are kept
   when the consumer is built.

## 6. Acceptance (fixed before any build; the channel revised the same day)

Epime's clarification (October 8) fixed what the receiver must read. A quotient proves class
invariance for in-kernel changes. A corruption that carries one valid codeword to another of a
different class cannot be refused by any decoder that round-trips the undamaged word. So the
admitted channel and its separation are declared operands.

- **Lean.** `Transport/HelicalCode` passes the queue's check with no axiom, `sorry` or
  `native_decide`, and its laws are in the atlas.
- **The consumer.** On known-truth terrains in at least three boundary charts (text bytes, notes on
  a pitch helix, sampled waves), generated by exact routines. Every reading is an exact count, on
  unseen words:
  - single-strand substitutions at contacts with intact partners are located exactly (the slipped
    contacts are the substituted ones);
  - with a template frame, the repair is unique and the round trip holds;
  - without one, the class is returned exactly when every repair decodes to the same class, and
    otherwise the decoder refuses, naming the contacts and the classes;
  - coordinated in-kernel substitutions keep the class;
  - coordinated out-of-kernel substitutions are counted against the known truth as the residual,
    never claimed as refused (online they have no witness);
  - two frames of coprime periods recover each position from its residue pair;
  - a crossing change moves the linking reading by exactly its sign, and a duplex passage by two.
- **No catered machinery.** No authored decoder table. The kernel is the receiver's own quotient,
  and the pairing is the declared involution of the code's own kind.

**Recorded failures checked.**
- An authored routine standing in for learning: the decoder is a quotient of the machine's own
  receivers.
- Text run as the exception: three boundary charts in the acceptance.
- Seen material graded as unseen: unseen words only.
- Bits read as progress: exact counts, not code length.
- An unbounded guarantee claimed past its channel: the residual is declared and counted.
