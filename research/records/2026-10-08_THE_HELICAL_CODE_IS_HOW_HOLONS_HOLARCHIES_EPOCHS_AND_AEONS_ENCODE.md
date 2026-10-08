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

## 4. The laws, kernel-checked

[formal-checked; conditional where marked] `Transport/HelicalCode`
(`lean/Holonics/Transport/HelicalCode.lean`, imported from `lean/HolonicsResearch.lean`, outside the
`Framework` closure) states the following, building on the owners above and duplicating none of
them. The sole queue accepted it at `0669655169b8`: the compiler exited zero, and all 81 declarations
carry only `propext`, `Classical.choice` and `Quot.sound`. A narrow consumer of the research root's
new import passed 8 queries. The full research library and the HNN were not rerun. Receipt:
[native-v2](receipts/2026-10-08-helical-code/native-v2/HANDOFF.md). The first attempt, `12fcee787`,
failed at one statement (an inferred `Group (α → α)`); [native-v1](receipts/2026-10-08-helical-code/native-v1/VALIDATION.json)
keeps it unrewritten. The module states:
- the complement-reverse anti-automorphism and its involution;
- the fixed words of a fixed-point-free pairing have even length and correspond to their first
  halves;
- the pairing read through every frame is a fixed-point-free involution;
- one crossing change moves the signed crossing sum by exactly 2, so the linking number moves by 1.

Its atlas rows are `helical.*` in `geometry.tsv`. The accepted scope is the review's:
- the partner's face holds under a uniform clock with constant openings;
- the crossing laws are arithmetic on declared signed diagrams;
- two repairs are proved distinct, not exhaustive;
- letter-level freedom is not carrier-level freedom.

Its second part states the perfected laws:
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

   **The first consumer, step 1** (`agent-inferred`). It was designed from a read-only survey of the
   native path at `f12fb506c`, then corrected by Epime's source review (proceed, with five
   corrections and the carried support). Its owned slice:
   - `compression/keys/duplex.rs` and its tests;
   - the `pub mod duplex` export in `compression/keys.rs`;
   - two methods in `compression/keys/transport.rs`;
   - the `helical.*` atlas owners.

   It consumes `LocatedTransport`, `PairContact`/`pair_lock`, `Encoding::{found, encode}` and
   `width_over_readings` → `LawfulOptions::assemble` → `release`, and founds no subsystem. Its
   equations at the consumer:
   - **Lifts, with the carry.** `LocatedTransport::lifts(key, u)` gives the `n + 1` absolute lifts
     `ℓ₀ = key mod D`, `ℓ_{k+1} = ℓ_k + A(u_k)`, unreduced: phase `ℓ mod D`, whole winding
     `ℓ div D`. `CarryHelix::of_residues(r)` gives the unique `ℓ ∈ [0, D)` with `residues(ℓ) = r`
     (Lean `joint_residue_determines_position`); the absolute position keeps the winding.
   - **Fit first.** The clean strand must be a passage of the transport,
     `emit(ℓ_k mod D) = u_k` for every `k < n`. Otherwise the consumer returns the located defect,
     never a duplex. No inverse branch of a non-injective `F` is chosen.
   - **The partner, paired before the quotient.**
     - `Pairing::new(σ)` refuses fixed points and non-involutions, and `σ̄(w)_k = σ(w_{n−1−k})`.
     - The partner's `n + 1` lifts are `ℓ′_k = R(ℓ_n mod D) + (ℓ_n − ℓ_{n−k})`, `k = 0..n`, with
       `R` the gauge's `reflect_key`. Their phases are `R(ℓ_{n−k})`, and the partner ends at
       `reflect_key(key)`.
     - Partner letter `k` is carried by the step `ℓ′_k → ℓ′_{k+1}` and read at its arrival. For
       every `k < n` the consumer checks `lt.reflected().step(ℓ′_{k+1}) = ℓ′_k` and
       `σ(lt.reflected().emit(ℓ′_{k+1})) = σ̄(u)_k`.
     - This is `F′ = R∘F⁻¹∘R`, the reversed step keyed by arrival. `T_c⁻¹ = T_cᵀ` holds in the
       native coordinates only; a physical paired return keeps `R`, the reversed order, the
       complemented labels and the producing frames.
   - **Contacts, kinematic only.** A declared injective chart `v₊` with `v₋ = v₊∘σ`. The unit-rate
     slip `v₊(a) − v₋(b)` vanishes exactly when `b = σ(a)`, read through `PairContact` and
     `pair_lock`. A power claim needs a declared positive-weight `ContactMaterial` that is definite
     on the attained slips; none is made in this step.
   - **The receiver's class** is `class_R(w) = ((E e_{ℓ_k mod D})_{k=0..n}, ℓ_n div D)`: every
     receiving state, the terminal included, and the terminal carry probe. It is a read-only
     receipt tuple, never retained as a per-occurrence chain; the continuing retained object
     stays the future-sufficient quotient. `E` is founded from the development keys' chart and is
     the receiver's own quotient, never an authored table.
   - **The channel and inner code.** Substitutions at declared contacts on either strand, at
     equal length: single-strand, or coordinated and complementary. The slipped contacts are
     `{k : p′_{n−1−k} ≠ σ(u′_k)}`.
   - **The repair family, exact and carried.** For the independent factors `F_k` (the clean letter,
     or the two candidates at a slipped contact), the support keeps full carried positions:
     `X_0 = {key}`, `X_{k+1} = {x + A(a) : x ∈ X_k, a ∈ F_k}`, with back-pointers to actual
     members.
     - `E` reads `x mod D`, and the carry probe reads the division with remainder of `x`. The
       quotient is taken only after every admitted terminal and carry receiver is included.
     - Since `0 ≤ A(a) < D` with at most two candidates a contact, `|X_k| ≤ k(D − 1) + 1`. A
       rolling exact support needs at most two such sets, and the transition work is bounded by
       `Σ_k |X_k||F_k|`. This is polynomial for this declared independent channel, not a general
       claim that families are cheap.
     - When fitting the transport couples the factors, only supported extendable prefixes count
       (forward and backward support), and that added cost is stated.
   - **Release.** The class is released exactly when it is constant over the complete family: zero
     width through `width_over_readings` over the complete readings, never a sample. Otherwise the
     consumer holds, naming the slipped contacts and two actual witness members with their differing
     classes. A declared template side collapses each factor.
   - **Absorption, against known truth only.** A coordinated substitution is absorbed exactly when
     the damaged word's class equals the truth's class. Its carried shift `Δ = A(u′_i) − A(u_i)` is
     a signed representative that moves every later absolute lift. The count stays on the
     acceptance side, never inside the decoder.

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
