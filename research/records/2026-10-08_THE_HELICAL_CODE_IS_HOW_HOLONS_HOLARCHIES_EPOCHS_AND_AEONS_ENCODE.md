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
3. **frames**: receivers' residue partitions, whose cells are epochs, on which the dihedral group
   acts simply transitively;
4. a **decoder** with its declared channel: the pairing as an inner repetition code that locates
   single-strand defects, and a quotient with a designed kernel as the outer code, with the
   coordinated substitutions outside the kernel as its counted residual;
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
`Prop`s, checked and tested by the Rust owner at every reading. The projected writhe is not
projection invariant (`projectedWrithe_is_not_projection_invariant`), and it is not the ribbon
writhe that `Lk = Tw + Wr` needs. The Reidemeister colouring laws are local Swing transports, and a
full-turn phase forgets the writhe (`Geometry/HolonicUnknotting`). Topological conservation alone
supplies no stored-energy or access theorem.

[built] The HNN's source moments are the strand's face (`SourceMoment`). The located transport
reads residues and carries (`compression::keys::transport`, `CarryHelix`), and the HNN's encoding
squares (`hnn/encoding.rs`) are its conduct. The compression kernel is the greatest
navigator-invariant blind subgroup (`Foundation/CausalRelevance`).

## 4. The laws written now

[definition; owed to the validation queue] `Transport/HelicalCode` states, building on the owners
above:
- the complement-reverse anti-automorphism and its involution;
- the fixed words of a fixed-point-free pairing have even length and correspond to their first
  halves;
- the pairing read through every frame is a fixed-point-free involution;
- two frames of coprime periods meet in exactly one position per pair of residues;
- one crossing change moves the signed crossing sum by exactly 2, so the linking number moves by 1.

The module was written without a compiler and goes to the sole queue for its Lean check before any
claim. Its second part states the perfected laws:
- **resonance on a strand:** `(1 − Ĝ⁻ᵖ) m_{Np} = (1 − Ĝ⁻ᴺᵖ) m_p` in any ring, so `Ĝᵖ = 1` gives
  `m_{Np} = N·m_p`;
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
   as the core's Gauss sum (#62). The closure law `ΔLk = ΔTw + Wr` (supercoiling as the closure
   remainder) consumes it.
2. Projection invariance of `Lk` and `HalvesAgree` (the open `Prop`s of `TopologicalReceiver`), so
   that conservation without crossings is a theorem.
3. The energy split between twist and writhe as a constitutive law, with its buckling threshold (#62).
4. **The consumer.** A native owner of the helical code, built from the existing owners:
   - placement on a navigator's helix (the source port);
   - the declared embedding of letters into contact velocities, so that complementarity is zero
     slip through `lock_iff_zero_power`;
   - receivers' frames;
   - the decoder's quotient with its declared channel.

   Its round trip, stated at the consumer: `decode(read_R(pair(place(u)))) = class_R(u)` for every
   word `u` and every admitted defect of the declared channel.

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
  - coordinated out-of-kernel substitutions are counted as the residual, never claimed as refused;
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
