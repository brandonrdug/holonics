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

[definition] A helical code is the composition of five objects. The guide states it:
1. a **strand** on a navigator's helix, with face `m = Σ_k Ĝ(τ(k))⁻¹E(u_k)`;
2. a **pairing** by a fixed-point-free involution `σ` through helical pair contacts;
3. **frames**: receivers' residue partitions, whose cells are epochs;
4. a **decoder**: a quotient with a designed kernel;
5. a **topology**: the linking number, conserved and split as twist plus writhe, changed only by
   crossings.

Its roles: the Holon is the addressed current, the Holarchy the paired and nested duplex, the epoch
a frame cell, and the aeon the passage whose charge is the linking number.

## 3. What is already proved (owners)

[formal-checked] `Transport/HelicalPairInteraction`:
- the phase transport `S⁻ᵈPSᵈ` (rotor stepping and the helix step) with its period and carry laws;
- `reflectedReturn A F = A⁻¹FA`, involutive when `F` is (`reflectedReturn_involutive`) and without
  fixed points when `F` has none (`reflectedReturn_no_fixed_point`): the pairing read at any phase,
  the Enigma's two properties;
- `boundary_involution_reciprocal` and `menu_loop_closure`: the Bombe's loop closure;
- the pair slip map, the contact face, and `lock_iff_zero_power`.

[formal-checked] `Aeon/Clock/CarryWord`: the carry word as the epoch reading of two clocks; it never
recurs exactly at an irrational rate (`never_locks_iff_irrational`), so the code's placement can be
kept from resonating with itself.

[formal-checked] The linking number from an embedding and a declared projection is symmetric and
projection-side independent (`Foundation/TopologicalReceiver`, atlas `winding.linking-number`). The
projected writhe is not projection-invariant (`winding.writhe-not-invariant`, a counterexample). The
Reidemeister colouring laws are local Swing transports, and a full-turn phase forgets the writhe
(`Geometry/HolonicUnknotting`).

[built] The HNN's source moments are the strand's face (`SourceMoment`). The located transport reads
residues and carries (`compression::keys::transport`). The compression kernel is the greatest
navigator-invariant blind subgroup (`Foundation/CausalRelevance`).

## 4. The laws written now

[definition; owed to the validation queue] `Transport/HelicalCode` states, building on the owners
above:
- the complement-reverse anti-automorphism and its involution;
- the fixed words of a fixed-point-free pairing have even length and correspond to their first
  halves;
- the pairing read at every phase is a fixed-point-free involution;
- two frames of coprime periods meet in exactly one position per pair of residues;
- one crossing change moves the signed crossing sum by exactly 2, so the linking number moves by 1.

The module is written without a compiler and goes to the sole queue for its Lean check before any
claim.

## 5. Owed

1. `Lk = Tw + Wr` (Călugăreanu–White–Fuller), first for polygonal ribbons (#62).
2. The decoder's designed kernel as a law: for a substitution channel at a declared position, the
   class map is constant along that position exactly when the substitutions there lie in the kernel.
   Then its error-absorption reading (#62).
3. **The consumer.** A native owner of the helical code, built from the existing owners:
   - placement on a navigator's helix (the source port);
   - pairing read through pair contacts;
   - receivers' frames;
   - the decoder's quotient.
   Its round trip stated at the consumer: `decode(read_R(pair(place(u)))) = class_R(u)` for every
   word `u` and every admitted defect inside the kernel. It refuses, never guesses, where a defect
   leaves the kernel.

## 6. Acceptance (fixed before any build)

- **Lean.** `Transport/HelicalCode` passes the queue's check with no axiom, `sorry` or
  `native_decide`, and its laws are in the atlas.
- **The consumer.** On known-truth terrains in at least three boundary charts (text bytes, notes on
  a pitch helix, sampled waves), generated by exact routines:
  - the round trip holds for every word and every admitted in-kernel defect;
  - an out-of-kernel defect is refused, never decoded wrongly;
  - two frames of coprime periods recover each position from its residue pair;
  - a crossing change moves the linking reading by exactly its sign.
  The reading is exact counts, on unseen words.
- **No catered machinery.** No authored decoder table: the kernel is the receiver's own quotient,
  and the pairing is the declared involution of the code's own kind.

**Recorded failures checked.** An authored routine standing in for learning (the decoder is a
quotient of the machine's own receivers). Text run as the exception (three boundary charts in the
acceptance). Seen material graded as unseen (unseen words only). Bits read as progress (exact
counts, not code length).
