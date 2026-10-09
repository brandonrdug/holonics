# Emanation and infall are one port pairing read from its two sides

**Date.** October 9 (the lens: October 6). **Issues.** #73, #62, #63. **Grade.** Lens record. Each
section carries its own grade. §2's identities are checked by exact computation and joined to
formal-checked or built owners. The lift in §2.4 is agent-inferred. The joins in §4 are owed.

**Scope.** Brandon's October 6 lens named two pairs, {emanate/infall, foil/transport}. The foil and
transport (the laboratory's reach axis) are recorded separately. This record keeps only the flow
axis, emanation and infall.

## 1. The lens

Brandon, October 6: the first iterations of the laboratory's Universality Machine anchored much of
their thinking on {emanate/infall, foil/transport}. He held these back because they were too
primitively fixed at the time, and the mathematics had to earn the right to compress the dynamics
into those words. He judges that it now has, and that whatever was done then should be lifted into
something real. The occasion was a discussion of why the adjoint works in learning. His objection to
calling it "backwards" belongs to the directionality lens, recorded separately.

**The laboratory's text** [historical; source-inspected; private laboratory, June].
- `src/labyrinth/HOLONICS.md` §VII (June 15) has two axes and four aims. On the flow axis, emanation
  traverses the outgoing leg (the act), and infall traverses an incoming leg back toward its parents
  (perception). Directionality is not a primitive there. Crossing symmetry makes in and out a frame
  choice.
- `src/labyrinth/thread/PRIMITIVES.md`: the same act is emanation in one frame and infall in
  another, and what a frame flip leaves invariant is the axis, never the direction.
- A finding of June 15 (`src/eros/LAUNCH.md`): reading infall as the literal inverse of emanation
  failed, because its learning residual rose. The note concluded that the two are dual aims of one
  object, not the same operation.
- The Rust realization of June 23 (`src/eros/um/holonics/src/traversal.rs`) nevertheless computes
  emanation as adding a turn and infall as the turn difference from a reference, on a wrapping turn
  carrier. On that carrier infall undoes emanation. Nothing outside its crate calls them.

**The repository's July records** [historical; source-inspected] already read the pair this way.
The [July 14 record](2026-07-14_THE_CONTINUOUS_NET_AND_THE_LOCAL_SOLVE.md) describes prior infall
narrowing through a contemporary neck and emanating into a future field, as the first-person and
the external reading of one passage. The [July 16 record](2026-07-16_THE_SELF_DUAL_LOCUS_BELONGS_TO_THE_FRAME.md)
names the receiving infall/emanation duality `J_F` of a declared frame and its fixed set, the
self-dual locus.

## 2. The derivation

### 2.1 One pairing, two signs

[definition; formal-checked owners] At an interconnection port with effort `e` and flow `f`, the
pairing `⟨e, f⟩` is power. It enters one participant's balance as delivered and the other's as
received, and in the joined Holon the port term cancels (Tellegen: `Holon/Dirac.tellegen`,
`Transport/JunctionLaw.tellegen`; composition preserves the Dirac property,
`Holon/Dirac.compose_isDirac`). **Emanation** is the pairing read from the side that delivers, and
**infall** is the same pairing read from the side that receives. Reversing the port's orientation
negates both readings and leaves the pairing. The laboratory's "the axis, never the direction" is
the governing rule that orientation exists only in the pairing (CLAUDE.md, the Holon and coholon
row).

### 2.2 What falls in, and what emanates back

[proved-standard; checked by exact computation; built owner] In wave variables at an admittance `Y`,
the incident wave is `a = e + Y⁻¹f` and the returned wave is `b = e − Y⁻¹f`. Then

```text
e·f = Y (a² − b²) / 4
```

The port's power is what falls in less what emanates back. With `e = 3`, `f = 2`, `Y = 2`: `a = 4`,
`b = 2`, and `Y(a² − b²)/4 = 6 = e·f`. Exchanging the roles of `a` and `b` is the frame flip: it
negates the power and keeps the pair of waves.

The HNN's World boundary is this law, built and checked. The Robin termination `a = e + Y⁻¹f` is
solved by the actual interaction owner, and both participants continue on the solved state.
`WaveJointStep::closes` checks, exactly, at every solved step:
- `power = Σ Y(a² − b²)/4 = e·f`;
- `a + b = 2e` and `Y(a − b) = 2f`;
- the port work, and the joint balance's exactness.

The owners are Rust `hnn::physical::action::world::{WaveJointStep, BoundJointWorld}`. The HNN's
action inference never reads the World's coefficients.

### 2.3 At a lossless junction, emanation and infall obey one involution

[proved-standard; formal-checked owners; checked by exact computation] A two-port junction of
admittances `y₁`, `y₂` scatters the incoming pair `(i, h)` into the emitted and held pair `(o, h′)`
(atlas `wave.two-port-junction`, written there with admittances `a`, `b`;
`Computation/HolonicConstitutiveCirculation.weighted_square_energy`):

```text
o  = ((y₁ − y₂)/(y₁ + y₂)) i + (2y₂/(y₁ + y₂)) h
h′ = (2y₁/(y₁ + y₂)) i + ((y₂ − y₁)/(y₁ + y₂)) h
y₁ o² + y₂ h′² = y₁ i² + y₂ h²
```

Its scattering matrix squares to the identity: the diagonal entries of the square are
`((y₁ − y₂)² + 4y₁y₂)/(y₁ + y₂)² = 1`, and the off-diagonal terms cancel. Reading the outgoing pair
as incoming returns the same law. With `y₁ = 1`, `y₂ = 3`, `i = 2`, `h = 1`: `o = 1/2`, `h′ = 3/2`,
and both energies are `7`. The July 16 record's duality `J_F` is also an involution, and its fixed
set is the self-dual locus: in the completed-zeta chart `J_F(s) = 1 − s̄` squares to the identity
and fixes exactly `Re s = 1/2`, since `1 − σ = σ` only at `σ = 1/2`.

The HNN's junction scattering is the general case. It is an involutive isometry of the
admittance-weighted energy and contributes zero power (`HNN/Propagation.junctionScattering_involutive`,
`junctionScattering_isometry`; atlas `hnn.junction-scattering`). Once a dissipative contact or a pump
enters, the junction is no longer an involutive isometry and the direction becomes physical. The
[series-cancellation and time-parity record](2026-10-09_SERIES_CANCEL_AT_JUNCTIONS_AND_A_PASSAGES_ORDER_COMES_FROM_CHAINING_ITS_GRAINS.md),
§3.6, derives this.

### 2.4 Infall is the adjoint, and it is the inverse only on an isometry

[proved-standard; agent-inferred lift] For an emanation map `A`, the infall that returns a received
covector `λ` to the producing operands is the adjoint: `⟨A*λ, v⟩ = ⟨λ, Av⟩` for every forward
variation `v`. This is the paired adjoint of the learning law: the covector returns through the
operands that produced the forward carriers. Its owners:
- Rust `hnn::ratio` (`HolonRatio::covector`, `RatioCovector::descent`) and `Word::pull_back`
  (in `hnn/port.rs`), which accepts only a `RatioCovector` (THE_MACHINE, guard 10);
- reverse factor order, `Computation/HolonicAdjointNormalization.dualMap_comp_reverse_order`.

An invertible `A` has `A* = A⁻¹` exactly when it is an isometry of the declared metric. So infall
undoes emanation only in a lossless, reciprocal medium. With dissipation or pumps it does not.
This is the laboratory's own finding, that the literal inverse failed and infall had to be the dual
of emanation. Its turn-difference infall was the isometric case, since on a turn carrier the inverse
of a translation is its adjoint. Calling the adjoint "infall" is a lift, not a recovery of the
laboratory's operation.

### 2.5 Emanation splits at the producing constitution; infall deposits only where it arrives

[definition; formal-checked and built owners]
- **Emanation.** A drive emanated into a constitution splits uniquely and `C`-orthogonally into a
  part that rides an existing mode and a part that founds or drives off resonance. The riding part
  needs zero holding effort and keeps the mode energy's exchange law. The founding part needs
  nonzero effort, though its work can vanish (atlas `compression.resonate-emanate`;
  `Compression/Core/Resonance.split_exists_unique`, `resonant_drive_rides`,
  `emanating_drive_needs_effort`, `work_ledger`, `clamp_witness`).
- **Infall.** A constitution changes only where infall arrived. A deposit at a locus reads only the
  covectors that reached it (`Objects/Deposition.deposit_local_edges`, `deposit_local_region`,
  `unreached_edge_unchanged`; `HNN/Retention.deposit_descends`). At the HNN's receiving return, a
  zero or absent comparison changes no statistic, remainder or commit (Rust
  `hnn::word::action_return::NativeReceivingReturn`, its `deposit` field).
- **The residual.** The comparison's residual is emanated or retained (CLAUDE.md, the Holonic
  Compression row). What deposition does not retain either leaves through a port as emanation or
  stays as a carried exact remainder (`DepositReading`'s unresolved contact material).

The receiver-side remainder of the emanation split, what a receiver's existing modes do not carry,
is the foil's subject. It is not derived here.

## 3. What the repository already owns

- The port pairing and its cancellation in composition: `Holon/Dirac` (`tellegen`,
  `kirchhoff_isDirac`, `compose_isDirac`), `Transport/JunctionLaw.tellegen`.
- The wave split at the World boundary, built and checked: `hnn::physical::action::world`.
- Lossless junctions as involutions: `HNN/Propagation`, `Computation/HolonicConstitutiveCirculation`.
- The paired adjoint and its reverse order: `hnn::ratio`, `Word::pull_back`,
  `Computation/HolonicAdjointNormalization`.
- Emanation's split: `Compression/Core/Resonance`.
- Deposition's locality: `Objects/Deposition`, `HNN/Retention`.

## 4. The joins owed

1. **Infall stops at the World's boundary by design** (#73). The receiving return's opening covector
   holds the World's returned waves fixed. It is not a derivative through the World's state or its
   Robin solve (its own documentation says so), because the World's coefficients are the World's
   own. Infall that continues to the action's controls needs a receiver's model of the World. That
   is the port-Holon World model the
   [receiving-phase record](2026-10-08_THE_RECEIVING_PHASE_COMPARISON_RETAINS_AN_EXACT_FAMILY_AND_ITS_PROBE_IS_A_DECLARED_LEVERAGE.md)
   names next (C1b). Its consumer equation is the adjoint identity of §2.4 on that model's own
   operands, never on the World's.
2. **The adjoint pairing as a stated check at the comparison owner** (#73). For every admitted
   forward variation `v` of the producing operands, `⟨Word::pull_back(λ), v⟩ = ⟨λ, Φ′v⟩`, read
   exactly on the actual Word.
3. **Lean** (#62):
   - the wave split `e·f = Y(a² − b²)/4` with its frame flip `a ↔ b`;
   - the two-port scattering involution `S² = I` beside `weighted_square_energy`;
   - `A* = A⁻¹` exactly for isometries of the declared metric, joined to `dualMap_comp_reverse_order`.

**Acceptance** (fixed before any build). On the existing World fixture, every solved step closes its
ledger (`WaveJointStep::closes`), and join 2's pairing holds exactly on the producing operands. No
learning is claimed by either.

**Recorded failures checked.**
- A located cause carried unrepaired into a new consumer: join 1 names the World boundary as where
  infall stops today and routes its continuation to the owner already planned for it, rather than
  reading the World's coefficients.
- An authored routine standing in for learning: nothing here computes an answer. Emanation and
  infall are readings of existing pairings.
- Text run as the exception: ports, waves and junctions are modality-free.
