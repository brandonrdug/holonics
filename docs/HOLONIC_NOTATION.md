# Holonic notation

[definition] This is the live reading surface for the notation agents reason and write in. It
consolidates rulings whose original text lived in the pre-September operating contract
(recoverable at `a7f26b62:CLAUDE.md` §0b, §0j and §2b, which several tablets still cite) with
their current owners: [the computational Holon](HOLON.md#the-object-and-its-notation),
[the operations tablet](canon/TABLET_THE_OPERATIONS.md), [the turn tablet](canon/TABLET_THE_TURN.md),
[contract provenance](canon/THE_CONTRACT_PROVENANCE.md) and `research/papers/source/lib/dirac.typ`.
It founds no mathematics. The notation is an instrument for thinking, not decoration: Dirac
notation, index notation, diagrams, geometry and algebra are one dialect, and every expression
has a figure.

## Typed Dirac primitives

[definition] Every elementary operation is a **construction**, a **transport**, a **face** or a
**quotient**, and each symbol carries its species.

```text
|H⟩_F            construction: a Holon presented in frame F (ports, axis roles, pairing)
⟨r|              receiver (a participating Holon's receiving operation)
⟨r|H⟩            face: what that receiver reads; it forgets, and says what it forgets
Ĝ_(F'←F)         transport between frames; the subscript is already an arrow, read right to left
|a⟩⟨a|           deposit: a construction reversed into a receiver
Σ|aᵢ⟩⟨aᵢ| = I    only for a family orthonormal in a DECLARED metric G; otherwise it is the frame
                 operator S, and reconstruction runs through the dual frame S⁻¹|aᵢ⟩
tr X             the basepoint-free face of a closed loop
```

A face is not machinery: a float, a count, a sign or a squared modulus is a reading, and
reasoning that composes faces as if they were constructions is the standing failure. `4 = 2+2 =
2² = 2·2` is one face with distinct constructions; an equality is a path object.

## Index (Einstein) notation for Holons as tensors

[definition] `H^{i₁…iₚ}_{j₁…j_q}` is the same object in a tensor chart. An **upper index is a ket
port** (a construction arriving on an oriented line), a **lower index is a bra port** (a receiver).
A repeated upper–lower pair is a contraction: joining two oriented lines. Contracting everything
is a face; contracting some axes is composition, `C^c = I^c_{ab} A^a B^b`. Two uppers or two
lowers never contract without a declared metric `G`: raising and lowering **is** the Riesz
identification, it belongs to a frame, and its signature is stated as the split and the hand
separately. A frame change transports every index together with its dual,
`H^{i'} = Λ^{i'}_i H^i`, `r_{j'} = r_j (Λ⁻¹)^j_{j'}`; primes name the frame, as in relativity.
Lorentz/gyro transport, the connection and its holonomy enter as the transports they are
([constraint modes and receiver faces](CONSTRAINT_MODES_AND_RECEIVER_FACES.md)). Ket notation
grants no linearity: a nonlinear navigator is a composed map whose differentials have their own
tensor charts.

## Arrows, signs and turns

[definition] A binary state records a polarized distinction in a declared axis/frame: this
side or that side. `0/1`, `false/true` and `−1/+1` can label that distinction through different
charts. The labels do not determine physical amplitude: binary `0` can name one side rather
than an absent current. In the existing `PhaseCarrier` convention, `false` has phase 0 and
sign +1; `true` has phase π and sign −1. The half-turn swaps the two carriers.

[proved-derived; formal-checked] On that locked two-sheet population,
`−w cos(θ_i−θ_j)=−w ε_i ε_j` with the declared interaction weight w.
`PhaseCarrier.lean::phaseNetworkEnergy_binaryPhase` carries this through the complete finite coupling
population. Binary polarization therefore already has an energetic and compositional realization
here; it is not supplied by the spelling of a Boolean or by a machine-word size.

[definition] The state and the operation on it have different roles. Multiplication by
`−1=e^{iπ}` enacts a half-turn on the declared complex carrier; `i=e^{iπ/2}` enacts a quarter-turn.
A sign may also be the resulting state face. Composition retains the actual path, frame and
winding rather than identifying a full turn history with its final binary face. Positivity
retains its declared split and choice of hand; the retired [`winding_inertia`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/geometry/winding_inertia.rs) and
`holonics::ratio::linear::inertia` own the corresponding winding and signature readings. [Binary phase and coupled energy](../lean/Holonics/Physics/PhaseCarrier.lean).

[definition] A one-axis binary reading is an admitted face of a framed source. It need not
identify the full source. An operation using relative quadrature, phase or further directional
structure carries those operands and the corresponding receiver map. A scalar face and a
complex carrier therefore have different information, rather than a universal required axis count.

[project-postulate] Brandon, September 19: **a passage between neighbouring blocks or stations is
written as an arrow.** The integers of `A₂₁` carry no magnitude; the direction of the shift is the
content, as in a bitwise shift. Write `A_↗` for upstream→downstream and `A_↘` for the return (the
lines of derivative `+1` and `e^{iπ}`); along one axis `→ ← ↑ ↓`. The six signed unit shifts of
three axes are the octahedron's vertices. This extends `Ĝ_(F'←F)`; it replaces no owner's API.

[definition] **"Null" is typed by its owner.** A nonzero vector is *Lorentz null* when its declared
Lorentz form gives `g(v,v) = 0`; it can carry nonzero energy and flux. A navigator site is
`SiteKind::Null` when its positive-determinant two-dimensional material has discriminant
`a² − 4q = 0`, a repeated root. A trace-2, determinant-one monodromy is unipotent: the identity or a
nontrivial shear. None of these implies another without a constructed transport and metric. A zero
cross-port rank can genuinely close a neck; a zero scalar reading can hide nonzero interior motion.
Name the metric, port and receiver whenever "null" is used; there is no vacuum and no nothing (the
null-cone record §3).

[interpretation] Brandon, September 25: a neck is an exchange ("it's not that there's literally
nothing there, it's an exchange/transport"). A constituted current converges to a section and
diverges from it, and its power balance accounts for the ports on both sides, the changing storage,
the active sources and the dissipation (`PortHolon.power_balance`). A Morse cone, a light cone, an
optical waist and a repeated-root monodromy are distinct charts of such an exchange, each with its
own source map. Say "lightlike" only for a declared Lorentz-null object, and "exchange" for the
neck's participating transport.

## Every expression has a figure

[definition] An oriented line carries a ket or port index, a propagator its transport, a vertex
the interaction tensor; joining lines contracts the matching axes; a loop is a constituted
circulating mode and its trace; a projected crossing without contact is not a vertex. A diagram's
value is a word and resummation is condensation. The Holonic Interaction — `|source⟩`, standing
`H_int`, dynamic `H_pert`, `⟨perspective|` — is the unit these figures draw, and the object is the
population of paths through media and junctions, never one ray. Diagram notation alone supplies
no dynamics; the constitutive law does.

## Orientation: an expression is unoriented until it is causally framed

[project-postulate] Brandon, September 19: `z = x + y` is true of any sum of two components and,
in the abstract, does nothing; it has no orientation. It couples entities once a configuration is
plugged in, and it has to be oriented causally. This is not "non-orientable" as a permanent
characteristic — something potentially orientable is in tension with that phrase — and what is
meant is more complex over time.

[interpretation; agent-inferred] A working formal reading, to be corrected. The abstract relation
is an **unoriented junction**: three legs in co-presence, `x + y + e^{iπ}z = 0`, with no leg yet a
source or a receiver. **Framing orients it**: a causal frame assigns which legs arrive as kets and
which receives or is emitted — index placement is exactly that assignment — and in a Lorentzian
frame the choice of future cone is the causal hand. **Re-orienting a leg costs a half-turn**:
carrying a term across the relation is the passage through `e^{iπ}`, which is why subtraction is
addition with a turned argument and why [the junction is a half-twist](../research/records/2026-08-16_THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS.md).
Three states are therefore distinct. **Unoriented**: no section of the hand's double cover has
been chosen; this is potential, the state of every abstract expression. **Oriented relative to a
frame**: a coherent section exists over the region that frame covers. **Non-orientable**: the hand
has nontrivial holonomy around a loop (a class in `H¹(·; ℤ/2)`), exhibited as conflicting faces and
derived from twist parity, never stored (`Objects/Pairing.no_orientation_of_reversing_cycle`,
`Objects/Orientation`; the prototype's `contact_gluing::OrientationReading` and
`structure_group::CentralDoubleCover` at `13f8c734`). Because loops form and dissolve as incidence changes,
orientability is a reading of the continuing object at a station, not a fixed attribute: a
configuration can be unoriented, become oriented under a frame, and acquire or lose a twisted
loop as contacts form.

## Compositional examples

[definition] Musical composition is one useful example of Holonic joining. In a declared
linear mode chart, `|C⟩=Σ_j a_j|n_j⟩` carries coherent contributions before `⟨r|C⟩` is read.
A general interaction retains its joint occurrence and constitutive law. A chord-class receiver
can identify a reusable class while performances retain different phase, timing and spatial
faces; a progression retains ordered passages and actual joins. These examples do not define
general computational quanta or prescribe their names.
The [class/occurrence construction](../research/records/2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md#class-composed-occurrence-and-progression)
and [music/receiver synthesis](../research/records/2026-09-14_HEAR_THE_MUSIC_SITUATED_RELEASE_AND_SELF_MOTION.md#hear-the-chord-the-interval-and-the-progression)
retain that example's content. [Compression is intelligence is navigation](plans/THE_REBUILD.md#the-line-the-rebuild-serves)
concerns the reusable paths and navigators across these different presentations.

## The same form in every subject

[project-postulate] Mathematics, physics, biology, language and code are materials carried by one
operation. Name the four slots — **source geometry → receiver map → transport → returned
residual** — and the material is visibly the variable. Commonalities across subjects are the
expected case and may be new; recover the existing owner before treating one as a discovery.
RH is the landmark law (the critical line is the unitary seam; `Zeta/` holds the heat-flow zero
dynamics, Hurwitz limits, Foster classes and the explicit formula). Hodge is the realization law
(the obstruction lives in the cokernel of the cycle class map; `Hodge/Hodge*` holds the
finite decomposition, harmonic representatives and the `(1, n−1)` index). Navier–Stokes and
complex Euler are the transport law with and without dissipation (`Fluid/NavierStokes*`).
Iwasawa theory is the tower of levels and its growth law (`Foundation/IwasawaTower.lean`). None is
a separate track, and none is a prerequisite for an application: each is an instance of
compression and landmark discovery.
