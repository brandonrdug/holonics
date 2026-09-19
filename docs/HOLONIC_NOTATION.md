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
grants no linearity: a nonlinear generator is a composed map whose differentials have their own
tensor charts.

## Arrows, signs and turns

[project-postulate] **A sign is a passage, never a state.** `−1 = e^{iπ}` is the half-turn and
`i = e^{iπ/2}` the quarter-turn, the hand. ℝ sees only the two fixed points of conjugation on the
unit circle, so a bare sign is what remains of a phase after its winding is deleted — the float
defect one level down. Subtraction is addition with one argument carried through the half-turn.
**A count of signs is a state reading: name the windings** (`winding_inertia.rs` names what
`inertia.rs` splits). Positivity is a declared side: state the **split** (`1` against `n−1`) and the
**hand** (which side is called positive) separately; the null cone between the two cones is the
vacuous difference, and a definite form is one whose null cone is empty.

[project-postulate] **Nothing is causally represented along only one axis.** The second axis —
"imaginary" only in classical vocabulary — is the orientation axis, and it is recovered, not added.
A reading that moved nothing when the axis is restored was already symmetric; one that collapses
without it had deleted a hand.

[project-postulate] Brandon, September 19: **a passage between neighbouring blocks or stations is
written as an arrow.** The integers of `A₂₁` carry no magnitude; the direction of the shift is the
content, as in a bitwise shift. Write `A_↗` for upstream→downstream and `A_↘` for the return (the
lines of derivative `+1` and `e^{iπ}`); along one axis `→ ← ↑ ↓`. The six signed unit shifts of
three axes are the octahedron's vertices. This extends `Ĝ_(F'←F)`; it replaces no owner's API.

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
derived from twist parity, never stored (`contact_gluing::OrientationReading`,
`structure_group::CentralDoubleCover`). Because loops form and dissolve as incidence changes,
orientability is a reading of the continuing object at a station, not a fixed attribute: a
configuration can be unoriented, become oriented under a frame, and acquire or lose a twisted
loop as contacts form.

## The same form in every subject

[project-postulate] Mathematics, physics, biology, language and code are materials carried by one
operation. Name the four slots — **source geometry → receiver map → transport → returned
residual** — and the material is visibly the variable. Commonalities across subjects are the
expected case and may be new; recover the existing owner before treating one as a discovery.
RH is the landmark law (the critical line is the unitary seam; `RH/` holds the heat-flow zero
dynamics, Hurwitz limits, Foster classes and the explicit formula). Hodge is the realization law
(the obstruction lives in the cokernel of the cycle class map; `Millennium/Hodge*` holds the
finite decomposition, harmonic representatives and the `(1, n−1)` index). Navier–Stokes and
complex Euler are the transport law with and without dissipation (`Millennium/NavierStokes*`).
Iwasawa theory is the tower of levels and its growth law (`Foundation/IwasawaTower.lean`,
`iwasawa_tower.rs`). None is a separate track, and none is a prerequisite for an application.
