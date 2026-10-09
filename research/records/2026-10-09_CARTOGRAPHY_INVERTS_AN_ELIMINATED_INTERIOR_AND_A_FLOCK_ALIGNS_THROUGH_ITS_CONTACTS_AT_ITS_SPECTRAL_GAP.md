# Cartography inverts an eliminated interior, and a flock aligns through its contacts at its spectral gap

**Date.** October 9 (the lens: October 2). **Issues.** #73, #148, #62, #63. **Grade.** Lens record.
Each section carries its own grade. The identities of §§2–3 are checked by exact computation; the
laboratory's measurements are cited, not rerun; the joins in §5 are owed. Collective motion is
treated strictly as mathematics: alignment dynamics on a population of movers, with no biological
claim.

## 1. The lens

Brandon, October 2, in one passage:
- **Cartography.** Recover the laboratory's cartography: the idea of using lightning data to model
  the atmosphere and the ground, so as to computationally induce a model of the medium that sustains
  the currents we want to propagate. The same logic holds for visual and acoustic information, since
  multimodality is general.
- **The flock.** Relate the prime wheel, the toroid and the RH work to the laboratory's flock.
  Navigation is the other side of the coin from compression; they act at once and on each other.
  The gaps between the flock's members, read as spectra, shape what the flock does relative to the
  terrain, as charges aligning in the atmosphere do before lightning. He also called this "ant
  integration".

He illustrated squad navigation with a game, as an illustration only; it is not used here.

**The laboratory's work** [historical; source-inspected]. Its records named below were copied into
this repository's records unchanged; the code paths are the private laboratory's.
- **Inverse transport.** The laboratory's `crates/holonic-engine/src/inverse_transport.rs` and its
  [record of July 27](2026-07-27_THE_CUT_CONDITIONS_THE_EDGE_FIBER_THE_COMPLETE_OPERATOR_RETURNS_THE_HIDDEN_CURRENT.md).
  It reconstructs a hidden passive network from clamped potentials `φ` and receiver functionals
  `r`, with response `rᵀ(I + τL)φ`. Each response is one exact affine constraint on the unknown
  conductances, and the law keeps the complete affine fibre of conductances consistent with what
  was returned.
  - On a synthetic six-node world (`15` potential edges, `τ = 1`), the cold run needed `15` queries,
    and a run with `5` inherited cut landmarks needed `10` new ones.
  - Both recovered the `8` positive edges, one component, and cycle rank `3 = 8 − 6 + 1`.
  - The record states that this is a grading instrument, not a model of lightning, and that it
    imports no dataset.
- **Lightning data (RELAMPAGO).** The laboratory read satellite lightning-mapper events from about
  twenty minutes of one December 2018 window through a different law: an atmospheric inverse that
  returns every height in a radiosonde profile whose temperature can carry the reported infrared
  brightness temperature, and never chooses one. Its held-out grade
  ([record of July 28](2026-07-28_THE_CAUSAL_BASIS_OPENS_THE_LOCAL_HORIZON_THE_RETURN_GROWS_THE_RECEIVER_POPULATION.md))
  found that local coordinates do not determine flash membership: `1,786` pairs that returned apart
  were forced together, and `1,401` that returned together were forced apart. The canon's audit
  ([THE_RECOVERED_LAW](../../docs/canon/THE_RECOVERED_LAW.md)) records that all `21,147` spectral
  pairs returned apart, with zero positive relations from the second modality. No lightning
  cartography was demonstrated.
- **The flock.** The [flock record of July 13](2026-07-13_THE_FLOCK_THE_JOINT_AND_THE_FOLD.md) says
  the flock is navigation from the first person, never a swarm algorithm. Its members couple only
  through the shared world: one member's action changes the world, and the world's next reading
  reaches another. There is no shared controller and no direct read of another member's interior.
  - The first realization (July 1, deleted July 2, in the laboratory's history) was six walkers
    homing the primes between two anchors by skipping the multiples of primes already found: a
    sieve. It founded the `168` primes below `1000`.
  - No alignment dynamics was ever built.
- **Ant integration.** The [record of July 11](2026-07-11_THE_CALCULUS_IN_CIRCULATION.md) reads the
  ant as the exact part, `∫f′ = f`, and the winding as the part that is not. The ratified canon
  ([geometry, navigation and weave](../../docs/canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md)) defines
  ant integration as a higher-order consequence emerging from many local carriers handing off
  caused differences, with no carrier owning the whole delivery.

## 2. Cartography inverts the elimination of an interior

### 2.1 What a boundary receiver receives

[proved-standard; formal-checked owners] The forward law is the first line of deposition's loop:
`j = ⋆_Θ dφ` and `∂j = σ`, whose solve is `Lφ = σ` with `L = dᵀ diag(Θ) d` (atlas
`deposition.solve-is-laplacian`, Lean `Objects/Membrane.solves_iff_laplacian`; atlas
`heat.leader-breakdown`; the guide's [deposition](../../docs/ELEMENTARY_OBJECTS.md#8-deposition)).
A receiver family that reads currents only at a boundary `B` (its sensors) receives the response

```text
Λ_Θ = L_BB − L_BI L_II⁻¹ L_IB
```

This is the interior eliminated at its pivot, the series cancellation of the
[junction record](2026-10-09_SERIES_CANCEL_AT_JUNCTIONS_AND_A_PASSAGES_ORDER_COMES_FROM_CHAINING_ITS_GRAINS.md)
§2.1, and the tube's `Λ_DN`. HNN_FORMULA calls this Schur transfer integration by reflection
([reflection, leaders and recursive packing](../../docs/HNN_FORMULA.md#reflection-leaders-and-recursive-packing)).
**Cartography is locating `Θ` from `Λ_Θ`: the inverse of that elimination, which is integration by
reflection read backward.**

### 2.2 The located medium is a class

[proved-standard; checked by exact computation] A star of conductances `1, 2, 3` from three boundary
nodes to one interior node, and a triangle of conductances `1/3, 1, 1/2` on the same three boundary
nodes, have the same response:

```text
Λ = [[5/6, −1/3, −1/2], [−1/3, 4/3, −1], [−1/2, −1, 3/2]]
```

No boundary receiver separates them (the Y–Δ move). For circular planar networks, the response
determines the conductances up to such moves, and determines them exactly for critical networks
(Curtis, Ingerman and Morrow, 1998). The cartographic fibre is the boundary receivers' kernel.
Enlarging the receiver family, with more ports, interior probes or phases, shrinks it. That is the
key record's law: a source is located modulo the kernel of the admitted receivers (atlas
`compression.kernel-greatest-invariant`; Lean `Foundation/CausalRelevance`;
[the key record](2026-10-08_A_KEY_IS_LOCATED_WHERE_ITS_RECEIPTS_RESONATE_AND_A_SECRET_IS_DORMANT_TO_ITS_RECEIVERS.md)).
The canon's [circulating cartographer](../../docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md)
(August 12, historical doctrine; its "terrain" is the older spelling of the medium) already holds
the two halves in words. Its §1 says the map is the continuing morphology that passage changes, and
its §4 says a compression keeps every compatible predecessor until a later consequence separates
them. This section gives the boundary inverse its exact form.

[proved-standard] With access to the interior the inverse is local and exact. For
`L = Σ_(i<j) c_ij (e_i − e_j)(e_i − e_j)ᵀ`,

```text
rᵀ L φ = Σ_(i<j) c_ij (r_i − r_j)(φ_i − φ_j)
```

so each clamped query is one affine constraint on the conductances. This is the laboratory's law,
and its synthetic result is the one in §1.

### 2.3 Lightning is the forward loop, cartography its reading

[agent-inferred; owners named] Breakdown raises conductance on the grown edges, and the return
stroke solves the first line again on the changed constitution (the guide's deposition section,
lightning; atlas `heat.leader-breakdown`, `deposition.square-law-bends-split`). So the medium that
sustains a stroke is the constitution its own currents deposited. Reading that medium from
lightning data is the boundary inverse of §2.1, plural in the way of §2.2. Light and sound have the
same structure: a magnitude-only reading leaves a plural fibre (isospectral drums and homometric
crystals, atlas `fibre.isospectral-homometric`), and phases or arrival times at several receivers
shrink it.

[agent-inferred] **The HNN's cartography is its World model.** Learning a World's constitution from
its returned waves is this inverse. The port-Holon World model that the
[receiving-phase record](2026-10-08_THE_RECEIVING_PHASE_COMPARISON_RETAINS_AN_EXACT_FAMILY_AND_ITS_PROBE_IS_A_DECLARED_LEVERAGE.md)
§7 designs (C1b) keeps an exact affine fibre `c + N k` of states consistent with every actual
incident and returned pair, and one fibre per compatible key. That fibre is the cartographic
fibre. The laboratory's complete affine fibre of conductances is the same construction on a passive
network.

## 3. A flock aligns through its contacts

### 3.1 Members couple only through the world

[definition; agent-inferred; owners named] A flock's members are Holons that couple only through the
shared world, which is the laboratory's own law and the interconnection law (`Holon::interconnect`;
receivers are Holons joined at ports). Eliminating the world's interior between them gives the
members' effective coupling, a Schur complement as in §2.1. Its dynamic form keeps the world's
memory (atlas `resolvent.dynamic-schur`). So the spacing and the medium between members set the
weights of their coupling, and no alignment rule is authored.

### 3.2 Alignment is slip dissipation, at the rate of the spectral gap

[proved-standard; checked by exact computation; formal-checked owners] Velocity alignment
`v̇_i = Σ_j w_ij (v_j − v_i)` is `v̇ = −Mv` with `M = Σ_(i<j) w_ij (e_i − e_j)(e_i − e_j)ᵀ`. That is the
contact material of pairwise slip contacts, whose dissipation is
`⟨v, Mv⟩ = Σ_(i<j) w_ij |v_i − v_j|² ≥ 0` (atlas `contact.material`, `contact.power`). Then:
- the mean velocity is conserved, since `1ᵀM = 0`;
- every other mode decays;
- the slowest decay on a connected flock is at `λ₂(M)`, the algebraic connectivity: the spectral
  gap.

*Example.* Three members on a path with unit weights have `M` with eigenvalues `0, 1, 3`. The step
`v ← (I − M/3)v` takes `(1, 0, −1)` to `(2/3)ᵏ(1, 0, −1)`. It takes `(3, 0, 0)` through `(2, 1, 0)`,
`(5/3, 1, 1/3)` and `(13/9, 1, 5/9)`, keeping the mean `1`.

[agent-inferred] The flock's response to a terrain drive `f` is the resolvent `(s + M)⁻¹ f`, so the
terrain modes that meet the slow eigenvectors move the flock most. That is the precise sense in
which the gaps between members, read as spectra, decide what the flock does relative to the
terrain: the spacing enters through the weights, and the spectrum of `M` decides the rate of
alignment and the modes the flock responds to.

### 3.3 Phase alignment is a lock

[formal-checked owners; agent-inferred reading] For members that carry phases, a pair contact
advancing at integer rates reads zero power exactly at its lock
(`Transport/HelicalPairInteraction.lock_iff_zero_power`). The half-turn sheets of pumped parametrons
are an Ising lock (atlas `parametron.ising-lock`, `Objects/Parametron.drivenPhaseEnergy_binaryPhase`).
Charges aligning in a field before breakdown are a medium's collective lock, which the dielectric
threshold releases into a leader (the deposition loop above).

### 3.4 The prime wheel is a flock on a ring

[proved-standard; checked by exact computation; owners] The `φ(M)` units modulo a primorial `M` sit
on `ℤ/M`. At `M = 30` they are `1, 7, 11, 13, 17, 19, 23, 29`, with gap word `6 4 2 4 2 4 6 2`. The
spectrum of their positions is the Ramanujan sum

```text
Σ_(u ∈ (ℤ/M)^×) e^(2πi k u / M) = c_M(k) = Σ_(d | gcd(M, k)) d μ(M/d)
```

At `M = 30` and `k = 0, 1, 2, 3, 5, 6, 10, 15` it reads `8, −1, 1, 2, 4, −2, −4, −8`. Parseval gives
`Σ_(k mod M) c_M(k)² = M φ(M)`: `240 = 30·8`, and at `M = 2310` it gives `1,108,800 = 2310·480`.
The flock of units hears a terrain mode `k` only through `gcd(M, k)`.

Adding a prime `p` copies the wheel `p` times and cuts the multiples of `p` (atlas
`prime.wheel-copy-cut`, `coupling.twin-wheel`, Lean `Mathematics/TwinWheel`). In the RH work the cut
is the Euler factor's removal, `D_(S∪{p})(s) = (1 − p^(−s)) D_S(s)` (atlas `rh.prime-wheel-euler`;
the paper `mathematics/theorems/prime-wheel-euler-transport.typ`). One step both compresses, since
a cut prunes a whole progression, and navigates, since the gap word is the walk. This is the lens's
compression and navigation acting at once and on each other.

### 3.5 The flock is not a sieve

[definition] The laboratory's first flock was a sieve. Under "No catered machinery" a sieve may
generate a terrain's truth and never stands in for the machine's learning. The wheel's periods are
keys the machine locates: the frames at which a strand resonates
([the encoder record](2026-10-09_THE_HOLONIC_ENCODER_EXPLODES_A_SOURCE_INTO_CO_PRESENT_FRAMES_AND_AN_AXIS_EXPOSES_WITHOUT_AUTHORING_WHEN_NO_RELABELLING_MOVES_IT.md)
§2).

### 3.6 Ant integration is the exact part

[formal-checked owners] The laboratory's ant is the telescoping of exact increments,
`Σ_(k<n) (f(k+1) − f(k)) = f(n) − f(0)` (atlas `jet.telescoping`). A route's adjoint return
telescopes to its ends (atlas `learn.route-deposit`). What does not telescope is harmonic and is
read only on cycles: every cocycle is an exact part plus a unique harmonic one (atlas
`cell.harmonic-unique`). Many members' small exact steps integrate independently of the path. A
flock's collective circling is the harmonic remainder, its winding.

## 4. What the repository already owns

Every owner named in §§2–3 was opened for this record. The ones the joins consume:
- the solve and its Laplacian (`Objects/Membrane`);
- elimination with memory (`resolvent.dynamic-schur`);
- the receivers' kernel (`Foundation/CausalRelevance`);
- the contact material and its dissipation (`contact.material`);
- locks (`Transport/HelicalPairInteraction`, `Objects/Parametron`);
- the wheel's copy–cut (`Mathematics/TwinWheel`, the Euler transport paper);
- the World model's design (the receiving-phase record, §7).

## 5. The joins owed

1. **The cartographic fibre** (Lean, #62). `Λ_Θ` as the Schur complement on the receivers' boundary;
   `Θ ∼ Θ′ ⟺ Λ_Θ = Λ_Θ′` as that receiver's kernel; the Y–Δ witness of §2.2. Its consumer is the
   C1b World model's fibre.
2. **A World with a hidden medium** (#73, #148). Generate a known-truth World with a hidden passive
   network by exact routines. The machine locates its constitution through its own encoding,
   comparisons and deposition, from boundary probes only. The laboratory's inverse law stays an
   exterior reference: inside the machine it would be an authored solver.
3. **The alignment rate as a reading** (Lean, #62). The consensus flow conserves the mean, and one
   step `I − ηM` contracts the rest by `max(|1 − ηλ₂|, |1 − ηλ_n|)`. No current owner consumes it.
   It is stated so that any population whose members couple only through the field can read its
   alignment rate.
4. **The wheel's spectrum** (Lean, #62): the Ramanujan sum as the units' spectrum, and Parseval
   `Mφ(M)`, joined to `Mathematics/TwinWheel`.

**Acceptance for the first loop** (fixed before any build), join 2:
- on unseen probes, the located constitution's boundary response equals the truth's, as exact
  rationals;
- the fibre that remains is reported exactly (for a star world, its Y–Δ class);
- the number of probes is reported beside the cold count of the laboratory's law, as a reference,
  not a target.

**Recorded failures checked.**
- An authored routine standing in for learning: the inverse law and the sieve stay exterior,
  terrain generators or references.
- Seen graded as unseen: the acceptance reads unseen probes.
- Text run as the exception: currents, light and sound share the construction.
- Bits read as progress: the fibre is reported, not a code length.
- A design thought in the programming language: the flock is a Laplacian's spectrum and a wheel's
  residues, not an agent loop.
