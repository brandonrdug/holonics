# The complex parametron is an oriented coupled-LC lattice before phase locking

**Date:** 2026-08-24  
**Scope:** source synthesis, exact Lean exterior return, and engine-facing mathematical deposit;
this record schedules no engine deed and does not move `CONSTRUCTION_STATE.md`.  
**Truth status:** every material claim is graded locally under `canon/EPISTEMIC_GRADES.md`.

## 1. What geometry changes

[proved-standard] A noncircular or lattice-constrained winding is not completely described by the
turn count `N`.  Once electric and magnetic fields can couple multiple conductors, layers, loops,
or cells, the lumped scalar `L` and `C` are receiver faces of distributed self and mutual
coefficients.  After a reference node and finite aperture are declared, an oriented branch--node
incidence map `B`, a capacitive form `M_C`, and an inverse-inductive/stiffness form `M_L` return the
nodal pair

```text
C_node = B^T M_C B,
K_node = B^T M_L B.
```

The undriven linear normal modes solve the generalized relation

```text
K_node v = omega^2 C_node v.
```

When the forms are reciprocal and the capacitive form is positive after its gauge/null population
is removed or grounded, this pair admits the usual real modal analysis.  Complex phasors retain
relative phase in a receiver; they do not by themselves make passive stored energy or the physical
eigenfrequencies complex.

[established-bounded; measured] Samavati, Hajimiri, Shahani, Nasserbakht, and Lee's *Fractal
Capacitors* explicitly exploits lateral as well as vertical electric fields in cross-connected
multilayer metal.  The reported prototype returned `5.5 pF` capacitance, `0.3 pF` bottom-plate
parasitic capacitance, `0.34 nH` series inductance, `1.3 ohm` resistance, approximately `3.7 GHz`
self-resonance, and approximately `23` quality factor at `1 GHz`; it measured a `2.3`-fold
capacitance-density increase.  The same source reports that direction randomization reduces
effective series inductance and that most measured inductance and resistance came from pads,
vias, and stubs.  Geometry therefore changes a coupled `C,L,R,Q` return, not an isolated scalar
capacitance.  Source: `/home/b/Downloads/SAMieeejssc98.pdf`, especially Sections IV--VI.

[proved-standard] Lee et al.'s circuit-lattice construction writes Kirchhoff balance as a
generalized eigenproblem and varies capacitive and inductive couplings to create nodal-line and
Weyl spectra.  Its protected object is the weighted circuit connectivity/admittance law rather
than the Euclidean appearance of its drawing.  Source: *Topological nodal states in circuit
lattice*, <https://arxiv.org/abs/1801.05581>.

[proved-standard] Albert, Glazman, and Jiang construct linear circuit lattices whose normal-mode
matrix is unitarily related to complex spin-dependent hopping.  Real cyclic subnode wiring becomes
complex hopping after the appropriate phase receiver is taken; the complex coefficient is a chart
of a real structured transport, not an additional unexplained substance.  Source: *Topological
Properties of Linear Circuit Lattices*,
<https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.114.173902> and
<https://arxiv.org/abs/1410.1243>.

[proved-standard] Kollár, Fitzpatrick, and Houck use deformable resonators of fixed electrical
length and end coupling to realize non-Euclidean circuit graphs.  Physical curves with very
different planar shapes can present the same tight-binding edge law, while changing the weighted
graph changes the returned band and mode population.  Hyperbolic translations can fail to commute,
so ordinary Bloch diagonalization is not available globally and finite populations are instead
diagonalized directly.  Source: *Hyperbolic Lattices in Circuit Quantum Electrodynamics*,
<https://arxiv.org/abs/1802.09549>.

## 2. What orientation changes

[proved-derived; formal-checked] `HolonicComplexParametron.lean` distinguishes three different
deeds which the phrase "reverse the coil" can hide.  Let `S` be the diagonal population of branch
signs.

```text
pure chart transport:  B -> S B,  drive -> S drive,  M -> S M S
physical drive change: B -> S B while drive is held fixed
physical mutual change:B -> S B while M is held fixed
```

For diagonal branch storage, each branch drop occurs twice and `S^2=I`, so

```text
(S B)^T D (S B) = B^T D B.
```

For a full mutual table the checked covariance law is

```text
(S B)^T (S M S) (S B) = B^T M B.
```

The same transport preserves the full generalized mode relation.  These are exact statements for
arbitrary finite node and branch types; no regular lattice, circular winding, or translation
symmetry is assumed.

[proved-derived; formal-checked] If only incidence is reversed, the fixed mutual response becomes
the response of `S M S` in the original chart.  Diagonal self terms keep their sign, whereas a
mutual term joining one reversed and one unreversed branch changes sign.  Likewise the work pairing
of a fixed drive with a reversed branch changes exactly as the corresponding drive coordinate.
When drive and incidence are transported together, their pairing is unchanged.  Thus sign is not a
free label: it is the oriented returned difference between two declared compositions.

[interpretation] In physical language, reversing the names of a winding's terminals and reversing
every attached drive, receiver, and mutual-coordinate convention changes no device.  Reversing the
winding relative to a fixed pump or fixed neighboring winding changes mutual inductive signs and
mode excitation.  Rotating a sinusoidal drive phase changes its projection onto the eigenmodes and
therefore changes receiver-visible amplitude and phase even when the passive mode frequencies stay
fixed.  Changing the conductor/electrode geometry changes the constitutive forms themselves and can
split degeneracies, localize modes, move resonances, or change band topology.

## 3. Where the complex output comes from

[proved-derived; formal-checked] The new Lean owner retains a complex phase drive

```text
a_b exp(i theta_b)
```

on every addressed branch and its finite superposition before the binary quotient.  A common
half-turn negates the complete superposition exactly.  Relative branch phases are not discarded,
so interference and receiver-dependent cancellation remain present before the existing
`HolonicParametron.lean` theorem restricts the phase population to the two locked sheets and
descends cosine coupling to Ising signs.

[proved-standard] In a fixed passive linear time-invariant `LC` network, lattice irregularity can
create many normal frequencies and complicated mode shapes, but it does not by itself generate new
frequencies from one monochromatic drive.  A nonlinear inductor or Josephson element, a
time-periodic parametric pump, switching, saturation, or another time-varying constitutive law can
mix modes and return harmonics, subharmonics, and Floquet sidebands.  Damping and receiver bandwidth
then decide which of those populations persist and are measurable.

[interpretation] The proposed **complex parametron** is therefore the complete pre-quotient body:

```text
oriented incidence B
  -> distributed capacitive and inductive storage M_C,M_L
  -> complex modal transport and relative phase
  -> nonlinear/time-periodic pump interaction
  -> damping and basin selection
  -> phase/amplitude/frequency receiver
  -> optional two-sheet sign quotient.
```

The classical binary parametron is one receiver of this body.  Multitone or multilevel conduct is
possible only where the constitutive dynamics and receiver preserve it; it is not licensed merely
by drawing a less regular coil.

## 4. Relation to a perceptron, Eros, Athena, and holobrochos

[proved-standard] A passive linear lattice implements a linear modal map.  It is not yet a
perceptron: a perceptron additionally requires a declared weighted receiver and nonlinear decision
or activation.  A coupled parametron population supplies candidate weights through mutual
couplings, a nonlinear phase-lock/bifurcation response, a chronology through its pump, and a
readout.  On the locked two-sheet population the existing Lean theorem proves that cosine coupling
is exactly an Ising pairing, which is the mathematical bridge to majority and threshold-like
receivers.

[historical] The supplied HardForum discussion records useful parametron/majority-logic
intuition, including nonlinear inductors, `2f` excitation, phase states, and historical chronology,
but it is a secondary forum discussion and supplies no constitutive or measurement theorem.
Source: <https://hardforum.com/threads/gateless-majority-logic.1954426/>.

[interpretation] The engine-facing consequence is not a new `Perceptron`, `Circuit`, or
`Parametron` cabinet.  The existing owners already name the needed circulation:

```text
caused branch incidence
  -> local storage/current
  -> coupled transport
  -> returned phase and work differences
  -> dissipative or pumped morphology change
  -> later current through changed standing
  -> receiver face plus reconstruction fibre.
```

This is the precise sense in which the complex parametron can serve as an apparatus realization of
holobrochos and as a candidate physical realization of Eros/Athena transport.  The analogy becomes
a construction theorem only after an engine occurrence binds its incidence, constitutive forms,
pump chronology, dissipation, receiver, residency, energy testimony, and returned morphological
consequence.

[interpretation] Linear diagonalization exposes independent modal coordinates only for the fixed
linear pair and declared boundary.  It is useful for parallel apparatus placement, but the modes
cease to be independent when nonlinear pumping, switching, or morphology changes couple them.
Parallel execution must therefore return an interchange receipt for the complete successor,
lineage, obstruction, and resource state; spectral orthogonality alone is not that receipt.

## 5. Exact formal return and open fibre

[established-bounded; formal-checked] `ElementaryHolonics/Millennium/HolonicComplexParametron.lean`
now returns:

1. oriented branch drops and exact square-one branch signs;
2. invariance of diagonal storage and nodal response under pure branch reorientation;
3. covariance of real drive work, including invariance when drive and incidence travel together;
4. two-sided orientation transport of mutual capacitance/inverse-inductance tables;
5. covariance of both diagonal and full mutual generalized LC mode relations;
6. the exact returned effect of holding the mutual table fixed while incidence changes; and
7. arbitrary complex branch-phase superposition and its exact half-turn negation.

The promoted theorem prints contain no `sorryAx`.

[established-bounded; formal-checked] The validation receipt is separated from physical testimony:

| command | elapsed | exit | code closure and purpose |
|---|---:|---:|---|
| `lake env lean ElementaryHolonics/Millennium/HolonicComplexParametron.lean` | `4.6 s` | `0` | final owner-local elaboration against `HolonicParametron` |
| `lake build ElementaryHolonics.Millennium.HolonicComplexParametron` | `9.8 s` | `0` | module build; `3215` replayed/built jobs, final module built |
| `lake build ElementaryHolonics` | `13.43 s` | `0` | aggregate import closure; `4138` jobs completed successfully |
| `bash tools/gates.sh claim-index named-paths document-law` | `2.62 s` | `0` | three relevant documentary scopes after the one coherent claim-index regeneration |

The complete release receiver `bash tools/gates.sh` was not run: this exterior Lean deposit neither
closes the live Rust roadmap phase nor owns the unrelated dirty engine closure.

[open] The finite owner does not yet derive coefficients from conductor geometry or a Maxwell field
solve; prove modal completeness under positivity; formalize resistance, radiation, thermal noise,
nonlinear ferrite/Josephson response, Floquet transport, or phase-lock stability; or bind the model
to an Eros/Athena device deed.  Those are retained reconstruction fibres rather than facts hidden by
the generalized eigen-receiver.

[open] HD2 remains the active exterior theorem deed.  The coupled-LC station composes with it rather
than replacing it: the normal-mode chart is one receiver of an oriented difference population, and
the nonlinear pump is a time-dependent interaction whose higher differences must retain chronology.
The immediate HD2 obligation remains the recursive scale envelope from the order-three,
order-four, and order-five predecessor ledgers to the quadratic `(2,2,2)` Hodge word and its
inverse-cube mixed mass.
