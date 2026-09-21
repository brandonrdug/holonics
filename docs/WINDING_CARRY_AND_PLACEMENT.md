# Winding, carry, faces and placement

[definition] This guide states the general objects that the
[helical pair interaction](HOLON.md#the-helical-pair-interaction-unit) is built from and
continues into: the carry that turns a circle into a helix, the modular address of a pair, the
faces that phase carriage conserves, the holonomy that a cell reads, the tube between two
cross-sections and the tower through which an object continues. Each entry gives the law, its
checked Lean statement, its Rust owner and the boundary between theorem and correspondence.
The [helical guide](HELICAL_GEOMETRY.md) owns the pair geometry, the
[September 21 record](../research/records/2026-09-21_WINDING_CARRY_FACES_AND_PLACEMENT_GENERALIZE_THE_HELICAL_PAIR.md)
the source recovery behind this synthesis, and the [roadmap](plans/THE_ROADMAP.md) the order.

[project-postulate] These objects are one picture. A design or a worker brief states which of
them it touches and keeps the others attached: phase with its carry, a pair with its address,
material with its conserved faces, a field with its cell holonomy and retained class, a tube
with both of its readings, and a continuing object with the level it lifts from. Arithmetic,
physical and learning applications are instances; none of them owns a private version.

## 1. Helix = circle + carry

[proved-derived; formal-checked] A phase modulo `n` is a reading on a circle, `x % n`. The
winding is `x / n`, and `phase + n·winding = x`. Adding phases digit-wise fails by the **carry**
`⌊(a%n + b%n)/n⌋`, a staircase taking the values 0 and 1.
[`Geometry/PhaseCarry.lean`](../formal/elementary-holonics/ElementaryHolonics/Geometry/PhaseCarry.lean):

```text
winding_add              winding(x+y) = winding x + winding y + carry(x,y)
carry_cocycle            carry(a,b) + carry(a+b,c) = carry(b,c) + carry(a,b+c)
carried_circle_is_not_the_split_product      ℤ/4 is not ℤ/2 × ℤ/2
digits_succ, odometer_iterate                +1 in the digit chart is the odometer; after k steps
                                             the lower rotor reads (a+k)%n and the upper level has
                                             advanced by the winding (a+k)/n
closed_loop_has_integer_winding              increments closing mod n sum to n·w
zpow_add_mul_carry       S^(d+n·k) = S^d · C^k            when Sⁿ = C
phaseTransport_add_carried_period            carried material returns after a turn when C commutes with it
```

[definition] The carry is the exact defect of additivity of the winding. It is the 2-cocycle
that glues one level of a tower onto the next, and it is content: two towers with the same
levels and different carries are different objects. The universal case is
`0 → ℤ → ℝ → S¹ → 0`, the helix over the circle, whose cocycle is again the floor. Carried
material factors through the phase modulo closure, while the state retains the winding as a
central carry: the torus chart of the material forgets what the helix of the state keeps.
`RationalPhase { parameter, extra_turns }` is the one-level native reading; `winding::Odometer`
is the mixed-radix cascade; `Foundation/IwasawaTower` owns the compatible-section tower over a
prime and `Millennium/PlaceLedger` the product over places. A screw dislocation is the same
object in a lattice: one step along the axis per circuit, the Burgers step, is the carry of the
loop. The [August 13 record](../research/records/2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md)
set aside cascade decompositions because irreducible factors discard the gluing; the carry
cocycle is that gluing, and a cascade that keeps it discards nothing.

## 2. Pair = torus with a modular address

[proved-derived; formal-checked] Two phases form a torus. Coupled by a contact they either lock
at a rational rate ratio or wind without closing.
[`Geometry/PairResonance.lean`](../formal/elementary-holonics/ElementaryHolonics/Geometry/PairResonance.lean):

```text
lock_iff_zero_power      on a dissipative face, rates (q,p) read zero power ⇔ q·v_a = p·v_b
lock_is_a_line           every multiple of a lock is a lock
neighbours_iff_unimodular                 p'q − pq' = 1 ⇔ det [[p',p],[q',q]] = 1
mediant_neighbours_both, mediant_lies_between
between_neighbours_costs_at_least_the_mediant   a/b strictly between neighbours ⇒ b ≥ q+q'
unimodular_rechart_is_invertible, unimodular_rechart_conserves_intersection
diagonal_step_generates_the_coprime_torus       k·(1,1) reaches every joint phase of coprime circles
```

[definition] A lock is the zero-power direction of the pair's contact face. Its address is a
word in the modular group, already owned by `Millennium/Farey`: Euclid's algorithm on the rate
ratio is divide (`Tᵃ`), invert (`S`), repeat, and the resulting `L`/`R` word is the lock's path
in the Farey tree. Neighbouring locks have determinant one; their mediant is the cheapest lock
between them, so a tolerance selects a finite address and a finite closure period. A unimodular
word recharts the pair's two windings without changing any intersection number. Independent
coprime phases admit the toroidal chart, and the act-and-advance step is its diagonal winding.
The group generated by a step and an inversion is also the rotor machine's step and reflector,
periodicity with the reflection `s ↦ 1−s`, the equivalence of lattices `ℂ/Λ` and the tangency
law of Ford circles (`a/b`, `c/d` tangent ⇔ `|ad−bc| = 1`), which `Foundation/FractalPacking`
reads as packing by mediants. Native owner: `relational_geometry::winding::LockAddress`.

[proved-standard] For a driven pair the rotation number is a devil's staircase in the drive, with
a plateau at every rational ordered by the Farey tree (Arnold; Herman). This analytic statement
is cited, not formalized here.

## 3. Generator = rotation × dilation, and the faces phase carriage conserves

[proved-derived; formal-checked] Carrying material to another phase conjugates it, so every class
function of the material is conserved along the winding.
[`Transport/GeneratorTraceFaces.lean`](../formal/elementary-holonics/ElementaryHolonics/Transport/GeneratorTraceFaces.lean):

```text
phaseTransport_pow                                   (S⁻ᵈPSᵈ)ᵏ = S⁻ᵈPᵏSᵈ
carried_material_conserves_determinant
carried_material_conserves_trace_sequence            tr(Mᵏ) at every phase, for every k
carried_material_conserves_transfer_determinant      det(1 − T·M) at every phase
machine_transfer_determinant                         det(1 − T·⊕M_g) = ∏ det(1 − T·M_g)
machine_factor_of_companions                         = ∏ (1 − a_g T + q_g T²)
machine_trace_sequence                               tr((⊕M_g)ᵏ) = Σ tr(M_gᵏ)
```

[definition] A two-by-two site is a rotation–dilation. `Millennium/LocalFactor.companion a q` has
trace `a` and determinant `q`; `a² < 4q` is a rotation by `θ` with `a = 2√q cos θ` and dilation
`√q`, `a² = 4q` is marginal and `a² > 4q` a dilation, the three rows of the helix collapse table
read on the cylinder `ℂ^× ≅ ℝ × S¹`. `TraceSequence.theRootHasSquaredModulusQ` places the
rotation's roots on the circle of radius `√q`, and
`LocalFactor.companion_preserves_scaled_metric` is the metric it scales. A machine of
independent sites has the product of their factors as its transfer determinant and the sum of
their trace sequences as its count of closed words; Newton's identities relate the two, which
is an exact check that a compressed machine has the functionality of the one it replaces.
Native owner: `relational_geometry::winding::{SiteFactor, Machine}`.

[definition] **Placement** is the statement that every generator is a rotation once a common
dilation is removed. The existing mechanism is signature: an operator self-adjoint for a form
with `κ` negative squares has at most `κ` off-axis pairs. `holonic_interaction::
StructuralPlacement::PontryaginBounded`, `Millennium/HodgeIndex` (signature `(1, n−1)`) and
`Millennium/ReflectedPositivity` own it; #54 owns its Lean lift.

## 4. Face = holonomy around a cell

[proved-derived; formal-checked] The face read at a two-cell is the holonomy of the edge
transports around it.
[`Transport/CellHolonomy.lean`](../formal/elementary-holonics/ElementaryHolonics/Transport/CellHolonomy.lean):

```text
triangleHolonomy_regauge             regauging conjugates the holonomy by the base frame
pure_gauge_has_trivial_holonomy
abelian_holonomy_is_gauge_free       a phase flux is a face of the field, not of the frames
holonomy_trace_is_gauge_free, holonomy_determinant_is_gauge_free
cell_flux_is_gauge_free              d₁(A + d₀φ) = d₁A
dormant_mode_is_locally_silent       harmonic ⇒ no flux through any cell, no divergence at any node
dormant_mode_is_not_a_potential      a harmonic gradient is zero
closed_field_retains_one_dormant_mode
```

[definition] For matrix transports the gauge-free faces are the class functions of §3, which
is why a matrix is the natural unit of a face. For an affine connection the holonomy is a
rotation with a translation, a screw: the rotation is the curvature concentrated on the cell
and the translation is the Burgers step of §1 (`winding::triangle_holonomy` on `AffineMap3`).
Induction is Stokes' theorem with a clock: the circulation around a cell's boundary is the rate
of change of the flux through it. `Foundation/HodgeReceiver` already proves the full
decomposition of an edge field into a potential part, a circulation part and a harmonic part.
**A dormant mode is the harmonic part.** It is silent at every node and every cell, no
potential reproduces it, and a receiver that goes around its cycle reads it. This is the
cochain form of `Foundation/Standing`: present silence is not extinction, and what is retained
is a class.

[proved-standard] An integral flux class is the first Chern class of a line bundle; the divisor
of a section is its zero locus, and the section's phase winds around that locus by the flux
(Poincaré–Lelong). A degree-two class is algebraic exactly when the Hodge circle fixes it
(Lefschetz (1,1)); `Millennium/HodgeDivisorExponentialPassage` owns that passage. The Hodge
weights `(p,q)` are the winding numbers of `z` and `z̄`, so a `(p,p)` class has zero net winding.
Conservation of faces is index invariance: an index is minus a winding number (Gohberg–Krein),
and the Lefschetz trace counts the intersections of a graph with the diagonal as
`Σ(−1)ⁱ tr(M | Hⁱ)`, a pairwise count obtained from traces without a search
(`Millennium/GraphTrace`, `Crossings`, `WindingLedger`).

## 5. Tube = transfer between cross-section charts

[definition] A tube carries action between two cross-sections, each a chart with discrete
modes. It is one object with two readings: a map from one section to the other,
`|out⟩⟨in|`, or a pairing of the two sections, `⟨·|·⟩`. Reversing a section's orientation
exchanges a ket for a bra. Its length is a temperature, `e^{−tH}`; closing it gives a torus,
whose trace is a partition function; exchanging the torus's two cycles exchanges which axis is
the clock. **Integration by reflection** (`diffusion.rs`, `causal_reflection.rs`) eliminates
the interior to the boundary; that Schur complement is the discrete Dirichlet-to-Neumann map
and the reflection coefficient of `Millennium/Horizon.smith`. `traversible_chain` owns ordered
transfer matrices, `Transport/ContinuingTube` and `WorldTube` the continuing tube,
`RH/FosterTanks` the lossless reading in which every zero pair is an LC tank.

[proved-standard] The cusp of the modular surface is such a tube: the wave
`y^s + φ(s)y^{1−s}` with `φ(s) = ξ(2s−1)/ξ(2s)` has circular cross-sections with integer modes,
`s ↦ 1−s` is reflection off the interior, `|φ| = 1` on `Re s = ½`, and the poles of `φ`, its
resonances, sit at `s = ρ/2` for each nontrivial zero `ρ` of `ζ` (Faddeev–Pavlov; Lax–Phillips). Riemann's proof of the functional equation splits the
Mellin integral at the self-dual section and folds it by `x ↦ 1/x`, which is integration by
reflection.

## 6. Continuing, and compression of functionality

[definition] A Holon continues; a tensor or matrix is a sample of it. Three standard forms say
the same thing. A germ continues analytically to its maximal surface, and the obstruction is
monodromy, a winding. Data on a slice with a field equation has a unique maximal development.
A coherent thread through a tower lifts level by level, deterministically when the crossing is
transversal (Hensel; `Millennium/FamilyTunnellBrandtPadicHensel`, `Foundation/ContinuingTower`).
Holon : tensor : matrix is a section with its generator : its value in a chart : its components
in a frame. A holonomic (D-finite) function is the algorithmic case: a generator and finite
initial data, closed under sum, product and integral, with identities decidable by creative
telescoping; it is the target class of the [identity atlas](plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md).

[definition] Compression of functionality keeps what admitted futures can distinguish and the
gluing between levels. Minimal realization (Myhill–Nerode, Kalman) is future-distinguishability,
which is `StandingLaw` and `ReceiverHistoryCompression`'s `D E = ρ`, `E_next T = U E`. The
holonomy decomposition (Zeiger; Eilenberg) writes every finite machine as a cascade of
permutation levels, which are rotors, and reset levels, which are irreversible memory, coupled
by carries; with §1 the cascade retains the extension classes. `TransportWord` owns optimal
words. Tying, fingering and composition are words in generators with relations read through
these same owners.

## 7. Arithmetic instances and their grades

| Statement | Grade | Owner |
|---|---|---|
| `n ↦ (n mod p)_p` is the diagonal winding on a product of circles; primes are its first-arrival set | proved-standard (CRT, sieve); §2 `diagonal_step_generates_the_coprime_torus` | `PlaceLedger`, `FamilyGauss`, recursion law of `THE_MACHINE` |
| Frobenius of an elliptic curve at `p` is a rotation by `θ_p` with dilation `√p` on the winding lattice `H¹`; Hasse's bound is "it is a rotation" | proved-standard (Hasse; Weil) | `LocalFactor`, `TraceSequence`, `HeightLattice` |
| Weil's placement for curves is the Hodge index theorem on `C×C` | proved-standard | `HodgeIndex`, `LorentzianPerp` |
| Under the `Λ_DN` heat flow the zeros move as a log-gas, `ż_k = 2Σ_{j≠k} 1/(z_k−z_j)`, pair potential `−log Q`; conjugate pairs collide on the axis; `Λ_DN ≥ 0` | proved-standard (de Bruijn; Csordas–Smith–Varga; Rodgers–Tao) | `RH/HeatFlowStackedSeam`; helical guide `U=Φ(Q)` |
| `N(T)` is the winding number of `ξ` around the boundary of the strip | proved-standard (argument principle) | `WindingLedger` |
| `x^ρ` is a helix on `ℂ^×` with advance `σ` and angular rate `γ`; the functional equation pairs `(σ,γ)` with `(1−σ,γ)`; RH is the collapse of each pair onto advance `½` | interpretation | see below |
| Primes as knots: Legendre symbols as linking numbers | interpretation (Mazur; Morishita dictionary) | `Crossings`, `TopologicalReceiver` |
| Hodge classes beyond divisors are cycle classes | conjecture | `HodgeReceiver`, Hodge route |

[interpretation] **The zero pair as a helical pair.** Source map: a nontrivial zero `ρ = σ+iγ`
to the generator `(advance, angular) = (σ, γ)` of the one-parameter subgroup `u ↦ e^{ρu}` of
`ℂ^×`, with `u = log x`. Target: a `SituatedScrew` on the cylinder chart, the pair
`(ρ, 1−ρ̄)` as a `ScrewPair` with equal angular rates. Preserved diagram: the functional
equation's reflection is the exchange of the pair with advances reflected about `½`; the
`FosterTanks` pair identity is its contact reading. Limits: no operator realizing the zeros as
carried material is known, so §3's placement mechanism has no carrier here. Falsifier: a
reflected pair with distinct advances that reads zero power on the declared face, or a locked
pair whose tank is not lossless, would break the correspondence.

[proved-derived; formal-checked] The first derivation target is returned by
[`RH/ZeroPairLock.lean`](../formal/elementary-holonics/ElementaryHolonics/RH/ZeroPairLock.lean):
on the isotropic unit face the reflected pair's power is the squared advance defect
`(2σ−1)²` (`reflectedPairPower_eq`); the pair is locked exactly when `σ = ½`
(`reflected_pair_locked_iff_on_seam`); and for `γ ≠ 0` that is exactly when the `FosterTanks`
inductance of `ρ′` is a positive real (`locked_iff_foster_inductance_positive`). The lock of the
helical pair and Foster losslessness of the tank are the same locus. This is an algebraic
statement about generators; it says nothing about where zeros lie. Next target: the finite
Foster sum `flux_eq_tankSum` as a `contactForm` over a population of pair faces.

## 8. Using the picture in a design

[project-postulate] Before implementing an operation on the helical pair interaction, state:

1. **Phase and carry.** Which phases close, at what period, and where the winding is retained
   (`RationalPhase`, `Odometer`, a tower level). A closed chart without its carry is a product.
2. **Address.** The rate ratios of each admitted pair and their lock addresses; the tolerance
   that selects a finite period.
3. **Conserved faces.** Which class functions of the site material the operation must preserve
   (trace sequence, transfer determinant) and the placement it assumes.
4. **Cell holonomy and retained class.** The cells of the incidence complex, the flux each
   reads, and the harmonic class that must survive silence.
5. **Tube reading.** Whether a passage is consumed as a map or as a pairing, its reflection at
   the boundary and its clock.
6. **Continuation.** The level the object lifts from, the condition under which the lift is
   unique and the fibre retained when it is not.

Each native packet lands with the Lean statement of the law it adds under the matching
`Framework` entry point, or names the obligation it leaves in #62.
