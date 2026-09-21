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
levels and different carries are different objects. The universal-cover case is
`0 → ℤ → ℝ → S¹ → 0`; choosing a phase section produces the floor cocycle. Carried
material factors through the phase modulo closure when the carried-period element commutes
with that material, while the state retains the winding: the torus chart of the material forgets what the helix of the state keeps.
`RationalPhase { parameter, extra_turns }` retains an exact Cayley circle point and extra turns
per passage: `parameter` is a tangent half-angle, not a turn count or rational angular rate.
Its `chart_winding`/`lifted_winding` require a separately checked finite closure. A rational
Cayley point need not close at any finite period. `winding::Odometer` is the mixed-radix cascade
for declared finite levels; a nonclosing phase retains its exact transport or enclosure and
unreduced lift instead of acquiring an invented radix. `Foundation/IwasawaTower` owns the
compatible-section tower over a prime and `Millennium/PlaceLedger` the product over places. A screw dislocation is the same
object in a lattice: one step along the axis per circuit, the Burgers step, is the carry of the
loop. The [August 13 record](../research/records/2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md)
set aside cascade decompositions because irreducible factors discard the gluing; the carry
cocycle supplies that gluing in the cyclic extension example. A general cascade retains its
full dependency and decoder maps as in §6.

## 2. Pair = torus with a modular address

[proved-derived; formal-checked] Two periodic phase charts form a torus. At a supplied contact configuration, a rational
synchronized direction satisfies `q·v_a=p·v_b`. Periodic closure and dynamical attraction to a
locked orbit are further properties of the actual motion, not consequences of this local equation.
[`Geometry/PairResonance.lean`](../formal/elementary-holonics/ElementaryHolonics/Geometry/PairResonance.lean):

```text
lock_iff_zero_power      with positive weight and null-definite response, zero power ⇔ q·v_a = p·v_b
lock_is_a_line           every multiple of a lock is a lock
neighbours_iff_unimodular                 p'q − pq' = 1 ⇔ det [[p',p],[q',q]] = 1
mediant_neighbours_both, mediant_lies_between        cross inequalities; ratio reading needs positive denominators
between_neighbours_costs_at_least_the_mediant   a/b strictly between neighbours ⇒ b ≥ q+q'
unimodular_rechart_is_invertible, unimodular_rechart_conserves_intersection
diagonal_step_generates_the_coprime_torus       k·(1,1) reaches every joint phase of coprime circles
```

[definition] A kinematic lock is a zero-slip direction of the pair. For symmetric `D_f⪰0` and
positive weight, zero power means `D_f J_f u=0`; it implies zero slip only when `D_f` has no
null direction on `im J_f`. `pair_lock` checks the kinematic equation at the retained initial
configuration, independently of material. A persistent lock must satisfy it along the admitted
trajectory. Zero velocities, a stationary partner and opposite signs retain their kernel
directions even though `LockAddress` currently represents only strictly positive ratios.
A positive rational lock's address is a word in the modular group, already owned by `Millennium/Farey`: Euclid's algorithm on the rate
ratio is divide (`Tᵃ`), invert (`S`), repeat, and the resulting `L`/`R` word is the lock's path
in the Farey tree. Neighbouring locks have determinant one; their mediant is the cheapest lock
between them, so a nonempty rational tolerance interval has a least-denominator representative.
The interval contains infinitely many rational addresses: a finite candidate sweep also needs a
declared denominator/word bound. The denominator is a period only in a declared normalized
commensurate clock chart. A rate approximation retains its phase-drift and receiver-error
bound over the engagement horizon; it does not establish exact physical closure. A unimodular
word recharts the pair's two windings without changing any intersection number. Independent
coprime phases admit the toroidal chart, and the act-and-advance step is its diagonal winding.
The modular step/inversion representation and a finite rotor step/reflector each supply
ordered group actions; identifying them requires a homomorphism respecting their relations.
An arbitrary reflector is not a modular inversion merely because both are involutive. The
Farey determinant also gives the tangency law of Ford circles (`a/b`, `c/d` tangent iff
`|ad−bc|=1`), read by `Foundation/FractalPacking` as packing by mediants. Native owner: `relational_geometry::winding::LockAddress`.

[interpretation] Mode-locking staircases provide an analytic instance for specified driven
circle-map families ([Alsedà–Borrós-Cullell](https://arxiv.org/abs/2012.03340)); transferring that
instance to an HNN pair requires its actual evolution and rotation-number map. The first
obligation is to exhibit a stable periodic orbit and its drive interval. The rigid rotation
family `x ↦ x+α` has rotation number `α` and no plateaus, refuting a universal staircase claim
for driven pairs. The local lock theorem above remains independent of that analytic question.

## 3. Generator faces, rotation–dilation and placement

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

[definition] A real two-by-two material has trace `a` and determinant `q`.
`Millennium/LocalFactor.companion a q` realizes those faces. When `a²<4q` it is similar over
ℝ to a rotation scaled by `√q` in an adapted metric; `TraceSequence.theRootHasSquaredModulusQ`
and `LocalFactor.companion_preserves_scaled_metric` own these readings. `a²=4q` permits a
nontrivial Jordan shear; `a²>4q` gives distinct real eigenvalues, including negative or zero
ones when admitted. The native `SiteKind::{Rotation,Marginal,Dilation}` names these discriminant
branches, not a universal Euclidean polar decomposition. A `SituatedScrew` does not determine
a `SiteFactor`: the model must supply the represented two-dimensional material block. Larger
or coupled blocks retain their own operator and faces.

[proved-derived; formal-checked] For **block-diagonal** sites, the transfer determinant is the
product of their factors and the trace sequence is the sum of theirs. Native owner:
`relational_geometry::winding::{SiteFactor,Machine}`. Trace powers count weighted closed walks
when the material is an adjacency representation; for a general matrix they are trace readings.
Newton's identities check spectral consistency. They do not prove source/receiver equivalence:
`I₂` and `[[1,1],[0,1]]` both have trace powers `2` and transfer determinant `(1−T)²`, but the
receiver `(1,0)` after one step from `(0,1)` reads `0` and `1`. Compression additionally supplies
`D E=ρ` and `E_next T_g=U_g E` for the admitted actions, or retains the separating remainder.
A coupled HNN may use the site product as the uncoupled reference; its full operator generally
has a different determinant.

[conditional] **Placement** asks whether specified spectral modes lie on a circle after a
common positive dilation, or on an axis in a generator chart. The applicable operator,
pairing and bridge between these readings must be declared. For a nondegenerate form `G` with
signature `(p,q)`, the existing `StructuralPlacement::PontryaginBounded` arm requires
`A*G+GA=0` and bounds open-right-half-plane modes by `min(p,q)`; its spectral symmetry is
`λ ↦ −conj λ`. `Millennium/HodgeIndex` and `ReflectedPositivity` give related signature
constructions, and #54 owns the corresponding Lean lift. A general dissipative
`A=(Ω−M_contact)G` does not satisfy that equality. Signature alone neither makes it a rotation
nor transfers the conservative bound to all of its off-axis modes. The exact rate form
`A*G+GA=−2G M_contact G` selects the applicable arm.

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
closed_field_retains_one_dormant_mode (existence); closed_field_retains_unique_harmonic_mode (uniqueness)
```

[definition] For matrix transports the gauge-free faces are the class functions of §3, which
is why a matrix is the natural unit of a face. For proper rigid edge transports the holonomy lies in `SE(3)` and admits a screw reading.
`winding::triangle_holonomy` accepts general affine maps, including shear and singular maps;
those need not be rigid screws. `burgers_step` returns the translation only when the linear
part is identity. For a rotating affine holonomy `(R,t)`, closure of a based point is
`(R−I)x+t=0`; closure of the whole frame is `R=I, t=0`. Translation alone is not the test.
The native `followed_by` convention applies maps left to right, whereas standard column
matrices/permutations multiply right to left. Its formal realization uses the opposite group
or reverses the represented word; a noncommuting triangle checks the convention.
Faraday induction additionally supplies the constitutive/time law and orientation
`circulation(E)=−∂_t flux(B)`; the spatial cochain identity alone is not that evolution. `Foundation/HodgeReceiver` already proves the full
decomposition of an edge field into a potential part, a circulation part and a harmonic part.
**A harmonic mode is a realization of standing relative to node-divergence and cell-flux
receivers.** A nonzero such mode is not a potential and a suitable cycle receiver separates
it. Harmonic dimension may be zero or greater than one; each cohomology class has one harmonic
representative for the declared positive metric. General `Foundation/Standing` also retains
nonharmonic directions whenever an admitted future distinguishes them. The HNN binding must
state its present receivers, future separator and transport; silence alone does not select the
harmonic quotient. Multiplicative nonabelian holonomy and the additive Hodge complex require
their declared representation/linearization before their fields can be identified.

[proved-standard] An integral flux class is the first Chern class of a line bundle; the divisor
of a section is its zero locus, and local section winding around the divisor is related to curvature by the Poincaré–Lelong
current identity, with its metric and normalization. For a smooth projective complex variety, an integral degree-two `(1,1)` class is a
line-bundle Chern class and hence a divisor class (Lefschetz (1,1)); `Millennium/HodgeDivisorExponentialPassage` owns that passage. On the unit Hodge circle, a component of type `(p,q)` has character `z^p z̄^q`,
so the net winding is `p−q`; a `(p,p)` class has zero net winding.
Index invariance supplies another face: the Fredholm index of a Toeplitz operator with
continuous invertible matrix symbol is minus the winding of its determinant (Gohberg–Krein).
The Lefschetz number `Σ(−1)ⁱ tr(M | Hⁱ)` reads graph/diagonal intersection with the applicable
compactness, orientation and intersection multiplicities
(`Millennium/GraphTrace`, `Crossings`, `WindingLedger`).

## 5. Tube = transfer between cross-section charts

[definition] A tube carries action between two cross-sections, each a chart with discrete
modes. It is one object with two readings: a map from one section to the other,
`|out⟩⟨in|`, or a pairing of the two sections, `⟨·|·⟩`. A declared nondegenerate pairing identifies a section with its dual and relates the map
and pairing readings. In a heat/Euclidean specialization, propagation is `e^{−tH}`; after
supplying units, `t` can be an inverse-temperature parameter. A trace-class closing gives
`tr(e^{−tH})`. A torus or exchange of its clock cycles requires the additional periodic
geometric and boundary structure; a general tube does not supply it automatically. **Integration by reflection** (`diffusion.rs`, `causal_reflection.rs`) eliminates
the interior to the boundary; that Schur complement is the discrete Dirichlet-to-Neumann map
and the reflection coefficient of `Millennium/Horizon.smith`. `traversible_chain` owns ordered
transfer matrices, `Transport/ContinuingTube` and `WorldTube` the continuing tube,
`RH/FosterTanks` the lossless reading in which every zero pair is an LC tank.

[proved-standard] The cusp of the modular surface is such a tube: the wave
`y^s + φ(s)y^{1−s}` with `φ(s) = ξ_c(2s−1)/ξ_c(2s)`, where
`ξ_c(s)=π^(−s/2)Γ(s/2)ζ(s)` is the meromorphic completion (without the entire-ξ factor
`s(s−1)/2`), has circular cross-sections with integer modes,
`s ↦ 1−s` is reflection off the interior, `|φ| = 1` on `Re s = ½`, and the poles of `φ`, its
resonances, sit at `s = ρ/2` for each nontrivial zero `ρ` of `ζ` ([Gelbart–Miller, §4](https://sites.math.rutgers.edu/~sdmiller/gelbart-miller-zeta.pdf)). Riemann's proof of the functional equation splits the
Mellin integral at the self-dual section and folds it by `x ↦ 1/x`, which is integration by
reflection.

## 6. Continuing, and compression of functionality

[definition] A Holon continues; a tensor or matrix is a sample of it. Analytic germs, well-posed evolution and compatible towers supply distinct instances with
their own hypotheses. A germ continues along admissible paths; singularities or a natural
boundary can obstruct extension, and monodromy records path dependence where continuation
exists. Slice data has a unique development only for the specified well-posed equation and
boundary/gauge conditions. A coherent thread through a tower lifts level by level, uniquely
when the required lifting condition holds (Hensel; `Millennium/FamilyTunnellBrandtPadicHensel`, `Foundation/ContinuingTower`).
Holon : tensor : matrix is a section with its generator : its value in a chart : its components
in a frame. An admitted [D-finite function](https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf) is an algorithmic instance: a generator and finite
initial data, closed under sum, product and integral, with a supplied annihilator and sufficient exact initial data deciding equality on the
admitted germ/domain. Creative telescoping constructs differential/recurrence relations for
specified sums and integrals, with their boundary terms; it is the target class of the [identity atlas](plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md).

[definition] Compression of functionality keeps what admitted futures can distinguish and the
gluing between levels. Minimal realization (Myhill–Nerode, Kalman) is future-distinguishability,
which is `StandingLaw` and `ReceiverHistoryCompression`'s `D E = ρ`, `E_next T = U E`. The
[holonomy decomposition of finite transformation semigroups](https://arxiv.org/abs/1508.06345)
uses permutation/reset cascades with state-dependent interlevel dependencies and a covering
map. General permutation groups need not be cyclic rotors; reset maps have no group inverse.
The carry cocycle is a concrete instance of such gluing, not a classification of every cascade.
An HNN use supplies the covering/decoder and its action square. `TransportWord` owns optimal
words. Tying, fingering and composition are words in generators with relations read through
these same owners.

## 7. Arithmetic instances and their grades

| Statement | Grade | Owner |
|---|---|---|
| `n ↦ (n mod p)_p` is diagonal winding on a finite product of residue circles (CRT); a growing sieve removes multiples of admitted primes, with coverage through `√n` needed to decide primality | proved-standard (CRT, sieve); §2 `diagonal_step_generates_the_coprime_torus` | `PlaceLedger`, `FamilyGauss`, recursion law of `THE_MACHINE` |
| At good reduction, elliptic Frobenius has characteristic roots of modulus `√p`; after a complex embedding their normalized phases include the real boundary cases. Hasse bounds its trace by `2√p` | proved-standard (Hasse; Weil) | `LocalFactor`, `TraceSequence`, `HeightLattice` |
| Weil's placement for curves is the Hodge index theorem on `C×C` | proved-standard | `HodgeIndex`, `LorentzianPerp` |
| On simple-zero branches of the declared backward heat flow, `ż_k = 2Σ_{j≠k} 1/(z_k−z_j)` with the source's convergence/regularization; collisions need their limiting law. The pair potential reads `−log Q`; separately `Λ_DN ≥ 0` | proved-standard (de Bruijn; Csordas–Smith–Varga; Rodgers–Tao) | `RH/HeatFlowStackedSeam`; helical guide `U=Φ(Q)` |
| Zero count in a finite strip rectangle is the winding of `ξ` on its positively oriented boundary, when that boundary has no zeros; multiplicities are retained | proved-standard (argument principle) | `WindingLedger` |
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
   (`RationalPhase`, `Odometer`, a tower level). A phase-only chart can forget the nontrivial extension carried by its lift.
2. **Address.** The local rate relation and its sign/stationary cases, positive lock address when
   applicable, tolerance/horizon and any separate finite search bound; prove closure if used.
3. **Conserved faces.** The represented material block, class functions preserved by frame carriage
   (trace sequence, transfer determinant), and placement hypotheses. Material learning may
   change these faces; functionality still uses the source/receiver descent equations.
4. **Cell holonomy and retained class.** The cells of the incidence complex, the flux each
   reads, and any harmonic class retained by those receivers; state other future separators too.
5. **Tube reading.** Whether a passage is consumed as a map or as a pairing, its reflection at
   the boundary and its clock.
6. **Continuation.** The level the object lifts from, the condition under which the lift is
   unique and the fibre retained when it is not.

Each native packet lands with the Lean statement of the law it adds under the matching
`Framework` entry point, or names the obligation it leaves in #62.
