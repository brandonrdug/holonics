# The Swing is a move about a grip: a grip turns, a push boosts, and a free body falls

**September 28, 2026.** Brandon asked for the primitives of motion to be re-derived: "the motions
are the turn and the boost, it's about pivoting and free-falling, the 'reflection' thing isn't
important, we just want complex flux and turning/boosts for momenta and inertia as well as higher
derivatives of motion." On reading the first draft he added: tie the geometry and hypergeometry to
lattices and crystals, induction and cross-entropy (Maxwell, Faraday), the conservation of faces,
transcendentals as constraints, and the Einstein and quantum lifts (§5).

This record derives the primitives, replaces the Swing's frozen chart and joins the result to the
owners that already hold its pieces. GPT-6 Astra reviewed the first draft adversarially; its
counterexamples are folded in where they apply, and the draft's errors are listed in §10. The
receipts are the Lean module `Geometry/Motion` and the exact symbolic checks in
`research/notebook/motion/motion_identities.py` (§9).

Earlier records read turns and boosts before this derivation, and each now points here: [the egg is a torus whose shape is a boost](2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md), [the null cone is the constitution's lock](2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md) (boosts as ratios of clock readings), [the light is the change](2026-09-24_THE_LIGHT_IS_THE_CHANGE_AND_EXPRESSION_COLLAPSES_ONTO_FINITELY_MANY_CRITICAL_CLASSES.md) and [seasons are rotations, generations are boosts](2026-09-25_SEASONS_ARE_ROTATIONS_GENERATIONS_ARE_BOOSTS_AND_THE_PRIME_WHEEL_IS_A_PRODUCT_OF_RESIDUE_RINGS.md).

## 0. The result

- **There are three kinds of motion: the turn, the boost and free fall.** Every quadratic motion of
  one degree of freedom is exactly one of them, by the sign of one determinant: a turn (elliptic),
  free fall (parabolic, a shear) or a boost (hyperbolic). Every move of the plane's area-preserving
  group factors uniquely as a turn, a boost and a shear (the Iwasawa factorization `KAN`), and the
  Lorentz group factors the same way into rotations, boosts and null rotations.
- **Power decides turn or boost.** An effort that does no work turns; one that does work boosts.
  A stationary ideal grip turns. A moving grip, a push along the motion, a pump and friction boost.
  With no effort at all, a body free-falls: in phase space its motion is the shear `(q, p) ↦
  (q + hp/m, p)`, which inertia alone produces.
- **A receiver reads a linear rate as turn plus boost.** Against its energy metric `G`, a rate `A`
  splits uniquely into a `G`-skew turn and a `G`-self-adjoint boost, and only the boost, the
  metric's motion and the forcing change the energy. The split is covariant under recharting; only
  a different receiver's metric changes it.
- **A move has the pivot it holds; a grip is what holds it.** A finite move's pivot is its fixed
  point, or its invariant axis with free fall along it. What the move holds invariant (a distance,
  a bearing, a cross ratio) is its grip. A physical grip is a constraint with its reaction, supplied
  by the constitution.
- **Along a path, the velocity carries the motion.** Where it does not vanish, `ẇ = v⁻¹v̇` is boost
  rate plus `i` times turn rate, and every higher derivative of position is `v` times a polynomial
  in the jets of `ẇ`.
- **The Swing is re-derived as the move about a grip**, with momentum carried through it and free
  fall between grips. The point reflection `S_a x = 2a − x` is one move of that family, the
  half-turn, and a proper continuous motion only in the plane or a complex chart.

## 1. What was meant

Brandon's statements, in the order they were made:
- **Pivoting with inertia** (July 14): "The cross boundary swing as a way of the first-person
  modulating their inertia and pivoting is literal", with the "monkey swinging between trees"
  (July 16).
- **Holding something fixed** (July 16): "I must hold something fixed … in order to then
  pivot/balance off of it. If the pivot is the fixed thing, and you are the body …"
- **Chaining inertias** (July 18): the swing is "about chaining 'starting' inertias in order to
  accelerate towards objectives".
- **Rotations and boosts** (July 27): numbers "do not need to be individually large, they are all
  rotations and boosts relative to each other".
- **The one move and its grip** (August 6, [canon](../../docs/canon/THE_DIALECT.md)): "the pivot needs
  to utilize an invariant 'grip' which is the relationship between both sides of the equation", with
  `pV = nRT` as the example; the canon's gloss is "a change of frame preserving an invariant grip".
- **The sling** (August 26): gravity assist "is like the swing coarse grained", and "a throw to put
  things in free-fall, yet a precise impulse".
- **The leap, the throw and the decision** (September 12): a "leap" was "an extension of the swing
  that caters to free-fall motion"; a decision is when the intelligence "drops the ball … it releases
  action into a mode of free-fall", and words are thrown to be caught.
- **Currents in free fall** (September 27): "the currents are always in free-fall, what emanates is
  also in free-fall but it is not the same thing from prior to an intersection."

The concept was always a motion: a pivot held by a grip, momentum carried through it, a release
into free fall, and a catch.

## 2. What the repository froze, and why it fails

The objects guide defined the Swing by its frozen-board chart, the point reflection
`S_a x = 2a − x`, and the code and Lean followed (`geometry::swing`, `Geometry/AffineSwing`).
- **It is the endpoint of a half-swing, not the swing.** A body carried half a turn about a pivot
  lands at `2a − x`; the arc, the momentum and the time of the passage are dropped.
- [proved-derived] **Words of point reflections are poor in motions.** Each `S_a` has linear part
  `−I`, so every word has linear part `±I`: it composes only translations and half-turns. A
  quarter-turn in the plane is not one. Cartan–Dieudonné concerns reflections in hyperplanes, which
  the objects hold separately as `2P_D − I`.
- [proved-derived] **In an odd real dimension the point reflection is not a proper continuous
  motion.** `det(−I_d) = (−1)^d`, and a path of invertible maps from the identity cannot change the
  determinant's sign. It remains a lawful discrete map (parity).
- [proved-derived] **A Swing without an anchor law says nothing.** Every map is pointwise a Swing,
  `T(x) = S_((x+T(x))/2)(x)`, so declaring each update a Swing moves the unexplained work into the
  choice of anchor. The objects' Swing declared its anchor. (The HNN junction's anchor is the
  exception: `hnn::propagation::junction_scattering` derives it from admittance-weighted participation, a
  constitutive law.)

## 3. The derivation

### 3.1 Three kinds of motion

[proved-standard; checked] **Quadratic motion of one degree of freedom.** For
`H = ½(αp² + 2βpq + γq²)` the flow on `(q, p)` has the generator

```text
X = [[β, α], [−γ, −β]],     tr X = 0,     X² = −(det X)·I,     det X = αγ − β²
```

With `α = 1/m` the inverse inertia, `γ` the stiffness and `β` a coupling:
- `det X > 0`: **a turn.** The flow rotates in the energy's own chart: an oscillator, storage and
  flow exchanging (the parametron's LC exchange).
- `det X = 0`: **free fall.** `X² = 0`, the flow is a shear. For `β = γ = 0` one step of duration `h`
  is `(q, p) ↦ (q + hp/m, p)`: inertia alone, the free particle.
- `det X < 0`: **a boost.** The flow stretches one direction and shrinks the other: the inverted
  pendulum, the squeeze.

[proved-standard; checked] **Every move factors as a turn, a boost and a shear.** For
`M = [[a, b], [c, d]]` with `ad − bc = 1` and `r² = a² + c²`,

```text
M = K(r) · diag(r, r⁻¹) · [[1, (ab + cd)/r²], [0, 1]]        K(r) = [[a/r, −c/r], [c/r, a/r]]
```

uniquely: the Iwasawa factorization `SL(2, ℝ) = KAN`, a turn times a boost times a shear. The Lorentz
group factors the same way (`SO⁺(1, 3) = KAN`): rotations, boosts along one axis, and null rotations
that fix a light direction. The factors are exact in the quadratic extension carrying `r`, stated by
its constraint `r² = a² + c²`; the move itself stays rational and is carried undivided.

### 3.2 A receiver's reading of a rate

[proved-standard; the receiver reading `agent-inferred`] Let a receiver read a linear motion
`ẋ = Ax + f` against its energy metric `G`, invertible and self-adjoint, with `A† = G⁻¹AᵀG`:

```text
turn    T = ½(A − A†)        G-skew
boost   B = ½(A + A†)        G-self-adjoint
A = T + B, uniquely         (a map both G-skew and G-self-adjoint is zero)
Ė = ½ xᵀ(AᵀG + GA + Ġ)x + xᵀGf = xᵀGBx + ½ xᵀĠx + xᵀGf,     E = ½xᵀGx
```

The turn does no work. The boost, the metric's own motion `Ġ` (a pump, §3.3) and the forcing `f`
change the energy.
- **Recharting does not change it.** Under `x = Sy`, `A′ = S⁻¹AS`, `G′ = SᵀGS`, and `T′ = S⁻¹TS`,
  `B′ = S⁻¹BS`: a pure turn stays pure. Only a different receiver, a different `G` for the same
  motion, changes the split. `A = αI` is a boost for every `G`.
- **The spectrum is the conserved face.** Each mode's rate `λ = β + iθ` (growth and frequency) is
  the same for every receiver. The split agrees with the spectrum exactly when `A` is `G`-normal. When
  it is not, a receiver reads boosts no mode carries: every mode can decay while `E` grows for a
  while. Shear flows amplify this way before any mode is unstable (Trefethen, Trefethen, Reddy and
  Driscoll, 1993).
- **A complex channel** uses a Hermitian metric and the conjugate transpose. For `ż = cz` with
  `c = β + iθ`, `θ` is the turn (the frequency) and `β` the boost (the log-growth rate): the complex
  flux of one channel.
- **An indefinite metric keeps the algebra and changes its meaning.** With the interval `η` as `G`,
  every Lorentz move is `η`-skew, so a Lorentz boost falls in the "turn" part: it holds the interval.
  The rotation/boost split needs an observer `u` (`η(u, u) = −1`) and its rest-frame metric
  `G_u = η + 2u♭⊗u♭`. The observer's energy of a momentum is `−η(u, p)`, read separately.

### 3.3 Power decides turn or boost

[proved-standard; checked] **A point mass.** With constant mass, nonzero velocity `v` in an inertial
frame and effort `F`,

```text
Ė = ⟨F, v⟩ = m|v|² Re(ẇ),      θ̇ = Im(v̄F)/(m|v|²),      ẇ = v⁻¹v̇
```

so the effort along the motion is the boost and the effort across it the turn. The Lorentz force
shows both: the magnetic part turns a charge's momentum without work; the electric part along the
motion boosts it.

[proved-standard] **Grips.** An ideal constraint's reaction annihilates every admissible virtual
velocity. For a stationary constraint it does no actual work, so **a stationary grip only turns**.
A moving grip does work: for `f(q, t) = 0` with reaction `λ∇f`, the power is `−λ∂_t f`. A child
pumping a swing and a slingshot are moving grips that boost.

[proved-derived; checked] **The Holon's law in its quadratic chart.** With `H = ½xᵀQx`, `Q = Qᵀ ≻ 0`,
`J` skew and `R ⪰ 0`, the motion `ẋ = (J − R)Qx + Bu` has

```text
turn  T = JQ,     boost  B = −RQ      (relative to G = Q)
Ḣ = −(Qx)ᵀR(Qx) + (Qx)ᵀBu
```

The power-neutral interconnection turns; the resistive elements are friction, a boost that only
lowers energy; the ports exchange energy. Beyond this chart the power balance remains and the metric
reading does not:
- **Nonlinear storage.** `H = p²/2 + q⁴/4` conserves `H`, but not `q² + p²`: the skew part conserves
  the energy, which is not a metric sphere.
- **Sources** act at the ports; their part along the motion boosts and their part across it turns.
- **Pumps** move the storage. `H = (p² + κ(t)q²)/2` exchanges power `κ̇q²/2` with no additive source:
  the `½xᵀĠx` term.
- **Inertia is the kinetic constitutive relation**, not all storage. A spring stores energy and is
  not inertia; in momentum coordinates the kinetic storage is `M⁻¹`.

**Free fall** is motion under inertia alone: the geodesic of the kinetic metric, `∇_u u = 0`, with
gravity as the connection, not a push. A lossless oscillator is not in free fall; its spring pushes.
In phase space free fall is the shear of §3.1.

### 3.4 A move and its pivot

[proved-standard; checked] Let a finite move be `x ↦ Mx + b`.
- **A pivot point.** When `I − M` is invertible, `O = (I − M)⁻¹b` is the unique fixed point and
  `Mx + b − O = M(x − O)`.
- **An invariant axis with free fall along it.** When the eigenvalue `1` of `M` is semisimple, split
  `b = b_∥ + b_⊥` along `ker(I − M) ⊕ range(I − M)`. The set `O + ker(I − M)`, with `(I − M)O = b_⊥`,
  is invariant, and `Mx + b = O + M(x − O) + b_∥`: the move about it, then free fall `b_∥` along it.
  Its points are fixed only when `b_∥ = 0`. For a proper rigid move in three dimensions this is
  Chasles's screw, with a one-dimensional axis; a helix is a turn about an axis with free fall
  along it.
- **A shear has no such split.** For `M = [[1, 1], [0, 1]]`, `ker(I − M)` and `range(I − M)`
  coincide; with `b = (0, 1)` the orbit of the origin is `(n(n − 1)/2, n)`. Free fall in phase space
  is exactly this case.
- **The complex chart.** `z ↦ kz + b`, `k ∈ ℂ^×`: for `k ≠ 1` the pivot is `O = b/(1 − k)`, the
  move a turn if `|k| = 1`, a scalar dilation if `k > 0`, both otherwise; `k = 1` with `b ≠ 0` is a
  translation, with no finite fixed point. Moves compose as `(k₁, b₁)∘(k₂, b₂) = (k₁k₂, k₁b₂ + b₁)`.
  The old Swing is `k = −1`, the half-turn.
- **A pivot is kinematic; a grip is constitutive.** The fixed point of a finite map is not
  automatically a physical grip, and a finite move does not determine the trajectory between its
  endpoints. A grip is a constraint with its reaction, which the constitution supplies.

### 3.5 What a move holds

[proved-standard] What a move holds invariant is its grip.
- A turn about `O` holds the `G`-distance `|x − O|_G` (a rope).
- A positive scalar dilation about `O` holds the bearing, the ray from `O` (a rail); a general
  self-adjoint boost holds only its principal axes. Constant-bearing pursuit is the relative
  position under positive scalar dilations toward the chaser.
- **A Möbius move holds the cross ratio** of every four points: Brandon's cross-ratio swing.

[proved-standard; checked] **The multiplier is a cross ratio of the two pivots, the body and its
image.** For `m(z) = (az + b)/(cz + d)`, `ad − bc ≠ 0`, with distinct finite fixed points `z₁, z₂`
(`Compression/Landmark/FixedPoint`, atlas `landmark.mobius-fixed-points`) and `μ_i = cz_i + d`,

```text
(m(z) − z₁)(z − z₂)·μ₁ = μ₂·(z − z₁)(m(z) − z₂),     K = μ₂/μ₁ = m′(z₁),   m′(z₂) = K⁻¹
(μ₁ + μ₂)² = tr²,  μ₁μ₂ = det,  so  K + K⁻¹ + 2 = tr²/det
```

The order of the arguments matters: `swing_pair(m(z), z, z₁, z₂)` reads `K`, and exchanging the first
two reads `K⁻¹`. Fixed points at infinity need homogeneous coordinates.

For real nonsingular two-by-two representatives, read projectively (on the ratios of the two
components), `tr²/det` classifies the move, and this is `navigator::trace::SiteKind`:

| `SiteKind` (`a = tr`, `q = det`) | `tr²/det` | multiplier `K` | the move |
|---|---|---|---|
| Rotation, `q > 0`, `a² < 4q` | `[0, 4)` | on the unit circle, `K ≠ 1` | a turn |
| Boost, `q > 0`, `a² > 4q` | `(4, ∞)` | real, positive, `K ≠ 1` | a boost |
| Null, `q > 0`, `a² = 4q` | `4` | `K = 1`: parabolic, or the identity | free fall (a shear) |
| Reflection, `q < 0` | `(−∞, 0]` | real, negative | a half-turn with a boost |
| Degenerate, `q = 0` | none | none | not invertible; possibly a lawful singular evolution |

The reading is projective: `I` and `2I` act alike on ratios, and a real quarter-turn matrix has trace
zero and projective multiplier `−1`. For a nonsingular trace-zero matrix, Cayley–Hamilton gives
`M² = −(det M)·I`, a projective involution: the harmonic conjugation the objects called the
projective Swing. It is Möbius-conjugate to a half-turn of the sphere about the axis through its two
pivots (`1 − z` fixes `½` and `∞`, which are not antipodal).

[proved-standard] **The Möbius group is the Lorentz group.** `PSL(2, ℂ) ≅ SO⁺(1, 3)`, acting on the
sphere of light directions (Penrose and Rindler; Oblak). A move with two distinct fixed light
directions is, in an adapted Lorentz frame, a commuting boost along the axis joining them and a turn
about it; a parabolic move is a null rotation, not diagonalizable. Reading the multiplier as a
rapidity needs the representation map: in `Spacetime/Boost`, velocity addition multiplies the
Doppler chart `D(β) = k²` while the rapidity is `log k` (`doppler_betaOf`). In `SL(2, ℂ)` a full
spatial turn is `−I` and two are `I`.

### 3.6 Along a path

[proved-derived; checked] Carry the velocity `v` with its frame and clock. Where it does not vanish,
the lifted chart `w = log(v/v_*)` (a nonzero reference `v_*`, winding kept by a continuous lift along
the path) gives

```text
ẇ = v⁻¹v̇ = β̇ + iθ̇                      boost rate + i · turn rate
ẍ = v·ẇ                                   tangential |v|β̇; normal |v|θ̇ = |v|²κ
x⃛ = v·(ẇ² + ẅ)                            the jerk
x^(n+1) = v·Y_n,   Y_0 = 1,   Y_(n+1) = Ẏ_n + ẇ·Y_n        (Y_n the complete Bell polynomial)
```

so every higher derivative of motion (acceleration, jerk, snap, crackle, pop) is `v` times a
polynomial in the jets of the one complex rate. `v⁻¹v̇` is the Maurer–Cartan form, the ratio's
`R⁻¹dR` (objects §9) evaluated on a clock.
- **The chart fails at rest.** `x = t²/2` has a regular acceleration at `t = 0`, where `v = 0` and
  `ẇ = 1/t`. The velocity, not its logarithm, is the carrier.
- **Constant rate `r ≠ 0`:** `x(t) = x₀ + v₀(e^(rt) − 1)/r`, an equiangular spiral about
  `x₀ − v₀/r`; a real `r` gives a radial line and an imaginary `r` a circle; `r → 0` is a straight
  line. A finite multiplier alone does not supply this interpolation.
- **The pendulum.** `x − O = ℓe^(iφ)` gives `ẇ = φ̈/φ̇ + iφ̇` away from the turning points. With `φ`
  from the downward vertical, the rope's tension is `mℓφ̇² + mg cos φ`: it balances gravity's radial
  part, supplies the centripetal acceleration, does no work, and must stay nonnegative. Gravity's
  tangential part `ℓφ̈ = −g sin φ` is the boost.
- **The discrete chart.** On equal clock intervals and in one frame, the machine carries the
  undivided pair of steps `(Δx_t, Δx_(t+1))`; their ratio, where the first is nonzero, is the step's
  turn and boost. Equal steps say only that the sampled steps agree.
- **Three dimensions.** With `σ = (v·v̇)/|v|²` and `Ω_⊥ = (v × v̇)/|v|²`, `v̇ = σv + Ω_⊥ × v`; the
  velocity does not determine the body's spin about `v`. The Frenet frame turns at `|v|(τT + κB)` per
  unit time (torsion needs `κ ≠ 0`). Constant speed, curvature and torsion give the circular helix.

### 3.7 Momentum and inertia

[proved-standard] Momentum is the constitutive dual of the rate, `p = ∂L/∂ξ`; in the kinetic
quadratic case `p = Mξ`, and a singular constitution keeps its fibre. Forces and torques are efforts
at ports, and power is their pairing `⟨e, f⟩`, the Holon's port law.
- **A planar body**, in body coordinates at its centre of mass, with constant mass and inertia:
  `m(v̇ + iωv) = F`, `Iω̇ = τ`.
- **A free rigid body:** `L̇_b + ω × L_b = 0`, `L_b = Iω`. Its spatial angular momentum stays
  constant while its angular velocity can precess (Euler and Poinsot): inertia shapes free fall.
- **A relativistic point** falls freely along `∇_u u = 0`; local inertial coordinates do not remove
  tidal curvature.

### 3.8 The passage: grip, swing, release, free fall, catch

[interpretation, on the exact laws above] The motion Brandon described in July is a passage, each
stage with its own law:
- **grip:** a constraint holds a pivot; a stationary grip turns the body without work;
- **swing:** the turn about it, boosted by the pushes along the arc (gravity's tangential part on a
  pendulum, the rider's pumping on a playground swing, which moves the grip);
- **release:** the grip let go; with no impulse, the momentum at release carries into free fall.
  Brandon's decision "drops the ball": release is the threshold commit of
  [the chase record, §6](2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md);
- **free fall:** inertia only;
- **catch:** a new grip, which exchanges momentum with it and may dissipate energy; reception at a
  contact.

It closes into a cycle only where the passage actually returns.

[proved-standard; checked] **The sling is a turn about a moving pivot.** In asymptotic conservative
scattering off a body of velocity `V` (a gravity assist, treating the craft as a test particle), the
flyby is a turn about `V`: `v_out = Rv_in + (I − R)V`, with `R` a rotation. A receiver centred at rest
reads

```text
|v_out|² − |v_in|² = 2 Re( V̄ (v_out − v_in) )
```

so it can gain, lose or keep speed. The turn is about a pivot that is not the receiver's centre, and
the receiver's energy reading changes: this is what "chaining starting inertias" computes. The
body's recoil is in the joint balance.

## 4. Where the objects already hold it

[established-bounded; source-inspected, with Astra's narrowing] The primitives are how the existing
objects move; each owner holds the part named, and no more.

| Object and owner | What it holds of the motion |
|---|---|
| Holon law (`Holon/{Law,Dirac,Element}`) | in the quadratic chart, the turn `JQ`, friction `−RQ` and port power; the power balance in general |
| Parametron (`Objects/Parametron`, `HNN/Ring`) | oscillation as a turn, the LC exchange, the half-turn symmetry of the sheets; `HNN/Ring` keeps the pump's stiffness-change work |
| The pump | quadrature squeezing is conjugate-linear, `ż = az + b z̄`, not a complex scalar rate; over a pump period the Floquet monodromy is a turn below threshold, a boost inside a resonance tongue, and a shear at its edge (Hill; Magnus and Winkler). In the principal resonance its trace is below `−2`: a half-turn with a boost, the subharmonic lock whose two phases differ by a half-turn. The objects leave this open (#62) |
| Pair contact (`holon::contact`) | a constraint on relative motion; no slip transmits motion at its Farey ratio and can transfer energy between the bodies; slip under friction lowers energy |
| Navigator and helix (`geometry::screw`) | a screw's kinematics: a turn about an axis with free fall along it; force-free only under its own law |
| Ratio (`Objects/Ratio`) | `ℓ = log R` splits as `Re ℓ = ½ log(q/p)` and the phase; `R⁻¹dR` is a rate once evaluated on a clock |
| `SiteKind` (`navigator::trace`) | the projective classification of a two-by-two transfer (§3.5) |
| Boost (`Physics/Spacetime/Boost`) | collinear light-cone boosts as Doppler ratios, and clock readings |
| Aeon (`aeon`, `Aeon/Clock`) | elapsed time as a clock's windings plus phase: the lift of that clock's section crossings, not a spatial turn |
| Clocked pantograph (`HolonicClockedPantographicSwing`) | declared crossings, quotient and remainder gearing, and inner interaction fibres |
| Pantograph (`HolonicPantographicSwingJets`) | the scalar pantograph `Q − O = s(P − O)` and its own jet recurrence (a different recurrence from §3.6's) |

## 5. The lifts

Each join names its owner; "checked" marks an identity verified exactly before writing.

### 5.1 The conservation of faces

- [proved-derived] **The multiplier is a conserved face.** A change of frame conjugates a move,
  `M ↦ S⁻¹MS`, keeping its trace and determinant, so it keeps the multiplier `K` and the kind of
  move about the move's own pivots. The objects' conservation of faces
  (`Transport/NavigatorTraceFaces`: determinant, trace sequence, transfer determinant) therefore
  conserves which motion a navigator makes.
- [proved-standard] **For a rate, the spectrum is the conserved face and the split is the reading**
  (§3.2).

### 5.2 Lattices and crystals

- [proved-standard] **A crystal is a lattice held by its moves.** A turn that preserves a lattice
  has an integer trace, so `|tr| < 2` leaves `tr ∈ {−1, 0, 1}`: with the identity and the half-turn,
  the turns of order `1, 2, 3, 4, 6`. This crystallographic restriction is Niven's fact
  (`winding.niven-star-values`: `2cos(2πm/n) ∈ ℚ` exactly when `n/gcd(m, n) ∈ {1, 2, 3, 4, 6}`).
- [proved-standard] **The lattice's moves are `SL(2, ℤ)`:** turns of order `3, 4, 6`, shears (the
  lattice's free fall, `[[1, 1], [0, 1]]`) and boosts (`|tr| > 2`). Its quotient `PSL(2, ℤ)` is
  generated by a half-turn and a third-turn, the
  [trefoil record's](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md)
  presentation.
- [proved-standard; checked] **A lattice boost is a Lorentz boost.** `[[2, 1], [1, 1]]` stretches by
  `φ²` along one eigendirection and shrinks by `φ⁻²` along the other, and it holds the indefinite
  form `x² − xy − y²` (the norm of `ℤ[φ]`): in that form's light-cone chart it is a boost with Doppler
  ratio `φ²`. The golden quasicrystal (the Fibonacci chain, the carry word at the golden rate,
  `Aeon/Clock/CarryWord`) is `ℤ²` cut and projected along its expanding direction.
- [proved-standard] **A crystal's turn closes; a quasicrystal's never does.** In `ℚ(i)` the only
  turns of finite order are the units `±1, ±i`. Every other rational turn, such as `(3 + 4i)/5`, is an
  irrational fraction of a full turn (Niven), so its windings never recur: a one-dimensional
  quasicrystal clock (`never_locks_iff_irrational`).

### 5.3 Hypergeometry

- [proved-standard] **Monodromy is a group of moves.** Carrying a hypergeometric family's pair of
  solutions around a singular point applies a move to it: a turn at a point of finite order, a shear
  at a cusp (one period added to another: a carry), a boost otherwise. The Gauss equation with
  exponent differences `½, ⅓, 0` has the `(2, 3, ∞)` triangle group: the half-turn, the third-turn and
  the cusp's shear, `PSL(2, ℤ)` again.
- [proved-standard] **The egg's period is a Legendre family.** `(π/2)₂F₁(½, ½; 1; λ)`
  ([the probability record](2026-09-27_PROBABILITY_IS_A_RECEIVER_GEOMETRY_BAYES_IS_THE_RATIOS_TRANSLATION_AND_THE_EGGS_PERIOD_IS_HYPERGEOMETRIC.md))
  has monodromy `Γ(2)`, generated by the shears `[[1, 2], [0, 1]]` and `[[1, 0], [−2, 1]]`: going
  around a cusp adds twice one period to the other. The Schwarz map and this monodromy are owed in
  #62.
- [formal-checked] The self-similar navigator's complex dimensions read this way already: the real
  part a dilation, the imaginary part a rotation in the log chart (`fractal.self-similar-zeta`).

### 5.4 Induction and cross-entropy (Maxwell and Faraday)

- [proved-standard] **The electromagnetic field is a field of rates.** `dp^μ/dτ = (q/m)F^μ_ν p^ν`: the
  field acts on a charge's momentum as an infinitesimal Lorentz move. Relative to an observer, `E`
  boosts (along the motion it does work) and `B` turns (it does none), and `F = E + iB` is one complex
  vector.
- [proved-standard; checked] **The field's own evolution is a turn.** In vacuum, with `c = 1`,
  Maxwell's equations are `i∂_t F = ∇ × F` for `F = E + iB` (Riemann–Silberstein). The curl is
  self-adjoint, so the field's energy is conserved. A current is a push: in Poynting's
  `u̇ + ∇·S = −J·E`, only `J·E` exchanges energy.
- [formal-checked] **Faraday's induction is the coexact part.** The circulating emf is not an exact
  drop (`HolonicDiscreteInduction.emf_ne_exactDrop_of_fluxDifference_ne_zero`), and flux is the
  coordinate whose source is the negative circulation (`em.faraday-successor`).
- [proved-derived; checked] **For a linear field, turn and boost are Helmholtz–Hodge.** The
  self-adjoint part `Sx` is the gradient of `½xᵀSx` (exact, curl-free) and the skew part `Tx` is
  divergence-free, a circulation. So the objects' `exact ⊕ coexact ⊕ harmonic` is `boost ⊕ turn ⊕
  dormant` in the linear chart. A fluid's velocity gradient is strain plus vorticity (Cauchy and
  Stokes), and vortex stretching `ω·Sω` is the strain boosting the vorticity: the mechanism the
  Navier–Stokes target asks about.
- **Cross-entropy splits the same way.** The ratio's log is `Re ℓ = ½ log(q/p)`, whose expectation is
  the Kullback–Leibler divergence, plus the phase. Entropy production splits alike:
  - [formal-checked] relaxation toward the stationary face lowers the divergence to it (the
    H-theorem, `heat.h-theorem-core`);
  - [formal-checked] the arrow that survives at stationarity lives on cycles: an open chain is
    reversible and has no stationary arrow, and a ring's production is its one current times its
    cycle affinity (`heat.chain-no-arrow`, `heat.ring-current-affinity`);
  - [proved-standard] a linear diffusion is reversible exactly when its drift has no turn relative to
    its stationary metric (the housekeeping and excess split; Hatano and Sasa, 2001; Kwon, Ao and
    Thouless, 2005): stationary production is a circulation.

### 5.5 Transcendentals as constraints

[definition] A move is carried by its algebraic data: the undivided matrix, a multiplier in `ℚ(i)`, a
Doppler ratio, the constraint `r² = a² + c²` of its factors. π and `e` enter only as constraints:
- `e^(2πi) = 1` is the condition that a turn closes, `k^q = 1`, a lock at its Farey address;
- `e^(iπ) = −1` is the half-turn;
- `e` is the boost that is its own rate, `d/dβ e^β = e^β`.

Angles and rapidities are the logarithmic chart, read at a grain with their winding. A digit of π is a
receiver face, never a coefficient (objects, "π and e are constraint identities"). Exactness has
limits to state: a Cayley turn is rational where its denominator is invertible and never reaches the
half-turn; the factors of `1 + i` need `√2`; a rational Doppler ratio gives a rational boost, but a
rational velocity need not give a rational Doppler ratio (velocity `½` needs `k² = 3`).

### 5.6 Einstein

- [proved-standard] **Free fall is the geodesic**, and gravity the connection.
- [formal-checked; checked] **Two boosts leave a turn.** `[K_x, K_y] = −J_z`, and a closed loop of
  non-collinear boosts returns a rotation equal to its velocity triangle's area defect
  (`Physics/Spacetime/Wigner`, `lorentz.thomas-wigner-holonomy`). Boosts close only up to turns: the
  Thomas–Wigner gyration, which is Brandon's gyroparallelogram.
- [proved-standard] **Tidal curvature is a strain field, frame dragging a rotation field.** Relative to
  an observer the Weyl tensor splits into an electric part (tidal stretching and squeezing) and a
  magnetic part (gravitomagnetism), joined as the complex `E + iB` whose eigenvalues give the Petrov
  classification.
- [proved-standard] **A free-falling congruence focuses by strain and resists by rotation.** Its rate
  is expansion and shear plus vorticity, and Raychaudhuri's
  `dθ/dτ = −θ²/3 − σ² + ω² − R_μν u^μ u^ν` makes shear and matter focus it while vorticity resists:
  the structure of the focusing theorems, and of vortex stretching.

### 5.7 The quantum

- [formal-checked] **Unitary evolution is a turn, imaginary time a boost.** `−iH` is skew and
  conserves the norm; `e^(−τH)` is a non-unitary semigroup (`quantum.evolution-kinds`). The Wick
  rotation multiplies the rate by `i`, which exchanges them: `i(β + iθ) = −θ + iβ`.
- [proved-standard] **Energy is a turn rate.** `E = ħω`, and momentum is a spatial turn rate,
  `p = ħk`. A decaying state has complex energy `E − iΓ/2`, whose rate `−Γ/(2ħ) − iE/ħ` is a decay
  plus a turn, the form of a damped mode's `−γ + iω`.
- [proved-derived; the clock reading an interpretation] **Mass is a proper-time turn rate.**
  `ψ(τ) = e^(−iMc²τ/ħ)ψ(0)` (`quantum.proper-time-phase`); a clock's elapsed time is its windings
  plus phase (objects §12).
- [proved-standard] **Spin and Berry.** In `SU(2)` a full turn is `−I` and two are `I`. Berry's phase
  is the turn a state accumulates around a loop, a cell holonomy (`Transport/CellHolonomy`).

## 6. What is retired, and what stays

- **Retired as a definition:** "the Swing is the point reflection `S_a x = 2a − x`". Its algebra
  stays, as the half-turn: a proper continuous motion in the plane and in any complex chart; in an odd
  real dimension a lawful discrete map (parity) that no continuous motion reaches.
- **Renamed:** the HNN junction's `2P_D − I` is the lossless junction's scattering. It conserves the
  joint norm, does no work, has determinant `(−1)^codim`, and keeps its consumed law.
- **Stays, re-read:** harmonic conjugation is a projective involution, Möbius-conjugate to a half-turn;
  the cross ratio is the Möbius move's grip; the completed zeta is invariant under `s ↦ 1 − s`, the
  half-turn about `½`, and the critical line is the fixed set of `s ↦ 1 − s̄`.
- **"Pins" have three roles** (the [source contract](../../docs/HNN_FORMULA.md#the-source-and-release-contract)):
  a pivot, a move's fixed point; a key, a navigator's initial configuration; and a material locus.
  They correspond in particular constructions and are not interchangeable.

## 7. The first consumer: the chase

[proved-derived; source-inspected] The chase terrain's traction law
(`holarchy::terrain::chase::traction_bound`) is, on the lattice, `|Δv|² ≤ (γμ_c g h²/ℓ)²` with the
mover's coefficient `γ`. For a nonzero velocity and `k = v′/v`,

```text
|k − 1|²·|v|² ≤ (γ μ_c g h²/ℓ)²        the admitted moves form a disk about 1 that shrinks with speed
a pure turn by θ:  |k − 1| = 2|sin(θ/2)|
```

The disk is only the traction envelope. The runner's moves also obey the lattice, its speed bound,
the arena's walls, the demand chosen on the previous ground, the current ground's traction and held
slips. During a slip the realized move can be the identity while the demanded one lies outside the
disk, and opening velocities are zero and stopping gives `k = 0`, so the consumer carries the
undivided pair `(v, v′)`, not `k`. It does not consume this reading yet.

[after-note, September 28; THE_REBUILD U4] It now does. `holonics::geometry::motion` owns the pair
`(v, v′)` over `ℤ[i]` (`Move`) with its change, its kind decided on the integers without division
(rest, start, stop, free fall, turn, boost, turn and boost), its traction disk, its power and its
signed turn, each cited to this record's Lean. The chase's traction law, demand, slip test and
letters, the chaser's admitted motions and the viable tube's successors read their moves through it,
and every chase receipt is unchanged; the move reading of the 16 action seeds is in the
[notebook](../notebook/hnn_design/README.md#f6-the-chase-reads-the-move-pair-and-the-move-reading-u4s-rebase-september-28).
Still owed in #62: the Lean statement that the integer kind test is the ratio's kind where `v ≠ 0`,
which the Rust tests check on every pair of `[−2, 2]²`.

## 8. What this does not claim

- The text receivers (the tree and the population) are not yet Holons joined at ports
  ([THE_MACHINE](../../docs/THE_MACHINE.md)); their learning is not yet read as this motion, and that
  consumer obligation stands. Brandon's position (September 28): the physical computation is the ideal,
  and framing the machine as text prediction makes the problem harder and less sensible. The
  construction proceeds from the motion; text is one boundary chart of it.
- The Lorentz identification, the Iwasawa factorization, Chasles, Euler–Poinsot, d'Alembert,
  Raychaudhuri, Petrov, Hill's equation and the reversibility of linear diffusions are standard and
  cited, not re-proved here.
- The grip reading of constraint equations (`pV = nRT`) is an interpretation. A regular
  time-independent constraint is preserved along motions tangent to it; a time-dependent one needs
  `∂_t C + DC·ẋ = 0`; and preserving an equation does not imply zero work.

## 9. Receipts and obligations

- **Lean** (`Geometry/Motion`, in the `Holonics` library, no `sorry`): the turn/boost split, its
  uniqueness and its energy law, including the moving metric and forcing; the port-Hamiltonian chart;
  the quadratic Hamiltonian kinds and the free particle's shear; the Iwasawa factorization of
  `SL(2)` with its square root as a hypothesis, and the uniqueness of its factors; the affine pivot,
  its composition, the pivot-free translation and the free-fall split; the complex chart and its
  join to the pantograph; the multiplier as a cross ratio with `K + K⁻¹ + 2 = tr²/det` and `K = −1`
  exactly at trace zero; point-reflection words of every length and `det(−I_d) = (−1)^d`; the point
  mass's power and signed turn rate; the sling; the traction disk; and the path jets
  `x^(n+1) = e^w·Y_n` with the Bell recursion. Twelve atlas rows `motion.*` carry them.
- **Checks** (`research/notebook/motion/motion_identities.py`, exact, sympy): every identity marked
  "checked" above, 27 in all.
- **Owed in #62:** `PSL(2, ℂ) ≅ SO⁺(1, 3)`; Chasles; Lancret; the crystallographic restriction;
  the hypergeometric monodromy and the Schwarz map; Hill's Floquet kinds for the pump; the Weyl
  split and Petrov; Raychaudhuri; the reversibility of linear diffusions; polar factors over exact
  square-root extensions; and the chase consumer of `(v, v′)`.

## 10. The first draft's errors (corrected above)

GPT-6 Astra's review found these in the draft, and they are corrected in place:
- "Turn and boost are receiver-relative" conflated recharting (which moves nothing) with a change of
  receiver; `αI` is a boost for every metric.
- The energy law omitted the metric's motion and the forcing.
- "An ideal grip only turns" holds only for a stationary grip.
- "Sources and pumps are pushes": a source across the motion turns; a pump acts through `Ġ`.
- "Storage is inertia": inertia is the kinetic relation only; "free fall is lossless, sourceless
  motion" wrongly included oscillators.
- The pivot decomposition assumed a semisimple eigenvalue and a positive metric, which excluded free
  fall itself, the shear.
- "A boost holds the bearing" holds only for scalar dilations.
- The velocity's logarithm was offered as the universal carrier; it fails at rest.
- The pendulum's rope does not supply the whole normal acceleration; gravity's radial part enters.
- The sling was presented as a metric change; it is a turn about a pivot that is not the receiver's
  centre.
- The chase's law omitted the mover's coefficient and the lattice conversion, and the turn's chord
  its absolute value.
- "Nothing derived the anchor" was false for the HNN junction.
