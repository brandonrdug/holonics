# The shadow is the receiver's kernel, and the egg is two rings in relative motion

**Date:** 2026-09-26. **Status:** a derivation, audited by Sol before it was presented; the corrections are applied in
place (#62; step 6).
**Occasion.** Brandon asked for more work on Hügelschäffer's egg, together with entropic lenses and
the gradient between the integrating and differentiating roles across relativistic frames, and for
the shadows to be derived alongside the receivers. He supplied two figures: the egg and hyperbola
family, and the vesica piscis with its egg profiles. In his words: "light and shadow are coupled,
one is the literal energy stuff and one is the gaps between the literal energy stuff … the gaps
between light is the music … shadows are legitimately how you would think of the image (face) of a
massive structure … that is *difference*." He also reminded me of the golden ratio, of the Rubik
groups with God's Algorithm, and of compression is intelligence is navigation.

Grades:
- [proved-standard]: established mathematics or physics;
- [proved-derived]: checked here or in a cited record;
- [derived]: follows from the stated objects;
- [conditional]: holds under a named hypothesis;
- [image]: a reading, not yet a derivation.

Prior records carry the pieces:
- the egg as an elliptic curve (2026-09-24);
- shadows as projections, after Tufte's *Shadows of Feynman Diagrams* (2026-08-20);
- integrating and differentiating roles as the inertia of a rate form (2026-09-15);
- Rubik faces as navigation graphs (2026-09-19);
- the golden reciprocal (2026-09-12).

## 1. The shadow is the receiver's kernel

- [proved-standard; the names are definitions] For a finite-dimensional linear receiver
  `R : S → F`, `dim im R + dim ker R = dim S`. We call the image the face and the kernel the
  shadow: the differences the receiver cannot distinguish. No canonical split of a source into a
  visible part and a shadow exists without a chosen complement. The cokernel `F/im R` is the
  co-shadow, the output the receiver cannot reach. A nonlinear receiver has an
  indistinguishability relation `x ~ y ⟺ R(x) = R(y)` in place of a kernel.
- [proved-derived; repository owners] The *minimal* retention quotient identifies precisely the
  differences no admitted future receiver distinguishes (`Foundation/Standing`,
  `Holarchy/Hearing.futureNull_le_ker_present`: the future kernel lies in the present kernel). A
  lawful retention may keep more distinctions than that. The landmark tree's standing being this
  quotient is [conditional]: it needs its own map from the source to the future faces.
- [derived] Face and shadow always arrive together at every reception: every face is cast with its
  shadow.
- [image] "Light and shadow are coupled, always present simultaneously" is this complementarity.

## 2. Objects are seen by their shadows

- **The optical theorem** [proved-standard]. Unitarity gives `σ_tot = (4π/k) Im f(0)`, which
  includes scattering and any absorption or inelastic removal. A zero total cross-section in a
  channel means no scattering or absorption in that channel. Visibility in general depends on the
  probe and the field measured. "What we see of a structure is what it removes" is an **[image]**.
- **Babinet** [conditional: scalar Kirchhoff diffraction with ideal complementary screens]. The
  complex fields of complementary screens sum to the unobstructed field. It is not a general
  identity for vector fields or intensities. "Two faces of one wave" is an **[image]**.
- **A mass's shadow** [proved-standard]. For a Schwarzschild black hole, the critical impact
  parameter of null rays is `√27 GM/c²`, set by the unstable photon orbits. The apparent angular
  size needs the observer's distance and position.

## 3. The shadow makes the heat

- **Unruh** [proved-standard: Bisognano–Wichmann, under the QFT hypotheses]. The Minkowski vacuum
  restricted to a Rindler wedge is KMS with respect to boosts. A detector on an eternal uniformly
  accelerated trajectory of proper acceleration `a` responds thermally at `T = ħa/(2π c k_B)`.
  Vacuum correlations across the wedge's horizon underlie that KMS property. The horizon is the
  region the receiver can never receive from, and calling it its shadow is an **[image]**. A KMS
  temperature is not itself heat, and no general heat flux across the horizon follows.
- **Bekenstein and Hawking** [proved-standard]. A black hole's entropy is
  `S = k_B c³ A/(4Għ)`, with `A` the *horizon* area: Bekenstein proposed the proportionality and
  Hawking's radiation fixed the coefficient. `T = ħc³/(8πGMk_B)` holds for an uncharged,
  nonrotating hole, measured at infinity. A projected optical shadow has no such entropy.
- [image] **Temperature as a receiver's shadow.** An inertial detector reads the vacuum. An
  eternally accelerated one, whose frame has a horizon, responds thermally. This is not a derived
  temperature law.

## 4. The egg is the face of two rings in relative motion

- **The construction** [proved-standard; the egg record]. Hügelschäffer's egg is de La Hire's
  ellipse built from two circles, radii `a > b`, with the smaller circle's centre displaced by `w`:
  `(a² + w² + 2wx)y² = b²(a² − x²)`. With the circles concentric (`w = 0`) it is the ellipse.
- **The modulus** [proved-derived; the egg record].
  - For `0 < w < a` the curve is a genus-one curve whose modulus is
    `λ = ((a − w)/(a + w))² = k⁻⁴`, with `k = √((1+β)/(1−β))` at `β = w/a`. Reading `β` as a velocity
    and `k` as a Doppler factor is an assigned **[image]**, and so are "rest frame" and "lightlike
    limit".
  - At `w = 0` the affine oval is an ellipse, while the complete projective cubic is an `I₂` fibre.
    The neck (`w = a`) is Kodaira `I₄`.
  - The egg's period grows as `2χ/(ab)` with `χ = log k`, for the record's regular differential.
- **The two circles as two receivers** [image]. The egg can be read as a face of two rings with a
  displacement parameter. Reading that parameter as receiver-relative motion needs a receiver and
  a transport map. The bounded oval and the unbounded branch are the curve's two real components
  [proved-standard]; once a group origin is chosen, translation exchanges them.
- **The vesica piscis is a lens** [proved-standard; the figure's panel a].
  - Two equal circles, each through the other's centre, intersect in a biconvex lens. Its height is
    `√3` times the radius.
  - The lens is the geometric intersection of the two discs. Its two corners are where the circles
    meet.
  - [image] Reading the lens as two receivers' common face, and its corners as landmarks, needs
    receiver and optical maps. A convex shape alone does not focus rays.
- **The listed dimensions are quadratic surds** [proved-standard]. `√2`, `√3`, `2 − √2` and
  `(1+√3)/2` are constructible by compass and straightedge. The figure's remaining labels are
  unverified. The repository carries them exactly as their constraints
  (`compression::landmark::quadratic::QuadraticSurd`).

## 5. The integrating and differentiating roles are read by the receiver's frame

- **Roles as inertia** [proved-derived; the 2026-09-15 record]. For `ẋ = Ax + s` read with the
  metric `G`, the source-free rate form is `Σ_G = A*G + GA + Ġ`. Its negative directions integrate
  (contract), its positive directions differentiate (expand), and its null directions transport. A
  constant chart change acts by congruence, so the counts of each are invariant (Sylvester;
  `inertia.rs`).
- **Doppler** [proved-standard]. One emission is compressed by `k` for a receiver ahead and
  stretched by `k⁻¹` for a receiver behind. One current plays two roles, according to the
  receiver's frame. The coordinate of the gradient between the roles is the rapidity `χ = log k`,
  which adds when boosts compose.
- [proved-derived; correction, Sol] Any invertible chart change, constant or time-dependent
  (`A′ = BAB⁻¹ + ḂB⁻¹`, `G′ = B⁻*GB⁻¹`), gives `Σ_(G′) = B⁻* Σ_G B⁻¹`, so the inertia is
  invariant under all of them, boosts included. The first draft's claim, that only the receiver's
  acceleration moves the roles and that this is Unruh's condition, is **withdrawn**: acceleration
  can occur with constant metric components, and `Ġ` can arise without acceleration.
- [image] The integrating and differentiating gradient is the receiver's rapidity, and the egg's
  period counts it.

## 6. Collisions and transport are priced by the shadow

[proved-standard; hard spheres, leading kinetic order]
- For an identical hard-sphere gas with `σ = πd²`, the mean free path is `ℓ = 1/(√2 nσ)`.
  `1/(nσ)` holds for a test particle among stationary targets.
- `D ~ vℓ/3` and `η ~ ρvℓ/3 ~ mv/σ` are scalings, and their coefficients depend on the kinetic
  model. At fixed `n` and `T`, they scale inversely with the cross-section: the shadow's area.
- [image] In the Navier–Stokes limit, the viscosity is the molecules' shadow.

## 7. The golden ratio is the navigator whose faces compress least

- **Worst approximable** [proved-standard].
  - `φ = [1; 1, 1, …]`, and its convergents are ratios of consecutive Fibonacci numbers.
  - By Hurwitz, every irrational `x` has infinitely many `p/q` with `|x − p/q| < 1/(√5 q²)`, and
    `√5` is optimal because of `φ`.
  - `φ`'s path in the Stern–Brocot (Farey) tree alternates forever: the lock address that never
    settles, the helix that never locks.
- **Compression duality** [image]. `φ` has the shortest navigator, `x ↦ 1 + 1/x`, a single letter
  repeated, and it attains the maximal asymptotic approximation constant in Hurwitz's sense
  (`liminf q‖qφ‖ = 1/√5`). A short navigator against poorly approximated rational faces is the
  purest case of "compression is of navigators, not of faces", once a code and a cost are declared.
- **Robustness** [conjectural picture]. Greene's criterion and MacKay's renormalization support the
  golden circle's exceptional robustness in the standard map numerically. That it is the last to
  break is not proved.
- **Quasicrystals** [proved-standard, once slope, window and projection are declared; the
  September 25 record]. The Fibonacci chain is a cut-and-project set with slope `1/φ`.

## 8. God's Algorithm navigates by shadows

- **The group** [proved-standard]. The Rubik's cube group has order
  `|G| = 43,252,003,274,489,856,000 = 2²⁷·3¹⁴·5³·7²·11`. Its Cayley graph's diameter, God's
  number, is 20 in the half-turn metric (Rokicki, Kociemba, Davidson and Dethridge, 2010) and 26 in
  the quarter-turn metric (Rokicki and Davidson, 2014).
- **Navigation value** [definition; the 2026-09-19 record]. `D(x) = min_g (c(g) + D(T_g x))`, and
  the minimizing moves form the policy fibre.
- **Shadows are lower bounds** [proved-standard]. When the generators descend to a quotient
  (`q T_g = U_g q`), the quotient distance never exceeds the full distance: a shadow's distance is a
  lower bound.
  - Pattern databases (Korf) and Kociemba's two-phase method use such shadows as admissible bounds.
  - The proof of God's number partitioned the group into the cosets of Kociemba's subgroup `H`
    (`|H| = 19,508,428,800 = 2¹⁶·3⁵·5²·7²`; there are `2,217,093,120` cosets, and `H` is not
    asserted normal). The cosets form a set of fibres, and they were solved to establish the upper
    bound.
  - [image] "Optimal navigation proceeds by shadows": pattern databases do give admissible lower
    bounds, while the coset computation plays a different role.
- **Navigation and compression** [proved-standard bounds; the reading is an image]. The group count
  gives a fixed-state information lower bound, `log₂|G|` between 65 and 66 bits. The 20-move
  theorem gives a uniform, generally nonminimal move-word encoding bound, `20 log₂ 18` between 83
  and 84 bits. A shortest word is not unique, and the difference between these bounds is not an
  established overhead without a declared code.

## 9. The joint reading

[image; every line inherits the grades above] Several readings compose here:
- **Face and shadow.** A receiver's face and its shadow (kernel) are one package. Compression keeps
  the face and drops the shadow of every admitted future.
- **Visibility.** An object is seen by what it removes: its shadow.
- **Heat.** A receiver's heat is the entanglement across its horizon (§3).
- **Transport.** Collision transport is priced by the shadow's area.
- **The egg.** The egg is two rings read by a receiver in relative motion. The rapidity is the
  gradient between integrating and differentiating, and its lens corners are landmarks.
- **Navigation.** It proceeds by shadows (lower bounds), and the shortest word is the compression.
- **The golden ratio.** It is where the navigator is shortest and its faces are least compressible.

"Consciousness witnesses the shadows; the gaps are the music" has one exact instance. For the
Dirichlet Laplacian on a disjoint union of intervals, the eigenvalues `(πk/ℓ_j)²` depend only on the
multiset of the holes' lengths, not on their positions (the September 25 record,
`spectralZeta_eq_riemannZeta_mul_geometricZeta`). What that receiver hears is the gaps. As a
general claim about consciousness it is an **[image]**.

## Obligations

- **Lean:**
  - rank–nullity as the face and shadow of a receiver (join `Holarchy/Hearing`);
  - the egg–Doppler modulus identity (owed from the egg record);
  - the quotient lower bound for navigation values;
  - Hurwitz's constant with its optimality at `φ`.
- The chart-invariance of `Σ_G`'s inertia under time-dependent charts, stated in Lean beside
  `inertia.rs`.
