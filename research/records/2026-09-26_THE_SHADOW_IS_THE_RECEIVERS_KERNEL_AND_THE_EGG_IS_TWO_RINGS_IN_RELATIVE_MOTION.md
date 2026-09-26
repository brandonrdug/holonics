# The shadow is the receiver's kernel, and the egg is two rings in relative motion

**Date:** 2026-09-26. **Status:** a derivation with grades, sent to Sol for audit before it is
presented (#62; step 6).
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

- [proved-standard] A linear receiver `R : S → F` splits every source into what it shows and what
  it cannot show. In finite dimension, `rank R + nullity R = dim S`. The face is the image, and the
  shadow is the kernel: the differences the receiver cannot distinguish. The cokernel is the
  co-shadow: what it cannot reach.
- [proved-derived; repository owners] Holonic Compression's kernel and cokernel are these two, and
  retention is the quotient of the source by the shadow of every admitted future face
  (`Foundation/Standing`, `Holarchy/Hearing.futureNull_le_ker_present`). **What compression keeps
  is the light, and what it drops is the shadow, exactly.** The landmark tree's standing is the past
  modulo the shadow of every admitted future read.
- [derived] Face and shadow always arrive together at every reception: every face is cast with its
  shadow.
- [image] "Light and shadow are coupled, always present simultaneously" is this complementarity.

## 2. Objects are seen by their shadows

- **The optical theorem** [proved-standard]. An object's total cross-section is fixed by the
  forward interference of its scattered wave with the incident wave:
  `σ = (4π/k) Im f(0)`. An object that removes nothing from any beam is invisible. What we see of
  a massive structure is what it removes or redirects.
- **Babinet** [proved-standard, in scalar Kirchhoff diffraction]. The field behind an obstacle plus
  the field through the complementary aperture equals the incident field. Shadow and light are the
  two complementary faces of one wave.
- **A mass's shadow** [proved-standard]. The Schwarzschild shadow's critical impact parameter is
  `√27 GM/c²`, set by the unstable photon orbits.

## 3. The shadow makes the heat

- **Unruh** [proved-standard: Bisognano–Wichmann]. A uniformly accelerated receiver has a horizon:
  a region it can never receive from, its shadow. Restricted to the receiver's wedge, the
  Minkowski vacuum is a thermal (KMS) state at `T = ħa/(2π c k_B)`. The heat the receiver perceives
  is the entanglement across its shadow.
- **Hawking and Bekenstein** [proved-standard]. A black hole's entropy is its horizon area,
  `S = k_B c³ A/(4Għ)`, and its temperature is `T = ħc³/(8πGMk_B)`. The entropy of a massive
  structure's shadow is the area of the shadow's boundary.
- [derived] **Temperature is a receiver's shadow.** An inertial receiver sees the vacuum. An
  accelerating one, whose frame hides a region, sees heat. What is received, the music, is shaped by
  what the receiver cannot receive.

## 4. The egg is the face of two rings in relative motion

- **The construction** [proved-standard; the egg record]. Hügelschäffer's egg is de La Hire's
  ellipse built from two circles, radii `a > b`, with the smaller circle's centre displaced by `w`:
  `(a² + w² + 2wx)y² = b²(a² − x²)`. With the circles concentric (`w = 0`) it is the ellipse.
- **The modulus** [proved-derived; the egg record].
  - For `0 < w < a` the curve is a genus-one curve whose modulus is
    `λ = ((a − w)/(a + w))² = k⁻⁴`, with `k = √((1+β)/(1−β))` the Doppler factor at `β = w/a`.
  - The ellipse is the rest frame. The neck (`w = a`, Kodaira `I₄`) is the lightlike limit.
  - The egg's period grows as `2χ/(ab)` in the rapidity `χ = log k`.
- **The two circles are two receivers** [derived].
  - The displacement between the two generating circles is their relative motion.
  - The egg is the face of two rings in relative motion. The bounded oval and the unbounded branch
    are its two real sheets, exchanged by the curve's `ℤ/2`.
  - At rest the two rings read a symmetric ellipse. In motion, one side is blunt and one sharp. At
    the lightlike limit the displaced circle touches the other: the neck.
- **The vesica piscis is a lens** [proved-standard; the figure's panel a].
  - Two equal circles, each through the other's centre, intersect in a biconvex lens. Its height is
    `√3` times the radius.
  - The lens is the region both circles hold: two receivers' common face. Its two corners are the
    points where the two circles' paths meet.
  - [image] Those corners are landmarks in the objects' sense (faces where navigator paths
    converge). The convex lens converges and the concave complement diverges.
- **Every dimension in the egg-profile figure is a quadratic surd** [proved-standard]. `√2`, `√3`,
  `2 − √2`, `(1+√3)/2` and the rest are constructible by compass and straightedge: navigable by
  words of circle and line constructions. The repository carries them exactly as their constraints
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
- [derived; to be checked] A constant boost is an isometry of the Minkowski form, so it leaves the
  inertia of `Σ_G` unchanged. Only the receiver's own acceleration (`Ġ ≠ 0`) moves the roles, and
  that is the same condition under which Unruh's heat appears (§3).
- [image] The integrating and differentiating gradient is the receiver's rapidity, and the egg's
  period counts it.

## 6. Collisions and transport are priced by the shadow

[proved-standard; hard spheres, leading kinetic order]
- The mean free path is `ℓ = 1/(nσ)`, with `σ` the collision cross-section: the shadow each
  particle casts on the others.
- Diffusion `D ~ ℓv/3` and viscosity `η ~ m v/(3σ)` are inversely the shadow area.
- [image] In the Navier–Stokes limit, the viscosity is the molecules' shadow.

## 7. The golden ratio is the navigator whose faces compress least

- **Worst approximable** [proved-standard].
  - `φ = [1; 1, 1, …]`, and its convergents are ratios of consecutive Fibonacci numbers.
  - By Hurwitz, every irrational `x` has infinitely many `p/q` with `|x − p/q| < 1/(√5 q²)`, and
    `√5` is optimal because of `φ`.
  - `φ`'s path in the Stern–Brocot (Farey) tree alternates forever: the lock address that never
    settles, the helix that never locks.
- **Compression duality** [derived]. `φ` has the shortest navigator, `x ↦ 1 + 1/x`, a single letter
  repeated. Its rational faces converge the slowest among all irrationals. So compression of the
  navigator and compression of the face come apart most at `φ`. This is the purest case of
  "compression is of navigators, not of faces".
- **Robustness** [established numerically, and partly proved: Greene, MacKay]. The golden-mean
  invariant circle is the last to break in the standard map.
- **Quasicrystals** [proved-standard; the September 25 record]. The Fibonacci chain is the
  cut-and-project set with slope `1/φ`.

## 8. God's Algorithm navigates by shadows

- **The group** [proved-standard]. The Rubik's cube group has order
  `|G| = 43,252,003,274,489,856,000 = 2²⁷·3¹⁴·5³·7²·11`. Its Cayley graph's diameter, God's
  number, is 20 in the half-turn metric (Rokicki, Kociemba, Davidson and Dethridge, 2010) and 26 in
  the quarter-turn metric (2014).
- **Navigation value** [definition; the 2026-09-19 record]. `D(x) = min_g (c(g) + D(T_g x))`, and
  the minimizing moves form the policy fibre.
- **Shadows are lower bounds** [proved-standard]. When the generators descend to a quotient
  (`q T_g = U_g q`), the quotient distance never exceeds the full distance: a shadow's distance is a
  lower bound.
  - Pattern databases (Korf) and Kociemba's two-phase method use such shadows as admissible bounds.
  - The proof of God's number partitioned the group into the cosets of Kociemba's subgroup `H`
    (`|H| = 19,508,428,800`, and `|G/H| = 2,217,093,120`). Those cosets are the fibres of a
    projection.
  - Optimal navigation proceeds by shadows.
- **Navigation is compression** [derived]. Every state's shortest word is its address: at most 20
  letters over 18 generators. The code-length pair is the state's information, `log₂|G|` between 65
  and 66 bits, against the worst navigation word, `20 log₂ 18` between 83 and 84 bits. The distance
  between them is the address overhead of the navigator.

## 9. The joint reading

[image] Several readings compose here:
- **Face and shadow.** A receiver's face and its shadow (kernel) are one package. Compression keeps
  the face and drops the shadow of every admitted future.
- **Visibility.** An object is seen by what it removes: its shadow.
- **Heat.** A receiver's heat is the entanglement across its horizon (§3).
- **Transport.** Collision transport is priced by the shadow's area.
- **The egg.** The egg is two rings read by a receiver in relative motion. The rapidity is the
  gradient between integrating and differentiating, and its lens corners are landmarks.
- **Navigation.** It proceeds by shadows (lower bounds), and the shortest word is the compression.
- **The golden ratio.** It is where the navigator is shortest and its faces are least compressible.

"Consciousness witnesses the shadows; the gaps are the music" has one exact instance. The spectrum
of a fractal string depends only on the lengths of its holes, the gaps (the September 25 record,
`spectralZeta_eq_riemannZeta_mul_geometricZeta`). What is heard is the gaps.

## Obligations

- **Lean:**
  - rank–nullity as the face and shadow of a receiver (join `Holarchy/Hearing`);
  - the egg–Doppler modulus identity (owed from the egg record);
  - the quotient lower bound for navigation values;
  - Hurwitz's constant with its optimality at `φ`.
- **To be checked:** that a constant boost leaves the inertia of `Σ_G` invariant, together with the
  exact form of the `Ġ` term for an accelerating receiver.
