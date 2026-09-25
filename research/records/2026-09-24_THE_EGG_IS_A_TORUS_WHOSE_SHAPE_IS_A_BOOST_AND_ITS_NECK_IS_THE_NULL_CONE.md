# The egg is a torus whose shape is a boost, and its neck is the null cone

**Date:** 2026-09-24. **Occasion:** Brandon's question about Hügelschäffer's egg curve and its double
egg that degenerates onto the ellipse. How do they join flux (complex Euler and Navier–Stokes), entropy, and
the toroidal/helical geometry, as "convergence into something prime, and divergence"? The two
ResearchGate figures refuse automated access (HTTP 403); this record works from the standard
construction.

**Truth discipline:**
- Classical results are `[proved-standard]`.
- The algebra first checked here (exact computer algebra) is `[proved-derived]`, pending Lean.
- Correspondences into the objects are `[interpretation]`.
- Lean and Rust obligations are listed at the end.

## 1. The egg is an elliptic curve

Hügelschäffer's construction is de La Hire's construction of the ellipse from two concentric circles
(radii `a > b`), with the smaller circle's centre displaced by `w`. The curve is

`(a² + w² + 2wx) y² = b²(a² − x²)`,

and `w = 0` gives the ellipse `x²/a² + y²/b² = 1`.

`[proved-derived]`:
- For `0 < w < a` the cubic has no affine singular point, and its projective closure is smooth.
- It is therefore a curve of genus one: over `ℂ` a torus `ℂ/Λ`, and over `ℚ` (rational `a, b, w`, with the
  rational points `(±a, 0)`) an elliptic curve.
- With `u = 2wx + a² + w²` and `Y = uy` it becomes, exactly,

  `Y² = −(b²/4w²) · u (u − (a−w)²)(u − (a+w)²)`,

  a quadratic twist of the Legendre curve with modulus

  `λ = ((a−w)/(a+w))² = ((1−β)/(1+β))² = k⁻⁴`, where `β = w/a` and `k = √((1+β)/(1−β))`.

**The egg's shape parameter is a boost.** The displacement ratio `w/a` plays the role of a velocity
`β`, and the curve's modulus is the fourth power of the inverse Doppler ratio. The ellipse is the rest
frame (`β = 0`, `λ = 1`), and the egg opens at the lightlike limit (`β → 1`, `λ → 0`).

## 2. Convergence and divergence are the curve's two real sheets

The cubic has three real roots `0 < (a−w)² < (a+w)²`, so its real locus has two components. `[proved-standard]`
- **The egg:** a compact oval over `−a ≤ x ≤ a`.
- **An unbounded branch:** left of the asymptote `x = −(a² + w²)/(2w)`.

For a real elliptic curve with two real components, `E(ℝ) ≅ S¹ × ℤ/2`. `[proved-standard]` With the origin on
the unbounded branch, the egg is the non-identity coset: egg + egg lands on the branch, and branch + egg
lands on the egg. The bound sheet and the divergent sheet are the two halves of one torus's real
structure, exchanged by the group law. `[interpretation]` They are the parametron's half-turn sheets:
the Ising lock's `ℤ/2`.

As a closed simple curve on the complex torus, the egg oval is a **primitive cycle**, "prime" in the
aeon sense (null-cone record, §5). `[interpretation]`

## 3. The neck is the degeneration, and its monodromy is null

- **`β → 1` (`w → a`).** The asymptote reaches the egg's pointed tip, and the cubic factors as
  `(a + x)(2a y² − b²(a − x))`: a line and a parabola. The oval and the branch meet in nodes at `(−a, ±b)`.
  The egg opens: its tip becomes a wall, and its interior joins the unbounded branch. `[proved-derived]`
- **The torus picture.** A cycle of the torus pinches to a node: the vanishing cycle. That pinch is the
  neck, where convergence meets divergence. `[proved-standard]` (nodal degeneration)
- **Monodromy.** Around the degeneration the monodromy is unipotent, a Dehn twist of trace 2: a **null**
  site in the trace classification (the null-cone record §4; `navigator::trace::SiteKind::Null`).
  `[proved-standard]` (Picard–Lefschetz)
- **Time around the egg.** In the curve's invariant clock `dx/y`, the time around the egg (the period of
  the oval) grows like `log(1/λ) = 4 log k` as `β → 1`. It is linear in the rapidity `χ = log k`, up to a
  fixed scale: critical slowing down at the neck. `[proved-standard]` (logarithmic period near a nodal
  fibre); the rapidity reading is `[interpretation]`.
- **`β → 0`.** The asymptote runs to `−∞`, the divergent sheet leaves, and the curve drops to the conic:
  the symmetric, closed rest-frame ellipse.

## 4. Flux: the converging and diverging pair is the logarithm of a Möbius ratio

- **Potential of a source/sink pair.** For a planar source–sink pair of strengths `±m` with circulations
  `±Γ` at `z₁, z₂`, the complex potential is `F = ((m + iΓ)/2π) · log((z − z₁)/(z − z₂))`, with `Γ` the clockwise circulation (for counterclockwise `Γ`, write `m − iΓ`; `Physics/Fluid/Singularity.circulation_flux_jump`): the logarithm
  of a ratio, the same chart as loss `ℓ = log R`.
  - `Re F` (log of the distance ratio) is the potential: Apollonian circles.
  - `Im F` (the winding) is the stream function: circles through both points.

  `[proved-standard]`
- **Classification by Möbius flow.** The streamlines of point-singularity pairs are the orbits of
  one-parameter Möbius groups with fixed points `z₁, z₂`. `[proved-standard]`
  - **Source–sink pair** (Γ = 0): hyperbolic, a **boost**. The source is the repelling fixed point
    (divergence) and the sink the attracting one (convergence).
  - **Vortex pair** (m = 0): elliptic, a **rotation**.
  - **Doublet** (the pair merged): parabolic, a **null** lock.
  - **Spiral pair** (m, Γ ≠ 0): loxodromic, a spiral inflow and outflow; in three dimensions, the
    helix.

  These are the same site kinds that classify the machine's sites and the egg's degeneration.
  `[interpretation]` of a `[proved-standard]` classification.
- **A body is a globe.** In a uniform stream, the dividing streamline closes into a body exactly when
  the enclosed singularities have zero net strength (Gauss; the Rankine–von Kármán singularity method).
  - Nonzero net emission opens it into a half-body: a tube with asymptotic width.
  - A fore–aft uneven distribution of a zero-sum makes an egg.
  - Closure is relative completeness (ELEMENTARY_OBJECTS §7): the boundary bounds an interior whose net
    flux balances.

  `[proved-standard]`; the globe reading is `[interpretation]`.
- **In three dimensions.** Norbury's family of steady vortex rings runs from a thin-cored **torus** to
  **Hill's spherical vortex** as the ring's hole closes. The cross-sections pass through D- and egg-like
  shapes. The toroidal geometry deforms continuously into the egg. `[proved-standard]` (Norbury 1973)

## 5. Entropy

- **Production across the neck.** Steady diffusion between an emitter and an absorber has the same
  log-ratio potential, since `log r` is the planar Green's function. Entropy production is flux times
  the log of a ratio: Schnakenberg's `σ = ½ Σ (J₊ − J₋) log(J₊/J₋)`, aeon A6. The production across a
  neck is the flux through it times the log-ratio drop. `[proved-standard]`
- **Life against stars.** Chaisson's free-energy rate density (energy throughput per unit mass),
  `[established-bounded; measured]`, order of magnitude, erg s⁻¹ g⁻¹:

  | System | Rate |
  |---|---|
  | Milky Way | ≈ 0.5 |
  | Sun | ≈ 2 |
  | Earth's climate | ≈ 75 |
  | Plants | ≈ 900 |
  | Human body | ≈ 2 × 10⁴ |
  | Brain | ≈ 1.5 × 10⁵ |
  | Modern society | ≈ 5 × 10⁵ |

  Per unit mass, living structure already out-diffuses stars by four to five orders of magnitude.
  Stars dominate total power. England's "dissipative adaptation" is a hypothesis in the same
  direction. `[interpretation]`

## 6. The object

The joint object is a **real elliptic fibration over an aeon's parameter**. In the objects:
- **The fibres:** the torus `E_β` with modulus `λ = k⁻⁴`. Its bounded real cycle, the egg, is a
  primitive cycle ("prime"). Its unbounded real cycle is the divergent sheet. The group law's `ℤ/2`
  exchanges the two sheets.
- **The degenerations:** the discriminant of the fibration vanishes at the rest frame (`β = 0`) and at
  the null limit (`β = 1`). Those are the aeon's epochs; the neck's monodromy is a null site.
- **Flux:** the flux through the family is the logarithm of a Möbius ratio. Its kind (rotation, null,
  boost, loxodromic) is the same trace classification.
- **Entropy production:** flux times log-ratio across the neck.
- **Scale:** a Holarchy has such eggs at every grain: cells, organisms, stars, galaxies. The parameter
  `β` is receiver-relative.

`[interpretation]` as a whole; the constituents are graded above.

## Obligations

- **Lean and Rust (#145 identity atlas; BSD targets):**
  - the exact identity between the egg cubic and the twisted Legendre form, with `λ = k⁻⁴`;
  - the real two-component structure and the degenerate fibres at `β = 0, 1`;
  - rational eggs as elliptic curves over `ℚ`, as a BSD target family (their rational points and ranks).
- **K3 (#74):**
  - planar point-singularity flows as one-parameter Möbius navigators, classified by site kind;
  - a closed body ⇔ zero net strength;
  - Schnakenberg production at a neck.
- **#62:**
  - the Picard–Lefschetz null monodromy and the logarithmic period at the neck;
  - Norbury's torus-to-sphere vortex-ring family.
