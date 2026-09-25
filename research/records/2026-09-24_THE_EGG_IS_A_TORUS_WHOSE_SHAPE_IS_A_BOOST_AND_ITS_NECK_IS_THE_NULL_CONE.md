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

## 3. The two singular fibres, and the neck as an exchange

Settled with Sol (GPT-6), September 25; the first version of this section had the wrong
differential and counted the neck as one node.

`[proved-derived]` **The projective family.** Homogenizing gives
`𝓕_w = ((a²+w²)Z + 2wX)Y² − b²Z(a²Z² − X²)`.

**At `w = a`: the neck, Kodaira `I₄`.**
- `𝓕_a = (X + aZ)(2aY² + b²Z(X − aZ))`: a line and a conic.
- They meet transversely at `[−a : ±b : 1]`, with separate points at infinity `[0:1:0]` and
  `[1:0:0]`.
- The total surface has an ordinary double point over each crossing. Resolving both inserts two
  components, so the minimal smooth fibre is a cycle of four rational curves.
- The positively oriented monodromy on `H₁` is conjugate to `[[1,4],[0,1]]`, trace 2: two visible
  nodes, four twists counted with smoothing multiplicity, and one independent primitive vanishing
  class `δ`.
- `[proved-standard]` for the `I_n` classification (Kodaira 1963; Tate 1975).

**At `w = 0`: the ellipse, Kodaira `I₂`.**
- The complete projective fibre is `Z(a²Y² + b²X² − a²b²Z²) = 0`: the line at infinity plus the
  ellipse, meeting at `[a : ±ib : 0]`, where the total surface is smooth.
- The monodromy is conjugate to `[[1,2],[0,1]]`, trace 2. The affine ellipse is one component of a
  singular fibre, not a smooth genus-one fibre.

**The Legendre check.**
- With `A = (a−w)²` and `B = (a+w)²`, the generic fibre is `V² = u(u−A)(u−B)`, with
  `Δ = 256a²w²(a²−w²)⁴` and `c₄ = 16(a⁴ + 14a²w² + w⁴)`.
- `c₄ ≠ 0` at `w = 0, a`, so the discriminant orders 2 and 4 give `I₂` and `I₄` independently.
- `λ = A/B` approaches 1 once at `w = 0` and 0 twice at `w = a`. The Legendre fibre at `∞` is
  `I₂*`, outside `0 < w ≤ a`.

**The period that grows.**
- The regular differential is `ω = dx/F_y = dx/(2(a²+w²+2wx)y)`.
- The real egg oval is the cycle crossing the neck, dual to the vanishing cycle around the colliding
  branch points `u = 0, A`:
  `∫_egg ω = (2/(b(a+w)))·K(√(1−λ)) = (1/(ab))·log(8a/(a−w)) + O((a−w)log(1/(a−w))) = (1/(2ab))·log(1/λ) + O(1)`.
- In the rapidity chart (`λ = k⁻⁴`, `χ = log k`) the leading term is `2χ/(ab)`: the time around the
  egg is linear in the rapidity.
- The vanishing cycle's own period tends to `iπ/(2ab)`: its loop shrinks, its period does not.
- The old form `dx/y` is not the regular differential. Its egg period stays finite.
- `[proved-standard]` for the complete-elliptic-integral asymptotic (DLMF §19.12).

**What "null" means here** `[definition]` (Brandon, September 25: "it's not that there's literally
nothing there, it's an exchange/transport").
- Trace 2 is the lightlike class of the site classification: zero interval, pure transport at the
  characteristic.
- The neck is where the family's topology changes: the level at which interior and exterior
  exchange. It is not an absence.
- The scalar face (trace 2) does not distinguish the two boundary parameters; their return words
  do, `T_δ²` at the ellipse and `T_δ⁴` at the neck.

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
  - the `I₄`/`I₂` fibres, their monodromies `T_δ⁴`, `T_δ²` and the egg period `2χ/(ab)` (§3, settled
    with Sol; the Lean statements are owed);
  - Norbury's torus-to-sphere vortex-ring family.
