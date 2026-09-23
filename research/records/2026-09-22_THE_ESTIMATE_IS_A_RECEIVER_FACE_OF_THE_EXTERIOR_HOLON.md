# The estimate is a receiver face of the exterior Holon

**Date:** 2026-09-22. **Status:** corrected research proposal for Claude iteration. This supersedes the external-majorant framing and floating-point source plates in the earlier surface-current deposit. It does not claim RH, Hodge, BSD or Navier–Stokes has been proved.

## Brandon's correction

A geometry should supply the *form* of the relation that a proof reads. The prior proposal put an inequality outside the object and asked the source to satisfy it. That is backwards for the Holonic programme. The primary task is to construct the source-conforming Holon whose cells, constitution, reflected ports, generator words and receivers determine the relation. An inequality, when useful, is a face of its power or area reading. It is not an independent controller and cannot be inserted as an unexplained majorant.

The same correction applies to representation. A complex number or a sine value is not natively a floating-point sample. The analytic source is a convergent series/generator with a domain, remainder or exact functional identity. An image is a receiver chart of that source. The earlier sampled mpmath zeta and sampled complex-flux contour packets were removed; the replacement figures use exact dyadic interval jets, a rational shear and symbolic trigonometric generators.

## Exterior lift of the foundational Holon

Do not introduce a rival primitive. Start with H=(K,∂ₐ;Π;𝒟;𝓔;G;π) and construct its graded exterior realization Λ•_G H. At each grain ℓ it has:

- oriented chains K_ℓ and their boundary; the connection transports fibre coefficients, with curvature recorded on a cell rather than erased;
- blades v₁∧⋯∧vₖ and their induced metric pairing det(⟨vᵢ,vⱼ⟩_G), wherever G is positive on the relevant span;
- k-face flow and dual effort ports whose pairing is power, with the Dirac structure canceling internal shared-face power;
- constitutive element relations for storage, flux, resistive contacts, sources, active work and deposition;
- generator words w, clocks, phase lifts, reflected words and incidence-preserving restrictions π_(ℓ←ℓ+1);
- receiving Holons that read oriented area/volume, boundary flux, winding, class pairing, and unresolved interior fibres.

The exterior lift is itself a Holon only when the port joining, element relations and restrictions are closed under this lift. That closure is a formal obligation, not obtained by naming Λ•.

A simple state/observer chart, analogous only in shape to an SSM, is

  state:    ∂_τ q_ℓ + d β_ℓ = s_ℓ,
            β_ℓ ∈ 𝓔_ℓ(q_ℓ, d_A μ_ℓ, pair slips, generators),
            Θ̇_ℓ = Dep_ℓ(reached covectors);

  observer: y_(ℓ,R) =
            (⟨q_ℓ, Ω_R⟩, ⟨β_ℓ, ∂Ω_R⟩,
             ⟨class coholon_R, current_ℓ⟩, receiver's own state).

Here q is an n-form of stored current on an n-cell and β an (n−1)-form of flux. The ordinary exterior d in the balance gives Stokes. Connection-valued d_A transports the coefficient fibres and may have d_A²=F_A; nonzero curvature becomes a cell face. A source or active element appears in s and port power. A receiver is itself a joined Holon, not merely a matrix C.

The local law has an exact gluing identity:

  ⟨dβ, Ω₁+Ω₂⟩ = ⟨β, ∂Ω₁+∂Ω₂⟩.

The shared oriented face cancels when both Holons present the same trace with opposite incidence. If traces differ, the mismatch is an interface current, not a failed numerical tolerance. Under grain restriction the requested naturality square is

  π_(ℓ←ℓ+1) T_(ℓ+1,w) = T_(ℓ,w) π_(ℓ←ℓ+1)

on incidence, exterior blades, constitution, ports, phase/carry and receivers. If it does not commute, retain its typed defect and its future-distinguishing fibre. Reflection R is a typed involution on these objects; it must preserve or reverse the declared orientations and power pairing as stated by the source.

## Fractal generators give exact scale laws

Foundation/FractalPacking.lean already gives the exact two-branch maps g_L(x)=x/3 and g_R(x)=(x+2)/3, ordered address words, child containment and sibling separation. For a word w of length n, its interval length is exactly 3^(−n). Finite induction over the two addressed children gives 2^n cells and exact total length (2/3)^n; that population-level statement is not yet a named Lean theorem. This is a generator/receiver law, with no sampled coordinate or auxiliary majorant. An infinite compatible survivor requires the actual nested-family construction; a display of a few levels alone is not that construction.

The new formal theorem sibling_total_width in that owner proves the one-step receiver law exactly: width(leftChild c)+width(rightChild c)=(2/3)width(c). Focused Lean compilation passed; its axiom audit contains no sorryAx. Iterating the law over the addressed child population gives the level relation above, while a separate inverse-limit construction is still needed for the infinite survivor.

For an n-dimensional generator g_w, the area/volume face is induced by Λ^k Dg_w and the constitutive metric, not by an authored width/height ratio. A nonlinear or overlapping family must retain its Jacobian, multiplicity, orientation and preimage fibres. Reflection across a boundary can be another generator only if it acts on the actual source law and gluing data. The scale limit is a compatible section of the Holon tower; a comparison inequality may be derived from its positive constitution, but is not the definition of the tower.

## What the four subjects ask of this object

**RH.** The source is the completed-zeta/heat series with its actual functional equation, not a plotted zero. One exact analytic chart is the Euler–Maclaurin generator, on its admitted domain:

  ζ(s)=Σ_(n<N)n^(−s)+N^(1−s)/(s−1)+(1/2)N^(−s)
       +Σ_(k=1)^M [B_(2k)/(2k)!](s)_(2k−1)N^(−s−2k+1)+R_(N,M)(s).

The remainder is part of the chart, not discarded when the finite word is rendered. A phase coholon reads α=(2π)⁻¹ Im(dF/F) on zero-free cells; its exterior current dα reads zero multiplicity on two-faces. Anti-linear reflection J(s)=1−conj(s) acts on source, divisor and face orientation. The Riemann claim is that the normal off-line class of the source-conforming *global* divisor Holon vanishes. A candidate proof constructs a natural transformation from the exact ζ generator through reflected finite divisors and their tower to that class, then shows the class is forced to zero by the object's source-specific constitutive/holonomy law. The formal finite split in RH/FiniteZeroCurrent.lean is one bounded component. The reflected-quartet polynomial shows why a reflection-only Holon cannot force the class to vanish. Any positive-current inequality is a receiver face of a stronger source law, not a free hypothesis promoted to an explanation.

**Hodge.** The finite Hodge complex already supplies exact/coexact/harmonic states, but a global Hodge class is an object in a rational (p,p) cohomology receiver. Algebraic cycles give a morphism into it. The conjecture asks whether that morphism is essentially surjective on the stated class, with Poincaré duality, rationality, polarization and analytic comparison supplied by the source. Exterior area/period pairing describes the receiving law. The proved shear shows that a class can remain fixed while a harmonic representative moves; a metric-dependent observer cannot substitute for the cycle-class morphism.

**Complex Euler/Navier–Stokes.** A smooth fluid motion realizes q=C_i vol₃ and β_i=ι_(C_i u−ν∇C_i) vol₃, with signed source S_i and joined boundary ports. For U=a+i b, the real and imaginary constitutive terms must be expanded from the same complex source. In the exact plate, sine denotes the entire generator sin z=Σ_(m≥0)(−1)^m z^(2m+1)/(2m+1)!; its displayed face law follows symbolically from that generator and a divergence-free U, with no sampled field. It is one instantaneous datum, not a PDE solution. A global result would be a source-conforming extension of this solution Holon through the terminal time in a category whose receiver detects the required regularity, with all interior and boundary fibres retained. The existing dyadic canonical-derivative condition is one possible observer of such an extension. It is not the Holon. A proof cannot define the extension into existence: it must derive it from the PDE and initial data, including the nonlinear hidden-mode return.

**BSD.** The Néron–Tate regulator is the squared exterior covolume of a positive-definite height lattice, while the real period is an integral receiver of a differential. The local Frobenius factors and global L-series are generator faces. The BSD claim is a source-specific relation between these analytic, arithmetic and determinant-line receivers. A generic scale or reflection geometry does not identify them.

## Formal construction order

1. Define the exterior realization as an operation on the existing Holon facets, including induced metric, orientation, power ports and curvature face. Prove the exact shared-face Stokes/Dirac identity and state the conditions for closure under Holon interconnection.
2. Give reflection and addressed fractal restriction as morphisms of the whole exterior Holon. Prove the scale square or return its actual defect. The exact Cantor family is the control; a source-specific ζ or fluid instance must supply its own generator.
3. Bind each existing RH/Hodge/NS/BSD source to that operation through a typed, noncircular source morphism. The source equation, constitutive relation and observer equation travel together.
4. Ask whether the desired global statement is a zero obstruction, a surjective class map, an extension through a terminal boundary, or a determinant-line identity. Use inequalities only when they are proved readings of the source Holon's constitution.

This is a different problem statement from searching for an arbitrary estimate. It also preserves mathematical accountability: the Holon must be shown to conform to the actual source and to possess the claimed global section. Calling a missing source-specific law a Holon would merely rename the gap.

## Exact figures and previous deposit

The replacement source plates in research/papers/source/papers/categorical-holonics/figures/source-hatches.typ show (1) rational interval subdivisions and the actual Euler–Maclaurin ζ jet/receiving square, (2) the exact rational Hodge shear, (3) a symbolic complex Euler/NS normal-flux generator, and (4) categorical state/observer and scale squares of the exterior Holon. The volume-flux figures were likewise rebuilt with integer/rational geometric charts and no invented zero trajectories. The previous sampled contour scripts and JSON packets were deleted. Projection coordinates only place ink; their mathematical captions identify the source law and remain conditional where that law has not been proved.

The previous research record, 2026-09-22_REFLECTED_SURFACE_CURRENTS_AND_FRACTAL_VOLUME_TOWERS.md, retains the conditional classical derivations and literature/source route. Its external-majorant framing and numerical-plate description are superseded by this correction.
