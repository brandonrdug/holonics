# Swing, stress and interior feedback form the fluid construction

[project-postulate] Brandon asked whether Holonics had actually synthesized interior/exterior,
microscopic/macroscopic, complex Euler and Navier–Stokes from Swing and the computational
Holon, with Hodge, RH and BSD connected through the same research. This continues the
September 14 exact-mode, active-stress and fractal corrections. It does not restart the
paused Athena goal or make an unsolved Millennium endpoint a prerequisite for its product.

## Recovered construction and the missing join

[established-bounded; source-inspected] The prior source already contains real derivations:
nonlinear Lamb current and pressure/stretching/diffusion; finite Galerkin advection and local
Picard existence; clocked source Swing; Hodge/Green and temporal residue; changing fluid
receivers; dynamic boundary elimination; and the September 13 Elsasser/complex-fluid sign
identities. The [connected derivation](../../docs/HOLONIC_FLUID_CONSTRUCTION.md) retains their
exact source links and develops the missing primitive-to-balance account. “Never attempted”
would misstate that source history. Leaving the results scattered made their composition
and implementation consequences unnecessarily obscure.

## Returned mathematical products

[proved-derived; formal-checked] The native normal solve is graph-projection Swing.
With K=I+DD†, let a=K⁻¹(u+Db); then P_G(u,b)=(a,D†a), and the actual emitted/held pair
is R_G=2P_G−I. The exact solve identity proves P_G²=P_G and R_G²=I. The theorem refers to
the original `Millennium.Swing.swing`, not a new verbal use of “reflection”.

[proved-derived; formal-checked] Inverse paired couplings additionally satisfy
R_C(x,y)=(Cy,C⁻¹x). Composing with the identity-graph Swing yields
R_C R_I=diag(C,C⁻¹). These are `graphScattering_inversePair` and
`paired_graphSwings_transport` in the same existing constitutive owner.

[proved-derived] For an energy-compatible finite advection J with J†=−J, the Cayley
operator C_h=(I−hJ/2)⁻¹(I+hJ/2) is an isometry. The paired-Swing identity realizes that
conservative advection step and its reverse on the two carriers. Its rational operator
identity is exact; its finite-step approximation to the continuous frozen-field flow is
stated separately. The changing advecting field remains a nonlinear operand.

[proved-derived; formal-checked] The actual finite-Galerkin N=S_ν−B(self,self) has

```text
N(b+r)+N(b−r)=2[N(b)−B(r,r)],
N(b+r)−N(b−r)=2[S_νr−B(b,r)−B(r,b)],
N(2b−u)+N(u)−2ḃ=2[N(b)−ḃ−B(u−b,u−b)].
```

The moving rate uses −I plus 2ḃ. Applying the affine state map to a rate instead would
have produced a false defect. `FluidReceiverClosure` now proves these identities using
its actual Galerkin convolution/Leray/Stokes owners. Its existing moving-receiver theorem
carries the same full feedback into the coarse equation.

[proved-derived] The written synthesis derives Euler by varying kinetic action along
volume-preserving material motions; it derives Newtonian NS by adding the complete
constitutive stress. Relativistic energy and momentum projections follow from the
perfect-fluid stress tensor, with heat/shear stress carried through their covariant
divergence. Hodge pressure elimination and physical curved-manifold viscosity retain
their distinct domains. Boundary memory and microscopic unresolved stress are derived
as two receiver cuts of a continuing interior.

[proved-derived] A specified internal-field class now has a complete written construction:
μ_Q=W'(Q)−κΔQ, advection A_Qu=u·∇Q, its adjoint force P(μ_Q∇Q), and positive
mobility M. Opposite advection/adjoint powers cancel, leaving viscous and material
dissipation. The derived directional stress is
`σ_Q=[W(Q)+κ|∇Q|²/2]I−κ∇Q⊗∇Q`. This recovers a classical phase-field fluid class
through the Holon's operations and supplies an explicit more-resolved alternative to a
velocity/pressure-only closure. Smoothness, boundary conditions, units and constitutive
operands are stated. Its continuum Lean formalization/native field consumer are not
claimed to exist.

[proved-derived; formal-checked] The existing arithmetic companion
M=[[a,−q],[1,0]] now has the exact scaled metric G=[[1,−a/2],[−a/2,q]] with MᵀGM=qG.
`LocalFactor.companion_preserves_scaled_metric` and `companion_metric_complete_square`
prove the identity and completed square. Strict a²<4q supplies the positive pairing;
the equality boundary degenerates. This rejoins the actual BSD local transfer to a
constituted phase/energy relation, retaining its arithmetic source.

[definition] The same derivation connects Hodge harmonic circulation and heat traces to
fractal scale questions, and retains the existing RH critical-coordinate/time map and
BSD transfer/determinant/trace equations. It neither equates their sources by shared
notation nor discards the reusable operators because their global endpoints remain open.
Complex-bilinear Euler/NS and conducting-fluid induction retain their different stretching
signs and real-energy consequences.

## Integration and verification

[established-bounded; source-inspected] The Holon guide, model formula, formal framework,
mathematical synthesis, fluid/reflection guide and architecture map now point through the
same derivation. The prior thirteen-page exact-mode and active-face synopsis remains the
completed illustrated return in `7cdeaa5f`; this mathematical extension is reusable source
work rather than another presentation campaign.

[established-bounded; process-audit] The targeted build covers
`ElementaryHolonics.Computation.HolonicConstitutiveCirculation`,
`ElementaryHolonics.Physics.FluidReceiverClosure`, and
`ElementaryHolonics.Millennium.LocalFactor`. The initial LocalFactor build required the
symbolic real metric definition to be marked noncomputable; that Lean elaboration issue
was corrected without changing its exact mathematics. The final targeted build passed (3868 jobs); its result is recorded in
`.local/artifacts/2026-09-14-exact-faces/fluid-synthesis-build-final.log`.
The new theorem audit output uses the existing `propext`, `Classical.choice` and
`Quot.sound` foundation, with no `sorryAx`.

[open] The continuum Q-field consumer and a general microphysical derivation of its
constitutive coefficients remain explicit implementation/research work. The written
construction is complete at its specified constitutive scope. The native Athena
assembly's current/material/encoded-action join remains separately recorded in
CONSTRUCTION_STATE; it is not replaced by this fluid derivation or by another lifecycle
condition.
