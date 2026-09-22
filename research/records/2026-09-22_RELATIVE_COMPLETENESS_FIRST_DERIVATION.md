# Relative completeness: first formal owner and the derivation route

**Tree:** `f04a664f`. **Status:** draft by Lean worker L3 of the elementary-object formal joins,
for primary review. **Request:** formalize object 7 of the
[elementary objects](../../docs/ELEMENTARY_OBJECTS.md#7-relative-completeness-globe) (owed join 6
of the [cementing record](2026-09-22_THE_ELEMENTARY_OBJECTS_ARE_CEMENTED_AS_THE_HOLONIC_LIBRARY.md#owed-formal-joins-62)),
and set out the route to the full relative completeness theorem from the Einstein lifts paired
with complex Euler/Navier–Stokes. This record proves nothing beyond the Lean module it names.
Everything else below is a graded route with open statements.

## 1. What is now formal

[proved-derived; formal-checked] `formal/elementary-holonics/ElementaryHolonics/Objects/RelativeCompleteness.lean`
states the three clauses over existing owners:

| Clause | Lean | Composed owner |
|---|---|---|
| (1) coupled | `Region.Coupled`: two admitted states with one boundary datum are separated by an admitted boundary future | `CausalRelevance.NonLinear.futureAgreement` |
| (2) not determined | `Region.NotDetermined`: every admitted state's boundary-history fibre holds a state whose difference moves persistently (`PersistentMotion`: after every word it still moves under some generator, and it recurs after a nonempty word) | same; nontrivial fibre is `NotDetermined.fibre_nontrivial` |
| (3) bounds | `Membrane.BoundsInterior`: the membrane is the boundary of the region's declared interior chain, `∂Ω = S`; a bounding membrane is closed and carries zero net exact flux (`Bounds.closed`, `closed_iff_no_exact_flux`) | `ExteriorBoundary.stokes_pairing` |

[definition] Clause (1) is "the boundary datum depends on the interior state"; coupling through a
conserved charge counts. This is the coordinator ruling of 2026-09-22 (the library text is to be
aligned). Clause (1) does not require `β` to vary along the interior dynamics.

[definition] Clause (3) and the dynamics are declared side by side. The membrane is tied to the
region's interior chain, but which cochain values or faces on the membrane the boundary map `β`
returns is not formalized. The membrane witnesses therefore say nothing about the dynamics.

[definition; agent-inferred] Persistence is stated as exact recurrence of the fibre difference (a
discrete Poincaré recurrence). This excludes a quench and every strict contraction. It also
excludes conservative quasi-periodic interiors such as the irrational `3-4-5` rotation of
`Foundation/Standing.lean`. Admitting those needs approximate recurrence against a declared
metric, which is open.

The linear block criterion follows. Take the unit-clock Euler step `E = 1 + M` of
`[x_int; x_bd]' = [[A,B],[C,D]] [x_int; x_bd]` with the exterior reading `x_bd`. Then:

- the future-blind population (`CausalRelevance.futureCollapsed`) is exactly
  `{(u,0) | u ∈ ⋂ₖ ker(C Aᵏ)}` for every `B`, `D` (`mem_blockCollapsed_iff`);
- coupled ⇔ `C ≠ 0` (`block_coupled_iff`);
- not determined ⇔ some `u ∈ ⋂ₖ ker(C Aᵏ)` has `A u ≠ 0` and `(1 + A)ⁿ u = u` for some `n > 0`
  (`block_notDetermined_iff`). This rests on the general one-generator statement: persistent
  motion of a difference `d` holds exactly when `Eⁿ d = d` for some `n > 0` and `E d ≠ d`
  (`ofAdditive_persistent_iff`, `periodic_moves_forever`);
- `⋂ₖ ker(C Aᵏ)` is the greatest `A`-invariant subspace of `ker C`
  (`observabilityKernel_greatest`);
- for a world tube whose outward receiver is `C`, a nonzero interior current in `⋂ₖ ker(C Aᵏ)` is
  lawful silence (`WorldTube.IsLawfulSilence`), and `C (Aᵏ current) = 0` for every `k`
  (`observabilityKernel_lawfulSilence`). Nothing more is proved about the images `Aᵏ current`;
- in finite dimension the horizon `finrank` suffices (Cayley–Hamilton,
  `observabilityKernel_eq_horizonKernel_finrank`). This is Kalman's observability kernel
  [standard: Kalman 1960; Kalman, Ho and Narendra 1963].

[proved-derived; formal-checked] Relativity: refining the receiver family can only remove clause
(2) and only add clause (1) (`Refines.notDetermined`, `Refines.coupled`).

[established-bounded; formal-checked] Positive instances over `ℚ`:

- `linearGlobe_relativelyComplete`: a quarter-turning interior pair plus a mass, with the
  exterior reading the mass;
- `birkhoffGlobe_relativelyComplete`: a nonlinear Birkhoff globe, a quarter turn read only
  through `Standing.planeEnergy`, whose coupling separates two admitted interiors of energies `1`
  and `4`;
- the coarse half of `relativity_witness`.

[counterexample; formal-checked] Each refutes relative completeness of the named region:

- a cold lattice `A = 0` (`coldLattice_fails`) and a quench `A = −1` (`quench_fails`) fail (2),
  although both are coupled with a nonzero fibre;
- the `Millennium/Ricci.lean` triangle flow read by its conserved total fails (2)
  (`ricci_fails`): its fibre vector `(1,−1,0)` moves, but it contracts by `1/2` per tick
  (`theDeviationContractsAtTheWindingRate` at `τ = 1/6`);
- a fully observable interior fails (2), and a sealed interior `C = 0` fails (1);
- the lateral membrane of a strip with open ends fails (3), since a vertex potential has exact
  flux `1` through it (`tubeMembrane_escapes`);
- a hollow edge loop on the complex without its face is closed but bounds nothing
  (`hollowMembrane_closed_not_bounds`);
- the finer half of `relativity_witness`: one dynamics is complete for the mass channel alone and
  incomplete once a second boundary channel that reads the fibre is added.

[definition; agent-inferred] The Gödel phrasing comes from Brandon's direction retained in the
[cementing record](2026-09-22_THE_ELEMENTARY_OBJECTS_ARE_CEMENTED_AS_THE_HOLONIC_LIBRARY.md#brandons-direction-retained),
and it is an analogy. The formal content is only (a) a relatively complete region's receivers do
not separate its states, and (b) which regions are complete changes with the receiver family. No
incompleteness theorem in the logical sense is claimed.

## 2. Boundary integrals that read an interior

[standard] Gauss: `∮_S E·dA = Q_enc/ε₀`. Newtonian gravity: `∮_S g·dA = −4πG M_enc`. In both,
a closed surface reads one interior charge, and the exact part of any potential contributes
zero net flux.

[proved-derived; formal-checked] The discrete counterpart of "exact parts contribute zero" is
`Membrane.closed_iff_no_exact_flux`. It holds for exact coholons only; this module does not
state a named Gauss law with a source.

[standard] In general relativity, ADM mass is a flux integral at spatial infinity [Arnowitt,
Deser and Misner 1962]. Komar mass is `−(1/8πG)∮_S ⋆dξ♭` for a stationary Killing field `ξ`, and
in vacuum it is independent of the closed surface `S` [Komar 1959; Wald 1984, §11.2].

[definition; agent-inferred] Surface independence reads as the continuum form of clause (3)
combined with a divergence-free current.

[standard] The Dirichlet-to-Neumann map `Λ_DN` of a static elliptic problem determines an
isotropic interior conductivity. In dimension `≥ 3` this holds for smooth conductivities
[Calderón 1980; Sylvester and Uhlmann 1987]. In dimension 2 it holds as well [Nachman 1996, for
conductivities with two derivatives; Astala and Päivärinta 2006, for bounded measurable
conductivities]. Anisotropic conductivities are determined only up to boundary-fixing
diffeomorphism. These are statements about recovering the **constitution** from the boundary.

[definition; agent-inferred] Relative completeness concerns the **dynamic state** instead. In
the linear chart, the input–output map depends only on the controllable and observable part
[standard: Kalman decomposition]. The formal object for clause (2) is the unobservable part with
motion. The Schur elimination owner is `Millennium/Reflection.lean`
(`theBoundaryRowCarriesTheTransportAndTheSource`). Its join to the block criterion is not
formalized: the Schur complement `D − C A⁻¹ B` is a static reduction, while the criterion uses
the full word family.

## 3. Birkhoff as the GR instance

[standard] Birkhoff's theorem: a spherically symmetric vacuum solution of Einstein's equations is
locally Schwarzschild [Jebsen 1921; Birkhoff 1923; Hawking and Ellis 1973]. It is static only
outside the horizon (`r > 2GM/c²`); inside, the Schwarzschild region is not static. The vacuum
exterior of a spherically symmetric body extending beyond its horizon radius depends on `M`
alone. A radially pulsating interior therefore radiates no monopole gravitational wave.

[definition; agent-inferred] In the three clauses, under the governing clause (1) of §1:

- (1) holds through the conserved charge `M`: the boundary datum depends on the interior state
  (different interior masses give different exterior geometries), even though it is constant
  along the interior dynamics;
- (2) holds if the spherically symmetric interior motions with fixed `M` form a fibre that moves
  persistently; a pulsation damped to rest would fail it;
- (3) holds: the bounding 2-sphere bounds the interior ball.

`birkhoffGlobe` is a finite algebraic shadow of this reading. It is not general relativity.

[open] The discrete Birkhoff statement is owed. A group `G` acts on a finite complex. `A`
commutes with `G`, and the exterior receivers `C` factor through the `G`-average. Then every
non-invariant isotypic component of the interior lies in `⋂ₖ ker(C Aᵏ)`, and clause (2) holds
exactly when `A` moves some such component. The formal owners already have the pieces (a
representation-theoretic projection and the block criterion), but the join is not stated.

## 4. Entrance and escape currents: the Euler/Navier–Stokes side

[standard] Reynolds transport: the moving-boundary balance of
[MASS_ENERGY §3](../../docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md#3-interior-to-exterior-energy-transport)
reads `d/dt ∫_Ω a = −∮_∂Ω (j − a w)·n + ∫_Ω s`. The term `(j − a w)·n` is the
entrance/escape current, and internal interfaces cancel under gluing
(`HolonicFieldTheoryPassage.oppositeExchange_glues_to_total_conservation`).

[proved-derived; formal-checked] In the spectral chart, `NavierStokesFourierKirchhoff.sum_transfer_add_tsum_compl`
is the Kirchhoff law for triad transfer. At a band-limited slice, `NavierStokesBandLimitedRelevance`
proves:

- zero transfer into the complement of the double cube (`tsum_compl_transfer_eq_zero`);
- exchange-free dissipation of the double-cube mass (`hasDerivAt_bandMass_of_bandLimited`).

[open] The join "the relevance theorem is relative completeness in the spectral chart" is
**not** a consequence of these theorems. With band = interior and far tail = exterior, the owner
gives zero coupling at that instant, so clause (1) fails there. The missing hypotheses are:

1. a time-extended frontier current: band limitation is a one-slice hypothesis, and the owner
   does not propagate it (the nonlinear transfer generally widens the support);
2. a nonzero frontier transfer from the band into a declared exterior shell (the energy flux
   `Π(K)` across wavenumber `K` [standard: Frisch 1995, ch. 6]);
3. a fibre statement: the exterior shell's readings do not determine the band modes, and the
   fibre carries persistent motion.

No owner states 2 or 3. The quantitative version (`NavierStokesTailRelevance`) supplies only a
per-time tail tolerance, and `TailRelevanceControl` remains a hypothesis.

## 5. What the Einstein owners give

[established-bounded; source-inspected]

| Owner | What it gives here |
|---|---|
| `HolonicCurvedArcEinstein` | Gauss–Bonnet as phase holonomy (`gaussBonnet_is_phaseHolonomy`): a closed-surface total is topological (`2πχ`). This is the closed-membrane reading of curvature. It also has a Minkowski control and the Bianchi conservation interface (`flatLorentzVacuumDynamics_conserves`). It has no mass flux integral. |
| `HolonicFieldTheoryPassage` | Exact action gluing over disjoint regions and cancellation of opposite exchange at internal interfaces. A closed reaction ledger makes an unseen carrier the exact remainder: an exterior deficit is read as an interior/escaping term, not as leakage. |
| `CurvatureAndGap` | `F = dA + A∧A`, with the commutator as the nonabelian term; mass as the first rung; the area law as face-over-boundary. |
| `Ricci` | A total-conserving diffusion on the triangle: a total receiver sees nothing of the deviation, but the deviation contracts. Now encoded: `RelativeCompleteness.ricci_fails` proves the contracting fibre fails clause (2), in contrast with the recurrent globe. |
| `Reflection` | Exact elimination of a declared interior onto its boundary, where the boundary is a declaration. This is receiver relativity in the static chart. |

None of them states a Gauss/ADM/Komar flux theorem, a Birkhoff theorem, or a dimension-dependent
radius law.

## 6. Bounding radius against dimension

[standard] For `d` spacetime dimensions, the Schwarzschild–Tangherlini exterior has
`f(r) = 1 − (r_s/r)^{d−3}` with `r_s^{d−3} = 16πGM / ((d−2) Ω_{d−2} c²)`, where
`Ω_{d−2} = 2π^{(d−1)/2}/Γ((d−1)/2)` is the area of the unit `(d−2)`-sphere [Tangherlini 1963;
Myers and Perry 1986]. At `d = 4` this is `r_s = 2GM/c²`.

[standard] The unit `n`-ball volume `V_n = π^{n/2}/Γ(n/2+1)` is maximal over real `n` at
`n ≈ 5.2569`, and at the integer `n = 5`. The unit sphere area `S_{n−1} = n V_n` is maximal near
`n ≈ 7.2569`.

[standard; citation owed] Higher-dimensional Birkhoff-type uniqueness of the spherically
symmetric vacuum exterior is stated in the literature. The exact reference is to be supplied
before it is used.

[open] How the bounding radius enters a globe criterion is not derived. The candidate reading is
that the closed membrane's area factor `Ω_{d−2}` sets the flux normalization of the mass reading,
through Gauss/Komar. Any claim that the criterion selects a dimension (for example through the
`n`-ball maximum) is unsupported, and this record does not assert it.

## 7. Open theorem statements (#62)

1. **Discrete Gauss with source.** On a finite complex with `∂j = σ` (`JunctionLaw`) and
   `S = ∂Ω`, the membrane flux of `j` equals the total source in `Ω`. This is a named join of
   `stokes_pairing` and the junction law.
2. **Discrete Birkhoff.** The symmetry statement of §3.
3. **Nonlinear clause (2).** Local relative completeness via the observability rank condition
   of the linearization [standard: Hermann and Krener 1977], joined to `Region.NotDetermined`,
   together with an approximate-recurrence form of persistence that admits quasi-periodic
   conservative interiors.
4. **Spectral join.** The three hypotheses of §4, stated on the Navier–Stokes owners.
5. **The relative completeness theorem.** For a region `Ω` with closed `∂Ω` in a `d`-dimensional
   Einstein chart carrying a complex Euler/Navier–Stokes current, relative completeness for the
   asymptotic receiver family would hold when:
   - a quasi-local or Komar mass flux through `∂Ω` is nonzero (1);
   - the interior admits motions that change no exterior multipole flux, i.e. non-radiating
     modes with motion (2);
   - `∂Ω` bounds the interior chain, and the boundary map is joined to the membrane's faces (3).

   The bounding radius law is to be derived from the flux normalization. Every part of this
   statement is `[open]`.

## Sources

Arnowitt, R., Deser, S., Misner, C. W. (1962), *The dynamics of general relativity*.
Birkhoff, G. D. (1923), *Relativity and Modern Physics*. Calderón, A. P. (1980), *On an inverse
boundary value problem*. Frisch, U. (1995), *Turbulence*. Hawking, S. W., Ellis, G. F. R. (1973),
*The Large Scale Structure of Space-Time*. Hermann, R., Krener, A. J. (1977), *Nonlinear
controllability and observability*, IEEE TAC 22. Jebsen, J. T. (1921), Ark. Mat. Astron. Fys. 15.
Astala, K., Päivärinta, L. (2006), Ann. Math. 163. Kalman, R. E. (1960), *On the general theory of control systems*; Kalman, Ho, Narendra (1963),
*Controllability of linear dynamical systems*. Komar, A. (1959), Phys. Rev. 113. Nachman, A. I. (1996), Ann. Math. 143. Myers, R. C.,
Perry, M. J. (1986), Ann. Phys. 172. Sylvester, J., Uhlmann, G. (1987), Ann. Math. 125.
Tangherlini, F. R. (1963), Nuovo Cimento 27. Wald, R. M. (1984), *General Relativity*.
