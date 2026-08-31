# Entropy is a typed interior-turn current, free energy is a constitutive difference, and induction promotes a local law

Date: 2026-08-26  
Scope: exact microscopic lineage, entropy/heat current, action, free energy, relativistic turn,
electromagnetic induction, proof induction, the Complex Parametron, and the common Millennium
instrument

## Result

[proved-derived; formal-checked] `HolonicEntropyActionInduction.lean` now constructs a common exact
carrier rather than identifying several uses of the word *induction* by analogy.  Its local datum is

```text
coordinate(successor(x)) - coordinate(x) = source(x).
```

Structural induction promotes this one-grain law through every finite successor word and returns

```text
coordinate(orbit(n)) - coordinate(initial)
  = sum of the addressed local sources along the orbit.
```

The theorem uses no limit, rounding, stochastic premise, or deleted intermediate occurrence.

[proved-derived; formal-checked] The existing finite Faraday history is an actual instance of the
carrier: magnetic flux is the transported coordinate and negative oriented face circulation is its
source.  The generic induction theorem reconstructs the exact finite Faraday telescope.  Thus proof
induction and electromagnetic induction share one proved successor-current diagram after the
physical source map is supplied; they are not declared identical as operations.

[proved-derived; formal-checked] The same file constructs the exact entropy world-tube balance

```text
S(k+1) - S(k) + outwardEntropyFlux(k) = interiorProduction(k),
```

and proves its finite telescope.  Stored entropy is monotone only after two additional facts are
declared and used: the admitted side-boundary flux vanishes and the constitutive production is
nonnegative.  This is the precise separation between a kinematic boundary identity and a material
second-law theorem.

[proved-derived; formal-checked] The boundary condition is now receiver-relative rather than
artificially strengthened to source equality.  For any additive receiver, if the complete side
flux lies in its kernel, the received storage difference equals the received production sum.
When every received local production grain is nonnegative, the received storage is monotone; and
its total returned difference is zero exactly when every received production grain is zero.  In
the closed identity receiver this specializes to: finite global entropy change is null if and only
if every nonnegative local production occurrence is null.  Thus monotonicity is the exact
consequence of a declared cone, production law, and killed boundary current.

## What “entropy as an interior turn” now means

[interpretation] The preferred holonic reading of *entropy* as “within a turning” is admitted through
three typed maps, each of which can fire or fail independently:

```text
successor history -> stored/current/produced entropy balance,
inverse-temperature derivative -> symmetric stretch + antisymmetric turn,
potential gradient -> conservative skew circulation + positive dissipative crossing.
```

The phrase is productive because it schedules these maps.  It is falsified as a source realization
whenever the named entropy coordinate, local transport, or constitutive law fails to commute through
them; the phrase alone proves none of those premises.

[proved-derived; formal-checked] For a rational four-axis thermal receiver, the exact local
derivative splits as

```text
D_ij = (D_ij + D_ji)/2 + (D_ij - D_ji)/2.
```

The first part is symmetric stretch.  The second is an antisymmetric turn: exchanging the addressed
directions negates it, and repeating one direction returns zero.  The four-axis carrier therefore
returns six independent turn planes before any `3 + 1` receiver names spatial and temporal faces.

[proved-standard; external-source] In relativistic equilibrium thermodynamics the inverse-
temperature four-vector is a primary field, and its antisymmetric derivative is paired with spin
potential/spin current in the entropy-current construction.  Hypersurface independence requires
the appropriate divergence and side-boundary return, not a scalar entropy reading alone.  Source:
[Becattini, *Covariant statistical mechanics and the stress-energy tensor*](https://arxiv.org/abs/1201.5278).

[proved-derived; formal-checked] `SkewDissipativeTurnLaw` makes the action/turn split exact over a
declared gradient carrier.  An alternating bilinear turn annihilates its self-pairing, while a
nonnegative dissipation face remains.  With every correction and boundary source set to zero, the
returned potential rate is nonpositive.  The source term is retained so that open, driven, or
non-stationary systems are not silently presented as closed gradients.

## Exact lineage precedes every entropy quotient

[proved-standard; external-source] Wang's finite path model maximizes Shannon path information under
normalization and a mean-action constraint, returning weights proportional to `exp(-eta*A_k)`.
Least action is the most heavily weighted path only for the corresponding positive multiplier; an
equal-action population remains unresolved by that receiver.  The subsequent diffusion, Ohm, and
Fourier passages use further Brownian, harmonic, common-diffusivity, and material assumptions.
Source: [Wang, *Maximum entropy change and least action principle for nonequilibrium systems*](https://arxiv.org/abs/cond-mat/0312329).

[proved-standard] The exact information identity used by a lineage-retaining transition population
is the chain rule

```text
H(source, target) = H(source) + H(target | source).
```

It is not generally the marginal identity

```text
H(target) - H(source) = H(target | source).
```

because distinct source occurrences may merge into one target reading.  The joint occurrence
population retains which source caused which transition; the target marginal does not.

[proved-derived; formal-checked] The new theorem
`no_successor_factor_of_equal_entropy` returns the exact receiver-insufficiency obstruction.  If two
histories have the same entropy coordinate but an admitted successor receiver separates them, no
successor law factors through the entropy coordinate.  This is the deterministic statement needed
by the engine: microscopic addressed paths and their reconstruction fibres are primary; entropy,
probability, and path weights are later receiver coordinates when a source-specific map supplies
them.

[proved-standard; external-source] Unitary quantum evolution can make coordinate-space entropy sums
oscillate or decrease.  A proposed universal monotone quantum entropy law therefore requires an
additional collapse, creation, aperture, coarse-graining, or other constitutive mechanism.  Source:
[Geiger and Kedem, *On Quantum Entropy*](https://pmc.ncbi.nlm.nih.gov/articles/PMC9601376/).

## Positive production is an interaction theorem

[proved-derived; formal-checked] For an ordered scalar carrier and monotone response `lambda`, the
file proves

```text
(target - source) * (lambda(target) - lambda(source)) >= 0.
```

It then sums this grain over an exact finite occurrence population with nonnegative addressed
conductances.  Sign is not attached to a bare state: it is the common orientation of two returned
differences across one interaction.

[proved-standard; external-source] This is the algebraic core of the generalized relativistic
H-theorem: positive transition kernels and a monotone constitutive logarithm make the paired
before/after difference nonnegative.  The particular `kappa` logarithm and equilibrium law remain
source-specific.  Source: [Kaniadakis, *Relativistic Roots of κ-Entropy*](https://pmc.ncbi.nlm.nih.gov/articles/PMC11119737/).

[proved-standard; external-source] In relativistic dissipative hydrodynamics, entropy production
separates bulk expansion, shear, and diffusion currents; positive transport matrices return
nonnegative quadratic production.  Frame choices such as Landau and Eckart are receiver charts,
and first-order invariance does not remove higher-order causal/relaxation obligations.  Source:
[Harutyunyan and Sedrakian, *Relativistic dissipative hydrodynamics from kinetic theory with a multicomponent mixture*](https://arxiv.org/abs/2302.09596).

## Difference, constitutive kernel, and the torus two-current

[proved-derived; formal-checked] Weak monotonicity alone permits a constitutive kernel.  The checked
strict law now removes it exactly:

```text
(target - source) * (lambda(target) - lambda(source)) = 0
  iff target = source,

0 < (target - source) * (lambda(target) - lambda(source))
  iff target != source,
```

when `lambda` is strictly monotone.  Thus the “nullity of the null” has a precise local
realization: a nonzero returned coordinate difference is equivalent to strictly positive
interaction production after the declared constitutive radical has been removed.  Without strict
monotonicity, zero production retains the complete kernel fibre and cannot be promoted to source
identity.

[proved-derived; formal-checked] A four-coordinate entropy/action current is now placed on the four
addressed winding directions of the finite torus carrier.  Two presented currents `J` and `K`
return the alternating receiver two-current

```text
Omega(J,K;i,j) = J_i K_j - J_j K_i.
```

Exchanging `i,j` or exchanging `J,K` reverses orientation; self-pairing and scalar-aligned pairing
vanish.  Away from the zero-cross fibre, swapping the currents is therefore proved to return a
different oriented reading.  On integral winding populations this construction is definitionally
the already-owned six-plane `cycleWedge` in `HolonicFourForceSectorCarrier.lean`; entropy/action
uses the common interaction owner rather than founding another plane calculus.  A nonzero reading
therefore certifies an oriented receiver-visible difference.  Zero does
not identify the currents: the file exhibits two distinct aligned rational currents in the same
zero-cross fibre.  Simultaneously transporting both four-coordinate currents through any integral
chart endomorphism commutes exactly with transporting the six returned plane coordinates through
its exterior-square action.  This is the exact finite content of multiple time/entropy axes, basis
covariance, and noncommuting receiver orientation.  The product is an exterior two-current on a
declared plane, not a silent simplification of two causally distinct time lines into one scalar
`t^2`.

[proved-derived; formal-checked] The zero and nonzero cross-current fibres are now separated more
sharply.  A nonzero plane reading rules out scalar alignment on that observed plane.  Over a field,
if the reference four-current is nonzero, vanishing of all six plane readings is equivalent to the
existence of one scalar carrying the complete second current along the first.  The proof retains a
chosen nonzero pivot coordinate and reconstructs the scalar from it; it does not identify the two
currents.  When both currents evolve, their returned two-current satisfies the exact discrete
Leibniz law

```text
Omega(J1,K1)-Omega(J0,K0)
  = Omega(J1-J0,K0) + Omega(J1,K1-K0).
```

Change can therefore enter through either current, orientation exchange is signed, and aligned
transport has null exterior face while retaining its complete one-dimensional reconstruction
fibre.

[project-postulate] For a Complex Parametron/toroidal holon, the four coordinates are realized by
the retained winding populations, while induction and constitutive response transport their
current.  The alternating two-current is the candidate face flux between winding directions.  A
source-specific physical theorem must still identify the complex coefficient current, material
Hodge map, chronology and boundary return; binary locking is a later quotient of this carrier.

## Free energy and least action

[proved-derived; formal-checked] Physical free energy is typed by a `ThermalConstitution` carrying an
additive map from an entropy quantity line to an energy quantity line:

```text
F(E,S) = E - Theta(S).
```

The returned difference preserves the energy and entropy transports separately,

```text
Delta F = Delta E - Theta(Delta S),
```

and a closed grain with nonnegative dissipation cannot increase `F`.  Temperature is the special
coordinate realization `Theta(S)=T*S`; it is not multiplied into entropy until the chart and units
make that map well typed.

[proved-standard; external-source] In relativistic diffusion with a heat bath, relative entropy has
an exact nonpositive quadratic derivative under the admitted diffusion law, while the subsystem's
entropy need not rise monotonically because energy and boundary exchange remain separate.  The
thermodynamic identity `T*S = W - F` appears only with those source variables and bath assumptions.
Source: [Haba, *Energy and entropy of relativistic diffusing particles*](https://arxiv.org/abs/1003.1205).

[proved-standard; external-source] The reviewed Free Energy Principle begins with a particular
Langevin carrier and an Onsager--Machlup path action.  Its non-equilibrium steady-state flow splits
into a skew part, a dissipative part, and an explicit correction.  Its variational free energy
equals surprisal only when the approximate posterior is exact; otherwise the nonnegative KL defect
remains.  Expected free energy and path action coincide only under the paper's stated precise-
particle passage.  Source: [Friston et al., *The free energy principle made simpler but not too simple*](https://arxiv.org/abs/2201.06387).

[project-postulate] The holonic Free Energy Principle passage is consequently not “every system
minimizes one scalar.”  It is the following typed construction obligation:

```text
addressed path family and exact action
  -> conservative turn + dissipative constitutive crossing + open source
  -> entropy/current world-tube
  -> typed energy-minus-entropy potential
  -> receiver-specific selection with the complete equal-action fibre retained
  -> returned morphology changing later successor conduct.
```

For Eros, the terminal clause requires the selected path to change the continuing ecology, survive
source-detached remount, and alter later navigation under an admitted receiver.  A path score or
shortest final word alone does not establish that return.

## Complex Parametron and field transport

[project-postulate] The Complex Parametron supplies a bounded physical realization target for the
same carrier.  Its toroidal incidence body stores complex phase current; mutual induction supplies
the successor source; capacitance/inductance and loss instantiate the symmetric/positive
constitutive forms; the antisymmetric face current carries circulation; and a locked binary phase
is a later receiver quotient.  A continuum or calibrated apparatus theorem must still construct
these maps from its conductor, ferrite, gap, and boundary sections.

[project-postulate] The four physical force sectors consume the current law through distinct
internal fibres.  Electromagnetism uses the checked Faraday source instance and still owes the
calibrated material Hodge and Poynting passage.  The weak and strong sectors require their chiral
`SU(2)_L x U(1)_Y` and `SU(3)` representations, ordered curvature/holonomy, matter currents, positive
actions, and continuum returns.  Gravity uses frame/Spin curvature, stress--energy current,
Bianchi/Noether return, and a typed horizon/thermal boundary.  The shared six turn planes are the
base carrier; equal plane counts do not name force species.

[project-postulate] Heat and gravity meet through a field/current theorem, not through a deletion of
either field.  Microscopic action and interaction currents contribute to stress--energy; a metric
and connection transport that source; a thermal receiver returns temperature, entropy storage,
entropy flux, and production.  The cosmological constant remains the typed inverse-area curvature
coefficient in the Einstein receiver.  A bridge to vacuum free energy requires the declared
gravitational coupling and preserves the inference/reconstruction fibre already exposed by
`HolonicCosmologicalInference.lean`.

## Millennium consumption

[project-postulate] The checked successor/current/production owner is a common instrument edge with
six different source obligations:

| Worktrack | Source realization of the common current | Decisive next theorem |
|---|---|---|
| RH | contour/test-function successor current; explicit-formula boundary flux; Weil production form | construct the full prime/archimedean current and prove its positive constitutive form uniformly on the admitted test family |
| BSD | localization/descent/height successor current; analytic/algebraic difference; leading-term flux | prove the source-specific Hecke/Waldspurger constitutive identity, then promote it uniformly through every prime successor |
| Hodge | cover/subdivision successor; overlap boundary current; algebraic-cycle reconstruction defect | normalize the cover-small tetrahedral carrier and prove realization preserves its fundamental class before the product/duality passage |
| Navier--Stokes | energy/enstrophy storage; advective/viscous/boundary current; vortex-stretching production | derive the terminally integrable oriented production law from the PDE and transport it through restart, rather than repeating compact-interior partitions |
| Yang--Mills | gauge-orbit successor; curvature/action current; physical-quotient dissipation/spectral production | construct a positive gauge-covariant action on the exact quotient and prove a scale-uniform positive first excitation under continuum reconstruction |
| P versus NP | computation successor; resource current; reconstruction-fibre production/branching | prove either a polynomial successor factorization or an explicit separating history that survives every admitted polynomial quotient |

[proved-derived; formal-checked] This deed returns three roadmap-grade artifacts simultaneously: a
proved constitutive law, an exact local-to-global reconstruction theorem, and a receiver-
insufficiency counterexample.  It does not inhabit any official Millennium statement.

[open] The shortest shared residual is now a **source-realization square**, not another abstract
telescoping theorem:

```text
source occurrence --actual successor--> source occurrence
       |                                  |
       v                                  v
storage/current/production carrier --law--> returned difference
       |                                  |
       v                                  v
official receiver ---------------------> official consequence.
```

For Hodge the nearest already-constructed source is the tetrahedral open-star cover.  For
Navier--Stokes it is the signed enstrophy/Hodge direction current.  For electromagnetism it is the
finite Faraday history.  The latter now inhabits the top square; the former two still owe the named
source constitutive and global reconstruction arrows.

## Axiom and source audit

[proved-derived; formal-checked] Focused Lean verification succeeds for
`HolonicEntropyActionInduction.lean`.  Its audit reports only Mathlib's ordinary quotient/extensional
infrastructure (`propext`, `Classical.choice`, and `Quot.sound`) and no `sorryAx`.  Every probabilistic
or continuum claim above remains in its external-source or project-postulate grade and is not used
to close the checked finite theorems.

[definition] This research record changes no Rust/CUDA construction phase and does not move
`CONSTRUCTION_STATE.md`.  It is a theorem-line deposit consumed by the Millennium roadmap and by a
later engine source-realization passage only when the engine's live construction authority names
that edge.
