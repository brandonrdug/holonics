# The finite Leibniz swing separates null charge from conserved action and a dark relic requires a surviving carrier

Date: 2026-08-25

## 1. The exact inferred-coordinate difference is a common primitive

[proved-standard] For two coordinates whose receiver is their product, the complete finite
difference has two exact ordered decompositions:

```text
x1*y1 - x0*y0
  = (x1-x0)*y0 + x1*(y1-y0)       -- change x, then y
  = x0*(y1-y0) + (x1-x0)*y1.      -- change y, then x
```

The intermediate pivot differs, but the exterior return does not.  The difference between a
source-pivot linearization and the exact return is the mixed face:

```text
x1*y1 - x0*y0
  = (x1-x0)*y0 + x0*(y1-y0) + (x1-x0)*(y1-y0).
```

[proved-derived; formal-checked] `HolonicDifferenceCalculus.lean` now proves these three identities
over every commutative ring.  It also proves

```text
target^2 - source^2 = (target-source)*(target+source).
```

All four theorems compile without `sorryAx`.  This promotes the earlier cosmological-constant
calculation into the common difference owner.

[interpretation] This is the elementary two-pivot swing.  One coordinate is held as the pivot while
the other moves; then the pivot changes and the second movement occurs.  The mixed product is the
interior interaction face swept between the two orders.  A differential product rule deletes that
second-order face in an infinitesimal receiver; the finite identity retains it exactly.

[proved-derived; formal-checked] The cosmological specialization is obtained from
`Lambda = (3/c^2) Omega H^2`:

```text
Lambda2 - Lambda1
  = (3/c^2) [Omega2*(H2^2-H1^2) + (Omega2-Omega1)*H1^2]
  = (3/c^2) [Omega1*(H2^2-H1^2) + (Omega2-Omega1)*H2^2].
```

The terms are not independent error bars.  They are two exact paths through the same joint
parameter face.  This is why a printed marginal `Omega`, a printed marginal `H`, and a covariance
summary cannot reconstruct the complete inferred `Lambda` population.

## 2. Nuclear reactions test which nullity is actually null

[proved-standard] A closed relativistic reaction conserves total four-momentum:

```text
sum incoming p^mu = sum outgoing p^mu.
```

For a reaction written in rest-mass coordinates, its released energy is

```text
Q = (sum incoming rest masses - sum outgoing rest masses) c^2,
```

and the outgoing ledger must include kinetic energy, radiation, recoil and every weakly observed
carrier.  A neutron-capture experiment compared atomic mass differences with the emitted gamma
energy plus nuclear recoil and directly confirmed this closure to four parts in ten million:
[NIST/ILL/MIT account](https://www.nist.gov/news-events/news/2005/12/einstein-was-right-again-experiments-confirm-e-mc2).

[proved-standard] Fusion and fission therefore change the invariant mass of the bound subsystem,
not the total energy of a closed world-tube.  If reaction products and heat remain inside a closed
box, their energy remains in the box's total mass.  If radiation or particles cross the boundary,
the box loses exactly the corresponding energy face divided by `c^2`.  The DOE's fusion account
states the same binding-energy passage for light nuclei:
[DOE fusion reaction account](https://www.energy.gov/science/doe-explainsfusion-reactions).

[proved-standard] Matter and antimatter carry conjugate charges, but conjugate charge does not mean
negative energy.  Schematically,

```text
(charge, energy) + (-charge, energy) = (0, 2*energy).
```

Annihilation can return a null electric-charge face while the complete four-momentum is transported
to photons or other products.  The ALPHA-g experiment found antihydrogen motion consistent with
downward gravitational attraction and ruled out repulsive gravity of magnitude `1 g`; it did not
find an energy sign reversal:
[ALPHA-g primary paper](https://www.nature.com/articles/s41586-023-06527-1).

[proved-derived; formal-checked] `HolonicFieldTheoryPassage.lean` now proves the charge/energy
separation above, proves nonzero energy after charge cancellation when the admitted particle-energy
face is nonzero, and supplies an exact reaction ledger.  In a closed ledger the defect of the
visible receiver is exactly the omitted weak-carrier face.

[established-bounded] Beta decay is the canonical receiver-insufficiency experiment.  The visible
nucleus-plus-electron receiver did not close energy, momentum and angular momentum; the neutrino
was introduced as the missing outgoing carrier and was later detected.  The lesson is not that a
conservation law failed.  It is that the admitted receiver family was insufficient.  Fermilab's
historical summary records the missing-energy origin:
[Fermilab neutrino history](https://www.slac.stanford.edu/pubs/slacreports/reports18/slac-r-1034.pdf).

## 3. Why ordinary nuclear reactions are not the dark-matter remainder

[proved-standard] In general relativity there is no separate geometric species called
"dark curvature."  Curvature responds to the total admitted stress--energy.  Nuclear binding,
thermal motion, photons, neutrinos, magnetic fields, and ordinary matter all gravitate through
their corresponding stress--energy faces.

[established-bounded; measured] The dark-matter inference is plural: galactic dynamics, cluster
dynamics, gravitational lensing, CMB anisotropies, and structure growth require a long-lived,
predominantly nonrelativistic source population beyond the observed baryonic inventory under the
admitted gravitational model.  The current Particle Data Group review summarizes these independent
receivers and the difficulty of fitting all of them with baryons or a scale-local modification:
[PDG dark-matter review](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-matter.pdf).

[proved-standard] Ordinary fusion, fission and decay redistribute a known baryonic system's
stress--energy among bound rest energy, motion and radiation.  They do not by themselves produce a
new stable, cold, collisionless population.  Radiation also dilutes differently from nonrelativistic
matter in an expanding cosmology and does not cluster in the required way.  Thus reaction heat or
annihilation photons are not a substitute for the dark-matter carrier.

[conditional] A nuclear or particle reaction could participate in dark-matter production only if
it has an admitted channel into a sufficiently stable dark state.  Then the dark state, not the
vanishing visible charge or the released heat alone, is the retained carrier.  Direct-detection
experiments test the reverse passage by looking for nuclear recoils caused by an incoming dark
particle; current xenon experiments constrain such interactions rather than having established a
dark-matter detection:
[PandaX-4T nuclear-recoil search](https://www.nature.com/articles/s41586-023-05982-0).

## 4. High-energy phase transitions can produce dark relics, but only through a constitutive passage

[proved-standard] The reduced number-density Boltzmann passage for a pair-annihilating species is

```text
dn/dt + 3 H n
  = - <sigma v> (n^2 - n_eq^2) + S.
```

Its faces are respectively local population change, expansion/dilution, pair
annihilation/creation, and admitted production.  The full object is a phase-space distribution and
collision operator; the number density is already a receiver compression.  The standard reduction
and its assumptions are reviewed by the
[PDG](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-matter.pdf), while the exact relativistic
thermal-average construction is due to
[Gondolo and Gelmini](https://doi.org/10.1016/0550-3213(91)90438-4).

[proved-derived; formal-checked] The collision difference is now tied to the common finite Leibniz
owner:

```text
n^2 - n_eq^2 = (n-n_eq)*(n+n_eq).
```

The first factor is the polarized departure from equilibrium.  The second is the admitted
interaction population.  `HolonicFieldTheoryPassage.lean` retains population difference,
expansion dilution, collision removal and production as four separate faces and proves exact
reconstruction of any one from a balanced chronology cell.

[proved-standard] Freeze-out occurs when number-changing interactions no longer keep pace with
expansion, leaving a surviving comoving remainder.  Freeze-in instead accumulates a species whose
coupling is too weak for it ever to equilibrate:
[original freeze-in construction](https://arxiv.org/abs/0911.1120).

[conditional; model-specific] Asymmetric dark matter is the closest established model family to
the proposed "cancellation leaves a difference" mechanism.  Pair annihilation removes the
particle--antiparticle symmetric population, while a protected imbalance
`n_dark - n_antidark` survives.  A cosmological transition may generate or relate that asymmetry to
the visible baryon asymmetry.  The relic is the nonzero oriented population difference, not energy
destroyed by the cancelled pairs; the annihilation products still carry the symmetric component's
four-momentum.  The [PDG review](https://pdg.lbl.gov/2025/reviews/rpp2025-rev-dark-matter.pdf)
surveys this distinction.

[conditional; model-specific] A first-order cosmological phase transition can alter masses,
interaction rates, entropy, and transport across bubble walls.  In one explicit mechanism, dark
particles gain mass at the wall; most reflect and annihilate, while the transmitted population
survives as the relic:
[filtered dark matter](https://arxiv.org/abs/1912.02830).  In another, reflected particles collect
in shrinking false-vacuum regions and can collapse into primordial black holes after a Boltzmann
transport calculation:
[phase-transition primordial black holes](https://arxiv.org/abs/2105.07481).

[interpretation] These models realize the proposed holonic compression more sharply than the vague
phrase "high energy creates dark matter."  The bubble wall is an addressed chart transition.  Its
mass jump and incidence decide which phase-space paths transmit, reflect, annihilate, or become
trapped.  The quotient is productive only because a typed remainder survives the transition and
later cosmological transport.  Energy scale alone supplies no such theorem.

## 5. Softmax, sigmoid and the population receiver

[proved-standard] For a thermal ensemble, normalized occupation weights have the form

```text
p_i = exp(-beta E_i) / sum_j exp(-beta E_j).
```

This is a softmax receiver on the energy/action differences.  A common shift of every `E_i` lies in
its kernel.  For two states the occupation ratio reduces to a logistic/Fermi-type chart,

```text
p_1 = 1 / (1 + exp(beta*(E_1-E_0)))
```

under the corresponding two-state assumptions.

[interpretation] The exponential receiver converts a difference landscape into a normalized
population, but it does not replace the nuclear or particle interaction law.  Cross sections,
matrix elements, selection rules, tunnelling, decay widths, expansion and boundary conditions
still determine the path weights.  The complete holonic object is therefore

```text
phase-space occurrences
  -> local interaction / transition amplitudes
  -> collision and boundary transport
  -> population history
  -> normalized occupation receiver
  -> retained reconstruction fibre of micro-paths.
```

Freeze-out is a particularly clean locking event: the equilibrium receiver ceases to reconstruct
the evolving population because interaction and expansion no longer commute at the required rate.
The surviving defect is the relic.

## 6. The immediate research consequence

[interpretation] The strongest next physical comparison is not "does a reaction lose mass?" but:

```text
Which typed current leaves the visible receiver,
through which interaction face,
with what four-momentum and lifetime,
and does its transported population reproduce
lensing + dynamics + CMB + structure growth in one common gravitational chart?
```

[open] No existing holonic theorem constructs a Standard Model or dark-sector collision operator,
derives a viable relic abundance, or proves that any named phase transition supplies the observed
dark matter.  The completed exact algebra now isolates what such a theorem must return: the
finite-Leibniz interaction remainder, closed reaction/current balance, a nonempty surviving carrier,
lawful chronology, and a common multi-receiver gravitational reconstruction.
