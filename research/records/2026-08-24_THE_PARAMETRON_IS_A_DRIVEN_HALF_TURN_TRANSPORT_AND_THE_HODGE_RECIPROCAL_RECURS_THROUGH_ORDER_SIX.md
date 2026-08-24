# The parametron is a driven half-turn transport and the Hodge reciprocal recurs through order six

**Date:** 2026-08-24  
**Scope:** exterior physical synthesis and Lean theorem return; this record schedules no engine
deed and does not move `CONSTRUCTION_STATE.md`.  
**Truth status:** each claim is graded locally under `canon/EPISTEMIC_GRADES.md`.

## 1. The device in the supplied diagram

[proved-standard] The classical parametron is a resonant circuit with a nonlinear reactive element.
Driving the reactive parameter near twice the resonant frequency produces a subharmonic response at
the resonant frequency with two stationary phases separated by `π`.  Eiichi Goto used those two
phases as the binary face.  Primary sources and bounded historical descriptions:

- E. Goto, *The Parametron, a Digital Computing Element Which Utilizes Parametric Oscillation*,
  Proceedings of the IRE 47 (1959), 1304--1316,
  <https://ieeemilestones.ethw.org/w/images/3/33/Goto_IRE4708.pdf>;
- Information Processing Society of Japan, *Parametron*,
  <https://museum.ipsj.or.jp/computer/dawn/0007.html>;
- IPSJ, *Parametron archives*,
  <https://museum.ipsj.or.jp/en/heritage/Parametron_arcives.html>.

[proved-standard] In the ferrite circuit shown by the user, DC bias places the ferrite cores on a
nonlinear part of their `B-H` curves.  The `2f` excitation then varies the effective inductance.  The
two secondary windings are oppositely connected so direct `2f` pickup cancels while they and the
capacitor form the tuned `f` circuit.  This is described in the contemporary Mitsubishi technical
account at <https://www.giho.mitsubishielectric.co.jp/giho/pdf/1956/5609.pdf>.

[proved-standard] Networks of classical parametrons were operated in three excitation groups and
implemented majority logic.  Thus pump chronology, transformer incidence, phase transport, stable
storage, and receiver readout were already parts of the physical computation rather than an
external instruction/data distinction.  The bounded historical source is the IPSJ Parametron
archives page above.

## 2. The holonic apparatus card

[interpretation] The source object is not a bit.  It is a driven dissipative trajectory with at
least carrier amplitude `r`, phase `θ`, pump phase `ψ`, nonlinear storage, coupling incidence,
chronology, and loss.  A standard averaged phase face contains the double-angle potential

```text
V_pump(θ) = -κ cos(2θ-ψ).
```

The maps are:

```text
driven trajectory
  -> locked phase sheet θ or θ+π
  -> complex carrier exp(iθ)
  -> binary receiver σ in {+1,-1}.
```

The preserved diagram is the pump's half-turn invariance together with sign reversal of the
carrier.  The limit is the phase-locked two-sheet population.  The first theorem is the exact Ising
descent of cosine coupling there.  The falsifier is any locked coupling whose energy cannot factor
through the sign receiver, or any purported binary conclusion which varies inside the retained
amplitude/phase/chronology fibre.

[proved-derived; formal-checked] `HolonicParametron.lean` returns the first theorem:

```text
V_pump(θ+π) = V_pump(θ),
exp(i(θ+π)) = -exp(iθ),
cos(θ_i-θ_j) = σ_i σ_j  for θ_i,θ_j in {0,π}.
```

Consequently every finite addressed population of locked cosine couplings descends exactly to the
corresponding Ising energy.  The same file proves the full-turn fibre
`exp(i(θ+2π))=exp(iθ)`, so the binary carrier face does not erase the fact that distinct source
phases were identified.

[interpretation] This is a literal instance of the I9 storage--flux closure:

```text
phase θ             -> local effort / phase difference
nonlinear L,C         -> stored oscillator energy
transformer coupling -> transported phase current
loss + pump schedule -> returned basin selection
readout              -> receiver sign with a reconstruction fibre.
```

The pump is simultaneously energy supply and chronology.  Nonlinearity creates the two-sheet
aperture; coupling biases which sheet is continued; dissipation deposits the returned branch.  The
swing is the exact half-turn action, not a metaphor added after readout.

## 3. Ising machines and QFP/AQFP

[proved-standard] A network of parametrically driven oscillators can encode an Ising pairing by
representing spins with the two phase states and interactions with oscillator couplings.  A current
Josephson-parametric-oscillator construction is S. Razmkhah et al., *A Josephson Parametric
Oscillator-Based Ising Machine*, Phys. Rev. B 109, 014511 (2024),
<https://journals.aps.org/prb/abstract/10.1103/PhysRevB.109.014511>.

[interpretation] The mathematical bridge is stronger when it retains the torus before the Ising
receiver.  An `N`-oscillator phase population lives on `(S¹)^N`; pump locking imposes a `Z/2` sheet
receiver; coupling transports relative phases; winding and phase slips remain in the reconstruction
fibre.  The Ising Hamiltonian is therefore a quotient of a coupled phase-torus transport, not the
source topology.

[proved-standard] AQFP is an energy-efficient superconducting logic family based on the quantum
flux parametron and adiabatic switching.  Its operating principle and potential-shape account are
reviewed by N. Takeuchi et al., *Adiabatic Quantum-Flux-Parametron: A Tutorial Review* (2022),
<https://www.jstage.jst.go.jp/article/transele/E105.C/6/E105.C_2021SEP0003/_article/-char/en>.

[open] The exact AQFP bridge has not yet returned.  It requires the Josephson current--phase law,
flux quantization, loop inductance, excitation chronology, time-dependent potential, circulating
current receiver, and dissipative/adiabatic hypotheses.  `HolonicParametron.lean` proves the
classical/JPO locked-phase quotient; it does not silently substitute that phase model for the AQFP
flux-state dynamics.

## 4. Consequence for the higher-difference transport frontier

[interpretation] The useful import is the phase-torus transport before binary collapse.  Linearizing
coupled phase current near a locked section produces a weighted graph-Laplacian response; damping
conducts phase differences diffusively; the remaining winding population is the harmonic part.
This is one finite storage--gradient--divergence instance of a higher-difference transport owner
whose other receivers include fluid Hodge transport, covariant curvature, monodromy, local/global
arithmetic transport, and successor-sensitive computation.

[proved-derived; formal-checked] `NavierStokesReciprocalDifferenceRecurrence.lean` now proves the
exact shifted binomial product law on every addressed path window through order six.  When a local
denominator/reciprocal product is one, the highest reciprocal difference recurs through the
positive-order denominator differences.  If the denominator has zero third difference, the exact
sixth-order recurrence is

```text
q(0) Δ⁶r(0)
  = -(6 Δq(0) Δ⁵r(1) + 15 Δ²q(0) Δ⁴r(2)).
```

The theorem is instantiated on the genuine `|k|²` denominator and totalized Hodge reciprocal
along any seven-point coordinate window which avoids `k=0`.  No global inverse at the totalized
zero mode is assumed.

[proved-derived; formal-checked] The same owner proves the exact sparsity facts needed by the
three-axis word: distinct-coordinate denominator differences vanish, every same-coordinate second
difference is `2`, every same-coordinate third difference vanishes, and the candidate denominator
face type has cardinality seven--one value face, three first-difference faces, and three
second-difference faces.

[open] The exact next deed is now HD0, not a Navier--Stokes-named lemma: extract the generic bounded
recurrence into `Foundation/HigherDifferenceTransport.lean`, construct its ordered multi-generator
product/reciprocal face tree, prove the commuting interchange quotient and a noncommuting
falsifier, and retain rebase and receiver fibres.  The sparse `Δ₀²Δ₁²Δ₂²` quadratic identity is
then the first analytic specialization.  It feeds the twenty-seven numerator/reciprocal Leibniz
faces, inverse-cube mass, eight subset receivers, and near/far Haar partition required by the
uniform fluid physical-kernel witness.

## 5. Grade and construction boundary

[established-bounded; formal-checked] The two new Lean owners compile in the ElementaryHolonics
toolchain and their printed promoted theorems contain no `sorryAx`.  They establish the driven
half-turn/Ising quotient and the one-path order-six Hodge reciprocal recurrence in their declared
scopes.

[open] No uniform Navier--Stokes physical-kernel witness, critical-vorticity integrability theorem,
or Millennium solution is claimed by this station.  The next proof obligation is the universal
HD0 owner and its ordered word theorem; the sparse three-axis recurrence is its first fluid
receiver.
