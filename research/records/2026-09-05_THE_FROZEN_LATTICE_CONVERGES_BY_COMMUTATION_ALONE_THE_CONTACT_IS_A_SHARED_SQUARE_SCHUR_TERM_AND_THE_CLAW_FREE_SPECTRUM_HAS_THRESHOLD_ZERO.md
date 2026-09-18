# The frozen lattice converges by commutation alone, the contact is a shared-square Schur term, and the claw-free spectrum has threshold zero

**Date:** 2026-09-05
**Kind:** analysis and review note for the RH line, occasioned by the Flux Lattice canvas. It
schedules nothing. [The roadmap](../../docs/plans/THE_ROADMAP.md) and
[the position](../../CONSTRUCTION_STATE.md) remain the only construction authorities; the
[MFR strategy](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md)
remains the standing mathematical goal.
**Truth status:** per claim below. `established-bounded; computational-witness` for every
number, from
[`research/experiments/flux_lattice_spectrum/`](../experiments/flux_lattice_spectrum/)
(`lattice_spectrum.js`, `receipt.json`, the same engine as the canvas); `proved-standard` for the
named classical theorems; `interpretation` for every bridge to ζ, each with a falsifier;
`open` for what §8 names. No theorem about ζ is claimed.
**Evidence surface:** the canvas
[Flux Lattice](https://claude.ai/code/artifact/ce5e5059-7f1b-4ef6-a907-e68cf6ac6639)
(artboards Flux Lattice, Generators, Winding, Spectrum).
**Provenance.** Brandon, 2026-09-05, in order: chess as an abstract model of combinatorial
potentials and flux intersections, moves as parametric oriented linear transformations,
compound moves non-commutative, *"the intersections will show commonalities and similar
outcomes; despite there being a near infinite number of possibilities and combinations, there
are inevitable outcomes because of natural flux"*; then *"the possibilities converge, this is
exactly like primes and the Riemann Zeta zeros, no?"*; then the pattern reading of the residual
(1, 4, 16, 24 as powers of two); then *"how can cross terms ever stop crossing?"*; then the
correction that the lattice carries no captures, so *"the ecology is frozen for the entirety of
the flux lattice"*, the Hamiltonian/electron-gun reading of captures, the random-opponent
argument (*"independent contemporarily, determined retroactively"*), and *"couple that to
holonic entropy and heat diffusion... you would call that gradient temperature... we're
talking about Markov chains."*

---

## 0. The object, exactly

[definition] The lattice is pseudo-legal chess without castling, en passant or check. From the
initial board each side has a **menu**: its top-`k` moves at the root by a fixed development
score, plus two moves that become legal only after one of those (*enabled* moves; every root
move that opens one is recorded as an enabler). A generator is a `(from, to)` pair, used at most
once. Sides alternate. Boards reached by different sequences merge into one node when they are
the same position; the node retains `paths`, the number of sequences reaching it. **No menu ever
contains a capture.** Every count below is finite and at this aperture.

[definition] For one side, the commutation graph has the menu moves as vertices and an edge where
both orders are legal and reach the same board, evaluated after the enablers the pair needs. The
other relations are *gated* (one order only), *exclusive* (neither) and *divergent* (both orders,
different boards; none occurred). The **dependence graph** is the complement of the commutation
graph. The **clique polynomial** is `P(z) = Σ_C (−1)^|C| z^|C|` over cliques of the commutation
graph, including the empty one.

---

## 1. Two convergences, and the lattice isolates one

[proved-derived; formal-checked] A word of transports is order-blind exactly when the transports
commute, `orderBlind_iff_commute` in
[the chain-series record](2026-08-20_A_TRANSPORT_IS_A_WORD_AND_THE_CHAIN_SERIES_IS_WHAT_NON_COMMUTATION_FORCES.md).
Equivalently, a chronology exists exactly where transports fail to commute. The lattice's merge
is the quotient by the commuting part of each side's menu, and the retained `paths` is the fibre
that quotient forgets. This is the pattern the
[Hodge-words record](2026-08-24_THE_ANISOTROPIC_HODGE_WORDS_RETURNED_COMPLETE_OCCURRENCES_BEFORE_COMMUTING_CONDENSATION.md)
already states as reusable: retain the complete ordered occurrence population, quotient only
through a declared commuting receiver, carry the fibre multiplicity.

[established-bounded; computational-witness] White 4 / black 3, plies 0 through 8:

| ply | sequences | boards | unique-path boards | mean log₂ paths |
|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 0 |
| 1 | 4 | 4 | 4 | 0 |
| 2 | 16 | 16 | 16 | 0 |
| 3 | 55 | 31 | 7 | 0.77 |
| 4 | 175 | 52 | 1 | 1.67 |
| 5 | 482 | 61 | 0 | 2.83 |
| 6 | 1090 | 53 | 0 | 4.14 |
| 7 | 2006 | 34 | 0 | 5.64 |
| 8 | 2704 | 16 | 0 | 7.08 |

The piece population is 32 throughout. Sequences grow, boards rise and then fall, and the fibre
entropy `log₂ paths` grows about linearly. So the convergence here is **order-forgetting**: path
information is destroyed while the state space is conserved. The system is conservative in the
sense that no generator disappears; it is only ever gated.

[definition] The second convergence is **state-space collapse**: a capture removes a piece and
with it a generator set, the reachable boards shrink, and the reduction is physical rather than
observational. It is absent from the lattice by construction. Brandon's reading of Deep Blue's
19.c4 (a position where the remaining continuations had already collapsed into one class) is a
within-band reading of a descent that captures drive.

[proved-standard] Chess itself marks the boundary between the two. The fifty-move rule (FIDE Laws
of Chess, art. 9.3) resets only on a pawn move or a capture, because those are the only moves
that cannot be undone. Every piece move is reversible. Hence the game's irreversible generators
are exactly pawn advances and captures.

[interpretation] Material level is a **band**, in the sense of
[the bands reading](2026-08-20_LANDMARKS_AND_MODULI.md) and the earlier canvas: within a band the
dynamics are the frozen lattice (commutation, transposition, the clique polynomial); a capture is
a crossing between bands, irreversible; the game is a descent through bands with the frozen
dynamics on each plateau. The lattice as built is one band.

---

## 2. The lumping is exact, and the Markov property is the causal constraint

[proved-standard] Sequences form a tree; boards form its quotient. The quotient is a Markov chain
on boards exactly because the legal moves of a board depend on the board and not on the path to
it: strong lumpability, `PC = C·P̄` with zero defect, in the form already deposited as (K.1) to
(K.3) of
[the Markov-kernel record](2026-08-18_THE_MARKOV_KERNEL_IS_A_SOFTMAX_CHART_THE_NORMALIZATIONS_ARE_QUOTIENT_SECTIONS_AND_THE_MANIFOLD_IS_NOT_THE_RECONSTRUCTION.md)
(Kemeny and Snell, *Finite Markov Chains*, 1960). That record calls Markovity a compression claim;
here the claim holds exactly, which is why the board is the right node.

[definition] A **prediction** in Brandon's sense is a statement about the future flux of a board.
The Markov property says exactly that this flux is a function of the board alone. What the path
still determines is not the future but the **measure**: under a uniform prior on sequences, the
induced weight of a board is `paths`, so `log paths` is the fibre entropy and boards reached by
many orders are the heavy ones. That is the `paths` readout in the canvas, and it is a receiver
measurement in the sense of AGENTS.md, not a substitute for the current.

---

## 3. The pairwise law is an Euler product, and the contact is a Schur term

[proved-standard] Cartier and Foata (1969) and Viennot's heaps: the generating function of the
free partially commutative monoid on a commutation graph `G` is `1/P(z)` with `P` the signed clique
polynomial above. Since cliques of `G` are independent sets of its complement `G_d`,
`P(z) = I_{G_d}(−z)` where `I` is the independence polynomial of the dependence graph. For the free
commutative monoid `P = (1 − z)^n`, every zero at 1; for the free monoid `P = 1 − nz`, one zero
at `1/n`.

[interpretation] The correspondence is literal at this level: generators are primes, boards are
integers (unordered factorizations), sequences are ordered factorizations, `ζ(s) = ∏ 1/(1 − p^{−s})`
is the generating function of the free commutative monoid on the primes, and the zeros of `P` are
the poles of the count series, the role the nontrivial zeros play in the explicit formula of
[the zero-wave record](2026-07-17_THE_WHEEL_RECURS_THE_ZERO_WAVE_CARRIES_THE_PRIME_CURRENT.md) §V.
The falsifier is stated in §8.

[established-bounded; computational-witness] Sides independent, the once-only pairwise count
from each side's commutation graph reproduces the engine exactly through ply 2 and then exceeds
it. The excess, the **contact**, obeys a **shared-square law** at every ply of every menu tested
(white/black 4/3, 3/3, 2/2 through ply 8; 5/4, 6/5 through ply 7):

```text
contact(p) = Σ_{∅≠T⊆shared squares} (−1)^{|T|+1} · |W_T(w)| · |B_T(b)|,
w = ⌈p/2⌉, b = ⌊p/2⌋,
```

where `W_T(w)` is the set of white traces of length `w` using every white move into the squares
of `T`, and likewise `B_T(b)`. With one shared square (d5, menus 4/3) it is a single product of
marginals, `1·1, 1·4, 4·4, 4·6, 6·6, 6·4` at plies 3 to 8, each factor a binomial `C(4, ·)`
because the four remaining generators on each side commute with the d-pawn. Brandon's reading of
`1, 4, 16` as `4⁰, 4¹, 4²` is these binomials; `24 = 4·6` is where they leave the powers, and the
predicted turnover `36, 24` at plies 7 and 8 returned exactly. The record of a modelling defect
belongs here: a gated move can have several enablers (Bc8→e6 opens after d7→d5 or d7→d6); with
only the first recorded the residual went negative at ply 4 of the 6/5 menu. That was the model,
not the lattice.

[proved-standard] Write `K(w, b) = 1` when white trace `w` and black trace `b` cannot coexist. The
contact is `Σ K`. The law says `K` is a sum of at most `2^{|shared|} − 1` separable terms: a
kernel of finite rank. This is a special case of a general identity. Marginalizing a set of states
of a Markov chain yields the *stochastic complement* (Meyer, *SIAM Review* 31, 1989), which is the
Schur complement of `I − P` onto the retained states; for a resistor network the same operation is
Kron reduction, a Schur complement of the Laplacian. The repository's
[effective-tension theorem](../papers/source/mathematics/theorems/conditioned-effective-tension.typ)
is this algebra in variational form: after the old interior relaxes, the remaining form is
`S = D − C*A⁻¹C`, `q ≥ 0 ⇔ S ≥ 0`, and shorting is associative. Against an opponent who moves
randomly, the operator's effective game is exactly such a complement: the opponent's interior is
integrated out and what remains is `S`. The cross term `C` never leaves. Brandon's objection
("how can cross terms ever stop crossing?") is correct, and the precise statement is that what
varies is the **rank** of the crossing kernel, not its presence.

[interpretation] Captures make `K` non-separable, because whether `w` and `b` can coexist then
depends on their interleaving and is not a function of the pair. The count becomes a sum over
histories, and by the chain-series record every term past the first in such a sum is a
commutator. The random-opponent argument then reads: the operator's moves are independent of the
opponent's *contemporarily* (the expectation over noise is taken) and determined by them
*retroactively* (the board is the state), which is the definition of a Markov decision process.
For a finite MDP an optimal policy is deterministic (Bellman; Puterman, *Markov Decision
Processes*), so against noise the operator has a fixed rule and only has to outpace the opponent's
entropy, not its intelligence.

---

## 4. Temperature is the opponent's policy aperture

[definition] Give the opponent the softmax policy `π_β(m | board) ∝ exp(β·score(m))`. At `β = 0` it
is uniform noise, maximum entropy; as `β → ∞` it is best response and the game is minimax. The
operator's expected outcome as a function of `β` is Brandon's gradient from chaos to order, and
`β` is a declared exterior aperture in the sense of AGENTS.md: reported, not intrinsic to the
board.

[proved-standard] This softmax is the object already typed in
[the reasoning-cycle tablet](../../docs/canon/TABLET_THE_REASONING_CYCLE.md): a ratio cocycle
`r(i,j) = exp(β(s_i − s_j))` on the additive-gauge quotient, whose Jacobian
`β(diag p − p pᵀ)` is a Laplacian with `vᵀJv = β·Var_p(v)`. The uniform random walk on the board
graph is the discrete heat equation on that graph. So the two-sided game at temperature `β` is a
drift–diffusion process: the operator supplies drift, the opponent supplies diffusion, and the
mixing rate is the spectral gap of the transition operator.

[proved-standard] The thermodynamic face is conditional exactly as
[the heat record](2026-07-17_HEAT_IS_THE_INEXACT_BOUNDARY_CURRENT_TEMPERATURE_IS_THE_INTEGRATING_FRAME.md)
states: temperature is the intensive frame that integrates contact, and
`F[p] − F[p_eq] = k_B T·D(p‖p_eq)` only after the ensemble, support and boundary are fixed. Here
the ensemble is the opponent's policy, the support is the legal-move set, and the boundary is the
board. The canon's rule that Shannon entropy is not thermodynamic entropy by itself is respected:
`log paths` and policy entropy are receiver measurements over declared ensembles.

[proved-standard] At `β = ∞` with both sides perfect the game collapses to the value of the
initial position and who moves first. Checkers is solved as a draw (Schaeffer et al., *Science*
317, 2007); chess is not solved. Brandon's statement that the difference is degrees of freedom
and motion constraints rather than anything mystical is the correct reading of that gap.

---

## 5. The spectrum: claw-free dependence gives real zeros and threshold zero

[established-bounded; computational-witness] For every menu tested the dependence graph is
claw-free, every zero of `P` is real, and the backward-heat threshold is zero:

| menu | `P(z)` | zeros |
|---|---|---|
| white 4 | `1 − 6z + 12z² − 10z³ + 3z⁴ = (1 − z)³(1 − 3z)` | 1, 1, 1, 1/3 |
| black 3 | `1 − 5z + 8z² − 5z³ + z⁴ = (1 − z)²(1 − 3z + z²)` | 1, 1, (3 ± √5)/2 |
| white 6 | `1 − 8z + 23z² − 28z³ + 12z⁴` | 1, 1/2, 1/2, 1/3 |
| black 5, white 5 | `1 − 7z + 15z² − 13z³ + 4z⁴ = (1 − z)³(1 − 4z)` | 1, 1, 1, 1/4 |

The smallest real zero fixes the growth rate of distinct traces in the free trace monoid on the
menu (`×3` per generator for white 4 against `×6` free), the others sit at 1 and between.

[proved-standard] Chudnovsky and Seymour, *J. Combin. Theory B* 97 (2007): the independence
polynomial of a claw-free graph has only real zeros. Since `P(z) = I_{G_d}(−z)`, a claw-free
dependence graph forces every zero of `P` real and positive. The factorizations above are
instances. The obstruction is a **claw**: one generator that fails to commute with three mutually
commuting ones. In these menus no pawn, knight or bishop move does that; a capture, whose
legality depends on the mover's arrival, the target's arrival and a blocker, is the natural
source of claws, and so is check.

[proved-derived; formal-checked] The repository already owns the polynomial threshold:
`DeBruijnNewmanPolynomial.lambda (p : ℝ[X]) = sInf {t | nonreal (heatR t p) = 0}` with
`lambda_nonpos` when `p` has no non-real zero and `lambda_nonneg` otherwise, over
`HeatFlowOfPolynomials`, `HeatSemigroup` and `PolyaStep`
(`formal/elementary-holonics/ElementaryHolonics/RH/`). The lattice polynomials are inhabitants:
`lambda P_menu ≤ 0` by `lambda_nonpos`, since the zeros are real. The MFR plan's example
`z² + 1 − 2t`, real-rooted from `t = 1/2`, is the same flow on a polynomial with a claw-like
obstruction. So the finite lattice sits in the **ordered phase** for every menu tested, by a
theorem whose hypothesis is combinatorial.

[proved-standard] A second route to real spectrum is dynamical. A Markov chain satisfying detailed
balance has a transition operator self-adjoint in `L²(π)`, hence real eigenvalues (Levin, Peres
and Wilmer, *Markov Chains and Mixing Times*, Lemma 12.2). Within one band, the uniform random walk
on piece moves alone is reversible, because every piece move has an inverse move. Pawn advances
and captures break detailed balance, and only they can put eigenvalues off the real axis.

[interpretation] Hilbert–Pólya, read through this lattice, is the statement that the arithmetic
chain is effectively reversible despite its arrow. The lattice makes the two obstructions
concrete and separable: a claw in the dependence graph, and an irreversible generator in the
dynamics. Both are absent from the frozen lattice, which is why every spectrum computed so far
is real.

---

## 6. Two different parameters, and the criticality reading

[proved-standard] The de Bruijn–Newman family `H_t(x) = ∫ e^{tu²} Φ(u) cos(xu) du` satisfies the
backward heat equation `∂_t H = −∂_x² H`. Newman (1976): if `H_t` has real zeros then so does
`H_{t'}` for `t' > t`; de Bruijn (1950): real zeros for `t ≥ 1/2` (standard time). Rodgers and
Tao (2018): `Λ ≥ 0`. In repository coordinates these are `Λ_DN ∈ [0, 1/8]`, `seamTimes = Ici Λ_DN`
and `RiemannHypothesis ↔ Λ_DN = 0`, all formal-checked (`DeBruijnSeal`, `DescentZeros`,
`CriticalChart`), with RT5/RT6 supplying an off-seam zero at every negative time.

[interpretation] Read as a one-parameter family, increasing `t` is cooling toward order (real
zeros), decreasing `t` is heating toward disorder (complex zeros), and `Λ` is the critical
temperature. RT6 says every negative time is disordered; DB4 says order is complete by `1/8`.
RH says the ordered phase reaches exactly the physical boundary `t = 0`, which is Newman's
remark that RH, if true, is only barely so. The Bost–Connes correspondence already deposited in
[the flow tablet](../../docs/canon/TABLET_THE_FLOW.md) §8.3, a `C*`-dynamical system with
partition function ζ and symmetry breaking at `β = 1`, is the other face of the same criticality
reading and carries its stated four-part debt.

[interpretation] The chess temperature of §4 and the de Bruijn–Newman time are **different
parameters**. One is the entropy of a policy over generators; the other is a heat time on the
Fourier side of the counting function. What they share is the shape: a one-parameter family with
an ordered and a disordered regime and a threshold. The falsifier and first derivation target are
in §8.

---

## 7. Primes as unique-path boards, and why they die in the frozen lattice

[definition] Call a board **prime** when `paths = 1`: exactly one sequence reaches it, so no
commuting pair occurs in its history. This is the lattice form of "a prime is a refusal": a
number is prime when no rectangle assembles it, a board is prime when no reordering assembles it,
matching [the primitivity reading](2026-08-09_A_PRIME_IS_A_PRIMITIVE_CLOSED_STRING_AND_EVERY_FORMULA_FOR_ONE_IS_INFORMATION_FREE.md)
that primality is irreducibility of an action.

[established-bounded; computational-witness] Prime boards are all boards through ply 2, then
7 of 31, 1 of 52, and none from ply 5 on (menus 4/3); 19 of 84, 9 of 193, none from ply 5 (menus
6/5). In the frozen lattice the prime density does not thin like `1/log n`; it vanishes, because
the generator set is finite and once-only, so every long history contains a commuting pair.

[interpretation] Arithmetic keeps producing primes because the additive structure keeps creating
new irreducibles; the zero-wave record calls this the refusal current and reads RH as its
unbiasedness at every scale (every correction mode with the same `x^{1/2}` envelope). The lattice
analogue of a persistent refusal current therefore requires **generator renewal**: captures that
remove generators and promotions that create them. A frozen ecology has no primes at depth. This
is the same point as §1 from the arithmetic side: the interesting convergence, and the
interesting refusal, both need the ecology to change.

---

## 8. What this suggests for the RH line, with falsifiers

[interpretation] **The sign question is a passivity question, and the lattice says which
algebra.** The Foster contract already reads RH as Foster's reactance theorem for `Ξ`, every tank
with positive inductance. The effective-tension theorem's `S = D − C*A⁻¹C` is the Schur complement
that censoring a Markov chain or Kron-reducing a passive network produces. The lattice's
contribution is a worked case where the reduced form is computed exactly and its cross kernel is
finite-rank with an explicit inclusion–exclusion over shared squares. First derivation target:
write the folded source of MFR2 as a censored chain on prime-power events, identify the old
interior with the commuting (multiplicative) sector, and ask whether its contact kernel with the
additive sector is finite-rank in any truncation. Falsifier: a truncation whose contact kernel has
rank growing with the truncation, which would say the arithmetic crossing is of the
capture kind and must be summed over histories.

[interpretation] **A combinatorial hypothesis that forces real zeros exists, and it is the
right shape.** Chudnovsky–Seymour is a theorem of the form "a local forbidden configuration in
the dependence graph implies every zero of the independence polynomial is real." `Ξ`'s Hadamard
product `∏ (1 − z²/ρ²)` is an independence-polynomial-like product over zero pairs (the Foster
tanks). First derivation target: for the finite Foster forms the FT contract builds, define the
dependence graph among tanks induced by the flow threads `2/(z_j − z_k)` and test whether a
claw-free condition on that graph is provable at each truncation. Falsifier: a truncation whose
tank graph contains a claw while its zeros stay real, which would show the criterion is sufficient
but not the mechanism.

[interpretation] **The two obstructions are separable and should be tested separately.** The
lattice offers a controlled experiment that the arithmetic object does not: the recurrent lattice
(generators reusable, pieces returning) at inverse temperature `β` has a transfer operator `P_β`
with Artin–Mazur zeta `1/det(1 − zP_β)`. Derivation target: compute its spectrum as `β` varies,
with and without captures. Prediction from §5: with pieces only, detailed balance holds at
`β = 0` and the spectrum is real; irreversibility enters through pawns and captures, not through
`β`. Falsifier: a claw-free, capture-free menu whose spectrum leaves the real axis at some finite
`β`, which would couple the two parameters and make the gradient one-dimensional after all.

[open] None of this touches `Λ_DN ≤ 0`. The missing inequality is unchanged. What the note
supplies is a finite model in which every analogue of the open question is a theorem with a
combinatorial hypothesis, a computed kernel of explicit rank, and two obstructions that can be
switched on independently.

---

## 9. Boundaries

- The lattice is pseudo-legal chess at a fixed root with fixed menus; nothing here is a statement
  about chess as a game, and every count depends on the menu aperture.
- "Generators are primes" is an interpretation of generating functions, exact for the free
  commutative monoid and structural otherwise; it does not identify any lattice zero with a zero
  of ζ.
- Temperature is a policy aperture and the de Bruijn–Newman time is a heat time; §6 records them
  as different parameters with a shape in common, and §8 states what would refute even that.
- The receipt's reality tolerance is `1e−4` on imaginary parts, because Durand–Kerner leaves
  small residues on repeated real zeros; the factorizations in §5 are exact by hand.
- No engine source, formal source, canon, roadmap or position changed. The experiment directory
  and this record are the only additions.
