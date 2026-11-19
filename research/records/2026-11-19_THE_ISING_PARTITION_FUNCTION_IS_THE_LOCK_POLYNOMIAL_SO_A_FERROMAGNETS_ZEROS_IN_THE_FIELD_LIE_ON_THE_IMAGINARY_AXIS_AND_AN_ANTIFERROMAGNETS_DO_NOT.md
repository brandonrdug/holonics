# The Ising partition function is the lock polynomial, so a ferromagnet's zeros in the field lie on the imaginary axis, and an antiferromagnet's do not

November 19, 2026, 00:30 to 00:50 UTC. A derivation with its Lean proof and a host ruler, the fifth set of the
evening. Nothing ran on a learner or on the card, and no line was touched. Each paragraph carries its grade: `tree`
(read in this repository), `from training` (a result of the literature, named) or `agent-inferred` (this record's
join). Every Lean statement cited names its module and theorem, and the module builds with no `sorry`, no added
axiom and no `native_decide` (§6). Refs #410.

Owners touched: `parametron.lee-yang-circle`, `parametron.ising-lock`. One atlas row enters,
`thermal.ising-lee-yang` (§6).

Receipts: [`fifth_ruler.py`](2026-11-19_THE_ISING_PARTITION_FUNCTION_IS_THE_LOCK_POLYNOMIAL_SO_A_FERROMAGNETS_ZEROS_IN_THE_FIELD_LIE_ON_THE_IMAGINARY_AXIS_AND_AN_ANTIFERROMAGNETS_DO_NOT_receipts/fifth_ruler.py), three sections, every check an assert, all pass, 0.1 seconds in one
process on the cloud container's host (numpy's default threads; double floats for sums, roots and angles, printed as
the ruler's readings); its output [`fifth_ruler_output.txt`](2026-11-19_THE_ISING_PARTITION_FUNCTION_IS_THE_LOCK_POLYNOMIAL_SO_A_FERROMAGNETS_ZEROS_IN_THE_FIELD_LIE_ON_THE_IMAGINARY_AXIS_AND_AN_ANTIFERROMAGNETS_DO_NOT_receipts/fifth_ruler_output.txt) and the guesses fixed in its
source before its first run, [`guesses.txt`](2026-11-19_THE_ISING_PARTITION_FUNCTION_IS_THE_LOCK_POLYNOMIAL_SO_A_FERROMAGNETS_ZEROS_IN_THE_FIELD_LIE_ON_THE_IMAGINARY_AXIS_AND_AN_ANTIFERROMAGNETS_DO_NOT_receipts/guesses.txt) (the first run started 00:44:59 UTC and the passing
run 00:45:08 UTC by `date -u`).

## 1. The frame

`tree`. The fourth record of November 18
([the half is the positivity of the reversal's own form](2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_A_FINITE_COMPLEX_HAS_ITS_ZEROS_AND_COUNT_IN_LEAN_COUPLED_LOCKS_KEEP_THE_CIRCLE_TWO_TORIS_INDEX_THEOREM_IS_A_NORM_AND_BELOW_REYNOLDS_ONE_THE_COUNT_DECIDES.md))
proved the Lee–Yang circle theorem for the lock polynomial
`Π(z) = Σ_S (∏_(i∈S, j∉S) a_ij) ∏_(i∈S) z_i` with symmetric couplings in `[−1, 1]`
(`Coupling/LeeYangCircle`, atlas `parametron.lee-yang-circle`). Its header said that this polynomial is the Ising
partition function up to a monomial, and said that the identity was stated there only. The survey of the evening
(what in the tree has standing outside it) ranked that theorem third, and named the missing identity as the step
between a statement about a polynomial and the statement a physicist uses. This record writes the partition function
and proves the identity, so the theorem is stated in the field `h`, where the physics reads it.

`from training`. What the theorem is for. The free energy per site of a lattice of spins is `−(1/β) log Z / |V|`,
and a phase transition is a point where its limit over growing lattices is not analytic. At finite size `Z` is a
polynomial in the fugacity, and `log Z` is analytic wherever `Z` does not vanish, so a transition can only sit
where zeros of `Z` close in on the real axis as the lattice grows. Lee and Yang (1952) proved that for a
ferromagnet every zero in the field lies on the imaginary axis. It was the first rigorous statement of where a phase
transition can occur, and it is used in three places today: statistical mechanics (the Yang–Lee edge singularity,
Fisher's zeros, the extensions of Griffiths, Simon–Griffiths and Newman); the theory of stable polynomials
(Asano's contraction and Ruelle's form of it are the ancestors of the Borcherds–Brändén characterization of
stability preservers); and experiment, where Lee–Yang zeros were observed through the coherence of a probe spin
coupled to a spin bath (Peng and others, Physical Review Letters, 2015).

Prior formal work, read on the web after this record merged (the sixth record of November 19, §1): the Lean 4
project [phasetr/ising-model](https://phasetr.github.io/ising-model/coverage/chapters-2-10.html) lists the Lee–Yang
circle theorem for the Ising model, and the infinite-volume analyticity of the free energy off the circle, as done.
This module is not a first formalization; it joins the theorem to the tree's lock polynomial.

## 2. What the tree held

`tree`. `Coupling/LeeYangCircle` holds the circle theorem (`lockPoly_zero_on_circle`), the two half-planes
(`lockPoly_ne_zero_of_norm_lt_one`, `lockPoly_ne_zero_of_one_lt_norm`), the two-lock polynomial
`1 + (a₀₁ + a₁₀) ζ + ζ²` (`lockPoly_two`) and a coupling above one that puts two locks' zeros off the circle
(`two_locks_off_circle_of_one_lt`). `Objects/Parametron` holds the locked sheet's Ising energy
(`drivenPhaseEnergy_binaryPhase`, atlas `parametron.ising-lock`): on the two sheets `θ ∈ {0, π}` the driven phase
energy is `−w σ_i σ_j` with the drive as a field. `Objects/ParametronLock` holds two coupled locks
(`parametron.coupled-locks-lee-yang`). A search of `lean/` for `partition function` finds the levels' partition
function of a thermal port (`Physics/Information/PortWork.partition`, `Z(E) = Σ exp(−Eᵢ/θ)`), the one of a
constitution's edge levels (`Aeon/Production/FirstLaw`) and the single lock's `Π(a) = 1 + a/K` (`ParametronLock`),
and none for a population of coupled sheets: no module wrote `Σ_σ exp(−βE(σ))` for the Ising energy and joined it
to `Π`. At a real field the Ising partition function is the port's `Z(E)` at the configurations' levels and
`θ = 1/β`; that join is read here and not proved.

## 3. The cut identity, and the partition function as the lock polynomial

`proved-standard`. Take a finite set `V` of sites, a symmetric real exchange `J`, an inverse temperature `β` and
complex fields `h_i`. A configuration is its set `S` of up sites, with `s_i = 1` on `S` and `−1` off it, and

  `Z = Σ_S exp(β/2 · Σ_(i,j) J_ij s_i s_j + β Σ_i h_i s_i)` (`Coupling/LeeYangIsing.isingZ`),

the double sum over ordered pairs, so each pair is weighed once. Two lines carry the proof.

- **The exchange pays only across the cut** (`coupling_sum_eq`): `Σ_(i,j) J_ij s_i s_j = Σ J − 4 Σ_(i∈S, j∉S) J_ij`.
  The product `s_i s_j` is `+1` for a pair on one side and `−1` for a pair the cut separates, and symmetry counts
  each separated pair twice.
- **The field pays only on the up sites** (`field_sum_eq`): `Σ h_i s_i = 2 Σ_(i∈S) h_i − Σ h`.

So one configuration's weight is `exp(β/2 ΣJ − β Σh) · ∏_(i∈S, j∉S) e^(−2βJ_ij) · ∏_(i∈S) e^(2βh_i)`
(`exp_exponent`), and summing over `S`,

  `Z = exp(β/2 ΣJ − β Σh) · Π(e^(−2βJ), e^(2βh))` (`isingZ_eq_lockPoly`).

The prefactor never vanishes, so `Z` and `Π` share their zeros. A diagonal entry `J_ii` adds the constant
`β J_ii / 2` to every exponent and moves no zero; the identity holds with it.

`agent-inferred`, the reading on the objects. A site is a lock with two sheets, an exchange is a pair contact
whose weight `e^(−2βJ)` is paid exactly when the cut separates its two ends, and the field is each lock's fugacity.
A ferromagnetic contact (`J ≥ 0`, the two ends agreeing) has weight in `(0, 1]`, inside the circle theorem's
range; a disagreeing contact (`J < 0`) has weight above one, outside it.

## 4. The Lee–Yang theorem in the field, and where it fails

`proved-standard`. For a ferromagnet at `β > 0`:

- **No zero in either half-plane** (`isingZ_ne_zero_of_re_pos`, `isingZ_ne_zero_of_re_neg`). If every field has
  positive real part, every fugacity has `|e^(2βh_i)| = e^(2β Re h_i) > 1` (`norm_fugacity`), and the circle
  theorem's outer half-plane gives `Π ≠ 0`; every field with negative real part gives the inner one. The fields may
  differ from site to site.
- **The theorem** (`lee_yang_ising`). In one common field `h`, `Z = 0` gives `Re h = 0`; in the fugacity, every
  zero lies on the unit circle (`lee_yang_ising_fugacity`).
- **The ferromagnet is load-bearing** (`antiferromagnet_zero_off_axis`, a counterexample). Two sites with exchange
  `−K < 0` at any `β > 0`: the lock polynomial is `ζ² + 2yζ + 1` with `y = e^(2βK) > 1`, whose roots
  `−y ± √(y² − 1)` are real and negative with product one, so neither is on the circle, and `h = log ζ / (2β)` is
  a zero of `Z` with `Re h = log|ζ| / (2β) ≠ 0`.

`from training`, what follows physically. At finite size `Z` has finitely many zeros in the field and all sit on
the imaginary axis, so a real field `h ≠ 0` stands a fixed distance from every one of them, and `log Z` is
analytic there. As the lattice grows, the zeros can close in on the real axis only at `h = 0`. That is why a
ferromagnet orders only at zero field, and why its magnetization is smooth in any nonzero real field. An
antiferromagnet in a uniform field does have transitions at nonzero field (the Néel line of the Ising
antiferromagnet), and the counterexample is the smallest place where the hypothesis that excludes it shows.

## 5. Guesses and scores, and what follows for the machine

The guesses were fixed in the ruler's source before its first run (`guesses.txt`). The first run stopped in
section B at its third two-site case, `K = 2`, `β = 2`: the instrument computed the root `−y + √(y² − 1)` at
`y = e⁸` by subtraction, lost its digits to cancellation, and read `Z(h)/Z(0) = 3·10⁻⁹` against a bound of
`10⁻¹⁰`. That was a defect of the instrument, not a miss of the statement. The root was rewritten in its
cancellation-free form `−1/(y + √(y² − 1))`, nothing else changed, and the passing run read `8·10⁻¹⁶` there.

- **A** (scored: hit). On `n = 2` to `7` sites with symmetric `J` of either sign, diagonal included, the
  partition function summed over the `2ⁿ` spin configurations equals the prefactor times the lock polynomial, worst
  relative gap `4.4·10⁻¹⁵` over 36 samples. The planted asymmetric `J` misses by 12.4 relative, so the instrument
  sees a failure of the symmetry hypothesis.
- **B** (scored: hit). For 36 random ferromagnets on `n = 2` to `10` sites, every root in the fugacity sits on
  `|z| = 1`, worst deviation `4.0·10⁻¹⁵`, and the coefficients are palindromic (the circle theorem's reversal,
  `lockPoly_reversal`). All 28 planted antiferromagnets have a root off the circle. The three two-site cases put
  `Z(h)/Z(0)` under `10⁻¹⁵` at `h = log ζ/(2β)` with `Re h` between −0.83 and −2.17.
- **C** (scored: hit). On the Curie–Weiss ferromagnet (`J = 1/n` between distinct sites), the least angle of a zero
  from `z = 1` at `β = 2` falls from 0.877 at `n = 4` to 0.241 at `n = 14` (ratio 0.274 against the guess's
  "under one half"); at `β = 0.5` it falls from 1.629 to 1.042 (ratio 0.640 against "over one half").

`agent-inferred`, a reading not guessed beforehand. At `β = 2` the product `n · θ_min` reads 3.51, 3.48, 3.45,
3.41, 3.39 and 3.37 for `n = 4` to `14`. Lee and Yang's relation between the spontaneous magnetization `m` and the
density of zeros at `θ = 0` (`from training`: `m = 2π g(0)`, zeros spaced `2π/(n m)` near the real axis, the
first at about `π/(n m)`) gives `π/m = 3.28` with `m = tanh(2m) ≈ 0.957`, and the readings fall toward it. At
`β = 0.5` the least angle is still falling at `n = 14`; its limit, the Yang–Lee edge, is not read here.

`agent-inferred`, what follows for the machine, stated as a test. The parametron's locked sheets are Ising sites
(`parametron.ising-lock`), so a population of locks whose contacts all agree has every zero of its sum over sheets
on the imaginary axis of its drive, by `lee_yang_ising`. The test: for such a population, the share of locks on one
sheet, read against a real drive, is smooth at every nonzero drive at every size, and it can steepen without bound as
the population grows only at zero drive; a population whose contacts disagree can steepen at a nonzero drive. What
does not transfer: the engine's contacts carry complex phases and learned weights, not `±1` sheets with a real
symmetric exchange, and no limit over growing populations is proved. The statement reaches a population of locks
only once it sits on its two sheets.

## 6. Lean, atlas and receipts

`tree`. `lean/HolonicsResearch/Coupling/LeeYangIsing.lean` (namespace `Holonics.Coupling.LeeYangIsing`, imported by
`lean/HolonicsResearch.lean`) holds `spin`, `exponent`, `isingZ`, `lockCoupling` and `fugacity`, and the
theorems `coupling_sum_eq`, `field_sum_eq`, `exp_exponent`, `isingZ_eq_lockPoly`, `norm_fugacity`,
`isingZ_ne_zero_of_re_pos`, `isingZ_ne_zero_of_re_neg`, `lee_yang_ising`, `lee_yang_ising_fugacity` and
`antiferromagnet_zero_off_axis`. Its audit prints `[propext, Classical.choice, Quot.sound]` for each. The header of
`Coupling/LeeYangCircle` now names this module where it said the identity was stated in the header only.

The atlas row `thermal.ising-lee-yang` (`docs/atlas/physics.tsv`) enters with these owners and
`uses:parametron.lee-yang-circle, uses:parametron.ising-lock`.

What the module does not state: no limit over growing `V` (the density of zeros, the thermodynamic free energy and
its analyticity off `h = 0`); spins are `±1`, so the single-spin extensions of Griffiths, Simon–Griffiths and
Newman and the quantum versions are not here; the exchange is real and symmetric and the fields enter linearly.
