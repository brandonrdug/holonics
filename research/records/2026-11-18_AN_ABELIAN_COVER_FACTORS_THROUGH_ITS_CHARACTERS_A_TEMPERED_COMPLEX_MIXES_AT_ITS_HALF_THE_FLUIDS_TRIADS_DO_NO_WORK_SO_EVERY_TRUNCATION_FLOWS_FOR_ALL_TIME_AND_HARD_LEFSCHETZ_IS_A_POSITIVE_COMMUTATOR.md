# An abelian cover factors through its characters, a tempered complex mixes at its half, the fluid's triads do no work so every truncation flows for all time, and hard Lefschetz is a positive commutator

November 18, 2026, 23:08 to 23:42 UTC. Derivations with their Lean proofs and a host ruler, the third set of the
evening. Nothing ran on a learner or on the card, and no line was touched. Each paragraph carries its grade: `tree`
(read in this repository), `from training` (a result of the literature, named) or `agent-inferred` (this record's
join). A statement cited as Lean names its module and theorem; every such module builds with no `sorry`, no added
axiom and no `native_decide` (§10). Refs #410.

This record continues [the first set](2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_A_FINITE_COMPLEX_HAS_ITS_ZEROS_AND_COUNT_IN_LEAN_COUPLED_LOCKS_KEEP_THE_CIRCLE_TWO_TORIS_INDEX_THEOREM_IS_A_NORM_AND_BELOW_REYNOLDS_ONE_THE_COUNT_DECIDES.md)
and [the second](2026-11-18_A_REGULAR_COMPLEXS_OWN_HALF_IS_ONE_CHAIN_OF_FIVE_READINGS_A_KEPT_POSITIVE_FORM_EXISTS_WHERE_THE_MODES_ARE_SEMISIMPLE_ON_THE_LOCUS_AND_THE_SECOND_LAW_STARTS_FROM_ANY_DENSITY.md)
("the first record", "the second record"), whose mechanism it keeps: a move with a reversal builds a form the move
scales, and where the form is positive every mode sits at the half.

Owners touched: `trace.double-cover-artin`, `trace.ihara-bass-connection`, `trace.regular-zeros-on-circle`,
`trace.prime-cycle-half-rank`, `trace.regular-half-chain`, `key.connection-cheeger`, `rh.escape-threshold-half`,
`ns.comb-conserved-counts`, `ns.laminar-class-reynolds`, `ns.laminar-stability-uniqueness`,
`hodge.two-tori-lattice-chart`, `hodge.torus-power-narayana`, `hodge.dimension-bounded-lefschetz`. Eight atlas rows
enter and three gain Lean owners (§10).

Receipts: [`third_ruler.py`](2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR_receipts/third_ruler.py),
five sections, every check an assert, all pass, 8.9 seconds in one process on the cloud container's host (numpy's
default threads; double floats throughout, printed as the ruler's readings); its output
[`third_ruler_output.txt`](2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR_receipts/third_ruler_output.txt)
and the guesses fixed in its source before its first run,
[`guesses.txt`](2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR_receipts/guesses.txt)
(the passing run started 23:32:09 UTC by `date -u`; the first run's stamp was not kept).

## 1. The frame

The first two records placed a finite complex's modes at the half in six charts and joined five readings of that
half into one statement. Three readings stood beside them unproved: what a cover adds to its base (the first record
proved it for two sheets only), how a tempered complex spreads density (the half read by sets of cells rather than by
modes or walks), and how many prime cycles a tempered complex has (the second record had their Möbius form and the
walk count's bound, not the two joined). This record proves the three (§3 to §5).

On the fluid, the first record's truncation took two things as hypotheses: that its feed does no work, and that a
solution exists. This record proves both: the fluid's own triads do no work (§6), and every truncation therefore runs
for all time from every real divergence-free state, once, with its energy account and, below Reynolds one, with the
second record's decay (§7). On Hodge, the hard Lefschetz theorem is proved from the positivity of one commutator, and
the integral (1,1) classes of a product of `n` tori are written as sums over pairs of factors (§8).

## 2. What the tree held

`tree`, read before each statement was written.

- `Landmarks/IharaBassConnection`: Ihara–Bass with a connection and Artin's factorization for a double cover
  (`artin_double_cover_hashimoto`, one block operation); atlas `trace.double-cover-artin`, whose scope names the
  factorization's general form as Stark and Terras's. Its header named the cover of more sheets as not there.
- `Landmarks/RegularComplexZeros` (`walkCount_bound`, `eigen`, `trace_hashimoto_pow`), `Landmarks/RegularComplexHalf`
  (`half_tfae`) and `Landmarks/IharaEulerProduct` (`primeCycles_moebius` over `ℤ`, `trace_hashimoto_pow`); atlas
  `trace.prime-cycle-half-rank`, whose expression carries the Möbius line and the bound as two statements.
- Atlas `key.connection-cheeger` (a connection Laplacian's Cheeger inequality, cited, with its gauge invariance in
  Lean) and `rh.escape-threshold-half` (the half as an escape threshold, expanders from Selberg's 3/16). No row held
  the expander mixing lemma, Hoffman's bound or the walk's relaxation on a tempered complex.
- `Fluid/NavierStokesGalerkinInstance`: the truncation, `Conservative` and `WeightedConservative` as hypotheses, and
  its sentence that the fluid's own feed being conservative "needs the mode set closed under `k ↦ -k` with the reality
  condition, and is not assembled here". `Fluid/NavierStokesLaminarStability` (the second record): stability,
  uniqueness and decay below Reynolds one, for a truncation given as a hypothesis. Atlas `ns.comb-conserved-counts`
  ("the feed's conservation is a hypothesis, not proved for the fluid's triads here") and `ns.laminar-class-reynolds`
  ("no existence and no limit of truncations here").
- `Hodge/HodgeEllipticProduct` and `Hodge/HermitianLightCone` (the first record): the (1,1) classes of two tori and the
  index theorem; atlas `hodge.two-tori-lattice-chart` and `hodge.torus-power-narayana` (the count of Hodge classes on
  `Eⁿ` by a ruler, no Lean). `Hodge/HodgeDimensionBoundedLefschetz` takes hard Lefschetz as a surjective reflection
  (atlas `hodge.dimension-bounded-lefschetz`). The two Hodge files of this set were begun by the evening's first proof
  thread and finished here.

## 3. An abelian cover's dart determinant is the product of its characters

**3.1 The statement.** `proved-derived; formal-checked` (`Landmarks/IharaAbelianCover`). Take a finite complex (cells
`V`, contacts `E`), a finite commutative ring `G` whose additive group carries the voltages (every finite abelian group
is one: a product of `ZMod mᵢ`), and a voltage `σ` on the darts. The cover has cells `V × G`, and the dart `(d, s)`
leaves `src d` on sheet `s` and enters `tgt d` on sheet `s + σ(d)`. With one primitive additive character `ψ` into a
domain in which `#G` is not zero, the `k`-th character is `x ↦ ψ(kx)`, and

  `det(1 − u B_Y) = ∏_(k∈G) det(1 − u · diag(ψ(k σ)) · B)` (`artin_abelian_cover`),

for every voltage and every `u`. The proof is one intertwining with no division: the matrix
`W = 1 ⊗ (ψ(sk))_(s,k)` carries functions of the sheets to their characters, `(1 − uB_Y) W = W · blockDiag_k(1 − u
diag(ψ(kσ)) B)` (`cover_mul_fourier`), and `W` is invertible because the characters are orthogonal (`W̄W = #G`,
`charTableInv_mul_charTable`). When `σ(d̄) = −σ(d)` each twist is a connection (`twist_connection`), so every factor
obeys Ihara–Bass with its own connection (`artin_abelian_cover_ihara_bass`), the trivial character's factor is the
base (`artin_abelian_cover_base`, so `base_dvd_cover`), and the cover is a complex of the plain kind whose own dart
operator the statement reads (`hashimoto_cover`, `artin_abelian_cover_hashimoto`). One loop of voltage `h` over `ℤ/m`
gives `∏_k (1 − ψ(kh)u)(1 − ψ(−kh)u)` (`loopCover_det`), and with voltage 1 the product multiplies out to `(1 − u^m)²`,
the `m`-cycle's own determinant (`cycle_det`).

**3.2 The reading.** `from training` and `agent-inferred`. This is Artin's factorization `ζ_Y = ∏_χ L(χ)` for an
abelian cover of a finite complex (Stark and Terras 1996). Read on the objects: the voltage is a pair contact's carry
between sheets, the characters are the cover's own frames, and the factorization is the diagonalization of the sheets
by those frames. Each character reads a closed walk by its holonomy, the sum of the voltages it crossed, and the gauge
theorem of `IharaBassConnection` (a twist's determinant reads holonomies alone) applies to every factor. A product
vanishes where one of its factors does, so the cover's zeros are the base's together with each twist's, and the cover
sits on the half exactly when every character's twisted complex does (`agent-inferred`, immediate from A1). This is the
finite form of the statement that the Riemann hypothesis for a number field's zeta is the Riemann hypothesis for each
of its characters' L-functions.

## 4. A tempered complex spreads density within its half

**4.1 The statements.** `proved-standard; formal-checked` (`Landmarks/RegularComplexDensityLaw`). The module works in
three layers. A real symmetric `A` whose rows all sum to `d` on `n` cells, with a bound `μ` on the mean-free functions
(`|Af|² ≤ μ²|f|²`), satisfies:

- mixing: `|e(S, T) − d|S||T|/n| ≤ μ √(|S|(1 − |S|/n) · |T|(1 − |T|/n))` (`Balanced.mixing`), through the split
  `e(S, T) = d|S||T|/n + (centred S)·A(centred T)` (`Balanced.contacts_eq`);
- the boundary: `e(S, Sᶜ) ≥ (d − μ₂)|S|(n − |S|)/n` from the one-sided bound (`Balanced.cheeger`, the easy side of
  Cheeger's inequality);
- free sets: a set with no inner contacts has `|S|/n ≤ ν/(d + ν)` from the lower bound (`Balanced.hoffman_density`);
- relaxation: the walk `P = A/d` has `|Pᵗp − u|² ≤ (μ/d)^(2t)|p − u|²`, and with nonnegative entries its relative
  entropy against the uniform density is at most `(n − 1)(μ/d)^(2t)` nats (`Balanced.relaxation`,
  `Balanced.relEntropy_walk_le`);
- the floor: with natural entries, `d(n − d) ≤ (n − 1)μ²` (`Balanced.floor`).

The bridge from the modes (`Balanced.meanFreeBound_of_eigen` and its one-sided forms) turns a bound on every mode but
the count into these bounds, and on a complex with `q + 1` darts at every cell whose other modes are tempered, `μ =
2√q` (`tempered_meanFreeBound`): two sets share their expected contacts within `2√q √(|S||T|)` (`tempered_mixing`),
every set loses at least `(q + 1 − 2√q)|S|(n − |S|)/n` contacts (`tempered_boundary`), no free set holds more than a
share `2√q/(q + 1 + 2√q)` of the cells (`tempered_hoffman`), and a walk closes on the uniform density at
`2√q/(q + 1)` a tick (`tempered_relaxation`, `tempered_relEntropy`).

**4.2 The reading.** `agent-inferred`. The first two records read the half by modes, zeros, walks and an index. Here it
is read by density: the tempered hypothesis is the statement that what a cell holds spreads to every set in proportion
to its size, up to the half's own square root, and that the forgetting of a start runs at the half's rate. A receiver
that counts contacts between two regions reads the half without solving for a mode. The floor is the trace's and tends
to `√(q + 1)`, below `2√q`, so it constrains complexes better than tempered and never a tempered one; the floor at
`2√q` itself (Alon and Boppana, `from training`) reads walks on the covering tree, the construction that would carry
the floor to the half.

## 5. The prime cycles of a tempered complex number `qⁿ/n` up to the square root

**5.1 The statements.** `proved-derived; formal-checked` (`Landmarks/PrimeCycleHalf`). Write `c = |E| − |V|`, `W_l` the
trace of `Bˡ` and `N_n` the prime cycles of length `n` (the necklaces of `IharaEulerProduct`). The bridge reads the
integer Möbius form in the reals, `Σ_(d∣n) μ(n/d) W_d = n N_n` (`primeCycles_moebius_real`). Under the tempered
hypothesis, each length's remainder is `|W_d − q^d| ≤ 1 + 2|c| + 2(|V| − 1)√q^d` (`walkCount_sub_pow_le`), and for
`n ≥ 1`:

- P1: `|n N_n − Σ_(d∣n) μ(n/d) q^d| ≤ Σ_(d∣n) (1 + 2|c| + 2(|V| − 1)√q^d)` (`moebius_error`);
- P2: `|N_n − qⁿ/n| ≤ (2|V| − 1)√qⁿ + 1 + 2|c|` (`prime_cycle_theorem_div`), because a proper divisor `d` of `n` has
  `2d ≤ n` and so `q^d ≤ √qⁿ`;
- P3: for `q ≥ 2`, `|n N_n − qⁿ| ≤ 8|E| √qⁿ` with a constant free of `n` (`prime_cycle_theorem_uniform`);
- P4, on every finite complex: `n N_n ≤ tr Bⁿ` (`mul_primeCycles_le_trace`), every term of `Σ_(d∣n) d N_d` being a
  count.

**5.2 The reading.** `from training` and `agent-inferred`. This is the prime number theorem for a graph (Ihara 1966;
Terras) with the Riemann hypothesis's error term: the prime cycles of length `n` number `qⁿ/n`, and the error is the
half's own size, each mode other than the count adding `√q^d` and nothing in the error growing faster. With
`half_tfae` of the second record, a complex's own half now reads as a band for its modes, a circle for its zeros, a
square root for its walk count, a count of negative squares, a density law (§4) and a prime count with a square-root
error. On the integers the same pairing is the explicit formula, whose zeros the error term reads; the finite word that
places them is the positive form on the unending family, the construction the second record's §6.3 names.

## 6. The fluid's own triads do no work

**6.1 The statements.** `proved-derived; formal-checked` (`Fluid/NavierStokesTriadConservation`). For any wave vectors
and amplitudes across their own wave vectors, the sum over triples with `κ_p + κ_q + κ_r = 0` of
`(κ_q · a_p)(a_q · a_r)` is zero (`triadSum_eq_zero`): exchanging `q` and `r` keeps the condition and the second
factor, and the two halves add to `(κ_q + κ_r) · a_p = −κ_p · a_p = 0`, the chart of `∫ (u·∇u)·u = −½∫(∇·u)|u|² = 0`.
On a wave set closed under `k ↦ k̄` with `κ(k̄) = −κ(k)` and a real field (`a(k̄) = conj a(k)`), the work of Leray's
feed is `−i` times that sum, so `Σ_k ⟨a_k, N_k⟩ = 0` (`sum_inner_feed_leray_eq_zero`), and a truncation whose state is
real at every time keeps its energy equality with no hypothesis on the feed (`Truncation.energy_add_dissipation_of_real`).
The truncated field keeps the real, divergence-free states (`field_isRealField`, `wavePairing_field_eq_zero`). In the
plane, with stream amplitudes, the six orderings of each closed triad's geometric factor add to zero, so the enstrophy
is conserved too (`weightedTriadSum_normSq_eq_zero`, `Truncation.weightedConservative_of_real_two`), and the critical
reading of every plane truncation is bounded for all time by `√(Σ‖κ_k‖⁻⁴) √(2E₂(0))`
(`Truncation.critical_le_of_real_two`).

**6.2 The reading.** `agent-inferred`. A triad is a closed pair contact of three modes, and the identity says that the
transport around it returns the energy it moves. The first record's hypothesis is the fluid's own. Two dimensions and
three part at one place: the enstrophy work, zero in the plane and not zero in space (ruler D: 7.3e-18 against 1.8e-2
of its scale), which is the stretching of vorticity.

## 7. Every truncation flows for all time, once

**7.1 The global flow of a dissipative law.** `proved-derived; formal-checked` (`Fluid/DissipativeGlobalFlow`). On a
complete real inner product space, a field with `⟪x, F x⟫ ≤ 0` that is Lipschitz on every ball has from every state one
solution on `[0, ∞)`, whose norm never rises (`exists_global`, `existsUnique_global`). The proof steps Picard and
Lindelöf on the ball the start sits in: the step time depends on the ball and not on the point
(`exists_step`), and because the norm never rises every later start stays in that ball (`exists_on_Icc`). A field
`A + B(·,·)` with `⟪x, Ax⟫ ≤ 0` and `⟪x, Bxx⟫ = 0` is both (`lipschitzOnBalls_linear_add_bilinear`,
`dissipative_linear_add_bilinear`), and with a damping rate it decays at `e^(−νt)` (`norm_le_exp_quadratic`).

**7.2 The join.** `proved-derived; formal-checked` (`Fluid/NavierStokesTruncatedGlobal`). The amplitudes of all modes
form a real inner product space (`State`), the real divergence-free states a subspace of it (`realStates`), and on that
subspace the truncated field's work is the damping's alone, `⟪x, Fx⟫ = −ν Σ_k ‖κ_k‖²‖x_k‖²` (`inner_fieldOn`). So:

- every Galerkin truncation with Leray's projections on a wave set closed under `k ↦ −k`, with distinct nonzero wave
  vectors and `ν > 0`, has from every real divergence-free opening state a solution for all `t ≥ 0`, real and
  divergence-free at every time (`exists_truncation`);
- two truncations from one state agree at every time, real or not (`truncation_eq`, from the field's Lipschitz
  constant on a ball that holds both on `[0, T]`);
- it keeps `E(t) + ν∫₀ᵗ Σ_k ‖κ_k‖²‖a_k‖² = E(0)` (`exists_truncation_energy`);
- in the plane its critical reading stays under `√(Σ‖κ_k‖⁻⁴) √(2E₂(0))` (`exists_truncation_plane`);
- below Reynolds one in any dimension (`X(0) < ν`, every wave vector at least `w₀` long),
  `X(t) ≤ X(0) · exp(−(ν − X(0)) w₀² t)` (`exists_truncation_laminar`), the second record's S6 with its instance.

**7.3 The reading.** `agent-inferred`. Every statement of the first and second records that took a truncation as a
hypothesis now has an instance from every real divergence-free opening state. The constants of existence depend on the
truncation (the Lipschitz constant on a ball grows with the modes); the energy equality, the plane's bound and the
laminar decay do not. Those uniform bounds are the inputs a limit of truncations uses: in the plane, the energy and the
enstrophy together give Leray and Ladyzhenskaya's global solution once the limit is taken (`from training`); in space,
below Reynolds one, the laminar class gives it for small data (Lei and Lin 2011, `from training`). The construction
this names for the fluid on all wave vectors is the compactness step from the truncations' uniform bounds to a limit,
with the second record's `Fluid/NavierStokesLaminarAllModes` as its receiver; above Reynolds one in space, it is a
second count that the triads conserve or dissipate, which the enstrophy is not.

## 8. Hard Lefschetz is a positive commutator, and the (1,1) classes of `n` tori are pairs

**8.1 Hard Lefschetz.** `proved-derived; formal-checked` (`Hodge/LefschetzFromPositivity`). A real inner product space
with a move `U`, its reversal `D = U†` and their commutator `H = DU − UD`, with `HU − UH = −2U`, has
`‖Ux‖² − ‖Dx‖² = ⟪x, Hx⟫` for every `x` (`Triple.norm_sq_U_sub_norm_sq_D`). On a weight `m ∈ ℕ` each step along the
string multiplies the squared norm by at least `(j + 1)(m − j) > 0`, so `m! ‖x‖ ≤ ‖Uᵐ x‖` in any dimension
(`Triple.hard_lefschetz`). On primitives the same identity is an equality, `⟪Uʲx, Uʲy⟫ = ∏_(i<j) (i + 1)(m − i) ⟪x, y⟫`
(`Triple.inner_iterate_primitive_nat`), the Hodge–Riemann form with its positive constant. In finite dimension
`Uᵐ : W(m) → W(−m)` is a linear equivalence (`Triple.lefschetzMap_bijective`, `Triple.lefschetzEquiv`), the two halves
have equal dimension (`Triple.finrank_weightSpace_neg`), and `dim P(m) + dim W(m + 2) = dim W(m)` with `P(m)`
orthogonal to `U W(m + 2)` (`Triple.finrank_primitive_add`, `Triple.inner_primitive_move`).

**8.2 The (1,1) classes of a product of tori.** `proved-derived; formal-checked` (`Hodge/HodgeEllipticPower`). For tori
`Eᵢ = ℂ/(ℤ + ℤτᵢ)` over a finite ordered index, an alternating integer form on the lattice is of type (1,1) if and only
if each block above the diagonal is a homomorphism `Eᵢ → Eⱼ` (`isHodge_iff_blocks`), and every alternating form is, in
exactly one way, a combination of the fibre classes and of the blocks' lattice maps (`eq_sum_of_isAlt`,
`sum_decomposition_unique`). So the integral (1,1) classes are exactly the integer combinations of fibre classes and of
graphs of homomorphisms between two factors (`isHodge_iff_combination`).

**8.3 The reading.** `agent-inferred`. Hard Lefschetz is the half's mechanism once more: a move with its reversal builds
a form, here the commutator, and its positivity places every vector of positive weight where the move cannot lose it.
For a variety, what remains is the triple on its cohomology with a positive pairing: the Kähler identities give it, and
the Hodge–Riemann signs turn the intersection pairing into a positive one on each primitive part. In degree two on a
product of tori, every Hodge class is a sum of pair contacts between two factors, each one complex multiplier carrying
one lattice into another: the product adds no new kind of class. In degree `2k` the classes of `hodge.torus-power-narayana`
need products of these divisors, and from fourfolds Weil's classes, which are not products of divisors; the
construction there is the cycle that carries a Weil class, the case the Hodge conjecture for abelian varieties turns on.

## 9. Guesses and scores, and what follows for the machine

**9.1 Guesses** (fixed in the ruler's source before its first run, scored from its output). A: the cover's determinant
equals the product over characters to `1e-9` relative, the `m`-cycle gives `(1 − u^m)²`, a wrong character set misses:
hit (worst gap 4.8e-15; the wrong set misses by 7.8). B: mixing, Cheeger, Hoffman, relaxation and entropy hold on every
sampled tempered specimen, and two disjoint copies break mixing at `μ = 2√q`: hit, with one note: of the four random
multigraphs one (80 cells, degree 4, second mode 3.498 against 3.464) was not tempered, and every law held at its
spectral value; the planted copies deviate 60 against a bound of 51.96. C: inside P1 to `n = 16` on tempered specimens,
an untempered one outside: hit (Petersen 0.850, `K₄` 0.972, the prism 4.96). D: the triads' work zero to `1e-12` in two
and three dimensions, the plane's enstrophy work too, three dimensions' not, and a truncation set without `−k` does
work: half. The first four held (5.7e-17, 2.3e-17, 7.3e-18, 1.8e-2). The last missed as written: one wave vector
dropped with its `−k` kept did no work (1.8e-17), so the closed set is sufficient and not necessary; a random subset of
18 of 32 vectors not closed under `−k` did work (2.7e-3), and so did a non-real field on the closed set (2.7e-2), which
became the planted instances. E: RK4 on a plane truncation keeps the energy equality to `1e-6` and the norm never
rises: hit (1.2e-7 of `E(0)` over 1,500 steps, no rise); the planted `x' = x²` leaves `10⁶` by `t = 1.010`.

**9.2 Tests offered** (`agent-inferred`; none run on a learner).

- A coupled bank is a cover (§3). A bank of rings coupled by carries in an abelian group of residues is a cover of its
  base, and its modes are the base's together with each character's twisted modes: a ruler reads the twisted
  operators one character at a time, and a bank whose new modes leave the band names the character that carries them.
- A density read is a mode read (§4). Whether a contact graph of the machine is tempered can be read from the contacts
  two regions share against `d|S||T|/n`, with no eigenvalue solve, and the walk's forgetting rate `2√q/(q + 1)` is the
  clock a tempered region's start is lost on.
- Landmarks counted at the half (§5). The prime cycles of a tempered contact graph number `qⁿ/n` within the half's
  square root; a count above it at some length names a mode outside the band, the second record's one-sided test read
  on prime cycles.
- A law that does no work runs (§7). A realization whose update is a damping plus a transport that does no work has
  one flow for all time from every state; a run that leaves a ball has broken the transport's balance, and the
  balance `⟪x, Bxx⟫ = 0` is the check to read first.

**9.3 What does not transfer.** No statement here is about an unending family: the zeta function's zeros, a complex of
growing size, the fluid on all wave vectors or a variety's cohomology. Each is the construction named where its section
stands: the floor at `2√q` from the covering tree (§4.2), the positive form on the unending family (§5.2), the
compactness step from the truncations' uniform bounds (§7.3), and the Kähler triple with its positive pairing, with
the cycle of a Weil class beyond degree two (§8.3).

## 10. Lean, atlas and receipts

**10.1 Lean.** Eight modules under `lean/HolonicsResearch/`, each importing Mathlib and earlier modules of the tree or
of this list. Each builds with no `sorry`, no added axiom and no `native_decide`, and every audited theorem depends on
`propext`, `Classical.choice` and `Quot.sound` alone.

| Module | Lines | Theorems | Holds |
|---|---|---|---|
| `Landmarks/IharaAbelianCover` | 493 | 21 | §3: Artin's factorization over an abelian cover, the loop and the `m`-cycle |
| `Landmarks/RegularComplexDensityLaw` | 1,005 | 76 | §4: mixing, the boundary, free sets, relaxation, the floor |
| `Landmarks/PrimeCycleHalf` | 504 | 25 | §5: the prime cycle theorem at the half |
| `Fluid/NavierStokesTriadConservation` | 767 | 43 | §6: the triads do no work, the plane's enstrophy |
| `Fluid/DissipativeGlobalFlow` | 484 | 17 | §7.1: one global flow of a dissipative law |
| `Fluid/NavierStokesTruncatedGlobal` | 425 | 19 | §7.2: every truncation flows for all time, once |
| `Hodge/LefschetzFromPositivity` | 590 | 39 | §8.1: hard Lefschetz from a positive commutator |
| `Hodge/HodgeEllipticPower` | 507 | 28 | §8.2: the integral (1,1) classes of `n` tori |

Headers changed beside them: `Landmarks/IharaBassConnection` (the cover of more sheets now points to
`IharaAbelianCover`), `Fluid/NavierStokesGalerkinInstance` and `Fluid/NavierStokesLaminarStability` (existence for a
truncation now points to `NavierStokesTruncatedGlobal`). Where it was checked: in this thread's cloud container with
the project's pinned toolchain and Mathlib's cached build, each file by `lake env lean`, and all eight with the three
changed modules by `bash tools/lean_check.sh` on their module names (gate 4: 8,745 jobs, exit 0, 23:37:49 to 23:38:21
UTC). The root `HolonicsResearch.lean` gains their eight imports. The reason the guide gives for building on the PC
does not reach a kernel check of a proof under the pinned toolchain, as the first record's §14.1 states
(`agent-inferred`).

**10.2 Atlas.** Eight rows enter: `trace.abelian-cover-artin`, `trace.tempered-density-law` and
`trace.prime-cycle-theorem-half` (geometry); `hodge.torus-power-divisors`, `hodge.hard-lefschetz-positivity`,
`ns.triads-do-no-work`, `ns.dissipative-global-flow` and `ns.truncated-global-solution` (targets).
`ns.comb-conserved-counts` (its hypothesis now proved for the fluid's triads), `ns.laminar-class-reynolds` (existence
now held) and `trace.prime-cycle-half-rank` (its Möbius line joined to its bound) gain owners from this set.

**10.3 #410.** No open box of #410 names these statements; the set adds to its rows and leaves its boxes as they stand.

**10.4 Receipts.** The ruler, its output and the guesses, named at the head of this record. Its five sections: A
Artin's factorization on six cyclic covers at random `u` and the `m`-cycle; B the density law on four random
multigraphs of degree 4 and 6; C prime cycles by Möbius inversion of the traces on Petersen and `K₄`; D the triads'
energy and enstrophy work in two and three dimensions; E RK4 on a plane truncation with its energy account. Each null
is held to a planted instance in the same run (a wrong character set in A, two disjoint copies in B, an untempered
prism in C, a set not closed under `−k` and a non-real field in D, the field `x' = x²` in E).
