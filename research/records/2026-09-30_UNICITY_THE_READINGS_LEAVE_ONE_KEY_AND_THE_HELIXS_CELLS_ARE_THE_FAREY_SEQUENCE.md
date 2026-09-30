# Unicity: the readings leave one key, and the helix's cells are the Farey sequence

**Date.** September 30. **Issues.** #62, #63, #73. **Grade.** Each claim is graded where it is
made. [formal-checked] is Lean `Foundation/Unicity` over `Compression/Landmark/Context/Population`,
[proved-standard] cites the literature, [interpretation] is a reading the framework does not prove.

**Occasion.** Brandon asked: "How many times does an organism that has never witnessed a
classification of motion need to observe the motion before it can refine an internal model of how
the motion reproduces? … this is the same kind of question you'd ask if you wanted to reverse
engineer a dead language or decrypt anything. It's just another way of asking 'when can you hear the
music?'" Shannon named the answer the **unicity distance** (*Communication Theory of Secrecy
Systems*, 1949). Brandon made it a keystone: "raise that into a formal derivation in Holonics …
probably pairs well with surprise and cross-entropy … we have key insights about division/inversion
and modulo, and the 'by how much each observation constrains' is perfect for our causal calculus …
The 'gap between two counts' points straight at RH."

Three derivers take the question independently, and their derivations are reconciled where they
intersect: GPT-6 Astra, a Sonnet 5.5 derivation over abstract computational models (resonance,
affinity, balance, transport; mathematics only, read from operations and not from any application),
and this record (Opus). §6 records the intersections with the Sonnet derivation. Astra's are added
when its derivation returns.

**Prior work this builds on.**
- The [September 25 hearing record](2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md):
  hearing a string of holes multiplies by ζ, listening divides by it (Möbius inversion);
  Lapidus–Maier's `RH ⇔ (ISP)_D` for every `D ≠ ½` (atlas `rh.inverse-spectral-fractal-string`);
  "heard, not listened" typed at the HNN's deposit.
- The egg population's survivors and the mixture's likelihood telescope (Lean `Population`:
  `survivor_code`, `survivors_product`, `population_mixture`).
- The relevance kernel (Lean `Foundation/CausalRelevance`, atlas `info.relevance-kernel`), the
  Bombe's publication rule in `hnn::keys` (publish when the fibre is one gauge orbit; Lean
  `Compression/Core/Keys.fibre_eq_orbit`, under gauge reachability and boundary pinning), observed-
  prefix agreement and next-step separation (`Computation/NavigatorObservationScope`), and the pair
  contact's Farey lock address. These are scoped identification laws, not a universal encounter
  count, and this record stays within their scopes.

## 1. Unicity in the objects

[definition] A **key** is a navigator's initial configuration (its gauge quotiented). A **reading**
is a receiver's face of the passage at its grain, one a tick. The **survivors** `S_t` are the keys
whose readings agree with every reading received before `t` (`Population.survivors`). **Unicity** is
reached when the survivors are one class of the admitted-future quotient. The unicity distance `n*`
is the first tick at which that holds.

[proved-derived; formal-checked, `Population.survivor_code`] **The surprise a reading carries is the
log of a ratio of two counts.** Under the uniform mixture, the face of the true reading at `t` is
`#S_(t+1)/#S_t`, the path's product is `#S_n/|K|`, and the code is `log₂|K| − log₂ #S_n`. The
per-reading constraint is the ratio `R_t = #S_t/#S_(t+1)`, and its log is the surprise crossing the
receiver's section. This is the governing law "loss is the log of a ratio" read on counts: pathwise
and exact, with no expectation taken. Under any prior the mixture codes within `−log₂ π(key)` of the
true key (`population_mixture`): the realized surprise an ignorant receiver pays above the keyed one
is at most `−log₂ π(key)`, the true key's own description under the prior. It is not bounded by the
key entropy `H(K)` in general. `H(K)` bounds it only in expectation, under a declared joint
probability model of keys and readings (correction, Codex review).

[proved-derived; formal-checked, `Unicity.survivors_card_succ_eq_iff`] **A null reading.** `R_t = 1`
(surprise zero) exactly when every survivor makes the true reading. A reading constrains only
through its component that separates survivors. This is the relevance kernel restricted to the
survivors.

[proved-derived; formal-checked, `Unicity.eventually_survivors_iff`, `eventually_survivors_eq_class`]
**The class that never collapses.** For a finite key set, from some tick on the survivors are exactly
the keys indistinguishable from the true one, and the code stays `log₂|K| − log₂|class|` for ever.
Identification is only ever up to the admitted-future quotient, which is retention's quotient
(`Foundation/Standing`) seen from the key's side. More readings of the same kind never go below it.

[proved-derived; formal-checked, `Unicity.classes_le_pow_of_separating`,
`clog_classes_le_of_separating`] **The pigeonhole count.** If `n` readings over an alphabet `C`
separate every two classes, the class count is at most `|C|ⁿ`, so `n ≥ clog_|C|(classes)`.

[proved-standard] **Shannon's form is a statistical crossover, not a certificate.** In the
random-cipher model with `M` equally likely keys, the expected number of spurious keys after `n`
readings is `(M − 1)·2^(−nD)`, with `D = log₂|A| − h` the redundancy per reading (`D(P‖U)`). At
`nD = log₂ M` the expected number of survivors is `2 − 1/M`, not one: `n* = H(K)/D` marks where the
expected spurious count crosses one, and it certifies no singleton. The law depends on the source,
the key law and their dependence. The pathwise laws above certify a class exactly and need no
random-cipher model.

## 2. Residues: the constraint is a divisor of the modulus

[proved-derived; formal-checked, `Unicity.kernelChain`, `consistent_iff_sub_mem`,
`card_eq_fibre_mul_prod`, `relIndex_dvd_card_reading`, `index_kernelChain_le_pow`, `clog_index_le`]
Keys in an additive group `X`, read by additive maps into `V` (a residue reading, a linear face):
- the survivors after `n` readings are a coset `key + ker_n` of the kernel chain;
- the key count factors exactly, `|X| = |ker_n| · ∏_(t<n) [ker_t : ker_(t+1)]` (Lagrange along the
  chain): whole readings multiply, and the surviving fibre is the remainder;
- each ratio `[ker_t : ker_(t+1)]` divides `|V|`, so the surprise of a residue reading comes in quanta
  `log d` with `d` a divisor of the modulus;
- reaching a fibre of index `I` takes at least `clog_|V| I` readings.

This is the division-with-remainder form of unicity: `log|X| = Σ log R_t + log|ker_n|` without a
logarithm. [proved-standard] For coprime moduli the ratios of the two residue readings multiply to
the full modulus (the Chinese remainder theorem), so readings on coprime rings reach unicity at
once. On shared factors they overlap.

## 3. The helix: its unicity cells are the Farey sequence

[proved-derived; formal-checked, `Unicity.floor_ne_iff_exists_between`, `readings_agree_iff`] A
rotation key `α` read by its whole windings `⌊nα⌋` (the helix: circle and carry; the reading is the
carry) is separated from `β ≥ α` at reading `n` exactly when a fraction `k/n` lies in `(α, β]`.
After `N` readings the survivors of a key are exactly its **Farey cell of order `N`**: the partition
of the keys by all fractions of denominator at most `N`.

[proved-derived; formal-checked, `rational_keys_separated`, `farey_neighbours_agree_below`,
`farey_neighbours_separate_at`] **A rational key is heard when its own cycle closes.** Two keys are
separated at the least denominator among the fractions in the half-open interval between them. For
Farey neighbours `p/q < p'/q'` (`p'q − pq' = 1`) every `N < q'` readings agree, and the reading at
`q'` separates them. There `q'·(p'/q')` is the integer `p'` and the neighbour below falls short of
it. The helix hears a periodic key at its own period: completeness, not duration (the cycle's law).
Scope: this is unicity within a finite key family, the rationals of height at most `Q`, where every
two keys are separated within `Q` readings. A real key's Farey cell has positive measure at every
`N` and never shrinks to a point: a continuous key never becomes a singleton, and a positive-measure
survivor set is not a located key.

[proved-standard] The `N`-th reading adds, in each unit interval, the `φ(N)` reduced fractions of
denominator `N` (Euler's totient). After `N` readings a unit interval of keys holds
`Φ(N) = Σ_(n≤N) φ(n)` cells, and `Φ(N) = 3N²/π² + O(N log N)` (Mertens, 1874). The cells are
unequal: neighbours `p/q < p'/q'` bound a cell of width `1/(qq')`. [proved-derived, from those
widths; Lean owed] A zero-entropy navigator is heard slowly. The information its readings carry about the key grows only as the log of the cell count,
twice `log N` plus a bounded term, where a positive-entropy source pays a constant `D` a reading.
Shannon's `H(K)/D` has no finite value here: the key is continuous and the readings are nearly
redundant.

## 4. RH is a gap between two counts

1. [proved-standard] **Franel–Landau** (1924). Let `f_1 < … < f_Φ` be the Farey fractions of order
   `N` in `(0, 1]` and `δ_v = f_v − v/Φ(N)`. RH holds if and only if `Σ_v |δ_v| = O(N^(1/2+ε))` for
   every `ε > 0` (Landau), and if and only if `Σ_v δ_v² = O(N^(−1+ε))` (Franel).
2. [proved-derived, by §3 composed with 1] **RH is a statement about the helix's unicity.** The
   `f_v` are exactly the cuts of the helix's unicity cells after `N` readings. `v` counts the cells
   below the key `f_v`, and `Φ(N)·f_v` is the count the uniform density predicts. RH holds if and
   only if the gap between these two counts is `O(N^(1/2+ε))` in `L¹` over the cuts: the helix
   hears every region of keys at the fairest rate square-root cancellation allows. Lean owes the
   composition (§7).
3. [proved-standard] **The prime count.** von Koch (1901): RH holds if and only if
   `π(x) − Li(x) = O(√x log x)`: the actual count against the count the density receiver predicts.
   Equivalently `M(x) = Σ_(n≤x) μ(n) = O(x^(1/2+ε))`. [interpretation; a restatement, not
   evidence] Each actual zero `ρ = β + iγ` of multiplicity `m_ρ` enters `ψ(x)` with coefficient
   `−m_ρ/ρ`, and `x^ρ = x^β e^(iγ log x)` is, on the clock `log x`, a Swing with boost rate `β` and
   turn rate `γ` (`Geometry/Motion.complex_rate_split`). After the `√x` normalization its boost is
   `β − ½`. RH is exactly the statement that every normalized boost is zero, so reading every mode
   as a pure turn already assumes RH (correction, Codex review). A zero with `β > ½` would be a
   mode louder than the square-root floor. The `π − Li` receiver needs, beyond `ψ`, the prime powers
   removed and partial summation. The repository's actual-source owners
   (`Zeta/ExplicitFormulaFiniteHeight.explicit_formula_finite_height`, with entire test weights,
   zero-free rectangle boundaries, multiplicities and both horizontal edges;
   `SpectralKernelDecay.explicit_formula_limit_weil` and
   `PrimeSideConverges.explicit_formula_classical_weil`, with smooth compactly supported kernels)
   do not directly prove an unsmoothed `π − Li` receiver.
4. [proved-standard] **Hearing and nullity** (September 25). Lapidus–Maier: the geometry of a
   fractal string of dimension `D` is heard from its spectrum exactly when ζ has no zero on
   `Re s = D`. So RH is equivalent to the hearing being unique at every dimension but ½. The zeros are
   the inaudible dimensions: a unicity failure at the spectral receiver.
5. [proved-standard] **Plural fibres of the zeta receiver.** Gassmann (1926), Perlis (1977):
   non-isomorphic number fields can share a Dedekind zeta function (arithmetic equivalence). Sunada
   (1985) turned the same group-theoretic triple into isospectral non-isometric manifolds, and Gordon,
   Webb and Wolpert (1992) into isospectral plane domains, answering Kac (1966, "Can one hear the shape
   of a drum?") in the negative. A receiver that reads fixed-point counts (the splitting of primes,
   closed geodesics, a trace formula) cannot separate Gassmann-equivalent keys. Its unicity is infinite
   on that fibre, and only a different kind of reading closes it.
6. [proved-standard; interpretation for the reading] **The parity problem** (Selberg): at a
   declared level of distribution and error budget, sieve inputs cannot distinguish sets that differ
   by the parity of their prime-factor count, so that sieve receiver cannot locate the Liouville
   direction `λ(n)`. This is scoped to the sieve receiver, its level and its error terms. It does not
   establish that `λ` lies in `futureCollapsed` under every admitted transport. Chowla's conjecture and Sarnak's Möbius disjointness
   conjecture (μ uncorrelated with every zero-entropy sequence) say, in this language, that no
   zero-entropy navigator locates μ. Both are conjectures.
7. **A correction to the brief sent to Astra.** For a deterministic helix, the Farey keys of height
   `Q` are separated by `Q` readings (§3), not `Q²`. The large sieve's `N − 1 + Q²` concerns another
   receiver: detecting energy at Farey frequencies in an arbitrary sequence, with the amplitudes
   unknown. The upper energy inequality and the Farey separation do not by themselves give
   injectivity or a noise-stable inverse, so a uniqueness claim there needs the actual observation
   map and a lower bound (Codex review). Whether the `√x` level of Bombieri–Vinogradov is exactly that receiver's unicity threshold
   is left open for Astra.

## 5. The HNN: hearing against listening

[definition; agent-inferred] **The two counts.** For a known-truth terrain and a declared key family:
- `n*_terrain`: the readings after which the family's survivors are one class. The terrain computes it
  exactly. It is a measurement, never a receiver (the governing law "No catered machinery").
- `n*_machine`: the readings the machine takes in before its release locks the rule on fresh
  confirmation.

Their ratio measures the learner, in any modality. The uniform mixture over the declared family is
the ideal listener. Its surprise curve `Σ log R_t` on the machine's own passage is the reference
against which the machine's own surprise curve is read.

[measured] **Order-2.** The family "lag `ℓ ≤ 40`, map `f` of `ℤ/4`" has
`40 · 4⁴ = 10240 = 2¹¹·5` keys, and `clog₄ 10240 = 7` (`Unicity.order2_family_count`,
`order2_unicity_lower`). One request shows 8 rule steps. The machine read 128 training requests
(1,024 rule steps) and released 0 whole sections of 128 on fresh confirmation (the
modulus loop's confirmation, September 30, with the transport founded off one).
`n*_machine` exceeds 1,024 readings, against a family whose count can pin the key in 7.

[interpretation; the experiment named] **The mechanism, in the September 25 record's terms: the
machine hears and does not listen.** The comparison's covector reaches the locus (heard). The
certified step moves `E` by `[2⁻⁹, 2⁻⁸)` a deposit while a lock needs `2⁷`–`2⁹` times that (the
[diagnosis](2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
§3). The intersection §6.4 names a second cause: the comparison is read away from resonance.
Gradient descent on a 600-entry port drifts, while elimination of survivors (the Bombe's loop
closure, `hnn::keys`) reaches unicity at the data's rate. The next learning loop reads both counts,
and the per-move key information, on the same passage.

## 6. Intersections with the abstract-model derivation (Sonnet 5.5)

That derivation extracted six abstract objects: a pencil of modes built from rank-one contact terms;
a two-state lock with exchange polynomial `Π = 1 + a/K`; a dissipative chain of checks; balance and
constraint systems; transport across a section (the Schur complement); and Farey rate locks.
Its statements carry their own grades. Its classical citations were given from memory and are
checked before any enters the atlas.

1. **One law in three charts: the fibre that never closes is the relevance kernel.** Its linear
   state chart: `d` readings of one receiver locate a state, where `d` is the Krylov dimension under
   the admitted transports, and the fibre is `x + K_fut` of dimension `n − d` (Kalman observability,
   [proved-standard]). This record's finite chart is `eventually_survivors_eq_class`, and its residue
   chart is the kernel chain's coset. Both derivations reach the same corollary: a fibre closes only
   by a different kind of reading (a probe that changes the constitution, a second section, an
   oriented reading), never by more of the same. That is the parametron's dormancy ("a silent mode
   reopens when the constitution changes") and lesson 9 in mathematical form: a refusal changes the
   receiver family, never the limit.
2. **The residue constraint, exactly.** This record proves that each reading's ratio divides the
   modulus. The Sonnet derivation gives its exact value for one linear reading `r·x mod N` on
   `(ℤ/N)ⁿ`: `N/g`, with `g = gcd(r, N)` the nonunit fibre that repeating the reading never closes.
   Together: the surprise of a residue reading is exactly `log(N/g)`, and the fibre `g` is the
   inversion's nonunit fibre (the ratio object).
3. **Two receivers of one helix, a factor of `q` apart.** Its rate-lock law reads the *slip*, the
   relative phase of two rates, at a grain `ε`. Farey neighbours then separate after `⌈ε·qq'⌉`
   readings. This record's carry receiver (the whole windings) separates them at `q'`. The two laws
   agree, and they measure different receivers. The slip accumulates `1/(qq')` a step, while the
   carry reads the key's own cycle closing at its period. [interpretation] Reading the carry (loop
   closure, the Bombe's check) hears a periodic key a factor `q` sooner than reading the relative
   phase alone.
4. **Resonance maximizes what a reading carries.** For the lock `θ = a/(a+K)`, one read's Fisher
   information about `ln K` is `θ(1−θ)`, maximal (`1/4`) at the lock's own resonance `a = K` and
   wasted by the factor `4θ(1−θ)` elsewhere ([proved-derived] there). [interpretation, testable] The
   diagnosis found 10,179 of 10,240 bank members past threshold, where the lock is already decided;
   if its face reads as `θ`, `θ(1−θ)` is small there and each comparison says little about the key. A second candidate cause of `n*_machine ≫
   n*_terrain`: the release's comparison is read far from resonance. The next loop measures the
   comparison's per-reading information at its operating point.
5. **The reader of a key is division with remainder.** Its law identification (`2d` moments, the
   Stieltjes continued fraction, Euclid on polynomials) and this record's helix (the Farey cell,
   whose neighbours satisfy the convergents' unimodularity, atlas `coupling.convergent-determinant`)
   are one structure. A key is read by a continued fraction: each partial quotient is one division
   with remainder, and the reading terminates exactly for a finite-rank or rational key.
   [interpretation] The observation count and the division count differ: `q` readings of a passive
   helix against about `log q` partial quotients for a reader that divides.
6. **Specificity beyond one comparison is paid in dissipation.** A chain of checks at equilibrium
   collapses to its end-to-end ratio. Each driven, irreversible check multiplies the discrimination,
   at activations `C(D) = (η − 1)/(η − D)` for a stage discrimination `D` below its cap `η`
   ([proved-derived] there). Both derivations read the log-ratios as adding into one surprise.
   [interpretation] The HNN's deposition is its irreversible step. Unicity reached in few readings is
   bought in dissipated work, never free.
7. **A section forgets placement.** Its transport law: a boundary response determines the interior
   only up to star–mesh moves. The September 25 record's listening recovers a string's lengths and
   not where the holes were placed. Both say that a receiver at a section recovers a spectrum or
   multiset, and placement needs a reading that carries phase: spectral placement (lesson 11).

## 7. Owed (#62)

- `Foundation/Unicity`: the relevance kernel as the limit of the kernel chain when the readings
  enumerate the admitted future (`futureCollapsed = ⨅_n ker_n`); the helix's cell count `Φ(N)` and
  the `φ(N)` new cuts of the `N`-th reading; the survivors of a residue reading `r·x mod N` counted
  exactly, `N/gcd(r, N)`.
- `Zeta`: Franel–Landau's equivalence stated with its hypotheses, and its composition with
  `readings_agree_iff` (RH ⇔ the helix's unicity cells are square-root fair).
- The expected (Shannon) form: the key-equivocation chain rule
  `H(K|Xⁿ) = H(K) − Σ I(K; X_t|X_<t)` with `I` the ignorant receiver's cross-entropy above the keyed
  one, and the random-cipher bound on spurious keys.
- Arithmetic equivalence and its isospectral twin, stated as fibres of the zeta and spectral
  receivers.
