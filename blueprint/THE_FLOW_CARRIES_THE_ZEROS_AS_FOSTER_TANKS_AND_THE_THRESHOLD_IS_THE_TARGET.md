# The flow carries the zeros as Foster tanks, and the threshold is the target

**Founded:** 2026-09-03, by Brandon's direct instruction: *"I am directing that campaign."*  
**Authority:** this is a subordinate contract. [`THE_ROADMAP.md`](THE_ROADMAP.md) alone orders
construction and [`../CONSTRUCTION_STATE.md`](../CONSTRUCTION_STATE.md) alone records position;
this file composes the phases the roadmap lists under the RH line and schedules nothing by
itself.  
**Truth status:** `definition` for the contract; every returned phase carries its own grade under
[`../canon/EPISTEMIC_GRADES.md`](../canon/EPISTEMIC_GRADES.md).  
**Occasion:** the two records of 2026-09-03,
[`the flow reading`](../research/records/2026-09-03_THE_SEAMS_ARE_LOCAL_OPTIMA_OF_THE_THREAD_ENERGY_THE_PRIMES_ARE_THE_MISSING_HALF_AND_THE_FLOW_BINDS_THE_INTEGER_EVENTS.md)
and
[`the compound statement`](../research/records/2026-09-03_THE_SEAM_IS_THE_GEOMETRIC_MEAN_OF_THE_DUAL_CHARTS_THE_KERNEL_CHAINS_AND_ROTATES_AND_THE_SQUARE_TELESCOPES_AGAINST_THE_CHAIN.md),
and Brandon's question that followed them: *"Why not move with the Hadamard expansion? Would our
goal not be to prove `Λ = 0`?"*

---

## 0. The target, stated once

[definition] The de Bruijn--Newman threshold of the completed zeta is `Λ`. Rodgers and Tao proved
`Λ ≥ 0`; de Bruijn and Newman proved `RH ⟺ Λ ≤ 0`. The target of this campaign is `Λ = 0`, which is
the Riemann Hypothesis in the flow's coordinate. Every phase below returns an exact owner on the
way to that statement or returns the first exact missing inequality with its falsifier. No phase
may return a structure field, hypothesis, or certificate that assumes the target, and no
conditional bridge may be described as the target reached
([`../AGENTS.md`](../AGENTS.md), construction grade; the fleet document's return contract, adopted
here as the primary line's).

[definition] The campaign's object is the Foster form. Hadamard's product for `Ξ(z) = ξ(½ + z)`,
paired by the functional equation, gives

```text
Ξ′(z)/Ξ(z) = Σ_pairs 2z / (z² − ρ′²),      ρ′ = ρ − ½.
```

Each term is the impedance of a parallel LC tank with capacitance `½` and inductance `−2/ρ′²`;
under RH the inductance is `2/γ²` and the tank resonates at `(LC)^{−1/2} = γ`. RH is Foster's
reactance theorem for this one function: every tank has positive inductance. The flow moves the
tanks by the threads `2/(z_j − z_k)`. The campaign builds the tanks exactly, then the flow on
them, then the threshold.

[definition] The standing this campaign composes, all under
`soma/formal/elementary-holonics/ElementaryHolonics/RH/`: the disc factorization
(`ZeroFactorizationExists`), Landau's lemma for `ξ` with its explicit remainder
(`LogDerivativeRemainder`, `JensenCountsTheComb`, `LandauLemma`, `LandauXi`, `LandauAtHeight`),
the order-one envelope and Jensen counting (`RiemannXiGrowth`, `ZeroCounting`,
`RiemannXiZeroCounting`), the entire flow (`HeatFlowEntire`, `HeatEquationEntire`,
`ZeroDynamicsEntire`, `SimpleZeroPersists`, `SimpleZeroCurve`, `RectangleCountStable`), the
polynomial flow and its threshold (`HeatFlowOfPolynomials`, `HeatSemigroup`, `PolyaStep`,
`ForwardPreservation`, `PairDescent`, `DeBruijnNewmanPolynomial`, `PhaseFlowLedger`), the
integer-event owners (`HeatFlowBinding`, `HeatFlowStackedSeam`), the explicit formula
(`ExplicitFormulaReceiver`, `ExplicitFormulaLimit`, `ArchimedeanReceiver`), the Weil owners
(`WeilPositivity`, `ZeroComb`, `ZeroCombPairing`, `GlobalWeilFinishLine`), and the anchor
`Millennium/Seam.lean` against Mathlib's `RiemannHypothesis`. The coordinate correction of
2026-09-02 governs every transport between repository time `u` and standard time `t = −4u`.

---

## 1. The ordered phases

[definition] The order is fixed. A phase passes on its declared exact artifact and grade, under
the 180-second process boundary, with `#print axioms` free of `sorryAx` and new axioms.

### FT0 — the paired finite Foster form with Landau's remainder

Return, on a centred disc, the log-derivative of `ξ` as the sum over reflection pairs of zeros
in the disc of the tank impedances `2(z − ½)/((z − ½)² − ρ′²)`, plus Landau's remainder with the
bound the tree already proves; the tank data as definitions (`capacitance = ½`,
`inductance ρ′ = −2/ρ′²`, `resonance`); and the elementary equivalence that every tank of the disc
has real positive inductance iff every zero of the disc lies on the seam.

**Pass FT0:** the theorem builds on `exists_zeroFactorization_riemannXi_jensen` and
`norm_logDeriv_le` without a new axiom; the pairing uses `ZeroComb`'s reflection symmetry of the
divisor; the equivalence is proved.  
**Falsifier:** a disc and a point on which the paired sum plus the remainder bound fails against
the directly computed `ξ′/ξ`.

### FT1 — the centre value, the count, and the exponent of convergence

Return first the centre value `riemannXi (½) ≠ 0`, carried by FT0 and by `OffLineJensen` as a
hypothesis, discharged by an enclosure of the theta tail or of the completed zeta at `½`; then
`N(R) ≤ C · R · log R` for the zeros of `ξ` in the centred disc of radius `R`, from the order-one
envelope through Jensen; and the summability `Σ_ρ |ρ′|^{−2} < ∞` of the paired inverse squares.

**Pass FT1:** all three theorems formal-checked; the constant is exhibited, not existential; the
FT0 existence theorems are restated without the carried hypothesis.  
**Falsifier:** a radius at which the exhibited constant is beaten by the divisor mass the tree
already computes.

### FT2 — the paired canonical product

Return the product `P(z) = Π_{i} (1 − ((z − ½)/(u_i − ½))²)` over the zeros of `ξ` repeated by
multiplicity, locally uniformly convergent on every centred disc by FT1: `P` entire, `P`
reflection symmetric, the zero set of `P` equal to the zero set of `ξ`, and off the zeros
`P′/P = Σ_u m_u · 2(z − ½)/((z − ½)² − (u − ½)²)`, the Foster series over all zeros. Each pair
contributes twice, so `P` is the paired product squared; FT3 compares it with `ξ²`.
*Corrected in place 2026-09-03:* the envelope of `P` first asked for here is not needed by FT3's
route and is withdrawn; the order `2 m_u` of `P` at each zero is established in FT3 where it is used.

**Pass FT2:** `P` entire, `P` symmetric, zero sets equal, the log-derivative series proved.  
**Falsifier:** a disc on which the zero set of `P` and the zero set of `ξ` differ.

### FT3 — Hadamard, and the entire-face thread law

Return `ξ² = ξ(½)² · P` by the finite/tail split of `P` on every centred disc (the finite part is
the square of the symmetric factorization's polynomial up to a constant, the tail nonvanishing),
so that `ξ²/P` is entire and nonvanishing; its log-derivative `2ξ′/ξ − P′/P` is bounded by
`O(log(|z| + 2))` through Landau's remainder (FT0) and the tail of the Foster series (FT1), hence
constant by Cauchy's estimate, hence zero by the reflection symmetry. Hence the full Foster form
as a convergent series, `ξ′/ξ = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²)`, and the principal-value
comb flux at the entire face. Discharge the port `PhaseFlowLedger.RodgersTaoZeroDynamics` for
`heatE t ξ` at every `t` for which `HeatFlowEntire` returns an entire function of the class, the
same argument running on `heatE t ξ` once its Landau bound and count are returned.

*Corrected in place 2026-09-03:* the argument on `heatE t ξ` needs the centre value
`heatE t ξ (½) ≠ 0` at every `t` (Jensen's count and the paired product both require it), and the
centre value at every time is a property of the kernel, `∫ e^{tu²} Φ(u) du` with a positive
integrand, which is FT4's artifact. FT3 therefore passes on `ξ`: `ξ² = ξ(½)² P`, the full Foster
form, the principal-value comb flux at every simple zero of `ξ`, and the port amended to discs
centred at `½` on `C¹` curves with its field at `t = 0` a theorem. The discharge for the family
`heatE t ξ` is FT4 (i), the Foster class.

**Pass FT3:** `FosterHadamard.sq_eq_centre_mul_P`, `FosterHadamard.foster_form`, and
`CombFlux.flux_riemannXi` are theorems; `RodgersTaoZeroDynamics` states the law at centre `½` and
`CombFlux.flux_time_zero` is its field at `t = 0`.  
**Falsifier:** a simple zero of `ξ` at which the finite comb flux on a declared truncation
disagrees with `ξ″/ξ′`, or a point at which `ξ² − ξ(½)² P` is nonzero.

### FT4 — the flow at the entire face and the threshold defined

Return first (i) the Foster class: FT0--FT3 generalized over symmetric entire functions of finite
order below two with a centre value, so that the Hadamard identity, the Foster form, and the comb
flux hold for every member; then the kernel `Φ` with its cosine-transform identity to `heatE` in
the corrected coordinate, whose positive integrand returns the centre value `heatE t ξ (½) ≠ 0`
at every `t` and, with the majorant's growth envelope, places `heatE t ξ` in the class, discharging
`RodgersTaoZeroDynamics (fun t => heatE t riemannXi)` so that the docstring of
`ZeroDynamicsEntire` no longer names its second half open; then the entire-face forward
preservation (the flow never creates a pair), the real-zero times as a nonempty closed up-set,
`Λ_DN` as their infimum, and `RH ⟺ Λ_DN ≤ 0` against Mathlib's `RiemannHypothesis` through
`Millennium/Seam.lean`. This absorbs the labels `RH6`--`RH9` of the fleet document as the primary
line's own.

*Returned 2026-09-03 (i)–(ii):* the Foster class (`FosterClassLandau` … `FosterClassFlux`),
`ξ` and every `heatE t ξ` as members (`FosterClassHeat`, `FosterClassHeatFlow`), the kernel
`Φ(u) = e^{u/2} Ψ(e^{2u})` with `Φ > 0`, `Φ` even, the representation
`ξ(s) = ∫ e^{(s − ½)u} Φ(u) du`, the flow identity
`heatE t ξ (z) = ∫ e^{−t u²} e^{(z − ½)u} Φ(u) du` in the corrected coordinate, the centre value at
every time, and the port `RodgersTaoZeroDynamics (fun t => heatE t ξ)` as a theorem
(`HeatKernelPhi`); receipt
[`the FT4 (i)–(ii) record`](../research/records/2026-09-03_FT4_THE_FOSTER_CLASS_HOLDS_EVERY_FLOWED_XI_THE_KERNEL_IS_POSITIVE_AND_THE_PORT_IS_A_THEOREM.md).
*Returned 2026-09-03 (iii)–(v):* the semigroup at the entire face (`KernelFlow`), Hurwitz on a
rectangle (`HurwitzLine`), the seam polynomials and their Euler iterates (`PolyaLine`), the
seam-zeroed members as locally uniform limits of seam polynomials (`LineApproximation`), the Euler
iterates converging to the flow (`EulerIterates`), and, in the standard coordinate `τ = −t`, the
seam times `{τ | ∀ z, heatE (−τ) ξ z = 0 → Re z = ½}` as a **closed up-set** with
`0 ∈ seamTimes ↔ RH`, `Λ_DN := sInf seamTimes`, and
**`seamTimes.Nonempty → (RH ⟺ Λ_DN ≤ 0)`** (`RealZeroTimes`, `LinePreservation`); receipt
[`the FT4 (iii)–(v) record`](../research/records/2026-09-03_FT4_THE_FLOW_NEVER_CREATES_A_PAIR_THE_SEAM_TIMES_ARE_A_CLOSED_UP_SET_AND_RH_IS_THE_THRESHOLD_GIVEN_ONE_SEAM_TIME.md).
*Obstruction named 2026-09-03:* de Bruijn's bound "from `PairDescent` transported to the entire
face" does not transport as written, since at the entire face a highest nonreal pair need not
exist; the nonemptiness of the seam times (de Bruijn's theorem, `τ ≥ ½`) is FT4's remaining item
and the first exact missing item of the line, carried as the explicit hypothesis of the
equivalence.

**Pass FT4:** the port is a theorem; the equivalence is formal-checked with `Λ_DN` defined from
the actual `Φ`, never from a polynomial shortcut; de Bruijn's `Λ_DN ≤ ½` returns from
`PairDescent` transported to the entire face.  
**Falsifier:** a time in the real-zero set below which a real-zero time exists, contradicting the
up-set law.

### FT5 — the time-zero coupling: the flowed explicit formula

Return the explicit formula of `heatE t ξ` for every `t`: its zero side is the divisor of
`heatE t ξ`, its integer-event side carries the weights `n^{−1/2} · e^{t(log n)²} · n^{−2tv}` of
`HeatFlowBinding` under the same Gamma response, and the two sides agree in the limit of
`ExplicitFormulaLimit`. This is the seam where the Euler side meets the flow, and it is the
campaign's new mathematics: at `t = 0` the integer side is the von Mangoldt comb; at `t ≠ 0` it is
the bound comb, and the binding defect of every composite is exhibited in the receiver.

**Pass FT5:** the flowed explicit formula is a theorem for the test class of
`ExplicitFormulaReceiver`, and its `t = 0` specialization is definitionally the standing one.  
**Falsifier:** a test function and a time at which the zero side of `heatE t ξ` and the bound
integer side differ by more than the horizontal-edge remainder.

### FT6 — the threshold

Return `Λ_DN ≥ 0` by the Rodgers--Tao argument (the `RT0`--`RT6` labels of the fleet document
adopted as the primary line's), and then the target. The target's exact form under this contract:
a pair of `ξ` at time zero has height `y₀ > 0`; forward preservation and pair descent land it at a
time `τ` with `0 < τ ≤ y₀²/2`; along `[0, τ]` FT5 gives the flowed explicit formula with the
binding defect active; FT6 must return the inequality the bound integer side violates that the
free one satisfies, or the first exact missing inequality with its falsifier. The prohibition of
§0 binds: the target may not be assumed in any field, hypothesis, or certificate.

**Pass FT6:** `Λ_DN = 0` formal-checked against `RH.Statement`, or the named missing inequality
with a falsifier that can fire, deposited as the phase's return.  
**Falsifier:** for the target, the null falsifier of the conjecture itself; for the missing
inequality, a construction in the class of FT2 with a pair at time zero satisfying it.

---

## 2. What the campaign forbids

1. No phase returns a structure whose field is the target or an implication to it.
2. No numerical enclosure of `Λ_DN` substitutes for a theorem; the polynomial thresholds of the
   morning record are witnesses, not phases.
3. No coordinate transport between `heatE` time and standard time without the factor and sign of
   the 2026-09-02 correction.
4. No language, parser, or template enters the interior; every owner is Lean under the root
   umbrella, and drivers are observers.
5. No estimate of duration is a phase artifact. A phase returns or names its obstruction.

## 3. Relation to the engine frontier

[definition] Brandon directed this campaign on 2026-09-03 while `SKE4` is the engine frontier.
The roadmap carries this campaign as the RH line's ordered position beside the engine's, as it
has carried the RH line independently since 2026-09-02. The two lines share no owner and no
process; each advances on its own gate.
