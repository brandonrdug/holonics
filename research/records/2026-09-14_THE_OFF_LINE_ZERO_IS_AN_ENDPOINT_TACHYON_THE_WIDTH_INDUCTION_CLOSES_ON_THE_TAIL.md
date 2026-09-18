# The off-line zero is an endpoint tachyon, and the width induction closes on the tail

**Date:** 2026-09-14
**Provenance:** Brandon, same-day direct discussion. The requested shape, in his words:
*"a counterexample proof against the zeroes being off of the critical strip … if there was
literally any zero off of the critical line, the flux of everything else would be deterministically
different"*, *"like matter moving at the speed of light … think tachyon"*, and for the collision
branch: *"a split from one timeline to another, where the 'another' is a child of the previous
continuity."* Requested disposition: deposit the idea as a research note, not as a construction.

**Truth status:** the individual claims carry the grades below. The assembled proof architecture is
`interpretation` with named maps, a first derivation target and falsifiers. **No new global RH bound
is claimed; `Λ_DN ≤ 0` remains open.**

---

## 1 · The proposed proof shape

[interpretation] Assume one zero off the line at `1/2 + d + iy`, `d > 0`, taken rightmost. Do not
seek a contradiction with an external prime law; seek the failure of **self-consistency of the
divisor population**. The claim to establish is causal: the other zeros' flux would have to differ
deterministically, and no lawful continuation of the whole population can supply the difference.
The collision where zeros meet is not a second universe but a **child continuity** of the same
owner — a chart transition at the degeneracy, with the divisor and its multiplicities retained.

## 2 · Why a flux contradiction is an equivalence, not a contradiction

[proved-standard] The explicit formula

```text
ψ(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½ log(1−x⁻²)
```

makes every zero contribute `x^{1/2±d} e^{iy log x}`. An off-line zero forces a deterministic
`x^d`-scale distortion of the prime flux's error. This is exact, and it is precisely why the route
cannot close by itself: the distortion is *equivalent* to the zero's existence, and the prime flux
is the object under study, not an independent referee. The available external facts are asymptotic:
the classical zero-free region (Vinogradov–Korobov) and numerical verification to finite height
already exclude zeros too near `Re(s) = 1`; the open part is uniformity in height.

[proved-standard] Newman's equivalence: RH ⟺ `Λ_DN ≤ 0`. Rodgers–Tao (Forum of Mathematics Pi,
2020; arXiv:1801.05914) prove `Λ_DN ≥ 0`. Hence **RH ⟺ `Λ_DN = 0`**: the configuration is exactly
marginal, and no proof may use a strict margin. Any induction must close at the boundary itself.

## 3 · The rigid contradiction lives in the divisor population

[proved-derived; formal-checked] The existing owners already supply the local identities:
`PairPopulation.reflect` and `TransverseCurrentBound.reflected_pair_center` fix the normal centre;
`Balance` proves functional reflection and conjugation coincide exactly on the critical line; at
`d > 0` the partner contributes the exact baseline normal current `−1/d`, the opposite member
contributes `d/(d²+y²)`, and `weightedSurplus_nonneg` retains each admitted zero's nonnegative
inward term under the rightmost ordering. The width law and its integration theorem are in
[the centered-current construction](../../docs/RH_CENTERED_CURRENT_UPPER_BOUND.md):

```text
d' ≤ −1/d − J_R + ε_R,        (d²)' ≤ −2 − 2 d (J_R − ε_R),
d(T)² + 2 (1 + a) T ≤ d(0)²   whenever   d (J_R − ε_R) ≥ a ≥ 0,
```

with `ε_R` instantiated for the actual source through `FiniteZeroCurrent`,
`FosterClassFlux.comb'_sub_le`, `heatE_norm_negative_zero_velocity_sub_comb_le` and
`re_negative_zero_velocity_le`. `J_R ≥ 0` is unconditional for the admitted finite population:
every admitted zero is a Lenz current, inward.

[proved-derived] **The reduction this note deposits:** since `−1/d < 0` and `J_R ≥ 0`, no admitted
zero can push another outward. The only term that can is the exterior remainder `T_R`, and the
Foster bound gives `|T_R| ≤ ε_R`. Therefore the rigid contradiction has exactly one honest
location — a **uniform inward orientation (or domination) of the tail** for the actual ξ family at
all heights, with admissible continuation through multiple-zero events. This is the `[open]`
statement already named in the centered-current construction; the present note registers the
induction architecture that consumes it.

## 4 · The tachyon and light-cone reading

[interpretation] A tachyon (`m² < 0`) is a vacuum instability, not a faster-than-light signal: the
configuration is not the minimum and the field condenses. The transplant here: the seam flow
`G_τ = G_ss` is odd under `τ → −τ`; one direction contracts (zeros drawn to the axis), the other is
anti-diffusive and nucleates (shocks, branchings). The all-real configuration at `t = 0` is the
**vacuum**; an off-line zero is a **tachyonic mode at the endpoint**. The certificate is the
positive potential `x = d² ≥ 0` or the normalized-log clock
`B_Y(x) = x/4 + (Y²/8) log(1 + 2x/Y²)` with `d B_Y/dt ≤ −1` — unit rate in every case, so the
"speed of light" is one, and `a = 0` is lightlike, `a > 0` timelike (faster decay), `a < 0`
spacelike (outward, tail-funded). The de Bruijn–Newman cone is `x + 2t = const`; RH says the cone
at `t = 0` is empty, exactly tangent to the axis. Time parity reads: the attractor of the time-odd
dissipative flow coincides with the fixed axis of the spatial parity (`s → 1−s`).

[interpretation] The graph form of the collision branch: at a multiple zero the pole order and
residue jump; the continuation is a chart transition (typed dilation/blow-up) that preserves the
divisor with multiplicity. One move owner, one continuity; the "child" inherits the parent's
divisor population. A cloned second universe would duplicate the owner and is refused by the
operating contract.

## 5 · Falsifiers

- [established-bounded; computational-witness] The existing quartet control
  (`research/experiments/mfr_entropy_heat_current/moving_plate_and_burgers.json`) satisfies the same
  complex Burgers law and symmetries with off-line initial zeros. **Any claim that the local
  identities or combinatorial structure alone close the induction is refuted by this control.**
  Only the actual ξ kernel/source conditions may close it.
- An actual ξ-sourced rightmost zero whose exterior tail is outward with enough margin to defeat the
  clock (`T_R > 0` and `d' > 0` admitted) kills the proposed bracket at that receiver and returns an
  obstruction, not a proof.
- If the multiple-zero continuation is shown to emit a positive width that reaches `t = 0`, RH is
  false; the continuation must be proved sign-preserving or reported as the obstruction.

## 6 · First derivation target

[open] Write the **periplus lemma** (September 15 renaming of "tail orientation"; a circumnavigation
record of the divisor population, not an external referee) for the actual ξ family: height-uniform
control of `J_R(t) − ε_R(t)` along rightmost-zero trajectories; then the **multiple-zero
continuation lemma** (pole order `k`, residue jump, width-sign preservation). Run both against the
quartet control as a separator: the control must fail the ξ-source hypothesis while satisfying
every formal statement used. Success returns a bounded strip exclusion or `Λ_DN ≤ 0`; failure
returns the precise missing inequality. Lean remains exterior verification; no
cultivation/inference consumer changes here. The September 15 strategy addendum (§9) sharpens
this target into the birth law and the address-lattice periplus law.

## 7 · The mass-squared descent and the fusion reading

[definition] Declare the **transverse invariant mass-squared of a rightmost zero pair** as
`m_⊥² = d²`. This is a supplied correspondence between the pair's normal separation and a
mass-squared; it is not the mass-squared of a field.

[proved-derived] Under the forward seam clock the width obeys `(d²)′ ≤ −2(1+a) < 0`: a descent
equation. Every unit of heat time buys at least two units of transverse mass-squared, released as
the heat of `G_τ = G_ss`. The flow is therefore a condensation, and the collision at `d = 0` is a
**fusion**: two simple zeros fuse into a multiple zero with the multiplicity retained — the
divisor's bound state — while the inverse, outward (spacelike) reaction can only be funded by the
exterior tail `T_R`. The eddy currents of the current construction are the dissipation channel for
the released width.

[interpretation] The nuclear chart maps: the mass defect and `Q = Δm c²` have the shape of the
width deficit; fusion rolls downhill toward deepest binding; the critical line is the iron peak of
the divisor population; `t = 0` is the symmetry-restored endpoint; the Coulomb barrier that makes
stellar fusion slow is the tail; and `Λ_DN = 0` is the **drip line** — Rodgers–Tao places the
vacuum exactly at threshold, and RH says the extremal zero is nonetheless bound, by zero margin.
No zero lies beyond the drip line.

[interpretation] Falsifier: if an actual-ξ zero's width grew under the forward flow, the
condensation reading dies with it. The proved content remains the width law and the tail bound;
the nuclear names are an interpretation of that equation with a supplied map.

## 8 · Boundary

Nothing in this note moves a numerical bound, imports a Polymath certificate as a Holonics result,
or changes the active Athena brief. The equivalence correction (§2), the Lenz reduction (§3), the
endpoint/tachyon and graph readings (§4), the falsifiers (§5) and the fusion/mass-squared
correspondence (§7) are deposited so the next attempt starts from the tail rather than from an
already-eliminated flux contradiction.

## 9 · September 15 addendum: the periplus strategy

**Provenance:** Brandon, September 15 direct discussion, same session. Corrections adopted:
the §6 open lemma is renamed **periplus** — a circumnavigation record of the divisor
population, every admitted zero a port with its bearing logged, not an external tail referee.
The shell-class modulation line drafted in discussion for the derivation target is superseded
by the address-lattice law below. His physical reading: RH is a circuitry and lightning-strike
construction with one real intermediary between two plates; the strip is not a vacuum; off-line
zeros are measured like dark matter, by the motion they induce on the visible sector; rotation
and free-fall are release-and-transport; and tori and knots are the native motion charts. The
strategy builds on the §4 tachyon starting-point: it does not replace it.

### The two-plate circuit, bound to the formal owners

[proved-derived; formal-checked] The plates are grounded: `riemannXi_ne_zero_of_one_le_re`
excludes zeros on `Re(s) ≥ 1`, `riemannXi_ne_zero_of_re_nonpos` excludes `Re(s) ≤ 0` by
reflection, and `riemannXi_zero_in_strip` confines every strike to the open strip. The single
real intermediary is the half-centre: functional reflection and conjugation coincide exactly on
the critical line (`Balance`), and equal reflected multiplicities give the normalized normal
face `m/(2m) = 1/2` (`PairPopulation.reflect`,
`TransverseCurrentBound.reflected_pair_center`) — one real unit of current per two real units
of pair mass. The inverted ratio is the width clock `(d²)' ≤ −2`: two units of transverse
mass-squared per one unit of heat time. The 1:2 and 2:1 faces are the same conserved transport
read from the two plates.

[proved-derived] The atmosphere is real: the finite side of the Weil pairing is the von
Mangoldt series with every local weight nonnegative (`RH.Xi`), and the Gaussian weight carries
the archimedean side. An off-line zero is a displacement in a real medium, not a vacuum
tachyon; its velocity is the comb log over the divisor population plus the medium's
displacement current `ε_R` (`FosterClassFlux`, `FiniteZeroCurrent`).

[proved-derived; formal-checked] The tide instruments are Weil squares:
`ĥ(s) = G(s)·conj(G(1−s̄))` reads `|G|²` on the line
(`WeilPositivity.spectralKernel_eq_normSq_on_line`), the zero receiver is nonnegative-real
under RH (`truncatedZeroReceiver_nonneg_of_RH`), and positivity of every device forces RH
through the named port `HasWeilCriterion`. One certified evaluation exists: the two-power
vector at addresses `{2, 4, 8}` returns exactly `3·log 2` (`WeilVector`) — the address, not
the size, decides the weight. The infinite device census is replaceable by a conservation law;
the samples are admissible without being sampled.

### The birth law and the address-lattice periplus

[open] **Birth law (the primary kill candidate).** RH is equivalent to: every conjugate pair
in the divisor population enters at `d² = 0` on the de Bruijn–Newman cone `x + 2t = const` —
nucleation *is* a collision in the invariant chart, where the conserved translation is the
divisor with multiplicity. A pair entering with `d² > 0` and outward rate is a source term no
chart change absorbs; it kills the fixed-population induction. The discriminating census
records every birth/collision under the seam flow as `(d², t, multiplicity)`: ξ must show
cone-respecting births only; one violating birth fires the §5 falsifier.

[open] **Address-lattice periplus law (supersedes the shell-class modulation guess).** The
dyadic shell `[2^k, 2^{k+1}]` is one full period of the prime flux's log phase `e^{iy log x}`
[proved-standard as a phase statement]. The shell's characteristic class is the divisor
lattice of its exponent: `2^5 − 1` factors only through `Φ_1, Φ_5`, while
`2^6 − 1 = (2^3−1)(2^3+1)` inherits the child cyclotomics and `2^8 = (2^4)²` likewise; Fermat
shells `2^{2^m} + 1` force primes `≡ 1 mod 2^{m+1}`; Zsigmondy supplies a primitive prime per
new exponent; Cunningham chains are address structures of the doubling map — prime as point,
chain as line, orbit cycle as loop, one object at three receiver scopes. The law to establish:
the zero comb's sailing log `d·(J_R − ε_R)` and the prime side's address lattice translate with
conservation uniformly in height. The quartet control has no addresses and cannot carry this
phase; that is the sharpened separator over the §5/§6 control role.
`Small Composite Numbers in Orbits of Linear Maps` (arXiv:2508.18305) bounds the orbit lengths;
it is exterior evidence at its declared scope.

### The dark-sector dictionary

[proved-derived; conditional] `Λ_DN` is the persistence time of the dark sector — the forward
condensation needed to absorb all complex mass. RH false with a simple off-line zero forces
`Λ_DN > 0`, because `SimpleZeroPersists` retains a unique simple zero of `H_t` near `t₀`; a
multiple zero owes the continuation lemma. Rodgers–Tao's `Λ_DN ≥ 0` says the dark sector
regenerates under every backward perturbation: the vacuum is exactly marginal — the §7 drip
line. RH is the zero-residual claim: the visible sector needs no dark term, and numerical
verification to height ~10¹³ shows no anomaly; the dark sector, if real, hides beyond the
verified horizon, so only the periplus closing crosses it. The cosmological-constant reading is
literal: `Λ_DN` embeds a correction for motion we cannot yet see.

### The motion charts (tori, knots, holonomy)

[interpretation] Physical charts of the same integer-winding family, each at its declared
scope: (i) free-fall is the line phase of transport; the turn exists as holonomy and becomes an
event only at loop closure — a torque-free gyroscope accumulates geodetic precession with no
local impulse, so free-spin is conserved winding between receipts; (ii) the `(p,q)` torus knot
(`HolonicTorusKnots`) is the spin/translation translation — one embedded curve of the geometric
two-torus, rotation chart for one receiver, linear-pull chart for another; (iii) helicity as
linking (`HelicityAsLinking`) is the conservation face: `helicity_cons`, reconnection
invariance under named moves, and `helicity_borromean` — a nonempty crossing population
invisible to the quadratic receiver, the partition-class distinction at receiver scope; writhe
alone is not an invariant, and framing plus the actual fields are owed; (iv) ferrimagnetism is
the counter-wound chart: two interlinked sublattice tori with opposing winding, exterior faces
cancelling to the small clock orientation, eddy channels closed by the insulating lattice, the
transporting face being precession phase in quanta of `ħ`. The `m_⊥² = d²` correspondence of §7
remains a supplied correspondence, not a field mass; these charts interpret the winding
conservation without altering it.

### Updated derivation order

1. Pilot census (exterior, **exact**, no float decisions): certified isolating intervals for the
   ξ zeros (ball arithmetic, e.g. arb; zero index and gap classes stay integers); exact sign
   certificates for the margin `J_pop(d, y) − ε_R` over each enclosure in rational arithmetic,
   with the exact Foster tail and `GammaStirling`-class bounds; worst-gap configurations located
   as exact pairs of zero indices. Floats appear only as declared preview charts, never as
   decision variables; the transcendentals (π, log, exp) stay symbolic — the log is its
   normalized integral mode, not a floating literal.
2. Height-uniformity scaling: certified zero tables toward `10⁶`; exact trend of the worst
   certificate, carried by zero index and Gram-block address classes, not by float position.
3. The surviving branch returns to Lean: the periplus lemma against `FiniteZeroCurrent`,
   `FoldedSourceBounds`, `heatE_norm_negative_zero_velocity_sub_comb_le` and the
   `GlobalWeilFinishLine` separator, with `ZeroGap`'s exact rational height selection and
   `OffLineJensen`'s unconditional count receiver; the birth law as the conservation clause of
   the multiple-zero continuation.
4. Any configuration whose exact certificate fails returns the obstruction as an exact
   rectangle; the strategy then converges on the birth law for ξ specifically, with the Weil
   devices as its receivers.

### Certified census return (2026-09-15, same day)

**Provenance:** Brandon authorized the exact census and its corrections: no floats anywhere,
no window exhaustion, the macroscopic flux pattern over the microscopic zeros, and the
repository's own certified zero solver. The first Python draft (`research/experiments/
rh_periplus_census/`) was removed the same day; the census now rides the atlas law.

**Instrument (existing owners, no new engine):** `relational_geometry::eta_atlas` —
`build_atlas`/`scan_integer_bands`/`descend` certify each zero as a winding: band boxes at a
*derived* Euler–Maclaurin start (the level is checkable, not declared), boundary winding kept
as two arms, cut-reusing refinement to winding-one lineages, serializable and verifiable
artifacts. The apparatus is `ResidentEtaHead` (`holonic-engine::cuda_eta_head`) — the O(N)
head of every pending boundary midpoint of one depth in one card launch, exact fixed-point
interval arithmetic at 96 fractional bits; nothing semantic is decided on the card, and the
receipts verify under the same law. Shell representatives were scanned and refined to
certified zero boxes in minutes, not hours: bands `1024–1026` (56 s), `4096–4098` (79 s),
`16384–16386` (2 m 33 s), 24 workers, `grains=6, grain_bits=48`, alongside the existing
verified `atlas-12-36.ron`.

**Reader:** `holonic-engine/examples/
the_periplus_surplus_reads_the_certified_zero_comb.rs` computes, in BigInt/BigRational only,
the certified surplus `d·J_R` and margin `M = d·J_R − 1` per lineage at dyadic widths
`1/2, 1/4, 1/16, 1/256`, with the certified neighbor distances taken at interval ends; every
admitted zero outside the artifacts contributes a nonnegative omitted term, so each margin is
a certified lower bound. Display is outward-rounded at 8 bits and declared as display; the
receipts live at `.local/artifacts/rh-periplus-census/periplus_surplus.json`.

[proved-derived; computational-certificate] **The surplus is second-order in the width.** At
every certified configuration and every small width, `M = d·J_R − 1 ≈ d²·C(y) − 1`: the
population's direct inward surplus on a hypothetical off-seam quartet vanishes quadratically
as `d → 0`. The linear `d·log(y)` density heuristic is refuted as the near-seam asymptotic.
The arb-ball census run earlier the same day returned the same surplus at the shared heights —
two independent exact instruments agree.

[proved-derived; computational-certificate] **The macroscopic flux pattern.** The certified
band windings are the counting current: at `y ≈ 1024` one band winds 0 and the next 2 (a gap
band adjacent to a double band, gap certified `[27/64, 29/64]`); at `y ≈ 4096` and `16384` the
bands wind 1–2 with certified gaps in `[35/64, 37/64]` and `[9/8, 73/64]`; the derived EM
start grows essentially linearly with height (`954 → 3949 → 16451`) — the recurring head is
the compressed level each band re-derives and the verifier re-derives, exactly the
recurring-solution-as-mode structure. Within the certified population the per-shell margin
minima stay deeply negative at small widths (shell 10 at `d = 1/16`: `M_lo = −247/256`), the
tight configurations remaining the large-gap ones.

[open; derived target] **The birth-cone consequence, in oriented form.** At `d → 0` the
certified surplus is `O(d²)`, so the population alone can never fund an outward birth. The
exterior remainder is not a magnitude: the Foster split is a parametric modulo — the product
splits at the half-disc modulus `‖z − 1/2‖ = R/2` into the finite tank product and the
*exterior factor* `tail(R)(z) = ∏'_{i ∉ T(R)} (1 + a_i z)` (`FosterClassSplit`), whose exact
log-derivative is the oriented exterior current `logDeriv(tail)(s) = Σ' tank(i, s)`
(`logDeriv_tail`), parametric in the cut. The magnitude bound `‖logDeriv tail‖ ≤ ε_R`
(`norm_logDeriv_tail_le`, Landau's Borel–Carathéodory face in `LogDerivativeRemainder`) is a
derived receiver chart of that oriented object, consumed by the width law's worst case; the
House rule is that an enclosure retains the signed/oriented defect with a bound, not the
magnitude as source. The width law therefore reads, oriented, as the identity
`d' = −1/d − J_R(R) − Re(Rem(R))` with the total normal current of population plus exterior
current. The periplus lemma's target, without any absolute operator:

```text
d·(J_R(R) + Re(Rem(R))) ≥ 0     uniformly in height,
```

equivalently the exterior current's outward face never exceeds the certified funding
`d²·C(y)` — the paired cross-sections cancel by the half-centre parity, the unpaired
population terms are inward by the rightmost ordering, and the one surviving face is the
orientation of the parametric remainder. At the seam (`d → 0`) the outward face is killed in
the limit: the funding vanishes quadratically, which is the marginal face of the birth law,
not a pointwise vanishing of the atmosphere. Widening the certified ranges (more bands per
shell, not exhaustive sweeps) tightens `C(y)`; the multiple-zero continuation and birth census
remain the formal discriminator on the Lean side, with the Weil devices as receivers.

[project-postulate] **The periplus is one face of a wider integration** (Brandon, same-day
correction): the solution space is not the two-variable width chart alone. The named owners to
integrate at their declared scopes: series expansions and conserved faces
(`CONSTRAINT_MODES_AND_RECEIVER_FACES` — one constraint mode's paired coordinate faces,
stress through oriented faces); spring/orbital equilibria and what `1/2` carries
(`HolonicPantographicSwingJets` — the triangular jet ledger `j_n = gainⁿ·scale^choose(n,2)·j₀`
and the typed jerk/snap/crackle/pop force-current readings under `D^r F = mass + D^(r+2)
position`; `HolonicClockedPantographicSwing` — clock ratios by integer quotient with the
remainder retained as within-cycle phase, the oriented modulo at the clock level); the curved
arc and its higher derivatives (`HolonicCurvedArcEinstein` — six typed arc ports, curvature
return as gyrogroup gyration, Gauss–Bonnet holonomy `2πχ`, and the Einstein falsifier: only a
locally calibrated arc/differential equation survives, never a universal coupling); natural
cross-entropy flux (`CrossEntropyFiber`, the complex cross-entropy with angular lift and
winding in `Physics/InformationDifference`); and the hypergeometric/toroidal carriers
(`hypergeometric_closure` in the integrand-organ route, `HolonicTorusKnots`,
`HolonicFourTorusCarrier`, string/M compactified mode transport). The seam flow's zero
dynamics `ż = −G_ss/G_s` is itself a ratio of higher derivatives, and the width law's
`(d²)′` is the jet face of that trajectory — the pantographic ledger is the general law the
RH jets instantiate.

## 10 · The unified strategy for `Λ_DN ≤ 0`

**Provenance:** Brandon's September 15 request to unify the RH strategies around the
equivalent of `Λ_DN ≤ 0`, building on this document's tachyon starting-point.

### The equivalent, stated once

[definition] In this architecture `Λ_DN` is the **persistence time of the dark sector**: the
forward seam-flow time needed to absorb every complex (off-seam) holon of the divisor
population. Rodgers–Tao prove `Λ_DN ≥ 0` — the vacuum is exactly marginal — so RH is
`Λ_DN = 0`, and the Holonic equivalent of `Λ_DN ≤ 0` is:

> **Every zero of ξ is a lightlike holon.** The divisor population at `t = 0` is fully
> condensed: no complex mass, no outstanding width, no outward-funded birth, and the real
> spectrum needs no dark term.

Four receiver faces of that one statement, each binding existing owners:

1. **Clock face.** The cone `x + 2t = const` at `t = 0` is empty, and every birth enters at
   `d² = 0` — the birth law. The clock `dB_Y/dt ≤ −1` is height-uniform: unit rate, lightlike
   on the seam, `a = 0` the marginal case.
2. **Current face (the periplus).** `d·(J_R(R) + Re(Rem(R))) ≥ 0` uniformly in height — the
   total normal current (certified population plus oriented parametric remainder) is inward
   at every rightmost configuration; the paired cross-sections cancel by half-centre parity,
   the unpaired population terms are inward by the rightmost ordering.
3. **Device face (Weil).** The zero receiver is real and nonnegative on every Weil square
   (`HasWeilCriterion` port; `truncatedZeroReceiver_nonneg_of_RH` proved under RH) — every
   tide instrument reads only real flux, and the infinite census is replaced by a
   conservation law.
4. **Ledger face (the finish line).** The prime side and the archimedean side account for the
   zero receiver through the certified residual identity on cofinal contours
   (`GlobalWeilFinishLine`), whose off-critical-line test separator is the terminal
   discriminator.

### The strategies, one architecture

- **S1 · Birth census (primary).** Census every birth/collision as `(d², t, multiplicity)`;
  RH ⟺ cone-respecting births only. The formal core is the multiple-zero continuation lemma
  (pole order `k`, residue jump, width-sign preservation). The quartet control — fixed
  population, no arithmetic addresses — is the separator. One cone-violating birth fires the
  §5 falsifier and names the obstruction; that return is convergence, not failure.
- **S2 · Periplus (oriented domination).** Prove `d·(J_R + Re(Rem)) ≥ 0` against
  `FiniteZeroCurrent`, `FosterClassFlux.comb'_sub_le`, `FoldedSourceBounds`, consuming the
  oriented exterior current `Rem(R) = logDeriv(tail) = Σ' tank` as source and its magnitude
  face only as a chart. The certified census contributes the comb-side funding `d²·C(y)` and
  the cross-section family (certified band windings, two arms kept).
- **S3 · Weil devices and the address lattice.** Discharge the criterion through the
  address-lattice law: dyadic shells as log-clock periods, divisor-lattice shell classes
  (Zsigmondy primitive primes, Fermat congruence phases, Cunningham point–line–loop orbits),
  with the certified two-power evaluation `3·log 2` at addresses `{2, 4, 8}` as the certified
  instance. The quartet control carries no addresses and cannot produce this phase.
- **S4 · Finish line.** `GlobalWeilFinishLine`'s structure — cofinal contours, weighted
  argument principle, residual identity, convergence, off-critical-line separator — is the
  terminal consumer every route returns to, pursued or refuted with named locations.

**Convergence order.** The census feeds S2's funding side and S1's event data; S1's boundary
case is the seam itself, where S2's domination forces the outward face to zero; S3 discharges
S4's separator hypothesis through the arithmetic face. The wider integration (§9) supplies
each face's higher structure — jets, cross-entropy flux, hypergeometric modes, toroidal
carriers — without introducing a second engine.

**Boundary.** No numerical bound moves; the active Athena brief is unchanged; every claim
above carries its grade; the falsifiers are part of the architecture, not decoration. Lean
remains exterior verification; no cultivation/inference consumer changes.
