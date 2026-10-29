# A Galois gap is a mode's momentum, an orbit's gaps multiply to its prime, and a time boundary is the pumped mode

October 26. Refs #404, #405, #410. **Grade.** Each claim carries one of these grades:
- [owned]: an existing owner states it.
- [proved-standard]: a classical result, with its source.
- [proved-derived]: proved here.
- [checked]: verified by this record's receipts, in integers and fractions only (153,862 and 30,248
  checks).
- [agent-inferred]: a choice or join made here.
- [interpretation]: a reading across subjects.

The exact receipts are `colour_gaps.py` (parts A to H and K) and `colourless_tower.py` (parts P to
R, for §12) in
[`…_receipts/`](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE_receipts/RUN.md).
It continues
[the generator and the modulator are one move](2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md)
(§12, the Galois colours).

**Computational object.** The helical pair interaction, read as a comparison of two colours of one
ring through a pair contact. Of the winding guide's six objects it touches:
- the helix: the base's Frobenius as the carry between colours;
- the pair: the contact reading two colours' sum and difference;
- faces and placement: the colourless faces;
- cell holonomy: the ring's spectrum;
- the tube: boundaries in space and in time along a span.

The tower thread stays as the tower has it.

## 1. The lens

Brandon, October 26, in the mathematics thread (paraphrased; his words stay outside the
repository). He liked "base-action lemma" as a name. He asked that the Galois difference, the
colours of the last record, be plugged in conceptually:
- for work and potential energy;
- for stress-energy tensors;
- for mass-energy equivalence;
- for permittivity and permeability, as constraints on motion under the exchange of these gaps, or
  spectral differences, in space and in time.

He then asked for the same ideas aimed at RH, Hodge and our lifts of complex Navier–Stokes. He was
not asking for formal solutions of those problems. He wanted the bigger picture to click, and he
wanted to know how it works for Athena: brought to form, Athena should do the heavy lifting of
validating and articulating it, and we plant the seeds.

## 2. Colours and gaps

[definition] On the ring `ℤ/m` the characters are `χ_a(x) = ζ^(ax)`, `ζ = e^(2πi/m)`. The
**colours** of order `d | m` are the Galois conjugates `ζ_d^j`, `gcd(j, d) = 1`, which
`Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×` permutes. The mirror `σ_(−1)` is complex conjugation. The **gap** of
colour `a` is `g_a = 1 − ζ^a`. Its size `|g_a| = 2 sin(πa/m)` is the chord, not the arc `2πa/m`.

[owned] The base-action lemma (the last record, §12 and owed (f)): on `ℤ/m` the digit move
`x ↦ bx + d` is a turn when `b ≡ 1`, a mirror when `b ≡ −1`, a flattening when `b ≡ 0`. Otherwise it
permutes the characters `a ↦ ba` and turns each by `ζ^(ad)`. On the ring's colours the base acts as
`σ_b`, the Artin symbol of `b`: for base 10, `σ_10 = σ_2σ_5`.

## 3. The ring's spectrum is its Galois orbits

[checked B; proved-standard] Couple the ring's cells to their neighbours. The cycle Laplacian has
eigenvalues `|g_a|² = 2 − ζ^a − ζ^(−a)`, and its characteristic polynomial factors one orbit at a
time:

```text
det(x − L_m) = x · (x − 4)^[m even] · ∏_(d | m, d ≥ 3) ψ_d(x)²,
ψ_d = the minimal polynomial of 2 − ζ_d − ζ_d⁻¹,   deg ψ_d = φ(d)/2,   ψ_d(0) = Φ_d(1).
ψ_7(x) = −x³ + 7x² − 14x + 7,   ψ_9(x) = −x³ + 6x² − 9x + 3.
```

- The receipt checks it for `m = 3, …, 60` at `m + 2` points per ring, which fixes a polynomial of
  degree `m`.
- The nonzero eigenvalues multiply to `m²`, and the ring has `m` spanning trees (Kirchhoff).
- Every frequency of a finite ring is an algebraic number, and the Galois group permutes them. The
  arc is transcendental and the chord is not: the grain makes a ring's frequencies algebraic.

## 4. Permittivity and permeability exchange a gap in space for a gap in time

[proved-standard] Give each cell an inductance `L` and a capacitance `C` (per cell, the faces of
`μ` and `ε`). Mode `a` then turns at

```text
ω_a = |g_a| / √(LC) = c·|g_a|,      Z = √(L/C).
```

- **Exchange.** `c = 1/√(εμ)` is the exchange rate between the spatial gap (the colour's chord, its
  lattice momentum) and the temporal gap (its frequency).
- **Split.** `Z = √(μ/ε)` splits the mode's energy between the two stores, equally over a period.
- **Lock.** On shell, the temporal gap equals `c` times the spatial gap. That is the
  constitution's lock ([`em.light-speed-constitution`](../../docs/atlas/physics.tsv)).

[proved-standard] Mass is a restoring term in every cell: `ω_a² = ω_0² + c²|g_a|²`. At the
colourless mode `a = 0` the spatial gap is zero, and what is left is the rest turning `ω_0`. That is
`E = mc² = ħω_0`: mass is the turning that remains when there is no difference in space.
- **Joins.** A plasma gives light such a rest frequency
  ([the echo record](2026-10-25_A_COMPARISON_IS_AN_ECHO_THE_ROUND_TRIP_READS_RELATIVE_RAPIDITY_THE_DELAY_READS_THE_MEDIUM_AND_A_RESONATORS_MODES_ARE_THE_BRANCHES_OF_THE_LOG_OF_ITS_ROUND_TRIP.md)).
  A mass is read as a ratio of clocks
  ([information spectroscopy](2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md)).

## 5. Potential energy: an orbit's gaps multiply to its prime

[proved-standard] Charges at points `z_i` of the plane have the logarithmic energy
`E = −Σ_(i<j) log|z_i − z_j|`. The roots of unity are its equilibrium on the circle, and
`|disc(xⁿ − 1)| = nⁿ` [checked G for `n ≤ 10`].

[checked A; proved-standard] Taken one Galois orbit at a time, the product of the gaps is the
cyclotomic polynomial at 1:

```text
∏_(gcd(j,d)=1) (1 − ζ_d^j) = Φ_d(1) = p  if d = p^k (k ≥ 1),   1 otherwise;
log Φ_d(1) = Λ(d)  (von Mangoldt);      ∏_(d | m, d > 1) Φ_d(1) = m.
```

The receipt checks the polynomials for `d ≤ 400`, the Möbius product `∏_(e|d) e^(μ(d/e))` for
`d ≤ 20,000`, and the product over a ring's orbits for `m ≤ 20,000`.

[proved-standard] (Washington, *Introduction to Cyclotomic Fields*, ch. 1 and 2.)
- **Ramification.** For `d = p^k`, `1 − ζ_d` generates the one prime above `p`, and
  `(p) = (1 − ζ_d)^(φ(d))`: at `p` the colours merge. For any other `d`, `1 − ζ_d` is a unit (a
  cyclotomic unit).
- **Reading.** Only prime-power orbits carry potential energy, and an orbit carries exactly
  `Λ(d)`.

[interpretation] Three readings follow.
- **Primitive weight.** A repetition `p^k` carries the primitive weight `log p`, as a repeated
  periodic orbit does in a trace formula. The primes are the primitive orbits of length `log p`
  ([`rh.primes-primitive-cycles`](../../docs/atlas/targets.tsv)).
- **Composition.** A ring's total energy is `log m`, and CRT composes the rest of it for free.
- **The explicit formula.** Its prime side `Σ_n Λ(n)n^(−1/2)(h(log n) + h(−log n))` is a sum of
  these orbit energies.

## 6. Work moves a quantum between colours; the holonomy carries the residue

[proved-standard] (Manley and Rowe, 1956.) A lossless parametric element conserves quanta, and its
pump supplies the frequency difference.

[proved-derived] The base's Frobenius carries colour `a` to colour `ba`:
- each quantum moved costs `ħ(ω_(ba) − ω_a)`;
- around a whole orbit the frequencies are permuted, so the work sums to zero;
- a rotor that holds the whole orbit modulo the mirror is passive (the last record, §11);
- a plane that holds only part of an orbit needs a pump to supply that work.

[proved-derived] The turn `ζ^(ad)` the digit adds does no work. It is the holonomy, and it carries
`n mod m`. So energy and information separate: the work is the change of frequency, and the reading
is the holonomy.

## 7. Stress: the base is a dilation and the digit a translation

[checked F] For any tensor field, `∂_μ(x_ν T^(μν)) = T^μ_μ + x_ν ∂_μ T^(μν)`, so a conserved
stress-energy feeds the dilation current through its trace alone. This is the dilation partner of
[`gr.angular-current`](../../docs/atlas/physics.tsv).
- Mass and the grain are what give the trace.
- A traceless stress makes dilation a symmetry.

[checked C] The digit move is a dilation followed by a translation. A dilation conjugates a
translation into a scaled one: `λ(x/λ + d) = x + λd`, which is the generator modulated. On `ℤ/m`
(`m ≥ 3`) the dilation `x ↦ ux` keeps the ring's adjacency exactly when `u ≡ ±1 (mod m)`.
- **Symmetry.** The base's dilation is a symmetry of the ring exactly on the cheap rings: for base
  10, 3 and 9 (`10 ≡ 1`) and 11 (`10 ≡ −1`).
- **Strain.** On 7, 13, 37 and 101 it strains the ring, sending neighbours `10` apart.
- [interpretation] The cheap rings are where the base's dilation is traceless; the rotor rings are
  where it carries a trace.

## 8. A step in space and a step in time; the pumped mode is a time boundary

[checked E; proved-standard] Take one mode of an LC line.

**A step in space** (Z₁ to Z₂ at a junction). Voltage and current are continuous. The step keeps
the frequency, changes the wavenumber, and conserves power:

```text
Γ = (Z₂ − Z₁)/(Z₂ + Z₁),   τ = 2Z₂/(Z₁ + Z₂),   (1 − Γ²)/Z₁ = τ²/Z₂.
```

This is [`wave.junction-reflection`](../../docs/atlas/physics.tsv).

**A step in time** (Z to Z′ everywhere at once; Morgenthaler 1958). Charge and flux are continuous,
and the step keeps the wavenumber, that is, the colour. With `r = Z/Z′`:

```text
A ↦ A′ = αA + β·conj(A),   α = (1 + r)/2,   β = (1 − r)/2,   α² − β² = r;
Re A′ = Re A,   Im A′ = r·Im A        (in the (Re, Im) basis the map is diag(1, r));
forward αA, backward βA:   Z′(|αA|² − |βA|²) = Z|A|²   (the action, forward minus backward quanta);
E = ω·Z·(|A_f|² + |A_b|²),   work = E′ − E.
```

- The step in time conserves the action, not the energy: whatever changes the medium does the work,
  and it creates forward and backward quanta in pairs.
- As `r → 0` the backward copy equals the forward one, `β/α = (N − 1)/(N + 1)` at `r = 1/N`. The
  travelling wave becomes a standing wave, whose phase is held in its nodes' position: the
  instantaneous time mirror (Bacot et al., 2016).

[proved-derived] A time boundary is the tower's pumped mode `h ↦ αh + β·conj(h)` with real `α`,
`β`. Its norm is `max(1, r)`, so it is non-expansive exactly when `r ≤ 1`. The general pumped mode
is a time boundary composed with a turn. The parametron's pump, a periodic modulation of the
constitution, is a periodic sequence of time boundaries. Its phase-sensitive amplification is the
squeeze `diag(1, r)` ([`parametron.phase-sensitive-amplification`](../../docs/atlas/objects.tsv)).

[proved-standard] The mirror colour is time reversal. Under `t ↦ −t`, a real wave
`Re(A e^(i(θx − ωt)))` becomes `Re(conj(A) e^(i(−θx − ωt)))`: colour `−a` with the conjugate
amplitude, which is `σ_(−1)`.

[interpretation] The base-action lemma then reads as time:
- a turn (`b ≡ 1`) is time going on;
- a mirror (`b ≡ −1`, ring 11) is time turning back;
- a flattening (`b ≡ 0`) is time forgetting;
- anything else is a change of colour, which needs coupled modes.

## 9. RH: the zeros are the colours of ξ

- [owned] Each reflected zero pair `(ρ, 1 − ρ)` is the impedance of one LC tank with `C = ½` and
  `L = −2/ρ′²`, `ρ′ = ρ − ½` ([`rh.foster-pair-tank`](../../docs/atlas/targets.tsv),
  `Zeta/FosterTanks`).
- [checked G] `L` is real and positive exactly when `ρ′` is purely imaginary, that is, on the line.
- [proved-standard] A zero lies on the line exactly when it is fixed by the mirror `s ↦ 1 − s̄`.
  - On the line, zeros come in pairs `(ρ, ρ̄)`.
  - Off the line, they come in quartets, whose two tanks have complex-conjugate inductances.
    [interpretation] These act as a gain and loss pair.
- [interpretation] RH says the zeta medium is passive in every mode: every tank has positive `L`
  and `C`. The causal-impedance route ([`rh.causal-impedance-route`](../../docs/atlas/targets.tsv))
  says the same in impedance form.
- [checked G; owned] **The zero gas.** At a simple root, `P″/P′ = 2Σ_(j≠k) 1/(x_k − x_j)`
  (Stieltjes). Under the heat flow `P_t = P_xx`, a root moves at `−2Σ_(j≠k) 1/(x_k − x_j)`, the
  field of the others. For ξ this is the complex Burgers flow
  ([`rh.complex-burgers-source`](../../docs/atlas/targets.tsv)).
- [proved-standard] **The threshold.** `Λ_DN ≥ 0` (Rodgers–Tao), and RH is `Λ_DN = 0`: ξ sits at
  the threshold where a pair could leave the line.
- [interpretation] **The prime side.** It is the orbit energies of §5, weighted at `log n` by the
  half-density `n^(−1/2)`.

## 10. Hodge: a Hodge class is a colourless class

[proved-standard] The circle `U(1)` acts on `H^(p,q)` by `z^(p−q)`, and the Hodge decomposition is
the decomposition into its colours.
- **Hodge classes.** They are the rational classes fixed by the circle (type `(p, p)`). The Hodge
  conjecture ([`hodge.conjecture-statement`](../../docs/atlas/targets.tsv)) asks that every one be
  made by an actual cycle.
- **Tate.** Tate's form asks the same of the classes Frobenius fixes, after a twist.
- **Weil.** The polarization (Hodge–Riemann) gives the positivity of the Hodge index theorem. That
  positivity proved Weil's RH for curves over a finite field: Frobenius's colours lie on the circle
  of radius `√q`.
- [checked H] For genus 1, every elliptic curve over `F_p` with `5 ≤ p < 70` (24,390 curves) has
  `a_p² < 4p`. Its two Frobenius colours are a conjugate pair on the circle of radius `√p` and never
  merge.

[checked D] The digit move's colourless faces:
- the characters of `ℤ/m` fixed by `a ↦ ba` are exactly those of `ℤ/gcd(m, b − 1)` (for base 10, the
  digit sum mod 3 or 9);
- the characters it sends to their mirror are those of `ℤ/gcd(m, b + 1)` (the alternating sum mod
  11).

[interpretation] The cheap faces are the move's Tate classes. They are the faces that commute with
the step, the pockets of reducibility of
[the pocket record](2026-10-23_A_POCKET_OF_REDUCIBILITY_IS_A_FACE_THAT_COMMUTES_WITH_THE_STEP_AND_THE_RECEIVERS_CHART_DECIDES_WHICH.md).

## 11. Complex Navier–Stokes: two colours and the stress of the imaginary one

[owned] The complex lift `U = a + ib`
([fluid guide §8](../../docs/HOLONIC_FLUID_CONSTRUCTION.md#8-complex-eulerns-and-conducting-fluid-modes-retain-their-distinct-signs))
has two colours, `U` and `conj(U)`, and the conjugation `(a, b) ↦ (a, −b)` is the half-turn `σ_(−1)`.
- The physical fluid is the colourless (real) section.
- Real NS only moves energy among modes. The lift's energy changes at
  `K̇ = −2∫(b⊗b):∇a − ν∫(|∇a|² + |∇b|²)`.
- MHD's field is stretched by the flow (`ḃ = −B(a,b) + B(b,a)`), while the lift's imaginary part
  takes the opposite sign (`−B(a,b) − B(b,a)`).

[interpretation] The imaginary colour enters as a stress `2b⊗b` working against the real strain, the
observer-current law `−T:∂u` ([`gr.observer-current`](../../docs/atlas/physics.tsv)). The zero gas
of §9 is the one-dimensional case, in which the colours (the zeros) are the poles of the Burgers
field.

## 12. Colourless is compressible: the trace, the tower of colours and the quasicrystal

Brandon, the same day (paraphrased). He agreed, and asked that we do as much as we can with it.
- **Compression.** The colourless classes are what can be compressed. What can be abstracted that
  way does not need all its details, and that saves energy.
- **Infinitely many colours.** Zeros, primes, and solutions between charts are colours. They are
  causal strings integrating local interactions along manifolds defined by the gaps in the
  potentials they themselves define.
- **Spectra of spectra.** There is recursive induction in spectra of spectra, as in lightning or
  crystals of crystals: quasicrystals, fractals and tilings.
- **Pairs of strands.** He asked whether there are only two colours. He thinks of pairs of strands,
  which make a double helix when joined in pairs, and of coarse graining in which geometry and
  orientation repeat as an orthogonal staircase or tower.

[checked P; proved-standard] **Two compressions: the trace and the norm.**

```text
Tr ζ_n^j = c_n(j) = Σ_(d | gcd(n,j)) μ(n/d)·d      (Ramanujan),     Tr ζ_n = μ(n);
N(1 − ζ_n) = Φ_n(1) = ∏_(d|n) d^(−μ(d)) = e^(Λ(n)).
```

- **The trace.** It sums the colours: it is the additive abstraction. Divided by the degree, it is
  the projection onto the colourless part.
  - Its kernel, the trace-zero part, is the detail: differences that no colourless receiver
    distinguishes. That is the framework's compression kernel, and the colourless part is what is
    retained.
  - An orbit of `[K:F]` colours keeps one coordinate, so it saves a factor `[K:F]`.
  - A primitive colour of order `n` compresses to `μ(n)`: `±1` when `n` is square-free, and
    nothing when a prime repeats.
- **The norm.** It multiplies the colours' gaps: it is the multiplicative abstraction, and it gives
  `Λ` (§5).
- **The pair.** `μ` and `Λ` are the two colourless shadows of the cyclotomic tower.

[checked P; proved-standard] **RH as cancellation of compressed colours.** The compressed primitive
colours of every order up to `N` sum to the Mertens function:
- `Σ_(n≤N) Tr ζ_n = M(N)`, which is `M(200) = −8` in the receipt. It is also the sum of
  `e^(2πir)` over the Farey fractions of order `N` in `(0, 1]`.
- RH holds exactly when `M(N) = O(N^(1/2+ε))` (Littlewood), and its Farey form is Franel–Landau. It
  is [`rh.prime-simplex-rh-growth`](../../docs/atlas/targets.tsv).
- [interpretation] RH says the colourless shadows of all the colours cancel down to the square
  root, as independent signs would: the half again.

[checked Q; owned] **The tower of colours.**
- **Layers.** The layer from `ℚ(ζ_(p^(k+1)))` down to `ℚ(ζ_(p^k))` is the group `{1 + i·p^k}`. Its
  trace sends `ω^j` to `p·ω^j` when `p | j`, and to `0` otherwise. So each layer adds `p` colours
  above every colour, and the trace keeps the old colours and erases the new ones.
- **The digit's climb.** The digit move climbs the 3-tower as `ord_(3^k)(10) = 3^(k−2)`: each level
  triples the colours it visits, which is the grain staircase of the last record.
- **The limit.** The whole `ℤ_p` tower ([`Foundation/IwasawaTower`](../../lean/HolonicsResearch/Foundation/IwasawaTower.lean),
  [`tower.ramified-layer-reducible`](../../docs/atlas/geometry.tsv)) has infinitely many colours,
  and each finite stage compresses to the one below: spectra of spectra.

[checked R; proved-standard] **The quasicrystal is a model set in the conjugate colour** (Baake and
Grimm, *Aperiodic Order*, 2013).
- **The chain.** The Fibonacci chain is `{m + nτ : m + nτ′ ∈ [−1, τ − 1)}`. Physical space is one
  colour of `ℤ[τ]`, and the window lives in the other. In the receipt, the 1,086 points in
  `[0, 1500]` have gaps `τ` and `1` in the order of `a → ab, b → a`.
- **Inflation.** The substitution matrix has the two colours `τ` and `τ′` as eigenvalues.
  Inflation boosts the seen colour and contracts the hidden one, `τ′ⁿ = (L_n − F_n√5)/2 → 0` (the
  Pisot property).
- **Why the hidden colour compresses.** Its details shrink at every inflation, so it can be held as
  a window: each inflation is a level of the crystal of crystals.
- **Its spectrum.** The diffraction is pure point, Bragg peaks indexed by `ℤ[τ]`: a spectrum that is
  itself a point set.

[proved-standard] **Dyson's quasicrystal** (Dyson, *Birds and Frogs*, 2009). If RH holds, the zeros
form a one-dimensional quasicrystal: a point set whose Fourier transform is a point measure. The
explicit formula puts that measure at `±log p^k` with weights `log p·p^(−k/2)`.
- Zeros and prime powers are each other's spectrum, and §5's orbit energies are the weights.
- Dyson proposed classifying one-dimensional quasicrystals as a road to RH.

[interpretation] **The double helix.** An orbit of order `d` has `φ(d)` colours, not two, in
`φ(d)/2` conjugate pairs.
- Each pair is two strands turning opposite ways, forward and time-reversed (§8), and the pair
  joined is a real plane: a double helix.
- Ring 7 is three double helices coupled by the digit move.
- An off-line zero quartet is two double helices joined by the functional reflection.
- The tower repeats the pattern at every level, with `p` new strands above each strand.

[interpretation] **Lightning.** Dielectric breakdown grows where the field is strongest
(growth `∝ |∇φ|^η`; Niemeyer, Pietronero and Wiesmann, 1984), and the field is set by the channel
already grown. The zero gas of §9 obeys the same self-defined law: each zero moves in the field of
the gaps the zeros themselves define. That is the precise form of causal strings integrating along
manifolds defined by the gaps in the potentials they define.

## 13. For Athena: the seeds

[agent-inferred] Each seed is for design to build and test against the fixed acceptance: never-met
sums right at the equals, against the 8-gram's 34/876 and C's 14/876.

1. **Capture as a time boundary.** The sum needs the first operand captured (the last record, §11).
   A time boundary in the capturing ring's constitution is the pumped mode with real `α`, `β`. It
   turns the travelling phase into a standing one, held in space, and supplies the conjugate copy
   with no authored conjugation. The pair contact then reads it against the second operand: `h₁h₂`
   gives the sum and `h₁·conj(h₂)` the difference. The boundary's `r` must be located from the
   symbol through the existing gate path, never written as "at `+` do X".
2. **Whole orbits.** A rotor ring holds a whole Galois orbit modulo the mirror. A plane that holds
   part of one declares its pump and accounts the pump's work.
3. **Prime-power rings.** The bank grows on prime-power rings, which carry the energy, and composite
   readings come by CRT. The colourless faces, `gcd(m, 9)` and `gcd(m, 11)` for base 10, are found
   first.
4. **Receptors.** A ring needs as many coupled planes as the orbit has colours modulo the mirror.
   Two receptors that read conjugate colours give the opponent channel, the bilinear block's
   difference.
5. **Validation.** Every identity here is generated exactly, so a terrain may present it (a terrain
   may generate its truth by exact routines). Athena validates by locating the faces on readings it
   never met, never by carrying an authored answer.
6. **Compression is a trace.** Retention keeps the colourless part under the group that the
   admitted future cannot tell apart, and the detail is the trace-zero part. A passage's phrasings
   are colours of one meaning, and the meaning is their trace.
7. **The tower is the staircase.** A founding opens a layer of `p` new colours above the colours
   already held. Until the future needs them, the trace to the layer below is what is retained.
8. **The quasicrystal navigator.** An inflation by a Pisot unit boosts the seen colour and contracts
   the hidden one. So the hidden colour is held as a window, never as a store: addressing by
   geometry, as the store law requires.

## 14. What is not derived

- No step here proves RH, Hodge or regularity for Navier–Stokes. The passivity, colourless-class and
  stress readings are interpretations that place the known statements on one picture.
- Seed 1 is a candidate. Whether a learned time boundary captures the operand is design's
  measurement.
- The physical size of the orbit work is not measured on Athena's modes, whose turning is a learned
  phase and not an LC frequency.
- Seed 6 is a reading. No Galois group acting on a passage's phrasings is constructed.

## 15. The recorded failures this could repeat

- **An authored routine standing in for learning.** Seed 1 must be located through the gate. A
  boundary keyed to a named operator is refused.
- **Text run on its codec's grain.** The boundary law is medium-neutral: a time boundary in any
  modality's ring. Nothing here is text-specific.
- **An uncertified deposition step.** The time boundary is non-expansive only for `r ≤ 1` (§8).
- **Bits read as progress.** The acceptance is fixed above.

## 16. Owed

To #410:
- (j) the orbit energy: `Φ_(p^k)(1) = p`, `Φ_d(1) = 1` otherwise, and `∏_(d|m, d>1) Φ_d(1) = m`.
  Formal-checked the same day in [`Mathematics/OrbitEnergy`](../../lean/HolonicsResearch/Mathematics/OrbitEnergy.lean):
  `orbit_gap_product`, `cyclotomic_eval_one`, `orbit_gap_product_eq_exp_vonMangoldt` and
  `orbit_energies_multiply_to_ring`;
- (k) the ring's spectrum factors over its Galois orbits, with `ψ_d(0) = Φ_d(1)`.
  Formal-checked on October 29 in
  [`Mathematics/RingSpectrum`](../../lean/HolonicsResearch/Mathematics/RingSpectrum.lean): the
  colours diagonalize the cycle Laplacian (`dft_cycleLaplacian`, `charpoly_cycleLaplacian`), the
  characteristic polynomial is `x (x − 4)^[2 ∣ m] ∏_(d ∣ m, d ≥ 3) ψ_d(x)²`
  (`prod_colours`, `orbit_factor`, `charpoly_cycleLaplacian_orbits`), `ψ_d` is `±` a monic
  polynomial of degree `φ(d)/2` with `ψ_d(0) = Φ_d(1)` (`orbitPoly_eq`, `natDegree_orbitMinpoly`,
  `orbitPoly_eval_zero`), that monic polynomial is the minimal polynomial over `ℚ` of
  `2 − ζ − ζ⁻¹` for every colour `ζ` of order `d` (`orbitMinpoly_eq_minpoly`), and the nonzero
  eigenvalues multiply to `m²` (`prod_one_sub_colour`, `prod_gapSq_ne_zero`), for every `m ≥ 1`.
  The worked cases `ψ_7` and `ψ_9` and the spanning-tree reading `m²/m = m` (Kirchhoff's
  matrix-tree theorem, not in Mathlib) stay checked, not formal. (k) is discharged;
- (l) the time boundary: `diag(1, r)` in `(Re, Im)`, the action conserved, and the pumped mode as
  its case. Formal-checked the same day in
  [`Physics/TimeBoundary`](../../lean/HolonicsResearch/Physics/TimeBoundary.lean), with
  non-expansion for `0 ≤ r ≤ 1`, conjugation as time reversal and the time mirror at `r = 0`. The
  same file proves the step's norm, `max(1, |r|)` (`timeBoundary_normSq_le`, attained by
  `timeBoundary_norm_attained`), and expansion for `r > 1` (`timeBoundary_expands`). (l) is
  discharged;
- (m) the dilation current: `∂_μ(x_ν T^(μν)) = T^μ_μ + x_ν ∂_μ T^(μν)`, beside the angular current in
  `Physics/ReceiverStressEnergy`. Formal-checked on October 26 in
  [`Physics/DilationCurrent`](../../lean/HolonicsResearch/Physics/DilationCurrent.lean)
  (`dilationDivergence_expansion`, `dilationDivergence_of_conserved`,
  `dilationDivergence_eq_zero_iff`), with the perfect fluid's trace `−ρ + 3p`
  (`perfectFluid_stressTrace`), radiation traceless and keeping dilation
  (`radiation_traceless`, `radiation_dilation_conserved`), dust reading `−ρ` and the charge at rest
  `D^0 = −x^0 ρ`. (m) is discharged;
- (n) the two compressions: `Tr ζ_n^j = c_n(j)`, `Tr ζ_n = μ(n)`, and the layer trace of the
  `p`-tower; `N(1 − ζ_n) = ∏_(d|n) d^(−μ(d))`. The norm half, `N(1 − ζ_n) = e^(Λ(n))`, is
  `cyclotomic_eval_one_eq_exp_vonMangoldt` in the same file. `Tr ζ_n = μ(n)` is
  `trace_primitive_colour` in [`Mathematics/ColourTrace`](../../lean/HolonicsResearch/Mathematics/ColourTrace.lean),
  and the same file proves the rest the same day: the Ramanujan sums `c_n(j)` (`ramanujan_sum`, from
  `sum_nthRoots_pow`), the layer trace (`layer_fixes_below`, `layer_trace`) and the sum of the
  traces of every order up to `N`, which is the Mertens function `M(N)` (`sum_traces_eq_mertens`).
  The product form `∏_(d|n) d^(−μ(d)) = e^(Λ(n))`, and `= Φ_n(1)` for `n ≥ 2`, is
  `prod_divisors_zpow_neg_moebius` and `prod_divisors_zpow_neg_moebius_eq_cyclotomic` in
  `Mathematics/OrbitEnergy`. (n) is discharged;
- (o) the Fibonacci model set: the window `[−1, τ − 1)` in the conjugate colour gives the
  substitution's chain. The two colours' arithmetic is formal-checked on October 26 in
  [`Mathematics/FibonacciModelSet`](../../lean/HolonicsResearch/Mathematics/FibonacciModelSet.lean):
  `τⁿ = (L_n + F_n√5)/2` and `τ′ⁿ = (L_n − F_n√5)/2` (`goldenRatio_pow`, `goldenConj_pow`), the
  norm `L_n² − 5F_n² = 4(−1)ⁿ` (`lucas_sq_sub_five_fib_sq`), the hidden colour contracting
  (`hidden_shrinks`, `hidden_tendsto_zero`), and the inflation `a ↦ ab`, `b ↦ a` multiplying the
  chain by its root with `F_(n+1)` long and `F_n` short tiles (`gaps_inflate`, `count_iterate`,
  `tile_count`), so one word measures `τⁿ⁺¹` seen and `τ′ⁿ⁺¹ → 0` hidden
  (`hidden_length_tendsto_zero`). The window statement itself is since discharged in #410 in the
  same file: the vertices of the chain are exactly the points `m + nτ ≥ 0` of `ℤ[τ]` with
  `m + nτ′ ∈ [−1, τ − 1)` (`vertices_eq_model_set`), the chain read in the hidden colour as a walk
  that inflation multiplies by `τ′` (`legal_inflate`).

Atlas rows:
- `colour.orbit-energy`;
- `colour.ring-spectrum-orbits`;
- `colour.dilation-symmetry`;
- `colour.colourless-faces`;
- `wave.time-boundary`;
- `wave.gap-exchange-mass`;
- `gr.dilation-current`;
- `hodge.colourless-classes-weil`;
- `colour.trace-compression`;
- `colour.colour-tower`;
- `quasi.fibonacci-model-set`.
