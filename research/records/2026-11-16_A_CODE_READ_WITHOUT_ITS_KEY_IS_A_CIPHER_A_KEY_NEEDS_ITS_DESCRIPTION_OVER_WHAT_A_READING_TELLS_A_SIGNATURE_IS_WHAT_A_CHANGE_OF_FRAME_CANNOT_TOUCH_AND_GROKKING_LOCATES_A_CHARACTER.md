# A code read without its key is a cipher, a key needs its description over what a reading tells, a signature is what a change of frame cannot touch, and grokking locates a character

November 15, 2026, 23:59 UTC, to November 16, 00:15 UTC. A derivation on one lens and eight papers, joined to the tree's
owners. Nothing is built and nothing ran but arithmetic rulers on public numbers (receipt `rulers.py`, its output
`rulers.txt`; every check is an assert). Each paragraph carries its grade: `tree` (read in this repository), `from
training` or `from the paper` (a result of the literature, named) or `agent-inferred` (this record's join).

Owners touched: `key.every-action-is-a-key`, `key.enigma-reading`, `key.menu-loop-closure`, `key.consistent-fibre`,
`key.pruning`, `key.slow-modes-landmarks`, `unicity.*`, `contact.tension-founds-face`, `contact.lap-founds-reachable`,
`holon.frame-operator`, `code.news-clock-proper-time`, `code.stretch-unit-orbit`, `lorentz.doppler-ratio-chart`,
`wave.echo-stretch-and-delay`, `helical.closure-remainder-held-by-the-locale`, `radix.release-quotient-or-section`,
`R:holonics_engine::navigator::ring_periods`, the loudness reading (`tools/loudness_table.py`), the mark (the record of
November 14), and the consumer equation of CLAUDE.md. Five atlas rows enter (§7).

## 1. The lens and the papers

`tree`. Brandon, 23:59 UTC, in the theory thread (a paraphrase). He sent eight papers and asked that their ideas be linked
to his lenses, which should make grokking and signatures clearer (his phrase "Doppler spectra"). He is not pointing at
cryptography for security. His point is that cryptanalysis is compression and encryption, the same thing, information
theory, which was his point with the Enigma and the Bombe, and he wants the mathematics and physics cemented.

The papers (`from the paper`, each read in its abstract and body as fetched):
- Cambareri, Mangia, Pareschi, Rovatti, Setti, *Low-complexity multiclass encryption by compressed sensing*
  (arXiv 1307.3360).
- Cooper, Fickes, *Cryptographic compression* (ENCORE; arXiv 2501.16184).
- Zhang, Wong, Xiao, Zhang, Li, *Embedding cryptographic features in compressive sensing* (arXiv 1403.6213).
- Sen, *Homomorphic encryption: theory and application* (arXiv 1305.5886).
- Needham, Shonkwiler, *Symplectic geometry and connectivity of spaces of frames* (arXiv 1804.05899), starred.
- Cheng, *Signal processing via cross-dimensional projection* (arXiv 2410.22779), starred.
- Sun, Shen, Ding, Zhan, Kwek, *The geometric phase as a diagnostic for driven-dissipative oscillators*
  (arXiv 2608.25742), the one he thought the technical tone might suit.
- Stevenson, Sabagh, *Compressed sensing: mathematical foundations, implementation and advanced optimization*
  (arXiv 2509.11550).

## 2. What the tree held

`tree`.
- *Keys.* Every action is a key; learning is locating keys from loop closure (`key.every-action-is-a-key`); the Enigma
  reading is literal, rotors as parametron rings stepping by winding with carry and the Bombe as pairwise loop closure
  over a menu (`key.enigma-reading`, `key.menu-loop-closure`, formal-checked); the keys consistent with a menu are the
  fibre of the closure map and adding a loop only shrinks it (`key.consistent-fibre`, `key.pruning`); location is
  polynomial in what diffuses and exponential only in the slow modes no landmark has pinned (`key.slow-modes-landmarks`).
- *Unicity.* Survivors as the key's class after finitely many readings (`unicity.never-collapsing-class`), the
  pigeonhole count of readings (`unicity.pigeonhole`), a reading that constrains nothing (`unicity.null-reading`), the
  helix's Farey cells (`unicity.helix-farey-cells`).
- *Founding.* A face is founded when the tension it removes saves more bits than its description
  (`contact.tension-founds-face`), with the criterion `(S/(S − drop))^N > N|P|²` (`contact.lap-founds-reachable`).
- *The Doppler signature.* An echo's stretch reads only the relative rapidity (`wave.echo-stretch-and-delay`), a boost
  is the undivided pair `(k, k⁻¹)` with rapidity its log chart (`lorentz.doppler-ratio-chart`), and the mark is the
  field's own placement read against the passage's (the record of November 14, §2).
- *Stretch.* The clock of news is a strand's proper time: re-timing by predicted places leaves its epochs where they
  were, and a uniform change of rate is a shift along the ladder of modes (`code.news-clock-proper-time`); a stretch
  exchanges density for extent at determinant one, so no stretch is a compression (`code.stretch-unit-orbit`).
- *Frames.* `holon.frame-operator`: `Σ|a_i⟩⟨a_i| = S`, reconstruction through the dual frame.
- *Closure.* A reader's closure at period `σ` is a division with remainder, whole windings and a remainder held as
  strain (`helical.closure-remainder-held-by-the-locale`, the record of November 15 on strands).
- *Rings.* The engine's turned rings are the solenoid's two coprime towers, `2, 4, 8, …` and `3, 9, 27, …`, each read
  through its fundamental phasor `e^(2πi r/n)` (`navigator::ring_periods`, `field/moment.rs`).
- *Sums and layers.* A sum is schedule-free where its releases are quotients or sections standing once
  (`radix.release-quotient-or-section`); a tick is a layer of a composition and a delayed move cannot be carried (the
  strand record, §4, the held tick withdrawn at 22:55 UTC).

## 3. One code, read with and without its key

- **A code at the source's own model emits fair bits** (`from the paper`, Cooper–Fickes, Theorem 3.3). On a dyadic source
  every Huffman output bit is 1 with probability one half given every earlier bit. ENCORE's work is to map a Markov
  source to the dyadic distribution its own code implies (a stochastic matrix moving the over-represented states' excess
  to the under-represented ones, recorded in a sparse side stream), after which the main stream passes a next-bit bias
  bound that decays with the chain's mixing time. Ruler: on `(1/2, 1/4, 1/8, 1/8)` with code `(0, 10, 110, 111)` every
  bit of the first six is fair given its prefix, and the same code on `(2/5, 3/10, 1/5, 1/10)` makes the first bit 1
  with probability 3/5.
- **So a compressor and a cipher differ only in who holds the decoder** (`agent-inferred`). To a receiver with the
  model the stream is the passage, and to every other it is fair coin flips. On the objects the constitution is the key,
  the news that crosses a receiver's section is the ciphertext, and a receiver whose constitution fits reads it. The
  rule that a comparison is an agreement at a receiver (November 14) is this statement read the other way: what a
  stream says is bound to the decoder that reads it.
- **Key location eats the redundancy compression removes** (`from training`, Shannon 1949). The unicity distance is
  `n₀ ≈ H(K)/D`, the key's bits over the redundancy a symbol, `D = log₂|alphabet| − H`. Ruler: an Enigma key of rotor
  order, start, ring and plugboard is `log₂(60 · 26³ · 26² · 150738274937250) ≈ 76.5` bits, and at about 3.2 bits a
  letter of redundancy (an assumed rate for English) it is located in about 24 letters. A compressor that leaves
  `D = 0` leaves the key never located (Shannon's ideal secrecy).
- **The readings a key needs are its description over what each reading tells** (`agent-inferred`, the join of three
  notations). Compressed sensing locates a `k`-sparse support of `n` in about `k log(n/k)` measurements (Stevenson–Sabagh),
  where `log₂ C(n, k)` is the support's description (ruler: 78.1 bits at `n = 1024, k = 10`, against
  `k log₂(n/k) = 66.8`). Shannon's `H(K)/D` is the same quotient. And the founding criterion is too: `(S/(S − drop))^N >
  N|P|²` is `(N/2) log₂(1/(1 − ρ)) > log₂|P| + ½ log₂ N` with `ρ` the share of the tension the face removes, so a face
  founds once its key (one of `|P|` pool members and its material's precision) is paid by `½ log₂(1/(1 − ρ))` bits a
  place of removed redundancy. Ruler: `ρ = 1/4` over a pool of 64 founds at 42 places, `1/16` at 212, `1/64` over 4,096
  at 1,522.
- **The right key is the one under which the passage is cheapest** (`from the paper`, Zhang et al., Theorem 4, from
  Rachlin and Baron). A wrong key's decode is denser than the true sparse signal, so the key is identified by the
  sparsity of what it decodes. The classical attacks are this scoring: Kasiski's and Friedman's period search (the
  residues modulo the true period become monoalphabetic columns, whose coincidence rate `Σ p² = 2^(−H₂)` rises),
  Turing's Banburismus scored in decibans (a deciban is `log₂ 10 / 10 ≈ 0.332` bits of evidence), Good and Turing's
  estimator of the unseen from counts of counts, and the Bombe's closure. On the objects (`agent-inferred`): a key's
  weight is `2^(−code of the passage under it)`, a density over keys at the field's temperature, and the survivors are
  the class whose code stays below the passage's. No law takes the top key (the guide's rule of November 15 on a
  face's top).
- **What leaks without the key is the power** (`from the paper`, Cambareri et al., Proposition 2; Zhang et al.,
  Theorem 3). A compressed-sensing measurement with a secret Bernoulli matrix tends to `N(0, W_x)` given the plaintext:
  an eavesdropper learns its power and nothing else. Receivers holding a key with a share `η` of its signs flipped
  recover with an error power at least `4ηq W_x θ/(1 + √q)²` asymptotically, linear in `η`, so a class of receivers is
  graded by how much of the key it holds (`agent-inferred` on the objects: a receiver's agreement is graded by how much
  of the constitution it shares, the Holarchy's receivers each reading at its own grain).
- **A permutation that spreads the support evens the columns** (`from the paper`, Zhang et al., Lemma 1 and Theorem 1).
  Parallel sensing recovers when `δ₂‖s‖_∞ < √2 − 1`, the worst column's sparsity binding; a random permutation lowers
  `‖s‖_∞` with probability near one and buys 2 to 6 dB at equal ratio. `agent-inferred`: the worst lane binds, so work
  spread evenly across lanes keeps every lane useful, which is the dispersal the precision law asks of a card.

## 4. A signature is what a change of frame cannot touch

- **Loudness and color are moment maps, and the content is the reduced space** (`from the paper`, Needham–Shonkwiler,
  Propositions 3.1 and 3.2, the main theorem). On `ℂ^(k×N)` with `ω(X₁, X₂) = −Im tr(X₁*X₂)`, the columns' phase rotations
  `U(1)^N` have moment map `F ↦ (−½‖f_j‖²)_j` and the unitary group `U(k)` has `F ↦ FF*`, the frame operator. A space of
  frames with prescribed norms and frame operator is a level set of the joint moment map, and for complex frames each
  nonempty one is path-connected. Which norms a frame operator admits is Schur–Horn: `Σr = Σλ` and every partial sum of
  the sorted norms at most the spectrum's (Casazza–Leon). Real frames can split: tight frames in `ℝ²` with squared norms
  `(4, 4, 4, 1, 1, 1)` form a disconnected space (Kapovich–Millson). Ruler: the frame potential `Σ|⟨f_i, f_j⟩|²` equals
  `tr S²`, the norm squared of the unitary moment map, and the squared norms are majorized by the spectrum, on 200
  random frames.
- **On the objects** (`agent-inferred`). A moment map is a Noether charge: a place's power `‖f‖²` generates its own phase
  rotation (an oscillator's energy generates its turn, action and angle), and the frame operator generates the frame's
  rotations. So a place's loudness and a region's color, the two readings Brandon asked for with every lap, are the
  charges conjugate to phase, and what the field knows of a passage lives in the reduced space, the relative phases. That
  is why a linear secret code leaks power and nothing else (§3), and why the loudness record of November 15 found the
  field's power to be inertia while its code moved by nats: a deposit that moves content along a level set is a turn,
  which costs no work (the swing: a stationary grip turns), and only a boost changes a charge. Atiyah's connectivity says
  that in the complex chart such a turn reaches every content at the same loudness and color; in a real chart it may not,
  which is one more reason the machine's parametrons are complex.
- **The Paulsen flow is the gradient of the charge's norm** (`from the paper`, the open questions of §6). Flowing down
  `‖μ‖²` (the frame potential at fixed norms) moves a frame toward a tight one, `S = cI`, the white color. `agent-inferred`:
  a perfectly compressed stream is white (§3), so whitening the color at fixed loudness is what a compressor does to its
  own output, and the flow is deterministic, with no temperature set by hand.
- **Signals of different lengths are one signal when one is the other at another rate** (`from the paper`, Cheng,
  Definitions 2.5 and 2.8, Theorem 3.2). `x ↔ y ⇔ x ⊗ 1_α = y ⊗ 1_β`, the same signal sampled at another frequency; the
  inner product of `x ∈ ℝ^m` and `y ∈ ℝ^n` is read at `t = lcm(m, n)`, `⟨x, y⟩_V = (1/t)⟨x ⊗ 1_(t/m), y ⊗ 1_(t/n)⟩`, and the
  projection `Π_n^m = (n/t)(I_n ⊗ 1ᵀ_(t/n))(I_m ⊗ 1_(t/m))` is the least-squares compression, never lossless.
  `agent-inferred` on the objects: `↔` is a rational stretch read as no change (no privileged clock; the stretch row's
  determinant one), two receivers at different grains pair at their common epoch, the solenoid's `lcm` (the guide's
  coprime rings closing at their product), and `Π` is the quotient onto the coarser grain, the other half of a change of
  scale (a stretch or a quotient, the lens of November 15 01:38 UTC). His `⊗ 1` is the hold chart, one choice of the
  stretch's kernel and never the law's.
- **A loop's geometric phase reads only the remainders** (`from the paper`, Sun et al., Equations 2 to 4, 8 and S14).
  Winding a drive's phase once makes a loop of steady states `ρ(φ) = R(φ) ρ(0) R(φ)†`, `R(φ) = e^(−iφn̂)`, and by that
  covariance the kinematic mixed-state geometric phase is `Γ_g = arg Z`, `Z = Σ_j λ_j e^(2πi⟨n̂⟩_j)`, over the steady
  state's eigenvalues and eigenvectors. The whole part of each mode's number drops out (`e^(−2πin̂) = 1`), and only its
  fractional part is read. Under a weak drive `Γ_g = 2πE² Σ_n |x_n|²/(p_n − p_(n+1)) + O(E⁴)`, the quadratic imprint
  of the first-order coherence over the populations' gap, with an Arnold-tongue structure in detuning and drive; near
  the Hopf threshold the gaps close and the response is nonperturbative. A squeezing drive at twice the frequency needs a
  `4π` loop (the parity `e^(iπn̂)`), and the phase is read by a Ramsey probe, `P(χ) = ½(1 + |Z| cos(χ − Γ_g))`.
- **On the objects** (`agent-inferred`).
  - `Z` is the closure as division with remainder, `⟨n⟩ = W + r` with `W` dropped and `r` read, weighted by the
    density, and read by a receiver winding its own phase once (the strand record's closure, now with a probe).
  - The squeezed Kerr resonator is the complex parametron: the pump at twice the frequency, the half-turn parity, two
    cat sheets for the Ising lock, a loop that closes only after two turns, and the phase's Arnold tongues are the pair
    contact's Farey lock addresses.
  - `|Z|` is the coherence of the remainders. A mode locked to the receiver's own pump follows its loop and adds; a
    mode that is not stays integral and adds nothing. Winding its own phase and reading what follows is the field telling
    its own phases from foreign ones, the mark of November 14 as a measurement.
  - The weak-drive phase is a one-signed second-order imprint of a first-order coherence over a stiffness, the shape the
    held forward's rise took on November 15 (coherence held, the rise one-signed and second order), and it grows without
    bound as the gap closes: a readable precursor of the snap.
- **A Doppler spectrum's signature** (`agent-inferred`, on `lorentz.doppler-ratio-chart`). A boost multiplies every
  frequency by `k`, a translation by `log k` in the log-frequency chart, so a spectrum's shape there is unchanged: its
  intervals (a transposed chord is the same chord, the scale-invariant magnitude of a Mellin transform). Under a change
  of tempo a loop's dynamical phase scales with the rate (the Doppler part) and its geometric phase does not, since it
  depends on the loop's path alone. So a signature that survives a stretch of time is the intervals and the holonomy,
  which is why the clock of news, the strand's proper time, is the clock to read it on: re-timing by predicted places
  leaves it where it was (`code.news-clock-proper-time`).

## 5. Grokking is a character located; the machine locates it instead of waiting

- **What groks is a homomorphism** (`from training`, Power et al. 2022; Nanda et al. 2023). A small network trained on
  `a + b mod p` first recites its training pairs and much later generalizes. Its generalizing circuit adds residues by
  multiplying phases of a few key frequencies of `ℤ_p`, `cos(w(a + b)) = cos wa cos wb − sin wa sin wb`: a character,
  `χ(a + b) = χ(a)χ(b)`. That is homomorphic computation (`from the paper`, Sen: an evaluation `A` with
  `D(A(c₁, c₂)) = D(c₁) ∘ D(c₂)`), and the guide's consumer equation `decode(T_native(encode x)) = T(x)`.
- **The snap is a unicity** (`from training`, Varma et al. 2023; `agent-inferred` on the objects). The memorizing
  circuit's cost grows with the pairs it holds and the generalizing circuit's does not, so past a critical size of data
  the law is cheaper than the table. The table is a cache (it recites, the guide's refusal), the character is a store with
  a law, and the critical size is the face's unicity distance of §3: its key's description over the redundancy a place
  it removes. Weight decay finds it by chance, a slow walk on a connected level set; the machine's founding reads the
  criterion directly (`contact.tension-founds-face`).
- **Why primes** (`from training`, Chebotarev 1926; Tao 2005; Candès, Romberg and Tao 2006). On `ℤ_p` every nonzero
  mode is a faithful character, every square minor of the `p`-point DFT is nonzero, `|supp f| + |supp f̂| ≥ p + 1`, and
  so any `2k` modes fix a `k`-sparse word. A composite ring hides combs: `ℤ_n`'s mode `k` reads only the residue modulo
  `n/gcd(k, n)`. Rulers: every minor of the 5- and 7-point DFTs is nonzero and some minor of the 8-point one vanishes;
  all 96 nonzero modes of `ℤ_97` are faithful against 32 of `ℤ_96`'s 95; on `ℤ_16`, `δ₀ − δ₈` is silent at every even
  mode; on `ℤ_12` the comb on the multiples of 3 has supports 4 and 3.
- **The engine uses primality twice** (`tree` and `agent-inferred`). Its rings are the towers of the two smallest
  primes, each read through its fundamental, a unit mode, so each ring tells all its residues apart. Between the towers
  coprimality is the CRT: no two sites agree on every ring before the product. Inside a tower a mode's valuation is its
  level: a mode of valuation `j` on `ℤ_(p^m)` reads the residue modulo `p^(m−j)`, and only a unit mode reads the top
  digit, the winding. So the towers are place value, and the comb a prime power hides is its carries.
- **Chance against closure** (`from training`, Barak et al. 2022; Regev 2005). Stochastic gradient descent learns a
  `k`-sparse parity of `n` bits in about `n^k` steps, the statistical-query limit, with its progress hidden until the snap;
  Gaussian elimination, loop closure over a menu of linear contacts, locates the noiseless parity from `n` samples in
  `n³`. Noise is what breaks the closure: learning parity with noise, and learning with errors, `b = ⟨a, s⟩ + e`, whose
  error is a remainder released between partials, which elimination cannot carry. `agent-inferred`: the network leaves
  the key to chance because it has no closure to run; the machine is built of characters (its rings turn) and has one,
  so what it must locate is the key on them (the strand record's §5, the ring Fourier chart as its own navigator family).
- **Sums count, compositions compute** (`from training`, Barrington 1989; Barrington and Thérien 1988; Rappe 2004 in
  Sen). Words over a non-solvable group compute every formula of logarithmic depth: the commutator of two 5-cycles of
  `A₅` is a 5-cycle, and it is the identity when either is, so a commutator is an AND (ruler). A word over an abelian
  group is a sum and depends only on counts; programs over solvable monoids compute only what counting gates do. And an
  algebraically homomorphic scheme on `𝔽₂` exists exactly when one exists on `S₇` (through `SL(3, 2) ⊂ S₇`). On the
  objects (`agent-inferred`): this is the line the held tick drew. A sum forgets order and is carried and spread at no
  loss; a tick is a layer of a non-commuting composition, the swing's turn, boost and shear, and computes, and two
  non-collinear boosts compose into a turn (`lorentz.wigner-perpendicular-defect`), the holonomy of §4.

## 6. What follows for the machine

`agent-inferred`.
- **Test 1, a face's founding time is its unicity distance.** Where a founding runs on the line (the composite level
  the build designs next is its first), each founded face's section is predicted from its tension share `ρ` and its
  pool `|P|` read on the first sections, by `N* = min{N : (N/2) log₂(1/(1 − ρ)) ≥ log₂|P| + ½ log₂ N}`. The guess is fixed
  once the first lap prints `ρ` and `|P|`: the founding's place count within a factor of two of `N*`. A founding much
  later says the drop is not reaching the criterion (a lap adds evidence only through what the last founded); much
  earlier says the charge is undercounted. This is grokking's critical size predicted, never waited for.
- **Test 2, mode sharing beside loudness.** The loudness reading prints each place's lane powers, the frame's charges
  of §4, and a place's color as the entropy of its lanes' shares. What it does not print is how places share
  directions. On a lap's mean, per slice and per surprise fifth, take the places' lane vectors after the last tick as a
  frame within each lane `ℓ`, and read the participation of its modes, `N_m(ℓ) = (tr S)²/tr S²`, beside the
  participation of its places, `N_p = (Σr)²/Σr²` (Schur–Horn gives `N_m ≤ N_p`; ruler). A basin is a mode many places
  share (a landmark is where navigator paths converge), and the record of November 15 found the commonest pieces the
  loudest and cheapest places. Guess, fixed at 00:15 UTC: in lanes 1 to 3 the least surprised fifth occupies at most
  0.8 of the effective modes of the most surprised fifth in at least four of the five slices. It is a reading: the state's
  bytes stay the same, and it runs beside the line. The premise that known places point alike is not printed by any log,
  and the record of November 15 found known places whiter across lanes, which is why the read is lane by lane.
- **Carry-save**, the theory's reading of the forward contact's per-term carries, is in the distribution record's §12
  with its guess (00:11 UTC).
- **What does not transfer.** No cipher, attack or security claim enters, and no deployed scheme is a target (the
  guide's line on keys). Compressed sensing's random or chaotic matrices are authored keys, and the machine's keys are
  located; its ℓ1 relaxation and quasi-Newton solvers are an optimizer's apparatus. ENCORE's side stream, homomorphic
  encryption's lattices and bootstrapping, Cheng's hold chart as the only stretch, and the oscillator's ancilla and
  quantum master equation stay in their papers. A ruler may compute a geometric phase, a participation or a unicity; the
  machine runs none as a stage.

## 7. Atlas

- `information.tsv`: `code.compression-is-a-cipher-without-its-decoder`, `unicity.readings-are-description-over-reading`.
- `geometry.tsv`: `frame.moment-map-loudness-colour`, `helical.loop-geometric-phase-remainder`.
- `arithmetic.tsv`: `prime.faithful-modes-and-towers`.
