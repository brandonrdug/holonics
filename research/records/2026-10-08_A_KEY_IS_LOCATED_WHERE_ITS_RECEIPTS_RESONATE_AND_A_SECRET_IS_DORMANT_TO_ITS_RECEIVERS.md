# A key is located where its receipts resonate, and a secret is dormant to its receivers

**Date.** October 8. **Issues.** #73, #148, #62, #63. **Grade.** Lens record. Each section carries
its own grade. The derivations in §2 and §3 are proved here; the rest are definitions or readings,
with their owners named.

## 1. The lens

Brandon, October 8: a song that matters is made by knowing what its listeners listen for; a lock is
opened by knowing what kind of key it expects and converging into it; the right words, a solved
problem and a recovered dead language are the same act, the differentiating and integrating of a
composition's constituents. "Resonating physics, dynamic geometry, asymmetric potentials. That's
everything." The Enigma/Bombe reading in the guide is literal: learning is locating keys.

[definition; agent-inferred] **The one object.** In every case there is an unknown source word (the
key: a composition of constituents), a family of receivers that read it lossily, each in its own
clock and grain (an inscription, a listener, a deletion, a projection, a noisy channel), and their
receipts. Reconstruction locates the key modulo the kernel of the admitted receivers
(`compression.kernel-greatest-invariant`, Lean `Foundation/CausalRelevance:futureCollapsed`): the
differences no admitted receiver distinguishes. Three operations do it, and they are the lens's
three words:

1. **Resonance** chooses what to read: the receipts' phase-carried moments, at the phases where the
   candidate keys' differences are not silent.
2. **Dynamic geometry** is how each receiver moves the reading: its transport of the source's phases
   into its own clock.
3. **The asymmetric potential** is how the reading converges: the comparison `ℓ = log R`, asymmetric
   in its two participants, whose covector `R⁻¹dR` is the descent, plus loop closure, which prunes
   the keys a receipt rules out.

## 2. The deletion receiver, exactly

[proved-derived] A source `x = (x_0, …, x_{n−1})` over a ring of constituents has the generating
polynomial `P_x(z) = Σ_k x_k z^k`. The deletion receiver `D_p` keeps each position independently
with rational retention `p ∈ (0, 1]` (`q = 1 − p`) and returns the survivors in order, the trace
`Y`. Then

```text
E[ Σ_j Y_j w^j ] = p · P_x(q + p w) = p · P_x(1 + p (w − 1))
```

*Proof.* `Σ_j Y_j w^j = Σ_k x_k · 1[k survives] · w^{N_k}`, where `N_k`, the survivors among the
positions before `k`, is binomial `(k, p)` and independent of `k`'s own survival. So the expectation
is `Σ_k x_k · p · (q + p w)^k`. ∎ Every coefficient is exact for rational `p`.

[proved-derived] **The receiver's clock and transport.** A trace index counts survivors: it is the
receiver's epoch count, the flux through its section (the aeon record), not the source's tick. The
transport `T_p(w) = 1 + p (w − 1)` is the homothety of ratio `p` about the fixed point `1`, a boost
toward `1`. The transports compose by multiplying retentions, `T_{p₁} ∘ T_{p₂} = T_{p₁ p₂}`, so the
deletion receivers form a one-parameter boost flow. The unit circle `|w| = 1` goes to the circle of
centre `q` and radius `p`, tangent to the unit circle at `1`. Every deletion receiver's circle passes
through `z = 1`: it is a landmark, the face where all the receivers' paths converge.

[proved-standard] **Resonance decides.** Two candidate keys differ in mean receipt by
`p · P_{x − x'}(T_p(w))`. They are separated only where the difference polynomial is not silent on
the arc that the receiver's circle reads near the landmark. A polynomial with coefficients in
`{−1, 0, 1}` cannot be silent on an arc of the unit circle (Borwein–Erdélyi 1997), which gives
`exp(Θ(n^{1/3}))` traces for mean-based reconstruction (De–O'Donnell–Servedio 2017; Nazarov–Peres
2017). Multi-symbol statistics, several phases at once, give `exp(Õ(n^{1/5}))` (Chase 2021). The
public OpenAI catalogue's family 122 states an `n^{Ω(log log n)}` lower bound and a quasipolynomial
decoder; these are its claims and were not checked here. The catalogue lists family 122 and then
124 (three-machine scheduling), with no 123 between them. Brandon's item 123 (October 9) is that
omitted slot: an information-reconstruction item to engineer, whose transfer to scheduling stays
exploratory until a concrete operation joins them. The opposite pole is the flat spectrum:
binary sequences that resonate nowhere (that catalogue's families 076, ultraflat Littlewood
polynomials, and 179, Barker sequences) are the keys that no first-moment reading locates.

## 3. Convergence: the likelihood, the relaxed key and its covector

[proved-derived] **The likelihood counts embeddings.**
`Pr[Y = y | x] = p^{|y|} q^{n − |y|} · N(x, y)`, where `N(x, y)` is the number of index sets `I`
with `x_I = y`: each deletion pattern is an index set of survivors, of probability
`p^{|I|} q^{n−|I|}`, and it returns `y` exactly when `x_I = y`. `N` counts the monotone paths of
the alignment lattice (source position × trace position), a diagonal step allowed only where the
symbols agree. That lattice is a pair contact whose slip is the deletion: a path follows the line
of slope `p` and wanders from it binomially.

[proved-derived] **The covector on a relaxed key.** Hold the key as per-position class masses
`s_i = softmax(λ_i)`, a soft constituent. The relaxed count `Ñ(s, y)` is multilinear in each `s_i`:
`Ñ = A_i + Σ_b s_i(b) B_{i,b}`, where `A_i` collects the paths that delete position `i` and
`B_{i,b}` the paths that read `b` there. With `r_i(b) = s_i(b) B_{i,b} / Ñ` (the posterior mass that
`i` survives and reads `b`) and `ρ_i = Σ_b r_i(b)` (its survival posterior),

```text
∂ log Ñ / ∂ λ_i(a) = r_i(a) − ρ_i · s_i(a) ,      Σ_a ( r_i(a) − ρ_i s_i(a) ) = 0
```

which is the guide's covector `q − p̃` on the surviving part: the observed (posterior) class mass
less the predicted mass, scaled by survival. The forward–backward sum over the lattice is the
integration over alignments, and this log-derivative is the differentiation. The lens's
"differentiating and integrating constituents" is exactly the passage and its adjoint. The
comparison is asymmetric (`D(p‖q) ≠ D(q‖p)`), and which side is the receiver decides the descent.

[definition] **Loop closure prunes.** The Bombe reads a menu: crib letter pairs as edges, each the
scrambler at its offset. A hypothesized key (the rotor order and position, the navigators' initial
configuration) is propagated around the menu's loops, and a contradiction removes it. The
survivors, its stops, are the preimage fibre. Welchman's diagonal board propagates the plugboard's
involution, and the reflector makes the whole cipher an involution: the Swing's half-turn
(`swing.half-turn`, Lean `Geometry/AffineSwing:theSwingIsAnInvolution`). Decipherment is the same
procedure: Kober's inflectional triplets are traces of one stem, Ventris's grid locates consonant
and vowel classes by loop closure across inscriptions, and the place names were the cribs that
fixed the key. Computational decipherment (Snyder–Barzilay–Knight 2010; Luo–Cao–Barzilay 2019, by
minimum-cost flow) runs alignment with a relaxed descent.

## 4. A secret is dormant to its receivers

[definition; agent-inferred] A construction is **secure against a receiver family `𝓡`** when every
key-dependent difference of its output lies in the kernel `K_𝓡` (every admitted receiver's face
agrees, at the declared advantage). **Learning** is enlarging `𝓡` by located resonances until the
relevant differences leave `K_𝓡`. Pseudorandomness is indistinguishability by a receiver class;
learning with errors and learning parity with noise are learning problems whose hardness is the
cryptographic assumption; parities have flat spectra and are invisible to correlational
(statistical-query) receivers; noise-cancelling sample combinations (Blum–Kalai–Wasserman) resonate
them out. Cryptography and machine learning are one law read from its two sides: dormancy and
resonance relative to a receiver family. Nothing here pursues a cryptanalytic application, and
nothing needs one.

[reading] **Music.** A pitch class is a phase on the circle and the octave its carry (a helix).
Key-finding is resonance on that circle: the phase of the pitch-class profile's fifth Fourier
coefficient places the diatonic collection on the circle of fifths (Quinn 2006; Amiot 2016). What
listeners listen for is their receivers' learned constitution. A song that matters places its
surprise at their grain, which is cross-entropy at their face, the news.

## 5. What the repository already owns, and what it measured

- Exact loop-closure key location, the Bombe's form: the turn menu (`hnn.turn-menu-fibre`,
  `compression::keys::TurnMenu`; the rotor's turns as stages, the fibre read from the menu
  relation's cycles and cosets), pair location over the span's distances (`hnn.pair-location`),
  the located transport (`compression.located-transport`), and local keys glued on a cover in the
  tower's trichotomy (`compression.local-keys-glue`).
- Repair as the key read the other way: two-sided restriction (`compression.pair-repair`), which on
  a forest reaches the joint fibre's projection (Lean `Transport/ForestRestriction`).
- Measured. On known-truth terrains, every released erased cell was right (1,088 of 1,088,
  [repair by reflection](2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md)).
  On text, every distance's turn menu lost its stationary turn within 4 to 12 edges and nothing was
  located ([the same path on text](2026-10-05_THE_SAME_PATH_ON_TEXT_KEY_LOCATION_AND_THE_RELEASE_ON_THE_BYTE_CHART.md)),
  and glued local keys released 11 of 768 erased cells, all 11 right, holding the rest
  ([text repair](2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md)).
- The source's phase-carried moments, the receiver clocks, the kernel, the half-turn, the preimage
  fibre and the deposition covector are all built (keystone mapping, mailbox reply of October 8).

[agent-inferred] **What the lens reads in that measurement.** Exact loop closure is the Bombe's
form, and it empties under deletion and noise: one wrong edge contradicts a whole menu, so the text
fibres empty. Trace reconstruction shows the other form of the same location: statistical resonance
over many receipts, plus descent on a relaxed key, degrades gracefully where exact survivors vanish.
The repository locates keys only in the exact form. The statistical form is the missing operation:
key location by resonance across a receiver family with soft constituents.

## 6. The joins owed

1. A native deletion receiver: its clock (survivor epochs), its transport `T_p`, and the moment law
   of §2. **The Lean is kernel-checked** (`formal-checked`; `Transport/DeletionReceiver` at
   `d5f7c140b`, [receipt](receipts/2026-10-09-deletion-receiver/PUBLICATION.md)). It covers:
   - the clock law `expect_pow_length` and the moment law `expect_genPoly`;
   - the transports composing (`transport_comp`) and the channels composing for every reading
     (`expect_expect`);
   - the likelihood with its embedding count (`expect_trace`);
   - the covector `r − ρ s` (`covector_column`, `covector_sum_zero`).
   The native receiver in Rust stays owed, with its consumer (item 2).
2. The trace likelihood as the machine's own pair-contact passage with slip, its forward–backward as
   passage and adjoint, and its covector `r − ρ s` deposited by the existing law. This must not be an
   authored decoder (the catered-machinery antipattern): the alignment lattice is the pair contact's
   own passage.
3. Resonant key location: the located keys' receiver family enlarged by phase readings at the
   receivers' landmarks, with soft keys, beside the exact turn menus.
4. The security–dormancy statement as a definition-level join on `futureCollapsed`, with its
   quantitative pole (Fourier flatness) owed in #62.

**Acceptance for the first loop** (fixed before any build): a known-truth terrain of sources and
deletion traces, generated by exact routines. The HNN locates the source through its own receivers
and deposition; the reading is exact recovery against the number of traces at declared `n` and
`p`, on unseen sources, beside the mean-based count of §2. No authored decoder, and no cryptanalytic
target.

**Recorded failures checked.** An authored routine standing in for learning (item 2 is the risk,
named). Seen material graded as unseen (the acceptance reads unseen sources only). Text run as the
exception (the deletion receiver is modality-free: symbols, notes and samples alike). Bits read as
progress (the reading is exact recovery, not code length).
