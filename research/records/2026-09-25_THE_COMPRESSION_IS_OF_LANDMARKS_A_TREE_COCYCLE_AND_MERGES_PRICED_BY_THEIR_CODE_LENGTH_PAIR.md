# The compression is of landmarks: a tree cocycle, and merges priced by their code-length pair

[historical] Brandon, September 25, after campaign 1's located failure. He said the exact
enclosures "ultimately mean nothing on their own", and that he prefers "the algebra and the
geometric addressing". On compression: "The way you'd naively say 'cache', it's more like a cocycle
in a natural autogradient, ideal for machine learning and what you call 'keys' and 'windows'; it's
that the compression is of landmarks connecting generators, like aligning charges of lightning,
when relevant they expand and are open for a time. Compression is really important." And:
tokenizers and BPE are "more primitive instances of this, like partials without complete
mathematics. Code length pairs, parts of helices and toroids." Codex GPT-6 Sol derived both
answers; this record keeps their law and their corrections.

## 1. Landmarks form a tree, and one path is open per cell

[definition; agent-inferred] The address words of a fractal navigator form a tree. A child
restricts its parent by one more letter (the newest cell, a binary odometer digit, a ring's phase
class); the fine-to-coarse restriction is the scale square. A landmark is a node where many
navigator paths converge. At each cell the current address opens one path, from the root to the
deepest founded landmark it reaches: the leader. Only the landmarks on that path are read and
deposited. A landmark is founded at first arrival, and it stays stored and unread while no address
opens it.
- [conditional] Calling a shared node a landmark in the elementary objects' sense needs its
  receiver face to certify convergence of the participating paths. A shared spelling alone does
  not establish it.

## 2. The weighting along the path is the compression

[proved-standard] Context-tree weighting (Willems–Shtarkov–Tjalkens 1995). Each landmark `s`
holds KT masses `C_s(c) = n_s(c) + 1/2`, with face `k_s(c) = C_s(c)/Σ_a C_s(a)`. Its weighted
likelihood is
- `W_s = E_s` at the maximum depth, and
- `W_s = ½E_s + ½ ∏_b W_(bs)` above it.

The prediction on the opened path composes as
`q_s(c) = λ_s k_s(c) + (1 − λ_s) q_(bs)(c)`, with `λ_s = E_s/(E_s + ∏_b W_(bs))`.
- KT likelihoods compose across observations.
- Child likelihoods multiply across disjoint routed subsequences.
- The stop and split alternatives add.
- Predictions are successive likelihood ratios.

The excess over the best fixed tree source is bounded algebraically, not measured: the model cost
`Γ_D(S)`, plus each leaf's parameter cost, which grows as half the logarithm of its count.

[proved-derived] **The cocycle.** On the opened path the edge ratios are
`R_(s→bs)(c) = q_(bs)(c)/q_s(c)`. The code length at the root telescopes through them to the
deepest landmark: an additive one-cochain on the path. The sequential code length also adds
across receiver crossings, by the chain rule.
- [correction, Sol] Changing the tree's prediction at a fixed arrived source supplies the first
  law's **deposition** term, `−Σ_c p′(c) log(q′(c)/q(c))`, not its exchange term. A tree has no
  two-cell on which a coboundary could be the exchange.

[proved-derived] **The local autogradient.** Each positive edge ratio has
`d log R = R⁻¹ dR`, and a deposit changes only the opened path. The learning covector is local:
counts, posterior weights and likelihood ratios, with no differentiation through a network.
- [correction, Sol] It is a natural gradient in the Fisher sense only once a metric is supplied.
- CTW alone does not locate a helical pair key.

## 3. Open and released

[definition applied] A landmark's distinct representation is released only when every admitted
future address, action and receiver read gives the same face without it (the retention law). A
storage budget alone gives no exact eviction rule. An aeon collapse takes the tree's future
quotient and keeps the active address, the applicable masses and the clock's carry; it does not
reset masses because an aeon ended.

## 4. Geometric addressing, and what the wave contributes

[agent-inferred] The address is typed and ordered:
- causally available preceding cells, with their binary odometer digits and carry;
- declared ring phase classes;
- key-located configurations, paid for when they enter a coding address.

The restriction order gives each mixed address one parent, so the scale square commutes. The wave
earns its computation by supplying phase or lock addresses that the tree weights in. A wave
correction to the count logits is a separate hypothesis, measured against the count-only face.
- [image] "Charges aligning like lightning" becomes a derivation only through a map from the
  pair contact's slip, phase transport and reached deposition to these addresses and faces.

## 5. Merges: tokenizers with their complete mathematics

[proved-derived] A merge `c ↦ ab` founds a reusable landmark word and contracts each selected
two-edge presentation into one. For a decoder `G` with symbol word `z` and the merged `G′, z′`
(same source, same boundary conventions), the complete descriptions are
- `K_old = |code(G)| − log₂ W_G(z)`, and
- `K_merge = |code(G′)| − log₂ W_(G′)(z′)`.

With `d = |code(G′)| − |code(G)|`, the merge is accepted exactly when `W_(G′)(z′)/W_G(z) > 2^d`,
an integer comparison once positive denominators are cleared. This is the code-length pair. It
prices the rule, the changed alphabet, every changed context and the encoded word.

[proved-standard; scope] Grammar-based MDL seeks the shortest decodable pair `(G, z)` with
`D_G(z) = x` (Kieffer–Yang 2000 prove universality for specified grammar-based codes, not
optimality of greedy pair choice). Re-Pair (Larsson–Moffat 2000) and Gage's BPE share the pair
operation.

[conditional] **Frequency as a proxy.** Pair frequency orders candidates by code gain only when:
- every counted occurrence is replaceable without overlap;
- every replacement saves the same bit length;
- rules cost the same;
- the changes to other contexts are equal.

Then the gain is `m·g − d`. Adaptive tree probabilities, unequal rules or overlaps break the
order. BPE's frequency is a proposal, not the acceptance equation.

[derived] **One source, several alphabets.** Bytes, token words and phase addresses are readings
of one source, so their likelihoods are never multiplied as independent evidence. The source's
mass is the segmentation-lattice sum `P_G(x) = Σ_(z: D_G(z) = x) P_G(z)`, and
`−log₂ P_G(z) = −log₂ P_G(x) − log₂ P_G(z | x)` prices a transmitted parse once. Kudo's unigram
tokenizer weights this lattice. The byte path is always the lossless fallback.

[image until derived] **Helices and tori.** The offset-one pair table (`HNN/IndexedOpen`) gives
the pair an oriented geometric address. A literal lock of two helices into one ring needs:
- the zero-slip pair contact `q v_a = p v_b`;
- both clocks' lifts and carries through the ordered pair;
- a common period where closure is claimed;
- the combined ring's storage, pump and receiving law;
- the encoding square `E_next T_ab = U_ab E`, or a retained separator.

[correction, Sol] A merge that stops shortening the code is not thereby releasable. Release needs
decoder and future-action equivalence, and a rule still referenced across an aeon collapse must
remain decodable.

## 6. What is built, and in what order

[agent-inferred] Decision 28 (THE_REBUILD) takes this as the receiving face's compression law:
- Decision 27's region table is the tree's forced-split depth-one case (ordinary CTW at that depth
  also mixes in the root's context-free face);
- the count-only tree face is built and measured first, then phase addresses, then any wave
  correction;
- merges, grammars and segmentation lattices belong to campaign 5, beside `HNN/Encoding`.

The receipts are strict orderings on the unchanged held-out cells, each decided by disjoint exact
enclosures or a sign certificate:
- the tree below online order-0, below order-1 and below PPM-2;
- with words, below the tree over bytes as well.

None is measured yet. The Lean statements are listed with Decision 28.
