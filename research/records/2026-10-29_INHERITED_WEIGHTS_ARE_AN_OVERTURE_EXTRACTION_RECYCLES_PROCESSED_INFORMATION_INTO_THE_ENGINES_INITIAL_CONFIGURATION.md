# Inherited weights are an overture: extraction recycles processed information into the engine's initial configuration

Refs #146 #404 #409. Status: [project-postulate: Brandon's lens, October 29; definition and joins
agent-inferred]. Claude (opus). Brandon's words are paraphrased; they stay in the conversation.

## 1. The lens

Brandon unparked equation extraction on October 29 and said what it is for. An open model's weights
are information, its initial parameters, and nothing more. They are an overture: broken, unfinished
melodies and harmonies that the engine takes up. A brain on its own is not the being; the being is
the active equilibrium of the whole organism, an engine or a star. So the weights are never the
model. Extraction recycles information that has already been processed to some degree, so that it
does not go to waste, and the engine carries the full responsibility for expressing intelligence.
The name "Soulkiller" is incidental.

What poisoned the October 28 Codex conversation was the opposite reading: a served model (Ollama)
supplying Athena's language, and an inference workspace that graded itself by parity with the
source model's logits. Both treated the weights as the model.

## 2. The law

[definition; agent-inferred] **Extracted coefficients enter as an overture.**
- They enter once, at the exterior boundary, converted exactly (a quantized block's scale and
  digits become dyadic ratios with their remainder), into the initial configuration of native
  navigators and the opening constitution of native owners: founding, never a running foreign
  forward.
- From that opening only deposition changes them, from covectors that reached their loci in the
  engine's own passage. Retention stays the quotient of the constitution.
- Nothing is graded by agreement with the source model. Extraction is checked once, at its own
  boundary (the native opening reproduces the source operation it charted, to the declared grain);
  after that the engine's product is read as Athena's, with the writings whole.
- A foreign model is never served, never run inside a law, and never stands in for a receiver.

## 3. Where the overture lands

[proved-derived; agent-inferred] The tower's laws already hold every block of a decoder Transformer
as a restriction, so extracted coefficients have native owners to land in:

| Source block | Native owner, as restricted |
|---|---|
| attention head, rotary positions | participation with constant moves: `u_m = e^(iω_m)` the rotary frequencies, `W_Q, W_K, W_V` the charts `Ȟ, H, Ψ` on the rotary pairs as complex modes, `κ = 0` (`hnn::tower::participation`) |
| ALiBi-style distance slopes | the head's friction `κ` against its met dissipation |
| RMS normalization | the contacts' ratio read `r̂ = r / ‖r‖_rms` |
| gated MLP | the pair contact `(W_a r̂ + b_a) ⊙ (W_b r̂ + b_b)`; a SiLU gate is the gate law's logistic on one drive |
| residual stream | the level's join `x^(ℓ+1) = x^ℓ + W₂ v + b₂` |
| embedding and unembedding | the encoding `E` and the readout `U` |

Once seeded, what the source held fixed the engine moves: the gates key each mode's decay, the
turns and pumps key its phase and lock, the friction is learned, and the moves themselves learn. The
overture is played by an engine whose geometry is its own.

## 4. The order

Equation extraction (#146) leaves the parked list. It joins after participation's card parity, as
the overture route for the participation charts and the contacts. Its first acceptance is fixed
here:
1. Exact intake of one small open model's blocks at the boundary. The K-block decoder on
   `codex/counting-faces-20261028` (`tools/athena_model_source.py`) is the port source, moved into
   the Rust boundary codec.
2. A native tower founded from those coefficients, with its extraction check at the boundary.
3. That tower then learns on the card on the race passage beside one founded without an overture,
   lap for lap, with the writings whole.

This corrects the October 29 audit record's §3. The served model stays withdrawn; the intake is
lawful as the overture's.

## 5. Audit, October 30: what step 1 takes in, and what it leaves out

[agent-inferred] Participation's card parity passed on October 29, so the order of §4 has reached
this work. Three choices fix step 1 before it is built.
- **The intake is the exterior intake law, given a Rust owner.** The law already has its Lean owner
  (`Foundation/ExteriorIntake.decode_exact_on_finite`, atlas `receipt.exterior-intake`): a finite
  IEEE word decodes exactly to its dyadic ratio, and a nonfinite word is refused. No Rust owner
  carries it yet. The K-block decoder named in §4 sits on an unpushed branch and is not the port
  source after all: a source released unquantized needs none. A `bf16` word is a sign, an odd
  mantissa and a power of two, so its intake has no remainder, while a quantized block is a lossy
  face of the same trained weights. The source is therefore taken as released, in `safetensors`
  `bf16`, and §4's step 1 reads "the exact intake of one small open model's blocks".
- **The lexical layer is founded natively; only the interior is the overture.** The source's
  embedding and unembedding are charts of its byte-pair vocabulary, an authored tokenizer that the
  engine refuses. So the encoding `E` and the readout `U` are founded on the engine's own units, as
  every race founds them, and only the interior blocks of §3 (attention as participation,
  normalization, the gated contacts, the residual joins) enter from the source. That an interior
  carries across a re-founded lexical layer is measured in the literature: Artetxe, Ruder and
  Yogatama (2020, "On the cross-lingual transferability of monolingual representations") move a
  trained encoder's body to new languages by learning new embeddings alone. Here the interior is
  not frozen; deposition moves it from the overture.
- **The tower is declared at the source's interior shape**, or at a prefix of its layers, which is
  a lawful restriction: width the hidden size, one participation head per query head with its
  rotary pairs as complex modes, contacts the gated MLP's width, levels the layers taken. Grouped
  key and value heads enter as copies of one chart in each head that shares it; deposition then
  parts them. The first source is a small llama-shaped decoder released under Apache-2.0
  (SmolLM2-135M: by its published configuration hidden size 576, 30 layers, 9 query heads over 3
  key-value heads, MLP width 1536, rotary positions, RMS normalization, a SiLU-gated MLP, no
  biases), its configuration read and pinned at intake rather than assumed.

Step 1's deliverable is the Rust owner of the intake: a `safetensors` file's `bf16`, `f16` and `f32`
tensors decoded to exact dyadic ratios at the boundary, nonfinite words refused, with the tensor
names and shapes kept as exterior codec information only. It is checked on constructed files at
every boundary case of each format. The weights themselves stay in `.local/` and are never
committed. The card's cost for step 3 is projected from step 2's measured pass, not assumed.

**Step 1, built (October 30).** `holonics::hnn::overture` carries the intake: `FloatFormat::decode`
is the Lean `decode` over `binary16`, `bfloat16` and `binary32`, and `Safetensors::read` admits a file
whose tensors' ranges hold their shapes and tile its data exactly. Its tests decode every `bfloat16`
and `binary16` word against Lean's value computed independently, refuse exactly the all-ones exponent
field (256 and 2,048 words), check that `binary32` carries every half-width value and that `bfloat16`
is `binary32`'s upper half, and refuse each malformed file by name.

[measured; host, decoding only, no model run] The released SmolLM2-135M file at revision `93efa2f0`
(269,060,552 bytes, SHA-256 `80521b40…5da1`; the weights stay in `.local/`) reads whole in 21.9 s
through `cargo run --example overture_intake`: 272 tensors, all `bfloat16`, 134,515,008 values, none
refused and none zero. Their leading bits sit at places `−30` through `3`, so with `bfloat16`'s eight
significant bits an exact carrier needs places `3` down to `−37`. The tower's material grain is
`2^(−24)`; the attention charts reach down to place `−30` and the MLP charts to `−28`. Step 2
therefore owes the founding's grain law: the opening material either widens its carrier to hold the
overture's places, or is released onto the material grain at a declared tolerance with each
coefficient's remainder accounted. The 30 layers hold 106,202,880 of the values; the embedding's
28,311,552 (tied to the unembedding) are left behind with the vocabulary, and the final norm's 576
go with the readout that is founded natively.

## 6. Step 2's grain law, and §3 read against the tower's step (October 30)

**The grain law, decided.** [measured; host, decoding only, no model run] Released onto the tower's
material grain `2^(−24)` to the nearest, the 30 layers' 106,202,880 coefficients land exactly but
for 3,940. Of those, 3,926 keep their leading bits with a remainder below the grain and 14 release to
zero (`down_proj` 917 and 6, `gate_proj` 917 and 2, `up_proj` 933 and 1, `q_proj` 433 and 2,
`o_proj` 406 and 2, `v_proj` 164 and 0, `k_proj` 156 and 1). In every kind the remainders' summed
magnitude is between `3.3·10⁻¹²` and `4.9·10⁻¹²` of the coefficients' (a decimal reading). Both
norms' gains land exactly.

[agent-inferred] So the opening material stays on the tower's own carrier. Each coefficient
releases onto `2^(−24)` to the nearest, and the founding returns, block by block, how many
coefficients it released and their remainder. Widening the material carrier would change a law
that every level and the card share, for 0.004% of the coefficients and a remainder twelve decimal
orders below their mass. A coefficient the founding composes is released once, after the
composition, with its remainder in the same receipt. Two compositions arise: a norm's gain folded
into the chart that reads it, and the base change of the Gibbs face below.

**§3 read against the step.** [agent-inferred, read from `Tower::step` and
`hnn::tower::participation`] Three of §3's blocks are restrictions as they stand. Two more hold once
the founding chooses its modes and folds a base change. Four terms are owed.
- **Holds.** Rotary positions are constant moves of the frame that participation carries. A source
  head's 64 dimensions pair as `(m, m + 32)` (the source's rotation is not interleaved), with
  `ω_m = 100000^(−m/32)`. The native frame turns the charts back where the source turns them
  forward, so the moves are `u_m = e^(−iω_m)`. Grouped key and value heads are copies (§5). The
  friction is `κ = 0`. The MLP's down projection is the join's `W₂`. There are no biases.
- **Holds with a choice of modes.** Participation carries a value by the same relative frame as the
  probe and the key: `y_i = U_i Σ_j a_ij conj(U_j) Ψ_j`. The source's values do not turn. So a
  source head takes 64 native modes:
  - 32 rotary modes carry `Ȟ` and `H`, with `Ψ` zero;
  - 32 still modes (`u = 1`) carry `Ψ`, with `Ȟ` and `H` zero.

  The face sums over the head's modes, so the still modes add nothing to it, and the rotary modes add
  nothing to the current. The output projection is `Cᵃ` on the still modes: for a value pair `(a, b)`,
  `Cᵃ_re = O[:, a]` and `Cᵃ_im = −O[:, b]`. The tower's 576 modes hold the 9 heads.
- **Holds with a base change.** The Gibbs face is base 2, the source's softmax base `e`. So
  `2^(β Re⟨q, k⟩) = e^(qᵀk/8)` when the probe chart carries the factor `log₂ e · 2^(beta_shift)/8`.
  `log₂ e` enters as a navigator's face, released with the chart.
- **Owed (1): the charts' input.** The charts read the level's input `x` as it stands. The source's
  `Q`, `K` and `V` read it normalized, `x/‖x‖_rms · g`, a scale per site that no fixed chart carries.
  The owed term reads the input as a ratio to its own power, the read the contacts already take, with
  `g` folded into each chart. The source's `ε = 10⁻⁵` is a floor for its floats. The ratio read has
  none, and the two differ by `ε/(2 mean x²)` relative.
- **Owed (2): the attention's join.** Participation's current is read through `Cᵃ`, normalized
  again, and enters the contacts' drive through `W₁ᵃ`. The source adds `O y` to the residual. The
  owed term is the join `x ← x + Re(Cᵃ y)`.
- **Owed (3): the contacts' read.** The contacts read the modes' face `r̂ = Re(C h)/‖Re(C h)‖_rms`.
  The source's MLP reads the residual after the attention has joined it, normalized. A gated tower
  cannot make its modes transparent: `λ = 0` has no logarithm for the gate to raise. The passage join
  (`Tower::join_passage`) already lets the contacts read the passing current, `W₁ˣ x`, but only under
  a news clock, as `x` stands, and before any attention join. The owed term is that read taken as a
  ratio to its power, after the join. The modes open silent (push zero), so the opening is the
  source's operation and deposition grows them.
- **Owed (4): the gate.** The source's MLP is `silu(W_g n) ⊙ (W_u n)`; the pair contact's two
  factors are both linear. The owed law is a gated pair contact `v = a σ₂(a log₂ e) ⊙ b`, with `σ₂`
  the gate law's base-2 logistic.

With the four terms, one native level reads `x' = x + Re(Cᵃ y(x/‖x‖))` and then
`x'' = x' + W₂ v(x'/‖x'‖)`. That is the source layer, and each term is a general law of the level
rather than a routine for this source. Step 2 builds the founding with its receipts. It checks the
block whose owner is already whole: the attention block as participation, on a declared normalized
input, against the source's block computed once at the boundary. Its acceptance is fixed before the
build. On a declared normalized input of 16 sites, every head's current, and the read the output
projection makes of all nine, differ from the source block's exact operation by at most `2^(−8)` of
their largest component. That is the relative grain of the `bfloat16` carrier in which the source
realizes its own block, so an extraction within it loses less than the source's own realization
does. The face grain is not the bound: the charts are released onto `2^(−16)`, and the pairing sums
64 such terms. The four owed terms are the build after it, each tested at its consumer: the joined
level reproduces the source layer on a declared input, under the same bound.
