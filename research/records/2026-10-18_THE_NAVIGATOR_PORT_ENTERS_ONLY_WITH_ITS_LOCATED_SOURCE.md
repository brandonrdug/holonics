# The navigator port enters only with its located source

Grade: definition, with proved-derived identities over ℚ. The consumer is open and nothing here is
built. Main is read at `5cc91c7`. Refs #73, #76, #62.

## The law

A located linear navigator has keys `(b, S_a, c)` of rank `r` and a state `x̃ ∈ ℚ^r` that each
action steps, `x̃ ← S_a x̃`. It enters the field through a second material port on its source
ring `g`, the *navigator port* `N_g = E_g^(ν)` (`2d_g × r`, code `navigator_port`). The port is
read at the opening's phase beside the count port `E_g`:

`s_g(0) = P_g^(τ_g) (m̃_g + N_g x̃)`

The field's odometer steps every class abelianly (`Field::step_class`), so order lives only in
the phase-binned and offset counts, up to the moment's capacity (`hnn.moment-capacity`). The
navigator carries order as a state. On a closing ring `P_g` permutes
the realified coordinates (`Ring::rotate`), so `(P_g^τ)ᵀ = P_g^(−τ)`. The identities:

1. **Admission.** A row `D` with `D N_g = c` exists iff `c` lies in the row space of `N_g`, iff
   `ker N_g ⊆ ker c`, iff `rank [N_g; c] = rank N_g`. That is, the port merges no navigator
   direction that the readout distinguishes. This is the encoding's separator
   (`HNN/Encoding.factor_of_ker_le`, `separator_refutes_factoring`; atlas `encoding.separator`)
   read at `E = N_g`, `ρ = c`.
2. **The decoder is a fibre, not a carried matrix.** Every `D` in `{D : D N_g = c}` reads
   `D (P_g^(−τ_g) s_g(0) − m̃_g) = D N_g x̃ = c x̃`. So no representative is chosen or saved.
   - A fixed `D` would be broken by the first deposit with a component outside `ker D`.
   - The rank form fails only when a deposit merges a direction that `c` reads, which is exactly
     when the navigator term must drop.
3. **The covector is tape-free.** For a covector `h` on `s_g(0)`:
   `⟨h, P^τ(m̃ + (N + δ) x̃)⟩ − ⟨h, P^τ(m̃ + N x̃)⟩ = ⟨(P^(−τ) h) ⊗ x̃, δ⟩`.
   - The sample at `Locus::SourcePort(g)` is the feature `x̃` with the covector `−P^(−τ) h`.
   - It is read from the opening's covector and the imposed state alone.
   - It never reads `D`, so the fibre needs no representative for deposition either.
4. **Phase placement** (agent-inferred, from the chart `E_g` learns in). `E_g` learns in the
   moment chart: its covector is `P_g^(c−τ_g) h` (`SourceMoment::encoder_covector`).
   - Placed at the opening's phase, `N_g` learns in the same chart, so the same `x̃` deposits the
     same direction at every lift.
   - Placed unrotated, `N_g` would see `h` itself. A direction it learned at lift `τ` would then be
     read turned by `P^(τ′−τ)` against the counts at a later lift `τ′`.
   - The sample's covector must match the placement: `P^(−τ) h` for the phased placement.
5. **Work.** `SourceOpeningReceipt.imposed` is quadratic in the injection, through the storage
   power `(step/4) Y_g |s_g|²` of each source ring (`PowerForm::ring_power`). Let `𝔅` be its
   polarization. On `s₀ + s_ν` it equals `imposed(s₀) + imposed(s_ν) + 2𝔅(s₀, s_ν)`. So it is
   computed once, on the combined injection, and is never the sum of the two terms' separate
   impositions.
6. **Retention.** `N_g` shares `Locus::SourcePort(g)` with `E_g`.
   - The quotient keeps `N_g` exactly when it keeps `E_g` (`o_g ≤ e_last`), and releases both
     together.
   - An opening that imposes `x̃` separates two constitutions with `(N_g − N′_g) x̃ ≠ 0`.
7. **The navigator is not quotiented by `ker N_g`.** The resident keeps the full keys and the full
   `x̃`, because a later reading `c S_w x̃` can separate states inside `ker N_g`.
   - The admission is per opening: each opening imposes the current `x̃` and needs only the present
     readout.
8. **One certified step per locus** (agent-inferred, from the locus law).
   - Main deposits at most one linear step per locus (`HnnError::RepeatedLinearStep`), and the port
     shares `SourcePort(g)` with `E_g`.
   - An opening that imposes `x̃` reaches both maps, so they deposit as one map, the column block
     `[E_g | N_g]` (`2d_g × (|A| + r)`), under one normal law at the locus.
   - Each count sample is padded as `[M(c) w(c); 0]`, and the navigator sample as `[0; x̃]`. The Gram
     carries the cross terms between counts and state.
   - The derivative of `⟨h, s_g(0)⟩` in the joint map is the sum of the two blocks' derivatives:
     identity 3 and the encoder contract (`hnn.encoder-moment-contract`). So one step of the joint
     map is exactly the joint deposit.
   - The reads stay two blocks. With `r = 0` the joint map is `E_g` alone.
   - The founding prior is `[E_0 | N_0]`. A paired source port's symmetry (`hnn::paired::PortSymmetry`,
     `W e_(σa) = B W e_a`) acts on the `E_g` block only: the navigator's columns lie outside the
     paired family (`σ` is `None` there), so the projected deposit leaves them free.

## Its dimension is located

`r` is the dimension of the navigator the witness located.
- The witness is a planned location owner; main has none. It returns one minimal realization
  `(b, S_a, c)` of the observed series.
- Its read set is the reset words: each action word applied once from the initial state `b` and
  read. Under the declared, reported hypothesis `rank ≤ n`, the series is determined by its
  readings on every word of length at most `2n − 1` (Carlyle–Paz; Fliess), as one class up to
  `GL(r)`.
- The port is founded at that `r`, by the field's source-port founding rule (`declared_source_port`,
  the declared sign sequence times ½). That function is fixed to the alphabet's columns at part 0,
  so the port needs its own part code and `r` columns.
- The port refuses a navigator of any other dimension.

A declared `r` would be a set capacity.

## Why it does not enter main now

The port's consumer is a linear source family in `hnn::moment`. It carries a located navigator, its
witness, and the material commit at which its admission held. Main has none of the three parts the
port depends on:
- **No location owner reads the Hankel block of an action/reading series.**
  - The witness's read set is reset words.
  - The continuing listener hears one trajectory. Identification from one trajectory needs its own
    sufficiency argument, and that argument is not derived.
- **No comparison is wired to a navigator's scalar reading `y` against `c x̃`.**
  - The field's comparisons (`HolonRatio`, `ReceivingFaceRatio`) read classes.
  - The undivided pair `(y : c x̃)` has owners, `ratio::LogRatio` and
    `receiver::receipt::ReceiptRatio::between`, but no consumer joins either to a located
    navigator.
- **The field has no second injection.** Without one, a check of the opening's support repeats what
  `SourceMoment::open_storage` gives by construction: it writes only source rings, at their widths.

So the port, its read faces and its openers would be Rust whose only callers are tests, and the
guide removes such code. They wait for their consumer.

## The source this settles

Two of Epime's outage commits of October 17 were reviewed for this record. They are kept in the
private backup and are not in public history.
- **`448e0c2`.**
  - The port as an opt-in `NormalLaw` on a source ring, with carriers `NavigatorMap` and
    `NavigatorGram` at `SourcePort(g)`.
  - Read faces for `E_g x` (decoder `D E_g = I`) and for `N_g x` (decoder `D N_g = c`, with the
    rank check).
  - An unrotated combined opener.
  - The card refusing a constitution or state that carries the port, before upload.
- **`31728b9`.**
  - The phase-placed opener, which checks `D P^(−λ)(s − s₀) = c x̃` at the opening's own lift.
  - Its test builds the `NavigatorMap` sample from the actual `Word` adjoint's opening covector.
    It checks the pairing `⟨h, P^τ N x̃⟩ = ⟨P^(−τ) h, N x̃⟩`, and re-admits the port after an
    actual deposit.
  - No production path builds a navigator sample.

The builder reported both increments passing their focused tests. They were not run for this
record. They depart from the law above in six places:
- `r` is the column count of an authored initial matrix, not a located dimension.
- The face carries one decoder `D`, where the law reads the whole fibre.
- The unrotated opener, and its deposit test with the unrotated covector, stay beside the placed
  one, against identity 4.
- The navigator map is a second linear step at `SourcePort(g)`. Main refuses that in the same
  transaction as `E_g`, so the joint deposit of identity 8 cannot happen.
- The class-coordinate face `E_g x` opens a word from coordinates handed in. That is a second
  source with no law and no consumer.
- A test fixture embeds a transport model learned outside the machine, from a private run. No test
  of this law needs it.

## What brings it back

The port lands in one build together with its consumer:
- **Location.** A location owner in `compression::keys` (the Hankel rank of the reset-word block,
  with its hypothesis carried), and the intertwiner `T` on `Encoding`: `T z₀ = z₀′`,
  `T U_a = U′_a T`, `D′ T = D`.
- **The linear source** in `hnn::moment`, which supplies `open_storage`.
  - Its openings impose the navigator term only while the witness is certified and the port is
    admitted at the current material commit.
  - Two counters, never one (agent-inferred). The carried tick (`ReceptionCarry`) moves `x̃`
    and the witness. The material commit (`Constitution::commit`) moves the port and its
    admission.
  - Refused teaching advances the tick and leaves the port and its admission unchanged.
  - A whole-reception failure commits nothing.
- **The port** is founded at the located `r`, placed at the phase, and deposits by identities 3
  and 8, as the column block of the locus's one map, only from openings that imposed it.
- **Saves.**
  - The navigator law goes in `LearnedRing`, and one navigator record goes in the resident passage.
  - The passage version goes up by one, and older versions are refused (the guide: no legacy
    decoder).
  - The card refuses the port before upload until it realizes it (#76).

Its acceptance is fourteen exact tests:
1. A field with no navigator is byte-identical to today: material, state text, material identity
   and openings.
2. The founding has its shape, and a readout outside the row space is refused, typed.
3. The combined opening is exact, and equals today's when the term is not imposed.
4. The combined work closes, and its cross term is nonzero on a fixture built for it.
5. Two members of the fibre read the same `c x̃`.
6. The covector (identity 3).
7. A fallback opening gives no navigator sample, and an imposed opening gives exactly one,
   deposited in the one step of the joint map.
8. Admission after a commit, both kept and broken.
9. The four arms of the two counters.
10. Save and restore, warm and cold.
11. Retention together with `E_g`.
12. The card's refusal.
13. Phase placement: the same `x̃` imposed at two lifts deposits the same direction in `N_g`.
14. Two resident states that differ only inside `ker N_g` are kept apart, and a later reading
    `c S_w x̃` separates them.

## Failures this guards against

From the [September 29 lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **§1 item 1, an authored routine standing in for learning:** a navigator located outside the
  machine and handed in as a fixture.
- **§1 item 5, an uncertified deposition step:** the port deposits only in its locus's one certified
  step (identity 8).
- **§1 item 9, a refusal answered with a larger limit:** a failed admission drops the term and never
  widens anything.
- **§3 lesson 3, a located cause carried unrepaired into a new consumer:** a fixed decoder.

From the guide:
- **A set capacity:** `r` declared instead of located.
- **Unconsumed Rust:** a port with no source.

## Lean owed (#62)

- Admission at `N_g`: the instance of `HNN/Encoding.{factor_of_ker_le, separator_refutes_factoring}`
  with `E = N_g`, `ρ = c`, and its rank form `rank [N; c] = rank N` (beside `HNN/Encoding`).
- The phased navigator covector is tape-free (beside `HNN/Moment.encoder_covector_tape_free`).
- The joint map's derivative is the sum of its blocks' derivatives (identity 8), and the combined
  imposition's cross term (identity 5).
