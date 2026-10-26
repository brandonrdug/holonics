# The binding bank is a strand clocked by its antecedent, and a release is traced by its address

**Date:** 2026-10-26. Refs #404 #405 #406 #386 #410. Written for the design thread's build of
Athena alpha, as two specifications it can implement in `hnn::tower`, each with its acceptance fixed
before the work, and a list of the theory gaps that would block the milestone. Status:
- §2's recall, overwrite and chunk laws are proved-standard or proved-derived, checked exactly by
  the receipt (rationals in `ℚ(ζ₃₂)`, no float);
- §1's single cause for three measured failures, §2's antecedent clocking, §4's trace law and every
  declared size are [agent-inferred], each with its reason;
- §3 and §5 are acceptances, fixed here, measured by the build.

**The request** (Brandon, October 26, paraphrased): most of the theory feels developed; coordinate,
keep the work aligned and ambitious, and use the momentum. The coordinator asked this thread to stop
opening new theory and to give the design thread what it needs for binding inside the learner and for
composed language from retained state. The design thread's plan (October 26) is: hear enough (the
learner on the card, same bits as the CPU), grow on each reread until unseen Holonics prose codes
below bz2, write from a cold restart with each phrase traced, then answer whole unseen GSM8K problems
with digit labels and speech transcripts from the same listener.

## 1. What the tower lacks: no read selects an earlier arrival by its content

`hnn::tower`'s state is a bank of diagonal complex modes, `h_t = λ_t ⊙ h_(t−1) + γ_t ⊙ B x_t`. Each
mode is one complex number, so its phase superposes everything the section pushed into it, weighted
by age. It is the helical code's strand with the positional clock `τ(k) = k`: a fading memory of the
passage, read as a whole. No read of it returns the one earlier arrival that followed a context like
the present one. Three measured failures have that shape [agent-inferred: one cause, tested by §3]:
- **Prose.** On the 64 held-out Holonics prose pieces the tower codes 3.117 bits a byte
  ([record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md));
  bz2 given the same training text coded them at 2.601 (October 25 orientation reading). bz2's block
  sorting codes a byte by the earlier occurrences of its context in the passage: in-context recall.
  [October 26 correction: the 3.117 was read at 8 chunks, in which prose falls in three pieces, not
  64; no reading of bz2 reproduces 2.601, and the bar is now declared with its pieces in
  [the prose and subject record](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING.md#1-item-5-prose): bz2 given the prose part of the training text,
  2.773.]
- **The subject.** None of the 16 samples continuing the held-out question about John answers about
  John, and 12 open on an invented or foreign name
  ([record](2026-10-23_THE_COPY_CONTACT_CARRIES_THE_QUESTIONS_PIECES_INTO_THE_ANSWER_AND_THE_SUBJECT_STILL_DRIFTS.md)).
  That record's own reading: the modes do not hold the name forty units back, so the tower opens a
  name of its own.
- **Arithmetic.** The question's quantities must be recalled at the calculation markup; the samples
  write well-formed markup with wrong arithmetic.

The classical name is associative recall (Zoology, arXiv 2312.04927): models whose recurrent state is
a vector per channel fail it, and models whose state is a key-by-value product pass it. The tower's
modes are the first kind.

## 2. Spec 1: the binding bank

### 2.1 The law in the objects

The helical code's strand is `m = Σ_k Ĝ(τ(k))⁻¹ E(u_k)`
([guide](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode)). Clock it by content
instead of position: let the tick of an arrival be a turn `s_k` located from the face it arrived
into. Then the read at a present turn `s_q`,

```text
Ĝ(s_q) m = Σ_k Ĝ(s_q − s_k) E(u_k),
```

passes through a decoder whose kernel is every nonzero turn difference, and returns the arrivals
whose key turn equals the query's. Two things make this exact. The navigator is a box of harmonics
of the key's turn, so the decoder is the average over its harmonics. And the strand's face holds a
value vector at each harmonic, not one number per mode. The second is the plural ranks the
orientation reading called for.

### 2.2 The equations at the consumer

One bank at level `ℓ` of the tower, with `d` key turns and the harmonic box
`N = {0, …, M₁ − 1} × … × {0, …, M_d − 1}`, `|N| = 2^m` (a power of two, so the read's `1/|N|` is a
shift):

```text
antecedent  a_t   = [r̂_(t−1), x^ℓ_(t−1)]                    the face the arrival came into
key turn    s(k_t) = 2^(−⌈log₂ w⌉) (W_k a_t + W_k′ x^ℓ_t + b_k)   d turns, half turns on 2^(−16); W_k′ by the October 26 amendment
query turn  s(q_t) = 2^(−⌈log₂ w⌉) (W_q [r̂_t, x^ℓ_t] + b_q)   the present face
value       v_t   = W_v x^ℓ_t + b_v                          d_v real channels
harmonic    φ_n(s) = e^(iπ⟨n, s⟩),  n ∈ N                     the turned mode's dyadic ladder at ⟨n, s⟩ mod 2
read at key u_t   = 2^(−m) S_(t−1) φ(s(k_t))                 what the bank already says at this key
news        e_t   = v_t − u_t
write       S_t   = ρ_t (S_(t−1) + g_t e_t φ(s(k_t))ᴴ)       S: d_v × |N| complex
gate        g_t   = 1/(1 + 2^(−(W_g x^ℓ_t + b_g))),  ρ_t = the gated mode's hold, ≤ 1 − 2^(−12)
read        v̂_t   = 2^(−m) S_t φ(s(q_t))
join        x^(ℓ+1)_t = x^ℓ_t + W₂ v_t + b₂ + O [Re v̂_t ; Im v̂_t]
```

- **The write is the news.** The bank deposits only the difference between what arrived and what it
  already said at that key (the delta rule; DeltaNet, arXiv 2406.06484). This is the retention law
  read inside the state: a comparison observed after an update is read through the contemporary state
  and returns its residual. Rebinding a key overwrites it, so the bank keeps no copies; its size is
  `d_v × |N|` whatever the section's length. It is a quotient, never a tape (receipt B).
- **Antecedent clocking** [agent-inferred]. The key reads the face before the arrival and the query
  reads the face after it. This is causal order, not a routine: the write pairs an arrival with the
  context it came into, and the read asks what followed the present context. It is the key law of
  CLAUDE.md ("an action expression and its antecedents induce a consequence"). `W_k`, `W_q`, `W_v`,
  `W_g` and `O` are located by the comparison's covector. Nothing says what to bind. Receipt E shows
  only the reach: with keys set by hand, the bank copies a repeated word's continuation exactly. The
  machine has to locate its own keys, and §3's acceptance measures whether it does.
- **[October 26 amendment: the key reads the arrival too.]** After the subject read of
  [the prose and subject record](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING.md#2-item-6-the-subject-question-fails)
  (0 of 16 samples about John). A key read from the antecedent alone is a function of the face
  before the arrival. So:
  - two arrivals under one antecedent face take one key, whatever they are, and the later
    overwrites the earlier;
  - an arrival under a face that no later query's turn reaches cannot be recalled. At rest the face
    is zero, so the key is the bias `b_k` alone. `John`, the prompt's first unit, is bound there.

  Such a bank answers "what followed this context" (copying). It cannot answer "which arrival was
  of this kind": a subject, a quantity's role, or a unit by its own content. The action-key law
  pairs the action expression with its antecedents, so the key reads both:
  `s(k_t) = 2^(−⌈log₂ w⌉)(W_k a_t + W_k′ x^ℓ_t + b_k)`. `W_k′` opens at zero, so the amended bank
  opens bit-identically on the built one, and the covector decides what each key carries. The
  separator framing that record's next loop reads tests only the second point. The amendment covers
  both.
- **The opening.** `O` opens at zero, so a banked tower opens bit-identically on its bankless twin,
  as the gated, turned and pumped modes open on theirs. The key and query turns open at zero (every
  key on one turn: the read is the section's recent average). The gate opens at `g = ½`.
- **Modality.** The bank reads classes of the declared alphabet and nothing else. Octets, pen strokes
  and speech half-cycles enter it alike.

### 2.3 Exact recall, the leak, and where a key must sit (receipts A–C)

For one key turn and `M` harmonics, `⟨φ(s), φ(s′)⟩ = K_M(s′ − s)`, with

```text
K_M(δ) = Σ_(n<M) e^(iπ n δ) = M                                if δ ∈ 2ℤ
                            = 0                                if δ ∈ (2/M)ℤ \ 2ℤ
                            = (1 − e^(iπMδ)) / (1 − e^(iπδ))     otherwise.
```

With `d` turns the kernel is the product of the coordinates' kernels. So:
- `|N|` keys on the grid `(2/M_i)ℤ` (one per grid point) are recalled exactly, and a read at a grid
  point no key holds returns zero (receipt B, all 16 of 16);
- an off-grid key leaks into every read by its kernel. Receipt C checks the closed form
  `16(1 − ζ^(a−3)) v̂ = 2v` exactly. On real values the matched read is real, so `Im v̂` is a reading
  of how far the keys sit off the grid. `O` reads it, and the build reports it;
- **a key reaches exact recall only by locking on the grid.** The grid points are Farey addresses of
  the key turn. The pumped mode already gives a residue a place to sit, by its lock. [agent-inferred]
  The first build keeps the key turn on the turned chart without a pump. `Im v̂` measures whether the
  learned keys settle near the grid. A pump on the key turn is the change if they do not.
- **Capacity** is `|N|` grid keys per bank. `H` banks with their own turns give `H|N|`.
- **Learning the key** is learning the phase part of the comparison. `∂ log φ_n/∂s = iπn`, so the
  key's covector is the turn (imaginary) part of the read's logarithmic derivative. The tower's real
  cross-entropy reaches it only through the read.

### 2.4 Passivity

`P = φφᴴ/|N|` is an orthogonal projector (`|φ_n| = 1`), and the write is
`S_(t−1)(I − g_t P) + g_t v_t φᴴ`. Since `|1 − g| ≤ 1` for `g ∈ [0, 1]`, the transition does not
expand, and

```text
‖S_t‖ ≤ ρ_t (‖S_(t−1)‖ + g_t √|N| ‖v_t‖)  ⇒  ‖S‖ ≤ √|N| max‖v‖ ρ/(1 − ρ) ≤ 2^12 √|N| max‖v‖
```

at the margin. On the grid each key's read is `w_a ← ρ((1 − g) w_a + g v)`, a convex combination of
the values bound to it, so `‖w_a‖ ≤ max‖v‖`. The carrier is declared from this bound: at
`|N| = 2^6` it is 15 bits above the value's grain. A crossing past it is a typed refusal, and the
carrier widens at that declared crossing.

### 2.5 The adjoint (the reverse scan inside a section)

With the convention `G = ∂L/∂Re + i ∂L/∂Im` and `dL = Re⟨G, dz⟩`, and `γ̂_t` the covector at `v̂_t`
from `O`'s adjoint:

```text
G_S   += 2^(−m) γ̂_t φ(s(q_t))ᴴ ;    G_φ(q_t) = 2^(−m) S_tᴴ γ̂_t
G_S′   = ρ_t G_S ;                   G_ρ(t)   = Re⟨G_S, S′_t⟩,   S′_t = S_(t−1) + g_t e_t φᴴ
G_g(t) = Re⟨G_S′, e_t φᴴ⟩ ;          G_e      = g_t G_S′ φ ;      G_v(t) = G_e
G_φ(k_t) = g_t G_S′ᴴ e_t − 2^(−m) S_(t−1)ᴴ G_e
G_S   ← G_S′ − 2^(−m) G_e φᴴ                                         carried to t − 1
G_s,i  = π Σ_n n_i Re(conj(G_φ,n) i φ_n)                            to W_k, b_k or W_q, b_q
```

The scan needs `S_(t−1)` at each cell. The section holds the bank at its opening, as it holds the
modes, and recomputes forward. Its per-cell bank is section workspace, released when the section
closes, like the cells' faces held for the certifying reread. The code's difference checks every
family.

### 2.6 The chunk form, for the card (receipt D)

Inside a chunk of `C` cells opening on `S₀`, with `R(τ, t) = Π_(τ≤σ≤t) ρ_σ`:

```text
(I + L) E = V − (R(0, t−1) 2^(−m) S₀ φ(s(k_t)))_t,   L_(tτ) = R(τ, t−1) g_τ 2^(−m) K(s(k_t) − s(k_τ)),  τ < t
v̂_t = R(0, t) 2^(−m) S₀ φ(s(q_t)) + Σ_(τ≤t) R(τ, t) g_τ 2^(−m) K(s(q_t) − s(k_τ)) e_τ
```

`I + L` is unit lower triangular, so forward substitution needs no division. The kernel `K` needs no
sum over harmonics. In exact rationals the chunk form equals the recurrence on every partition
(receipt D: 12 cells, keys on and off the grid, repeated keys, dyadic `g` and `ρ`; partitions (12),
(4,4,4), (5,7), (1 × 12) and (3,9) agree).
- **On the grain.** The two forms round different terms, so they agree on the grain only where
  nothing is released. The declaration therefore fixes the chunk length `C`. The CPU reference and
  the card compute the same rounded terms, and the card sums each term's co-present contributions in
  any order: integer addition is associative, so the bits agree. This is the hardware law's commuting
  partition.

### 2.7 Placement in `hnn::tower` [agent-inferred]

- A declared field `bank: Option<BankDeclaration { level, turns, harmonics: [M_1..M_d], banks, values }>`
  on `TowerDeclaration`.
- The bank's material joins the certified deposit's families, with the same moments and the same
  certificate: the section reread from its opening codes strictly fewer bits.
- `to_text`/`from_text` carry the bank's material. They do not carry its state at rest: a cold start
  opens the bank empty.
- The first declaration: one bank at the top level, `d = 2`, `M = 8 × 8` (`|N| = 64`), and `d_v`
  the level's width. That is 64 grid keys, four times the terrain's 16 bindings, so learned keys
  have room to sit apart on the grid.

## 3. Spec 1's acceptance (fixed before the build)

1. **Opening.** With `O = 0` the banked tower codes every section bit-identically to its bankless
   twin.
2. **Covector.** The code's difference agrees with the covector for `W_k, b_k, W_q, b_q, W_v, b_v,
   W_g, b_g`, the hold and `O`, in the existing test form.
3. **Card form.** The card's chunk form and the CPU's chunk form, at the declared `C`, give the same
   bits on a section.
4. **Recall on the terrain.** The MQAR terrain is fixed in receipt F:
   - 64 key classes and 64 value classes, 16 bindings a passage, then the 16 keys again in a
     shuffled order, each followed by its value;
   - each passage is shuffled by SHA-256 of its index, so a key's value is fixed only inside its
     passage. Key 0 alone is bound to 63 different values across the held-out set, so no
     constitution can name an answer;
   - training passages count up from index 0, and the held-out passages are indices
     1,000,000–1,000,999, SHA-256 `67212eb0…f2f0d3`.

   The bar: a banked tower names at least 95% of the 16,000 held-out answer cells. The bankless tower
   of the same declaration is measured beside it as the foil, not as the bar.
5. **Prose.** On the 64 held-out Holonics prose pieces, the banked listener codes at or below bz2
   given the same training text, both measured in one receipt. Setting `O` to zero after training
   raises its code: the read carries code, and removing it shows that.
   [October 26: read in [the prose and subject record](2026-10-26_THE_BANK_LOWERS_EVERY_MEDIUMS_HELD_OUT_CODE_AND_RECALLS_NO_SUBJECT_BOUND_AT_THE_OPENING.md#1-item-5-prose) on the tower's 8 chunks,
   with the bar declared there as each compressor's lower code given the whole training text or the
   prose part of it.]
6. **The subject.** Continuing the copy-contact record's held-out question about John over the same
   eight key streams, at least 12 of the 16 samples answer about John (now none does).

A failed item is the next loop's subject, named by its measurement.

## 4. Spec 2: writing from retained state, traced by its address

### 4.1 What is retained, and where the bindings live

A cold restart reads the constitution only (`Tower::from_text`): modes, contacts, face, founded
units, pair and ring faces, and the bank's material. It does not read the passage, the bank's state or
any index. The bindings live in two places.
- **Across passages: the contacts.** A rectifying contact pair is the constitution's key–value
  memory: the rows of `W₁` are keys matched by the rectifier, and the columns of `W₂` are the values
  they add to the face. This is the classical reading of a feed-forward block (Geva et al.,
  arXiv 2012.14913). What the heard text bound often enough is deposited there.
- **Inside the present passage: the bank.** After a cold restart the bank holds only the prompt and
  the release itself.

A connected paragraph needs both. The contacts supply what was heard about the subject; the bank
keeps the paragraph's own subject and quantities from drifting.

### 4.2 The trace law [agent-inferred]

**Provenance is an address, resolved outside the machine, never an index the machine keeps or
consults.** Each released class carries only quantities its forward already computed:
- (a) the contact rows that conducted most to its exponent: `v_i · (U W₂)_(c,i)`, the row's share
  of the released class's exponent;
- (b) the bank's read: which earlier cell of the prompt or release its key turn matched, from
  `K(s(q_t) − s(k_τ))` weighted by `R(τ, t) g_τ`.

The resolution of (a) to heard text is an observer census. The frozen constitution is run once over
the heard text, and each contact row's most-conducting heard spans are recorded with their sources.
That is the row's preimage fibre at its grain. Beside it, an exact-match resolution gives (c): the
longest heard span equal to each released phrase, with its source document.

None of (a)–(c) enters the machine. This keeps the retention law (no tape, no index) and the
lesson against counting recitation or an index of contexts as generation: the trace shows where a
phrase came from, and it is never how the phrase was made.

### 4.3 Spec 2's acceptance (fixed before the build)

1. **Restart.** The constitution read by `from_text` codes the held-out pieces bit-identically to the
   constitution before `to_text`.
2. **Unseen prompts.** Each prompt is the first 32 bytes (about a clause), cut back to the last
   space, of one of 16 held-out Holonics paragraphs that the machine never heard.
3. **Shown whole.** Each of the 16 releases is 600 bytes (about a paragraph of the guides), shown to
   Brandon whole and as it is, with
   its trace beside it. No control or reference text stands beside it.
4. **The recitation bar, derived rather than chosen.** Let `ℓ_rec` be the longest verbatim run that
   any of the 16 held-out paragraphs' own 600-byte continuations shares with the heard text: what
   the authors themselves reuse. A release whose longest verbatim run with the heard text exceeds
   `ℓ_rec` is shown, marked as recitation, and never counted as writing.
5. **Composition.** In each release counted as writing, the maximal verbatim runs that span at least
   two whole words resolve to at least two different heard documents. (One word recurs in any text,
   so a run must join two words to name a source.) The runs are joined at seams that occur nowhere
   in the heard text.
6. **Trace.** Every released class carries (a) and (b), and every maximal run carries (c).

Connectedness is Brandon's reading of the whole output. It is shown and never gated on.

## 5. The theory gaps that would block the milestone

- **Binding in the learner.** This was the missing law; §2 states it, and the receipt checks it.
  Owed to #410: `bank_recall_exact` (for a primitive `M`-th root `ω`, `Σ_(n<M) ω^(nd) = M·[M ∣ d]`,
  so a grid read returns its binding; Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` is the core),
  `bank_delta_overwrite` (`w_a ← ρ((1 − g)w_a + g v)` on the grid), and `bank_chunk_eq_recurrent`.
- **Provenance under the retention law.** §4.2 states it.
- **Nothing else in the theory blocks.** The remaining blockers are construction, each with its law
  already in place:
  - **Hearing enough** (the design thread's step 1): the card realization, with the hardware law of
    §2.6.
  - **Founding on reread** (step 2): the lap law (a lap founds only what the last lap made
    reachable) and the effective tension `S = T − B H⁺ Bᵀ`. Its founding direction is the top
    generalized eigenvectors of the tension (atlas `contact.pool-founding`). A founded direction can
    be a contact row or a bank's key turn.
  - **The readout reading the slow memory** (labels at 26 of 500 while the slow modes hold 176):
    the contacts' read of `r̂` at the label. The bank does not address this, so it is not in §3.
  - **Carried arithmetic** (whole GSM8K): the quantities are recalled by the bank (§3.6's subject
    test is its first reading). Sums and differences close under reflect-and-restart (records of
    October 25). A product's face is the bilinear block of the face table (atlas
    `contact.face-table-blocks`), which the pair contact already carries.

## 6. The recorded failures these choices could repeat

- **An authored routine standing in for learning.** Antecedent clocking is causal order, not a
  solution. Every map is located by the covector, and the terrain's bindings change with each
  passage, so no constitution can carry the answers. Receipt E's hand-set keys show the bank's reach
  only, and are never the machine.
- **Recitation counted as generation.** §4.3.4 derives the bar from held-out text, and §4.3.5
  requires seams that were never heard.
- **Text treated as the exception.** The bank reads classes of any alphabet. The listener's strokes
  and half-cycles pass through the same bank.
- **A design thought in arrays and tables.** The bank is a navigator's box of harmonics, read by
  characters: residues and spectral placement. The chunk form is the same series regrouped.
- **An uncertified deposition step.** The bank's material deposits through the section's
  certificate.
- **Seen material graded as unseen.** Held-out passage indices are disjoint and their set's SHA is
  fixed. Prompts come from paragraphs never heard.
- **Bits read as progress.** §3.4 and §3.6 are behaviour. §3.5's bits stand beside bz2 and beside the
  ablation.
- **A refusal answered with a larger limit.** The carrier width comes from §2.4's bound.

**The six general objects** ([winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)):
- the bank touches the helix (the strand's clock), the pair (the write pairs antecedent and arrival,
  and the read is a contact) and faces and placement (the characters of the harmonic box);
- cell holonomy, the tube (the section) and the tower thread (the bank lives at one level) stay
  attached.

**Navigators, terrain, kernel, cokernel, landmarks:**
- navigator: the harmonic box;
- terrain: the MQAR passages, Holonics prose and GSM8K;
- kernel: the nonzero grid differences the decoder averages out;
- cokernel: the leak `Im v̂` and the news not yet bound;
- landmarks: the grid points where learned keys converge.

## Receipts

`2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS_receipts/`:
`binding_bank.py` (parts A–F), its output `binding_bank.txt`, and `RUN.md` with the run's projection,
deadline, wall time, peak resident set and hashes.
