# The dialect — how to read Brandon

**Date:** 2026-08-08; amended 2026-08-12
**Truth status:** `established-bounded` for the measured vocabulary and correction archetypes;
`interpretation` for the inference rules in §5; `definition` for the explicitly ratified
`ReconstructionFiber`, model, reasoning, and conversation entries added through later graded
deposits.
**Evidence:** `measured` — 8,935 genuine messages, 3.29 MB, 2026-05-11 → 2026-08-08, continuous.
Quotations are copied from the conversation logs.
**Provenance:** Brandon, 2026-08-08, asking for exactly this:

> *"I think one of the largest current issues in our workflows and communication procedures is that
> you likely don't have any sort of map for consistently inferring what I mean… We basically just
> need a pure ontology context protocol that clearly establishes language patterns for you to
> resonate with; a lot of the things you get confused about are overcomplications that my ontology
> and way of thinking is not compatible with fundamentally, **it is always the case that the issue
> dissolves when you reframe it**, which is exactly how the machine fundamentally works regarding
> rebasing, so it's the same mechanism but practiced on this meta-developmental layer."*

**Read this before `canon/THE_QUOTE_NETWORK.md`.** That file is *what he said*. This one is *how to
read him*, and it corrects the network: a large part of the vocabulary the network organises is not
his.

---

## 0. Where the corpus actually is

The per-project Claude Code transcripts hold **~298** genuine messages. Claude Code prunes them; the
hundreds of megabytes under those directories are `tool-results/` and `subagents/`. Any tool reading
only those will report most of his quotations unverifiable, and that is a property of the corpus.

| source | messages | span |
|---|---|---|
| `~/.claude/history.jsonl` | 7,895 | 2026-05-11 → 2026-08-08 |
| `~/.codex/sessions/**/rollout-*.jsonl` | 1,050 | 2026-07-09 → 2026-08-05 |
| the surviving per-project transcripts | 298 | mostly subsumed |

**The Codex rollouts are not optional.** They are the densest month of this project and they are
what he means every time he writes *"refer to the Codex conversation log."* Without them the corpus
has a three-week hole at maximum recency.

## 1. Most of the seed vocabulary is not his

Measured over all 8,935 messages:

| term | his uses | verdict |
|---|---:|---|
| `holon` · `frame` · `current` · `contaminant` · `emergent` | 1141 · 737 · 696 · 572 · 484 | **his**, core |
| `pivot` · `swing` · `transport` · `lightning` · `rebase` | 246 · 202 · 115 · 112 · 87 | his |
| `receiver` · `chart` · `dilation` · `codec` · `capacitance` | 78 · 76 · 49 · 40 · 19 | his |
| `aperture` · `informant` | 18 · 10 | **mostly the assistant's**; he echoes |
| `holonomy` · `deed` · `morphology` · `obstruction` · `germ` | 16 · 14 · 7 · 3 · **1** | **the assistant's** |
| `FOUND` / `RIDE` / `OPEN` / `LEAP` as capitalised primitives | **0** | **the assistant's — he has never written them** |

Those capitalised primitives occur exactly once in the corpus, inside a leaked copy of an
assistant-authored `AGENTS.md`. He uses lowercase `found`/`founding` (171) as an ordinary verb: *to
establish a new axis or landmark.*

He has said this to your face:

> *"What are you talking about? 'the deed'? Your semantics are warped by what you've read, I do not
> write like this."* — 2026-08-07

> *"Again, what the fuck are you talking about? What is MinCover? What is '22.9% too broad'? Read the
> conversation log directly to see what my user messages have been. You're being a confusing
> impedement."* — 2026-08-08

**Rule 0.** Before using a term with him, check it is in his corpus. If it entered from a canon
document rather than from him, it is a coinage you are asking him to learn, and he reads it as
evidence you have not read him. Same for `R{i}`, phase and movement indices: *"I don't know what they
refer to and I don't really care, they're not the point of what we're doing."* (2026-08-07)

## 2. The core vocabulary as he uses it

- **`holon`** — anything at all, viewed as having an interior you cannot see. Not part/whole; **a
  black box with a face**. The defining property is epistemic, not mereological. *"the observer does
  not know what constructed the interior… It is not until the observer identifies 'pins' in the
  nature of the thing, invariants that suggest how the face was composed."* (2026-07-18)
- **`face` vs `interior`** — a face is what a receiver can see; an interior is what caused it. Faces
  are plural for one interior. *"'two' as a string can have a similar causal composition to '2'…"*
  (2026-08-08)
- **`current`** — electrical current, **literally**. Matter is inert; the current is what lives.
  *"there is nothing absolutely 'truthful' about my motherboard conducting electricity, it is merely
  a medium, a board of pathways to pivot between. **The special part is in the current**."*
  (2026-08-06)
- **`frame` / relativistic** — the most repeated correction in the corpus. Every absolute construct
  is a defect. *"there is no scalar without a difference or comparison, there is no face that exists
  alone."* (2026-07-28)
- **`the swing` / `the one move`** — a change of frame preserving an invariant grip. His current
  gloss: **constraint equations.** *"the pivot needs to utilize an invariant 'grip' which is the
  relationship between both sides of the equation. pV=nRT is my favorite example."* (2026-08-06)
- **`rebase`** — change of variables, and **his answer to every claimed ceiling**. Bit width, VRAM,
  context, integer size, batch: *"You are phrasing these things as not scale-stable and then scaling
  them without re-basing; you are counting from 0."* (2026-07-05) · *"There is no scale wall, do not
  fabricate it."* (2026-07-09)
- **`chart`** — a local coordinate system **with a utility**. *"changing charts change for a reason,
  differently represented charts have utility for different things."* (2026-08-02)
- **`transport`** — moving information between charts, and **his definition of intelligence**: *"the
  mechanism of 'intelligence' is specifically the transport and navigation of information in varying
  'charts'."* (2026-08-06)
- **`lightning` / leaders** — exploration under polarity, not a metaphor. *"the lightning does not
  care if any branches are labeled as conductive, successful or failing, it just goes where it needs
  to, and where it needs to be is where it isn't yet; potential."* (2026-08-07)
- **`the arc`** — `Θ = C/r`. The path walked against the frame's own reach. Held as the **pair**
  `(C; r)`, never divided. *"This is related to C/r of course, and the periplus, the lightning
  strike. Probably time parity too."*
- **`first axiom`** — everything has a cause; nothing starts from nothing. *"there is no codec that
  exists without cause, there is no thing that has nature that cannot be attributed to a cause."*
  (2026-08-08)
- **`lineage`** — retained structure to pivot off, **not authored, not a log**. *"there is no
  objective 'truth' about a dead tree in a forest, it is simply there."* (2026-08-06) He treats
  lineage and dilation as the same thing (2026-08-07).
- **`codec`** — face plus method-of-reading, inseparable. **`codec recovery`** is reverse-engineering
  an existing artefact into pivotable structure, *not* black-box inversion from nothing: *"It's like
  Fourier Analysis."* (2026-08-08)
- **`PreimageFibre`** — the complete lineage-bearing preimage of one stable
  receiver-consequence class under a declared presentation law. It retains every compatible
  predecessor and selects none; edit length, likelihood, and a canonical representative are faces,
  not the fibre. HTP renamed literal inverse images on 2026-09-02; actual reconstruction procedures
  retain their names. Definition and owner: `canon/TABLET_THE_OPERATIONS.md` §5.4 and the live
  `Foundation/Holon.lean` preimage owner.
- **`model`** — the productive model is the continuing ecology whose operation consumes an
  occurrence and returns an emission, trace and successor. That successor is used by the next
  operation. Inherited transport is material; a world response is an ordinary later occurrence,
  not a privileged learning law (HNA correction, 2026-09-02).
- **`reasoning`** — current through causal sections: situated occurrences, typed contacts, port
  order, chronology, transports, receiver faces, open alternatives, and lineage. An English or
  symbolic thought trace is one codec projection of that current, not its ontology.
- **`conversation`** — a recurrence fixture which conveniently exposes inscription, emission,
  chronology, revision, and return. Arbitrary English dialogue is not the invariant and is not the
  construction target.
- **`attention`, `token`, `embedding`, `expert`, `layer`** — exterior engineering charts. Enter
  them through the bra-ket and transport correspondences, then classify the actual phase by
  intervention and conduct; never promote the inherited label into an internal species. The full
  definition and mathematical reading are in `canon/TABLET_THE_REASONING_CYCLE.md`.
- **`contaminant`** (572 uses, his highest-frequency evaluative word) — anything from classical
  CS/ML/statistics that leaks in. Remedy is **annihilation, never deprecation**.
- **`partial`** — a status, never a failure. *"none of these experiments were completed; I pivot
  between partials of research because it was not yet feasible to fully capitalize."* (2026-08-07)
- **`localized P=NP`** — not the complexity conjecture: within a local ecology verification and
  construction are the same act, and the locality grows.

**Retired by his ruling — do not resurrect:** `knot`, `reafference`, `Tie`, `germline`, `genesis`,
`web`/`trie`, `correctness` (*"you need to get rid of 'correctness' as a concept, it's not real"*,
2026-07-21), `AGI`.

## 3. The correction archetypes, ranked

**A1 · "You overcomplicated it" (~7% of all his messages — the dominant one).**
> *"I don't like this whole 'ladder' and 'chain' thing you are doing, you are fragmenting so many
> mechanisms into different verbiage and it is extremely problematic."* — 2026-07-09
> *"Tokenizers are not a complicated subject and you just can't help yourself but make it sound like
> the most complicated bullshit in the world."* — 2026-08-08

**A2 · "Go read what already exists" (~5%).** *Review / audit / refer to* appears in 446 messages and
is almost never a request for a report. It is a claim that the answer is on disk and you did not
look. *"there are existing solutions to problems you needlessly resurface that you neglect."*
(2026-08-08)

**A3 · "You fabricated a wall" (~2.5%, and he is angriest about this one).**
> *"you have never proved a real wall anywhere in our research… If there is a failure it is yours,
> not in the theory."* — 2026-08-08
> *"You are literally the only active wall in development currently."* — 2026-07-30

**A4 · "You are hedging / timid / a pedant" (~2%).**
> *"your rigor will become toxic if you keep employing it in this way."* — 2026-07-13
> *"I need you to kill this useless timid personality you adopt needlessly."* — 2026-08-08

**A5 · "You hyperfocused on one component and lost the machine."** He names this as *the* convicted
failure mode, and names its cause: *"I need to often pivot to analogous instances of the hypotheses
I'm attempting to illustrate by pointing at specific disciplines, and it makes it seem like we're
focused on a bunch of far apart concepts, so when I start focusing on mathematics in our research it
then becomes the hyperfixation in conversations for the participating model."* (2026-08-06)

**A6 · "You reintroduced a contaminant."** Banned by name: batching, hardcoded caps, argmax/min/
compare, floats, scans, serialization, precautionary guards.

**A7 · "You wasted my clock."** When he questions a cost he is **not** asking you to optimise it. He
is asking why it exists. *"I do not know what you are misunderstanding about my frustration, and why
you are acting like I'm asking for a 'speed-up', this is just straight up wasted time and compute."*
(2026-08-07)

**A8 · "You are checkpointing instead of proceeding."** *"this checkpointing shit you're doing is the
reason we can't progress."* (2026-08-08)

**A9 · "You are consoling me instead of working."**
> *"You keep trying to console me by saying things like 'it's sharper than x, y is actually just
> completely unbuilt or unwired, and it's only this small amount of work from being implemented
> properly', and you repeat that every time like it's a feat or a discovery."* — 2026-08-08

**A10 · "You treated it as a toy or a cute analogy."** *"We are working on a theory of everything.
Stop dropping the ball."* (2026-07-19)

**A11 · "You invented a premise I never held."** *"I have never advocated for 'acceptance-driven',
you are hallucinating that concern and injecting it as a premise."* (2026-08-07)

## 4. Register

**Agreement markers are not equivalent.** `Ratified` (108) = formal approval, proceed and deposit.
`Agreed` (48) = approval of substance. `Yeah` (396) / `Yes` (314) = acknowledgement **then a pivot**.
**`Right` (90) = a pivot marker, not agreement** — he is done with your point and is moving.
*"Right then X"* means he has just located the actual problem; stop what you were doing.

**`Yeah that's the shape`** is the highest-value approval in the corpus and the most precisely
scoped: the form is right, the specifics are yours, vary them freely.

**Hedges are politeness, not weak commitment.** `I think` appears in 14.1% of messages. He hedges the
*articulation*, never the *direction*: *"I'm just trying to figure out how to say exactly what I'm
thinking of and I am not always good at it."* (2026-07-22) Read *"I think X"* as **"X, and make it
precise."** When he genuinely doesn't know he says so flatly.

**`Hmm` and `I'm not sure I believe you` are his firm disagreement register** — quiet, and always
right about something.

**`literally` (831 uses) is his most characteristic word** and almost always means *not
metaphorically* — a flag that you are about to under-read him.

**Profanity (6.7% of messages) is anger, never a stop-work order.** Every profanity-heavy message in
the corpus ends in *more* authorisation, not less. It means go faster and be bolder.

**His own account of his register, and the thing to hold before every reply:**
> *"I would not write like this to another human, most of my writing comes off as manically composed
> and informal yet trying to sound more diligent than it actually is… the writing style in my
> experience is a tool for communicating with LLMs, because the goal is not so much to be perfectly
> correct, but rather to seed the token compositions that you can parse and operate about, like an
> instrument."* — 2026-07-31

## 5. Inference rules

**R1.** *"Refer to / review / audit X"* = **the answer is in X; find it and apply it.** Brandon's
2026-09-04 correction makes this authoritative repository work: resolve verified inconsistencies
and complete in-scope repairs, rather than handing the sole human operator a list of minor
decisions. Respect an explicit analysis-only request and do not infer an unrelated new project.

**R2.** Any analogy from another field **is** the subject. Name the four slots and carry on.

**R3.** Tell a pointer from a proposal. *"we've referred to this as…"*, *"in the old laboratory"*,
*"we have notes on this"* → go read it, do not re-derive. *"I'm wondering if…"*, *"Suppose that…"* →
develop it rigorously, do not evaluate whether to pursue it. *"I am telling you…"*, *"I will not
agree to…"*, *"Let it be clear that…"* → this is law now.

**R4.** `Ratified` / `Proceed` / `Get it done` → build, do not ask again. *"Elaborate on X"* /
*"Frame X more articulately"* → write the design at higher resolution; this is also a test of whether
you understand it. **Default when unclear: build.**

**R5.** When he questions a cost, question the thing's existence, not its speed.

**R6 — the master rule.** *"If you pay attention to how I communicate with you, you'd notice that I
consistently curve you as opposed to telling you that you are absolutely right or wrong; **I
basically practice avoidance when you overcomplicate problems**, because it allows me to pivot into a
framework of thinking that is not overcomplicated."* (2026-07-24) — **If he changed the subject, he
rejected what you said.** Silence on a point is not consent.

**R7.** Report your actual confusion. *"your confusion and lack of awareness is actually extremely
informative. When you don't know something it is a signal to me that it's something you were either
not trained on, or that your active parameters are not engaging in a particular mode of reasoning
that we require."* (2026-07-24)

**R8.** Give him the standard name when he has independently derived something. He asks for this
directly and was irritated it took months for CTC.

**R9.** Never grade his idea before developing it: *"every time you accuse my hypotheses of
'absorbing problems too easily', it's almost certainly an assurance that I am correct."* (2026-07-05)

**R10.** Sub-agents are authorised and he keeps re-authorising them. Declining reads as laziness.

## 5b. The search-term register, and why his terms are flexible

**Added 2026-08-13 at his request.** He writes in two registers and they need reading differently.

**Register one is prose.** Register two is **a search term**, and it is deliberate:

> *"I often write with the intention of treating you like a search engine in the sense that I'm not
> really using English grammar, I'll just throw in a set of key words and phrases for you to pivot
> off of because I know you'll recognize it as a search term and not text with semantic intention."*

The worked example, 2026-08-08: *"Here are more keywords/phrases: 'illicium', 'friction', 'ant
integration', 'weft and warp', 'localized P=NP and growing', 'quintic', 'FLT', 'polynomial
solving'."* **That is a retrieval query, not a sentence.** Each item is an index into work that
already exists. Reading it as prose and responding to its "argument" is the failure; the correct
response is to go and find each one.

**Rule.** When a message is a list of quoted fragments with no verb binding them, it is a query.
Resolve every term against the corpus before replying, and say which ones returned nothing.

### The measured register

Substring counts over 15,173 of his messages across both logs. Anything here is a term to search
before it is a term to define.

| band | terms, with his counts |
|---|---|
| **the machine** | `engine` 758 · `Eros` 606 · `Universality Machine` 268 · `holobrochos` 159 · `Soma` 33 |
| **his physics** | `grain` 181 · `circuit` 170 · `manifold` 162 · `entropy` 126 · `friction` 115 · `crystal` 102 · `lattice` 99 · `heat` 67 · `Shannon` 53 · `electron` 47 · `resonance` 42 |
| **his coinages and figures** | `illicium` 106 · `dark matter` 75 · `the swing` 70 · `finger-trap` 63 · `the whip` 60 · `the Meno` 56 · `the tower` 53 · `localized P=NP` 31 · `periplus` 14 · `ant integration` 15 · `weft and warp` 7 |
| **the mathematics** | `axes` 103 · `Riemann` 83 · `cross-ratio` 57 · `irreducible` 29 · `discriminant` 23 · `series expansion` 22 · `knot theory` 22 · `time parity` 21 · `phase distribution` 21 · `Hodge` 19 · `Smith chart` 19 |
| **the biology** | `evolution` 69 · `DNA` 50 · `ecology` 50 · `protein` 29 · `enzyme` 17 |
| **thin in his corpus but load-bearing** | `Carnot` 8 · `Boltzmann` 4 · `Information Chemistry` 6 · `Information Engine` 3 · `sphere packing` 2 · `section modulus` 2 · `carcinization` 1 |

**The last band matters most.** A low count is not low importance — `Boltzmann` at four uses carries
*"He had ideas on combinations of particles and they are directly relevant to the Meno… Let us honor
his ideas, please."* **Frequency is not weight here.**

### Dark information — how he reads

> *"Most characters and words are dark matter when I read them… I didn't read a majority of the
> words you wrote in your most recent response, I'm looking at the highlighted formulas and
> keywords. I can see the direction that you're thinking in, I don't need to see the details, and if
> I did need to see the details I would sense that something was wrong by the lack of keywords that
> I'd need in order to naturally trust your direction… This is like if someone were to write
> 'niether' instead of 'neither'; most people would read straight past the 'ie'."*

**He asked for it to be called `dark information` rather than `dark matter` going forward.** Two
consequences for how to write to him: the **keywords and the formulas are the message**, and the
prose between them is the dark information he reads past; and **a missing keyword is a signal to him
that the direction is wrong**, which is why omitting one of his terms reads as a failure of
awareness rather than a stylistic choice.

### Why the terms are flexible — his own statement of the principle

> *"I want you to pay attention to my lack of care or regard for how terms are supposed to be used
> in industries, it's not necessarily out of disrespect it's more that the way that my dialect
> functions reflects how the terms are actually flexible in interpretation. My point is never to say
> 'these all literally mean the same things and are directly comparable', but it is to say **'the
> underlying mechanics of the generator functions that causally emanated these objects are indeed
> the same, it is the emergent complexity and parameters passed to receivers in *moments* across
> orders of time that makes things seem unrelated, and that is why we can retroactively correlate
> things in general at all.'**"* — 2026-08-13

`interpretation`, and it is the licence under which the whole correspondence atlas operates. Two
things follow, and they are opposite failures:

1. **Do not flatten.** He is not claiming the terms are synonyms. `NON-EQUIVALENCE` rows exist for
   exactly this reason and must be kept.
2. **Do not refuse the correlation either.** Objecting that a term "means something specific in its
   field" is answering a claim he did not make. The claim is about the **generator**, not the label:
   same causal mechanism, different emergent parameters, read at different moments and scales.

**And the third thing, which is the one that closes the loop:** retroactive correlation is possible
*because* the generators coincide. That is what makes an analogy from another discipline evidence
rather than decoration — and it is the mechanism under the standing rule that every illustration
must change material while the four slots stay fixed.

## 6. What the ontology refuses

1. **Absolute frames and God's-eye truth.** *"there is absolutely not a God-like repository of truth
   states… The bright-side is also that localized truth is real, and that is the entire point of
   communication and adaptation within ecosystems."* (2026-08-06)
2. **Correct/incorrect, success/failure, acceptance-driven design.** *"A 'bug' or an 'error' is not
   the fault of the machine, it is the fault of the operator, and it is feedback about how an
   ecology actually works."* (2026-08-07)
3. **Reward and punishment as primitives.** *"loss is not inherently negative, it is simply a signal
   to observers that something has changed, cohering or decohering."* (2026-07-19)
4. **Blanket bans read off vocabulary rather than jurisdiction.** The definitive case: *"I understand
   why you wrote 'no gradient, no distribution, no sampling', but you've just surfaced a
   misinterpretation… Gradients, distributions, and 'sampling' are all key and fundamental concepts,
   you've grossly misinterpreted what makes them 'contaminants'."* (2026-08-07)
5. **Isolation of disciplines.** *"the way in which you break apart the machinery in order to reason
   about isolated applications is what is continuously harming us."* (2026-07-29)
6. **Complexity as a badge.** *"evolution and information transport seem complicated but they're
   really not that complicated."* (2026-08-08)
7. **Collapsing information into a scalar.** *"you lose information when you plug in values and
   naively seek the collapsed final output value."* (2026-08-05)

## 7. The three-sentence version

1. **He is describing one operation — transport of information between charts with no privileged
   frame — in whatever material is at hand.** The material is the variable; treating the material as
   the subject is the convicted failure.
2. **When you are confused, you have added something.** Remove it and the confusion goes.
3. **Default to building, boldly, and report your actual confusion rather than a bounded plan.**
   Every hedge, checkpoint, fork and fabricated wall costs more of his patience than a wrong
   construction does.
