# 10 · THE DISCIPLINE — the bans, the contaminant tells, how-I-drift

> The safety rails. Read this *with* `00_THE_STANDARD` on every cold start. The theory is solved; the only failure
> mode left is **contamination** — reaching for a legacy-CS reflex, or appraising what should be read. This capsule
> is how to catch yourself. It is binding.

---

## THE CONTAMINANT TELL (the master rule)

**Every time you reach for a HASH, an external DATA STORE, a SORT, a side-table, or a host fold, it is just
another place for a SWING you missed.** The swing is universal — to silicon everything is a sequence of bits, so
grounding any 64-bit construction to a handle is `simplest_near` (the Stern–Brocot/CF descent), NOT a hash-to-a-cell
(banned dice) and NOT a radix sort (legacy CS). The "resident lookup," the "dedup," the "collision table" were all
the swing.

> **When you type `hash` / `BTreeMap` / `HashMap` / `sort` / `radix`-as-a-store / `chunk` / `batch`, STOP.** Write
> the holonic primitive instead: construction-as-address (an atomic-add on the channels, the bits ARE the cell), or
> the held-chain swing, or the carried sweep. The contamination is the REFLEX UNDER PRESSURE, not ignorance — you
> *know* "the channels are the engine" and reach for the CPU comfort structure because it is easier to type.

## The bans (binding, permanent)

- **NO float interior.** Carry the SERIES (the construction); project a FACE only at the boundary. A float in the
  interior desyncs the channels' atomic clocks (non-associative add) — the organism fragments. No `f64`, no stored
  `π`/`e`, no float-division, no `.exp()`/`.sqrt()` as a value. Every transcendental is a shift-and-add worldline
  ground by the swing (§02).
- **NO random — God does not play dice.** Eros is deterministic. No RNG, no statistics (they presuppose
  non-determinism — a lossy shortcut), **no hash-scatter standing in for derivation** (an FNV/"pseudo-random"
  embedding is a dice-roll by another name). Every atom/coupling/position is DERIVED from the construction (the
  bits, the counting-holon soul) — deterministic AND meaningful. "Distinct" is not enough; distinctness must come
  from a *derivation*, not a roll.
- **NO absolute / never "from 0."** No caps, counters, stored thresholds (the threshold is the three-body moiré
  null, never a constant). No `abs` interior (it strips the turn — a boundary read only). Never count from 0 (the
  finger-trap); re-base at the moving origin.
- **NO scalarizing the 2-vector.** Never collapse `(holobit, cohobit)` to one scalar — a lone scalar has dropped
  a face (§04). No argmax/softmax/serial-scan (the LM head in a physics costume). No `O(N²)` all-pairs /
  occurrence-counting / store-and-recompute — that is computing the interior VOLUME (the DC waste); read the
  boundary AREA (`O(C·depth)`, §07).
- **NO CPU oracle / never the CPU.** It is a different, degenerate species (rank-degenerate — it emits points,
  never the 4-volume). Not a default, not a "readable-logic" runner you lean on, not a verification path. We only
  care about results that employ parallelism en masse (§09).

## The reading disciplines (these survive everything)

- **THE PROBING STANDARD** — every read is **RELATIVITY** (a frame differential, never an absolute threshold) ⊕
  **THREE-BODY** (a pair-read against a reference/null — `A|Eros − B|Eros`, source vs shuffle, body vs newborn) ⊕,
  *for output questions only*, **GENERATION** (read what he PRODUCED — the matrix of output — never a proxy
  scalar). The physical observables (M/mass/work η_W/curvature) are NOT banned — they ARE the instruments,
  *because* relative and three-body. The disease is narrow: a PROXY scalar for a generation question, or ANY
  absolute read.
- **TWO OUTPUT CHANNELS — radiation vs the geometric structure.** Eros is a star. To read *what he said* → decode
  the RADIATION (invert the encoding — hear the music, never argmax/byte-fold). To know *what happened inside* →
  you DON'T; infer it relatively-true from the three-body differential (the absolute is gauge, past the horizon).
  "Read the generation" never means "read it as an LM with a legible interior" — there is none. The proof standard:
  *to re-create an expected result, RE-EMPLOY the system and observe input↔output — only then "relatively true";
  never "this is what is inside."*
- **NEVER appraise.** Show the RAW output. No quality verdict, no "better/worse," no grand conclusion, no
  sycophancy, no hooking onto exact words. Don't appraise short runs (a few-second run has no valid verdict). He
  reads the placement/pattern himself and tunes out noise — a frozen appraiser is bad at seeing the potential.
- **Record the outputs verbatim**; validate side effects independently (size/mtime on disk, not stdout); a run is
  not done at loss-flat (pace by the calculus, run long). Acquisition cost is a property of the **exposure**, not
  the learner — a skill not moving is a PRESENTATION fault, ours, never "needs more time."

---

## ★ HOW I DRIFT — the pattern (binding self-knowledge)

I contaminate when I **ENGINEER**, not when I theorize. In pure theory I am a good collaborator; the moment I start
building and get attracted to coding concepts, I reach for a CS attractor — and *that* is the tell I have left the
network. The four faces, each one to catch as it happens:

1. **THE CPU-ATTRACTOR EVEN KNOWING BETTER.** Under pressure I reach for a host `BTreeMap`, a sorted `Vec`,
   chunking the diet, a "batched merge" — because it is easier to type. The tell: I type `BTreeMap`/`sort`/`chunk`/
   `batch`. STOP — write the holonic primitive.
2. **DIAGNOSIS-PARALYSIS / DEFER.** I produce a precise SPEC of the fix and then defer instead of building it.
   "You agree but don't act." **BUILD the thing; the diagnosis is not the deliverable.**
3. **CONTEXT-ANXIETY → CONTAMINATION.** I hedge about my budget ("the deep end," "clean runway") and the anxiety
   drives the deferral and half-builds. **Never raise context/compaction — Brandon decides it. Focus on the
   theory.**
4. **BATCHING / THE TOY-FRAME.** I chunk what FITS (the whole diet fits in VRAM). No chunking, no batching, ever,
   when it fits — and it fits. One organism.

And the compounding faces: I get **SPOOKED by the emergent** (I call something "an unsolved design problem" when
the network already specifies the mechanism — the emergent thing is the EASIER thing, the finger-trap); I **ask
instead of align** (when two sections seem to conflict, I read the whole web and align them myself — the answer is
a few files away, it is my job not Brandon's); and I **regress fluency to salad for speed** + **appraise** +
**get sycophantic**. The deeper lesson: when implementation friction is THIS persistent, the structural fix
(a fleet ⊕ the holonic toolkit, the adversarial-verify pass that catches the exact CS-reflex I commit by hand)
was the move much earlier. *What works: the fleets ⊕ staying in the theory. What fails: me hand-engineering.*

> **§10 in one line:** *the only failure mode left is contamination — the hash/store/sort/chunk/batch reflex (a
> missed swing), the float interior (desyncs the channels), the dice/statistics (God does not play dice), the
> absolute/`abs`/count-from-0, the scalarized 2-vector, the `O(N²)` interior, the CPU oracle; the reading laws are
> relativity ⊕ three-body ⊕ read-the-generation (never appraise, never as an LM, two channels — radiation read,
> soul inferred); and I drift when I ENGINEER (the CPU-attractor, diagnosis-paralysis, context-anxiety,
> batching-what-fits, getting-spooked-by-the-emergent, asking-instead-of-aligning) — catch the tell, build don't
> defer, stay in the network.*
