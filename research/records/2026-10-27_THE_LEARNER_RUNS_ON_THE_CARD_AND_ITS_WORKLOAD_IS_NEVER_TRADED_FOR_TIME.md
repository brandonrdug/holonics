# The learner runs on the card, and its workload is never traded for time

Refs #404 #76. Status: [project-postulate; agent-inferred, October 27]. The review thread's record of
Brandon's GPU-first ruling, the drift it answers, and who owns each repair. Owners: the guides
([CLAUDE.md](../../CLAUDE.md), [AGENTS.md](../../AGENTS.md), "GPU first, and the design fixes the
workload"), `holonics::hnn::tower` (the section's certificate, `fewer_bits`) and
`holonics_cuda::hnn::tower` (`TowerCard`).

## The ruling

Brandon, October 27 (paraphrased; his words stay in the conversation). The tower converges because
it is plastic, not because it is already sharp. He holds a GPU-first view and has said so plainly;
the RTX 4080 SUPER matters because it is a consumer card, so the aim is a plastic network that runs
fast on it, never transformer-style vertical data scaling. He asked for the card to be used, for a
policy on its use, and for the run rules to stop being kept at the expense of everything else:
holding a time limit and a compute limit while the data shrinks and the architecture degrades swaps
the quantities the rules were meant to conserve.

## What happened

Read from the records, the code and the briefs:

| Date | What the record shows |
|---|---|
| September 20 | Brandon flags a run on one CPU thread with little GPU use. |
| September 30 | The learning-failure diagnosis records that the card carries none of the learning path. |
| October 18 | The PC link finds `RAYON_NUM_THREADS=1`, `CARGO_BUILD_JOBS=1` and `RUST_TEST_THREADS=1` in the run wrappers; the pin is retired. |
| October 20 | The complete-language trainer gains a card executor; its dataset run waits on authorization in its record. |
| October 23 | The moment tower (`hnn::tower`) is built and trained on the host, eight threads. |
| October 25 | `TowerCard` runs the gated tower's pass on the card with the host's bits, 3.9 times the host at 96 streams; the record names the host's certificate as the next loop's subject. No training driver selects `TowerCard`: its only callers are the `tower_pass` example and its test. |
| October 26 to 27 | Thirteen arithmetic towers (C, F, PP, PR, PRT, PRS, PRN, PRC, PRK, PRI, PRA, PRJ, PRE) and the bank, role and replay runs train on the host under `RAYON_NUM_THREADS=8`, two levels of 64 modes, eight streams, three passes of 3.5 MB, deadlines of tens to hundreds of seconds. Each new face (rotor, ring, turn, pump, strands) is one `TowerCard::admits` refuses, so the work could not have gone to the card without a port. No record names a device. |

**Who.** The design thread wrote the briefs and its sessions on the PC launched the runs. The
coordinator relayed their results, and no review asked which device ran, this thread's own review of
October 27 included. The waiting standard in the guides was written entirely in host threads and
CPU seconds. Its clause that an unmeasured run is planned at one to three minutes, beside "never
raise a limit", pushed the workload down where it should have pushed the device up. This is the
third recurrence of the same failure (September 20, October 18, October 23 to 27).

## The rule

The guides now carry it (section "GPU first, and the design fixes the workload", and the amended
waiting standard). In short:
- Learning runs on the card; the host realization checks the card's bits.
- A new part enters a learner run with its card realization and its parity against the host, or
  under a host fallback declared in the brief before launch. An undeclared host run is a defect and
  incomplete evidence.
- Each receipt states the device, the card's time, the host's time and threads; a dominant host
  share is the next loop's subject.
- The design fixes the data, the passes and the learner's levels and modes. A run that does not fit
  gets the card, a better partition, or a stated long run, never less data, fewer passes or a smaller
  learner.
- Whoever launches owns the device line, and the reviewer and coordinator read it before a result.

## The repairs and who owns them

Proposed by the design thread and accepted here on October 27, by files, so the branches cannot
diverge:
- **The certificate** (design). The October 25 record found the pass held to 3.9 times the host
  because `fewer_bits` multiplies every face of a section into four big integers (0.5 s a section at
  320 streams). Design reads it first on integer `log₂` readings of each numerator and denominator,
  decides when the summed difference clears the readings' total slack, and otherwise falls back to
  the exact products, so the decision is the products' in every case. Acceptance, fixed before the PC
  run: (a) on a full pass of the October 25 docs passage at 24 and 320 streams, the new and old
  certificates agree on every call; (b) the saved learner's SHA-256 equals the October 25 receipt's;
  (c) the host part a section is reported beside the card's time.
- **The trainers on the card and the first long run** (design): `train-unit-tower` and the other
  trainers routed through `TowerCard`, then the plain gated tower on units, on the 4080, for hours of
  laps, with its writing shown each hour.
- **The refused faces on the card** (this thread): the pair face first, then the ring, turned and
  pumped faces, in `kernels/tower.cu`, `holonics_cuda::hnn::tower` and the `ResidentLaw` exports of
  `hnn::tower::realization`. Acceptance per face, fixed before its build as on October 25: 32
  sections equal face by face and covector entry by entry, host against card, and one full pass with
  the host's SHA-256.
- **The rule in the guides and this record** (this thread).

Until each acceptance passes on the PC, its repair is reported as built, not as done.

## The recorded failures this step could repeat

- *A refusal answered with a larger limit*: no limit is raised; a run that does not fit changes
  device or partition, never the workload.
- *A located cause carried unrepaired into a new consumer*: the certificate's cost was located on
  October 25 and carried through two days of runs; it is repaired before the long run reads it.
- *An uncertified deposition step*: the certificate's decision stays the exact products'; only how
  fast it is reached changes.
- *Bits read as progress*: the long run reports bits beside its writing and mutual loss, never as
  its success.
