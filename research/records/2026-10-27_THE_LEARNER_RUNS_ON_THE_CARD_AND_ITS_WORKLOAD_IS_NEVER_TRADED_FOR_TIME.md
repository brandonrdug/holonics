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
| October 20 | The complete-language trainer gains a card executor; its dataset run waits on authorization in its record. Brandon approves two narrow runs that day: a CPU correctness reference (40 minutes, four cores, 8 GiB, five passes) and a GPU training plan whose scoring and output run on the CPU. Neither covers the tower runs that follow. |
| October 23 | The moment tower (`hnn::tower`) is built and trained on the host, eight threads. |
| October 25 | `TowerCard` runs the gated tower's pass on the card with the host's bits, 3.9 times the host at 96 streams; the record names the host's certificate as the next loop's subject. Its training route (`tower_pass train complete-language`, through `tower_classes::train_realized`) runs the class-passage trainers' pass on the card, and the October 25 training pass ran there; but every pass of that route reads its held-out passage on the host (`tower_train::held_out`, `Tower::read_cells`, rayon), and no unit-tower trainer selects `TowerCard`. |
| October 26 to 27 | Thirteen arithmetic towers (C, F, PP, PR, PRT, PRS, PRN, PRC, PRK, PRI, PRA, PRJ, PRE) and the bank, role and replay runs train through the host realization under `RAYON_NUM_THREADS=8`, two levels of 64 modes, eight streams, three passes of 3.5 MB, deadlines of tens to hundreds of seconds. The card ran none of their learning; the logs show the host realization ran, not what else held the card. Each new face (ring, turn, pump, pair face) is one `TowerCard::admits` refuses, and the rotor and strands are ones it cannot see (`ResidentLaw` does not carry them), so the work could not have gone to the card without a port. No record names a device. On October 27 the eight healed re-reads of design's review run on the host, eight threads, launched before the ruling: the written read has no card realization yet. |

**Who.** The design thread wrote the briefs and its sessions on the PC launched the runs. The
coordinator relayed their results, and no review asked which device ran, this thread's own review of
October 27 included. The waiting standard in the guides was written entirely in host threads and
CPU seconds. Its clause that an unmeasured run is planned at one to three minutes, beside "never
raise a limit", pushed the workload down where it should have pushed the device up. This is the
third recurrence of the same failure (September 20, October 18, October 23 to 27). The card's runs
of those days are the October 25 parity and training pass of the gated, rectifying tower on the
4080, a narrower law than the towers trained after it; its record leaves 14 of the observed-epoch
port's library tests failing, failures it found already present on main. Brandon's two narrow
approvals of October 20 are the only host exceptions on record, and neither covers these runs.

## The rule

The guides now carry it (section "GPU first, and the design fixes the workload", and the amended
waiting standard). In short:
- Learning runs on the card; the host realization checks the card's bits.
- A new part enters a learner run with its card realization and its parity against the host.
  Learning on the host needs Brandon's own exception, in his words, naming the workload, its purpose
  and its limits; a brief, a worker or another agent cannot grant it, and without it the run is
  blocked. A host learner run without it is a defect and incomplete evidence.
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
  trainers routed through `TowerCard`, the held-out read through the realization, then the plain
  gated two-ladder tower on the class passage (alphabet 257) through the October 25 card route, on
  the 4080, for hours of laps in segments under the card lock, with its writing shown each hour. Not
  on units: founding a unit alphabet has no card realization yet, so a units run would need host
  learning; the unit trainer's card route stays built for when the founder is ported. The written
  read's card realization is owed by design too.
- **The refused faces on the card** (this thread for the pair, ring and turned faces; design from
  the pumped face on, one Opus worker since October 27): the pair face first, then the ring,
  turned and pumped faces, then the rotor and the strands, in `kernels/tower.cu`,
  `holonics_cuda::hnn::tower` and the `ResidentLaw` exports of `hnn::tower::realization`.
  Acceptance per face, fixed before its build as on October 25: 32 sections equal face by face and
  covector entry by entry, host against card, and one full pass with the host's SHA-256.
- **The rule in the guides and this record** (this thread).

Until each acceptance passes on the PC, its repair is reported as built, not as done.

## Status, kept in three parts

Each part is ticked here when it changes, and none stands for another.

| Part | Status (October 27) |
|---|---|
| The policy documented | Done: the guides' section and this record, PR #528, merged as `bc642aa`. |
| The gate built | In part, on `claude/project-thread-1tl3uo`. Built by design: the certificate decided by partition (log₂ readings, the exact products as fallback), `train-unit-tower` through `TowerCard`, the held-out read through the realization (`Tower::read_parts_realized`), `TowerCard` refusing the rotor, the strands and openings with ring hands or strand residues, and its counters counting only completed launches; then the release through the realization (`Tower::advance_realized`, `tower_pass release`) and the host route's refusal of every command unless `HOLONICS_HOST_EXCEPTION` names a manifest that binds it to Brandon's exception (his words, this run's command, its limits) or to the card release it checks (its card log holding that release's `TOWER_REALIZATION card` and `TOWER_COMMAND` lines; `complete_language::host_exception`, whose run prints the `DEVICE` line with the manifest's SHA-256). Epime's source review of `edb3c11` (October 27, read-only) confirmed the partition certificate and named four defects, now repaired: a class read or compared outside the alphabet is refused before any realization (`Tower::admit_read`; the card's face read zero there and the readings took zero as one), a zero mass or total goes to the exact products, the realization admits the run's whole law and the trainer refuses zero passes before any output (`PassRealization::admit`), and the host route needs the exception above. Its fourth note, the held-out read padding its last short part with class zero, costs at most one part's work and changes no code. Its second note (after the PC's checks at `4374a509`), repaired: the 320-stream parity's host reference held every stream's cells for its reverse (projected 22.3 GB against 11.7 GB available), so `HostPass` keeps none between calls and reads each stream's forward again; the section, the realized read and the realized advance call `admit_read` themselves; the exception is the manifest above; and `race.sh` stops on the window and on unread windows. Owed: the written read on the card (design); the pair, ring, turned, pumped, rotor and strands faces with their parity (PR #529: the pair, ring and turned faces each pass their 32 sections on the 4080, their full passes by SHA-256 owed, and with the ring the card reads openings with ring hands; the pumped, rotor and strands faces and the full passes pass from the review thread to design, which merged PR #529's branch into its own on October 27). |
| The gate independently verified | Not yet. Owed: a review by a worker that did not build it (Epime or a reviewer thread) of the trainers' refusal and of one card run's device line, and the per-face parities run on the 4080. |

## The recorded failures this step could repeat

- *A refusal answered with a larger limit*: no limit is raised; a run that does not fit changes
  device or partition, never the workload.
- *A located cause carried unrepaired into a new consumer*: the certificate's cost was located on
  October 25 and carried through two days of runs; it is repaired before the long run reads it.
- *An uncertified deposition step*: the certificate's decision stays the exact products'; only how
  fast it is reached changes.
- *Bits read as progress*: the long run reports bits beside its writing and mutual loss, never as
  its success.
