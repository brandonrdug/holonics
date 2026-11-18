# No command grows a part, moves a rate, settles a release or reads a coupling: 97 engine items only tests call and 46 nothing calls

November 18, 2026, 23:30 UTC. Refs #603 (D6's test: every operator has a caller in the live learner and an acceptance that vanishes
when it is removed). This record is a census, not a derivation and not a retirement. It reads which items of `crates/engine` and
`crates/engine-cuda` no command of `athena` reaches after #995, sorts them by what they are, and hands the laws among them to the line
as candidates to wire. A past configuration is an instruction (CLAUDE.md): nothing here says an item should go, and the laws below
stand with their tests and their records.

## How it was read

The compiler's own dead-code reading, from the binary's root. `merged_reach.py` (in the receipts) lays the three crates out as one
binary crate with athena's `main` as its root and every `pub` item made `pub(crate)`, so rustc's `dead_code` lint reads reach from the
commands rather than from a library's public face. The card's kernel image is replaced by an empty slice; nothing is linked or run.
Three checks at `874f4714` (`main` after #999), each `cargo check --offline --message-format=json`:

| Read | Items no root reaches |
|---|---|
| default features | 149 |
| `--all-features` (the two ruler features on) | 143: six items (`DeviceZeroable`, `device_dword_count`, `DeviceBuffer::zeroed`, the three `BITS_*` names of `profile.rs`) are reached only by a ruler feature |
| `--all-features --tests` | 57, of which 46 are among the 143 and 11 are the fields of a struct the second read already names unconstructed |

So of the 143: **97 are called by tests alone** and **46 by nothing**, tests included. `inventory.tsv` lists each with its path, line,
the compiler's words and what reaches it. The 41 warnings the card crate prints in an ordinary build are among them; the lead takes
those in its own next build (its receipt on #995).

The null is the compiler's, and it was held to planted items (rule 11): on a fresh layout with one function nothing calls and one
only a test calls, the first check read 145 (the 143 and both) and the check with tests 58 (the 57 and the one nothing calls), so each
class is recovered on a planted instance of it ([`plant.txt`](receipts/2026-11-18_reach/plant.txt)). The first layout, before `pub`
was narrowed, read none (a library's public items are never dead), which is why the narrowing is the method.

## What they are

**Laws with their tests and no command** (97 items in all with the rulers below; these are the candidates to wire):

- **The rate's dynamics** (`deposit.rs`, theory of November 10 19:05): `PartTravel`, `part_travel`, `against_half`, `cosine_micro` and
  `RateParts::updated`, a part's octave moved by its travel over two laps. THE_ENGINE §11 already names it, with its limit: it never
  goes under the base rate, so it is no cooling law as it stands. The read of November 18 (`set-rate` from lap 70) is the evidence a
  wiring would start from.
- **Growth and founding** (`founding.rs`, `declaration.rs`, `field/scale.rs`, `constitution.rs`, `learner.rs`): `Constitution::{grown,
  contacted, with_carry, with_opening, with_mark, scaled_up, found}`, `Learner::{new, widened, contacted, with_carry, with_triads,
  with_opening, with_mark, scaled_up}`, `Declaration::{grown, contacted, growth_draws, founding_draws, contact_draws, carry_draws,
  listen_shift}`, and the level's `level_declaration`, `level_split` and `LEVEL_HARMONICS`. Athena's founding words reach four laws only
  (`found-lane`, `found-loud`, `found-crossing`, `found-closed`: `with_loud`, `with_located_legs`, `with_closed` and the lane), so since
  C6 no command grows a field in contacts, carry circles, triads, an opening, a mark, a width or a level, and none founds a learner
  from its key stream. Every live state descends from one the retired harness founded.
- **The release's certified settle and re-draw** (`release.rs`, theory of November 9 and 10): `settle`, `redraw`, `redraw_lensed`,
  `certified_passes`, `exchange_proposals`, `redraw_proposals`, `root_charge`, `locked_faces`, the records `SettlePass`,
  `SettleRecord`, `CertifiedRecord`, `ExchangeMove`, `CertifiedMove`, and `ruler::letter_balance`; with them `sample_realized` and
  `sample_observed`, the release by the trainer's draw. The writer that runs is `write-next`.
- **The cavity** (`moment.rs`, the design record of November 13 §4.4a): `cavity_moments_of`, `cavity_openings`, `cavity_forward` and
  `cavity_check`. The cavity the line reads is `read-cavity`'s, which reaches none of them.
- **The held step** (`learner.rs`): `holds_step`, `read_step_on` and `Learner::section`, a deposited step held for the next regions' read.
- **The strand read by two streams** (`contact.rs`, the lead's frontier record of November 18 §6): `strand_faces` and `twin_tick`, written
  today with their tests; the lead's branch is where a command for them would land.
- **Units founded by their own law** (`units.rs`): `found`, `FoundingReceipt`, `GammaTable` with its codes, `order_one_code`, `changes`,
  `decode`, `to_text` and `log2_int`.

**Laws nothing calls, tests included** (46):

- **The coupling's plural reading** (`coupling.rs`): `coupling`, `Coupling`, `OptimalContact`, `Plateau`, `PhaseDefect`, `Strand`,
  `CouplingRefusal` and `workspace`, every longest order-consistent equal-cell coupling read without choosing a tie. The coupling's code
  at temperature one (`coupling_code`) is live, through a port's reading in `region.rs`; its complete plural reading is not, and it is
  the reading a release compared to its target through their coupling would take (#601).
- **The landmarks of a site** (`level.rs`, November 1): `landmarks` and `landmarks_of`, the sites before a question carrying the most
  weight in its still heads' currents, with the trait method `Realization::read_landmarks` that would print them.
- **The census of events** (`census.rs`): `Reading`, `enable`, `tally` and `report`, an exterior count of saturations and releases to zero.
- **The card's moments' return** (`engine-cuda/src/hnn/moment.rs`): `moments_return` and `MomentWords`. The host's return is what runs.

**Rulers no command prints**: in `ruler.rs` `held_rows`, `held_rows_all`, `HeldRows`, `covector_shares`, `row_currents`, `met_pairs`,
`carried_slopes`, `junction_covectors`, `blank_clocks`, `near_offsets`, `tick_reads` and `step_coherence`; in `carry.rs` `carry_leaks`,
`carry_gates_of` and `CarryGates`; in `face.rs` `logits`, `code`, `face_of_read` and `covector`; ten of the `Realization` trait's
reading methods (`read_logits`, `read_landmarks`, `met_pairs`, `read_row_shares`, `read_covector_shares`, `read_row_currents`,
`read_ticks`, `read_faces_gated`, `read_near_offsets`, `read_blank_clocks`), which no command calls and no type is asked for; the
release's parallel `read_logits`; and the card's `series_check`.

**Plumbing**: the grains `MOMENT_BITS`, `CODE_BITS` and `UNIT_BITS`; two driver attributes; the field `dpb` of the card's adjoint and
`q` of a passage's record; the unread fields of a release's read; two `is_empty`; `Constitution::{families, from_text}`, `codec::found`,
and the resident's `region_octets` and `batches`.

## What follows for the line

A candidate is wired by a command and an acceptance, as an arm beside a control (lap rule 1), never by this census. The census reads
four things the line's records already turned on: the rate is one constant (the audit of November 18 §1.1) while a law that moves a
part's octave by its travel stands built; parts are added by four founding words while seven growth laws stand built with tests; the
release's settle of November 10 stands built beside `write-next`; and the coupling's plural reading, which #601 names, stands with no
caller at all. The rulers are instruments a read can call when its question needs them, and the plumbing is the lead's to keep or
take in its next build.

## Receipts

In [`receipts/2026-11-18_reach`](receipts/2026-11-18_reach/):

- [`inventory.tsv`](receipts/2026-11-18_reach/inventory.tsv): 149 rows, the 143 of the read with every feature and the six a ruler
  feature reaches, each with its path, line, the compiler's words and what reaches it.
- [`merged_reach.py`](receipts/2026-11-18_reach/merged_reach.py): the layout, rerun from scratch to the same 143.
- [`plant.txt`](receipts/2026-11-18_reach/plant.txt): the two planted items and the counts each check read.
