# The order repair, pinned before its runs

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the construction and the pins; [measured] for the development reads (§3), which
used development seeds and the text's choosing role only.

**Occasion.** Recorded failure 4 of the
[lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md): the
native readout sat at the byte marginal. It was located on September 25
([§5](2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md#5-the-source-and-encoding-the-table-without-its-index):
the phase-binned moment carries "the table without its index") and carried unrepaired into
`hnn::prediction`, whose text sections after the certified step were spaces and held readings.
Brandon's lens on the repair (September 29, relayed): "offset moments? modulo, remainders? spectral
placement". Order is not built as a table of pair counts at offsets; it is built from residues and
relative phases.

## 0. The recorded failures this work could repeat, and how each is avoided

- **2, recitation or an index.** The section's own data re-enter as a placement: counts on one ring
  over their own population, the source moment's law, nothing kept after the refinement's return.
  No offset table, no buffer, no window and no suffix depth is read; the request enters only through
  its phase-carried moment, as before. Held-out requests are fresh draws no run has read.
- **3, text as the exception.** The construction reads residues and relative phases only: a datum
  at its tick's residue, a station reading placed data by the rotation between them. §1 states it
  for an image scan, an acoustic stream and a motor word. Nothing reads a byte's value, a codec or an
  alphabet's meaning; the text run changes only the declared period.
- **4, the byte-marginal readout.** It is this loop's subject. Acceptance 2 measures it on a terrain
  whose continuation is fixed by order and whose marginal is uniform, against the static marginal
  and the per-station marginal on the same held-out stations, with the September 29 readout run on
  the same draws as the located failure's control.
- **7, bits read as progress.** Bits are printed beside the outputs. Text is judged by its 8
  sections alone; a held or illegible section is a failed output whatever the bits.
- Also **1** (no authored routine: the terrain's rule makes its truth; the machine learns it through
  its own deposition, and the lock is the release law's order, not a solution routine), **5** (the
  certified step is used as it is, in `hnn::constitution`, untouched), **6** (the held-out requests
  are fresh draws) and **9** (every bound is fixed here; no run is repeated with a larger limit).

## 1. What is built (`af5e7de6`)

**The construction** (`hnn::prediction`'s header, "Order is carried by residues and relative
phases"; `hnn::moment::SourceMoment::section`; `hnn::ratio::HolonRatio::compare_partition`):

- **Remainders.** Each datum is placed on the receiving ring's spectrum at its residue, by the
  source moment `m = Σ_k Ĝ(τ_k)⁻¹ E u_k`, unchanged. The ring's period is declared as a product of
  pairwise coprime factors, `D = 3·4·5 = 60` on the terrain and `D = 5·7 = 35` on text, so a datum's
  residue is its joint residue class and the ring resolves position modulo `D` (Lean
  `HNN/Prediction.joint_residue_determines_position`, the Chinese remainder theorem on positions).
  Station `j` reads every placed datum by the relative phase `P^(1+j+age)`, the ratio of the
  station's rotation to the datum's. The joint class lives on the product of the factors' spectra
  (one ring of period `D`, whose modes are the products of the factors' modes), because a sum of
  separate factor placements carries only the factors' marginal modes: the indicator of one joint
  class is not a sum of per-factor functions (`joint_class_not_additive`). A field of three small
  rotor rings summed linearly would read three residue tables without their index.
- **Relative phases between placed data: the section's own order.** A refinement's locked data are
  placed on the same spectrum at their stations' residues `τ + 1 + j`, over their own population
  (the response's port, source contract item 2), and every refinement reads the request's placement
  and the section's together (`prediction::injection`). Station `j` reads its own datum at rotation
  zero (`placed_at_station`) and its neighbours' by their relative phases.
- **Generation** (`prediction::generate`) opens with nothing locked. In each refinement every
  unlocked station is read from the one refined field, and every station whose top grain cell leads
  its runner-up by the largest gap `(n_top − n_2) L + (k_top − k_2)` locks, ties together. A locked
  datum re-enters as placed data. It stops when every station is locked (released at width zero:
  every lock read a unique top, `lock_reads_unique_top`) or when the largest gap is zero (held, the
  unlocked stations plural). At most `m` refinements.
- **Learning** (`prediction::stage`, `prediction::mask`). A training refinement draws a partition
  (the absorbing corruption chart: the number of locked stations uniform on `0 … m − 1`, then that
  many stations uniformly), places the targets of the locked stations and compares only the
  unlocked ones (`HolonRatio::compare_partition`), so no compared station reads its own target
  (`partition_reading_ignores_compared_targets`). Both placements enter through `E`, and
  `reference::compose_return` reads each against its own counts. Nothing locked is the September 29
  path exactly.

**The consumer equation** is unchanged: `ρ(F^K(I_h ⊕ placed section)) = T(request)` at the released
section, checked on the terrain's truth.

**Every modality reads it the same way.** A datum is placed at its tick's residue on a ring's
spectrum, and a station reads placed data by relative phase:
- text: a byte at its tick;
- an image scanned row by row: a pixel at its scan tick, so its left neighbour lies at relative
  phase 1 and the pixel above at relative phase `w` (the row width, below `D`);
- an acoustic stream: a sample at its sample tick, a periodic component of period `p` a relative
  phase `p`;
- a motor word: each screw at its step.

The section's locked data are placed data of the same kind in every case.

The computational object is the helical pair interaction. Of the winding guide's six objects the
loop touches four:
- **the helix**: the ring's residues and the joint residue class;
- **the pair**: the relative phase between two placed data, the ratio of two rotations;
- **faces and placement**: the section's placement and the lock at the grain;
- **the tube**: the section's span, `m` stations on the response clock.

The cell holonomy and the tower thread stay attached through the field's complex and its carry
chain (rings 1 and 2 step by ring 0's carries).

## 2. The pins

**The field for the terrain** (`hnn_prediction.rs`, `declare` at `order_declared`): ring 0 of
period `D = 60 = 3·4·5`, the source and receiving ring, its lock every port; rings 1 and 2 of period
60 stepping only by carries; a chain `0 — 1 — 2` joined node to node on every node at exponent 0; no
pair offset; `|A| = 5` (four symbols and the termination); `K = 2` words of `w = 1` tick; `m = 8`
stations; a deposit every 16 refinements; `Constitution::initial` with every step certified, as
committed (`hnn::constitution` is not touched). Nothing is authored for the terrain.

**The order-2 terrain** (`order_pairs`): a request of `n = 40` cells drawn uniformly from the 4
symbols; its target is the continuation `x_t = x_(t−2) + 1 (mod 4)` over the 8 stations. Each
station's target is fixed by the cell two ticks back, so by order; its marginal is uniform. `n = 40`
passes the September 29 ring's period 32, so that ring aliases the request's last cells, and
`n + m = 48 ≤ 60`.
- Training: 512 requests from `Draw::new(2_026_092_901)`; partitions from `Draw::new(2_026_092_904)`.
- Evaluation: 256 fresh requests from `Draw::new(2_026_092_902)`, each generated by locks. They are
  unread by any run: a request is one of `4^40`.

**Acceptance 1, the internal checks.** On every training refinement: the balance closes, the
pairing is exact on the executed charts, the commit's balance closes, the committed energy bound
holds, and every locus outside the diamond is unchanged at every deposit. On every generation
refinement the balance closes. **Passes** when every count equals its refinements (or deposits).

**Acceptance 2, the marginal test** (`hnn_prediction -- order2`). **Passes** when the stations
right on the 2,048 held-out stations are strictly more than both of these, counted on the same
stations:
- the static marginal's (the class most frequent in the training targets);
- the per-station marginal's (each station's most frequent training class).

A held section counts no station right. The exact sections, the stations right by station, and the
same counts for the September 29 readout on the same draws (`order2 pinned`: period 32, every
station compared with nothing placed, one refinement's release) are reported beside it.

**Acceptance 3, text** (`hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin <owner-only
file>`). The field is the terrain's with `D = 5·7 = 35` (at least the 32 stations), `|A| = 257` and
`m = 32`.
- Training reads the U6 split's choosing role: its 385 request relations whose response opens an
  agent part, in letter order, two passes (the pinned bound of 1,024 exceeds them), with partitions
  drawn as above. No `--read-reserve` is passed, and the evaluation window is never read.
- Generation answers the 8 validation requests F0's rule selects (`RELEASE_SEED = 20_260_929`).
- The sections are written whole to an owner-only file and shown in the conversation only, with
  nothing beside them. A held or illegible section is a failed output; the training code is
  reported beside, never as the result.

**Time and memory.** Training stops at 540,000 ms and the resident set is capped at
20,000,000,000 bytes, as before; a run that stops is reported incomplete and is not repeated. The
projections, from §3:

| Run | Projection | Peak resident set |
|---|---|---|
| `order2` | training about 160,000 ms, generation about 80,000 ms | about 1,200,000,000 bytes |
| `order2 pinned` | training about 75,000 ms, generation about 10,000 ms | about 400,000,000 bytes |
| `text` | training about 270,000 ms (770 refinements), generation at most about 60,000 ms | about 900,000,000 bytes |

## 3. The development reads (development seeds 21 and 22; the text's choosing role only)

Every read closed every balance, pairing and commit, held the committed energy bound at every
commit, and left every unreached locus unchanged. The held-out stations are 512 (64 requests).

| Read | Training | Released | Exact | Stations right | Static marginal, per station |
|---|---|---|---|---|---|
| order repair, `D = 60`, `n = 40`, `K = 2` | 512 | 64 | 8 | 216 | 128, 132 |
| order repair, `D = 60`, `n = 40`, `K = 2` | 1,024 | 64 | 3 | 177 | 128, 132 |
| order repair, `D = 60`, `n = 40`, `K = 1` | 512 | 64 | 10 | 220 | 128, 132 |
| order repair, `D = 105 = 3·5·7`, `n = 40` | 512 | 63 | 4 | 228 | 128, 132 |
| September 29 readout, `d = 32`, `n = 40` | 512 | 20 | 0 | 88 | 128, 132 |
| order repair, `D = 60`, `n = 16` | 512 | 64 | 17 | 288 | 128, 144 |
| September 29 readout, `d = 32`, `n = 16` | 512 | 35 | 2 | 202 | 128, 144 |

[agent-inferred] **The choices.**
- `D = 60`: `D = 105` reads as well at two and a half times the cost (725 ms a refinement, a peak of
  3,269,349,376 bytes).
- 512 training requests: 1,024 read worse on the development draws.
- `K = 2`: the September 29 pin, which `K = 1` does not improve.

**What the reads show before the pin.** At `n = 16` the stations reading the request's last cell
(odd stations, 41–42 of 64 each) lead those reading the cell before it (even, 29–31), and each
station's count follows the first two, as a chain of locked neighbours propagates. The request's
last cells are read through a superposition of every placed datum. With `E` at its declared sign
sequence, every datum's image spreads over the ring's `2D` coordinates. A linear readout cancels
the other data only when `2D ≥ (n + m − 1)(|A| − 1)` (the rows' differences must be orthogonal to
every other datum's class differences), `188` against `120` at `D = 60` and `n = 40`. The
certified step barely moves `E` (`2⁻¹⁶`) and moves `R` (`2⁻²..2⁰`).

**Text** (`D = 35`, one pass over the 385 choosing pairs): 134,886 ms, a peak of 847,208,448
bytes. The training code over the compared stations was `47130 + 0/16 + ε` bits. Eight development
sections, on choosing requests already read, were all held: after about nine locks each, every
unlocked station's top cell was shared at the grain `L_R = 16`.

**Probes.** A training refinement with its deposit share took 220 ms on the terrain (`D = 60`) and
311 ms on text (`D = 35`).
