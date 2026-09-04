# The spine

> **SUPERSEDED 2026-08-07 — ARCHIVED-BODY PROVENANCE.**
> This file describes the C++/CUDA engine, which was archived whole at `archive/cpp-engine/` when
> the body moved to Rust. Its mechanisms, measurements and open items are **historical record**, not
> the present position and not a schedule. The active spine is `CLAUDE.md` §0; the active roadmap is
> `blueprint/THE_ROADMAP.md`. Nothing here is deleted — a reader following a citation into this file
> should find what it said, and this banner telling them it no longer governs.


**Truth status:** `project-postulate` for the discipline; `computational-witness` for every reach
figure, which the build measures on each run and writes to `receipts/REACH_AUDIT.txt`.

This file exists because the repository could not say, on 2026-08-06, how much of itself its own
one move conducted through. Thirty-five construction steps had been admitted, every receipt was
true, and the answer was **nine headers out of six hundred and forty-nine.**

## 1. Reach is part of the grade

A receipt says *this deed returned*. It does not say *the body conducts through this*. Those are
different claims and only the first was ever graded, so a mechanism at one percent reach earned
exactly what a mechanism at a hundred percent earned, and nothing in the record disagreed with
itself while the two drifted apart.

**A mechanism is admitted at the reach it demonstrably conducts through, and its receipt states
that number.** `cmake/HolonicReach.cmake` computes it over the actual include graph, records a
floor per mechanism, and fails on regression. It is registered as `r0.reach_audit` under the
`audit` label and costs fifty milliseconds.

Reach is a measurement, never a target. Widening an include to raise a number is the same defect
as a receipt that overstates its code, and is caught the same way — by reading the owner.

## 2. What the spine is

These are the mechanisms the doctrine says the body conducts through. Measured 2026-08-06:

| header | reach | what it carries |
|---|---:|---|
| `structure/local_transport.hpp` | 14/649 | `T` — not assumed invertible, linear, metric, probabilistic, or scalar |
| `structure/chi_pair.hpp` | 13/649 | Chi as the **ordered pair** of parallel transports; projections refuse until the chart is declared |
| `structure/transition_invariants.hpp` | 10/649 | the eight-invariant atomic successor contract |
| `body/swing.hpp` | 9/649 | MEETING · FLYWHEEL · TEST · DEED; the only founding path |
| `body/live_machine.hpp` | 8/649 | one live standing, aperture absent from rest |
| `current/information_receipt.hpp` | **1/649** | the causal-information receipt the roadmap makes mandatory |
| `body/continuing_body.hpp` | 169/649 | the mathematical body's carrier |
| `exact/small_rational.hpp` | 256/649 | the exact rational arithmetic every mathematical deed runs on |

Two of these numbers are the whole diagnosis.

**`current/information_receipt.hpp` reaches one header — itself.**
`archive/blueprints/EROS_EMBODIMENT_ROADMAP.md:327-329` states that an ecology returning a count instead of
a receipt **is not admitted**. The receipt attached to production mathematical deeds is a different
type of the same name, `organ/generative_math_receipt.hpp`, carrying two `uint16_t` alternative
counts and a tally delta. By the project's own admission rule the mathematical body is unadmitted,
and no receipt said so because no receipt was asked about reach.

**`body/swing.hpp` reaches nine; `body/continuing_body.hpp` reaches one hundred and sixty-nine.**
They share no head, no continuation, and no rest record. **The C++ body is two machines.** The
library — bit-pure algebra, receiver geometry, GPU-resident executors — conducts through a carrier
that predates the one move. The spine and the nine ported ecologies conduct through the one move
and touch none of the library.

## 3. The asymmetry is a law and is not yet a cost

`archive/blueprints/EROS_EMBODIMENT_ROADMAP.md:183-185` — *"RIDE carries by the sandwich `R T R̃` and is
cheap because the terrain already paid; FOUND deposits one integer winding quantum and pays
curvature."*

In `body/swing.hpp` the law holds: `rebase_exposed` has no path to `found`, a founding with zero
winding refuses, and an OPEN cannot be converted by re-reading. **The cost does not.**
`pays_curvature` is a predicate over an enum; `rebase_exposed` and `cross` perform identical work,
and RIDE never reads the standing surface at all.

That is why re-running an already-founded computation is possible in this body: *nothing is cheaper
for having been founded.* The laboratory had four mechanisms that made it cheaper —

- a revision key plus **exact logical compare**, re-uploading device standing only on real
  difference (`live_current_cuda/executor.rs:686-706`);
- a shape short-circuit returning **zero work** when the population is unchanged
  (`text_material/resident.rs:470-472`);
- an **append delta** graded by `base_address_unchanged`, so founded device tensors keep their
  addresses (`text_material_cuda.rs:410-414`);
- **reuse counted in the receipt** — `standing_full_mounts`, `carrier_full_mounts`
  (`live_current_cuda/receipt.rs:36-77`).

Its measured ratio: 8,237 ms to condition an 88.7 MB route rest, 164 ms to generate from it. **That
fifty-fold gap is what RIDE means.** None of the four is ported.

The second reason: **the rest is not the standing.** Every rest here is a fixed-size trivially
copyable record written with one `write(2)` — 200 octets at the fourteenth step, 38,960 at the
thirty-fifth. The derived population is not in it. The laboratory's was
`LiveCurrentRestImage{ standing: SparseStandingSurface, lineages }`, variable-length, megabyte
scale, carrying the whole derived population. A rest that omits what was derived cannot make
remounting cheaper than re-deriving; it can only make it equal.

## 4. Cost against an independent implementation

`tests/conformance/r34_host_law.hpp` implements the trace-fiber deed's algorithm line for line,
with hardware division. It runs in **0.189 s**. The device deed computing the identical result ran
in **274.268 s** — 1,450× — and no test compared them, because the conformance test compares
outputs byte-for-byte and never compares cost.

**Where a host oracle exists, the receipt states both costs.** This is
`research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE...md:104-107` — *a cost law is a law* —
turned on the body's own conduct rather than on a ported algorithm.

Two causes were found and one is closed:

- **Closed 2026-08-06.** Every division on the device path was a sixty-four-iteration software
  loop, and `gcd` was Euclidean over it — five gcds and ten divisions per elimination step. `gcd`
  became Stein's binary construction (shifts, comparison, subtraction; **no division at all**) and
  the division now enters at the operand's leading bit rather than at sixty-four. Verified across
  691,324 cases against the superseded implementation with zero mismatches. **274.268 s → 150.00 s,
  and the binary audit fell from 84 s to 61 s**, because `exact/small_rational.hpp` reaches 39% of
  the tree.
- **Open.** 215 of 262 kernel launches are `<<<1,1>>>`. In the trace-fiber deed `close_kernel`
  guards with `if (blockIdx.x || threadIdx.x) return;` and then serially performs 5,184 group
  insertions, 14 exact eliminations over 85 columns, and 10,368 residual evaluations. The receipt
  reports `launched_threads = 5,385` on a card with roughly 10,240 cores. The elimination is data
  parallel over columns and the census over rows.

## 5. The standing stopped misnaming itself

`CLAUDE.md` §13 has said since 2026-08-05 that **morphology may never again name a counter**. The
excision renamed the receipts. It did not rename the standing: `body/rest_record.hpp` carried

```cpp
struct rest_region final { std::uint64_t morphology{}; std::uint64_t current{}; };
```

and one hundred and sixty-nine headers committed through it. Renamed 2026-08-06 to
`admitted_tally`, with the law recorded at the declaration, together with the same counter under
three other names — `condensed_snapshot`, `condensation_program`, and the weave cell.

`morphology_cell{scale, offset, passages}` in `current/current_program.hpp` keeps its name. It is a
per-site transport organization — a real morphology — and the distinction is exactly the one the
law draws.

## 6. What conducting through the spine requires

Not a phase. Four joins, in dependency order:

1. **One body.** `continuing_body`'s standing becomes the standing surface, so the 169 headers stop
   committing tallies and start committing structure.
2. **The rest carries the standing.** Variable-length, derived population included.
3. **RIDE actually rides.** Revision key with exact logical compare, shape short-circuit, append
   delta with stable base address, reuse counted in the receipt. All four exist in Rust and can be
   read directly rather than invented.
4. **The kernels use the card.** Independently worth doing: it is a standing tax on every
   mathematical deed in the body.

New construction conducts through the spine, and its receipt says at what reach. A mechanism that
cannot state its reach has not been graded.
