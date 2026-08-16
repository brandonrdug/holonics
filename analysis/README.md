# EXTERIOR INSTRUMENTS — nothing here is part of the body

> **BANNER. This directory is not the machine.** `analysis/` holds readers written *outside* the
> engine, in Python and numpy, against material the engine also reads. Nothing here is an organ,
> nothing here is a driver, and **no figure produced here is a machine return.** `CLAUDE.md`'s
> workspace table names `crates/` and `soma/`; this directory is deliberately not in it.

## Why the banner exists

An audit on 2026-08-15 measured a standing failure in how this repository gets read:

> Owned instruments are run heavily for *"does the tree still pass"* and bypassed almost entirely
> for *"does this reach anything, is this present, does this law hold."*

179 instruments were wired on the spot across three days to answer the second kind of question,
nineteen of them re-implementing mathematics the body already owns exactly, **fifteen of those in
floating point, in a workspace whose library crates contain none.** A directory of committed numpy
that answers questions about engine material is the durable form of that habit: it looks like an
owned instrument because it has a path.

So the rule is stated once, here, and applies to everything under this directory:

- **A reading taken here may be cited as an analysis and never as a return.** The distinction is the
  one `CLAUDE.md` draws between a receipt and the implementation: a figure computed outside the body
  says nothing about what the body can do.
- **Where an interior owner exists, it governs.** A disagreement between a script here and a Rust
  owner is resolved in favour of the owner, and the script is the thing to fix.
- **Every deposit built on a reading from here carries this banner's substance**, or it is
  presenting an outside analysis as an engine capability.

## `deposited_map/` — 1,043 lines of numpy over a foreign pretrained map

Its record is
`research/records/2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md`,
whose own errata — written the day of deposit — states the position and then names four defects in
the instrument, the sharpest being that the population statistics are taken over units that are not
independent: `read_map.py:81` computes the KV group as `head // (nq // nkv)`, so four heads share one
`W_V` and there are **84** distinct value maps rather than 336. Every per-head figure in that record
counts correlated units as independent.

**The interior owners of the same reading are `crates/holonic-engine/src/embedding_fiber.rs` and the
driver `crates/holonic-engine/examples/the_readout_returns_a_fiber_not_a_winner.rs`.** They are exact
and they conduct. Porting the reading into them is a construction and is not scheduled here; until it
happens, this directory is retained as the provenance of a dated analysis and for nothing else.

The `.json` files beside the scripts are that analysis's own output, kept so the record's figures can
be re-read rather than re-run.
