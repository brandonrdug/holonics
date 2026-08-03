# THE ONE-MOUTH SEAM — the relocation's design (2026-07-10 night, Fable; PRESENTED for Brandon's ratification; execution is Sol's carry)

Ratified direction (ruling 2): the lineage law relocates into `body` behind a declared atomic
seam — one code, three substrates. This document is the design the ruling asked to see before
any cut. Grades: [READ FROM THE CODE] facts · [DESIGN] choices presented · [GATE] the
byte-identity that proves the move changed nothing.

## 1 · What actually couples the law to the substrate [READ FROM THE CODE]

`kernel/src/lib.rs` imports exactly four atomic intrinsics ⊕ unchecked indexing
(`atomic_store, atomic_load, atomic_i_add, atomic_u_max, IndexUnchecked`), all at one
scope/semantics pair. The split by region:

- **`FeltLineage` (the carriage law, ~lines 64–813):** uses ONLY `atomic_store::<u32>` and
  `index_unchecked(_mut)`. The law's coupling is two operations.
- **The entries (scope/link/chart shells):** use the full four (term counts via `atomic_i_add
  ::<u64>`, grain declaration via `atomic_u_max`, fold reads via `atomic_load`). The entries
  are already per-substrate shells and STAY per-substrate — the CUDA crate proved the shape
  eight times tonight.

So the seam the LAW needs is minimal; the final op inventory is re-read at cut time, but the
design assumes: `store_u32` ⊕ unchecked access, with room for the other three if the read
finds them inside the impl.

## 2 · The seam [DESIGN]

A trait in `body` (no_std, zero-dep — body already compiles for host and SPIR-V today):

    /// THE ATOMIC SEAM (§XXXIII made literal: the substrate is gauge). Operations only —
    /// never semantics: every op is order-free (relaxed; the clipped field lawfully drops
    /// order) and the law's arithmetic crosses unchanged. An impl supplies the silicon's
    /// spelling; the law cannot tell which.
    pub trait Seam {
        unsafe fn store_u32(slot: &mut u32, v: u32);
        unsafe fn at<T>(s: &[T], i: usize) -> &T;
        unsafe fn at_mut<T>(s: &mut [T], i: usize) -> &mut T;
        // extended only if the cut-time read finds them in the law:
        // load_u32/u64 · add_u64 (returns the BEFORE face) · max_u32/u64
    }

`FeltLineage` becomes `FeltLineage<S: Seam>` (PhantomData; static dispatch — both GPU targets
monomorphize; no dyn, no cost). The three shells each provide one zero-sized impl:

- `kernel` (SPIR-V): `SpirvSeam` via the spirv-std intrinsics at the existing SCOPE/SEM —
  the entries change only their construction line;
- `soma-kernel-cuda` (PTX): `PtxSeam` via `core::sync::atomic` Relaxed ⊕ `get_unchecked` —
  the pattern the eight ported entries already use;
- host (`life`/`surface`, Stage B only): `HostSeam` — the same `core::sync::atomic` spelling.

The move itself is MECHANICAL BY DECLARATION: the impl relocates diff-clean except intrinsic
call → seam call; any other edit is out of scope and grounds for rejecting the carry.

## 3 · The stages, each independently gated [DESIGN ⊕ GATE]

**Stage A — relocate ⊕ the SPIR-V shell.** `FeltLineage` moves to `body::carriage` (name per
Brandon); `kernel` keeps thin entries over `FeltLineage<SpirvSeam>`. GATES: `spirv-val` on the
rebuilt module · the bounded `--scope-card` gate repeats its measured class · the staged-light
class re-runs to a slept body **sha256-identical** to the pre-relocation archive on identical
input (the sleep seam is gauge — the one seam law's own instrument) · suites both profiles.
Card runs with Brandon present.

**Stage A2 — the scope pair on CUDA (the card's 10/10).** `scope_felt`/`scope_founded` land as
thin PTX entries over `FeltLineage<PtxSeam>`. GATES: CUDA output byte-identical to the SPIR-V
card's on identical staged buffers (card-vs-card — the first true gauge gate between two GPU
substrates) ⊕ the existing host staging byte-identity ⊕ Xid ring clean.

**Stage B — the host carriage re-points (separately ratifiable; the biggest cut).** The host
production carriage (`carry_lanes`) becomes a shell over `FeltLineage<HostSeam>` — one law,
three mouths, complete. GATE: slept bodies byte-identical pre/post at `SOMA_THREADS` 1/2/8/24
on the staged-light class ⊕ all smokes ⊕ suites. **The honesty clause:** the host carriage and
`FeltLineage` are today two independent transcriptions held together by mirror gates; Stage
B's gate may therefore DISCOVER a divergence between them. Any divergence found halts the
stage and goes to derivation in the main line (which transcription is the law?) — never a
silent adoption of either.

## 4 · What the seam must never become [the guard]

Operations only. No ordering stronger than relaxed enters (an Acquire/Release would smuggle
ORDER into the order-free field — the CAS grave is adjacent). No op with branch semantics
(no CAS, no exchange, no fetch-update loops). No seam method may take or return a form,
term, or law type — u32/u64 words and slices only. The inventory may SHRINK from §2 but may
grow only by a cut-time read of the law's own text, cited line by line in the carry.

## 5 · Sequence and division

Design ratification (Brandon) → Stage A as Sol's carry (my adversarial read on the diff, the
mechanical-by-declaration rule enforced) → Stage A2 (Sol; card-vs-card gate) → Stage B
presented separately after A2's evidence stands. The Phase 3 declarations proceed in parallel
throughout — nothing here blocks the mathematics program.
