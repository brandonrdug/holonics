# `soma-standing-deposit`

Binds every deposited return to **two** hashes, and separates the two ways that binding can fail.

```text
   plan  ──▶  deposit  ──▶  standing/MANIFEST.txt  ──▶  verify  ──▶  REFUSE | HELD
                              content_sha256
                              closure_sha256
```

- **content hash** — the deposited octets.
- **closure hash** — the founding that produced them: the executable together with every input it
  mounted, folded content-only, in declared order.

And the distinction the whole tool exists for:

| species | meaning | response | exit |
|---|---|---|---|
| **CONTENT drift** | a deposit no longer holds what was deposited | the evidence is corrupt — **REFUSE** | `1` |
| **ABSENT** | a deposit is gone | that is the loss itself — **REFUSE** | `1` |
| **CLOSURE drift** | the founding's material moved | the machine advanced past what it rested — **REPORT** | `0` |

*A standing that could not fall behind the current would not be standing.*

## Why

The laboratory lost its tiger phase-atlas figures and a kernel-accepted theorem file named
`semantics_invariant_under_exact_chart.lean` to an untracked `runs/`. Only the name, the proof term
and a SHA-256 survive; neither artifact is recoverable at any commit in either repository. The
archived C++ body is the one place that led — `archive/cpp-engine/cmake/HolonicDeposit.cmake` and
`archive/cpp-engine/cmake/HolonicRegistry.cmake` built exactly this, and the verifier caught a
path-fold contamination with it. `grep -rln closure_sha256` hit only the archive. This is that
mechanism in Rust.

## Use

```sh
cargo run -p soma-standing-deposit --bin standing-deposit -- \
    deposit --root . --plan standing/PLAN.txt --standing standing

cargo run -p soma-standing-deposit --bin standing-deposit -- \
    verify --root . --standing standing --report output/standing-verify.txt
```

Exit status **is** the verdict. Nonzero on content drift or an absent deposit; zero on closure
drift. Anything that collapses those two has not ported the distinction.

## The plan

```text
# comments and blank lines are ignored
founding    <name>     opens a founding; names are unique within a plan
executable  <path>     at most one per founding, optional
mount       <path>     zero or more; ORDER IS LOAD-BEARING — the closure folds in order
return      <path>     zero or more; deposited into the standing
derived     <path>     zero or more; declared and deliberately NOT deposited
```

`derived` is a declared refusal, not an inferred one. The archived depositor classified returns by
filename pattern (`HolonicDeposit.cmake:35-37` — suffixes `.rest`/`.lean`, patterns `/receipts/`,
`POST_SEAL`, `DOSSIER`, refusals `STDOUT`/`STDERR`/`OPEN_PATHS`), so anything renamed silently
changed class. Here `derived_returns_not_deposited` counts a decision instead of a coincidence of
spelling.

## Three things this port does that the original could not

**1. The closure is recomputed, not proxied.** The archived manifest recorded a closure *hash* but
never the material behind it, so `HolonicRegistry.cmake:64-72` could not recompute one. It
substituted a proxy — compare the current build tree's output against the recorded *content* hash —
which misreads in both directions: a founding whose material moved but whose output is unchanged
reads as held, and a founding whose output is merely nondeterministic reads as drifted with its
material untouched. The `founding` row here records the material, so the closure is folded again
from what it actually is.

**2. No absolute frame enters a lineage.** `RelPath` refuses an absolute path, a `..` component, a
`.` component, a backslash, or whitespace, structurally at construction; and the closure folds
*content* digests only, never a path. Two checkouts at different absolute locations therefore
produce byte-identical manifests, which `the_closure_does_not_fold_an_absolute_frame` asserts by
depositing the same tree twice from two roots. This is `CLAUDE.md` §0 made executable: *"No absolute
frame in a lineage. Ten C++ card adapters folded the filesystem path into the rest integrity."*

**3. It reads the archived manifest.** The deposit row is byte-compatible with
`archive/cpp-engine/standing/MANIFEST.txt`, so `verify --standing archive/cpp-engine/standing`
rehashes all 123 CMake-written content hashes. They hold, and all 123 closures report
`closure_unrecomputable` — which is precisely the gap point 1 closes.

## Zero dependencies

A registry that verified deposits through a crate it did not itself verify would have moved the
trust, not established it. The SHA-256 in `src/sha256.rs` is written out and checked three ways:
the NIST vectors including the million-`a` case; a split-invariance test that re-hashes a
thousand-octet message at every one of its 1,000 splits; and the archived body's 123 CMake-computed
content hashes on real deposited octets. That last is the independent-implementation cross-check
`CLAUDE.md` §8 asks for, on evidence rather than a fixture.

Files are streamed through a 64 KiB stack buffer — hashing and copying in one pass over the octets,
never holding a file. That matters because a founding's executable is the largest thing in its
closure.

## Cost

*A cost law is a law* (`CLAUDE.md` §8). Verification is one pass over the deposited octets plus one
pass over the closure material, with one fold per founding rather than one per deposit. Measured on
this machine, debug build, mean of five:

| standing | deposits | octets | wall |
|---|---|---|---|
| `standing/` | 43 | 6,829 + 121,882 material | 10 ms |
| `archive/cpp-engine/standing/` | 123 | 802,855 | 31 ms |

The archived C++ verifier caught the path-fold contamination in 0.03 s over the same 123 deposits.

## The falsifier

From `blueprint/THE_ROADMAP.md`, "Deposit and closure drift cross to Rust":

> *Corrupt one deposited octet and confirm **refusal**. Advance the machine one step past its rest
> and confirm a **report**, not a refusal. If both produce the same response, the distinction that
> caught the path-fold contamination has not been ported.*

Both halves run in `src/tests.rs` — `one_corrupted_deposited_octet_refuses` and
`advancing_the_machine_one_step_reports_and_does_not_refuse` — plus
`the_two_species_are_separable_in_one_run`, which corrupts one founding's deposit and advances
another founding's material in the same standing and asserts that the verdict refuses on exactly the
first while reporting exactly the second. A verifier that has only ever seen clean input returns
zero and proves nothing about itself.
