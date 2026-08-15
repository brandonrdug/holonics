# The library was already on the disk, and the absence was measured by counting artifacts

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `measured` throughout — every figure below was taken this day by running the
thing, and each carries the command that produced it. `proved-standard` for the mathlib theorem the
kernel admitted.
**Occasion:** Brandon asked directly: *"Why do we not compile mathlib and put the machine to real
mathematics?"*

The answer is that we were compiling it — from source, the slow way, in an archived tree — and it
had stopped about ninety percent in, while the complete prebuilt library sat in a local cache
directory that nothing in the tree had ever consulted. **Reaching the kernel took two minutes and no
compilation at all**; giving this project's own nine files their oleans took a further twenty on
twenty-four cores, and both are minutes, not the standing constraint three live documents described.

---

## 1. What three live statements said, and what each was actually measuring

The claim *"mathlib is not compiled"* is stated in three independent places, in the driver headers
and module comments that a later session reads first. None of them is careless prose; each was
written by a session that believed it was reporting a constraint.

| owner | what it says | what it measured |
|---|---|---|
| `soma/life/examples/the_second_theorem_is_reachable_only_after_the_return.rs:37-41` | *"Mathlib is **not compiled here** — two `.olean` files in the whole tree. That is a hard constraint on any deed that wants a kernel verdict on real mathematics, and it is stated rather than worked around."* | `.olean` files under `soma/`. The archive held **2,622 mathlib oleans** at the identical revision. |
| `soma/life/examples/eros_lean_proof_production.rs:45-47` | *"`elementary-holonics` and `rh-source-transport` both `require mathlib`, whose package cache is not materialized under `soma/formal`, so **no verdict is available** for a theorem posed in their environment."* | True when written. The packages are vendored now — `soma/formal/elementary-holonics/.lake/packages/mathlib` carries **7,516** source modules at rev `a3a10db0`, byte-identical in revision to the archive's. |
| `soma/life/src/agentic_research.rs:1342-1349` | pointing a **test** at a mathlib-requiring project makes `lake env lean` *"clone the Mathlib package cache on the network."* | Correct, and correct as a rule for tests. It is not a constraint on a driver, and it is void once the packages are local. |

**Each is a different measurement, and not one of them was an attempt.** The capability was declared
absent three times by counting or inspecting artifacts, and never once by trying it.

> **A capability's absence is measured by attempting it, not by counting its artifacts.** A file
> count answers *"is the output here"*; it does not answer *"can this be reached"*, and those
> questions have different costs. Here the count was repeated three times over five days and the
> attempt cost two minutes.

This is the same species as the convicted *search for the mechanism, never the phrase* — an absence
claim from a grep over names — one level out: an absence claim from a census of build outputs. And
the second-theorem driver's own phrasing is what made it durable: *"stated rather than worked
around"* reads as rigour, and a later reader does not re-check a constraint that presents itself as
having already been considered.

---

## 2. The measurement: the library was already on this disk

```text
  ~/.cache/mathlib          16,510 .ltar files, 834 MB
                            oldest artifact  Jun  6
                            newest artifact  Aug  1
```

`lake exe cache get`, run in `soma/formal/elementary-holonics`, reported:

```text
  Using cache (Azure) from origin: leanprover-community/mathlib4
  No files to download
  Decompressing 7869 file(s)
  Unpacked in 12881 ms
  Completed successfully!
```

**`No files to download`.** Nothing was fetched. The complete prebuilt olean set for the exact
revision the manifest already pinned had been on the machine since before the partial build began,
and the two minutes the command took were spent decompressing local files.

### What the archive's build actually was

The archived and live projects have **byte-identical sources and byte-identical lakefiles** (`diff
-rq` returns nothing; both `require mathlib rev = "v4.27.0"`), and both resolve to mathlib rev
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. The archive's 2,622 oleans are therefore not a different
build target — they are **an incomplete from-source build of the same 2,904-target closure**, stopped
partway. `Mathlib.olean` did not exist there, so `import Mathlib` was unavailable and every kernel
deed in this tree ran in `kernel-witness`, the project that imports nothing.

**We did not compile mathlib because we were compiling mathlib.** The library ships its own build
outputs, the project's manifest already pinned the revision they were built for, and no document in
the tree named the command.

---

## 3. The result, with its control

After `lake exe cache get`:

```text
  oleans under soma/formal/elementary-holonics/.lake   7,523   (was 0)
  Mathlib.olean                                        present  734,664 octets
  on-disk extent                                       6.9 GB
```

**The two halves cost differently and the record must not blur them.** The cached oleans are
immediately loadable by `lake env lean`, which is the call the body makes and the only one a kernel
deed needs. Producing this *project's* own nine oleans is a separate job: `lake build` recomputed the
whole 2,904-target closure from source — it does not accept the cache's traces here — and completed
`Build completed successfully (2904 jobs)` in about twenty minutes across two attempts on
twenty-four cores, the first cut off by a ten-minute command cap with its work retained.
`ElementaryHolonics/RH/Statement.olean` and `RH/Route.olean` now exist, which is what the
sibling-import checks needed.

**A theorem the kernel admits, through the exact call path the body uses** — `lake env lean`, the
same command `LeanKernelWorld::grade` spawns at `soma/life/src/lean_mathematics.rs:815`:

```lean
import Mathlib

open Polynomial in
theorem probe_kernel_sees_all_of_mathlib (K : Type*) [Field K] (p q : K[X]) :
    (p * q).natDegree = p.natDegree + q.natDegree ∨ p = 0 ∨ q = 0 := by
  rcases eq_or_ne p 0 with hp | hp
  · exact Or.inr (Or.inl hp)
  rcases eq_or_ne q 0 with hq | hq
  · exact Or.inr (Or.inr hq)
  exact Or.inl (natDegree_mul hp hq)
```

Elaborated in **10.2 seconds**, exit 0, no diagnostic. `import Mathlib` — the whole library, not a
corner of it — and the theorem is real: the degree of a product of nonzero polynomials over a field.

**The control fires, so the check carries evidence.** The same apparatus on a false claim:

```text
  theorem also_false : (1 : Nat) = 2 := rfl
    -> error: Not a definitional equality: the left-hand side 1
       is not definitionally equal to the right-hand side 2
  natDegree_mul (by sorry) (by sorry)
    -> warning: declaration uses 'sorry'
```

The `sorry` case matters for the body specifically: `lake env lean` exits **zero** on a `sorry`, and
`LeanKernelWorld::grade:826-831` already refuses it by testing the candidate text for `sorry` and
`admit` before returning `KernelAdmitted`. The refusal was built before there was a library to need
it against.

### The probe that matters most: this repository's mathematics, in mathlib's environment

Run from `soma/formal/elementary-holonics`, which is the `project_root` a deed would pass:

```lean
import Mathlib
import ElementaryHolonics.RH.Statement

open Soma.Holonics.RH in
theorem the_repository_statement_is_the_mathlib_statement :
    Statement ↔ RiemannHypothesis := Iff.rfl
```

**Admitted in 9.0 seconds, exit 0, no diagnostic.** The repository's own `RH/Statement.lean` and the
whole of mathlib are in scope *together*, and the kernel confirms that what this tree calls
`Statement` is definitionally mathlib's `RiemannHypothesis` — which is what `statement_def` in that
file has always asserted and what nothing had ever checked from outside its own project.

`tools/lean_check.sh` now returns **12 clean, 0 issue**, and `ElementaryHolonics.lean` — the root
aggregator that previously reported `ROOT` for want of its own built leaves — is **`CLEAN`**. The one
remaining `ROOT` is `rh-source-transport`'s aggregator, whose project is unbuilt; that is build order
and is reported rather than counted.

---

## 4. What is owed, and it is not an organ

**Nothing.** `LeanKernelWorld::new(project_root, scratch_root, worker_aperture)` at
`soma/life/src/lean_mathematics.rs:781-795` already takes the project root **as a parameter**, and
`grade` at `:815` already runs `lake env lean` with `current_dir(&self.project_root)`. The three
drivers all pass `root.join("soma/formal/kernel-witness")` — a caller's choice, made when it was the
only project a kernel could reach.

Pointing a deed at `soma/formal/elementary-holonics` is a changed argument. The finger-trap rule is
satisfied without exception: the composition was attempted end to end and returned no absent type.

**The cost changes and must be declared.** `kernel-witness` elaborates in well under a second; a file
importing all of mathlib costs **10.2 seconds**, and `grade_all` runs its worker aperture in parallel
threads. A plural path family of thirty candidates is therefore minutes rather than seconds, and the
aperture is a declared receiver coordinate that a deed against this corpus must state.

---

## 5. Two defects found on the way, both repaired

### `tools/lean_check.sh` no longer terminated

The script did `find . -name '*.lean'` inside each project. That was correct when it was written —
`soma/formal/*/` held only its own sources. The live tree now vendors mathlib's **7,516** source
modules under `.lake/packages/`, so the script was elaborating mathlib itself, one file at a time,
and was killed at ten minutes having reached `Mathlib/Algebra/Group/Nat/Defs.lean`. It also emitted
`ISSUE` lines for mathlib modules whose dependencies were outside the partial build, which read as
defects in this project's mathematics and are not.

Repaired by excluding `./.lake/*`. Re-run against the live full build: **12 clean, 0 issue**, with
the two root aggregators reported as `ROOT` rather than counted.

The script now prefers the **live** build and falls back to the archive with a printed warning that
`import Mathlib` will fail there, and it prints the one-line recovery command when neither exists.
The layout note it already carried — Lean 4.27 puts oleans under `.lake/build/lib/lean/`, not
`.lake/build/lib/` — stands and still costs an hour if missed.

### The build is bound to no commit

`.gitignore:27` is `**/.lake/build/`, so **6.9 GB of built library is untracked and binds to no
commit** — and so were the archive's 4.2 GB before it. That is `CLAUDE.md` §0 lesson 1 exactly: the
shape that lost the tiger figures and `semantics_invariant_under_exact_chart`.

**The mitigation is that this artifact is reproducible from a pin rather than from a run.**
`lake-manifest.json` fixes mathlib at `a3a10db0`, `lean-toolchain` fixes the compiler at `v4.27.0`,
and `lake exe cache get` reconstructs the bytes from the library's own published cache. Both are
tracked. **The recovery command belongs beside the artifact**, and it is now in `tools/lean_check.sh`
where a session that finds the build missing will read it. A verifier binding the olean set to the
manifest pair is worth having and is not built.

---

## 6. What this does not claim

It does not claim a result in mathematics. It claims that the exterior kernel can now be handed a
theorem posed against the whole of a real mathematical library, that it admits a true one and refuses
a false one, and that the only thing standing between the deeds in this tree and that corpus was an
argument.

It does not claim the centrifuge changes. The centrifuge reads mathlib as **material** — 8,625 files
as text — and never needed a compiled library; that half was never blocked. What was blocked is the
**return**: a kernel verdict on a construction the body emitted into an environment where real
mathematics is in scope.

And it does not retire the network rule for tests. `agentic_research.rs:1342-1349` remains correct as
written: a test must not shell into a project that may clone. A driver may, and a driver is where a
world-return belongs.
