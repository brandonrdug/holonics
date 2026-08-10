# The committed boundary artifact is stale and cannot be rebuilt

**Date:** 2026-08-09
**Truth status:** `established-bounded` — every item measured by building or by running.
**Evidence:** `measured`, and each figure carries the command that produced it.
**Provenance:** found incidentally while checking whether a `soma/body/src/law.rs` excision altered
what the SPIR-V kernel compiles. None of it was the object of any brief; it is deposited so it does
not dissolve with the session that found it.

**Band:** 2026-08-09 · APPARATUS DEFECTS FOUND WHILE CHECKING SOMETHING ELSE

---

## 1. `soma/kernel/soma.spv` cannot be regenerated at HEAD

`soma/kernel/builder` fails:

```text
error: saturating_add is not implemented yet    ×2
   from soma/body/src/carriage.rs:1858   (self.continuation_depth.saturating_add(1))
   reached by scope_felt
```

`rustc_codegen_spirv` does not implement `saturating_add`. The comparison builds that established
the excision was safe both carried one identical patch replacing it with an explicit branch — which
is the correct control for *that* question, and it means **the committed artifact's toolchain path is
broken at HEAD.**

## 2. The committed artifact is stale

```text
committed  soma/kernel/soma.spv   sha256 9a805973…   2,538,328 bytes   mtime 2026-08-07 13:09
rebuilt (under the patch)         sha256 91d9b5c1…   2,556,944 bytes
```

**The boundary object in the tree is not what HEAD produces.** `CLAUDE.md` §0 lesson 1 is exactly
this: *"Bind every deposit to its content hash AND its closure hash, with a verifier."* The workspace
`Cargo.toml` states the design intent — *"their compiled artifacts … are committed boundary objects
that soma-surface and mount include directly, so the host workspace carries the artifact without
carrying the toolchain"* — and **there is no verifier**, so the artifact and its source drifted
silently for two days.

**What is owed:** a check that the committed `.spv` matches what the pinned toolchain produces, or an
explicit declaration that it is a frozen artifact with its provenance commit named. Either is
acceptable; the present state — a committed binary that nothing reproduces and nothing checks — is
not.

## 3. `soma-surface` is the Vulkan half of a boundary whose host is unwired

`soma/surface` is the **only** crate in the workspace depending on `wgpu` (v27, `spirv` feature) and
the **only** consumer of `soma/kernel/soma.spv` — two `include_bytes!` sites, `lib.rs:1780` and
`:3660`, both feeding `create_shader_module_passthrough`. `soma/kernel/builder/src/main.rs:13`
produces the artifact; nothing else reads it.

It **is** a workspace member, so `cargo test --workspace` compiles all 4,977 lines and runs its 17
tests. **But every one of those tests is in `sleep_tests.rs`, which contains zero occurrences of
`wgpu`, `Felt`, or `spv`** — they exercise `SleepingBody` and the v2→v9 archive mouth over
`body::medium::RegionalForm`. Host-side serialization versioning, not the card.

```text
   FeltSurface, FeltLineageMount, the compute pipelines, the shader mounts
      zero library consumers · zero drivers · zero tests
```

`soma_surface` occurs in **no `.rs` file in the workspace**; the dependency at
`soma/life/Cargo.toml:19` is declarative only.

**So there are two GPU paths and one is reached:**

| path | boundary artifact | state |
|---|---|---|
| CUDA | `soma/mount/soma-kernel-cuda` PTX + the engine's two nvcc kernels | driven — 7 mount gates return EXACT on the 4080 SUPER |
| Vulkan/SPIR-V | `soma/kernel/soma.spv` → `soma/surface` | artifact committed, **stale, unbuildable, host unwired** |

**What this is not.** It is not an argument for wiring it. `research/records/2026-07-26_THE_CONIC_OWNS_THE_FRAME_THE_CARD_WAITS_FOR_THE_HOST.md:257-261` is the precedent: a
proposed parallelization was **declined after measurement** because the bottleneck had already
departed, and `2026-07-26_THE_CARD_RESTRICTS…:181-183` refuses the general move — *"Moving those
small or branch-heavy operations to the card merely to say 'all-GPU' would not improve this bounded
world."* And under `2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER…`'s admission square, a second mode
`μ = (L, ABI, P, D, A, χ)` reopens admission entirely. **The cost is a full re-admission, not a free
second frame**, and the decision is Brandon's.

## 4. Ten binaries run from `target/` with no committed source

`canon/THE_MEASURED_CAPABILITIES.md:182` names **two**. There are **ten**: `zz_smith_cost_probe`,
`zz_torsion_width_law`, `zz_diag`, `zz_leak`, `zz_o2`, `zz_orbit`, `scratch_bring_search`,
`skein_far_probe_tmp`, `window_population_probe`, `witness_depth_probe`. Each returns
`git log --all -- "*<name>*"` → **0 commits**, and none has a live source.

**One `cargo clean` ends all ten.** This is `CLAUDE.md` §0 lesson 1's loss pattern reproduced — the
same shape as the tiger figures and `semantics_invariant_under_exact_chart`, which survive only as
names.

## 5. Two organs die by exhaustion instead of refusing

Measured under contention, so the exact kill point is frame-dependent; the **ladder** is internally
consistent and is what the finding rests on.

```text
eros_resonant_corpus_current    SIGKILL at 10,963 MB / 38.2 s on its default 1,556 lines
   ladder  200 → 257 MB · 400 → 933 · 800 → 3,494 · 1,200 → 8,225        ≈ n^1.8

eros_morphological_language_generation   did not return in ~35 min
   at the aperture its own source calls BOUNDED
```

Against `the_iron_tokens_carry_the_field`, which at **12,339,449 tokens** returns a typed obstruction
naming the exact required width — *"requires width 4183426185, past the declared capacity 8192"* —
and then answers a narrower question whole, in 259 s at 2,023 MB.

> **The organ with a declared aperture law scales to 12M tokens on 2 GB. The two without one cannot
> finish 1,556 lines.**

That is this project's own thesis, measured on its own organs, and it is the strongest argument in the
tree for the aperture discipline.

## 6. Five concurrent agents OOMed the box, and the reading was wrong first

Five sub-agents were dispatched on **disjoint file scopes** — which was checked — each independently
authorized to run `cargo test --workspace`, one of them additionally instructed to push organs until
they refuse. **The file scopes were disjoint and the build graph is shared**, so five full build
graphs plus a deliberate memory-pressure sweep ran at once and the box OOMed.

Brandon's correction: *"it's not a capacity problem, they're just running all of it at once."*

**This is the convicted defect in its own apparatus.** `2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER…:468`:
*"No concurrency claim may be inferred from worker count, collection membership, or GPU lanes."* And
`2026-08-03_THE_GEOMETRY_COMPUTES…:93-96`: *"The physical trace is the shadow of the authored control
flow."* A five-way fan-out was authored and the resulting crash was read as capacity.

**The fix, recorded because it is reusable:** every `cargo` invocation wrapped in
`flock <scratchpad>/cargo.lock` with `-j 2`, no `--workspace` from any agent, and the single workspace
gate run once by the dispatching session at the end. Serialization without stalling — the agents queue
rather than collide.

**The standing rule:** *disjoint writes do not imply disjoint resource use, and `target/` is one
directory.*

## 7. What this record does not claim

- **No organ is convicted here.** §§1–2 are toolchain and provenance; §3 is a wiring state, not a
  defect in `soma/surface`'s code; §4 is hygiene; §5 is two named organs and no others; §6 is the
  dispatching session's own error.
- **No performance conclusion.** Every timing and RSS figure has one contended frame and none is
  falsifiable (`CLAUDE.md` §8: a clock may measure, it may never select).
- **§3 does not recommend wiring or removing `soma/surface`.** It states what is true and names the
  admission cost either direction.
