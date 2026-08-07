# `standing/`

The deposited standing. **Tracked on purpose.**

`.gitignore` carries `/output/`, `/runs/`, `/data/`. That is the exact mechanism that permanently
lost the laboratory's tiger phase-atlas figures and the kernel-accepted theorem file
`semantics_invariant_under_exact_chart.lean` — only its name, its proof term and a SHA-256 survive,
at no commit in either repository. Every movement below Part one of `blueprint/THE_ROADMAP.md`
produces artifacts, and without a deposit they are produced into an ignored directory.

So: the machine writes its returns to `/output/`, and what carries standing is deposited here and
bound to two hashes.

| file | what it is |
|---|---|
| `PLAN.txt` | the founding plan — what founded what, out of what material |
| `MANIFEST.txt` | one row per deposit: `path content_sha256 closure_sha256 founding`, plus one `founding` row per founding recording its material |
| `output/**` | the deposited returns, at the same relative path they were returned to |

Deposit and verify with `soma/tools/standing-deposit`:

```sh
cargo run -p soma-standing-deposit --bin standing-deposit -- \
    deposit --root . --plan standing/PLAN.txt --standing standing

cargo run -p soma-standing-deposit --bin standing-deposit -- \
    verify --root . --standing standing
```

`verify` **refuses** on content drift or an absent deposit — the evidence is corrupt. It **reports**
closure drift — the machine has advanced past what it rested, which is ordinary; a standing that
could not fall behind the current would not be standing. See
`soma/tools/standing-deposit/README.md`.

## What is deposited now

43 returns, 6,829 octets, three foundings: the Lean the machine generated and an exterior kernel
graded, from `lean.proof-production`, `lean.kernel-witness`, and `agentic.research-kernel`.

## What is not deposited, and why the count reads zero

`derived_returns_not_deposited=0` here. The archived C++ manifest reads `126` for that field, and
that number does **not** name a backlog of standing owed a deposit: the C++ depositor counted there
the returns it deliberately **refused** as reproducible derived bulk — compiled objects and
diagnostic atlases, some forty megabytes the machine regenerates byte-identically
(`archive/cpp-engine/cmake/HolonicDeposit.cmake:12-19`). Those 126 lived in a C++ build tree that no
longer exists and cannot be regenerated, because the body that founded them was archived whole. The
field is a declared refusal, not an obligation.

## The closure's declared aperture

The foundings in `PLAN.txt` mount **source**, not built binaries. A `cargo` example binary is not
reproducible from tracked material alone — it carries the toolchain, the resolved lock, and the
profile — so recording its hash would report closure drift on every rebuild and say nothing about
whether the machine advanced. Stated rather than hidden: **a toolchain change is not visible in
these closures.** A founding whose binary is itself deposited should add an `executable` line, and
then it is.
