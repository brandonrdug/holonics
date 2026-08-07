# NUMBER WORLD 01 · THE COMPLETE 0..64 CONSTRUCTION LIGHT

**Grade:** RATIFIED · FIXTURE BUILT/VERIFIED · TWO CUDA EXECUTIONS EXACT · LIVED ATLAS BUILT/INSPECTED

This isolated boundary fixture implements the light ratified in
`RESEARCH/2026-07-12_THE_NUMBER_WORLD_AND_THE_LIVED_ATLAS.md`. It changes no body, kernel, surface,
or `life` mechanism. [`world.jsonl`](world.jsonl) is the one persistent source artifact. Its `.jsonl`
suffix declares that every LF-terminated record is one complete worldline; the equations and Rust
constructions are delivered directly, without an outer JSON wrapper entering the light.

The exact cohort is:

| domain | currents |
|---|---:|
| numeric construction family | 5,004 |
| corresponding `m[A]` construction family | 5,004 |
| cross-entity `m[A]`/`m[B]` witness | 1 |
| compact valid Rust | 2 |
| **total** | **10,011** |

Numeric lines 1–5,004 and unit lines 5,005–10,008 correspond one-for-one. Within each domain the
family census is successor 64 · predecessor 64 · ordered addition 2,145 · inverse subtraction
2,145 · ordered multiplication 280 · exact division 280 · powers 13 · inverse roots 13. Line
10,009 is `(2*m[A])*(2*m[B])=4*m[A]*m[B]`; the final two records are the ratified integer Rust
functions. No prime, composite, semiprime, shortest-route, or zeta label occurs in the delivered
material.

[`MANIFEST.tsv`](MANIFEST.tsv) is observer-only provenance. It maps every lineage to its exact
source range, operation family, parameters, evaluated face, unit relation, corresponding
numeric/unit line, and per-record SHA-256. It is never passed to `life`. [`SHA256SUMS`](SHA256SUMS)
pins the source and manifest.

## Generate and verify

Run from `src/soma`:

```bash
python3 observations/number-world-01/number_world.py generate
bash observations/number-world-01/verify.sh
```

Generation is deterministic. Verification independently rebuilds all equations, checks the exact
family and domain censuses, record uniqueness and LF framing, source/manifest digests, the absence
of class labels in the delivered source, the one-to-one unit correspondence, the cross-entity
witness, the immutable parent, and compilation of the two Rust currents. It also retains the larger
signed even-root relation `(+2)^2=4`, `(-2)^2=4`, `Root_2(4,+2)`, and `Root_2(4,-2)` as an
observer-only guard while proving those four constructions remain outside this first declared
nonnegative world.

The immutable parent is:

```text
observations/nurture-01/results/turn-02-bodies/1783906520241629126-cuda-continue-next.body
SHA-256 dabadf5c202680e187d77bfca71de3654cb420a186ef1c0bc710edae951b6f1d
```

## Measured CUDA executions

These commands were executed against the same immutable parent. Each destination was absent before
its execution.

```bash
parent=observations/nurture-01/results/turn-02-bodies/1783906520241629126-cuda-continue-next.body

SOMA_OBSERVATION_OUT=observations/number-world-01/results/run-a.txt \
SOMA_PERIPLUS_DIR=observations/number-world-01/results/run-a-bodies \
  cargo run --release -p life -- --cuda-continue "$parent" --later \
  observations/number-world-01/world.jsonl

SOMA_OBSERVATION_OUT=observations/number-world-01/results/run-b.txt \
SOMA_PERIPLUS_DIR=observations/number-world-01/results/run-b-bodies \
  cargo run --release -p life -- --cuda-continue "$parent" --later \
  observations/number-world-01/world.jsonl
```

All 10,011 records are co-present and integrate once at their common receiving edge. The manifest
and digest files are boundary instruments and must not be included after `--later`.

The two 528,819,644-octet successor archives are byte-identical. Their complete reports differ only
at the required create-new successor path; normalizing that one line makes both reports byte-exact.
The measured lifecycle is:

```text
10,011 currents · 161,556 delivered octets · carrier depth 44
29,670 lineage-local REGISTER carries · receiving axis 1,024
46,138 pre-edge touch visits at axis 256 · 4,404 distinct grips
430,788 ordered Mail landings · 278,225 distinct receiving coordinates
286,117 occupied/resultant standing coordinates · 63,042 fiber · 2,538 two-armed
terms: ride 474,579 · found-this 43,408 · found-that 53,710 · dark 2,186
body:light 528,819,596 : 163,468 · archive 528,819,644
```

The exact artifact ledger, family census, construction readings, reproduction command, and hashes
are in [`results/RESULTS.md`](results/RESULTS.md) and
[`results/SHA256SUMS`](results/SHA256SUMS).

`results/run-a-events.json` is the retained superseded schema-v1 extraction and has no Mail face.
`results/run-a-atlas.json` is the sole complete measured schema-v2 atlas artifact.

## Open the lived atlas

The dependency-free atlas draws the machine's exact raw axis-256 paths and receiving-edge axis-1024
Mail as separate chart faces. It performs no force layout, coordinate displacement, scoring, or
feedback into soma. From this directory:

```bash
python -m http.server 8123 --bind 127.0.0.1
```

Open:

```text
http://127.0.0.1:8123/tools/atlas/?artifact=../../results/run-a-atlas.json
```

See [`tools/atlas/README.md`](tools/atlas/README.md) for the controls, exact overlay derivation, and
deterministic gates. [`results/atlas-overview.png`](results/atlas-overview.png) is the inspected
whole-world view.
