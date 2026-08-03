# Parameterized elementary mechanics 01

**2026-07-21 · bounded production-source measurement · NVIDIA GeForce RTX 4080 SUPER**

## Question

Can one live production mouth carry both an oriented triangular junction and a topologically flat
local rewrite when dependency rank, cell dimension, and constituent grain are independent; admit
seams only through explicit interfaces; preserve the complete later-contact boundary during
compression; and remain exact across one-core host, eight-core host, CUDA, and durable rest?

## Command

```text
cargo test -p life --lib live_current_cuda::tests::graded_triangle_junction_is_exact_across_one_core_many_cores_cuda_and_rest -- --ignored --exact --nocapture
```

The complete non-device library surface was also checked with:

```text
cargo check --workspace --all-targets
cargo test --workspace --lib
```

## Exact physical output

```text
device="NVIDIA GeForce RTX 4080 SUPER"
triangle_cells=21
triangle_incidences=27
rewrite_cells=12
rewrite_incidences=6
source_grain=3
boundary_squared=0
regional_cells=4
standing_constituents=2
triangle_exposed_pins=2
rewrite_exposed_pins=2
contact_launches=6
parallel_contact_lanes=57
lineage_launches=9
retries=3
stack_growths=2
stack_bytes=35840
rest_words=8876
```

The ignored device test passed. The workspace library surface passed 673 tests with 11 ignored and
zero failures.

## What the cell establishes

- The triangular world satisfies its oriented boundary check and emits one constituent.
- The rewrite world keeps every source cell at dimension zero while dependency rank and grain
  change independently; `RewriteInterface` crosses as an actual incidence.
- One worker, eight workers, and CUDA return equal radiation, live lineages, and Standing for both
  worlds.
- Each outgoing constituent reproduces the same exact boundary-conduct family after compression.
- The combined two-constituent successor encodes, decodes, and remounts exactly without replay.

## What it does not establish

CUDA forms the contact field; canonical shared-topology composition remains host-side. The result
does not establish a universal rewrite matcher, general confluence, device-resident cellular
Standing, metric/diffusive dynamics, arbitrary future-observation congruence, or scale.
