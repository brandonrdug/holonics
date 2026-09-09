# Continuing four-torus current

[definition] An exterior exact mathematical experiment over the existing four-torus/Parametron
current chart. The source is
[`four_torus_current.rs`](../../../crates/holonic-engine/examples/four_torus_current.rs), using
the public `ExactRatMatrix` owner for geometry certificates and the full reference inverse.
The [construction record](../../records/2026-09-08_CLOCKED_TORUS_CURRENTS_CONTINUE_THROUGH_A_RETAINED_FIBRE.md)
owns the derivation, formal sources and scope.

[definition] `side = grain + 1 >= 2`. There are `side^4` vertices and `4 side^4` oriented
branches. `J` realizes four axis currents; `C` reads four cuts. `D` contains the actual base-zero
square currents in planes 01 and 02. The source law is
`j' + tau D M Dᵀ j' = j + J u + D f`, with
`M = [[mu,nu],[nu,mu]]`, `tau >= 0`, `mu±nu >= 0`. The source sequence varies the material,
clock interval and forcing independently of observed answers. This dimensionless rational law
is an exterior reference construction, with no native HNN execution or physical power claim.

[definition] The continuing state stores four cuts, two active face coordinates, chronology,
the geometric decoder parameter, and a sparse immutable residual blind to both receivers.
An arbitrary retained residual may require the full source extent. Full current decoding uses
the admitted geometric maps; the four-cut section alone leaves a nonzero current discrepancy.

```bash
PATH=/opt/cuda/bin:$PATH cargo build --release -p holonic-engine --example four_torus_current --no-default-features
python research/experiments/four_torus_current/verify.py \
  target/release/examples/four_torus_current /path/to/new/evidence-directory
```

[definition] `verify.py` executes seven fresh processes, compares their returned states and
receivers, and records each child's Linux `wait4` resource observations. It supplies no solver.
Use a new output directory to preserve previous evidence. The binary also supports
`run SIDE STEPS OUTPUT [blind]` and `resume STATE STEPS OUTPUT`.

[established-bounded; implemented-exact; computational-witness]
[`2026-09-08/run1/comparison.json`](2026-09-08/run1/comparison.json) returned:

- Twelve events on side 2, reproduced exactly by five events followed by seven in a new process,
  both with and without the joint-blind source remainder.
- Six matching events on side 3 preserve cuts, active face readings, clocks and the declared
  active material energy. Each event separately satisfies the full branch equation and exact
  decoder equality.
- The eight-entry cold residual changes the full current but leaves the declared future joint
  readings unchanged. Edge 2 separates the currents after twelve events.

[established-bounded; measured] The receipts report continuing update, full solve, decoder,
operator/source assembly, inverse certification, serialized standing and whole-process costs
separately. These are measurements of this dense reference apparatus, not a comparison against
an optimized sparse solver. The recorded build used an isolated checkout at `04064e78` plus the
new example, preserving another session's pending native changes. The initial measurement driver
attempt found no `/usr/bin/time`; the completed driver uses `wait4` and all seven returned exit 0.
