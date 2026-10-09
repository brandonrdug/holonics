# Native duplex example smoke

Source `9e8041d0a60579077838fc37cc31457fee54a05b`, tree `c09bbaa22cf7a4b9efa5121a0e0c71fc494086a4`.

Exact command `cargo run -p holonics --example helical_duplex` from `/home/b/Workspaces/holonics/.local/wt/helical-duplex-demo` exited zero. The worktree remains clean.

Fixed-key known-truth calibration only. Intact decoding releases; one-sided damage holds two witnesses, including the source, with diameter 1; coordinated damage releases a changed class and only the harness labels its residual. No learned repair acceptance.

| Unit | Complete stage wall ns | Child wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child peak RSS KiB |
|---|---:|---:|---:|---:|---:|---:|
| cache-prep | 9529464195 | 9346619072 | 17000000000 | 6787542000 | 4294967296 | 39172 |
| smoke | 34575764857 | 32822160044 | 65000000000 | 33579066000 | 2229260288 | 1645936 |

Private byte-sealed reflink cache; toolchain and registry provenance checked, local library and example freshly compiled. Existing exclusive queue, one CPU, 8 GiB job ceiling and fixed workload window retained. Preparation was a separate bounded unit. All final acceptances have matching cleanup and quiescent releases.

Three existing library dead-code warnings are preserved in stderr. This smoke does not authorize deleting those methods without consumer repair and ownership review.

Actual stdout:

```text
Helical duplex — known-truth calibration; no learned-repair claim
Navigator: periods=[3, 4], joint period=12, advances=[9, 4, 10, 3], cell labels=[0, 3, 2, 1]
Input passage: supplied key=1, letters=[0, 1], absolute lifts=[1, 10, 14]
Paired representation: partner=[0, 1], absolute lifts=[0, 4, 13]
Receiver result: readings=[[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]; [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]; [1, 0, 0, 0, 1, 0, 0, 0, 0, 0]], terminal winding=1
Intact decode: Released; members=1, diameter=0, readings=[[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]; [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]; [1, 0, 0, 0, 1, 0, 0, 0, 0, 0]], terminal winding=1
One-sided damage: strand contact 0 changes 0 to 1; partner=[0, 1]; carried shift=-5
One-sided decode: Held; members=2, diameter=1, reached supports=[1, 2, 2], differing coordinate=1
  witness 1: letters=[1, 1], lifts=[1, 5, 9], terminal winding=0
  witness 2: letters=[0, 1], lifts=[1, 10, 14], terminal winding=1
Harness-only known-truth check: source is among these witnesses=true; no class was released, so no residual label is assigned.
Coordinated damage (outside one-sided coverage): strand=[1, 1], partner=[0, 0], slipped contacts=[]
Coordinated decode: Released; members=1, diameter=0, readings=[[1, 0, 0, 0, 0, 0, 0, 0, 0, 0]; [0, 1, 0, 0, 0, 0, 1, 1, 0, 0]; [0, 0, 0, 1, 0, 1, 0, 0, 0, 1]], terminal winding=0
Harness-only known-truth result: Residual { at: 1 }
```

Whole [stdout](stages/helical-duplex-demo-smoke-20261009-v135.stdout), [stderr](stages/helical-duplex-demo-smoke-20261009-v135.stderr), [validation](VALIDATION.json). Source, executable and complete resource/provenance receipts are preserved here.
