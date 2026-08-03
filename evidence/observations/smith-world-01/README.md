# Smith world 01

Bounded exact validation of the conventional one-port Smith map and discrete reference-plane
phase rotation. This world is deliberately separate from the dyadic circuit periplus: it supplies
literal complex impedance `Z`, positive real reference impedance `Z0`, and
`Gamma=(Z-Z0)/(Z+Z0)`.

Run from `src/soma`:

```text
cargo run -p life -- boundary smith-validate observations/smith-world-01/plan.json
```

The output is create-new at `results/smith.json`.

