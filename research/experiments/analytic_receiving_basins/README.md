# Exact analytic receiving populations

[established-bounded; computational-witness] The [returned data](return.ron) is produced by
the public `relational-geometry` analytic library from ζ jets with Euler–Maclaurin remainders.
Three supplied initial squares, centered at `1/2+14i`, `1/2+21i`, `1/2+25i`, each with radius
`1/100000000`, propose receiving centers through three enclosed releases. The code then
certifies the actual source on squares of radius `1/10000` around the returned centers.
No known zero coordinates are supplied to the source or used as expected answers.

[established-bounded; computational-witness] All three receiving squares are strict contractions
with `q≤45/4096`; independent η boundary transport gives winding one on each. Nine complete
initial squares at real coordinates `1/4,1/2,3/4` and the three supplied heights reach those
receivers. Their release counts are `(3,2,3)`, `(3,2,3)`, `(3,1,3)` respectively. A tenth square
intersecting the ζ pole returns its source obstruction and the unchanged input region.

[definition] The receiving centers are proposed from enclosure centers, then independently
certified over full neighborhoods. `mean_value_release` retains `N(m)+N'(X)(X−m)`; it does
not replace X by m. An enclosed first-derivative refusal or finite horizon returns the current
family. No undecided region is labeled a fractal boundary. The mathematical recurrence and
all its preimages are specified in the [source guide](../../../docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md).

[definition] Reproduce from the repository root:

```sh
cargo run --release -p relational-geometry --example analytic_receiving_basins -- /absolute/output.ron
```

[established-bounded; measured] The retained run used 71 ζ jet callback evaluations and
19309585 microseconds on the Ryzen 9 7900X workstation. That end-to-end clock includes
discovering/certifying the three neighborhoods, the independent η winding calculations,
and the ten region requests; it excludes compilation and final serialization. The callback
count excludes η evaluations internal to winding. The nine captured-region requests took
257840–902331 microseconds each after receiving neighborhoods existed. These are CPU exact
analytic measurements, not GPU or power measurements. Source config and exact interval data
remain in the return.
