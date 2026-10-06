# Host shared-clock and physical aging interface

Supersedes v1, which was withdrawn before any native child launched. Base remains
128235e82943276a1eaa1ca9a7bc21fab0826f8e in .local/wt/capacity.

Both APIs now take the exact executed per-ring tick vector:

```rust
SourceMoment::check_clock_synchronization(
    &self, field: &Field, current: &Current,
    external_cells: u64, external_ticks: &[u64],
) -> Result<(), HnnError>
SourceMoment::synchronize_clock(
    &mut self, field: &Field, current: &Current,
    external_cells: u64, external_ticks: &[u64],
) -> Result<(), HnnError>
```

The check requires the complete field vector and each external advance at most
`period_g * external_cells`, plus the existing partition/extent/M/winding checks.
Synchronization changes M/profile and decays any retained Leaky first/offset
coordinates by the actual ticks of their source ring, using the existing exact
nearest-lattice transport. It preserves the original opening, own count/bins,
own accumulated tick count/age endpoint and held suffix. There is no pending
history or new save field. The retained coordinate box is unchanged: decay
cannot increase a coordinate. Zero-time rekey supplies a vector of zeros.

After selected ingest, derive ticks from each reached Current lift minus the
call's found lift, for the ACTUAL accepted prefix. Pass them and ingested.cells
to every OTHER mirror; the selected moment already paid its own steps. Validate
every prospective sibling check before address/aeon publication. On a refused
check discard the selected attempted open and restore found Current; untouched
siblings stay valid. Keep unchecked card-write failures discarding the affected
card open. After key relocation pass external_cells=0 and all-zero ticks. CUDA
Leaky remains outside the card scope; no new coordinate kernel is requested.

SourceCapacity::Reframed and its exact count remain as v1: fixed opening,
partition/profile and declared n/M; independent source endpoints and full
Current are counted; no old n_star or adaptive-Theta/key capacity claim.
Mandatory source-clock M plain|reframed plus the existing coordinate maps save
the complete supported ingestion state.

Host v2 includes a physics regression where an old source datum, one sibling
ring tick and a fresh owning datum without an owning source tick read charted
1/3 and 2/3. It also checks offset-pair aging and exact save/read, with malformed
external footprints refusing before mutation. This is a bounded unit fixture,
not a curriculum or scientific result.

Use the existing single queue, unchanged build envelope and fixed measured
operation projection: 128 aggregate CPU seconds,65 wall seconds,eight threads,
4 GiB group/Swap0,8 GiB prelaunch/4 GiB running floor. No native child launched
under the withdrawn v1 source. The two lease-only deferrals remain saved.
Host v2 linkage and focused host/CUDA regressions are the admitted scope;
full library/GPU/scientific reads remain distinct gates. No raised failed limit.
