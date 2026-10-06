# The leaky coordinates are bounded by the admitted drive count

**Date.** October 6. **Issues.** #73, #76, #62. **Grade.** [definition; agent-inferred].
The new Lean leaf and native integration draft are pending compiled checks by Opus.
No training, GPU job, compiler or scientific generator ran for this increment.

The computational object is the helical pair interaction. The join touches the helix
(the source ring's ticks and fixed opened transport), faces and placement (the slot
partition and cardinality reading), and tube (the retained passage continuing into its
future readings). Pair, cell holonomy and tower thread remain attached through the
existing field. The failures guarded here are a histogram mistaken for the retained
carrier, undriven dissipation mistaken for bounded driven motion, and a count read
through an incompatible producer or a different carrier.

## The recovered recurrence and future

The owners are `hnn/moment.rs::Leaky::{open,decay,enter,normalized}` and
`SourceMoment::{open_with,ingest,continued,normalized_counts,offset_table}`.
`HNN/IndexedOpen` already proves the exact nearest-point tick and the error relative
to unrounded transport (`leaky_tick_eq_nearest`, `leaky_count_ingest` and
`leaky_read_error`). The transport's energy factor is `rho^2 <= 1` per tick;
`dissipative_term_modulus` is its undriven amplitude statement. None bounds the
injected data between ticks. `Foundation/Standing`'s retention contract requires
keeping what the admitted future can distinguish. The future normalized reads use
the actual leaky coordinates, so their cardinality cannot be dropped from a claim
about the complete source moment.

For one fixed opening, the source stores dyadic `rho = k/2^s`, `0 < rho < 1`, and
the lattice unit `U = 2^u`, `u = L_nu + m`, where `m` is the least integer with
`2^m(1-rho) >= 1`. Every coordinate opens at zero. An executed ring tick is

```text
v_next = floor((2*v*k + 2^s) / 2^(s+1)) = nearest(rho*v).
```

After that cell's ticks, ingest adds exactly `U` to its one declared first slot and,
where an earlier cell exists, one slot of each offset map. A continued section's
entry adds `nearest(rho^age * U)`, between zero and `U`. Sparse maps keep strictly
positive integer entries at declared slots; absence is the single representation of
zero. The modulus, numerator, shift and unit do not change during this opening.
Changing a learned constitution between openings is outside this conditional count.

## A finite bound at each consumed count

For integer `v >= 0` and `0 <= rho <= 1`,

```text
0 <= nearest(rho*v) <= v.
```

The upper inequality uses that `rho*v <= v` and `v` is an integer; the extra half
unit in ties-up rounding cannot raise its floor above `v`. Thus any sequence of ticks
and at most `n` admitted injected data gives `0 <= v <= n*U`. No lower bound on tick
frequency is required. For a leaky ring with declared alphabet size `A`, period `d`
and `J` offsets, its finite slot count is

```text
S = d*A + J*d*A^2.
B(n) = (n*U + 1)^S.
N_complete(n) <= N_histogram,b(n) * product_leaky_rings B_g(n).
```

All opening metadata is fixed in this comparison. This count does not include an
adaptive constitution or an arbitrary choice of lattice precision. `N_histogram,b`
is the separately derived identity/ranged histogram and lift bound. It is not a
whole-moment crossover once any `B_g` is present. The new leaf
`HNN/LeakyCapacity.lean` reuses `IndexedOpen.carried`, proves the coordinate bound,
the finite integer box and its product count, and proves that the added factors
remain log-concave. The existing persistent-crossover argument consequently applies
to the **complete** product if a complete-product crossing is separately certified.

The runtime draft reads a cheaper exact integer upper bound in bits. For `n > 0`,
`ceil(log2(n*2^u+1)) = bit_length(n)+u`, so it sums

```text
state_bits_upper = ceil(log2 N_histogram,b(n))
                 + sum_g S_g*(bit_length(n)+u_g).
```

At `n=0` every leaky factor is one. This avoids allocating huge shifted values or
running a new crossover search at each receipt. The reading is explicitly an upper
bound; its `histogram_n_star` remains explicitly the narrower histogram crossover.
No whole-moment lossiness follows merely because `n` has crossed that number.

## Why there is no bound uniform over counts

A cell can fit no lock of a source ring and receive no predecessor carry. Its ring
takes zero ticks and its slot still gains `U`. Repeating that admitted datum gives
`v_n = n*U` at a fixed `rho < 1`. The recorded ingest counterexample in
`IndexedOpen.leaky_read_exceeds_chart_unit` already uses a source with repeated
nonfitting cells at the same phase. `LeakyCapacity.no_uniform_bound_without_ticks`
states the drive-only recurrence for any positive `U`.

A bound independent of `n` would need an actual admitted bound on drive between
positive ticks, together with fixed precision and a gap below one. It does not follow
from passivity. This increment does not impose such an extra source law; the finite
count-dependent box covers the existing admission. The no-uniform-bound theorem
quantifies over unbounded mathematical counts. The native `u64` count ceiling gives
the separate finite bound `(2^64-1)*U` at fixed metadata; that is a representation
ceiling, not a decay-derived bound on an indefinitely continuing source.

## The exact consuming condition

The private `checked-capacity-consumer.v2.rs` draft checks these before every reading:

1. The moment carries the partition from its actual opening: all ring periods,
   source indices, alphabet and offsets. That tag must equal the reading field's
   partition. Save/restore must carry it explicitly; the passed field is not used to
   invent an absent producer tag. The fixed partition is law metadata, not a passage.
2. The moment is the proved **ingest-only carrier**: every station extent is zero,
   every source's first mass is `n`, offset mass is `max(n-delta,0)`, vector shapes
   match, window occupancy/cursor match the consumed count, start/end phases match,
   and source ticks equal the reached lift minus opening lift. A populated
   `SourceMoment::continued` has another carrier and refuses this reading.
3. The full reached lift is within the admitted identity/ranged bound. This checks
   the reached state; the prefix theorem alone does not certify a stopping kernel.
4. Every leaky modulus is positive, below one and dyadic. Numerator/shift agree with
   it and `u` is the constructor's least lattice exponent at the field's population
   chart. Each map has declared slots, canonical positive values and `v <= n*2^u`.
   The latter uses quotient/remainder, avoiding allocation of the bound itself.

The resulting `SourceCapacity::Retained` gives `state_bits_upper` and explicitly
qualified `histogram_n_star`; it does not leave a supported leaky moment as `Owed`.
An unsupported partition, continued carrier, malformed saved coordinate or out-of-box
lift returns a typed error. There is no unchecked `SourceCapacity::of` bypass.

Opus owns joining the producing partition to open/read/write and migrating host
ingest, card ingest and StateReport to `checked_of(..., reached_current)` with typed
refusal and the established failed-open disposition. This is a concrete pending
consumer join, not a completed runtime claim. The increment uses merged source pin
`3c67beee7f656798f912c974f12c482ea12c5e42` for integration; its derivation worktree
remains based at `c0275dd0647d265c73525d12584bb224c6e90b25`.

The bounded exact scalar controls pass: `6144 = 3*2^11` drive/tick paths,
`255 = 3*5*17` dyadic opening metadata cases and `1053 = 3^4*13`
quotient/remainder comparisons. The separate scalar example
`d=(2,3,5)`, `A=5`, offsets `(1,3)`, one leaky ring with `u=4` and `S=275` gives
histogram crossing `436` and complete-product crossing `2534 = 2*7*181`.
The scalar lattice is declared for this arithmetic control; it is not reported as
a production field's actual grain. The native fixture draft tests the actual opened
grain, zero-tick ingestion, malformed maps, continuation refusals and incompatible
producer partitions. None of those native fixtures has been executed yet.
