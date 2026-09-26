import Holonics.Compression.Landmark.SiteKind
import Holonics.Compression.Landmark.FixedPoint
import Holonics.Compression.Landmark.Identity
import Holonics.Compression.Landmark.ConstraintIdentity
import Holonics.Compression.Landmark.PrimitiveCycle

/-!
# Landmark discovery: the faces where navigator paths converge

[definition] Rebuild step 3 (#145). **Landmarks** are faces where navigator paths converge: lock
addresses and fixed points, constraint identities, and the primitive cycles (primes) of a return
map. **Landmark discovery** locates them. This root gathers the general laws, stated over the
existing owners (`Transport/NavigatorTraceFaces`, `Geometry/{LocalFactor,TraceSequence}`,
`Geometry/{CrossRatio,TwoSidedIdentityAtlas}`, `Mathematics/{RatioSeriesTransport,
RadixWindowReceiver}`, `Physics/CompositeMassEnergy`, `Aeon/Production/Zeta`).

| Module | Law |
|---|---|
| `Landmark/SiteKind` | a site of positive determinant is a rotation (no real eigenvalue), a null lock (nilpotent traceless part) or a boost (two real eigenvalues of one sign), proved from the matrix; `det < 0` is a reflection, `det = 0` degenerate; `γ² = tr²/(4 det)`; the trace counts grow at exactly the rapidity `log k`; Hasse sites are rotations |
| `Landmark/FixedPoint` | a Möbius navigator has at most two fixed points; one attracts exactly when `tr ≠ 0`, and every path off the pole converges to it; the iterates of one boost converge to `±c` |
| `Landmark/Identity` | an identity is two constructions with one face (the kernel of the face); a chart family certifies exactly the identities of `V` exactly when `I(⋃ images) = I(V)` (Zariski density); missing a component invents `C − 1`, missing a point does not |
| `Landmark/ConstraintIdentity` | π (Machin's arms) and `e` are limits of their partial navigators' convergents; blocks compose associatively; a window is certified by the floors of both enclosure ends, and every window of π and `e` has a finite certificate; `e` is irrational from its own enclosure |
| `Landmark/PrimitiveCycle` | `tr(M_fⁿ) = Σ_(d∣n) d·p_d`, Möbius inversion, and `det(1 − T·M_f) = ∏_d (1 − T^d)^(p_d)`: the dynamical zeta is the Euler product over primitive cycles |

[open] Owed in #62: Gröbner completion and the face-kernel equality, Richardson undecidability,
the necklace integrality and infinite Euler product of a general nonnegative integer return map,
the first-arrival sieve tower as a general law, and the Lefschetz count of torus periodic points.
The identity-atlas search, navigator inference by loop closure and the landmark search's
coverage check are the Rust consumers (`holonics::compression`).
-/
