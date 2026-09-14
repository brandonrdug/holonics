# Exact contact surfaces, gyroparallelogram and receiver stress faces

[established-bounded; implemented-exact] `exact.py` uses rational arithmetic for noncollinear
Lorentz boosts, their gyration/coaddition, a local stress tensor and its receiver contractions.
`surfaces.py` constructs exact rational torus-boundary vertices and 216 conservative contact
facets on each of two boundaries. Their oriented area vectors and whole-facet containment
are checked before any plotting conversion. `receipt.json` and `surface_faces.json` retain
the actual inputs and returns.

[definition] The local tetrad uses signature (-,+,+,+), coordinates x⁰=ct, velocities in
units of c, and stress in unit E0. A pointwise orthonormal tetrad does not assert a globally
flat metric. The numerical example is the local observer algebra; the Einstein/Bianchi field
balance retains the actual geometric/constitutive assumptions in the subject guide.

[established-bounded; implemented-exact] Velocities `(3/5,0,0)` and `(0,4/5,0)` have Lorentz
factors `5/4` and `5/3`. Their two ordered velocity faces are `(3/5,16/25,0)` and
`(9/25,4/5,0)`. The gyration has spatial block `[[35,12],[-12,35]]/37`. The gyroparallelogram
fourth point is `(315/781,560/781,0)`; its two diagonals share the Einstein gyromidpoint
`(9/35,16/35,0)`. `diagram.py` retains rational conic stations for the Poincaré drawing;
a positive algebraic-root constraint specifies the transformed midpoint. Decimal SVG
coordinates are only a pixel code, produced by integer/rational quantization.

[established-bounded; implemented-exact] The supplied symmetric stress tensor and three
receivers give energy-density faces `10`, `67/4`, `298/9` in E0, and power-density faces
`2`, `7/4`, `10/3` in c E0. Transforming tensor, observer and oriented face together
preserves each contraction. Opposite orientations cancel their internal exchange. The local
slip/traction law gives opposite tangential tractions and a positive heat face `3/5` in its
declared normalized power-density unit.

[proved-derived] Contact-facet containment uses the 1-Lipschitz distance to the other core
circle. Its barycenter lies within the tube shrunk by the maximal L1 vertex distance, which
bounds every point of the triangle. The facet's oriented area vector is retained instead of
an unqualified scalar area. Under common material motion it transforms by the cofactor
`det DF·DF^-T`; the renderer applies that map to the displayed normal as well.

[definition] `render_surfaces.py` converts the exact geometric source to plotting coordinates
only after face selection. Floating graphics-library arithmetic paints this exterior image;
it makes no collision, source, tensor or mode decision. The generator, units, exact facet
membership and normal/area constraints remain in the source receipts.

```bash
python3 research/experiments/contact_receiver_faces/exact.py
python3 research/experiments/contact_receiver_faces/surfaces.py
python3 research/experiments/contact_receiver_faces/diagram.py
python3 research/experiments/contact_receiver_faces/render_surfaces.py
```

See `docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md` for the complete constraint-mode,
Lorentz/dilation, active-reception and Einstein-face construction and its source owners.
