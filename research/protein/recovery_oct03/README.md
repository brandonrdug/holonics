# Exact fixed-region receiving evidence — October 3

This extends the geometric evidence pinned at commit
`f6a8455b5efb0e4947719c2ebfa9c3d715dfb3cc`. It supplies all 966 newly derived
nondirectional source receivers for the same 69-residue candidate and fixed controls.
No target pose, folding, binding, proton population or pH behavior is established.

The original reciprocal/finite region is phi37 in [-1/16,0], psi37 in [0,1/16],
with phi26=-19/64 and beta=0. All 236 prior internal comparisons and both chord
bounds remain; the cumulative packet has 1202 internal comparisons, four
necessary/sufficient chord faces, and 140 pending target comparisons. Of the 966
new receivers, 644 are positive throughout the original region and 322 initially
remain unresolved. Unresolved bounds are not established physical clashes.

The pair comparisons use a declared severity aperture of (2/3)(r_a+r_b), with quadrance threshold (4/9)(r_a+r_b)^2, from the pinned radius chart. Reported clearance certifies these scaled inequalities only. Unscaled van der Waals separation and physical steric or chemical admission remain unestablished.

The prefix-free restriction cover has Kraft sum 1. The quarter phi37 in [-1/32,0],
psi37 in [0,1/32] is uniformly below the declared pair64/829 aperture. An eighth,
phi37 in [-1/16,-3/64], psi37 in [1/32,1/16], clears all 1202 nondirectional
conditions and the chord faces. Other unresolved leaves remain explicit.

The 110 possible directional obligations are separate. Their geometric receipt
contains 161 source quadrances and 76 D-H-A faces: 109 diagnostic pair apertures
are positive on that eighth and pair64/830 remains unresolved there. The H-angle
sign partition has 41 greater-than-quarter-turn, 23 less-than-quarter-turn and 12
unresolved faces. Twelve pair obligations have no D-H-A face; they are retained.
None of these partitions is a calibrated hydrogen-bond or repulsive-energy test.

The reviewed pair64/830 restriction supplies an exact control-point obstruction
at phi37=-3/64, psi37=1/32: its source quadrance upper bound is below 2, below the
declared 23104/5625 angstrom-squared aperture. This refutes uniform fixture
clearance of that eighth; it does not exclude the entire eighth. Its upper child,
phi37 in [-1/16,-3/64], psi37 in [3/64,1/16], clears the added aperture. This child
has measure 1/16 relative to the original region and inherits all 1202 conditions,
both chord bounds and the other 109 apertures. Angular and material obligations
remain open. The lower child remains unresolved.

`receivers.json` and `conditions.json` preserve exact source-bound tensors at
grains 2^96 and 2^80. `region_cover.json` retains the restrictions, witnesses and
inherited comparisons. `directional_geometry.json` preserves all directional
flags and readings. `runtime_receipts.json` records seven actual bounded stages,
including the 422 and 470 memory.max events in the directional stages; neither
stage had OOM or floor events. No inferred or newly executed chemical screening
model is included in this publication cut.

Run the portable replay in separately bounded parts:

```
python3 research/protein/recovery_oct03/verify.py --part source
python3 research/protein/recovery_oct03/verify.py --part regions
python3 research/protein/recovery_oct03/verify.py --part directional
```

These are exact receiving checks, without search, native generation, solver,
installation or network access. The dependency and payload hashes are in
`manifest.json`; this manifest omits its own digest. External execution receipts
can seal all eight files, including the manifest. The 1088 nested host-path
strings in the comparison lineage are replaced with digest-based receipt IDs;
the four native receipt identities remain, without redistributing those artifacts.

The source coordinates, covalent incidence, guards and selected root branch use
the existing portable `../data/source_faces.json`. Its local 1UBQ-frame ancestry,
observed 6ARU target anchors, CCD source attribution and limits are retained in
[the source guide](../SOURCES.md). wwPDB archive data are CC0 1.0; new code and
authored documentation are MIT OR Apache-2.0. No journal text or figure is copied.
Source-coordinate and transfer uncertainties remain unquantified. Arithmetic
enclosures are not experimental error bars or physiological populations.
