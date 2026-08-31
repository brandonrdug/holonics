# MorphoHDL: data types and machinery conventions

Source: `https://github.com/paradigms-of-intelligence/morpho`, commit `dc8dd2e405012909c711b651fbca39cf1f24ac44` (2026-08-23, "viewer: add cell glow and strike API"), cloned to `$S/refs/morpho`. All paths below are relative to that root.

## 1. Identity and purpose

MorphoHDL is "a minimalistic language for growing circuits through structural recursion" by Alexander Mordvintsev (Paradigms of Intelligence, Google), Apache-2.0. The article (`article.md`, rendered by `index.html` via `js/article.js`) frames it as a graph rewrite system: "Graph nodes are functional cells with indexed input and output ports, and edges are buses carrying a variable number of wires. Cells define rewrite rules: a single node is replaced by a set of subcells... Cells are size-agnostic." It is explicitly "a practical instance of Parametric L-Systems, where the hierarchical tree of cell lineage generates general graphs by inheriting lateral connections", and explicitly "a conceptual sketch rather than a complete, production-ready system". Scope is combinational circuits only; sequential logic is a design discussion.

Three interpreters of the same program exist (`article.md` "Interpreting MorphoHDL programs"): imperative execution (`tiny_morpho.py:CircuitRunner`), traced execution into a netlist (`tiny_morpho.py:CircuitCompiler`), and progressive graph rewriting (`js/compiler.js:CompiledGraph`). `js/utils.js:loadMorphoCode` slices the text between `# MORPHO_BEGIN` and `# MORPHO_END` in `tiny_morpho.py`, so the Python file is simultaneously the reference implementation and the source the browser parses.

## 2. Core data types

### Buses (Python)
A bus is a NumPy `int32` array indexed LSB-first, shape `(width,)` or `(width, samples)`. Constants at `tiny_morpho.py:112`:
```python
ZERO = np.zeros((1,), dtype=np.int32)
ONE  = np.ones((1,), dtype=np.int32)
VOID = np.zeros((0,), dtype=np.int32)
```
In compile mode a bus is the same array type but holds wire indices (see `add_input` below), so the user program cannot tell simulation from tracing.

### LUT primitive (`tiny_morpho.py:65`)
```python
def LUT(arg_n, lut, name=None):
    ...
    def f(*args):
        assert len(args) == arg_n
        if any(len(a) == 0 for a in args):
            raise IndexError
        runner = G_Runner.get() or CircuitRunner
        return runner.run_lut(lut, args, name)
```
Truth table bit index puts argument k at bit k (`CircuitRunner.run_lut`: `idx = idx + ((val.astype(np.int32)) << k)`; `out = (lut >> idx) & 1`). The name is pulled from the assignment via `inspect.stack()[1].code_context` ("a hack"). Library: `Not=LUT(1,0b01)`, `And=LUT(2,0b1000)`, `Or=LUT(2,0b1110)`, `Xor=LUT(2,0b0110)`, `Xor3=LUT(3,0b1001_0110)`, `Maj3=LUT(3,0b1110_1000)`, `carry_op=LUT(3,0b1110_1100)`, `Mux2=LUT(3,0b1100_1010)`. An empty input bus is a boundary, not a no-op.

### `@morpho` and `fallback` (`tiny_morpho.py:79`)
```python
def morpho(f=None, fallback=None):
    ...
    def wrapper(*args, **new_overrides):
        overrides = {**G_Overrides.get(), **new_overrides}
        ...
        target_f = overrides.get(f.__name__, f)
        runner = G_Runner.get() or CircuitRunner
        try:
            return runner.run_cell(target_f, args)
        except IndexError:
            if callable(fallback):
                return fallback(*args)
            elif isinstance(fallback, int):
                return args[fallback]
            raise
```
`fallback` is either a cell (same signature) or a positional index meaning "pass argument N through". Keyword arguments are cell substitutions ("alleles") propagated down the call tree via `contextvars` (`grid(x, y, grid_base=base_skip)`).

### Bus combinators (`tiny_morpho.py:104-121`)
`SPLIT(x)` returns `x[:n//2], x[n//2:]` and raises `IndexError` if `n < 2`. `LSLICE(x, ref)` / `HSLICE(x, ref)` cut `len(ref)` wires off the low/high end returning `(slice, rest)` and raise if `x` is shorter. `REPEAT(x, ref)` is `np.repeat(x, len(ref), 0)`. `CAT(*arrays)` is `np.concatenate(_normalize_shapes(arrays))`. Plain slicing (`carry[:-1]`, `x[::-1]`, `a[2]`) is also used and also raises on out-of-range.

### Traced netlist (`tiny_morpho.py:CircuitCompiler`)
```python
Op = namedtuple('Op', ['type', 'name', 'lut', 'args'], defaults=(None, None))
self.ops = [Op('CONST', '0'), Op('CONST', '1')]
```
Wire 0 and 1 are constants. `add_input` appends one `Op('INPUT', f'{name}[{i}]')` per bit and returns `np.arange(end-n, end)`. `run_lut` emits one `Op('GATE', name, lut, tuple(gate_args))` per output bit, broadcasting width-1 arguments (`a[0] if len(a)==1 else a[i]`). `run_cell` records `(f.__name__, in_widths, out_widths)` in `cell_calls`. `_optimize_gate` does constant propagation via `fix_lut_input`, duplicate-input merging via `merge_lut_inputs` (`np.diagonal` of the unpacked truth table), ignored-input detection, and collapses to constant or buffer; `strip_unused_gates` is a backward liveness pass. `compile(f, arg_sizes)` takes input names from `inspect.signature(f).parameters`; `jit_runner` memoizes compiled circuits by `tuple(len(a) for a in args)`.

### JS AST (`js/parser.js`)
`parse(code)` returns `{ luts: [{name, arity, value}], cells: [{name, inputs, outputs, fallback, ssa}] }`, where each SSA instruction is `{ targets, op, args, overrides? }` (`emitSSA`, temporaries `_tmp_N`). `x[i]` becomes `INDEX`, `x[a:b:c]` becomes `SLICE`. The tokenizer regex accepts `0b`, `0x`, underscores.

### JS primitives (`js/primitives.js:143`)
`PRIMITIVES` is a table of `(args, resolve) -> [outputWireLists] | null`; `null` is the boundary signal. E.g.
```js
SPLIT(args, resolve) {
    const w = resolve(args[0]);
    if (w.length < 2) return null;
    const half = Math.floor(w.length / 2);
    return [w.slice(0, half), w.slice(half)];
},
```
`optimizeLUT(lut, wires)` returns `[replacementWire, externalUseMask]` (`-1` = keep gate).

### SoA flat graph (`js/compiler.js`, `js/utils.js:SoA`)
`SoA(schema, capacity)` builds one typed array per field from `{name: [Type, fill, multiplier]}`, with `alloc(n)` and doubling `grow`. `CELL_TYPES = { INPUT: 1, OUTPUT: 2, LUT: 3, MORPHO: 4 }`.
```js
const CELL_SCHEMA = {
    active: [Uint8Array, 0],        // 1 if active, 0 if deleted
    type: [Uint8Array, 0],
    lutValue: [Uint32Array, 0],     // 0 represents hierarchical complex cell
    lutArity: [Uint8Array, 0],
    parent: [Int32Array, -1],       // Index of parent cell, or -1
    pinStart: [Int32Array, 0],
    inputCount: [Int32Array, 0],
    outputCount: [Int32Array, 0],
    activeOutputs: [Int32Array, 0], // for dead-code checking
    netStart: [Int32Array, -1],     // contiguous output nets driven by this cell
    firstTime: [Float32Array, 0],
    lastTime: [Float32Array, 0]
};
```
plus parallel JS arrays `cell.name[]` and `cell.def[]` (template `CompiledGraph` for MORPHO cells). Pins are input terminals only:
```js
const PIN_SCHEMA = { cell, net, nextDst, prevDst }   // Int32, -1
const NET_SCHEMA = { firstDstPin, driverCell, fanout }
```
Each net's destination pins form a circular doubly-linked ring (`connectPin`/`disconnectPin`/`mergeNets`). Nets 0 and 1 are reserved (`this.net = new SoA(NET_SCHEMA, ..., 2); this.net.name = ["ZERO", "ONE"]`). Pin layout: hierarchical cells are port-ordered; LUT cells are slot-ordered so `getLutPinIndex(cell, port, slot) = pinStart + slot*arity + port`, which lets `_splitCell` halve a wide LUT with zero allocation. A LUT slot is identified by the net it drives (`netStart[cell] + slot`), a key that "self-invalidates: a bypassed or dead slot has net.driverCell === -1".

### Materialization registry (`js/compiler.js:materialize`)
```js
const sigKey = (name, sig) => `${name}:[${sig.join(',')}]`;   // "ripple_adder:[4,4,1]"
function materialize(name, sig, context) {
    const overriddenName = context.cellOverrides?.[name] || name;
    const key = sigKey(overriddenName, sig);
    if (context.registry.has(key)) return context.registry.get(key);
    ...
    const graph = buildCellBody(cellDef, sig, context) ?? materializeFallback(cellDef, sig, context);
    context.registry.set(key, graph);
```
A rewrite rule is therefore a `cellDef` (SSA body + fallback); a materialized rule is a `CompiledGraph` per concrete input signature. `materializeFallback` with a numeric fallback builds "a pristine pass-through graph wiring input #fbIdx straight to the output". `materializeLut` returns `null` if any input bus is empty and broadcasts width-1 buses to `w = max(...lengths)`. `materializeCell` masks parent nets feeding unused child inputs with `-1` so DCE can prune drivers early.

### Geometry (`js/force_layout.js`)
```js
const CELL_LAYOUT_SCHEMA = { x, y, r, fx, fy, vx, vy };   // Float32, r fill 1
```
indexed by the same cell index as the graph. The WASM side (`graphs_engine/src/main.c`) exposes `points`, `vel` (xyz triples), `links`, `link_weights` and octree buffers through `BUFFER`/`DYNAMIC_BUFFER` macros that `prepareWASM` maps to typed-array views.

## 3. Growth semantics

**Root.** `compileModule(parsed, rootName, sig, optimize, maxFanout)` materializes the whole registry eagerly (Python-style recursion, memoized), then `createRoot()` builds a graph containing one INPUT cell per port, "A single unexpanded MORPHO cell", and one OUTPUT cell per port.

**One step** is `CompiledGraph.expandCell(targetCellIdx, optimize)` dispatching on `_expandStep`:
1. MORPHO cell: `_expandMorpho` inlines `cell.def[target]`. It maps inner input nets to the parent's pin nets (`innerToOuterNet[innerRootInputNet] = this.pin.net[targetPinStart + i]`), clones every non-system inner cell with `_cloneCellMetadata(i, targetCellIdx, innerGraph)` so `parent = targetCellIdx`, allocates fresh output nets, re-creates pins, then `_mergeGlobalIO` merges each inner output net into the parent's existing output net (`mergeNets(outerNet, targetNetStart + i)`), so consumers of the parent keep their pins untouched. Finally `_disconnectParentCell` sets `active[target] = 0`.
2. Wide INPUT/OUTPUT/LUT cell (`outputCount > 1` or `inputCount > 1`): `_splitCell` halves it at `S1 = floor(S/2)` into two children whose `parent` is the original, reusing the same pin and net ranges.
3. Leaf with a net exceeding `maxFanout`: `_bufferCellNets` inserts up to `numGroups = 3` `BUF` cells (`lut: { value: 2, arity: 1 }`) and re-parents destination pins.

`isExpandable` is true for any MORPHO cell, any multi-wire IO/LUT cell, or any cell with a high-fanout net; growth terminates when no cell is expandable (`Grower.isFullyExpanded`).

**Width propagation and termination.** Widths are never declared; they are the lengths of the wire lists flowing through `buildCellBody`. A child's output width is known only after the child materializes, which is why materialization is on demand and memoized by signature. Recursion ends when a primitive returns `null` (JS) or raises `IndexError` (Python); the enclosing cell is discarded and its `fallback` is materialized with the same signature. The article states the invariant: "The final growth result is order-independent, but the order matters for aesthetic reasons".

**Schedules** (`js/grower.js`): `expandNext` walks `headIdx` linearly over the append-only cell array, which is breadth-first by creation order; `expandLargest` pops a `MaxHeap` keyed by `getCellEstimateSize` (LUT count of the template, `estimateLUTCount`, computed at materialization). `_expandCell` chains single-child expansions so a rewrite that produces exactly one expandable cell keeps going within the same step.

**Optimization is interleaved with growth.** `expandCell(..., optimize=true)` calls `commitOptimizations()` = `propagateLUTs()` then `propagateDCE()`, both worklist-driven (`dirtyLutSlots`, `deadNets`) and cascading non-topologically; `disconnectPin` feeds `deadNets` whenever fanout reaches 0. Fanout buffers are protected from collapsing back (`isBuf && fanout > 1` -> skip).

**Geometry co-grows.** `LayoutEngine._updateGraph` gives each new cell a position derived from its parent:
```js
this.node.x[i] = this.node.x[parent] + (this.random() - 0.5)*2.0;
```
and the viewer seeds smoothed positions from the parent too (`viewer.js:loop`: `this.smoothedX[i] = this.smoothedX[parent]`). So a rewrite is literally a cell division at the parent's location, and lateral wiring is inherited through the net-merge step. Layout is otherwise independent of logic ("logic connectivity is not layout-dependent in the current prototype").

**Evaluation.** Python: `CircuitCompiler.__call__` evaluates ops in index order over `(ops, samples)` arrays. JS: there is no runtime evaluator in the shipped viewer; `scratch/test_compiler.js:simulate` does DFS topological evaluation of LUT slots (`addr |= val << portIdx; values[outNet] = (lutVal >> addr) & 1`). The viewer's "simulation" is `updateTimes()`, a Kahn sweep assigning `firstTime`/`lastTime` = unit-delay arrival depth, which drives the animated signal wave.

## 4. Rendering and UI conventions

**Controls.** Hero (`index.html`): `select-hero-method` BFS/Largest, `btn-hero-play` Pause/Resume (toggles `viewer.isRunning`, which freezes both expansion and layout relaxation), `btn-hero-expand` "Re-grow" (`heroViewer.reset(); heroViewer.startAutoExpand()`), `btn-hero-explore` linking to `demo.html?design=...&method=...`. Explorer (`demo.html`, `js/demo.js`): Auto/Step/Pause/Reset, Speed slider 1-200 "%/s", Method BFS/Heap, Show both/nodes/wires, "Run Logic Simulation", Export `netlist.json`/`mask.json`, a "Design Hierarchy" tree fed by `onCellAdded(cellIdx, name, parentIdx)` where clicking a label calls `setActiveCell` (descendants computed by walking `cell.parent`), dimming everything else to opacity 0.15.

**Animation.** `viewer.js:loop`: `expansionsPending += autoExpandSpeed * dt * cell.count / 100` (speed is a percentage of current cell count per second, so growth accelerates), then `grower.relaxLayout(2)` per frame, positions eased at 0.1 toward layout targets, new cells `strike(i)` a glow (`glowLife 0.5`), autoscale fits the bounding box. When growth completes `onGrowthComplete` auto-starts the timing wave: `simTime` cycles from `-(pauseDuration + fadeDuration)` to `maxDepth * tStep` with `TIMING_CONFIG = { pulseDuration: 0.35, fadeDuration: 0.5, pauseDuration: 2.0, defaultTStep: 0.45 }`.

**Layout.** Force-directed, not grid: Barnes-Hut repulsion on a Morton-sorted octree (`dilate3`, `buildOctree`, `theta 0.5`), spring `linkForce` toward `linkDistance 2.0` clamped to +/-0.25 and weighted `1/(deg_src+deg_dst)`, centering gravity `0.1/max(N,16)`, `compensateVelocity` removing net angular momentum, speed clamp and decay. Defaults: `repulsionForce 0.05, wireForce 1.0, velocityDecay 0.05, maxDist 80, gravity 0.1`. `js/hex_layout.js:HexLayoutEngine` is an alternative axial-hex annealer (`T0 0.5, decay 0.98`, BFS to nearest vacant hex from the parent, pushing occupants along the path) but is not imported by `Grower`.

**Color/shape** (`js/layout_renderer.js:CELL_STYLES`): inputs blue `[0.2,0.604,0.941]` glyph `I`; outputs red `[1.0,0.42,0.42]` glyph `O`; unexpanded MORPHO cells amber `__EXPANDABLE__ [0.98,0.69,0.02]`; `And` green `&`, `Xor` purple `^`, `Maj3` orange `M3`, `carry_op` teal `C`, `Mux2` green `Y`, `Not` pink `~`, `BUF` grey at half radius. Depth coloring is `vec3(ratio, 0.898*(1-ratio), 1-ratio*0.667)` (cyan at inputs to magenta-red at outputs). Multi-output nets fan out from a golden-angle spiral (`netOffsetsX/Y`, theta `2.3999632297286533`). Nodes are circles drawn as quads in a SwissGL shader from a `rgba32f` texture; node slot = 12 floats `(x,y,r,opacity,rgb,_,delay,charCode,brightness,struckAt)`, link slot = 8 floats `(p0,p1,tDriver,tTarget,isHighlighted,_)`. Background `[0.043,0.059,0.098]`. Static article figures (`js/figures.js`) replay `{x,y,labels,unique_labels,edges}` JSON with labels `in:root[bit]`/`out:root[bit]` and a "RESOLVED BITS" row of output dots.

## 5. Machinery conventions

- **Determinism.** Layout RNG is `mulberry32(1337)`; hex annealer shuffles with the same seeded RNG; JIT caches keyed by widths; expansion order is a pure function of `method`. Only `viewerId`/`plotId` use `Math.random`, and test fuzzing.
- **Identity.** Cells and nets are append-only indices; nothing is ever deleted, `active = 0` marks replacement, and `parent` gives the lineage chain (the tooltip walks it, `exportMask` uses it). Nets merge rather than move: `mergeNets` re-points pins and sets `driverCell[B] = -1`. Tests assert golden table sizes (`cell.count 1934, pin.count 6315, net.count 3711` for `wallace_multiplier [16,16]`, 936 active cells, 872 LUT wires).
- **Caching.** Registry by `sigKey`; `fixLutCache`/`mergeLutCache` maps in JS, `lru_cache` in Python; `getCellEstimateSize` reads a precomputed `estimateLUTCount`.
- **Recursion depth.** Python relies on the interpreter stack (log-depth for divide-and-conquer, linear for tail-recursive cells like `right_shifter`/`triangle`). JS `materialize` is recursive but memoized; `updateTimes` is deliberately iterative ("no recursion, no stack-depth limit").
- **Error handling.** `IndexError` is the sole control-flow mechanism in Python; `null` return is its JS twin. Parse errors carry `.line` for editor highlighting; `Unknown identifier`, `Unknown operation`, `Unknown cell` throw. `AGENTS.md` prescribes oracles over hardcoded checks: "Circular Linkages, Fanout conservation"; `verifyGraphIntegrity` asserts sum of fanouts equals connected pins, every ring is consistent, and every active cell owns its pins and drives its nets.
- **Laziness.** Dirty worklists (`dirtyLutSlots`, `deadNets`), `needsTextureUpdate` flags, `IntersectionObserver` pausing loops.

## 6. Abstractions to lift for a Lean mathematics CAD

1. A component is a rewrite rule with a fallback base case: recursion and termination live in one object (`cellDef {ssa, fallback}`), and the base case is data, not a conditional.
2. Failure is a boundary signal, not an error: a primitive returning `null`/raising unwinds to the nearest rule that can instantiate; a CAD passage that cannot transport should surrender to its fallback rather than abort.
3. Width is inferred at instantiation and memoized by signature (`name:[sig]`): specialize a lattice transport to concrete ranks on demand and cache the specialization.
4. Geometry and logic co-grow by cell division at the parent's position: children inherit their parent's coordinates and lateral edges are inherited through net merging.
5. Growth is a sequence of local rewrites whose result is order-independent; the schedule (BFS vs largest-first by estimated size) is a free aesthetic/placement parameter.
6. Append-only identity with `active` flags and a `parent` array: history is never lost, lineage is a cheap index walk, and undo is implicit.
7. Nets with a driver and a ring of destination pins, merged rather than rewired: connectivity is a partition of terminals, and inlining a rule is a merge of equivalence classes.
8. Constants are reserved slots 0 and 1 in the same index space as signals, so constant propagation is an ordinary merge.
9. Truth tables as integers with algebraic reductions (`fix_lut_input`, `merge_lut_inputs`, ignored-input detection): local rewrites on the primitive's own semantics, cacheable by `(arity, lut, i, val)`.
10. Optimization interleaved with growth via self-invalidating worklists keyed by output index: no global recompute, stale entries are skipped.
11. Cell substitution as keyword overrides propagated through the call context (`grid_base=base_skip`): a rule library parameterized by alleles without duplicating the recursion.
12. Positional fallback shorthand (`fallback=0`) turns "pass argument N through" into a first-class identity morphism.
13. Unit-delay depth (`updateTimes`) as the only temporal quantity: transport "action" over time is a topological sweep, and the same number drives both coloring and animation.
14. Fanout limits enforced structurally by inserting buffer cells: a physical constraint expressed as another rewrite rule.
15. Split-ordered flat storage (`pinStart + slot*arity + port`) so halving a wide primitive is index arithmetic.

**What MorphoHDL does not model.** Timing beyond unit topological depth; physical simulation (layout is aesthetic force relaxation, explicitly not feeding back into logic); 3D (WASM is xyz but the viewer pins `z = 0`); placement/routing constraints, area, wire delay; sequential logic, cycles, or state (the `REG`/forward-reference sketches "currently run" nowhere; `getTopologicalOrder` throws on a cycle); netlist export beyond layout JSON; typed values other than bits; any formal correctness argument (verification is by randomized/exhaustive oracle against integer arithmetic).
