"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const test = require("node:test");
const Exact = require("./exact-series.js");
const Core = require("./observatory-core.js");

const somaRoot = path.resolve(__dirname, "../..");
const read = (relative) => JSON.parse(fs.readFileSync(path.join(somaRoot, relative), "utf8"));
const analysis = read("observations/transport-foil-world-01/analysis.json");
const cellular = read("observations/eros-linguistic-code-world-01/host-run-09/CONSTITUENTS.json");
const prime = read("observations/bounded-polyglot-geometric-world-01/REPORT.json");
const explicit = read("observations/interval-explicit-formula-world-01/build-01/EXPLICIT.json");
const zeros = Core.parseZetaZeros(fs.readFileSync(path.join(somaRoot, "observations/interval-explicit-formula-world-01/LMFDB-FIRST-64-ZEROS.tsv"), "utf8"));

function exactFromRead(value) {
  return Exact.ratio(BigInt(value.numerator), BigInt(value.denominator));
}

function assertNoFractionalNumbers(value, location = "receipt") {
  if (typeof value === "number") {
    assert.equal(Number.isSafeInteger(value), true, `${location} collapsed to a fractional Number`);
    return;
  }
  if (!value || typeof value !== "object") return;
  for (const [key, child] of Object.entries(value)) assertNoFractionalNumbers(child, `${location}.${key}`);
}

test("ratified observer artifacts retain their declared schemas", () => {
  assert.equal(Core.validateAnalysis(analysis), true);
  assert.equal(Core.validateSmith(read("observations/smith-line-world-01/results/line.json")), true);
  assert.equal(Core.validateAtlas(read("observations/circuit-atlas-01/results/changed.atlas.json")), true);
  assert.equal(Core.validateAtlas(read("observations/circuit-atlas-01/results/prior.atlas.json")), true);
  assert.equal(Core.validateCellular(cellular), true);
  assert.equal(Core.validatePrime(prime), true);
  assert.equal(Core.validateExplicit(explicit), true);
});

test("cellular rendering is rooted in one selected carried path, not an absolute whole-body plot", () => {
  const scene = Core.cellularScene({
    report: cellular,
    cutIndex: 1,
    constituentIndex: 0,
    boundaryIndex: 0,
    pathIndex: 0,
    side: "primary",
    layers: new Set(["sheet", "frames"]),
  });
  const constituent = cellular.cuts[1].constituents[0];
  const selectedPath = constituent.boundaries[0].paths[0];
  assert.equal(scene.primitives.filter((item) => item.layer === "frames").length, new Set(selectedPath.steps.map((step) => step.incidence)).size);
  assert.ok(scene.primitives.filter((item) => item.layer === "sheet").length < constituent.cells.length);
  assert.equal(scene.metadata.render_scope.includes("receiver-relative causal order"), true);
  assert.equal(scene.metadata.fingerprint, constituent.fingerprint);
  assert.equal(constituent.source_wire_version, 3);
  assert.equal(constituent.boundaries[0].paths[0].steps[0]?.winding ?? null, null);
  assertNoFractionalNumbers(scene);
});

test("prime receiver retains the common lift, winding, fiber phase, and exact bounded axis relations", () => {
  const founded = Core.primeReceiverRead(prime, 193);
  const closed = Core.primeReceiverRead(prime, 195);
  const diagonal = Core.primeReceiverRead(prime, 53);
  assert.equal(founded.prime, true);
  assert.deepEqual(founded.pole_hits, []);
  assert.equal(closed.prime, false);
  assert.deepEqual(closed.pole_hits, [3, 5, 13]);
  assert.deepEqual(closed.path_coordinates.map((row) => row.axis), [2, 3]);
  assert.deepEqual(diagonal.path_coordinates.map(({ axis, quotient, direct }) => [axis, quotient, direct]), [
    [2, 26, 1],
    [3, 17, 2],
    [5, 10, 3],
    [7, 7, 4],
  ]);
  assert.deepEqual(
    [diagonal.founding_coordinate.axis, diagonal.founding_coordinate.quotient, diagonal.founding_coordinate.direct],
    [53, 1, 0]
  );
  assert.equal(diagonal.affine_relations[0].equation, "2n−1=105=3·5·7");
  assert.deepEqual(diagonal.latest_horizon, { axis: 7, boundary: 49, age: 4 });
  assert.equal(diagonal.lift_transitions[0].principal_phase_delta.text, "1/6");
  assert.equal(diagonal.lift_transitions[1].principal_phase_delta.text, "-1/15");
  assert.deepEqual(diagonal.chart_turns.map((row) => row.axis), [3]);
  assert.equal(diagonal.valuation.primitive_basis_vector, true);
  assert.deepEqual(diagonal.receiver_polynomials.s4.exponent_support, [0, 1, 4]);
  assert.equal(founded.receiver_species.s4.species, "identity-[1,1,1,1]");
  assert.equal(founded.receiver_species.cyclotomic.species, "four-cycle-[4]");
  const scene = Core.primeReceiverScene(prime, 193, 6);
  assert.equal(scene.primitives.some((item) => item.id === "prime:fiber:193"), false);
  assert.equal(scene.primitives.some((item) => item.id === "prime:incidence:193"), false);
  assert.ok(scene.primitives.some((item) => item.id === "prime:founding:193"));
  assert.ok(scene.primitives.some((item) => item.id === "prime:common-lift-base"));
  assert.equal(scene.primitives.some((item) => item.id.startsWith("prime:transition:")), false);
  assert.ok(scene.primitives.some((item) => item.id.startsWith("prime:transition-pin:")));
  assert.equal(scene.primitives.some((item) => item.id.startsWith("prime:leader:")), false);
  assert.equal(scene.metadata.neighbor_points_are_unjoined, true);
  assert.equal(scene.analysis.schema, Core.SCHEMAS.primeObserver);
  assertNoFractionalNumbers(scene.analysis);
});

test("prime succession is an exact cyclic string with a separately declared conjugate sheet", () => {
  const receipt = Core.primeAnalyticalReceipt(prime, 53, 12);
  const string = receipt.succession_strings.find((row) => row.axis === 7);
  assert.deepEqual(string.direct.filter((row) => row.discriminant).map((row) => row.value), [42, 49, 56, 63]);
  assert.equal(string.direct[0].phase_id, `phase:7:${string.direct[0].residue}`);
  assert.equal(string.conjugate[0].source_residue, string.direct[0].residue);
  assert.equal(string.conjugate[0].hand, -1);
  assert.ok(receipt.constants.pi.arms.one_fifth.terms.length > 1);
  assert.ok(receipt.log_basis.every((row) => row.series.components.log_two.terms.length === 8));
  const scene = Core.primeSuccessionScene(prime, 53, 12, 7);
  assert.equal(scene.metadata.centerline_is_second_strand, false);
  assert.deepEqual(scene.metadata.winding_crossings, [42, 49, 56, 63]);
  assertNoFractionalNumbers(scene.analysis);
});

test("retained rational series carry their terms and enclose without floating constants", () => {
  const pi = Exact.machinPi(8);
  const lower = exactFromRead(pi.enclosure.lower);
  const upper = exactFromRead(pi.enclosure.upper);
  assert.equal(Exact.compare(lower, Exact.ratio(314159n, 100000n)) < 0, false);
  assert.equal(Exact.compare(upper, Exact.ratio(314160n, 100000n)) < 0, true);
  const quarter = Exact.cyclotomicPhase(4, 1, 8, pi);
  assert.equal(quarter.real.lower.ratio, "0");
  assert.equal(quarter.real.upper.ratio, "0");
  assert.equal(quarter.imaginary.lower.ratio, "1");
  assert.equal(quarter.imaginary.upper.ratio, "1");
  const halfExp = Exact.expSeries(Exact.ratio(1n, 2n), 8);
  assert.equal(halfExp.terms.length, 8);
  assert.ok(halfExp.remainder_bound.ratio.includes("/"));
});

test("Zeta rebase preserves the exact cylinder while retaining ordered amplitude paths", () => {
  const scene = Core.zetaRebaseScene(prime, 1, 0);
  assert.equal(scene.metadata.equal, true);
  assert.equal(scene.metadata.path_order_preserved, true);
  assert.equal(scene.metadata.original_probability, scene.metadata.returned_probability);
  assert.ok(scene.primitives.some((item) => item.id === "zeta:path:0"));
  assert.ok(scene.primitives.some((item) => item.id === "zeta:path:1"));
  assert.equal(scene.analysis.datasets.phase_series_terms.length, 8);
  assertNoFractionalNumbers(scene);
});

test("Zeta scale-turn receipt retains prime powers, Gaussian series, and reciprocal sheets", () => {
  const receipt = Core.zetaAnalyticalReceipt(explicit, zeros, 0, 0, "1/8");
  assert.equal(receipt.prime_power_sites.length, 82);
  assert.equal(receipt.character_sheets.length, 4);
  assert.equal(receipt.character_series.length, 32);
  assert.equal(receipt.character_sheets.every((row) => row.unitary === false), true);
  assert.equal(receipt.listed_zero_field.samples.length, 81);
  assert.equal(receipt.listed_zero_field.samples.filter((row) => row.singular).length, 1);
  assert.ok(receipt.prime_power_sites.every((row) => row.amplitude_squared.ratio === `1/${row.value}` || row.value === 1));
  assertNoFractionalNumbers(receipt);
  const scene = Core.zetaSeriesScene(explicit, zeros, 0, 0, "0");
  assert.equal(scene.metadata.unitary, true);
  assert.ok(scene.primitives.some((item) => item.id === "zeta-series:sheet:direct"));
  assert.ok(scene.primitives.some((item) => item.id.startsWith("zeta-series:prime-power:")));
});

test("critical receiver uses rational Cayley geometry and exact residual endpoints", () => {
  assert.equal(zeros.length, 64);
  const scene = Core.criticalSmithFieldScene(zeros, explicit, 0, 0, "0");
  assert.equal(scene.metadata.critical_seam, "epsilon=0 maps exactly to the equator");
  assert.match(scene.metadata.field_status, /not the completed Xi field/);
  assert.match(scene.metadata.construction_boundary, /Weil\/Li positivity/);
  assert.ok(scene.primitives.some((item) => item.id === "critical:zero:1"));
  assert.ok(scene.primitives.some((item) => item.id === "critical:unitary-equator"));
  assert.ok(scene.primitives.some((item) => item.id === "critical:selected-normal-sheet"));
  assert.equal(scene.analysis.datasets.selected_normal_sheet.length, 9);
  assert.ok(scene.primitives.some((item) => item.id.startsWith("critical:leader:")));
  assertNoFractionalNumbers(scene.analysis);
  const residual = Core.criticalResidualIntervalScene(zeros, explicit, 0, 0);
  assert.equal(residual.metadata.midpoint_used, false);
  assert.equal(residual.metadata.source_endpoints_imported_as_exact_ratios, true);
  assert.ok(residual.primitives.some((item) => item.id === "critical-residual:interval:64"));
  assertNoFractionalNumbers(residual);
});

test("every analytical projection keeps exact rows and integer chart coordinates", () => {
  const smith = read("observations/smith-line-world-01/results/line.json");
  const scenes = [
    Core.primeReceiverScene(prime, 53, 12),
    Core.primeSuccessionScene(prime, 53, 12, 7),
    Core.wheelScene(prime, 3),
    Core.zetaRebaseScene(prime, 1, 0),
    Core.zetaSeriesScene(explicit, zeros, 0, 0, "1/8"),
    Core.criticalSmithFieldScene(zeros, explicit, 0, 0, "0"),
    Core.criticalResidualIntervalScene(zeros, explicit, 0, 0),
    Core.smithScene(smith, 4, "primary"),
  ];
  for (const scene of scenes) {
    assertNoFractionalNumbers(scene, scene.kind);
    assert.doesNotThrow(() => JSON.stringify(scene.analysis || scene.metadata));
  }
  const source = ["observatory-core.js", "exact-series.js"].map((file) => fs.readFileSync(path.join(__dirname, file), "utf8")).join("\n");
  assert.doesNotMatch(source, /Math\.(?:PI|sin|cos|tan|log|log10|exp|sqrt|hypot)/);
  assert.doesNotMatch(source, /(?:parseFloat|Number)\s*\(/);
});

test("transport geometry is a deterministic read of the exact word and state", () => {
  const run = Core.indexRuns(analysis).get("difference");
  const edge = Core.edgeOf(run, 2);
  const forward = read(edge === Core.edgeOf(run, 1) ? edge.journal.path : Core.edgeOf(run, 1).journal.path);
  const worldState = read(edge.world_after.path);
  assert.equal(Core.validateJournal(forward), true);
  assert.equal(Core.validateWorld(worldState), true);
  const input = { run, edge, forwardJournal: forward, worldState, side: "primary" };
  const first = Core.transportScene(input);
  const second = Core.transportScene(input);
  assert.deepEqual(Core.scenePrimitiveIds(first), Core.scenePrimitiveIds(second));
  assert.ok(first.primitives.some((item) => item.layer === "residual"));
  assert.ok(first.primitives.some((item) => item.layer === "contacts"));
  assert.equal(first.metadata.word_order, "w23");
  assertNoFractionalNumbers(first);
});

test("atlas rendering neither invents nor drops receipt cells", () => {
  const receipt = read("observations/circuit-atlas-01/results/changed.atlas.json");
  const scene = Core.atlasScene(receipt, "primary");
  const cellLines = scene.primitives.filter((item) => item.id.startsWith("atlas:primary:") && !item.id.endsWith(":origin"));
  assert.equal(cellLines.length, receipt.external.cells.length);
  assert.equal(scene.metadata.closed_loops, 0);
  assertNoFractionalNumbers(scene);
});

test("Smith rendering preserves the exact selected case in its receipt metadata", () => {
  const receipt = read("observations/smith-line-world-01/results/line.json");
  const scene = Core.smithScene(receipt, 4, "primary");
  assert.equal(scene.metadata.case, receipt.cases[4].label);
  assert.equal(scene.metadata.inverse_exact, true);
  assert.ok(scene.primitives.some((item) => item.id === "smith:load:orbit"));
});

test("comparison verdicts report factorial exactness without a score", () => {
  const comparison = Core.findComparison(analysis, "whole_hand_return");
  const fields = Core.comparisonFields(comparison);
  assert.equal(fields.length, 8);
  assert.ok(fields.some((field) => field.exact));
  assert.ok(fields.some((field) => !field.exact));
  assert.match(Core.comparisonVerdict(comparison).detail, /changed/);
});

test("artifact routing refuses traversal outside src/soma", () => {
  assert.equal(Core.somaRelativeUrl("observations/example.json"), "../../observations/example.json");
  assert.throws(() => Core.somaRelativeUrl("../outside.json"), /inside src\/soma/);
});
