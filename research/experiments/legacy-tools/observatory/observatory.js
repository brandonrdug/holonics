(function () {
  "use strict";

  const Core = window.SomaObservatoryCore;
  const Renderer = window.SomaSceneRenderer;
  const urls = {
    prime: "../../observations/bounded-polyglot-geometric-world-01/REPORT.json",
    explicit: "../../observations/interval-explicit-formula-world-01/build-01/EXPLICIT.json",
    zeros: "../../observations/interval-explicit-formula-world-01/LMFDB-FIRST-64-ZEROS.tsv",
    cellular: "../../observations/eros-linguistic-code-world-01/host-run-09/CONSTITUENTS.json",
  };

  const element = (id) => document.getElementById(id);
  const dom = {
    canvas: element("scene"),
    shell: element("viewport-shell"),
    status: element("load-status"),
    lamp: element("state-lamp"),
    schema: element("artifact-schema"),
    construction: element("construction-id"),
    comparison: element("comparison-name"),
    cut: element("cut-name"),
    primeControls: element("prime-controls"),
    zetaControls: element("zeta-controls"),
    criticalControls: element("critical-controls"),
    carrierControls: element("carrier-controls"),
    primeLens: element("prime-lens"),
    receiverControls: element("receiver-controls"),
    successionAxisControls: element("succession-axis-controls"),
    wheelControls: element("wheel-controls"),
    primeReceiver: element("prime-receiver"),
    primeReceiverNumber: element("prime-receiver-number"),
    primeSpan: element("prime-span"),
    primeSpanValue: element("prime-span-value"),
    primeAxis: element("prime-axis"),
    wheelStep: element("wheel-step"),
    zetaLens: element("zeta-lens"),
    zetaSeriesControls: element("zeta-series-controls"),
    zetaRebaseControls: element("zeta-rebase-controls"),
    zetaZero: element("zeta-zero"),
    zetaSample: element("zeta-sample"),
    zetaEpsilon: element("zeta-epsilon"),
    zetaCylinder: element("zeta-cylinder"),
    zetaPhase: element("zeta-phase"),
    criticalLens: element("critical-lens"),
    criticalZero: element("critical-zero"),
    explicitSample: element("explicit-sample"),
    criticalEpsilon: element("critical-epsilon"),
    carrierCut: element("carrier-cut"),
    carrierConstituent: element("carrier-constituent"),
    carrierBoundary: element("carrier-boundary"),
    carrierPath: element("carrier-path"),
    inspectConstituent: element("inspect-constituent"),
    receiverZoom: element("receiver-zoom"),
    resetView: element("reset-view"),
    fieldKicker: element("field-kicker"),
    fieldTitle: element("field-title"),
    primaryLegend: element("primary-legend"),
    siblingLegend: element("sibling-legend"),
    rideLegend: element("ride-legend"),
    foundLegend: element("found-legend"),
    leftLabel: element("left-viewport-label"),
    rightLabel: element("right-viewport-label"),
    projectionLabel: element("projection-label"),
    projectionNotice: element("projection-notice"),
    axisX: element("axis-x"),
    axisY: element("axis-y"),
    axisZ: element("axis-z"),
    verdict: element("comparison-verdict"),
    detail: element("comparison-detail"),
    invariants: element("invariant-strip"),
    gaugeRoot: element("gauge-root"),
    gaugeEmbedding: element("gauge-embedding"),
    gaugeMetric: element("gauge-metric"),
    gaugeIntrinsic: element("gauge-intrinsic"),
    gaugeSelected: element("gauge-selected"),
    gaugePresented: element("gauge-presented"),
    selectionTitle: element("selection-title"),
    selectionKind: element("selection-kind"),
    exactFields: element("exact-fields"),
    rawJson: element("raw-json"),
    clearSelection: element("clear-selection"),
    copyRecord: element("copy-record"),
    reportFile: element("report-file"),
    lifecycleTitle: element("lifecycle-title"),
    analysisExtent: element("analysis-extent"),
    analysisDataset: element("analysis-dataset"),
    analysisTableHead: element("analysis-table-head"),
    analysisTableBody: element("analysis-table-body"),
    exportAnalysis: element("export-analysis"),
  };

  const state = {
    prime: null,
    explicit: null,
    zeros: null,
    cellular: null,
    view: "prime",
    primeLens: "receiver",
    primeAxis: null,
    receiver: 193,
    span: 6,
    wheelStep: 3,
    zetaCylinder: 0,
    zetaPhase: 0,
    zetaLens: "series",
    zetaZero: 0,
    zetaSample: 0,
    zetaEpsilon: "0",
    criticalLens: "field",
    criticalZero: 0,
    explicitSample: 0,
    criticalEpsilon: "0",
    carrierCut: 1,
    carrierConstituent: 0,
    carrierBoundary: 0,
    carrierPath: 0,
    zoom: 100,
    layers: new Set(["sheet", "transport", "frames", "residual", "contacts", "labels"]),
    scene: null,
    selection: null,
    carrierLoading: null,
    analysisReceipt: null,
    analysisDataset: null,
    lifecycleRows: [],
  };

  const renderer = new Renderer(dom.canvas);

  function setStatus(message, status) {
    dom.status.textContent = message;
    dom.lamp.dataset.state = status || "loading";
  }

  async function fetchJson(url, validator) {
    const response = await fetch(url, { cache: "no-store" });
    if (!response.ok) throw new Error(`${response.status} while receiving ${url}`);
    const value = await response.json();
    if (validator) validator(value);
    return value;
  }

  async function fetchText(url) {
    const response = await fetch(url, { cache: "no-store" });
    if (!response.ok) throw new Error(`${response.status} while receiving ${url}`);
    return response.text();
  }

  function option(value, label) {
    const item = document.createElement("option");
    item.value = String(value);
    item.textContent = label;
    return item;
  }

  function setOptions(select, entries, selected) {
    select.replaceChildren(...entries.map(([value, label]) => option(value, label)));
    select.value = String(selected);
  }

  function clampInteger(value, low, high) {
    const source = /^[-+]?\d+$/.test(String(value)) ? BigInt(String(value)) : BigInt(low);
    const bounded = source < BigInt(low) ? BigInt(low) : source > BigInt(high) ? BigInt(high) : source;
    return parseInt(bounded.toString(), 10);
  }

  function compactValue(value) {
    if (value === null) return "null";
    if (value === undefined) return "absent";
    if (["string", "number", "boolean"].includes(typeof value)) return String(value);
    const encoded = JSON.stringify(value);
    return encoded.length > 180 ? `${encoded.slice(0, 176)}…` : encoded;
  }

  function humanKey(value) {
    return Core.humanize(String(value).replaceAll("_", " "));
  }

  function primitiveTitle(item) {
    const row = item.metadata || {};
    if (row.equation !== undefined) return row.equation;
    if (row.common_lift_identity !== undefined) return `Common lift · ${row.ordered_event}`;
    if (row.vertex_kind !== undefined && row.axis !== undefined) return `${row.vertex_kind} · p=${row.axis}`;
    if (row.candidate !== undefined) return `Integer ${row.candidate}`;
    if (row.prime_axis !== undefined) return `Prime axis ${row.prime_axis}`;
    if (row.axis !== undefined) return `Residue axis ${row.axis}`;
    if (row.zero !== undefined) return `Zeta zero ${row.zero}`;
    if (row.zero_prefix !== undefined) return `${row.zero_prefix} retained zero modes`;
    if (row.lifted_residue !== undefined) return `Lifted residue ${row.lifted_residue}`;
    if (row.step?.ordinal !== undefined) return `Path step ${row.step.ordinal + 1}`;
    return humanKey(item.id.split(":").slice(-2).join(" "));
  }

  function showRecord(title, kind, record) {
    state.selection = record;
    dom.selectionTitle.textContent = title;
    dom.selectionKind.textContent = kind;
    const entries = Object.entries(record || {});
    dom.exactFields.replaceChildren(...entries.slice(0, 18).map(([key, value]) => {
      const row = document.createElement("div");
      const term = document.createElement("dt");
      const description = document.createElement("dd");
      term.textContent = humanKey(key);
      description.textContent = compactValue(value);
      row.append(term, description);
      return row;
    }));
    dom.rawJson.textContent = JSON.stringify(record, null, 2);
    dom.clearSelection.disabled = false;
  }

  function showSceneSummary() {
    if (!state.scene) return;
    state.selection = null;
    showRecord("Receiver summary", "Observer declaration", state.scene.metadata);
    state.selection = null;
    dom.clearSelection.disabled = true;
  }

  function invariantCard(label, value, stateName) {
    const card = document.createElement("div");
    card.className = `invariant ${stateName ? `is-${stateName}` : ""}`.trim();
    const heading = document.createElement("b");
    const content = document.createElement("span");
    heading.textContent = label;
    content.textContent = value;
    card.append(heading, content);
    return card;
  }

  function setInvariants(rows) {
    dom.invariants.replaceChildren(...rows.map((row) => invariantCard(row[0], row[1], row[2])));
  }

  function lifecycleCard(number, title, detail, active, record) {
    const button = document.createElement("button");
    button.className = `edge-step${active ? " is-active" : ""}`;
    button.type = "button";
    const ordinal = document.createElement("span");
    ordinal.className = "edge-number";
    ordinal.textContent = String(number).padStart(2, "0");
    const copy = document.createElement("span");
    copy.className = "edge-copy";
    const strong = document.createElement("strong");
    const small = document.createElement("span");
    strong.textContent = title;
    small.textContent = detail;
    copy.append(strong, small);
    button.append(ordinal, copy);
    button.addEventListener("click", () => showRecord(title, "Relation cut", record || { title, detail }));
    return button;
  }

  function setLifecycle(title, summary, rows) {
    state.lifecycleRows = rows.map((row, ordinal) => ({
      ordinal: ordinal + 1,
      title: row.title,
      detail: row.detail,
      active: Boolean(row.active),
      record: row.record || null,
    }));
    state.lifecycleTitle = title;
    state.lifecycleSummary = summary;
  }

  function renderAnalysisTable() {
    const receipt = state.analysisReceipt;
    const datasets = receipt?.datasets || {};
    const rows = datasets[state.analysisDataset] || [];
    const columns = [];
    const seen = new Set();
    for (const row of rows) {
      for (const key of Object.keys(row || {})) {
        if (!seen.has(key)) {
          seen.add(key);
          columns.push(key);
        }
      }
    }
    const headerRow = document.createElement("tr");
    for (const column of columns) {
      const heading = document.createElement("th");
      heading.scope = "col";
      heading.textContent = humanKey(column);
      headerRow.append(heading);
    }
    dom.analysisTableHead.replaceChildren(headerRow);
    dom.analysisTableBody.replaceChildren(...rows.map((row, ordinal) => {
      const tableRow = document.createElement("tr");
      tableRow.tabIndex = 0;
      tableRow.title = "Inspect exact row";
      for (const column of columns) {
        const cell = document.createElement("td");
        cell.textContent = compactValue(row[column]);
        tableRow.append(cell);
      }
      const inspect = () => showRecord(`${humanKey(state.analysisDataset)} · row ${ordinal + 1}`, "Analytical receipt row", row);
      tableRow.addEventListener("click", inspect);
      tableRow.addEventListener("keydown", (event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          inspect();
        }
      });
      return tableRow;
    }));
    dom.analysisExtent.textContent = `${rows.length} rows · ${columns.length} fields`;
  }

  function setAnalysis(receipt) {
    const fallback = {
      schema: "soma-observer-scene-read-v1",
      observer_only: true,
      datasets: {
        scene_summary: state.scene ? [state.scene.metadata] : [],
        lawful_path: state.lifecycleRows,
      },
    };
    state.analysisReceipt = receipt || fallback;
    const datasets = { ...(state.analysisReceipt.datasets || {}) };
    if (!Object.hasOwn(datasets, "lawful_path")) datasets.lawful_path = state.lifecycleRows;
    state.analysisReceipt = { ...state.analysisReceipt, datasets };
    const entries = Object.entries(datasets).filter(([, rows]) => Array.isArray(rows)).map(([key, rows]) => [key, `${humanKey(key)} · ${rows.length}`]);
    const selected = entries.some(([key]) => key === state.analysisDataset) ? state.analysisDataset : entries[0]?.[0] || "lawful_path";
    state.analysisDataset = selected;
    setOptions(dom.analysisDataset, entries.length ? entries : [["lawful_path", "Lawful path · 0"]], selected);
    dom.lifecycleTitle.textContent = `${humanKey(selected)} · exact data`;
    renderAnalysisTable();
  }

  function fixedCamera(scene) {
    const declared = scene?.camera || {};
    return {
      mode: "integer-axonometric",
      distance: declared.distance ?? 12,
      target: declared.target || [0, 0, 0],
      projection: "orthographic",
      orthoScale: (declared.orthoScale || 10000) * 100 / state.zoom,
    };
  }

  function filteredScene(scene) {
    return { ...scene, primitives: scene.primitives.filter((item) => state.layers.has(item.layer)) };
  }

  function render() {
    if (!state.scene) return;
    const bounds = dom.canvas.getBoundingClientRect();
    const scene = filteredScene(state.scene);
    const camera = fixedCamera(scene);
    renderer.render([{
      scene,
      viewport: { x: 0, y: 0, width: bounds.width, height: bounds.height },
      camera,
    }], camera);
    dom.gaugeSelected.textContent = String(renderer.lastStats.selected);
    dom.gaugePresented.textContent = String(renderer.lastStats.presented);
  }

  function setCommon(context) {
    dom.construction.textContent = context.world;
    dom.comparison.textContent = context.receiver;
    dom.cut.textContent = context.cut;
    dom.fieldKicker.textContent = context.kicker;
    dom.fieldTitle.textContent = context.title;
    dom.leftLabel.textContent = context.leftLabel;
    dom.rightLabel.textContent = context.rightLabel;
    dom.projectionLabel.textContent = context.projectionLabel || "Declared receiver";
    dom.projectionNotice.textContent = context.projectionNotice;
    dom.axisX.textContent = context.axisX;
    dom.axisY.textContent = context.axisY;
    dom.axisZ.textContent = context.axisZ;
    dom.verdict.textContent = context.verdict;
    dom.detail.textContent = context.detail;
    dom.gaugeRoot.textContent = context.root;
    dom.gaugeEmbedding.textContent = context.coordinates;
    dom.gaugeMetric.textContent = context.metric;
    dom.gaugeIntrinsic.textContent = context.intrinsic;
    dom.primaryLegend.textContent = context.legends[0];
    dom.siblingLegend.textContent = context.legends[1];
    dom.rideLegend.textContent = context.legends[2];
    dom.foundLegend.textContent = context.legends[3];
    dom.schema.textContent = context.schema;
    setInvariants(context.invariants);
    setLifecycle(context.lifecycleTitle, context.lifecycleSummary, context.lifecycle);
    setAnalysis(context.scene.analysis || context.analysis || null);
  }

  function primeReceiverContext() {
    const scene = Core.primeReceiverScene(state.prime, state.receiver, state.span);
    const read = scene.metadata;
    const terminal = read.prime
      ? `${read.receiver} survives every prior residue pole and FOUNDS a new axis.`
      : `${read.receiver} closes on ${read.pole_hits.map((axis) => `mod ${axis}`).join(", ")}.`;
    const s4 = read.receiver_species.s4;
    const cyclotomic = read.receiver_species.cyclotomic;
    const bestRelation = read.affine_relations[0] || null;
    const lifecycle = [
      { title: "LIFT", detail: `n=${read.receiver} held across every fiber`, record: { receiver: read.receiver, origin: 0, path_axis_order: read.path_axis_order } },
      ...read.path_coordinates.map((row) => {
        const chartTurn = read.chart_turns.find((turn) => turn.axis === row.axis) || null;
        return {
          title: row.axis_role === "FOUND_NEW_BASIS" ? `FOUND · p=${row.axis}` : row.direct === 0 ? `CLOSE · p=${row.axis}` : chartTurn ? `RIDE / CHART TURN · p=${row.axis}` : `RIDE · p=${row.axis}`,
          detail: `q=${row.quotient} · r=${row.direct}/${row.axis}${chartTurn ? " · Δθ reverses" : ""}`,
          active: row.direct === 0 || row.axis_role === "FOUND_NEW_BASIS" || Boolean(chartTurn),
          record: chartTurn ? { incidence: row, chart_turn: chartTurn } : row,
        };
      }),
      ...(read.founding_coordinate ? [{
        title: `FOUND · p=${read.receiver}`,
        detail: "transverse basis birth after the divisor-test section",
        active: true,
        record: scene.analysis.founding,
      }] : []),
      ...(bestRelation ? [{
        title: "CROSS-AXIS PIN",
        detail: bestRelation.equation,
        record: bestRelation,
      }] : []),
      {
        title: "VALUATION",
        detail: read.valuation.primitive_basis_vector ? `e_${read.receiver}` : read.factorization_text,
        active: true,
        record: read.valuation,
      },
    ];
    return {
      scene,
      world: "bounded arithmetic",
      receiver: `${read.receiver} · common lifted integer`,
      cut: `${read.path_axis_order.length} carried incidences · ${read.chart_rank} fibers`,
      kicker: "Exact cyclotomic axis section",
      title: "One integer received across distinct prime fibers",
      leftLabel: `n=${read.receiver} · ordered axis section`,
      rightLabel: `rank ${read.chart_rank} · σ=${read.zeta_sigma}`,
      projectionNotice: "The base is divisor-test ordinal. Each fiber is the exact cyclotomic p-gon; the FOUNDing is transverse. Rational series enclosures survive behind every disposable integer-pixel mark.",
      axisX: "test ordinal",
      axisY: "Re ζₚʳ",
      axisZ: "Im ζₚʳ",
      verdict: terminal,
      detail: bestRelation ? `Strongest bounded cross-axis closure: ${bestRelation.equation}. Straight transition segments encode only the declared test word.` : read.display_warning,
      root: `integer ${read.receiver}`,
      coordinates: "(p,q,r), n=qp+r · one cyclotomic atlas per p",
      metric: "formal ℓₚ basis with retained rational log series",
      intrinsic: "finite cyclic fibers · horizon and FOUND seams typed",
      legends: ["Selected incidence", "Affine axis product", "Neighbor prime sample", "Pole / new basis"],
      invariants: [
        ["arithmetic", read.prime ? "prime · FOUND" : read.factorization_text, read.prime ? "exact" : "changed"],
        ["digit face", `mod 10=${read.digit_phase.decimal_terminal_digit} · mod 30=${read.digit_phase.residue_mod_30}`, "exact"],
        ["axis product", bestRelation?.equation || "none in bounded search", bestRelation ? "exact" : "changed"],
        ["receivers", `${s4?.species || "x⁴+x+1 unsampled"} · ${cyclotomic?.species || "Φ₅ unsampled"}`, s4?.unramified === false || cyclotomic?.unramified === false ? "changed" : "exact"],
      ],
      lifecycleTitle: "One common lift",
      lifecycleSummary: "lift → ordered fiber incidences → exact cross-axis pin → valuation",
      lifecycle,
      schema: scene.analysis.schema,
    };
  }

  function primeSuccessionContext() {
    const scene = Core.primeSuccessionScene(state.prime, state.receiver, state.span, state.primeAxis);
    const row = scene.metadata;
    const crossings = row.winding_crossings;
    return {
      scene,
      world: "bounded arithmetic succession",
      receiver: `n=${row.receiver} · held axis p=${row.axis}`,
      cut: `${row.aperture.low}..${row.aperture.high} · C_${row.axis}`,
      kicker: "Ordered cyclotomic strings",
      title: "Succession sweeps one prime fiber",
      leftLabel: `direct · ζ_${row.axis}^r`,
      rightLabel: `conjugate · ζ_${row.axis}^(-r)`,
      projectionNotice: "Every mark is one integer event. Lines carry only consecutive source adjacency. Direct and conjugate sheets meet at exact zero-phase winding closures; the centerline generates the sweep and is not a second strand.",
      axisX: "integer t",
      axisY: "Re ζₚʳ",
      axisZ: "Im ζₚʳ",
      verdict: crossings.length ? `The two sheets share ${crossings.length} complete winding closures in this aperture: ${crossings.join(", ")}.` : "This aperture contains no complete winding closure.",
      detail: `Residue recurs every ${row.recurrence_period} integer events; quotient q records the completed turns rather than disappearing into an angle.`,
      root: `receiver ${row.receiver} on axis ${row.axis}`,
      coordinates: `(t,q_${row.axis},r_${row.axis},ζ_${row.axis}^r)`,
      metric: "source chronology × exact cyclotomic incidence",
      intrinsic: "discrete succession strings and declared conjugate dual",
      legends: ["Direct string", "Conjugate string", "Recurring phase", "Winding closure"],
      invariants: [
        ["axis", String(row.axis), "exact"],
        ["period", String(row.recurrence_period), "exact"],
        ["closures", String(crossings.length), "exact"],
        ["series terms", String(row.exact_series_terms), "exact"],
      ],
      lifecycleTitle: "One succession string",
      lifecycleSummary: "integer event → residue phase → recurrence or complete winding",
      lifecycle: [
        { title: "HOLD AXIS", detail: `p=${row.axis}`, record: row },
        { title: "SWEEP", detail: `${row.aperture.low}..${row.aperture.high}`, record: scene.analysis.succession_strings.find((item) => item.axis === row.axis) },
        { title: "CONJUGATE", detail: "ζₚʳ ↔ ζₚ⁻ʳ", record: { duality: row.duality } },
        { title: "CLOSE", detail: crossings.length ? crossings.join(", ") : "outside aperture", active: crossings.length > 0, record: { crossings } },
      ],
      schema: scene.analysis.schema,
    };
  }

  function wheelContext() {
    const scene = Core.wheelScene(state.prime, state.wheelStep);
    const row = scene.metadata;
    return {
      scene,
      world: "primorial residue world",
      receiver: `axis ${row.founded_axis}`,
      cut: `mod ${row.prior_modulus} → ${row.successor_modulus}`,
      kicker: "Restriction followed by rebase",
      title: "Primorial self-similarity",
      leftLabel: `prior wheel · mod ${row.prior_modulus}`,
      rightLabel: `successor wheel · mod ${row.successor_modulus}`,
      projectionNotice: "The recurrence is the exact map from each uncut lifted residue back to its prior residue—not visual resemblance between two drawings.",
      axisX: "residue",
      axisY: "zero",
      axisZ: "rebase",
      verdict: `Axis ${row.founded_axis} copies ${row.copies} sheets, cuts ${row.cuts}, and joins ${row.joined_survivors} survivors.`,
      detail: "This is the Mandelbrot/Julia relation used here: restriction plus a lawful change of coordinates into the same phase law.",
      root: `prior wheel ${row.prior_modulus}`,
      coordinates: "residue modulo primorial",
      metric: "declared wheel phase",
      intrinsic: "flat sheets · discriminant at cuts",
      legends: ["Prior residue", "Lifted copy", "Rebased survivor", "Cut at pole"],
      invariants: [
        ["COPY", String(row.copies), "exact"],
        ["CUT", String(row.cuts), "changed"],
        ["JOIN", String(row.joined_survivors), "exact"],
        ["new modulus", String(row.successor_modulus), "exact"],
      ],
      lifecycleTitle: "One phase transition",
      lifecycleSummary: "prior wheel → copy → pole test → joined successor",
      lifecycle: [
        { title: "RESTRICT", detail: `mod ${row.prior_modulus}`, record: row },
        { title: "COPY", detail: `${row.copies} lifts per survivor`, record: row },
        { title: "CUT", detail: `${row.cuts} hit axis ${row.founded_axis}`, record: row },
        { title: "JOIN", detail: `${row.joined_survivors} survive`, record: row },
        { title: "REBASE", detail: `mod ${row.successor_modulus}`, active: true, record: row },
      ],
      schema: scene.analysis.schema,
    };
  }

  function zetaRebaseContext() {
    const scene = Core.zetaRebaseScene(state.prime, state.zetaCylinder, state.zetaPhase);
    const row = scene.metadata;
    return {
      scene,
      world: "Zeta valuation field",
      receiver: `60 divides N · cylinder ${row.cylinder + 1}`,
      cut: `σ = ${row.sigma}`,
      kicker: "Holonic probability",
      title: "Condition, shift, and return",
      leftLabel: "ordered multiplication · endpoint 60",
      rightLabel: `amplitude ${row.amplitude_scale}`,
      projectionNotice: "Conditioning selects a recurrence region. Dividing by 60 rebases it to the original valuation cylinder; the complex hand retains path orientation.",
      axisX: "prime axis",
      axisY: "valuation",
      axisZ: "phase",
      verdict: row.equal ? "The conditioned valuation law returns exactly after division by 60." : "The selected cylinder does not return.",
      detail: "Probability is the receiver quotient of recurrence. It does not erase the ordered multiplication paths or the amplitude hand.",
      root: `valuation cylinder ${row.cylinder + 1}`,
      coordinates: `v₂,v₃,v₅,v₇ at σ=${row.sigma}`,
      metric: "formal information step σ·ℓₚ with retained log series",
      intrinsic: "product valuation lattice",
      legends: ["2·2·3·5", "5·3·2·2", "Rebased law", "Condition shift"],
      invariants: [
        ["before", row.original_probability, "exact"],
        ["after rebase", row.returned_probability, row.equal ? "exact" : "changed"],
        ["P(60|N)", row.divisibility_probability, "exact"],
        ["phase", row.phase, "changed"],
      ],
      lifecycleTitle: "One conditional recurrence",
      lifecycleSummary: "cylinder → condition → valuation shift → divide/rebase → amplitude",
      lifecycle: [
        { title: "CYLINDER", detail: row.original_probability, record: row },
        { title: "CONDITION", detail: "60 divides N", record: row },
        { title: "SHIFT", detail: "+(2,1,1,0)", record: row },
        { title: "REBASE", detail: row.returned_probability, active: true, record: row },
        { title: "HAND", detail: row.phase, record: row },
      ],
      schema: scene.analysis.schema,
    };
  }

  function zetaSeriesContext() {
    const scene = Core.zetaSeriesScene(state.explicit, state.zeros, state.zetaZero, state.zetaSample, state.zetaEpsilon);
    const row = scene.metadata;
    return {
      scene,
      world: "exact Zeta scale-turn receiver",
      receiver: `ρ${row.pivot_zero} · x₀=${row.receiver_pivot}`,
      cut: `ε=${row.epsilon.ratio} · ${row.prime_power_sites} prime powers`,
      kicker: "Retained complex-series coefficients",
      title: "Prime-power sites and reciprocal character sheets",
      leftLabel: `ρ${row.pivot_zero} · direct / conjugate`,
      rightLabel: row.unitary ? "ε=0 · pure turn" : `ε=${row.epsilon.ratio} · reciprocal amplitude sheets`,
      projectionNotice: "The upper strings are projective reads of exact Gaussian-rational series coefficients. The lower current is the exact prime-power event order. Magnitude, scale, and tails remain ratios and formal ℓₚ words in the receipt.",
      axisX: "series / event order",
      axisY: "projective real",
      axisZ: "projective imaginary",
      verdict: row.unitary ? "Receiver rebase is pure turn on the unitary seam." : "The reciprocal sheets carry opposed nonunitary amplitude directions.",
      detail: "No log, exponential, sine, cosine, zero ordinate, or residual interval is collapsed to a floating scalar.",
      root: `zero character ρ${row.pivot_zero}`,
      coordinates: "Gaussian-rational coefficient sequence over formal u=k·ℓₚ",
      metric: "retained rational log series and exact squared amplitude 1/pᵏ",
      intrinsic: "four typed direct/conjugate/reciprocal sheets",
      legends: ["Direct series", "Conjugate series", "Reciprocal series", "Reflected conjugate / higher power"],
      invariants: [
        ["unitary", row.unitary ? "yes" : "no", row.unitary ? "exact" : "changed"],
        ["prime powers", String(row.prime_power_sites), "exact"],
        ["sheets", String(row.character_sheets), "exact"],
        ["terms / sheet", String(row.series_terms_per_sheet), "exact"],
      ],
      lifecycleTitle: "One scale-turn character",
      lifecycleSummary: "prime power → formal log basis → Gaussian series → conjugate / reciprocal sheet",
      lifecycle: [
        { title: "PRIME POWER", detail: `${row.prime_power_sites} exact sites`, record: scene.analysis.prime_power_sites },
        { title: "LOG BASIS", detail: "k·ℓₚ", record: scene.analysis.prime_log_basis },
        { title: "SERIES", detail: `${row.series_terms_per_sheet} retained terms per sheet`, record: scene.analysis.character_series },
        { title: "REBASE", detail: row.unitary ? "pure turn" : "amplitude changes", active: true, record: scene.analysis.receiver_pivot },
      ],
      schema: scene.analysis.schema,
    };
  }

  function zetaContext() {
    return state.zetaLens === "rebase" ? zetaRebaseContext() : zetaSeriesContext();
  }

  function criticalContext() {
    const scene = state.criticalLens === "residual"
      ? Core.criticalResidualIntervalScene(state.zeros, state.explicit, state.criticalZero, state.explicitSample)
      : Core.criticalSmithFieldScene(state.zeros, state.explicit, state.criticalZero, state.explicitSample, state.criticalEpsilon);
    const row = scene.metadata;
    const field = state.criticalLens === "field";
    return {
      scene,
      world: field ? "rational completed-Zeta receiver" : "exact imported residual testimony",
      receiver: `ρ${row.pivot_zero} · ${field ? row.pivot_s : `x=${row.sample_x}`}`,
      cut: field ? `${row.field_samples} factored field samples` : `${row.residual_intervals} interval rows`,
      kicker: field ? "Rational Cayley / Smith field" : "Directed residual intervals",
      title: field ? "The unitary seam carries a factored zero field" : "Residual endpoints remain separate",
      leftLabel: field ? `${row.listed_zeros} conjugate zero pairs` : `x=${row.sample_x}`,
      rightLabel: field ? `ε=${row.epsilon.ratio}` : "no midpoint",
      projectionNotice: field
        ? "Cayley and stereographic placement are rational maps. Each leader is one nearest retained factor; the complete field remains a factored sum word in data rather than one scalar vector."
        : "Each vertical mark is an exact lower/upper ratio pair imported from directed interval testimony. The dashed center path is display-only and never substitutes for the endpoints.",
      axisX: field ? "Cayley real" : "zero prefix",
      axisY: field ? "Cayley imaginary" : "residual ratio",
      axisZ: field ? "normal hemisphere" : "interval extent",
      verdict: field
        ? "The critical seam maps exactly to the Smith equator; listed zeros occupy that seam as discrete vortices."
        : "Every residual remains an interval, with no midpoint or floating comparison admitted.",
      detail: row.construction_boundary,
      root: field ? `critical pivot ρ${row.pivot_zero}` : `explicit sample x=${row.sample_x}`,
      coordinates: field ? "rational Cayley quotient → rational stereographic sphere" : "exact decimal endpoints → BigInt ratios",
      metric: field ? "factored squared-distance field and rational phase leaders" : "directed interval order",
      intrinsic: field ? "unitary equator · reciprocal hemispheres · zero factors" : "bounded residual intervals",
      legends: field ? ["ε<0 sheet", "ε>0 sheet", "Unitary seam", "Zero / singular factor"] : ["Lower endpoint", "Upper endpoint", "Crosses zero", "Negative interval"],
      invariants: field ? [
        ["zeros", String(row.listed_zeros), "exact"],
        ["field rows", String(row.field_samples), "exact"],
        ["critical seam", "ε=0", "exact"],
        ["completed Xi", "open", "changed"],
      ] : [
        ["intervals", String(row.residual_intervals), "exact"],
        ["midpoint", "unused", "exact"],
        ["endpoint carrier", "BigInt ratios", "exact"],
        ["complete trace", "open", "changed"],
      ],
      lifecycleTitle: field ? "One centered receiver" : "One directed residual cut",
      lifecycleSummary: field ? "center → Cayley quotient → unitary equator → factored leaders" : "lower endpoint → upper endpoint → retained interval",
      lifecycle: field ? [
        { title: "CENTER", detail: "w=s−1/2", record: scene.analysis.pivot_zero },
        { title: "CAYLEY", detail: "(w−a)/(w+a)", record: { transform: row.cayley_transform } },
        { title: "FIELD", detail: `${row.field_samples} exact factored samples`, record: scene.analysis.listed_zero_field },
        { title: "UNITARY CLOSURE", detail: "complete trace / Weil-Li positivity", active: true, record: { construction_boundary: row.construction_boundary } },
      ] : [
        { title: "IMPORT", detail: "directed decimal endpoints", record: scene.analysis.precision_source },
        { title: "RATIO", detail: "no midpoint", record: scene.analysis.residuals },
        { title: "CLOSURE", detail: "complete trace remains open", active: true, record: { construction_boundary: row.construction_boundary } },
      ],
      schema: scene.analysis.schema,
    };
  }

  function selectedCarrier() {
    const cut = state.cellular.cuts[state.carrierCut];
    const constituent = cut?.constituents[state.carrierConstituent] || null;
    const boundary = constituent?.boundaries[state.carrierBoundary] || null;
    const path = boundary?.paths[state.carrierPath] || null;
    return { cut, constituent, boundary, path };
  }

  function carrierContext() {
    const scene = Core.cellularScene({
      report: state.cellular,
      cutIndex: state.carrierCut,
      constituentIndex: state.carrierConstituent,
      boundaryIndex: state.carrierBoundary,
      pathIndex: state.carrierPath,
      layers: state.layers,
    });
    const row = scene.metadata;
    const selected = selectedCarrier();
    const lifecycle = selected.constituent
      ? selected.constituent.boundaries.map((boundary) => ({
        title: boundary.transition,
        detail: `${boundary.paths.length} paths · ${boundary.paths.reduce((sum, path) => sum + path.steps.length, 0)} steps`,
        active: boundary.ordinal === state.carrierBoundary,
        record: boundary,
      }))
      : [{ title: "REST", detail: "no cellular constituent", active: true, record: row }];
    return {
      scene,
      world: "linguistic-code rest wire",
      receiver: selected.constituent ? `constituent ${selected.constituent.ordinal + 1}` : "no constituent",
      cut: selected.boundary ? `boundary ${selected.boundary.ordinal + 1} · path ${state.carrierPath + 1}` : "rest only",
      kicker: "Topology-only testimony",
      title: "One selected causal path",
      leftLabel: selected.cut?.label || "rest cut",
      rightLabel: selected.boundary?.transition || "no path",
      projectionLabel: "Material unavailable",
      projectionNotice: "The rest artifact retained exact topology but discarded the source inscription. This view cannot honestly infer what the relation was about.",
      axisX: "event order",
      axisY: "grain",
      axisZ: "carrier",
      verdict: "The selected rest path is topologically inspectable; its linguistic or coding utility is not established.",
      detail: "Whole-body counts remain exact testimony and are deliberately not drawn as an undifferentiated particle stack.",
      root: selected.cut?.label || "rest",
      coordinates: "selected path causal order",
      metric: "none supplied by source world",
      intrinsic: "exterior carrier topology only",
      legends: ["Selected path", "Sibling", "RIDE", "FOUND / exposed"],
      invariants: [
        ["whole cells", String(row.cells || 0), "exact"],
        ["path cells", String(row.rendered_path_cells || 0), "exact"],
        ["path steps", String(selected.path?.steps.length || 0), "exact"],
        ["meaning", "not retained", "changed"],
      ],
      lifecycleTitle: "Retained boundary sequence",
      lifecycleSummary: "exact topology; application subject unavailable",
      lifecycle,
      schema: state.cellular.schema,
    };
  }

  function currentContext() {
    if (state.view === "zeta") return zetaContext();
    if (state.view === "critical") return criticalContext();
    if (state.view === "carrier") return carrierContext();
    if (state.primeLens === "wheel") return wheelContext();
    if (state.primeLens === "succession") return primeSuccessionContext();
    return primeReceiverContext();
  }

  function refresh() {
    if (!state.prime) return;
    if ((state.view === "critical" || state.view === "zeta") && (!state.explicit || !state.zeros)) return;
    if (state.view === "carrier" && !state.cellular) {
      void ensureCarrier();
      return;
    }
    const context = currentContext();
    state.scene = context.scene;
    setCommon(context);
    showSceneSummary();
    render();
  }

  function updateControlVisibility() {
    dom.primeControls.hidden = state.view !== "prime";
    dom.zetaControls.hidden = state.view !== "zeta";
    dom.criticalControls.hidden = state.view !== "critical";
    dom.carrierControls.hidden = state.view !== "carrier";
    dom.receiverControls.hidden = state.primeLens === "wheel";
    dom.successionAxisControls.hidden = state.primeLens !== "succession";
    dom.wheelControls.hidden = state.primeLens !== "wheel";
    dom.zetaSeriesControls.hidden = state.zetaLens !== "series";
    dom.zetaRebaseControls.hidden = state.zetaLens !== "rebase";
    document.querySelectorAll(".mode-button").forEach((button) => button.classList.toggle("is-active", button.dataset.view === state.view));
  }

  async function ensureCarrier() {
    if (state.cellular) return state.cellular;
    if (state.carrierLoading) return state.carrierLoading;
    setStatus("Receiving topology-only carrier artifact", "loading");
    state.carrierLoading = fetchJson(urls.cellular, Core.validateCellular)
      .then((cellular) => {
        state.cellular = cellular;
        populateCarrierCut();
        setStatus("Exact carrier artifact received", "ready");
        if (state.view === "carrier") refresh();
        return cellular;
      })
      .catch((error) => {
        setStatus(error.message, "error");
        return null;
      })
      .finally(() => { state.carrierLoading = null; });
    return state.carrierLoading;
  }

  function populatePrimeControls() {
    setOptions(dom.wheelStep, state.prime.zero_relative.wheel_steps.map((row, at) => [at, `p=${row.founded_axis} · mod ${row.prior_modulus} → ${row.successor_modulus}`]), state.wheelStep);
    setOptions(dom.zetaCylinder, state.prime.zeta.cylinders.map((row, at) => [at, `#${at + 1} · v=(${row.exponents.join(",")}) · ${Core.formatRational(row.original)}`]), state.zetaCylinder);
    setOptions(dom.zetaPhase, state.prime.zeta.phase_lifts.map((row, at) => [at, `t=${row.t} · ${row.phase}`]), state.zetaPhase);
    populatePrimeAxes();
  }

  function populatePrimeAxes() {
    if (!state.prime) return;
    const axes = Core.primeReceiverRead(state.prime, state.receiver).axes;
    if (!axes.includes(state.primeAxis)) state.primeAxis = axes[axes.length - 1] || 2;
    setOptions(dom.primeAxis, axes.map((axis) => [axis, `p=${axis} · period ${axis}`]), state.primeAxis);
  }

  function populateCriticalControls() {
    setOptions(dom.criticalZero, state.zeros.map((row, at) => [at, `ρ${row.ordinal} · ${row.exact_ordinate}`]), state.criticalZero);
    setOptions(dom.explicitSample, state.explicit.samples.map((row, at) => [at, `x=${row.x} · floor ${row.floor}`]), state.explicitSample);
    setOptions(dom.zetaZero, state.zeros.map((row, at) => [at, `ρ${row.ordinal} · ${row.exact_ordinate}`]), state.zetaZero);
    setOptions(dom.zetaSample, state.explicit.samples.map((row, at) => [at, `x=${row.x} · floor ${row.floor}`]), state.zetaSample);
  }

  function populateCarrierCut() {
    setOptions(dom.carrierCut, state.cellular.cuts.map((cut, at) => [at, `${Core.humanize(cut.label)} · ${cut.constituents.length} constituents`]), state.carrierCut);
    populateCarrierConstituent();
  }

  function populateCarrierConstituent() {
    const cut = state.cellular.cuts[state.carrierCut];
    state.carrierConstituent = clampInteger(state.carrierConstituent, 0, Math.max(0, cut.constituents.length - 1));
    const entries = cut.constituents.length
      ? cut.constituents.map((item, at) => [at, Core.cellularConstituentLabel(item)])
      : [[0, "No cellular constituent"]];
    setOptions(dom.carrierConstituent, entries, state.carrierConstituent);
    dom.carrierConstituent.disabled = cut.constituents.length === 0;
    populateCarrierBoundary();
  }

  function populateCarrierBoundary() {
    const { constituent } = selectedCarrier();
    state.carrierBoundary = clampInteger(state.carrierBoundary, 0, Math.max(0, (constituent?.boundaries.length || 1) - 1));
    const entries = constituent
      ? constituent.boundaries.map((row, at) => [at, `#${at + 1} · ${row.transition} · ${row.paths.length} paths`])
      : [[0, "No boundary"]];
    setOptions(dom.carrierBoundary, entries, state.carrierBoundary);
    dom.carrierBoundary.disabled = !constituent;
    populateCarrierPath();
  }

  function populateCarrierPath() {
    const { boundary } = selectedCarrier();
    state.carrierPath = clampInteger(state.carrierPath, 0, Math.max(0, (boundary?.paths.length || 1) - 1));
    const entries = boundary
      ? boundary.paths.map((row, at) => [at, `#${at + 1} · ${row.steps.length} steps · ${row.transport.length} terms`])
      : [[0, "No path"]];
    setOptions(dom.carrierPath, entries, state.carrierPath);
    dom.carrierPath.disabled = !boundary;
  }

  function bind() {
    document.querySelectorAll(".mode-button").forEach((button) => button.addEventListener("click", () => {
      state.view = button.dataset.view;
      updateControlVisibility();
      refresh();
    }));
    dom.primeLens.addEventListener("change", () => {
      state.primeLens = dom.primeLens.value;
      updateControlVisibility();
      refresh();
    });
    const receiveInteger = (value) => {
      state.receiver = clampInteger(value, 2, state.prime?.zero_relative.succession_horizon || 509);
      dom.primeReceiver.value = String(state.receiver);
      dom.primeReceiverNumber.value = String(state.receiver);
      populatePrimeAxes();
      refresh();
    };
    dom.primeReceiver.addEventListener("input", () => receiveInteger(dom.primeReceiver.value));
    dom.primeReceiverNumber.addEventListener("change", () => receiveInteger(dom.primeReceiverNumber.value));
    dom.primeSpan.addEventListener("input", () => {
      state.span = clampInteger(dom.primeSpan.value, 1, 24);
      dom.primeSpanValue.textContent = `±${state.span}`;
      refresh();
    });
    dom.primeAxis.addEventListener("change", () => { state.primeAxis = clampInteger(dom.primeAxis.value, 2, 509); refresh(); });
    dom.wheelStep.addEventListener("change", () => { state.wheelStep = clampInteger(dom.wheelStep.value, 0, Math.max(0, state.prime.zero_relative.wheel_steps.length - 1)); refresh(); });
    dom.zetaLens.addEventListener("change", () => { state.zetaLens = dom.zetaLens.value; updateControlVisibility(); refresh(); });
    dom.zetaZero.addEventListener("change", () => { state.zetaZero = clampInteger(dom.zetaZero.value, 0, state.zeros.length - 1); refresh(); });
    dom.zetaSample.addEventListener("change", () => { state.zetaSample = clampInteger(dom.zetaSample.value, 0, state.explicit.samples.length - 1); refresh(); });
    dom.zetaEpsilon.addEventListener("change", () => { state.zetaEpsilon = dom.zetaEpsilon.value; refresh(); });
    dom.zetaCylinder.addEventListener("change", () => { state.zetaCylinder = clampInteger(dom.zetaCylinder.value, 0, state.prime.zeta.cylinders.length - 1); refresh(); });
    dom.zetaPhase.addEventListener("change", () => { state.zetaPhase = clampInteger(dom.zetaPhase.value, 0, state.prime.zeta.phase_lifts.length - 1); refresh(); });
    dom.criticalLens.addEventListener("change", () => { state.criticalLens = dom.criticalLens.value; refresh(); });
    dom.criticalZero.addEventListener("change", () => { state.criticalZero = clampInteger(dom.criticalZero.value, 0, state.zeros.length - 1); refresh(); });
    dom.explicitSample.addEventListener("change", () => { state.explicitSample = clampInteger(dom.explicitSample.value, 0, state.explicit.samples.length - 1); refresh(); });
    dom.criticalEpsilon.addEventListener("change", () => { state.criticalEpsilon = dom.criticalEpsilon.value; refresh(); });
    dom.carrierCut.addEventListener("change", () => {
      state.carrierCut = clampInteger(dom.carrierCut.value, 0, state.cellular.cuts.length - 1);
      state.carrierConstituent = 0;
      state.carrierBoundary = 0;
      state.carrierPath = 0;
      populateCarrierConstituent();
      refresh();
    });
    dom.carrierConstituent.addEventListener("change", () => {
      state.carrierConstituent = clampInteger(dom.carrierConstituent.value, 0, Math.max(0, selectedCarrier().cut.constituents.length - 1));
      state.carrierBoundary = 0;
      state.carrierPath = 0;
      populateCarrierBoundary();
      refresh();
    });
    dom.carrierBoundary.addEventListener("change", () => {
      state.carrierBoundary = clampInteger(dom.carrierBoundary.value, 0, Math.max(0, (selectedCarrier().constituent?.boundaries.length || 1) - 1));
      state.carrierPath = 0;
      populateCarrierPath();
      refresh();
    });
    dom.carrierPath.addEventListener("change", () => { state.carrierPath = clampInteger(dom.carrierPath.value, 0, Math.max(0, (selectedCarrier().boundary?.paths.length || 1) - 1)); refresh(); });
    dom.receiverZoom.addEventListener("input", () => { state.zoom = clampInteger(dom.receiverZoom.value, 70, 180); render(); });
    dom.resetView.addEventListener("click", () => {
      state.zoom = 100;
      dom.receiverZoom.value = "100";
      render();
    });
    document.querySelectorAll("[data-layer]").forEach((checkbox) => checkbox.addEventListener("change", () => {
      if (checkbox.checked) state.layers.add(checkbox.dataset.layer);
      else state.layers.delete(checkbox.dataset.layer);
      render();
    }));
    dom.canvas.addEventListener("click", (event) => {
      const hit = renderer.pick(event.clientX, event.clientY);
      if (hit) showRecord(primitiveTitle(hit.item), `${humanKey(hit.item.layer)} · ${humanKey(hit.item.kind)}`, hit.item.metadata || {});
    });
    dom.clearSelection.addEventListener("click", showSceneSummary);
    dom.inspectConstituent.addEventListener("click", () => {
      showRecord("Whole topology counts", "Carrier constituent · application material absent", state.scene.metadata);
    });
    dom.copyRecord.addEventListener("click", async () => {
      await navigator.clipboard.writeText(dom.rawJson.textContent);
      dom.copyRecord.textContent = "Copied";
      window.setTimeout(() => { dom.copyRecord.textContent = "Copy"; }, 900);
    });
    dom.analysisDataset.addEventListener("change", () => {
      state.analysisDataset = dom.analysisDataset.value;
      dom.lifecycleTitle.textContent = `${humanKey(state.analysisDataset)} · exact data`;
      renderAnalysisTable();
    });
    dom.exportAnalysis.addEventListener("click", () => {
      if (!state.analysisReceipt) return;
      const encoded = JSON.stringify(state.analysisReceipt, null, 2);
      const blob = new Blob([encoded], { type: "application/json" });
      const link = document.createElement("a");
      const url = URL.createObjectURL(blob);
      link.href = url;
      link.download = `${state.analysisReceipt.schema || "soma-observer-receipt"}-${state.analysisReceipt.receiver || state.analysisReceipt.pivot_zero?.ordinal || "cut"}.json`;
      link.click();
      URL.revokeObjectURL(url);
    });
    dom.reportFile.addEventListener("change", async () => {
      const [file] = dom.reportFile.files;
      if (!file) return;
      try {
        const value = JSON.parse(await file.text());
        if (value.schema === Core.SCHEMAS.prime) {
          Core.validatePrime(value);
          state.prime = value;
          populatePrimeControls();
          state.view = "prime";
        } else if (value.schema === Core.SCHEMAS.explicit) {
          Core.validateExplicit(value);
          state.explicit = value;
          populateCriticalControls();
          state.view = "critical";
        } else if (value.schema === Core.SCHEMAS.cellular) {
          Core.validateCellular(value);
          state.cellular = value;
          populateCarrierCut();
          state.view = "carrier";
        } else {
          throw new Error(`unsupported observer schema ${value.schema || "absent"}`);
        }
        updateControlVisibility();
        setStatus(`Received ${file.name}`, "ready");
        refresh();
      } catch (error) {
        setStatus(error.message, "error");
      } finally {
        dom.reportFile.value = "";
      }
    });
    window.addEventListener("resize", render);
  }

  async function initialize() {
    bind();
    updateControlVisibility();
    setStatus("Receiving exact artifacts", "loading");
    try {
      const [prime, explicit, zerosText] = await Promise.all([
        fetchJson(urls.prime, Core.validatePrime),
        fetchJson(urls.explicit, Core.validateExplicit),
        fetchText(urls.zeros),
      ]);
      state.prime = prime;
      state.explicit = explicit;
      state.zeros = Core.parseZetaZeros(zerosText);
      populatePrimeControls();
      populateCriticalControls();
      setStatus("Exact prime, Zeta, and RH artifacts received", "ready");
      refresh();
    } catch (error) {
      console.error(error);
      setStatus(error.message, "error");
    }
  }

  initialize();
})();
