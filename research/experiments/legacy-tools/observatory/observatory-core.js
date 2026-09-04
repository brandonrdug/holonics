(function (root, factory) {
  const exact = typeof module === "object" && module.exports
    ? require("./exact-series.js")
    : root.SomaExactSeries;
  const api = factory(exact);
  if (typeof module === "object" && module.exports) module.exports = api;
  root.SomaObservatoryCore = api;
})(typeof globalThis !== "undefined" ? globalThis : this, function (Exact) {
  "use strict";

  if (!Exact) throw new Error("the exact rational-series carrier is absent");

  const SCHEMAS = Object.freeze({
    analysis: "soma-transport-foil-observer-report-v1",
    journal: "soma-transport-foil-journal-v1",
    world: "soma-transport-foil-world-v1",
    smith: "soma-transmission-line-receipt-v1",
    atlas: "soma-causal-volume-receipt-v1",
    cellular: "eros.live-constituent.observer.v1",
    prime: "soma-bounded-polyglot-geometric-world-report-v1",
    explicit: "soma-interval-explicit-formula-analysis-v1",
    primeObserver: "soma-prime-scale-turn-observer-v1",
    zetaObserver: "soma-zeta-scale-turn-observer-v1",
  });

  const EDGE_NAMES = Object.freeze({
    1: "forward word",
    2: "residual return",
    3: "fixed later probe",
    4: "probe return",
  });
  const validatedCellularReports = new WeakSet();

  function invariant(condition, message) {
    if (!condition) throw new Error(message);
  }

  function validateAnalysis(value) {
    invariant(value && value.schema === SCHEMAS.analysis, `expected ${SCHEMAS.analysis}`);
    invariant(Array.isArray(value.runs) && value.runs.length > 1, "observer report requires plural runs");
    invariant(Array.isArray(value.comparisons), "observer report comparisons are absent");
    const ids = new Set();
    for (const run of value.runs) {
      invariant(typeof run.id === "string" && run.id.length > 0, "run id is absent");
      invariant(!ids.has(run.id), `duplicate run ${run.id}`);
      ids.add(run.id);
      invariant(Array.isArray(run.edges) && run.edges.length > 0, `run ${run.id} has no edges`);
      for (const edge of run.edges) {
        invariant(Number.isInteger(edge.edge) && edge.edge > 0, `run ${run.id} has malformed edge`);
        invariant(edge.journal && typeof edge.journal.path === "string", `run ${run.id} edge ${edge.edge} journal is absent`);
        invariant(edge.world_after && typeof edge.world_after.path === "string", `run ${run.id} edge ${edge.edge} world state is absent`);
      }
    }
    for (const comparison of value.comparisons) {
      invariant(ids.has(comparison.left.run), `comparison ${comparison.id} has unknown left run`);
      invariant(ids.has(comparison.right.run), `comparison ${comparison.id} has unknown right run`);
    }
    return true;
  }

  function validateJournal(value) {
    invariant(value && value.schema === SCHEMAS.journal, `expected ${SCHEMAS.journal}`);
    invariant(Number.isInteger(value.edge), "journal edge is absent");
    invariant(value.observer && value.observer.observer_only === true, "journal observer provenance is absent");
    return true;
  }

  function validateWorld(value) {
    invariant(value && value.schema === SCHEMAS.world, `expected ${SCHEMAS.world}`);
    invariant(Number.isInteger(value.edge), "world edge is absent");
    invariant(Array.isArray(value.passages), "world passages are absent");
    return true;
  }

  function validateSmith(value) {
    invariant(value && value.schema === SCHEMAS.smith, `expected ${SCHEMAS.smith}`);
    invariant(Array.isArray(value.cases) && value.cases.length === value.lines, "Smith line cases disagree with extent");
    return true;
  }

  function validateAtlas(value) {
    invariant(value && value.schema === SCHEMAS.atlas, `expected ${SCHEMAS.atlas}`);
    invariant(Array.isArray(value.first_person) && value.first_person.length === value.relations, "atlas first-person relations disagree with extent");
    invariant(value.external && Array.isArray(value.external.cells), "atlas external cells are absent");
    invariant(value.external.cells.length === value.response_volumes + value.open_transits, "atlas cell extent disagrees with response and transit counts");
    return true;
  }

  function validateCellular(value) {
    invariant(value && value.schema === SCHEMAS.cellular, `expected ${SCHEMAS.cellular}`);
    invariant(value.observer_only === true, "cellular report is not marked observer-only");
    invariant(Array.isArray(value.cuts) && value.cuts.length > 0, "cellular report has no rest cuts");
    const labels = new Set();
    for (const cut of value.cuts) {
      invariant(typeof cut.label === "string" && cut.label.length > 0, "cellular rest cut label is absent");
      invariant(!labels.has(cut.label), `duplicate cellular rest cut ${cut.label}`);
      labels.add(cut.label);
      invariant(Number.isInteger(cut.standing_rank) && cut.standing_rank >= 0, `cut ${cut.label} rank is malformed`);
      invariant(Array.isArray(cut.scalar_standing), `cut ${cut.label} scalar Standing is absent`);
      invariant(Array.isArray(cut.lineages), `cut ${cut.label} live lineages are absent`);
      invariant(Array.isArray(cut.constituents), `cut ${cut.label} constituents are absent`);
      invariant(cut.memory && cut.memory.standing_cells === cut.scalar_standing.length, `cut ${cut.label} scalar extent disagrees`);
      invariant(cut.memory.standing_constituents === cut.constituents.length, `cut ${cut.label} constituent extent disagrees`);
      for (const [constituentOrdinal, constituent] of cut.constituents.entries()) {
        invariant(constituent.ordinal === constituentOrdinal, `cut ${cut.label} constituent order is malformed`);
        invariant(typeof constituent.fingerprint === "string" && constituent.fingerprint.length === 64, `cut ${cut.label} constituent fingerprint is malformed`);
        invariant(Number.isInteger(constituent.source_wire_version) && constituent.source_wire_version >= 3, `cut ${cut.label} constituent wire version is malformed`);
        invariant(Number.isInteger(constituent.grain) && constituent.grain > 0, `cut ${cut.label} constituent grain is malformed`);
        invariant(Number.isInteger(constituent.axis_count) && constituent.axis_count > 0, `cut ${cut.label} constituent axis extent is malformed`);
        invariant(Array.isArray(constituent.cells) && constituent.cells.length > 0, `cut ${cut.label} constituent cells are absent`);
        invariant(Array.isArray(constituent.incidences), `cut ${cut.label} constituent incidence is absent`);
        invariant(Array.isArray(constituent.pins), `cut ${cut.label} constituent pins are absent`);
        invariant(Array.isArray(constituent.boundaries) && constituent.boundaries.length > 0, `cut ${cut.label} constituent boundaries are absent`);
        invariant(Array.isArray(constituent.exposed), `cut ${cut.label} constituent exposed residual is absent`);
        for (const [cellOrdinal, cell] of constituent.cells.entries()) {
          invariant(cell.ordinal === cellOrdinal, `cut ${cut.label} cell order is malformed`);
        }
        for (const [incidenceOrdinal, incidence] of constituent.incidences.entries()) {
          invariant(incidence.ordinal === incidenceOrdinal, `cut ${cut.label} incidence order is malformed`);
          invariant(incidence.from >= 0 && incidence.from < constituent.cells.length, `cut ${cut.label} incidence source is absent`);
          invariant(incidence.to >= 0 && incidence.to < constituent.cells.length, `cut ${cut.label} incidence target is absent`);
          invariant(incidence.pin >= 0 && incidence.pin < constituent.pins.length, `cut ${cut.label} incidence pin is absent`);
        }
        for (const [pinOrdinal, pin] of constituent.pins.entries()) {
          invariant(pin.ordinal === pinOrdinal, `cut ${cut.label} pin order is malformed`);
        }
        for (const [boundaryOrdinal, boundary] of constituent.boundaries.entries()) {
          invariant(boundary.ordinal === boundaryOrdinal, `cut ${cut.label} boundary order is malformed`);
          invariant(Array.isArray(boundary.paths) && boundary.paths.length > 0, `cut ${cut.label} boundary paths are absent`);
          for (const [pathOrdinal, path] of boundary.paths.entries()) {
            invariant(path.ordinal === pathOrdinal, `cut ${cut.label} path order is malformed`);
            invariant(Array.isArray(path.steps), `cut ${cut.label} path steps are absent`);
            invariant(Array.isArray(path.transport), `cut ${cut.label} path transport is absent`);
            for (const step of path.steps) {
              invariant(step.incidence >= 0 && step.incidence < constituent.incidences.length, `cut ${cut.label} path incidence is absent`);
              invariant(step.support_axis >= 0 && step.support_axis < constituent.axis_count, `cut ${cut.label} path support is absent`);
            }
          }
        }
        for (const exposed of constituent.exposed) {
          invariant(exposed >= 0 && exposed < constituent.pins.length, `cut ${cut.label} exposed pin is absent`);
        }
      }
    }
    validatedCellularReports.add(value);
    return true;
  }

  function validatePrime(value) {
    invariant(value && value.schema === SCHEMAS.prime, `expected ${SCHEMAS.prime}`);
    invariant(value.zero_relative && value.zero_relative.origin === 0, "prime receiver has no zero origin");
    invariant(Array.isArray(value.zero_relative.founded_primes) && value.zero_relative.founded_primes.length > 0, "prime axes are absent");
    invariant(Array.isArray(value.zero_relative.wheel_steps), "primorial wheel transitions are absent");
    invariant(value.zeta && value.zeta.sigma > 1 && Array.isArray(value.zeta.axes), "normalizable Zeta receiver is absent");
    invariant(Array.isArray(value.zeta.cylinders) && value.zeta.cylinders.every((row) => row.equal === true), "Zeta rebase testimony is incomplete");
    invariant(Array.isArray(value.zeta.paths) && value.zeta.paths.length === 2, "ordered multiplication paths are absent");
    invariant(value.receivers && value.receivers.s4 && value.receivers.cyclotomic, "polynomial receiver species are absent");
    return true;
  }

  function validateExplicit(value) {
    invariant(value && value.schema === SCHEMAS.explicit, `expected ${SCHEMAS.explicit}`);
    invariant(Array.isArray(value.samples) && value.samples.length > 0, "explicit-formula samples are absent");
    for (const sample of value.samples) {
      invariant(Array.isArray(sample.residuals) && sample.residuals.length > 0, "explicit-formula residual path is absent");
    }
    return true;
  }

  function parseZetaZeros(text) {
    invariant(typeof text === "string", "Zeta-zero testimony is not text");
    const zeros = [];
    for (const line of text.split(/\r?\n/)) {
      const trimmed = line.trim();
      if (!trimmed || trimmed.startsWith("#")) continue;
      const [ordinalText, ordinateText, ...rest] = trimmed.split(/\s+/);
      invariant(rest.length === 0 && /^\d+$/.test(ordinalText), "malformed Zeta-zero row");
      const ordinal = BigInt(ordinalText);
      const ordinate = Exact.fromDecimal(ordinateText);
      invariant(ordinal > 0n && Exact.compare(ordinate, Exact.ratio(0n, 1n)) > 0, "malformed Zeta-zero row");
      zeros.push({
        ordinal: ordinal.toString(),
        real: Exact.read(Exact.ratio(1n, 2n)),
        ordinate: Exact.read(ordinate),
        exact_ordinate: ordinateText,
      });
    }
    invariant(zeros.length > 0, "Zeta-zero testimony is empty");
    return zeros;
  }

  function indexRuns(analysis) {
    return new Map(analysis.runs.map((run) => [run.id, run]));
  }

  function findComparison(analysis, id) {
    return analysis.comparisons.find((comparison) => comparison.id === id) || null;
  }

  function findComparisonFor(analysis, leftRun, leftEdge, rightRun, rightEdge) {
    return analysis.comparisons.find((comparison) =>
      comparison.left.run === leftRun && comparison.left.edge === leftEdge &&
      comparison.right.run === rightRun && comparison.right.edge === rightEdge
    ) || null;
  }

  function edgeOf(run, edgeNumber) {
    return run.edges.find((edge) => edge.edge === edgeNumber) || null;
  }

  function humanize(value) {
    return String(value || "").replaceAll("_", " ").replace(/\b\w/g, (letter) => letter.toUpperCase());
  }

  function runLabel(id) {
    const labels = {
      difference: "whole difference · W23",
      repeat: "exact repeat · W23",
      opposite: "opposite hand · W23",
      common: "common residual · W23",
      scalar_difference: "scalar difference · W23",
      scalar_opposite: "scalar opposite · W23",
      difference_w32: "whole difference · W32",
      no_return: "dark return · W23",
    };
    return labels[id] || humanize(id);
  }

  function formatRational(value) {
    if (typeof value === "number") return String(value);
    if (!value || value.numerator === undefined || value.denominator === undefined) return "—";
    return String(value.denominator) === "1" ? String(value.numerator) : `${value.numerator}/${value.denominator}`;
  }

  function eisensteinCartesian(value) {
    invariant(value && value.a && value.b, "malformed Eisenstein value");
    const a = exactFromRead(value.a);
    const b = exactFromRead(value.b);
    const chartX = Exact.sub(a, Exact.div(b, Exact.ratio(2n, 1n)));
    const chartY = b;
    const scale = Exact.ratio(640n, 1n);
    return {
      x: parseInt(Exact.floor(Exact.mul(chartX, scale)).toString(), 10),
      y: parseInt(Exact.floor(Exact.mul(chartY, scale)).toString(), 10),
      a: Exact.read(a),
      b: Exact.read(b),
      chart: "rational oblique Eisenstein basis; no sqrt(3) embedding",
    };
  }

  function formatEisenstein(value) {
    if (!value || !value.a || !value.b) return "—";
    const a = formatRational(value.a);
    const b = formatRational(value.b);
    if (b === "0") return a;
    return `${a} ${String(b).startsWith("-") ? "−" : "+"} ${String(b).replace("-", "")}ω`;
  }

  function somaRelativeUrl(path) {
    invariant(typeof path === "string" && !path.includes(".."), "artifact path must remain inside src/soma");
    return `../../${path}`;
  }

  function stageLayers(forwardJournal) {
    validateJournal(forwardJournal);
    const word = forwardJournal.observer.word;
    invariant(word && Array.isArray(word.input) && Array.isArray(word.stages), "forward word is absent");
    const layers = [{ id: "input", label: "input", gear: null, values: word.input }];
    for (const stage of word.stages) {
      layers.push({ id: `stage-${stage.ordinal}`, label: `${stage.ordinal + 1} · ${stage.gear.toUpperCase()}`, gear: stage.gear, values: stage.after });
    }
    return { order: word.order, terminal: word.terminal, layers };
  }

  function primitive(id, kind, layer, points, role, metadata, extras) {
    return Object.assign({ id, kind, layer, points, role, metadata: metadata || {} }, extras || {});
  }

  function sitePoint(layerIndex, siteIndex, layerCount) {
    const row = Math.floor(siteIndex / 2);
    const column = siteIndex % 2;
    return [
      (2 * layerIndex - (layerCount - 1)) * 1500,
      (2 * column - 1) * 900,
      (row - 1) * 1300,
    ];
  }

  function transportScene(input) {
    const { run, edge, forwardJournal, worldState, side = "primary", layers: visibleLayers } = input;
    const word = stageLayers(forwardJournal);
    const show = visibleLayers || new Set(["sheet", "transport", "frames", "residual", "contacts"]);
    const role = side === "sibling" ? "sibling" : "primary";
    const primitives = [];
    const layerCount = word.layers.length;

    for (let layerIndex = 0; layerIndex < layerCount; layerIndex += 1) {
      const stage = word.layers[layerIndex];
      const points = stage.values.map((_, siteIndex) => sitePoint(layerIndex, siteIndex, layerCount));

      if (show.has("sheet")) {
        for (let row = 0; row < 2; row += 1) {
          primitives.push(primitive(
            `${side}:sheet:${stage.id}:face:${row}`,
            "polygon",
            "sheet",
            [points[row * 2], points[row * 2 + 1], points[(row + 1) * 2 + 1], points[(row + 1) * 2]],
            role,
            { stage: stage.label, face: row, axes: ["H2", "F3"], run: run.id, edge: edge.edge },
            { width: 1 }
          ));
        }
        for (let row = 0; row < 3; row += 1) {
          const a = row * 2;
          const b = a + 1;
          primitives.push(primitive(
            `${side}:sheet:${stage.id}:h2:${row}`,
            "line",
            "sheet",
            [points[a], points[b]],
            "sheet-h2",
            { stage: stage.label, generator: "H2", row, run: run.id, edge: edge.edge },
            { width: stage.gear === "h2" ? 2 : 1 }
          ));
        }
        for (let column = 0; column < 2; column += 1) {
          for (let row = 0; row < 2; row += 1) {
            const a = row * 2 + column;
            const b = (row + 1) * 2 + column;
            primitives.push(primitive(
              `${side}:sheet:${stage.id}:f3:${column}:${row}`,
              "line",
              "sheet",
              [points[a], points[b]],
              "sheet-f3",
              { stage: stage.label, generator: "F3", column, row, run: run.id, edge: edge.edge },
              { width: stage.gear === "f3" ? 2 : 1 }
            ));
          }
        }
      }

      for (let siteIndex = 0; siteIndex < stage.values.length; siteIndex += 1) {
        const base = points[siteIndex];
        const value = eisensteinCartesian(stage.values[siteIndex]);
        const endpoint = [base[0], base[1] + value.x, base[2] + value.y];
        primitives.push(primitive(
          `${side}:value:${stage.id}:${siteIndex}`,
          "point",
          "sheet",
          [base],
          role,
          { run: run.id, edge: edge.edge, stage: stage.label, site: siteIndex, value: formatEisenstein(stage.values[siteIndex]), exact: stage.values[siteIndex] },
          { radius: 3 }
        ));
        if (show.has("frames")) {
          primitives.push(primitive(
            `${side}:value-vector:${stage.id}:${siteIndex}`,
            "line",
            "frames",
            [base, endpoint],
            role,
            { run: run.id, edge: edge.edge, stage: stage.label, site: siteIndex, vector: formatEisenstein(stage.values[siteIndex]), exact: stage.values[siteIndex] },
            { width: 1 }
          ));
        }
      }

      if (show.has("frames")) {
        const center = sitePoint(layerIndex, 2, layerCount).map((value, index) => index === 2 ? 0 : value);
        const axes = [
          { name: "K", vector: [720, 0, 0], axisRole: "axis-k" },
          { name: "H2", vector: [0, 720, 0], axisRole: "sheet-h2" },
          { name: "F3", vector: [0, 0, 720], axisRole: "sheet-f3" },
        ];
        for (const axis of axes) {
          primitives.push(primitive(
            `${side}:frame:${stage.id}:${axis.name}`,
            "line",
            "frames",
            [center, [center[0] + axis.vector[0], center[1] + axis.vector[1], center[2] + axis.vector[2]]],
            axis.axisRole,
            { run: run.id, edge: edge.edge, stage: stage.label, axis: axis.name, gauge: "receiver display frame" },
            { width: 2 }
          ));
        }
      }
    }

    if (show.has("transport")) {
      for (let layerIndex = 0; layerIndex < layerCount - 1; layerIndex += 1) {
        const deed = word.layers[layerIndex + 1].gear;
        for (let siteIndex = 0; siteIndex < 6; siteIndex += 1) {
          primitives.push(primitive(
            `${side}:transport:${layerIndex}:${siteIndex}`,
            "line",
            "transport",
            [sitePoint(layerIndex, siteIndex, layerCount), sitePoint(layerIndex + 1, siteIndex, layerCount)],
            role,
            { run: run.id, edge: edge.edge, site: siteIndex, ordered_deed: deed, word_order: word.order },
            { width: 1, dash: [3, 4] }
          ));
        }
      }
    }

    const standingSheet = worldState && worldState.standing && Array.isArray(worldState.standing.sheet)
      ? worldState.standing.sheet[0]
      : null;
    if (show.has("residual") && standingSheet && Array.isArray(standingSheet.residual)) {
      const terminalLayer = layerCount - 1;
      for (let siteIndex = 0; siteIndex < standingSheet.residual.length; siteIndex += 1) {
        const base = sitePoint(terminalLayer, siteIndex, layerCount);
        const residual = eisensteinCartesian(standingSheet.residual[siteIndex]);
        const endpoint = [base[0] + 400, base[1] + residual.x, base[2] + residual.y];
        const nonzero = residual.a.ratio !== "0" || residual.b.ratio !== "0";
        primitives.push(primitive(
          `${side}:residual:${siteIndex}`,
          "line",
          "residual",
          [base, endpoint],
          nonzero ? "found" : "quiet",
          {
            run: run.id,
            edge: edge.edge,
            site: siteIndex,
            cut: standingSheet.cut,
            residual: formatEisenstein(standingSheet.residual[siteIndex]),
            loss: formatRational(standingSheet.loss),
            exact: standingSheet.residual[siteIndex],
          },
          { width: nonzero ? 3 : 1 }
        ));
      }
    }

    if (show.has("contacts") && Array.isArray(run.contact_transport) && edge.edge > 1) {
      const contacts = run.contact_transport.filter((contact) => contact.to_edge === edge.edge);
      const terminalLayer = layerCount - 1;
      const destinations = new Map();
      for (const contact of contacts) {
        const from = Math.min(contact.from_local_lineage, 5);
        const destinationKey = contact.to_local_lineage;
        if (!destinations.has(destinationKey)) {
          destinations.set(destinationKey, [
            sitePoint(terminalLayer, from, layerCount)[0] + 1650,
            (2 * destinationKey - Math.max(0, destinations.size - 1)) * 300,
            2650,
          ]);
        }
        primitives.push(primitive(
          `${side}:contact:${contact.from_edge}:${contact.from_local_lineage}:${contact.to_edge}:${contact.to_local_lineage}`,
          "line",
          "contacts",
          [sitePoint(terminalLayer, from, layerCount), destinations.get(destinationKey)],
          contact.shared_grips > 0 ? "ride" : "quiet",
          Object.assign({ run: run.id, edge: edge.edge }, contact),
          { width: Math.min(4, 1 + contact.shared_grips) }
        ));
      }
    }

    return {
      kind: "transport",
      title: `${runLabel(run.id)} · edge ${edge.edge}`,
      primitives,
      camera: { mode: "integer-axonometric", distance: 16000, target: [0, 0, 0], projection: "orthographic", orthoScale: 18000 },
      metadata: {
        run: run.id,
        edge: edge.edge,
        edge_label: edge.label,
        word_order: word.order,
        loss: standingSheet ? formatRational(standingSheet.loss) : "not yet returned",
        contact_grips: edge.contact_grips,
        occupancy: edge.occupancy,
        topology: edge.topology,
        terms: edge.terms,
        receipt_elements: word.layers.reduce((total, layer) => total + layer.values.length, 0) +
          (standingSheet && Array.isArray(standingSheet.residual) ? standingSheet.residual.length : 0) +
          (Array.isArray(run.contact_transport) ? run.contact_transport.filter((contact) => contact.to_edge === edge.edge).length : 0),
        journal: edge.journal,
        world_after: edge.world_after,
      },
    };
  }

  function smithScene(receipt, caseIndex, side) {
    validateSmith(receipt);
    const selectedCase = receipt.cases[boundedIndex(caseIndex, receipt.cases.length)];
    const role = side === "sibling" ? "sibling" : "primary";
    const radius = 3200;
    const primitives = rationalSmithGrid(radius).map((item) => Object.assign({}, item, {
      id: item.id.replace("critical:", "smith:"),
    }));

    function orbit(which, revolution, orbitRole) {
      const points = revolution.quarter_orbit.map((point) => point.map((coordinate) => {
        const scaled = Exact.mul(exactFromRead(coordinate), Exact.ratio(BigInt(radius), 1n));
        return parseInt(Exact.floor(scaled).toString(), 10);
      }));
      if (points.length > 0) points.push(points[0]);
      primitives.push(primitive(`smith:${which}:orbit`, "polyline", "transport", points, orbitRole, {
        case: selectedCase.label,
        plane: which,
        axis: revolution.axis,
        radius_squared: formatRational(revolution.radius_squared),
        exact_orbit: revolution.quarter_orbit,
        projection: "exact quarter-turn orbit in a rational stereographic Smith grid",
      }, { width: 3 }));
      for (let index = 0; index < revolution.quarter_orbit.length; index += 1) {
        primitives.push(primitive(`smith:${which}:point:${index}`, "point", "transport", [points[index]], orbitRole, {
          case: selectedCase.label,
          plane: which,
          quarter_turn: index,
          exact: revolution.quarter_orbit[index],
        }, { radius: 4 }));
      }
    }

    orbit("load", selectedCase.load_revolution, role);
    orbit("reference", selectedCase.reference_revolution, side === "sibling" ? "primary" : "sibling");
    primitives.push(primitive("smith:axis", "line", "frames", [[-radius, 0, 0], [radius, 0, 0]], "axis-k", { axis: "incident current real axis" }, { width: 2 }));

    return {
      kind: "smith-exact",
      title: humanize(selectedCase.label),
      primitives,
      camera: { mode: "integer-axonometric", distance: 9000, target: [0, 0, 0], projection: "orthographic", orthoScale: 8200 },
      metadata: {
        case: selectedCase.label,
        gamma_load: `${formatRational(selectedCase.gamma_at_load.real)} + ${formatRational(selectedCase.gamma_at_load.imaginary)}i`,
        gamma_reference: `${formatRational(selectedCase.gamma_at_reference.real)} + ${formatRational(selectedCase.gamma_at_reference.imaginary)}i`,
        phase_quarter_turns: selectedCase.one_way_phase_quarter_turns,
        load_passive: selectedCase.load_passive_disk,
        reference_passive: selectedCase.reference_passive_disk,
        inverse_exact: selectedCase.input_impedance_inverse_exact,
        projection: "rational stereographic chart; exact quarter-orbit data remains authoritative",
        receipt_elements: selectedCase.load_revolution.quarter_orbit.length + selectedCase.reference_revolution.quarter_orbit.length,
        source_plan: receipt.plan,
      },
    };
  }

  function signedMod(value, modulus) {
    const source = BigInt(String(value));
    const ring = BigInt(String(modulus));
    let reduced = source % ring;
    if (reduced < 0n) reduced += ring;
    if (2n * reduced > ring) reduced -= ring;
    return parseInt(reduced.toString(), 10);
  }

  function atlasCoordinate(value, modulus) {
    const signed = BigInt(String(signedMod(value, modulus)));
    return parseInt((signed * 7000n / BigInt(String(modulus))).toString(), 10);
  }

  function atlasScene(receipt, side) {
    validateAtlas(receipt);
    const role = side === "sibling" ? "sibling" : "primary";
    const cells = receipt.external.cells;
    const maximumLineage = cells.reduce((maximum, cell) => Math.max(maximum, cell.lineage), 1);
    const primitives = [];

    for (const cell of cells) {
      const lineageHeight = parseInt((BigInt(cell.lineage) * 5000n / BigInt(maximumLineage)).toString(), 10) - 2500;
      const start = [
        atlasCoordinate(cell.before[0], receipt.axis),
        atlasCoordinate(cell.before[1], receipt.axis),
        lineageHeight,
      ];
      const end = [
        atlasCoordinate(cell.after[0], receipt.axis),
        atlasCoordinate(cell.after[1], receipt.axis),
        lineageHeight + Math.min(350, (cell.contact + 1) * 40),
      ];
      const cellRole = cell.kind === "open_transit" ? "quiet" : role;
      primitives.push(primitive(`atlas:${side}:${cell.id}`, "line", "transport", [start, end], cellRole, {
        standing: receipt.standing,
        axis: receipt.axis,
        id: cell.id,
        lineage: cell.lineage,
        segment: cell.segment,
        contact: cell.contact,
        kind: cell.kind,
        before: cell.before,
        after: cell.after,
        tangent_before: cell.tangent_before,
        tangent_after: cell.tangent_after,
        response: cell.response,
      }, { width: 1 }));
      if (cell.contact === 0 || cell.kind === "open_transit") {
        primitives.push(primitive(`atlas:${side}:${cell.id}:origin`, "point", "contacts", [start], cellRole, {
          standing: receipt.standing,
          id: cell.id,
          lineage: cell.lineage,
          kind: cell.kind,
          source_receipt: receipt.source_receipt,
        }, { radius: cell.kind === "open_transit" ? 2 : 2 }));
      }
    }

    return {
      kind: "atlas",
      title: `${humanize(receipt.standing)} field atlas`,
      primitives,
      camera: { mode: "integer-axonometric", distance: 14000, target: [0, 0, 0], projection: "orthographic", orthoScale: 15000 },
      metadata: {
        standing: receipt.standing,
        axis: receipt.axis,
        relations: receipt.relations,
        response_volumes: receipt.response_volumes,
        open_transits: receipt.open_transits,
        lineage_faces: receipt.lineage_faces,
        world_contact_faces: receipt.world_contact_faces,
        closed_loops: receipt.closed_loops,
        nontrivial_holonomies: receipt.nontrivial_holonomies,
        receipt_elements: cells.length,
        exact_source_receipt: receipt.exact_source_receipt,
        source_receipt: receipt.source_receipt,
      },
    };
  }

  function integerSqrt(value) {
    const source = BigInt(String(value));
    if (source <= 0n) return 0;
    let lower = 0n;
    let upper = source + 1n;
    while (upper - lower > 1n) {
      const middle = (lower + upper) / 2n;
      if (middle * middle <= source) lower = middle;
      else upper = middle;
    }
    return parseInt(lower.toString(), 10);
  }

  function primeAxesThrough(report, horizon) {
    validatePrime(report);
    return report.zero_relative.founded_primes.filter((prime) => prime <= horizon);
  }

  function centeredResidue(value, axis) {
    const residue = ((value % axis) + axis) % axis;
    return residue * 2 > axis ? residue - axis : residue;
  }

  function factorization(report, value) {
    let remaining = parseInt(String(value), 10);
    if (!Number.isSafeInteger(remaining)) return [];
    if (remaining < 0) remaining = -remaining;
    if (remaining < 2) return [];
    const factors = [];
    for (const prime of report.zero_relative.founded_primes) {
      if (prime * prime > remaining) break;
      let exponent = 0;
      while (remaining % prime === 0) {
        remaining /= prime;
        exponent += 1;
      }
      if (exponent) factors.push({ prime, exponent });
    }
    if (remaining > 1) factors.push({ prime: remaining, exponent: 1 });
    return factors;
  }

  function factorizationLabel(factors) {
    if (!factors.length) return "—";
    return factors.map((factor) => factor.exponent === 1 ? String(factor.prime) : `${factor.prime}^${factor.exponent}`).join(" × ");
  }

  function polynomialReceiverRead(receiver, species) {
    const support = receiver.coefficients_ascending
      .map((coefficient, exponent) => String(coefficient) !== "0" ? exponent : null)
      .filter((exponent) => exponent !== null);
    return {
      name: receiver.name,
      exponent_support: support,
      newton_hull: support.length ? [support[0], support[support.length - 1]] : [],
      newton_rank: support.length > 1 ? 1 : 0,
      species: species ? { ...species } : null,
    };
  }

  function digitPhase(value) {
    const terminal = ((value % 10) + 10) % 10;
    const unitCycle = [1, 3, 9, 7];
    const unitAt = unitCycle.indexOf(terminal);
    const residue30 = ((value % 30) + 30) % 30;
    const wheel30 = [1, 7, 11, 13, 17, 19, 23, 29];
    const wheelAt = wheel30.indexOf(residue30);
    const twinPairs = [[11, 13], [17, 19], [29, 1]];
    const twin = twinPairs.find((pair) => pair.includes(residue30)) || null;
    return {
      decimal_terminal_digit: terminal,
      residue_mod_2: value % 2,
      residue_mod_5: value % 5,
      unit_mod_10: unitAt >= 0,
      multiplicative_by_3_cycle: unitCycle,
      multiplicative_cycle_position: unitAt >= 0 ? unitAt : null,
      multiplicative_by_3_successor: unitAt >= 0 ? unitCycle[(unitAt + 1) % unitCycle.length] : null,
      residue_mod_30: residue30,
      admissible_mod_30: wheelAt >= 0,
      mod_30_wheel: wheel30,
      mod_30_position: wheelAt >= 0 ? wheelAt : null,
      twin_channel: twin,
    };
  }

  function axisLiftCoordinate(value, axis, role) {
    const direct = ((value % axis) + axis) % axis;
    const centered = centeredResidue(value, axis);
    const quotient = Math.floor(value / axis);
    return {
      axis,
      quotient,
      winding: quotient,
      residue: centered,
      centered_residue: centered,
      direct,
      phase_numerator: direct,
      phase_denominator: axis,
      phase_turns: Exact.read(Exact.ratio(BigInt(direct), BigInt(axis))),
      cyclotomic_element: `zeta_${axis}^${direct}`,
      pole_distance_law: `2 sin(pi*|${centered}|/${axis})`,
      horizon_square: axis * axis,
      horizon_age: value - axis * axis,
      common_lift: value,
      common_lift_equation: `${value} = ${quotient}*${axis} + ${direct}`,
      axis_role: role || (direct === 0 ? "DIVISOR_DISCRIMINANT" : "RIDE"),
    };
  }

  function boundedAffineRelations(report, receiver, axes) {
    const bestByAxes = new Map();
    const coefficientBound = 8;
    const offsetBound = 12;
    for (let multiplier = 1; multiplier <= coefficientBound; multiplier += 1) {
      for (let offset = -offsetBound; offset <= offsetBound; offset += 1) {
        if (offset === 0 || gcd(multiplier, Math.abs(offset)) !== 1) continue;
        const value = multiplier * receiver + offset;
        const magnitude = Math.abs(value);
        if (magnitude < 2) continue;
        const closedAxes = axes.filter((axis) => magnitude % axis === 0);
        if (closedAxes.length < 2) continue;
        const axisProduct = closedAxes.reduce((product, axis) => product * axis, 1);
        const cofactor = magnitude / axisProduct;
        const exactAxisProduct = magnitude === axisProduct;
        const left = `${multiplier === 1 ? "" : multiplier}n${offset < 0 ? "−" : "+"}${Math.abs(offset)}`;
        const factors = factorization(report, magnitude);
        const factorText = factorizationLabel(factors);
        const row = {
          receiver,
          multiplier,
          offset,
          value,
          magnitude,
          closed_axes: closedAxes,
          axis_product: axisProduct,
          cofactor,
          exact_axis_product: exactAxisProduct,
          factorization: factors,
          factorization_text: factorText,
          equation: `${left}=${magnitude}=${factorText.replaceAll(" × ", "·")}`,
          search_bounds: { multiplier: coefficientBound, absolute_offset: offsetBound },
          score: [exactAxisProduct ? 1 : 0, closedAxes.length, -(multiplier * 4 + (offset < 0 ? -offset : offset)), -cofactor],
        };
        const key = closedAxes.join("·");
        if (!bestByAxes.has(key) || bestByAxes.get(key).score < row.score) bestByAxes.set(key, row);
      }
    }
    return [...bestByAxes.values()]
      .sort((left, right) => {
        for (let at = 0; at < left.score.length; at += 1) {
          if (left.score[at] !== right.score[at]) return right.score[at] - left.score[at];
        }
        return 0;
      })
      .slice(0, 6)
      .map(({ score, ...row }) => row);
  }

  function reducedFraction(numerator, denominator) {
    const divisor = gcd(numerator < 0 ? -numerator : numerator, denominator < 0 ? -denominator : denominator) || 1;
    const sign = denominator < 0 ? -1 : 1;
    const reducedNumerator = sign * numerator / divisor;
    const reducedDenominator = sign * denominator / divisor;
    return {
      numerator: reducedNumerator,
      denominator: reducedDenominator,
      text: reducedDenominator === 1 ? String(reducedNumerator) : `${reducedNumerator}/${reducedDenominator}`,
    };
  }

  function liftTransitions(receiver, pathCoordinates) {
    const transitions = [];
    for (let at = 0; at < pathCoordinates.length - 1; at += 1) {
      const from = pathCoordinates[at];
      const to = pathCoordinates[at + 1];
      const phaseDelta = reducedFraction(to.direct * from.axis - from.direct * to.axis, to.axis * from.axis);
      const centeredDelta = reducedFraction(to.centered_residue * from.axis - from.centered_residue * to.axis, to.axis * from.axis);
      transitions.push({
        ordinal: at,
        receiver,
        from_axis: from.axis,
        to_axis: to.axis,
        from,
        to,
        common_lift_identity: `${from.axis}*${from.quotient}+${from.direct}=${receiver}=${to.axis}*${to.quotient}+${to.direct}`,
        winding_delta: to.quotient - from.quotient,
        principal_phase_delta: phaseDelta,
        centered_phase_delta: centeredDelta,
        principal_orientation: Math.sign(phaseDelta.numerator),
        centered_orientation: Math.sign(centeredDelta.numerator),
        chart_scope: "exact finite difference in the declared ordered principal/centered phase charts; not intrinsic smooth curvature",
      });
    }
    return transitions;
  }

  function discreteChartTurns(transitions) {
    const turns = [];
    for (let at = 0; at < transitions.length - 1; at += 1) {
      const incoming = transitions[at];
      const outgoing = transitions[at + 1];
      if (incoming.principal_orientation === 0 || outgoing.principal_orientation === 0 || incoming.principal_orientation === outgoing.principal_orientation) continue;
      turns.push({
        axis: incoming.to_axis,
        incoming_transition: incoming.ordinal,
        outgoing_transition: outgoing.ordinal,
        incoming_phase_delta: incoming.principal_phase_delta,
        outgoing_phase_delta: outgoing.principal_phase_delta,
        kind: "discrete orientation reversal in the declared principal-phase chart",
        intrinsic_status: "not a smooth critical point without a receiver potential and connection",
      });
    }
    return turns;
  }

  function primeReceiverRead(report, receiver) {
    validatePrime(report);
    const horizon = report.zero_relative.succession_horizon;
    const requested = /^[-+]?\d+$/.test(String(receiver)) ? BigInt(String(receiver)) : 2n;
    const bounded = requested < 2n ? 2n : requested > BigInt(horizon) ? BigInt(horizon) : requested;
    const value = parseInt(bounded.toString(), 10);
    const axes = primeAxesThrough(report, integerSqrt(value));
    const residues = axes.map((axis) => axisLiftCoordinate(value, axis));
    const poleHits = residues.filter((row) => row.direct === 0).map((row) => row.axis);
    const founded = report.zero_relative.founded_primes.includes(value);
    const s4 = report.receivers.s4.species.find((row) => row.prime === value) || null;
    const cyclotomic = report.receivers.cyclotomic.species.find((row) => row.prime === value) || null;
    const factors = factorization(report, value);
    const firstPoleAt = residues.findIndex((row) => row.direct === 0);
    const traversed = firstPoleAt >= 0 ? residues.slice(0, firstPoleAt + 1) : [...residues];
    const founding = founded ? axisLiftCoordinate(value, value, "FOUND_NEW_BASIS") : null;
    const pathCoordinates = traversed;
    const transitions = liftTransitions(value, pathCoordinates);
    const latestHorizon = residues.length ? residues[residues.length - 1] : null;
    return {
      receiver: value,
      origin: 0,
      prime: founded,
      phase: founded ? "FOUND_NEW_AXIS" : "CLOSES_PRIOR_AXIS",
      axes,
      residues,
      path_coordinates: pathCoordinates,
      lift_transitions: transitions,
      chart_turns: discreteChartTurns(transitions),
      founding_coordinate: founding,
      pole_hits: poleHits,
      first_pole: firstPoleAt >= 0 ? residues[firstPoleAt] : null,
      factorization: factors,
      factorization_text: factorizationLabel(factors),
      valuation: {
        basis: factors.map((factor) => factor.prime),
        exponent_vector: factors.map((factor) => factor.exponent),
        coordinates: factors,
        rank: factors.length,
        primitive_basis_vector: founded && factors.length === 1 && factors[0].exponent === 1,
      },
      digit_phase: digitPhase(value),
      horizon_births: residues.map((row) => ({ axis: row.axis, boundary: row.horizon_square, age: row.horizon_age })),
      latest_horizon: latestHorizon ? { axis: latestHorizon.axis, boundary: latestHorizon.horizon_square, age: latestHorizon.horizon_age } : null,
      affine_relations: boundedAffineRelations(report, value, axes),
      receiver_species: {
        s4: s4 && { world: report.receivers.s4.name, ...s4 },
        cyclotomic: cyclotomic && { world: report.receivers.cyclotomic.name, ...cyclotomic },
      },
      receiver_polynomials: {
        s4: polynomialReceiverRead(report.receivers.s4, s4),
        cyclotomic: polynomialReceiverRead(report.receivers.cyclotomic, cyclotomic),
      },
      scale_transport: {
        volume_rank: 3,
        boundary_rank: 2,
        exponent: "2/3",
        law: "(ell^3)^(2/3)=ell^2",
        interpretation: "codimension-one scale transport; not swept-volume recovery",
      },
      metric: `dℓ² = Σ (σ log p)² dθ_p², σ=${report.zeta.sigma}`,
      intrinsic_read: "each residue fiber is circular; the ordered base changes rank at horizon and FOUND seams",
    };
  }

  function labelPrimitive(id, point, text, role, metadata, align) {
    return primitive(id, "label", "labels", [point], role, Object.assign({ label: text }, metadata || {}), { align: align || "left" });
  }

  const EXACT_SERIES_TERMS = 8;
  let retainedPiSeries = null;

  function exactPiSeries() {
    if (!retainedPiSeries) retainedPiSeries = Exact.machinPi(EXACT_SERIES_TERMS);
    return retainedPiSeries;
  }

  function exactFromRead(value) {
    return Exact.ratio(BigInt(value.numerator), BigInt(value.denominator));
  }

  function intervalIntegerCoordinate(value, scale) {
    const lower = exactFromRead(value.lower);
    const upper = exactFromRead(value.upper);
    const center = Exact.div(Exact.add(lower, upper), Exact.ratio(2n, 1n));
    const scaled = Exact.mul(center, Exact.ratio(BigInt(scale), 1n));
    return parseInt(Exact.floor(scaled).toString(), 10);
  }

  function orderedBaseCoordinate(index, count) {
    if (count <= 1) return 0;
    return -4000 + parseInt((BigInt(index) * 8000n / BigInt(count - 1)).toString(), 10);
  }

  function phaseAtlas(axes) {
    const pi = exactPiSeries();
    const phases = [];
    for (const axis of axes) {
      for (let residue = 0; residue < axis; residue += 1) {
        const phase = Exact.cyclotomicPhase(axis, residue, EXACT_SERIES_TERMS, pi);
        phases.push(Object.freeze({
          id: `phase:${axis}:${residue}`,
          axis,
          residue,
          conjugate_id: `phase:${axis}:${residue === 0 ? 0 : axis - residue}`,
          element: phase.element,
          turn: phase.turn,
          quadrant: phase.quadrant,
          local_pi_factor: phase.local_pi_factor,
          real: phase.real,
          imaginary: phase.imaginary,
          embedding_series: phase.embedding_series,
        }));
      }
    }
    return phases;
  }

  function primeAnalyticalReceipt(report, receiver, span) {
    const read = primeReceiverRead(report, receiver);
    const requestedSpan = /^\d+$/.test(String(span)) ? BigInt(String(span)) : 6n;
    const boundedSpan = requestedSpan < 1n ? 1n : requestedSpan > 24n ? 24n : requestedSpan;
    const spanInteger = parseInt(boundedSpan.toString(), 10);
    const low = read.receiver - spanInteger < 2 ? 2 : read.receiver - spanInteger;
    const highCandidate = read.receiver + spanInteger;
    const high = highCandidate > report.zero_relative.succession_horizon
      ? report.zero_relative.succession_horizon
      : highCandidate;
    const phases = phaseAtlas(read.axes);
    const phaseById = new Map(phases.map((row) => [row.id, row]));
    const directRows = [];
    const conjugateRows = [];
    const crossings = [];
    const strings = [];

    for (const axis of read.axes) {
      const direct = [];
      const conjugate = [];
      const priorByResidue = new Map();
      let previousQuotient = null;
      for (let value = low; value <= high; value += 1) {
        const incidence = axisLiftCoordinate(value, axis);
        const conjugateResidue = incidence.direct === 0 ? 0 : axis - incidence.direct;
        const common = {
          ordinal: value - low,
          value,
          receiver_offset: value - read.receiver,
          axis,
          quotient: incidence.quotient,
          winding: incidence.winding,
          residue: incidence.direct,
          centered_residue: incidence.centered_residue,
          phase_id: `phase:${axis}:${incidence.direct}`,
          cyclotomic_element: incidence.cyclotomic_element,
          phase_turn: incidence.phase_turns,
          prior_same_phase: priorByResidue.has(incidence.direct) ? priorByResidue.get(incidence.direct) : null,
          recurrence_period: axis,
          winding_increment: previousQuotient === null ? null : incidence.quotient - previousQuotient,
          discriminant: incidence.direct === 0,
        };
        const directRow = Object.freeze({ ...common, sheet: "direct", hand: 1 });
        const conjugateRow = Object.freeze({
          ...common,
          sheet: "conjugate",
          hand: -1,
          source_residue: incidence.direct,
          residue: conjugateResidue,
          centered_residue: centeredResidue(conjugateResidue, axis),
          phase_id: `phase:${axis}:${conjugateResidue}`,
          cyclotomic_element: `zeta_${axis}^${conjugateResidue}`,
          phase_turn: Exact.read(Exact.ratio(BigInt(-incidence.direct), BigInt(axis))),
        });
        direct.push(directRow);
        conjugate.push(conjugateRow);
        directRows.push(directRow);
        conjugateRows.push(conjugateRow);
        if (incidence.direct === 0) crossings.push(Object.freeze({
          value,
          axis,
          quotient: incidence.quotient,
          direct_phase_id: directRow.phase_id,
          conjugate_phase_id: conjugateRow.phase_id,
          kind: "winding closure / divisor discriminant",
        }));
        priorByResidue.set(incidence.direct, value);
        previousQuotient = incidence.quotient;
      }
      strings.push(Object.freeze({ axis, aperture: Object.freeze({ low, high }), direct, conjugate }));
    }

    const axisSection = read.residues.map((row, ordinal) => Object.freeze({
      ordinal,
      axis: row.axis,
      quotient: row.quotient,
      winding: row.winding,
      residue: row.direct,
      centered_residue: row.centered_residue,
      phase_id: `phase:${row.axis}:${row.direct}`,
      cyclotomic_element: row.cyclotomic_element,
      phase_turn: row.phase_turns,
      pole_distance_law: row.pole_distance_law,
      horizon_square: row.horizon_square,
      horizon_age: row.horizon_age,
      axis_role: row.axis_role,
    }));
    const founding = read.founding_coordinate ? Object.freeze({
      axis: read.founding_coordinate.axis,
      quotient: read.founding_coordinate.quotient,
      residue: 0,
      cyclotomic_element: `zeta_${read.receiver}^0`,
      kind: "transverse basis birth",
      placement: "terminal seam after the complete divisor-test section",
    }) : null;
    const phaseRows = phases.map((row) => Object.freeze({
      id: row.id,
      axis: row.axis,
      residue: row.residue,
      element: row.element,
      turn: row.turn.ratio,
      conjugate_id: row.conjugate_id,
      real_enclosure: `${row.real.lower.ratio} .. ${row.real.upper.ratio}`,
      imaginary_enclosure: `${row.imaginary.lower.ratio} .. ${row.imaginary.upper.ratio}`,
      series: `${row.embedding_series.pi}; ${row.embedding_series.sine}; ${row.embedding_series.cosine}`,
    }));
    const logBasis = read.axes.map((axis) => Object.freeze({
      axis,
      formal_basis: `ell_${axis}`,
      series: Exact.logIntegerSeries(axis, EXACT_SERIES_TERMS),
    }));
    const transitionRows = read.lift_transitions.map((row) => Object.freeze({
      ordinal: row.ordinal,
      from_axis: row.from_axis,
      to_axis: row.to_axis,
      common_lift_identity: row.common_lift_identity,
      winding_delta: row.winding_delta,
      principal_phase_delta: row.principal_phase_delta.text,
      centered_phase_delta: row.centered_phase_delta.text,
    }));
    const affineRows = read.affine_relations.map((row) => Object.freeze({
      equation: row.equation,
      multiplier: row.multiplier,
      offset: row.offset,
      closed_axes: row.closed_axes.join("*"),
      cofactor: row.cofactor,
      exact_axis_product: row.exact_axis_product,
    }));
    const piSeries = exactPiSeries();
    const eSeries = Exact.expSeries(Exact.ratio(1n, 1n), EXACT_SERIES_TERMS);
    const eulerSeam = Object.freeze({
      identity: "exp(i*pi)=zeta_2^1=-1; therefore exp(i*pi)+1=0",
      exact_root: "zeta_2^1",
      relation: "the half-turn cyclotomic phase closes exactly; pi and exp remain retained series wherever an embedding is requested",
    });
    const retainedConstants = Object.freeze([
      Object.freeze({
        constant: "pi",
        identity: "pi=16*atan(1/5)-4*atan(1/239)",
        retained_series: piSeries,
      }),
      Object.freeze({
        constant: "e",
        identity: "e=exp(1)=sum_(j>=0) 1/j!",
        retained_series: eSeries,
      }),
      Object.freeze({
        constant: "Euler seam",
        ...eulerSeam,
      }),
    ]);

    invariant(axisSection.every((row) => phaseById.has(row.phase_id)), "every axis-section phase is present in the cyclotomic atlas");
    return Object.freeze({
      schema: SCHEMAS.primeObserver,
      observer_only: true,
      arithmetic_source_schema: report.schema,
      receiver: read.receiver,
      origin: 0,
      aperture: Object.freeze({ low, high }),
      exact_carrier: "integer quotients, integer residues, cyclotomic elements, BigInt ratios, and retained rational series",
      constants: Object.freeze({ pi: piSeries, e: eSeries, euler_seam: eulerSeam }),
      receiver_section: read,
      axis_section: axisSection,
      founding,
      phase_atlas: phases,
      log_basis: logBasis,
      succession_strings: strings,
      crossings,
      projection_declarations: Object.freeze({
        axis_section: "ordered divisor-test ordinal with fixed display-gauge fiber radius; no cross-fiber incidence chord",
        succession: "integer chronology along the center axis; cyclotomic enclosure quantized only at the disposable pixel boundary",
        quantization: "screen coordinate is the integer floor of the center of a certified rational enclosure; the enclosure remains in this receipt",
      }),
      datasets: Object.freeze({
        axis_section: axisSection,
        founding: founding ? [founding] : [],
        succession_direct: directRows,
        succession_conjugate: conjugateRows,
        winding_crossings: crossings,
        cyclotomic_phase_atlas: phaseRows,
        common_lift_transitions: transitionRows,
        affine_relations: affineRows,
        retained_constants: retainedConstants,
      }),
    });
  }

  function phaseScreenPoint(phase, base, radius) {
    return [
      base,
      intervalIntegerCoordinate(phase.real, radius),
      intervalIntegerCoordinate(phase.imaginary, radius),
    ];
  }

  function exactPrimeReceiverScene(report, receiver, span) {
    const receipt = primeAnalyticalReceipt(report, receiver, span);
    const read = receipt.receiver_section;
    const displayRows = read.residues;
    const displayAxes = displayRows.map((row) => row.axis);
    const baseByAxis = new Map(displayAxes.map((axis, ordinal) => [axis, orderedBaseCoordinate(ordinal, displayAxes.length)]));
    const phaseById = new Map(receipt.phase_atlas.map((row) => [row.id, row]));
    const radius = 820;
    const primitives = [];
    const centersByAxis = new Map();

    for (const [ordinal, row] of displayRows.entries()) {
      const axis = row.axis;
      const base = baseByAxis.get(axis);
      const center = [base, 0, 0];
      const fiber = [];
      for (let residue = 0; residue < axis; residue += 1) {
        fiber.push(phaseScreenPoint(phaseById.get(`phase:${axis}:${residue}`), base, radius));
      }
      fiber.push(fiber[0]);
      const incidencePhase = phaseById.get(`phase:${axis}:${row.direct}`);
      const incidence = phaseScreenPoint(incidencePhase, base, radius);
      const pole = phaseScreenPoint(phaseById.get(`phase:${axis}:0`), base, radius);
      centersByAxis.set(axis, center);
      primitives.push(primitive(
        `prime:fiber:${axis}`,
        "polyline",
        "sheet",
        fiber,
        "grid",
        {
          ...row,
          axis,
          receiver: read.receiver,
          fiber_coordinate: `zeta_${axis}^r`,
          base_coordinate: `divisor-test ordinal ${ordinal}`,
          chart: `exact cyclotomic ${axis}-gon over the ordered divisor-test base`,
          projection: receipt.projection_declarations.axis_section,
        },
        { width: 1 }
      ));
      primitives.push(primitive(`prime:base:${axis}`, "point", "frames", [center], "axis-k", {
        axis,
        receiver: read.receiver,
        base_coordinate: ordinal,
        horizon_square: row.horizon_square,
        role: "axis-test base",
      }, { radius: 2 }));
      primitives.push(primitive(`prime:pole:${axis}`, "point", "contacts", [pole], "exposed", {
        axis,
        residue: 0,
        role: "zero pole / divisor discriminant",
        receiver: read.receiver,
        horizon_square: row.horizon_square,
      }, { radius: 3 }));
      primitives.push(primitive(`prime:projection-arm:${axis}`, "line", "frames", [center, incidence], row.direct === 0 ? "exposed" : "ride", {
        ...row,
        receiver: read.receiver,
        relation: "axis base evaluates the common lift on this cyclotomic fiber",
      }, { width: 1 }));
      primitives.push(primitive(`prime:incidence:${axis}`, "point", "contacts", [incidence], row.direct === 0 ? "exposed" : "primary", {
        ...row,
        receiver: read.receiver,
        phase: incidencePhase,
        vertex_kind: row.direct === 0 ? "divisor discriminant" : "RIDE incidence",
        exact_explanation: `${row.common_lift_equation}; q=${row.quotient} complete turns and phase ${row.direct}/${axis}`,
      }, { radius: row.direct === 0 ? 5 : 4 }));
      primitives.push(labelPrimitive(`prime:fiber-label:${axis}`, [base, 0, -radius - 160], row.direct === 0
        ? `p=${axis} · CLOSE · q${row.quotient} r0`
        : `p=${axis} · horizon ${axis * axis}`, "quiet", { ...row, receiver: read.receiver }, "center"));
      if (row.direct !== 0) {
        primitives.push(labelPrimitive(`prime:incidence-label:${axis}`, [incidence[0], incidence[1], incidence[2] + 150], `q${row.quotient} · r${row.direct}`, "primary", { ...row, receiver: read.receiver }, "center"));
      }
    }

    const pathRows = read.path_coordinates;
    if (pathRows.length > 1) {
      primitives.push(primitive("prime:common-lift-base", "polyline", "frames", pathRows.map((row) => centersByAxis.get(row.axis)), "axis-k", {
        receiver: read.receiver,
        common_lift: read.receiver,
        axis_test_order: pathRows.map((row) => row.axis),
        relation: "one common integer carried through the declared divisor-test base",
      }, { width: 1, dash: [3, 4] }));
      for (let at = 0; at < pathRows.length - 1; at += 1) {
        const from = pathRows[at];
        const to = pathRows[at + 1];
        const transition = read.lift_transitions[at];
        const fromBase = centersByAxis.get(from.axis)[0];
        const toBase = centersByAxis.get(to.axis)[0];
        primitives.push(primitive(`prime:transition-pin:${from.axis}:${to.axis}`, "point", "transport", [[(fromBase + toBase) >> 1, 0, 0]], to.direct === 0 ? "exposed" : "primary", {
          ...transition,
          ordered_event: `${from.axis} -> ${to.axis}`,
          display_relation: "the base pin marks ordered common-lift transport; no cross-fiber chord is drawn",
        }, { radius: 3 }));
      }
    }

    if (read.founding_coordinate) {
      const lastBase = displayRows.length ? baseByAxis.get(displayRows[displayRows.length - 1].axis) : 0;
      const terminalBase = lastBase + 700;
      const aperture = [terminalBase, 0, 0];
      const founding = [terminalBase, 0, 1250];
      if (displayRows.length) {
        primitives.push(primitive("prime:founding-approach", "line", "frames", [[lastBase, 0, 0], aperture], "axis-k", {
          receiver: read.receiver,
          relation: "terminal test aperture after every prior axis RIDEs",
        }, { width: 1, dash: [3, 4] }));
      }
      primitives.push(primitive("prime:founding-arm", "line", "transport", [aperture, founding], "found", receipt.founding, { width: 3 }));
      primitives.push(primitive(`prime:founding:${read.receiver}`, "point", "contacts", [founding], "found", receipt.founding, { radius: 6 }));
      primitives.push(labelPrimitive(`prime:founding-label:${read.receiver}`, [founding[0], founding[1], founding[2] + 180], `p=${read.receiver} · FOUND transverse axis`, "found", receipt.founding, "center"));
    }

    if (displayRows.length) {
      const first = displayRows[0];
      primitives.push(labelPrimitive("prime:common-lift-label", [baseByAxis.get(first.axis) - 240, -1150, 0], `n=${read.receiver} · common lift`, "axis-k", {
        receiver: read.receiver,
        axis_test_order: pathRows.map((row) => row.axis),
      }));
    }

    for (let candidate = receipt.aperture.low; candidate <= receipt.aperture.high; candidate += 1) {
      if (candidate === read.receiver) continue;
      const candidatePrime = report.zero_relative.founded_primes.includes(candidate);
      for (const row of displayRows) {
        const axis = row.axis;
        const direct = ((candidate % axis) + axis) % axis;
        const point = phaseScreenPoint(phaseById.get(`phase:${axis}:${direct}`), baseByAxis.get(axis), radius);
        const poleHit = direct === 0;
        primitives.push(primitive(`prime:neighbor:${candidate}:axis:${axis}`, "point", "residual", [point], poleHit ? "exposed" : candidatePrime ? "ride" : "quiet", {
          candidate,
          receiver: read.receiver,
          prime: candidatePrime,
          axis,
          quotient: (candidate - direct) / axis,
          residue: direct,
          centered_residue: centeredResidue(candidate, axis),
          pole_hit: poleHit ? axis : null,
          factorization: factorizationLabel(factorization(report, candidate)),
          phase_id: `phase:${axis}:${direct}`,
          scope: "neighbor sample on the selected receiver's declared residue fiber; no cross-axis chord inferred",
        }, { radius: candidatePrime ? 2 : poleHit ? 2 : 1 }));
      }
    }

    for (const [relationAt, relation] of read.affine_relations.slice(0, 3).entries()) {
      const relationCenters = relation.closed_axes.map((axis) => centersByAxis.get(axis)).filter(Boolean);
      if (relationCenters.length < 2) continue;
      primitives.push(primitive(`prime:affine-relation:${relationAt}`, "polyline", "contacts", relationCenters, "sibling", {
        ...relation,
        geometry: "exact axis-product incidence highlighted on the divisor-test base",
      }, { width: relationAt === 0 ? 2 : 1, dash: relationAt === 0 ? [] : [2, 3] }));
      if (relationAt === 0) {
        const midpoint = relationCenters[relationCenters.length >> 1];
        primitives.push(labelPrimitive(`prime:affine-relation-label:${relationAt}`, [midpoint[0], 0, 1450], relation.equation, "sibling", relation, "center"));
      }
    }

    return {
      kind: "prime-receiver-exact",
      title: `${read.receiver} as one exact section through cyclotomic fibers`,
      primitives,
      camera: {
        mode: "integer-axonometric",
        distance: 12000,
        target: [0, 0, 0],
        projection: "orthographic",
        orthoScale: 11000,
      },
      metadata: Object.assign({}, read, {
        neighborhood: [receipt.aperture.low, receipt.aperture.high],
        zeta_sigma: report.zeta.sigma,
        coordinate_law: "base is exact divisor-test ordinal; every fiber is the cyclotomic p-gon; vertex is exact (p,q,r)",
        camera_root: `receiver ${read.receiver}`,
        display_warning: "the section has no cross-fiber incidence chords; the screen reads retained rational enclosures through declared integer-pixel quantization",
        chart_rank: displayRows.length,
        path_axis_order: pathRows.map((row) => row.axis),
        neighbor_points_are_unjoined: true,
        analytical_receipt_schema: receipt.schema,
        exact_series_terms: EXACT_SERIES_TERMS,
        receipt_elements: primitives.length,
      }),
      analysis: receipt,
    };
  }

  function primeSuccessionScene(report, receiver, span, selectedAxis) {
    const receipt = primeAnalyticalReceipt(report, receiver, span);
    const available = receipt.receiver_section.axes;
    const requested = /^\d+$/.test(String(selectedAxis)) ? parseInt(String(selectedAxis), 10) : null;
    const axis = requested && available.includes(requested) ? requested : available[available.length - 1];
    invariant(axis, "the succession receiver has at least one active prime axis");
    const string = receipt.succession_strings.find((row) => row.axis === axis);
    const phaseById = new Map(receipt.phase_atlas.map((row) => [row.id, row]));
    const radius = 1700;
    const chronologyStep = 560;
    const directPoints = string.direct.map((row) => {
      const point = phaseScreenPoint(phaseById.get(row.phase_id), row.receiver_offset * chronologyStep, radius);
      return point;
    });
    const conjugatePoints = string.conjugate.map((row) => phaseScreenPoint(
      phaseById.get(row.phase_id),
      row.receiver_offset * chronologyStep,
      radius
    ));
    const primitives = [];
    const centerline = string.direct.map((row) => [row.receiver_offset * chronologyStep, 0, 0]);
    primitives.push(primitive("prime-succession:centerline", "polyline", "frames", centerline, "axis-k", {
      axis,
      aperture: string.aperture,
      role: "source succession centerline; generator of the sweep, not a second strand",
    }, { width: 1, dash: [3, 4] }));
    primitives.push(primitive("prime-succession:direct", "polyline", "transport", directPoints, "primary", {
      axis,
      hand: 1,
      source_rows: string.direct.map((row) => row.ordinal),
      relation: "ordered discrete succession string in C_p",
      interpolation: "screen segment carries only adjacency between consecutive integer events",
    }, { width: 3 }));
    primitives.push(primitive("prime-succession:conjugate", "polyline", "transport", conjugatePoints, "sibling", {
      axis,
      hand: -1,
      source_rows: string.conjugate.map((row) => row.ordinal),
      duality: "cyclotomic conjugation zeta_p^r -> zeta_p^(-r)",
      interpolation: "screen segment carries only adjacency between consecutive integer events",
    }, { width: 2 }));

    for (const [ordinal, row] of string.direct.entries()) {
      const role = row.value === receipt.receiver ? "primary" : row.discriminant ? "found" : "ride";
      primitives.push(primitive(`prime-succession:direct:${row.value}`, "point", "contacts", [directPoints[ordinal]], role, row, { radius: row.value === receipt.receiver ? 6 : row.discriminant ? 5 : 2 }));
      primitives.push(primitive(`prime-succession:conjugate:${row.value}`, "point", "contacts", [conjugatePoints[ordinal]], row.value === receipt.receiver ? "sibling" : row.discriminant ? "found" : "quiet", string.conjugate[ordinal], { radius: row.value === receipt.receiver ? 5 : row.discriminant ? 4 : 2 }));
      if (row.discriminant) {
        primitives.push(primitive(`prime-succession:crossing:${row.value}`, "line", "residual", [directPoints[ordinal], conjugatePoints[ordinal]], "found", {
          value: row.value,
          axis,
          quotient: row.quotient,
          relation: "direct and conjugate sheets share the zero phase at one complete winding",
        }, { width: 2 }));
      }
      if (row.value === receipt.receiver) {
        primitives.push(labelPrimitive(`prime-succession:receiver-label:${row.value}`, [directPoints[ordinal][0], directPoints[ordinal][1], directPoints[ordinal][2] + 220], `n=${row.value} · q${row.quotient} r${row.residue}`, "primary", row, "center"));
      }
    }

    const receiverX = 0;
    const receiverFiber = [];
    for (let residue = 0; residue < axis; residue += 1) receiverFiber.push(phaseScreenPoint(phaseById.get(`phase:${axis}:${residue}`), receiverX, radius));
    receiverFiber.push(receiverFiber[0]);
    primitives.push(primitive("prime-succession:receiver-section", "polyline", "sheet", receiverFiber, "grid", {
      receiver: receipt.receiver,
      axis,
      role: "current receiver cross-section through the succession sweep",
    }, { width: 1 }));
    primitives.push(labelPrimitive("prime-succession:axis-label", [centerline[0][0], -2300, 0], `held axis p=${axis} · exact C_${axis} string`, "quiet", {
      axis,
      aperture: string.aperture,
      recurrence_period: axis,
    }));

    return {
      kind: "prime-succession-exact",
      title: `Succession sweeps the cyclotomic fiber at p=${axis}`,
      primitives,
      camera: {
        mode: "integer-axonometric",
        distance: 14000,
        target: [0, 0, 0],
        projection: "orthographic",
        orthoScale: 12500,
      },
      metadata: {
        receiver: receipt.receiver,
        axis,
        aperture: string.aperture,
        direct_rows: string.direct.length,
        conjugate_rows: string.conjugate.length,
        winding_crossings: string.direct.filter((row) => row.discriminant).map((row) => row.value),
        recurrence_period: axis,
        phase_species: `Q[zeta_${axis}]`,
        centerline_is_second_strand: false,
        duality: "cyclotomic conjugation",
        exact_series_terms: EXACT_SERIES_TERMS,
        analytical_receipt_schema: receipt.schema,
        receipt_elements: primitives.length,
      },
      analysis: receipt,
    };
  }

  function gcd(left, right) {
    let a = Math.abs(left);
    let b = Math.abs(right);
    while (b) [a, b] = [b, a % b];
    return a;
  }

  function phaseStripCoordinate(residue, modulus) {
    if (modulus <= 1) return 0;
    const centered = Exact.sub(
      Exact.mul(Exact.ratio(BigInt(residue), BigInt(modulus)), Exact.ratio(6000n, 1n)),
      Exact.ratio(3000n, 1n)
    );
    return parseInt(Exact.floor(centered).toString(), 10);
  }

  function exactWheelScene(report, stepIndex) {
    validatePrime(report);
    const steps = report.zero_relative.wheel_steps;
    const at = boundedIndex(stepIndex, steps.length);
    const step = steps[at];
    const sample = [];
    for (let residue = 0; residue < step.prior_modulus && sample.length < 24; residue += 1) {
      if (gcd(residue, step.prior_modulus) === 1) sample.push(residue);
    }
    if (step.prior_modulus === 1 && sample.length === 0) sample.push(0);
    const primitives = [
      primitive("wheel:before-axis", "line", "frames", [[-3300, 1500, 0], [3300, 1500, 0]], "primary", { modulus: step.prior_modulus }, { width: 2 }),
      primitive("wheel:after-axis", "line", "frames", [[-3300, -1500, 0], [3300, -1500, 0]], "ride", { modulus: step.successor_modulus }, { width: 2 }),
      labelPrimitive("wheel:before-label", [-3300, 1900, 0], `before · Z/${step.prior_modulus}Z`, "primary", step),
      labelPrimitive("wheel:after-label", [-3300, -1900, 0], `after · Z/${step.successor_modulus}Z`, "ride", step),
    ];
    const copies = [];
    for (const residue of sample) {
      const before = [phaseStripCoordinate(residue, step.prior_modulus), 1500, 0];
      primitives.push(primitive(`wheel:source:${residue}`, "point", "frames", [before], "primary", {
        residue,
        modulus: step.prior_modulus,
        phase: Exact.read(Exact.ratio(BigInt(residue), BigInt(step.prior_modulus || 1))),
      }, { radius: 3 }));
      for (let copy = 0; copy < step.copies; copy += 1) {
        const lifted = residue + copy * step.prior_modulus;
        const cut = lifted % step.founded_axis === 0;
        const after = [phaseStripCoordinate(lifted, step.successor_modulus), -1500, 0];
        const row = Object.freeze({
          prior_residue: residue,
          prior_phase: Exact.read(Exact.ratio(BigInt(residue), BigInt(step.prior_modulus || 1))),
          copy,
          lifted_residue: lifted,
          successor_phase: Exact.read(Exact.ratio(BigInt(lifted), BigInt(step.successor_modulus))),
          founded_axis: step.founded_axis,
          cut,
          rebase_returns: cut ? null : residue,
        });
        copies.push(row);
        primitives.push(primitive(`wheel:copy:${residue}:${copy}`, "line", "transport", [before, after], cut ? "exposed" : "ride", row, { width: cut ? 1 : 2, dash: cut ? [2, 3] : [] }));
        primitives.push(primitive(`wheel:target:${residue}:${copy}`, "point", cut ? "residual" : "transport", [after], cut ? "exposed" : "ride", row, { radius: cut ? 4 : 2 }));
      }
    }
    primitives.push(labelPrimitive("wheel:deed", [-3300, -2600, 0], `COPY ${step.copies} · CUT ${step.cuts} · JOIN ${step.joined_survivors}`, "sibling", step));
    const analysis = Object.freeze({
      schema: "soma-primorial-rebase-observer-v1",
      observer_only: true,
      step,
      exact_carrier: "integer residues and reduced phase ratios",
      projection: "ordered rational phase strips; no circle constant",
      datasets: Object.freeze({ lifted_copies: copies }),
    });
    return {
      kind: "prime-wheel-exact",
      title: `Found axis ${step.founded_axis}: exact restriction and rebase`,
      primitives,
      camera: { mode: "integer-axonometric", distance: 9000, target: [0, 0, 0], projection: "orthographic", orthoScale: 8500 },
      metadata: Object.assign({}, step, {
        sampled_prior_residues: sample,
        sample_is_receiver_restriction: sample.length < step.prior_survivors,
        recurrence_law: "each uncut lifted residue maps back to its prior residue modulo the prior primorial",
        projection: analysis.projection,
        receipt_elements: primitives.length,
      }),
      analysis,
    };
  }

  function boundedIndex(value, extent) {
    if (extent <= 0) return 0;
    const source = /^[-+]?\d+$/.test(String(value)) ? BigInt(String(value)) : 0n;
    if (source < 0n) return 0;
    if (source >= BigInt(extent)) return extent - 1;
    return parseInt(source.toString(), 10);
  }

  function parseExactRatio(value) {
    const text = String(value).trim();
    if (text.includes("/")) {
      const parts = text.split("/");
      invariant(parts.length === 2 && /^[-+]?\d+$/.test(parts[0]) && /^[-+]?\d+$/.test(parts[1]), "malformed exact ratio");
      return Exact.ratio(BigInt(parts[0]), BigInt(parts[1]));
    }
    return Exact.fromDecimal(text);
  }

  function intervalFromRead(value) {
    return Exact.interval(exactFromRead(value.lower), exactFromRead(value.upper));
  }

  function exactFactorial(value) {
    let result = 1n;
    for (let factor = 2n; factor <= value; factor += 1n) result *= factor;
    return result;
  }

  function isPrimeInteger(value) {
    if (value < 2) return false;
    for (let divisor = 2; divisor * divisor <= value; divisor += 1) {
      if (value % divisor === 0) return false;
    }
    return true;
  }

  function explicitPrimePowers(explicit) {
    validateExplicit(explicit);
    const horizon = explicit.samples[explicit.samples.length - 1].floor;
    const rows = [];
    for (let prime = 2; prime <= horizon; prime += 1) {
      if (!isPrimeInteger(prime)) continue;
      let value = prime;
      let harmonic = 1;
      while (value <= horizon) {
        rows.push({ prime, harmonic, value });
        if (value > (horizon - horizon % prime) / prime) break;
        value *= prime;
        harmonic += 1;
      }
    }
    rows.sort((left, right) => left.value - right.value || left.prime - right.prime);
    invariant(rows.length === explicit.prime_power_events.length, "derived prime-power population disagrees with the exact source extent");
    return rows.map((row, ordinal) => Object.freeze({ ...row, event: explicit.prime_power_events[ordinal] }));
  }

  function characterSeries(sheet, epsilon, gamma, termCount) {
    const lambda = Exact.complex(epsilon, gamma);
    const terms = [];
    for (let ordinal = 0n; ordinal < BigInt(termCount); ordinal += 1n) {
      const coefficient = Exact.complexScale(
        Exact.complexPower(lambda, ordinal),
        Exact.ratio(1n, exactFactorial(ordinal))
      );
      terms.push(Object.freeze({
        sheet,
        ordinal: ordinal.toString(),
        basis: ordinal === 0n ? "1" : ordinal === 1n ? "u" : `u^${ordinal}`,
        coefficient: Exact.complexRead(coefficient),
        recurrence: ordinal === 0n ? "identity" : `previous*(epsilon+i*gamma)/${ordinal}`,
      }));
    }
    return terms;
  }

  function exactAbs(value) {
    return Exact.abs(value);
  }

  function listedZeroField(zeros, pivot) {
    const pivotGamma = exactFromRead(pivot.ordinate);
    const rows = [];
    for (let epsilonStep = -4; epsilonStep <= 4; epsilonStep += 1) {
      const epsilon = Exact.ratio(BigInt(epsilonStep), 16n);
      for (let turnStep = -4; turnStep <= 4; turnStep += 1) {
        const offset = Exact.ratio(BigInt(turnStep), 1n);
        const turn = Exact.add(pivotGamma, offset);
        let nearest = null;
        let singular = false;
        for (const zero of zeros) {
          const positive = exactFromRead(zero.ordinate);
          for (const hand of [1n, -1n]) {
            const ordinate = hand === 1n ? positive : Exact.neg(positive);
            const delta = Exact.sub(turn, ordinate);
            const normSquared = Exact.add(Exact.mul(epsilon, epsilon), Exact.mul(delta, delta));
            if (Exact.compare(normSquared, Exact.ratio(0n, 1n)) === 0) {
              singular = true;
              nearest = {
                zero: zero.ordinal,
                hand: hand.toString(),
                delta: Exact.read(delta),
                norm_squared: Exact.read(normSquared),
              };
              continue;
            }
            if (!nearest || Exact.compare(normSquared, exactFromRead(nearest.norm_squared)) < 0) {
              nearest = {
                zero: zero.ordinal,
                hand: hand.toString(),
                delta: Exact.read(delta),
                norm_squared: Exact.read(normSquared),
              };
            }
          }
        }
        const nearestNorm = nearest && !singular ? exactFromRead(nearest.norm_squared) : null;
        const nearestDelta = nearest && !singular ? exactFromRead(nearest.delta) : null;
        const nearestRadialEpsilon = nearestNorm ? Exact.div(epsilon, nearestNorm) : null;
        const nearestRadialTurn = nearestNorm ? Exact.div(nearestDelta, nearestNorm) : null;
        rows.push(Object.freeze({
          epsilon_step: epsilonStep,
          turn_step: turnStep,
          epsilon: Exact.read(epsilon),
          turn_offset: Exact.read(offset),
          turn: Exact.read(turn),
          singular,
          nearest_zero: nearest,
          nearest_radial_epsilon: nearestRadialEpsilon ? Exact.read(nearestRadialEpsilon) : null,
          nearest_radial_turn: nearestRadialTurn ? Exact.read(nearestRadialTurn) : null,
          nearest_phase_epsilon: nearestRadialTurn ? Exact.read(Exact.neg(nearestRadialTurn)) : null,
          nearest_phase_turn: nearestRadialEpsilon ? Exact.read(nearestRadialEpsilon) : null,
          complete_gradient_word: `sum of ${zeros.length * 2} retained rational factor gradients; not collapsed to one denominator`,
          factor_species: `product over ${zeros.length} conjugate zero pairs; factors remain unmultiplied`,
        }));
      }
    }
    return rows;
  }

  function zetaAnalyticalReceipt(explicit, zeros, zeroIndex, sampleIndex, epsilonValue) {
    validateExplicit(explicit);
    invariant(Array.isArray(zeros) && zeros.length > 0, "Zeta analytical receipt has no certified zero testimony");
    const zeroAt = boundedIndex(zeroIndex, zeros.length);
    const sampleAt = boundedIndex(sampleIndex, explicit.samples.length);
    const pivot = zeros[zeroAt];
    const sample = explicit.samples[sampleAt];
    const epsilon = parseExactRatio(epsilonValue === undefined ? "0" : epsilonValue);
    const gamma = exactFromRead(pivot.ordinate);
    const powers = explicitPrimePowers(explicit);
    const primeLogMap = new Map();
    for (const row of powers) {
      if (!primeLogMap.has(row.prime)) primeLogMap.set(row.prime, Exact.logIntegerSeries(row.prime, EXACT_SERIES_TERMS));
    }
    const primePowerSites = powers.map((row, ordinal) => {
      const logPrime = primeLogMap.get(row.prime);
      const scale = Exact.intervalScale(intervalFromRead(logPrime.enclosure), Exact.ratio(BigInt(row.harmonic), 1n));
      const phaseCoefficient = Exact.mul(gamma, Exact.ratio(BigInt(row.harmonic), 1n));
      const normalCoefficient = Exact.mul(epsilon, Exact.ratio(BigInt(row.harmonic), 1n));
      return Object.freeze({
        ordinal,
        event: row.event,
        prime: row.prime,
        harmonic: row.harmonic,
        value: row.value,
        scale_word: row.harmonic === 1 ? `ell_${row.prime}` : `${row.harmonic}*ell_${row.prime}`,
        scale_series_id: `log:${row.prime}`,
        scale_enclosure: Exact.intervalRead(scale),
        von_mangoldt_coefficient: `ell_${row.prime}`,
        amplitude: `sqrt(1/${row.value})`,
        amplitude_squared: Exact.read(Exact.ratio(1n, BigInt(row.value))),
        zero_character: `exp((${Exact.text(epsilon)}+i*${Exact.text(gamma)})*${row.harmonic}*ell_${row.prime})`,
        normal_coefficient: Exact.read(normalCoefficient),
        phase_coefficient: Exact.read(phaseCoefficient),
      });
    });

    const sheets = [
      { id: "direct", epsilon, gamma },
      { id: "conjugate", epsilon, gamma: Exact.neg(gamma) },
      { id: "reciprocal", epsilon: Exact.neg(epsilon), gamma },
      { id: "reflected-conjugate", epsilon: Exact.neg(epsilon), gamma: Exact.neg(gamma) },
    ];
    const seriesRows = sheets.flatMap((sheet) => characterSeries(sheet.id, sheet.epsilon, sheet.gamma, EXACT_SERIES_TERMS));
    const samplePivot = Exact.fromDecimal(sample.x);
    const pivotLog = Exact.logRationalSeries(samplePivot, EXACT_SERIES_TERMS);
    const rebaseExponent = Exact.complex(Exact.neg(epsilon), Exact.neg(gamma));
    const rebaseSeries = characterSeries("receiver-rebase", rebaseExponent.re, rebaseExponent.im, EXACT_SERIES_TERMS);
    const field = listedZeroField(zeros, pivot);
    const selectedFieldSheet = field.filter((row) => row.epsilon.ratio === Exact.text(epsilon));
    const residuals = sample.residuals.map((row) => Object.freeze({
      zero_prefix: row.zero_prefix,
      lower: Exact.read(Exact.fromDecimal(row.normalized_residual.decimal[0])),
      upper: Exact.read(Exact.fromDecimal(row.normalized_residual.decimal[1])),
      source_kind: "directed decimal enclosure imported exactly as two ratios; no midpoint",
    }));
    const logRows = [...primeLogMap.entries()].map(([prime, series]) => Object.freeze({
      id: `log:${prime}`,
      prime,
      formal_basis: `ell_${prime}`,
      series,
    }));
    const sheetRows = sheets.map((sheet) => Object.freeze({
      id: sheet.id,
      epsilon: Exact.read(sheet.epsilon),
      gamma: Exact.read(sheet.gamma),
      unitary: Exact.compare(sheet.epsilon, Exact.ratio(0n, 1n)) === 0,
      character: `exp((${Exact.text(sheet.epsilon)}+i*${Exact.text(sheet.gamma)})u)`,
    }));
    return Object.freeze({
      schema: SCHEMAS.zetaObserver,
      observer_only: true,
      explicit_source_schema: explicit.schema,
      precision_source: `${explicit.precision_bits} bit directed interval testimony imported only through exact decimal endpoint ratios`,
      exact_carrier: "prime-power integers, formal logarithm bases, BigInt ratios, Gaussian-rational series coefficients, and factored zero fields",
      pivot_zero: pivot,
      receiver_pivot: Object.freeze({
        sample_ordinal: sample.ordinal,
        x: sample.x,
        exact_ratio: Exact.read(samplePivot),
        log_series: pivotLog,
      }),
      epsilon: Exact.read(epsilon),
      prime_log_basis: logRows,
      prime_power_sites: primePowerSites,
      character_sheets: sheetRows,
      character_series: seriesRows,
      receiver_rebase_series: rebaseSeries,
      listed_zero_field: Object.freeze({
        zero_pairs: zeros.length,
        grid: "epsilon=j/16, -4<=j<=4; turn=gamma_pivot+k, -4<=k<=4",
        product_form: "P_N(epsilon,t)=product_j (epsilon^2+(t-gamma_j)^2)(epsilon^2+(t+gamma_j)^2)",
        log_gradient_is_exact_rational: true,
        samples: field,
      }),
      residuals,
      construction_boundary: "close the complete prime-power and archimedean trace over an admissible test space in the unitary dual, equivalently complete Weil/Li positivity",
      datasets: Object.freeze({
        prime_power_sites: primePowerSites,
        character_sheets: sheetRows,
        character_series_terms: seriesRows,
        listed_zero_field: field,
        selected_normal_sheet: selectedFieldSheet,
        explicit_residual_intervals: residuals,
      }),
    });
  }

  function projectComplexCoefficient(coefficient, radius) {
    const real = exactFromRead(coefficient.real);
    const imaginary = exactFromRead(coefficient.imaginary);
    const norm = Exact.add(Exact.abs(real), Exact.abs(imaginary));
    if (Exact.compare(norm, Exact.ratio(0n, 1n)) === 0) return [0, 0];
    const y = Exact.floor(Exact.mul(Exact.div(real, norm), Exact.ratio(BigInt(radius), 1n)));
    const z = Exact.floor(Exact.mul(Exact.div(imaginary, norm), Exact.ratio(BigInt(radius), 1n)));
    return [parseInt(y.toString(), 10), parseInt(z.toString(), 10)];
  }

  function zetaSeriesScene(explicit, zeros, zeroIndex, sampleIndex, epsilonValue) {
    const receipt = zetaAnalyticalReceipt(explicit, zeros, zeroIndex, sampleIndex, epsilonValue);
    const primitives = [];
    const sheetRoles = new Map([
      ["direct", "primary"],
      ["conjugate", "sibling"],
      ["reciprocal", "ride"],
      ["reflected-conjugate", "found"],
    ]);
    const sheetRows = new Map();
    for (const row of receipt.character_series) {
      if (!sheetRows.has(row.sheet)) sheetRows.set(row.sheet, []);
      sheetRows.get(row.sheet).push(row);
    }
    for (const [sheet, rows] of sheetRows) {
      const points = rows.map((row) => {
        const ordinal = parseInt(row.ordinal, 10);
        const direction = projectComplexCoefficient(row.coefficient, 1250);
        return [-4800 + ordinal * 1350, 2400 + direction[0], direction[1]];
      });
      primitives.push(primitive(`zeta-series:sheet:${sheet}`, "polyline", "transport", points, sheetRoles.get(sheet), {
        sheet,
        source_terms: rows.map((row) => row.ordinal),
        relation: "retained Gaussian-rational coefficient recurrence",
        magnitude_is_not_used_for_display: true,
      }, { width: sheet === "direct" ? 3 : 2 }));
      for (const [at, row] of rows.entries()) {
        primitives.push(primitive(`zeta-series:sheet:${sheet}:term:${row.ordinal}`, "point", "contacts", [points[at]], sheetRoles.get(sheet), row, { radius: at === 0 ? 5 : 3 }));
      }
    }
    primitives.push(labelPrimitive("zeta-series:coefficient-title", [-5000, 4400, 0], "exp((epsilon+i*gamma)u) · retained coefficient strings", "quiet", {
      zero: receipt.pivot_zero,
      epsilon: receipt.epsilon,
      terms: EXACT_SERIES_TERMS,
    }));

    const powerPoints = [];
    const pointsByPrime = new Map();
    for (const row of receipt.prime_power_sites) {
      const point = [-5000 + row.ordinal * 120, -3600 + row.harmonic * 180, 0];
      powerPoints.push(point);
      if (!pointsByPrime.has(row.prime)) pointsByPrime.set(row.prime, []);
      pointsByPrime.get(row.prime).push({ row, point });
      primitives.push(primitive(`zeta-series:prime-power:${row.event}`, "point", "residual", [point], row.harmonic === 1 ? "ride" : "found", row, { radius: row.harmonic === 1 ? 2 : 4 }));
    }
    primitives.push(primitive("zeta-series:prime-power-order", "polyline", "frames", powerPoints, "axis-k", {
      order: "exact increasing prime-power value",
      source_events: receipt.prime_power_sites.map((row) => row.event),
      interpolation: "screen segment carries only adjacency in the source event order",
    }, { width: 1, dash: [2, 3] }));
    for (const [prime, rows] of pointsByPrime) {
      if (rows.length < 2) continue;
      primitives.push(primitive(`zeta-series:valuation-axis:${prime}`, "polyline", "transport", rows.map((row) => row.point), "sibling", {
        prime,
        values: rows.map((row) => row.row.value),
        relation: `powers of the same founded prime axis ${prime}`,
      }, { width: 2 }));
    }
    primitives.push(labelPrimitive("zeta-series:prime-power-title", [-5000, -4300, 0], `${receipt.prime_power_sites.length} exact prime-power sites · scale remains k*ell_p`, "quiet", {
      receiver_pivot: receipt.receiver_pivot,
      source_schema: receipt.explicit_source_schema,
    }));

    return {
      kind: "zeta-series-exact",
      title: `Prime-power scale and zero ${receipt.pivot_zero.ordinal} coefficient sheets`,
      primitives,
      camera: {
        mode: "integer-axonometric",
        distance: 16000,
        target: [0, 0, 0],
        projection: "orthographic",
        orthoScale: 14500,
      },
      metadata: {
        pivot_zero: receipt.pivot_zero.ordinal,
        gamma: receipt.pivot_zero.ordinate,
        epsilon: receipt.epsilon,
        unitary: receipt.character_sheets.every((row) => row.unitary),
        prime_power_sites: receipt.prime_power_sites.length,
        character_sheets: receipt.character_sheets.length,
        series_terms_per_sheet: EXACT_SERIES_TERMS,
        receiver_pivot: receipt.receiver_pivot.x,
        exact_carrier: receipt.exact_carrier,
        analytical_receipt_schema: receipt.schema,
        receipt_elements: primitives.length,
      },
      analysis: receipt,
    };
  }

  function cayleySpherePoint(epsilon, turn, scale) {
    const epsilonPlus = Exact.add(epsilon, scale);
    const epsilonMinus = Exact.sub(epsilon, scale);
    const denominator = Exact.add(Exact.mul(epsilonPlus, epsilonPlus), Exact.mul(turn, turn));
    invariant(Exact.compare(denominator, Exact.ratio(0n, 1n)) !== 0, "Cayley chart refuses its pole");
    const real = Exact.div(Exact.add(Exact.mul(epsilonMinus, epsilonPlus), Exact.mul(turn, turn)), denominator);
    const imaginary = Exact.div(Exact.mul(Exact.ratio(2n, 1n), Exact.mul(scale, turn)), denominator);
    const normSquared = Exact.add(Exact.mul(real, real), Exact.mul(imaginary, imaginary));
    const sphereDenominator = Exact.add(Exact.ratio(1n, 1n), normSquared);
    return {
      x: Exact.div(Exact.mul(Exact.ratio(2n, 1n), real), sphereDenominator),
      y: Exact.div(Exact.mul(Exact.ratio(2n, 1n), imaginary), sphereDenominator),
      z: Exact.div(Exact.sub(normSquared, Exact.ratio(1n, 1n)), sphereDenominator),
      cayley: Exact.complexRead(Exact.complex(real, imaginary)),
    };
  }

  function rationalSphereScreen(point, radius) {
    return [point.x, point.y, point.z].map((coordinate) => parseInt(Exact.floor(Exact.mul(coordinate, Exact.ratio(BigInt(radius), 1n))).toString(), 10));
  }

  function stereographicSpherePoint(u, v) {
    const squared = Exact.add(Exact.mul(u, u), Exact.mul(v, v));
    const denominator = Exact.add(squared, Exact.ratio(1n, 1n));
    return {
      x: Exact.div(Exact.mul(Exact.ratio(2n, 1n), u), denominator),
      y: Exact.div(Exact.mul(Exact.ratio(2n, 1n), v), denominator),
      z: Exact.div(Exact.sub(squared, Exact.ratio(1n, 1n)), denominator),
    };
  }

  function rationalSmithGrid(radius) {
    const primitives = [];
    const constants = [-2, -1, 0, 1, 2].map((value) => Exact.ratio(BigInt(value), 1n));
    for (const [hand, role] of [["u", "grid"], ["v", "quiet"]]) {
      for (const constant of constants) {
        const points = [];
        for (let step = -16; step <= 16; step += 1) {
          const moving = Exact.ratio(BigInt(step), 4n);
          const u = hand === "u" ? constant : moving;
          const v = hand === "u" ? moving : constant;
          points.push(rationalSphereScreen(stereographicSpherePoint(u, v), radius));
        }
        primitives.push(primitive(`critical:grid:${hand}:${Exact.text(constant)}`, "polyline", "sheet", points, role, {
          chart: "rational stereographic coordinate line",
          held_coordinate: hand,
          held_value: Exact.read(constant),
        }, { width: 1 }));
      }
    }
    const equator = [[-radius, 0, 0]];
    for (let step = -32; step <= 32; step += 1) {
      const parameter = Exact.ratio(BigInt(step), 8n);
      const squared = Exact.mul(parameter, parameter);
      const denominator = Exact.add(Exact.ratio(1n, 1n), squared);
      const point = {
        x: Exact.div(Exact.sub(Exact.ratio(1n, 1n), squared), denominator),
        y: Exact.div(Exact.mul(Exact.ratio(2n, 1n), parameter), denominator),
        z: Exact.ratio(0n, 1n),
      };
      equator.push(rationalSphereScreen(point, radius));
    }
    equator.push([-radius, 0, 0]);
    primitives.push(primitive("critical:unitary-equator", "polyline", "frames", equator, "ride", {
      locus: "epsilon=0",
      relation: "the Cayley unit circle becomes the stereographic equator",
      parameterization: "((1-t^2)/(1+t^2),2t/(1+t^2),0)",
    }, { width: 3 }));
    return primitives;
  }

  function criticalSmithFieldScene(zeros, explicit, zeroIndex, sampleIndex, epsilonValue) {
    const receipt = zetaAnalyticalReceipt(explicit, zeros, zeroIndex, sampleIndex, epsilonValue);
    const pivotGamma = exactFromRead(receipt.pivot_zero.ordinate);
    const radius = 3600;
    const primitives = rationalSmithGrid(radius);
    for (const zero of zeros) {
      const turn = exactFromRead(zero.ordinate);
      const sphere = cayleySpherePoint(Exact.ratio(0n, 1n), turn, pivotGamma);
      const point = rationalSphereScreen(sphere, radius);
      const selected = zero.ordinal === receipt.pivot_zero.ordinal;
      primitives.push(primitive(`critical:zero:${zero.ordinal}`, "point", "contacts", [point], selected ? "primary" : "ride", {
        zero: zero.ordinal,
        s: `1/2 + ${zero.exact_ordinate}i`,
        epsilon: "0",
        cayley: sphere.cayley,
        mapped_locus: "unitary equator",
      }, { radius: selected ? 6 : 2 }));
      if (selected) primitives.push(labelPrimitive(`critical:zero-label:${zero.ordinal}`, [point[0], point[1], point[2] + 180], `rho${zero.ordinal} · unitary pivot`, "primary", zero, "center"));
    }

    for (const row of receipt.listed_zero_field.samples) {
      const epsilon = exactFromRead(row.epsilon);
      const turn = exactFromRead(row.turn);
      const sphere = cayleySpherePoint(epsilon, turn, pivotGamma);
      const point = rationalSphereScreen(sphere, radius);
      const role = row.singular ? "found" : row.epsilon_step < 0 ? "primary" : row.epsilon_step > 0 ? "sibling" : "ride";
      primitives.push(primitive(`critical:field:${row.epsilon_step}:${row.turn_step}`, "point", "residual", [point], role, row, { radius: row.singular ? 6 : 2 }));
      if (!row.singular && row.nearest_phase_epsilon && row.nearest_phase_turn) {
        const directionEpsilon = exactFromRead(row.nearest_phase_epsilon);
        const directionTurn = exactFromRead(row.nearest_phase_turn);
        const l1 = Exact.add(Exact.abs(directionEpsilon), Exact.abs(directionTurn));
        if (Exact.compare(l1, Exact.ratio(0n, 1n)) !== 0) {
          const step = Exact.ratio(1n, 32n);
          const nextEpsilon = Exact.add(epsilon, Exact.mul(step, Exact.div(directionEpsilon, l1)));
          const nextTurn = Exact.add(turn, Exact.mul(step, Exact.div(directionTurn, l1)));
          const next = rationalSphereScreen(cayleySpherePoint(nextEpsilon, nextTurn, pivotGamma), radius);
          primitives.push(primitive(`critical:leader:${row.epsilon_step}:${row.turn_step}`, "line", "transport", [point, next], role, {
            source_sample: [row.epsilon_step, row.turn_step],
            relation: "nearest retained factor phase leader; complete gradient remains a factored sum word",
            direction_epsilon: row.nearest_phase_epsilon,
            direction_turn: row.nearest_phase_turn,
          }, { width: 2 }));
        }
      }
    }
    const selectedEpsilon = exactFromRead(receipt.epsilon);
    const selectedRole = Exact.compare(selectedEpsilon, Exact.ratio(0n, 1n)) < 0
      ? "primary"
      : Exact.compare(selectedEpsilon, Exact.ratio(0n, 1n)) > 0 ? "sibling" : "ride";
    const selectedSheetPoints = receipt.datasets.selected_normal_sheet.map((row) => rationalSphereScreen(
      cayleySpherePoint(exactFromRead(row.epsilon), exactFromRead(row.turn), pivotGamma),
      radius
    ));
    primitives.push(primitive("critical:selected-normal-sheet", "polyline", "frames", selectedSheetPoints, selectedRole, {
      epsilon: receipt.epsilon,
      ordered_turn_steps: receipt.datasets.selected_normal_sheet.map((row) => row.turn_step),
      relation: "selected exact normal sheet through the declared factored grid",
    }, { width: 4 }));
    primitives.push(labelPrimitive("critical:field-title", [-4800, 4300, 0], `rational Smith field · rho${receipt.pivot_zero.ordinal} · epsilon seam`, "quiet", {
      field: receipt.listed_zero_field.product_form,
      grid: receipt.listed_zero_field.grid,
    }));

    return {
      kind: "critical-smith-field-exact",
      title: `Unitary seam and factored zero field at rho${receipt.pivot_zero.ordinal}`,
      primitives,
      camera: {
        mode: "integer-axonometric",
        distance: 12000,
        target: [0, 0, 0],
        projection: "orthographic",
        orthoScale: 10000,
      },
      metadata: {
        pivot_zero: receipt.pivot_zero.ordinal,
        pivot_s: `1/2 + ${receipt.pivot_zero.exact_ordinate}i`,
        epsilon: receipt.epsilon,
        listed_zeros: zeros.length,
        field_samples: receipt.listed_zero_field.samples.length,
        selected_sheet_rows: receipt.datasets.selected_normal_sheet.length,
        cayley_transform: "(w-a)/(w+a) followed by rational stereographic compactification",
        critical_seam: "epsilon=0 maps exactly to the equator",
        field_status: "finite listed-zero factor field; not the completed Xi field",
        construction_boundary: receipt.construction_boundary,
        analytical_receipt_schema: receipt.schema,
        receipt_elements: primitives.length,
      },
      analysis: receipt,
    };
  }

  function criticalResidualIntervalScene(zeros, explicit, zeroIndex, sampleIndex) {
    const receipt = zetaAnalyticalReceipt(explicit, zeros, zeroIndex, sampleIndex, "0");
    const rows = receipt.residuals;
    let maximum = Exact.ratio(1n, 1n);
    for (const row of rows) {
      const lower = Exact.abs(exactFromRead(row.lower));
      const upper = Exact.abs(exactFromRead(row.upper));
      if (Exact.compare(lower, maximum) > 0) maximum = lower;
      if (Exact.compare(upper, maximum) > 0) maximum = upper;
    }
    const primitives = [
      primitive("critical-residual:zero", "line", "frames", [[-4400, 0, 0], [4400, 0, 0]], "axis-k", {
        relation: "exact zero residual axis",
      }, { width: 1 }),
    ];
    const centers = [];
    for (const [ordinal, row] of rows.entries()) {
      const x = orderedBaseCoordinate(ordinal, rows.length);
      const lower = exactFromRead(row.lower);
      const upper = exactFromRead(row.upper);
      const yLower = parseInt(Exact.floor(Exact.mul(Exact.div(lower, maximum), Exact.ratio(2600n, 1n))).toString(), 10);
      const yUpper = parseInt(Exact.ceil(Exact.mul(Exact.div(upper, maximum), Exact.ratio(2600n, 1n))).toString(), 10);
      const center = (yLower + yUpper) >> 1;
      centers.push([x, center, 0]);
      primitives.push(primitive(`critical-residual:interval:${row.zero_prefix}`, "line", "residual", [[x, yLower, 0], [x, yUpper, 0]], yUpper < 0 ? "found" : yLower > 0 ? "sibling" : "ride", row, { width: 4 }));
      primitives.push(primitive(`critical-residual:lower:${row.zero_prefix}`, "point", "contacts", [[x, yLower, 0]], "primary", { ...row, endpoint: "lower" }, { radius: 3 }));
      primitives.push(primitive(`critical-residual:upper:${row.zero_prefix}`, "point", "contacts", [[x, yUpper, 0]], "sibling", { ...row, endpoint: "upper" }, { radius: 3 }));
      primitives.push(labelPrimitive(`critical-residual:label:${row.zero_prefix}`, [x, -3200, 0], String(row.zero_prefix), "quiet", row, "center"));
    }
    primitives.push(primitive("critical-residual:order", "polyline", "transport", centers, "sibling", {
      source_prefixes: rows.map((row) => row.zero_prefix),
      relation: "display center of each exact interval only; endpoints remain the analytical object",
    }, { width: 1, dash: [2, 3] }));
    primitives.push(labelPrimitive("critical-residual:title", [-4400, 3400, 0], `x=${receipt.receiver_pivot.x} · imported directed residual ratios`, "quiet", {
      source: receipt.explicit_source_schema,
      midpoint_used: false,
    }));
    return {
      kind: "critical-residual-intervals-exact",
      title: `Exact residual intervals at x=${receipt.receiver_pivot.x}`,
      primitives,
      camera: {
        mode: "integer-axonometric",
        distance: 10000,
        target: [0, 0, 0],
        projection: "orthographic",
        orthoScale: 9500,
      },
      metadata: {
        pivot_zero: receipt.pivot_zero.ordinal,
        sample_x: receipt.receiver_pivot.x,
        residual_intervals: rows.length,
        midpoint_used: false,
        source_endpoints_imported_as_exact_ratios: true,
        construction_boundary: receipt.construction_boundary,
        analytical_receipt_schema: receipt.schema,
        receipt_elements: primitives.length,
      },
      analysis: receipt,
    };
  }

  function zetaRebaseScene(report, cylinderIndex, phaseIndex) {
    validatePrime(report);
    const zeta = report.zeta;
    const cylinderAt = boundedIndex(cylinderIndex, zeta.cylinders.length);
    const phaseAt = boundedIndex(phaseIndex, zeta.phase_lifts.length);
    const cylinder = zeta.cylinders[cylinderAt];
    const phase = zeta.phase_lifts[phaseAt];
    const primitives = [];
    const pathRows = [];
    for (const [pathAt, path] of zeta.paths.entries()) {
      let product = 1;
      const lane = pathAt === 0 ? -500 : 500;
      const points = [[-4500, -2500, lane]];
      for (const [factorAt, factor] of path.factors.entries()) {
        product *= factor;
        const point = [-4500 + (factorAt + 1) * 1050, -2500 + (factorAt + 1) * 1050, lane];
        const row = Object.freeze({
          path: pathAt,
          factor_ordinal: factorAt,
          factor,
          partial_product: product,
          formal_scale: `${zeta.sigma}*ell_${product}`,
          log_series: Exact.logIntegerSeries(BigInt(product), EXACT_SERIES_TERMS),
          endpoint_valuation: path.valuation,
        });
        pathRows.push(row);
        points.push(point);
        primitives.push(primitive(`zeta:path:${pathAt}:factor:${factorAt}`, "point", "transport", [point], pathAt === 0 ? "primary" : "sibling", row, { radius: 3 }));
        primitives.push(labelPrimitive(`zeta:path:${pathAt}:label:${factorAt}`, [point[0] + 100, point[1] + (pathAt === 0 ? 160 : -160), point[2]], `×${factor}`, pathAt === 0 ? "primary" : "sibling", row));
      }
      primitives.push(primitive(`zeta:path:${pathAt}`, "polyline", "transport", points, pathAt === 0 ? "primary" : "sibling", { path: pathAt, factors: path.factors, endpoint: path.endpoint, valuation: path.valuation, order_is_material: true }, { width: 3 }));
    }
    primitives.push(labelPrimitive("zeta:path-origin", [-4500, -3000, 0], "1 · identity", "quiet", { endpoint: 1 }));
    primitives.push(labelPrimitive("zeta:path-end", [-300, 2100, 0], `${zeta.multiplier} · same endpoint`, "ride", { endpoint: zeta.multiplier, valuation: zeta.multiplier_valuation }));

    const valuationRows = [];
    for (const [axisAt, axis] of zeta.axes.entries()) {
      const x = 900 + axisAt * 950;
      const originalExponent = cylinder.exponents[axisAt];
      const shiftedExponent = originalExponent + zeta.multiplier_valuation[axisAt];
      const original = [x, -2300 + originalExponent * 360, 0];
      const shifted = [x, -2300 + shiftedExponent * 360, 0];
      const rebased = [x, 1500 + originalExponent * 360, 0];
      const row = Object.freeze({
        prime_axis: axis,
        formal_log_basis: `ell_${axis}`,
        log_series: Exact.logIntegerSeries(BigInt(axis), EXACT_SERIES_TERMS),
        original_exponent: originalExponent,
        added_exponent: zeta.multiplier_valuation[axisAt],
        shifted_exponent: shiftedExponent,
        returned_exponent: originalExponent,
        equal: cylinder.equal,
      });
      valuationRows.push(row);
      primitives.push(primitive(`zeta:axis:${axis}`, "line", "frames", [[x, -2700, 0], [x, 3100, 0]], "grid", row, { width: 1 }));
      primitives.push(labelPrimitive(`zeta:axis-label:${axis}`, [x - 100, -3100, 0], `v_${axis}`, "quiet", row));
      primitives.push(primitive(`zeta:original:${axis}`, "point", "sheet", [original], "primary", row, { radius: 3 }));
      primitives.push(primitive(`zeta:shift:${axis}`, "line", "transport", [original, shifted], "found", row, { width: 2 }));
      primitives.push(primitive(`zeta:rebase:${axis}`, "line", "transport", [shifted, rebased], "ride", row, { width: 2, dash: [4, 3] }));
      primitives.push(primitive(`zeta:returned:${axis}`, "point", "residual", [rebased], "ride", row, { radius: 4 }));
    }

    const phaseSign = phase.t < 0 ? 1n : -1n;
    const phaseRows = [];
    const phasePoints = [];
    for (let ordinal = 0n; ordinal < BigInt(EXACT_SERIES_TERMS); ordinal += 1n) {
      const cycle = ordinal % 4n;
      const coefficient = cycle === 0n
        ? Exact.complex(Exact.ratio(1n, exactFactorial(ordinal)), Exact.ratio(0n, 1n))
        : cycle === 1n
          ? Exact.complex(Exact.ratio(0n, 1n), Exact.ratio(phaseSign, exactFactorial(ordinal)))
          : cycle === 2n
            ? Exact.complex(Exact.ratio(-1n, exactFactorial(ordinal)), Exact.ratio(0n, 1n))
            : Exact.complex(Exact.ratio(0n, 1n), Exact.ratio(-phaseSign, exactFactorial(ordinal)));
      const row = Object.freeze({
        ordinal: ordinal.toString(),
        coefficient: Exact.complexRead(coefficient),
        monomial: ordinal === 0n ? "1" : `ell_${zeta.multiplier}^${ordinal}`,
        series: `exp(${phaseSign > 0n ? "+" : "-"}i*ell_${zeta.multiplier})`,
      });
      phaseRows.push(row);
      const projected = projectComplexCoefficient(row.coefficient, 900);
      const x = 900 + parseInt(ordinal.toString(), 10) * 500;
      phasePoints.push([x, 3900 + projected[0], projected[1]]);
      primitives.push(primitive(`zeta:phase-term:${ordinal}`, "point", "contacts", [phasePoints[phasePoints.length - 1]], phase.t < 0 ? "primary" : "sibling", row, { radius: 3 }));
    }
    primitives.push(primitive("zeta:phase-series", "polyline", "transport", phasePoints, phase.t < 0 ? "primary" : "sibling", {
      exact_series: phaseRows,
      formal_log: `ell_${zeta.multiplier}`,
      log_series: Exact.logIntegerSeries(BigInt(zeta.multiplier), EXACT_SERIES_TERMS),
    }, { width: 2 }));
    primitives.push(labelPrimitive("zeta:phase-label", [900, 5400, 0], `formal amplitude character · t=${phase.t}`, phase.t < 0 ? "primary" : "sibling", phase));

    const analysis = Object.freeze({
      schema: "soma-zeta-rebase-exact-observer-v1",
      observer_only: true,
      exact_carrier: "ordered integer products, prime valuations, formal logarithm bases, and Gaussian-rational series coefficients",
      sigma: zeta.sigma,
      multiplier: zeta.multiplier,
      multiplier_log_series: Exact.logIntegerSeries(BigInt(zeta.multiplier), EXACT_SERIES_TERMS),
      cylinder_ordinal: cylinderAt,
      original_probability: cylinder.original,
      conditioned_then_rebased_probability: cylinder.conditioned_then_rebased,
      divisibility_probability: zeta.divisibility_probability,
      phase_testimony: phase,
      path_order_preserved: zeta.paths[0].factors.join(",") !== zeta.paths[1].factors.join(","),
      datasets: Object.freeze({
        ordered_path_steps: pathRows,
        valuation_rebase: valuationRows,
        phase_series_terms: phaseRows,
      }),
    });
    return {
      kind: "zeta-rebase-exact",
      title: `Condition on ${zeta.multiplier} | N, then rebase exactly`,
      primitives,
      camera: { mode: "integer-axonometric", distance: 12000, target: [0, 0, 0], projection: "orthographic", orthoScale: 12500 },
      metadata: {
        sigma: zeta.sigma,
        axes: zeta.axes,
        multiplier: zeta.multiplier,
        multiplier_valuation: zeta.multiplier_valuation,
        cylinder: cylinderAt,
        original_probability: formatRational(cylinder.original),
        returned_probability: formatRational(cylinder.conditioned_then_rebased),
        equal: cylinder.equal,
        divisibility_probability: formatRational(zeta.divisibility_probability),
        potential_shift: `${zeta.sigma}*ell_${zeta.multiplier}`,
        amplitude_scale: phase.amplitude_scale,
        phase: phase.phase,
        path_order_preserved: analysis.path_order_preserved,
        normalization_boundary: zeta.normalization_boundary,
        projection: "integer event order and valuation ranks; all logarithmic and phase content remains retained series data",
        receipt_elements: primitives.length,
      },
      analysis,
    };
  }

  function criticalReceiverScene(zeros, explicit, zeroIndex, sampleIndex) {
    return criticalSmithFieldScene(zeros, explicit, zeroIndex, sampleIndex, "0");
  }

  function cellularConstituentLabel(constituent) {
    if (!constituent) return "no cellular constituent";
    const transitions = constituent.boundaries.map((boundary) => boundary.transition).join("/");
    return `#${String(constituent.ordinal + 1).padStart(2, "0")} · wire v${constituent.source_wire_version} · g${constituent.grain} · ${constituent.axis_count} axes · ${transitions}`;
  }

  function cellularCoordinates(constituent, path) {
    const coordinates = new Map();
    if (!path || path.steps.length === 0) {
      const apex = constituent.cells.reduce((selected, cell) => !selected || cell.grain > selected.grain || (cell.grain === selected.grain && cell.layer > selected.layer) ? cell : selected, null);
      if (apex) coordinates.set(apex.ordinal, [0, 0, 0]);
      return coordinates;
    }
    const denominator = Math.max(1, path.steps.length);
    for (const [at, step] of path.steps.entries()) {
      const incidence = constituent.incidences[step.incidence];
      const from = constituent.cells[incidence.from];
      const to = constituent.cells[incidence.to];
      const startX = -4600 + parseInt((BigInt(at) * 9200n / BigInt(denominator)).toString(), 10);
      const endX = -4600 + parseInt((BigInt(at + 1) * 9200n / BigInt(denominator)).toString(), 10);
      if (!coordinates.has(from.ordinal)) {
        coordinates.set(from.ordinal, [startX, (2 * from.grain - constituent.grain) * 410, 0]);
      }
      if (!coordinates.has(to.ordinal)) {
        coordinates.set(to.ordinal, [endX, (2 * to.grain - constituent.grain) * 410, 0]);
      }
    }
    return coordinates;
  }

  function cellularIncidenceRole(incidence) {
    if (incidence.kind === "BOUNDARY") return "boundary-incidence";
    if (incidence.kind === "DEPENDENCY") return "dependency-incidence";
    return "transport-incidence";
  }

  function cellularPinRole(pin) {
    if (!pin.formed) return "open";
    return String(pin.formed.deed).startsWith("FOUND") ? "found" : "ride";
  }

  function cellularScene(input) {
    const {
      report,
      cutIndex = 0,
      constituentIndex = 0,
      boundaryIndex = 0,
      pathIndex = 0,
      side = "primary",
      layers: visibleLayers,
    } = input;
    if (!validatedCellularReports.has(report)) validateCellular(report);
    const cut = report.cuts[boundedIndex(cutIndex, report.cuts.length)];
    const constituent = cut.constituents[boundedIndex(constituentIndex, cut.constituents.length)] || null;
    const role = side === "sibling" ? "sibling" : "primary";
    const show = visibleLayers || new Set(["sheet", "transport", "frames", "residual", "contacts"]);
    if (!constituent) {
      return {
        kind: "cellular",
        title: `${humanize(cut.label)} · no cellular constituent`,
        primitives: [],
        camera: { mode: "integer-axonometric", distance: 10000, target: [0, 0, 0], projection: "orthographic", orthoScale: 10000 },
        metadata: {
          cut: cut.label,
          standing_rank: cut.standing_rank,
          scalar_standing: cut.scalar_standing.length,
          live_lineages: cut.lineages.length,
          constituents: 0,
          receipt_elements: cut.scalar_standing.length + cut.lineages.length,
          source_path: cut.source_path,
          rest_sha256: cut.rest_sha256,
        },
      };
    }

    const boundary = constituent.boundaries[boundedIndex(boundaryIndex, constituent.boundaries.length)];
    const path = boundary && boundary.paths[boundedIndex(pathIndex, boundary.paths.length)];
    const coordinates = cellularCoordinates(constituent, path);
    const activeIncidences = new Set(path ? path.steps.map((step) => step.incidence) : []);
    const activeCells = new Set();
    for (const incidenceAt of activeIncidences) {
      const incidence = constituent.incidences[incidenceAt];
      activeCells.add(incidence.from);
      activeCells.add(incidence.to);
    }
    for (const cellAt of coordinates.keys()) activeCells.add(cellAt);
    const primitives = [];
    const exposed = new Set(constituent.exposed);
    if (show.has("sheet")) {
      for (const cell of constituent.cells) {
        if (!activeCells.has(cell.ordinal) || !coordinates.has(cell.ordinal)) continue;
        primitives.push(primitive(
          `cellular:${side}:cell:${cell.ordinal}`,
          "point",
          "sheet",
          [coordinates.get(cell.ordinal)],
          role,
          { cut: cut.label, constituent: constituent.ordinal, ...cell },
          { radius: cell.grain === constituent.grain ? 4 : 1 }
        ));
      }
    }

    if (show.has("frames")) {
      for (const incidence of constituent.incidences) {
        if (!activeIncidences.has(incidence.ordinal)) continue;
        primitives.push(primitive(
          `cellular:${side}:incidence:${incidence.ordinal}`,
          "line",
          "frames",
          [coordinates.get(incidence.from), coordinates.get(incidence.to)],
          cellularIncidenceRole(incidence),
          { cut: cut.label, constituent: constituent.ordinal, ...incidence },
          { width: 1 }
        ));
      }
    }

    if (show.has("contacts")) {
      for (const incidence of constituent.incidences) {
        if (!activeIncidences.has(incidence.ordinal)) continue;
        const pin = constituent.pins[incidence.pin];
        const from = coordinates.get(incidence.from);
        const to = coordinates.get(incidence.to);
        const midpoint = from.map((value, axis) => (value + to[axis]) >> 1);
        primitives.push(primitive(
          `cellular:${side}:pin-crossing:${incidence.ordinal}`,
          "point",
          "contacts",
          [midpoint],
          cellularPinRole(pin),
          { cut: cut.label, constituent: constituent.ordinal, incidence: incidence.ordinal, pin },
          { radius: 2 }
        ));
      }
    }

    if (show.has("residual")) {
      for (const incidence of constituent.incidences) {
        if (!activeIncidences.has(incidence.ordinal) || !exposed.has(incidence.pin)) continue;
        const pin = constituent.pins[incidence.pin];
        const from = coordinates.get(incidence.from);
        const to = coordinates.get(incidence.to);
        const midpoint = from.map((value, axis) => (value + to[axis]) >> 1);
        primitives.push(primitive(
          `cellular:${side}:exposed:${incidence.ordinal}`,
          "point",
          "residual",
          [midpoint],
          "exposed",
          { cut: cut.label, constituent: constituent.ordinal, incidence: incidence.ordinal, exposed_pin: incidence.pin, pin },
          { radius: 4 }
        ));
      }
    }

    if (show.has("transport") && path) {
      for (const step of path.steps) {
        const incidence = constituent.incidences[step.incidence];
        primitives.push(primitive(
          `cellular:${side}:path:${boundary.ordinal}:${path.ordinal}:step:${step.ordinal}`,
          "line",
          "transport",
          [coordinates.get(incidence.from), coordinates.get(incidence.to)],
          role,
          { cut: cut.label, constituent: constituent.ordinal, boundary: boundary.ordinal, path: path.ordinal, incidence, step },
          { width: 3 }
        ));
      }
      const termCount = path.transport.length;
      const termPoints = path.transport.map((term, at) => [
        orderedBaseCoordinate(at, termCount),
        -3150,
        0,
      ]);
      if (termPoints.length > 1) {
        primitives.push(primitive(
          `cellular:${side}:path:${boundary.ordinal}:${path.ordinal}:term-word`,
          "polyline",
          "transport",
          termPoints,
          role,
          { cut: cut.label, constituent: constituent.ordinal, boundary: boundary.ordinal, path: path.ordinal, ordered_terms: termCount },
          { width: 1, dash: [2, 3] }
        ));
      }
      for (const [at, term] of path.transport.entries()) {
        primitives.push(primitive(
          `cellular:${side}:path:${boundary.ordinal}:${path.ordinal}:term:${term.ordinal}`,
          "point",
          "transport",
          [termPoints[at]],
          role,
          { cut: cut.label, constituent: constituent.ordinal, boundary: boundary.ordinal, path: path.ordinal, term },
          { radius: 4 }
        ));
      }
    }

    const pathSteps = constituent.boundaries.flatMap((item) => item.paths).reduce((total, item) => total + item.steps.length, 0);
    const transportTerms = constituent.boundaries.flatMap((item) => item.paths).reduce((total, item) => total + item.transport.length, 0);
    return {
      kind: "cellular",
      title: `${humanize(cut.label)} · ${cellularConstituentLabel(constituent)}`,
      primitives,
      camera: { mode: "integer-axonometric", distance: 12000, target: [0, 0, 0], projection: "orthographic", orthoScale: 12000 },
      metadata: {
        cut: cut.label,
        source_path: cut.source_path,
        rest_sha256: cut.rest_sha256,
        chronology: cut.chronology,
        standing_rank: cut.standing_rank,
        scalar_standing: cut.scalar_standing.length,
        live_lineages: cut.lineages.length,
        constituent: constituent.ordinal,
        fingerprint: constituent.fingerprint,
        grain: constituent.grain,
        axes: constituent.axis_count,
        cells: constituent.cells.length,
        incidences: constituent.incidences.length,
        pins: constituent.pins.length,
        exposed_pins: constituent.exposed.length,
        boundaries: constituent.boundaries.length,
        paths: constituent.boundaries.reduce((total, item) => total + item.paths.length, 0),
        path_steps: pathSteps,
        transport_terms: transportTerms,
        selected_boundary: boundary ? boundary.ordinal : null,
        selected_path: path ? path.ordinal : null,
        selected_transition: boundary ? boundary.transition : null,
        selected_path_folded: path ? path.interior_folded : null,
        rendered_path_cells: activeCells.size,
        rendered_path_incidences: activeIncidences.size,
        render_scope: "selected boundary path in its receiver-relative causal order; whole counts remain testimony only",
        receipt_elements: constituent.cells.length + constituent.incidences.length + constituent.pins.length + pathSteps + transportTerms,
      },
    };
  }

  function cellularComparison(left, right, boundaryIndex, pathIndex) {
    if (!left || !right) return [];
    const leftBoundary = left.boundaries[boundaryIndex] || null;
    const rightBoundary = right.boundaries[boundaryIndex] || null;
    const leftPath = leftBoundary?.paths[pathIndex] || null;
    const rightPath = rightBoundary?.paths[pathIndex] || null;
    const exactJson = (a, b) => JSON.stringify(a) === JSON.stringify(b);
    return [
      { label: "whole body", exact: left.fingerprint === right.fingerprint },
      { label: "grain", exact: left.grain === right.grain },
      { label: "axes", exact: left.axis_count === right.axis_count },
      { label: "cells", exact: exactJson(left.cells, right.cells) },
      { label: "incidence", exact: exactJson(left.incidences, right.incidences) },
      { label: "pins", exact: exactJson(left.pins, right.pins) },
      { label: "boundary", exact: exactJson(leftBoundary, rightBoundary) },
      { label: "path transport", exact: exactJson(leftPath, rightPath) },
    ];
  }

  const COMPARISON_FIELDS = Object.freeze([
    ["body", "body_exact"],
    ["radiation", "radiation_exact"],
    ["completion", "completion_exact"],
    ["construction", "construction_exact"],
    ["Mail", "mail_exact"],
    ["world before", "world_before_exact"],
    ["world after", "world_after_exact"],
    ["emitted wire", "emitted_wire_exact"],
  ]);

  function comparisonFields(comparison) {
    if (!comparison) return [];
    return COMPARISON_FIELDS.map(([label, key]) => ({ label, key, exact: comparison[key] === true }));
  }

  function comparisonVerdict(comparison) {
    if (!comparison) return { title: "Custom sibling alignment", detail: "No recorded factorial exactly matches this run and edge pairing." };
    const exact = comparisonFields(comparison).filter((field) => field.exact).map((field) => field.label);
    const changed = comparisonFields(comparison).filter((field) => !field.exact).map((field) => field.label);
    if (changed.length === 0) {
      return { title: "Exact repeat at every declared face", detail: `${exact.join(", ")} remain exact.` };
    }
    return {
      title: `${humanize(comparison.id)}`,
      detail: `${exact.length ? `${exact.join(", ")} exact; ` : ""}${changed.join(", ")} changed.`,
    };
  }

  function scenePrimitiveIds(scene) {
    return scene.primitives.map((item) => item.id);
  }

  return Object.freeze({
    SCHEMAS,
    EDGE_NAMES,
    validateAnalysis,
    validateJournal,
    validateWorld,
    validateSmith,
    validateAtlas,
    validateCellular,
    validatePrime,
    validateExplicit,
    parseZetaZeros,
    indexRuns,
    findComparison,
    findComparisonFor,
    edgeOf,
    humanize,
    runLabel,
    formatRational,
    eisensteinCartesian,
    formatEisenstein,
    somaRelativeUrl,
    stageLayers,
    transportScene,
    smithScene,
    atlasScene,
    primeReceiverRead,
    primeAnalyticalReceipt,
    primeReceiverScene: exactPrimeReceiverScene,
    primeSuccessionScene,
    wheelScene: exactWheelScene,
    zetaAnalyticalReceipt,
    zetaSeriesScene,
    zetaRebaseScene,
    criticalSmithFieldScene,
    criticalResidualIntervalScene,
    criticalReceiverScene,
    factorization,
    factorizationLabel,
    cellularConstituentLabel,
    cellularScene,
    cellularComparison,
    comparisonFields,
    comparisonVerdict,
    scenePrimitiveIds,
    signedMod,
  });
});
