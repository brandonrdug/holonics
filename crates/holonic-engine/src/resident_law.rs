//! **The resident laws — owner-local, one per kernel.** Each law carries its own species and
//! arity, names the material it reads, derives its a-priori octave bound and its shape and price,
//! states the resident ranges its kernel reads, and records its one kernel into a lane. The front
//! passage ([`crate::front_passage`]) binds occurrences to laws and consumes them once at compile;
//! nothing here is consulted while a deed runs.
//!
//! This module exists because the first form of the passage held an eleven-variant enum matched at
//! six sites — a central semantic cabinet every future architecture would have extended. A law is
//! now added by writing one type here and one kernel in `kernels/exact_resident_section.cu`; the
//! passage is untouched. `ResidentMaterial` lives here too: it is what the laws read.

use std::collections::BTreeMap;

use crate::embedding_fiber::MountedReadout;
use crate::ported_operation::OperationSpecies;
use crate::resident_section::{BandElements, Dyadic, DyadicEnclosure, Lane, LawShape, Positions, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface, SeriesAperture, StagedWords};

// ---------------------------------------------------------------------------------------------
// material
// ---------------------------------------------------------------------------------------------

/// A stored map mounted once, with the octave bound its row masses put on any contraction through
/// it — the a-priori term the deed's pricing needs before a single section exists.
pub struct MountedPopulation<'chart> {
    pub readout: MountedReadout<'chart>,
    /// Octaves of the largest row absolute mass **as a value** (aligned mass octaves plus the
    /// map's exponent), clamped at zero.
    pub mass_value_octaves: u32,
}

/// Entering codewords a runtime supplied and the mouth read from the container.
#[derive(Clone, Debug)]
pub struct EnteringRows {
    pub words: Vec<u16>,
    pub rows: usize,
    pub width: usize,
}

/// Everything a realization's laws name, mounted or read once by the caller at the apparatus
/// boundary. Nothing here computes a standing.
pub struct ResidentMaterial<'chart> {
    pub populations: BTreeMap<String, MountedPopulation<'chart>>,
    pub entering: BTreeMap<String, EnteringRows>,
    /// Band elements by name, with the greatest position they will be raised to.
    pub bands: BTreeMap<String, (BandElements<'chart>, u32)>,
    pub positions: Option<Positions<'chart>>,
    /// **Resident standings carried in from an earlier passage** — the previous layer's residual
    /// stream, a shared K/V standing — each with the a-priori octave bound it was admitted under
    /// (and measured at). Owned here: the earlier passage released them.
    pub standings: BTreeMap<String, (ResidentSection<'chart>, u32)>,
}

impl ResidentMaterial<'_> {
    pub fn empty() -> Self {
        Self { populations: BTreeMap::new(), entering: BTreeMap::new(), bands: BTreeMap::new(), positions: None, standings: BTreeMap::new() }
    }

    /// The resident octets of every mounted map, band and position — the source-map residency the
    /// deed requires.
    pub fn resident_octets(&self) -> u64 {
        self.populations.values().map(|p| p.readout.resident_octets() as u64).sum::<u64>()
            + self.bands.values().map(|(b, _)| b.resident_octets()).sum::<u64>()
            + self.positions.as_ref().map(Positions::resident_octets).unwrap_or(0)
            + self.standings.values().map(|(s, _)| s.resident_octets()).sum::<u64>()
    }
}


// ---------------------------------------------------------------------------------------------
// laws — owner-local: each one carries its species, its material, its bound, its shape, its
// footprint and its recording
// ---------------------------------------------------------------------------------------------

/// **One resident law an occurrence is bound to.** Everything the passage needs from a law is
/// asked of the law itself; nothing dispatches over a variant table. The passage consumes a law
/// once, at compile, and records its one kernel into a lane at realization.
pub trait ResidentLaw: std::fmt::Debug {
    /// The law's name, as the receipt prints it.
    fn name(&self) -> &'static str;
    /// The operation species the law realizes — checked against the diagram's declared species.
    fn species(&self) -> OperationSpecies;
    /// `(inputs, outputs)` — checked against the diagram's law.
    fn arity(&self) -> (usize, usize);
    /// The material this law names that the caller must have mounted or read, checked at compile.
    /// `Err(name)` names what is absent.
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String>;
    /// The a-priori bound on the octaves of this law's output words, from the bounds on its
    /// inputs (in input order) and the material's extents, at the declared grain `2^-F`.
    fn bound_octaves(&self, grain: ResidentGrain, inputs: &[u32], material: &ResidentMaterial<'_>) -> i64;
    /// The shape and price of this law on inputs of the given `(rows, width, octave bound)`.
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal>;
    /// The entering population this law stages on the card before the deed, if it enters one.
    fn stages(&self) -> Option<&str> {
        None
    }
    /// Beyond its inputs' sections, the resident ranges this law's kernel reads — mounted maps,
    /// gains, bands, positions, staged words. For the footprint certificate.
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)>;
    /// **The entailment of this law's parameters by the validated testimony of its occurrence** —
    /// asked at compile after the source occurrence validated every symbol, field and shape. A
    /// valid but unrelated slice must not authenticate this law: at least one resolved slice must
    /// NAME the operation, and every parameter the law holds must be entailed by a field, a shape
    /// or a slice.
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal>;
    /// Record this law's one semantic kernel into the lane, after its producers.
    #[allow(clippy::too_many_arguments)]
    fn record<'chart>(
        &self,
        surface: &ResidentSurface<'chart>,
        lane: &Lane<'_, 'chart>,
        inputs: &[&ResidentSection<'chart>],
        material: &ResidentMaterial<'chart>,
        staged: &BTreeMap<String, StagedWords<'chart>>,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal>;
}

fn ceil_log2(n: usize) -> u32 {
    if n <= 1 {
        0
    } else {
        (n - 1).ilog2() + 1
    }
}

fn map_range(map: &MountedReadout<'_>) -> (u64, u64) {
    let from = map.raw_resident();
    (from, from + map.resident_octets() as u64)
}

fn first(inputs: &[u32], i: usize) -> i64 {
    i64::from(inputs.get(i).copied().unwrap_or(0))
}

fn shape_at(inputs: &[(usize, usize, u32)], i: usize) -> (usize, usize, u32) {
    inputs.get(i).copied().unwrap_or((0, 0, 0))
}

/// Entering codewords a runtime supplied, read by the mouth and placed at the grain with an exact
/// dyadic scale. Species: construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Enter {
    pub population: String,
    pub scale: Dyadic,
}

impl ResidentLaw for Enter {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "enter"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (0, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        if material.entering.contains_key(&self.population) { Ok(()) } else { Err(self.population.clone()) }
    }
    fn bound_octaves(&self, grain: ResidentGrain, _inputs: &[u32], material: &ResidentMaterial<'_>) -> i64 {
        let f = i64::from(grain.0);
        let entering = &material.entering[&self.population];
        let mut widest = 0i64;
        for word in &entering.words {
            if let Ok(dyadic) = Dyadic::of_bfloat16_bits(*word) {
                let magnitude = i64::from(dyadic.octaves()) + i64::from(self.scale.octaves());
                let shifted = magnitude + i64::from(dyadic.exponent) + i64::from(self.scale.exponent) + f;
                widest = widest.max(shifted);
            }
        }
        widest + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, _inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let entering = &material.entering[&self.population];
        surface.shape_enter(entering.rows, entering.width, self.scale, grain)
    }
    fn stages(&self) -> Option<&str> {
        Some(&self.population)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        vec![staged[&self.population].range()]
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, _inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_enter(lane, &staged[&self.population], self.scale, out)
    }
}

/// **A resident standing carried in from an earlier passage** — the residual stream the previous
/// layer returned, or a shared key/value standing — entering this passage as a construction. It is
/// copied into the passage's own section by `section_carry` so the graph owns what it reads; no
/// octet crosses the apparatus boundary. Species: construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Standing {
    pub name: String,
}

impl ResidentLaw for Standing {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "standing"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (0, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        if material.standings.contains_key(&self.name) { Ok(()) } else { Err(self.name.clone()) }
    }
    fn bound_octaves(&self, _grain: ResidentGrain, _inputs: &[u32], material: &ResidentMaterial<'_>) -> i64 {
        i64::from(material.standings[&self.name].1)
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, _inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (section, octaves) = &material.standings[&self.name];
        surface.shape_carry(section.rows(), section.width(), *octaves)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        material.standings[&self.name].0.ranges().to_vec()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, _inputs: &[&ResidentSection<'chart>], material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_carry(lane, &material.standings[&self.name].0, out)
    }
}

/// A contraction through a mounted stored map. Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contract {
    pub population: String,
}

impl ResidentLaw for Contract {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "contract"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        if material.populations.contains_key(&self.population) { Ok(()) } else { Err(self.population.clone()) }
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0) + i64::from(material.populations[&self.population].mass_value_octaves) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        surface.shape_contract(rows, width, octaves, &material.populations[&self.population].readout)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        vec![map_range(&material.populations[&self.population].readout)]
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_contract(lane, inputs[0], &material.populations[&self.population].readout, out)
    }
}

/// The RMS rebase over runs of `group`, with the named gain or none, and the source's exact `eps`.
/// Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RmsRebase {
    pub group: usize,
    pub gain: Option<String>,
    pub eps: Dyadic,
}

impl ResidentLaw for RmsRebase {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "rms-rebase"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        match &self.gain {
            Some(gain) if !material.populations.contains_key(gain) => Err(gain.clone()),
            _ => Ok(()),
        }
    }
    fn bound_octaves(&self, grain: ResidentGrain, inputs: &[u32], material: &ResidentMaterial<'_>) -> i64 {
        let f = i64::from(grain.0);
        let gain_value = self
            .gain
            .as_ref()
            .map(|name| {
                let mounted = &material.populations[name];
                i64::from(mounted.readout.entry_octaves()) + i64::from(mounted.readout.exponent())
            })
            .unwrap_or(0);
        // |y_i| ≤ sqrt(group) · |g_i| for a point section, in the word F + log2(group)/2 + gain + 1;
        // for an interval section the root is at most 1/sqrt(eps) < 2^10, so the word is at most
        // oct + 10 + gain. The larger bounds both.
        (f + (i64::from(ceil_log2(self.group)) + 1) / 2 + gain_value.max(0) + 2).max(first(inputs, 0) + 10 + gain_value.max(0) + 1)
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        let gain = self.gain.as_ref().map(|name| &material.populations[name].readout);
        surface.shape_rms_rebase(rows, width, self.group, octaves, gain)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        self.gain.as_ref().map(|gain| vec![map_range(&material.populations[gain].readout)]).unwrap_or_default()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let gain = self.gain.as_ref().map(|name| &material.populations[name].readout);
        surface.record_rms_rebase(lane, inputs[0], self.group, gain, self.eps, shape, out)
    }
}

/// The chronology: the named band elements raised to each row's position. Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chronology {
    pub bands: String,
    pub heads: usize,
    pub head_width: usize,
}

impl ResidentLaw for Chronology {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "chronology"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, material: &ResidentMaterial<'_>) -> Result<(), String> {
        if !material.bands.contains_key(&self.bands) {
            return Err(self.bands.clone());
        }
        if material.positions.is_none() {
            return Err("positions".to_owned());
        }
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        let (elements, max_position) = &material.bands[&self.bands];
        let positions = material.positions.as_ref().ok_or(ResidentRefusal::Declaration { operation: "chronology", what: "no positions were mounted".to_owned() })?;
        surface.shape_chronology(rows, width, self.heads, self.head_width, octaves, elements, positions, *max_position)
    }
    fn reads<'chart>(&self, material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        let mut reads: Vec<(u64, u64)> = material.bands[&self.bands].0.ranges().to_vec();
        if let Some(positions) = &material.positions {
            reads.push(positions.range());
        }
        reads
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        let positions = material.positions.as_ref().ok_or(ResidentRefusal::Declaration { operation: "chronology", what: "no positions were mounted".to_owned() })?;
        surface.record_chronology(lane, inputs[0], self.heads, self.head_width, &material.bands[&self.bands].0, positions, out)
    }
}

/// The contact and carried construction over `(q, k, v)`. Species: construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contact {
    pub heads: usize,
    pub kv_heads: usize,
    pub head_width: usize,
    pub window: usize,
    pub terms: SeriesAperture,
}

impl ResidentLaw for Contact {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "contact"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (3, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 2) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, q_width, q_octaves) = shape_at(inputs, 0);
        let (_, k_width, k_octaves) = shape_at(inputs, 1);
        let (_, v_width, v_octaves) = shape_at(inputs, 2);
        surface.shape_contact(rows, q_width, k_width, v_width, self.heads, self.kv_heads, self.head_width, self.window, self.terms, grain, q_octaves, k_octaves, v_octaves)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_contact(lane, inputs[0], inputs[1], inputs[2], self.heads, self.kv_heads, self.head_width, self.window, self.terms, shape, out)
    }
}

/// The source's `gelu_pytorch_tanh` with its exact `binary64` constants. Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeluTanh {
    pub c1: Dyadic,
    pub c2: Dyadic,
    pub terms: SeriesAperture,
}

impl ResidentLaw for GeluTanh {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "gelu-tanh"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        surface.shape_gelu_tanh(rows, width, octaves, grain, self.c1, self.c2, self.terms)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_gelu_tanh(lane, inputs[0], self.c1, self.c2, self.terms, out)
    }
}

/// The pointwise product of two standings. Species: construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Hadamard;

impl ResidentLaw for Hadamard {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "hadamard"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (2, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0) + first(inputs, 1) - i64::from(grain.0) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, a) = shape_at(inputs, 0);
        surface.shape_hadamard(rows, width, a, shape_at(inputs, 1).2)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_hadamard(lane, inputs[0], inputs[1], out)
    }
}

/// The re-entry of a retained standing with a returned current. Species: construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReEntry;

impl ResidentLaw for ReEntry {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "re-entry"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Construction
    }
    fn arity(&self) -> (usize, usize) {
        (2, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0).max(first(inputs, 1)) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, a) = shape_at(inputs, 0);
        surface.shape_re_entry(rows, width, a, shape_at(inputs, 1).2)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_re_entry(lane, inputs[0], inputs[1], out)
    }
}

/// The product with an enclosed algebraic constant. Species: transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Scale {
    pub by: DyadicEnclosure,
}

impl ResidentLaw for Scale {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "scale"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Transport
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0) + i64::from(self.by.octaves()) - i64::from(self.by.grain) + 1
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        surface.shape_scale(rows, width, octaves, self.by)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_scale(lane, inputs[0], self.by, out)
    }
}

/// A declared span of columns withdrawn — the matched-sibling intervention. Species: quotient.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawColumns {
    pub from: usize,
    pub span: usize,
}

impl ResidentLaw for WithdrawColumns {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "withdraw-columns"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Quotient
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0)
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        surface.shape_withdraw_columns(rows, width, octaves, self.from, self.span)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_withdraw_columns(lane, inputs[0], self.from, self.span, out)
    }
}

/// **A control, unsound by construction**: the enclosure collapsed to a midpoint at this site.
/// Species: quotient.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CollapseControl;

impl ResidentLaw for CollapseControl {
    fn entailment(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        self.entail(validation)
    }
    fn name(&self) -> &'static str {
        "collapse-control"
    }
    fn species(&self) -> OperationSpecies {
        OperationSpecies::Quotient
    }
    fn arity(&self) -> (usize, usize) {
        (1, 1)
    }
    fn material(&self, _material: &ResidentMaterial<'_>) -> Result<(), String> {
        Ok(())
    }
    fn bound_octaves(&self, _grain: ResidentGrain, inputs: &[u32], _material: &ResidentMaterial<'_>) -> i64 {
        first(inputs, 0)
    }
    fn shape<'chart>(&self, surface: &ResidentSurface<'chart>, _grain: ResidentGrain, inputs: &[(usize, usize, u32)], _material: &ResidentMaterial<'chart>) -> Result<LawShape, ResidentRefusal> {
        let (rows, width, octaves) = shape_at(inputs, 0);
        surface.shape_collapse_control(rows, width, octaves)
    }
    fn reads<'chart>(&self, _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>) -> Vec<(u64, u64)> {
        Vec::new()
    }
    fn record<'chart>(&self, surface: &ResidentSurface<'chart>, lane: &Lane<'_, 'chart>, inputs: &[&ResidentSection<'chart>], _material: &ResidentMaterial<'chart>, _staged: &BTreeMap<String, StagedWords<'chart>>, _shape: &LawShape, out: &ResidentSection<'chart>) -> Result<(), ResidentRefusal> {
        surface.record_collapse_control(lane, inputs[0], out)
    }
}


// ---------------------------------------------------------------------------------------------
// entailment — the law's parameters are connected to the testimony that was validated, so a valid
// but unrelated slice cannot authenticate a binding
// ---------------------------------------------------------------------------------------------

use crate::source_occurrence::BindingValidation;
use num_bigint::BigInt;
use relational_geometry::Rat;

/// **What entails one law's parameters**, read off the validated testimony of its occurrence. A
/// binding is source-authenticated only when this returns: every parameter the law holds is
/// connected to a field, a shape or a slice that was itself resolved against authenticated content,
/// and at least one resolved slice NAMES the operation the law realizes. Nothing here is a name
/// match on the operation's label; it is the law's own parameters against the source's own text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawEntailment {
    pub law: &'static str,
    /// `(parameter, value as the law holds it, what entailed it)`.
    pub parameters: Vec<(String, String, String)>,
    /// The resolved slices that name the operation.
    pub naming_slices: Vec<String>,
}

/// Why a law's testimony does not entail it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntailmentRefusal {
    /// No resolved slice names the operation this law realizes — a valid but unrelated slice.
    SliceDoesNotEntail { law: &'static str, required_any_of: Vec<&'static str>, offered: Vec<String> },
    /// A parameter the law holds is entailed by no field, shape or slice of the testimony.
    ParameterUnentailed { law: &'static str, parameter: &'static str, value: String, testimony: Vec<String> },
}

impl std::fmt::Display for EntailmentRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

fn slices_of(validation: &BindingValidation) -> Vec<String> {
    validation.symbols.iter().filter_map(|symbol| symbol.slice.clone()).collect()
}

fn naming(law: &'static str, validation: &BindingValidation, required_any_of: &[&'static str]) -> Result<Vec<String>, EntailmentRefusal> {
    let slices = slices_of(validation);
    let naming: Vec<String> = slices.iter().filter(|slice| required_any_of.iter().any(|token| slice.contains(token))).cloned().collect();
    if naming.is_empty() {
        return Err(EntailmentRefusal::SliceDoesNotEntail { law, required_any_of: required_any_of.to_vec(), offered: slices });
    }
    Ok(naming)
}

fn testimony_of(validation: &BindingValidation) -> Vec<String> {
    let mut out: Vec<String> = validation.fields.iter().map(|(f, v)| format!("{f}={v}")).collect();
    out.extend(validation.shapes.iter().map(|(p, s)| format!("{p}:{s:?}")));
    out.extend(slices_of(validation));
    out
}

fn unentailed(law: &'static str, parameter: &'static str, value: impl std::fmt::Display, validation: &BindingValidation) -> EntailmentRefusal {
    EntailmentRefusal::ParameterUnentailed { law, parameter, value: value.to_string(), testimony: testimony_of(validation) }
}

/// A field whose value parses as this integer.
fn field_with_integer(validation: &BindingValidation, value: usize) -> Option<String> {
    validation.fields.iter().find(|(_, v)| v.trim().parse::<usize>().ok() == Some(value)).map(|(f, v)| format!("{f}={v}"))
}

fn field_named(validation: &BindingValidation, names: &[&str]) -> Option<(String, String)> {
    validation.fields.iter().find(|(f, _)| names.contains(&f.as_str())).cloned()
}

/// A field among `names` whose integer value is `value` — any of them, not the first named.
fn field_among(validation: &BindingValidation, names: &[&str], value: usize) -> Option<String> {
    validation.fields.iter().find(|(f, v)| names.contains(&f.as_str()) && v.trim().parse::<usize>().ok() == Some(value)).map(|(f, v)| format!("{f}={v}"))
}

/// The last attribute of a stored population's name — `self_attn.q_proj.weight` → `q_proj`.
fn attribute_of(population: &str) -> &str {
    let trimmed = population.strip_suffix(".weight").unwrap_or(population);
    trimmed.rsplit('.').next().unwrap_or(trimmed)
}

/// An exact rational from a decimal string such as `1e-06`, `0.044715`, `30.0`, `2560`.
pub fn decimal_to_rat(text: &str) -> Option<Rat> {
    let text = text.trim();
    let (mantissa, exponent) = match text.find(['e', 'E']) {
        Some(at) => (&text[..at], text[at + 1..].parse::<i32>().ok()?),
        None => (text, 0),
    };
    let negative = mantissa.starts_with('-');
    let mantissa = mantissa.trim_start_matches(['-', '+']);
    let (whole, fraction) = match mantissa.find('.') {
        Some(at) => (&mantissa[..at], &mantissa[at + 1..]),
        None => (mantissa, ""),
    };
    if whole.is_empty() && fraction.is_empty() {
        return None;
    }
    let digits = format!("{whole}{fraction}");
    if !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let numerator: BigInt = digits.parse().ok()?;
    let scale = exponent - fraction.len() as i32;
    let ten = BigInt::from(10);
    let value = if scale >= 0 {
        Rat::from_integer(numerator * num_traits::pow(ten, scale as usize))
    } else {
        Rat::new(numerator, num_traits::pow(ten, (-scale) as usize))
    };
    Some(if negative { -value } else { value })
}

/// Whether `value` (an exact dyadic) is the round-to-nearest `binary64` of `target`: the target lies
/// within half an ulp of the value, the ulp being `2^(e−52)` for a value in `[2^e, 2^(e+1))`.
fn is_nearest_binary64(value: &Dyadic, target: &Rat) -> bool {
    is_nearest_of_precision(value, target, 53)
}

/// Whether `value` is the round-to-nearest float of `precision` significant bits of `target`.
fn is_nearest_of_precision(value: &Dyadic, target: &Rat, precision: u32) -> bool {
    let v = value.value();
    if v.numer().sign() == num_bigint::Sign::NoSign {
        return false;
    }
    // the leading octave of |v|: 2^e ≤ |v| < 2^(e+1)
    let magnitude = value.significand.unsigned_abs();
    let octaves = 64 - magnitude.leading_zeros() as i32; // |sig| ∈ [2^(octaves-1), 2^octaves)
    let e = octaves - 1 + value.exponent;
    // the ulp of a value in [2^e, 2^(e+1)) with p significant bits is 2^(e−p+1); half of it is 2^(e−p)
    let half_ulp = pow2(e - precision as i32);
    let lower = &v - &half_ulp;
    let upper = &v + &half_ulp;
    lower <= *target && *target <= upper
}

fn pow2(exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(1) << exponent as usize)
    } else {
        Rat::new(BigInt::from(1), BigInt::from(1) << (-exponent) as usize)
    }
}

/// Whether an enclosure `[lo, hi]·2^-grain` encloses `target`.
fn encloses(by: &DyadicEnclosure, target: &Rat) -> bool {
    let scale = pow2(-(by.grain as i32));
    let lo = Rat::from_integer(BigInt::from(by.lo)) * &scale;
    let hi = Rat::from_integer(BigInt::from(by.hi)) * &scale;
    lo <= *target && *target <= hi
}

/// An exact rational enclosure of π by Machin's identity over two certified arctangent series —
/// `16·arctan(1/5) − 4·arctan(1/239)` — each with its alternating-tail certificate, so the
/// enclosure is certified and nothing is a float.
pub fn pi_enclosure(terms: u32) -> Option<(Rat, Rat)> {
    let a = crate::reopening::arctan_unit_fraction(5, terms).ok()?.enclosure();
    let b = crate::reopening::arctan_unit_fraction(239, terms).ok()?.enclosure();
    let sixteen = Rat::from_integer(BigInt::from(16));
    let four = Rat::from_integer(BigInt::from(4));
    // 16a − 4b: lower = 16·a.lower − 4·b.upper, upper = 16·a.upper − 4·b.lower
    Some((&sixteen * &a.lower - &four * &b.upper, &sixteen * &a.upper - &four * &b.lower))
}

impl Enter {
    /// `scale` is the `bfloat16` nearest to `√v` for a field `v` of the testimony — the source casts
    /// `hidden_size**0.5` to its weight dtype.
    fn scale_entailed_by(&self, validation: &BindingValidation) -> Option<String> {
        validation.fields.iter().find_map(|(field, value)| {
            let v = value.trim().parse::<u64>().ok()?;
            let target_square = Rat::from_integer(BigInt::from(v));
            // scale is the nearest bfloat16 (8 significant bits) to √v  ⇔  (scale − ulp/2)² ≤ v ≤ (scale + ulp/2)²
            let s = self.scale.value();
            if s.numer().sign() != num_bigint::Sign::Plus {
                return None;
            }
            let magnitude = self.scale.significand.unsigned_abs();
            let octaves = 64 - magnitude.leading_zeros() as i32;
            let e = octaves - 1 + self.scale.exponent;
            let half_ulp = pow2(e - 8); // ulp = 2^(e−7) for 8 significant bits; half of it
            let lower = &s - &half_ulp;
            let upper = &s + &half_ulp;
            (&lower * &lower <= target_square && target_square <= &upper * &upper).then(|| format!("{field}={value}: scale = the bfloat16 nearest √{v}"))
        })
    }
}

/// **The entailment of each law.** Asked by the passage at compile for every occurrence, after the
/// source occurrence validated the testimony; refuses before any pricing.
pub fn entailment_of(law: &dyn ResidentLaw, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
    law.entailment(validation)
}

impl Enter {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("enter", validation, &["embed"])?;
        let by = self.scale_entailed_by(validation).ok_or_else(|| unentailed("enter", "scale", format!("{}·2^{}", self.scale.significand, self.scale.exponent), validation))?;
        Ok(LawEntailment { law: "enter", parameters: vec![("scale".to_owned(), format!("{}·2^{}", self.scale.significand, self.scale.exponent), by), ("population".to_owned(), self.population.clone(), "the entering rows the runtime supplied under this name".to_owned())], naming_slices })
    }
}

impl Contract {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let attribute = attribute_of(&self.population).to_owned();
        let slices = slices_of(validation);
        let naming_slices: Vec<String> = slices.iter().filter(|slice| slice.contains(&attribute)).cloned().collect();
        if naming_slices.is_empty() {
            return Err(EntailmentRefusal::SliceDoesNotEntail { law: "contract", required_any_of: vec!["the population's own attribute in a resolved slice"], offered: slices });
        }
        let shape = validation.shapes.iter().find(|(p, _)| *p == self.population).ok_or_else(|| unentailed("contract", "population shape", &self.population, validation))?;
        Ok(LawEntailment { law: "contract", parameters: vec![("population".to_owned(), self.population.clone(), format!("declared shape {:?} identified in the container header", shape.1))], naming_slices })
    }
}

impl RmsRebase {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let mut naming_slices = naming("rms-rebase", validation, &["pow(2).mean", "pow(mean_squared, -0.5)"])?;
        let mut parameters = Vec::new();
        // eps: the binary64 nearest the declared decimal
        let (field, value) = field_named(validation, &["rms_norm_eps"]).ok_or_else(|| unentailed("rms-rebase", "eps", format!("{}·2^{}", self.eps.significand, self.eps.exponent), validation))?;
        let target = decimal_to_rat(&value).ok_or_else(|| unentailed("rms-rebase", "eps", value.clone(), validation))?;
        if !is_nearest_binary64(&self.eps, &target) {
            return Err(unentailed("rms-rebase", "eps", format!("{}·2^{} is not the binary64 nearest {value}", self.eps.significand, self.eps.exponent), validation));
        }
        parameters.push(("eps".to_owned(), format!("{}·2^{}", self.eps.significand, self.eps.exponent), format!("{field}={value}: the binary64 nearest the declared decimal")));
        // group: the gain's declared shape, or a field carrying the width
        match &self.gain {
            Some(gain) => {
                let attribute = attribute_of(gain).to_owned();
                let gain_slices: Vec<String> = slices_of(validation).into_iter().filter(|s| s.contains(&attribute)).collect();
                if gain_slices.is_empty() {
                    return Err(EntailmentRefusal::SliceDoesNotEntail { law: "rms-rebase", required_any_of: vec!["the gain population's own attribute in a resolved slice"], offered: slices_of(validation) });
                }
                naming_slices.extend(gain_slices);
                let shape = validation.shapes.iter().find(|(p, _)| p == gain).ok_or_else(|| unentailed("rms-rebase", "gain shape", gain, validation))?;
                if shape.1 != vec![self.group] {
                    return Err(unentailed("rms-rebase", "group", format!("{} against the gain's declared shape {:?}", self.group, shape.1), validation));
                }
                parameters.push(("group".to_owned(), self.group.to_string(), format!("{gain} declared shape {:?}", shape.1)));
                parameters.push(("gain".to_owned(), gain.clone(), "identified in the container header".to_owned()));
            }
            None => {
                let by = field_with_integer(validation, self.group).ok_or_else(|| unentailed("rms-rebase", "group", self.group, validation))?;
                parameters.push(("group".to_owned(), self.group.to_string(), by));
                parameters.push(("gain".to_owned(), "none".to_owned(), "with_scale=False in a resolved slice".to_owned()));
                if !slices_of(validation).iter().any(|s| s.contains("with_scale=False")) {
                    return Err(unentailed("rms-rebase", "gain", "none (with_scale=False not in any slice)", validation));
                }
            }
        }
        Ok(LawEntailment { law: "rms-rebase", parameters, naming_slices })
    }
}

impl Chronology {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("chronology", validation, &["rotary", "rope", "cos", "sin"])?;
        let heads_by = field_among(validation, &["num_attention_heads", "num_key_value_heads"], self.heads).ok_or_else(|| unentailed("chronology", "heads", self.heads, validation))?;
        let width_by = field_among(validation, &["head_dim", "global_head_dim"], self.head_width).ok_or_else(|| unentailed("chronology", "head_width", self.head_width, validation))?;
        Ok(LawEntailment { law: "chronology", parameters: vec![("heads".to_owned(), self.heads.to_string(), heads_by), ("head_width".to_owned(), self.head_width.to_string(), width_by), ("bands".to_owned(), self.bands.clone(), "the band elements the caller founded from the declared rope species and theta".to_owned())], naming_slices })
    }
}

impl Contact {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("contact", validation, &["attention_interface", "attn_weights", "softmax", "eager_attention_forward"])?;
        let heads_by = field_among(validation, &["num_attention_heads"], self.heads).ok_or_else(|| unentailed("contact", "heads", self.heads, validation))?;
        let kv_by = field_among(validation, &["num_key_value_heads"], self.kv_heads).ok_or_else(|| unentailed("contact", "kv_heads", self.kv_heads, validation))?;
        let width_by = field_among(validation, &["head_dim", "global_head_dim"], self.head_width).ok_or_else(|| unentailed("contact", "head_width", self.head_width, validation))?;
        let window_by = match field_named(validation, &["sliding_window"]) {
            Some((f, v)) if v.trim().parse::<usize>().ok() == Some(self.window) => format!("{f}={v}"),
            _ => match validation.fields.iter().find(|(_, v)| v == "full_attention") {
                Some((f, v)) => format!("{f}={v}: no window; the declared context bounds the reach"),
                None => return Err(unentailed("contact", "window", self.window, validation)),
            },
        };
        Ok(LawEntailment { law: "contact", parameters: vec![("heads".to_owned(), self.heads.to_string(), heads_by), ("kv_heads".to_owned(), self.kv_heads.to_string(), kv_by), ("head_width".to_owned(), self.head_width.to_string(), width_by), ("window".to_owned(), self.window.to_string(), window_by), ("terms".to_owned(), self.terms.0.to_string(), "a declared series aperture with a certified tail; apparatus, exhibited".to_owned())], naming_slices })
    }
}

impl GeluTanh {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("gelu-tanh", validation, &["act_fn", "gelu", "hidden_activation"])?;
        let activation = field_named(validation, &["hidden_activation"]).filter(|(_, v)| v == "gelu_pytorch_tanh").map(|(f, v)| format!("{f}={v}")).ok_or_else(|| unentailed("gelu-tanh", "activation", "gelu_pytorch_tanh", validation))?;
        // c2 = RN64(0.044715); c1 = RN64(√(2/π)) checked against a certified Machin enclosure of π
        let c2_target = decimal_to_rat("0.044715").expect("decimal");
        if !is_nearest_binary64(&self.c2, &c2_target) {
            return Err(unentailed("gelu-tanh", "c2", format!("{}·2^{} is not the binary64 nearest 0.044715", self.c2.significand, self.c2.exponent), validation));
        }
        let (pi_lo, pi_hi) = pi_enclosure(40).ok_or_else(|| unentailed("gelu-tanh", "c1", "π enclosure unavailable", validation))?;
        // c1 nearest √(2/π) ⇔ (c1 − u/2)² ≤ 2/π ≤ (c1 + u/2)²; with π ∈ [lo, hi]: 2/hi ≤ 2/π ≤ 2/lo,
        // so require (c1 − u/2)² ≤ 2/hi and 2/lo ≤ (c1 + u/2)² — sufficient, never assumed.
        let c1 = self.c1.value();
        let magnitude = self.c1.significand.unsigned_abs();
        let octaves = 64 - magnitude.leading_zeros() as i32;
        let e = octaves - 1 + self.c1.exponent;
        let half_ulp = pow2(e - 53);
        let lower = &c1 - &half_ulp;
        let upper = &c1 + &half_ulp;
        let two = Rat::from_integer(BigInt::from(2));
        let two_over_hi = &two / &pi_hi;
        let two_over_lo = &two / &pi_lo;
        if !(&lower * &lower <= two_over_hi && two_over_lo <= &upper * &upper) {
            return Err(unentailed("gelu-tanh", "c1", format!("{}·2^{} is not the binary64 nearest √(2/π) against the certified π enclosure", self.c1.significand, self.c1.exponent), validation));
        }
        Ok(LawEntailment { law: "gelu-tanh", parameters: vec![("activation".to_owned(), "gelu_pytorch_tanh".to_owned(), activation), ("c1".to_owned(), format!("{}·2^{}", self.c1.significand, self.c1.exponent), "the binary64 nearest √(2/π), against Machin's certified enclosure of π (40 terms)".to_owned()), ("c2".to_owned(), format!("{}·2^{}", self.c2.significand, self.c2.exponent), "the binary64 nearest 0.044715".to_owned()), ("terms".to_owned(), self.terms.0.to_string(), "a declared series aperture with a certified tail; apparatus, exhibited".to_owned())], naming_slices })
    }
}

impl Hadamard {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("hadamard", validation, &["*"])?;
        Ok(LawEntailment { law: "hadamard", parameters: Vec::new(), naming_slices })
    }
}

impl ReEntry {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("re-entry", validation, &["+"])?;
        Ok(LawEntailment { law: "re-entry", parameters: Vec::new(), naming_slices })
    }
}

impl Scale {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let slices = slices_of(validation);
        // (i) a power of a declared field: `hidden_size**-0.5` with hidden_size = v → by² ∋ 1/v
        for (field, value) in &validation.fields {
            if let Ok(v) = value.trim().parse::<u64>() {
                if slices.iter().any(|s| s.contains("**-0.5")) {
                    let target = Rat::new(BigInt::from(1), BigInt::from(v));
                    let lo = Rat::from_integer(BigInt::from(self.by.lo)) * pow2(-(self.by.grain as i32));
                    let hi = Rat::from_integer(BigInt::from(self.by.hi)) * pow2(-(self.by.grain as i32));
                    if &lo * &lo <= target && target <= &hi * &hi {
                        return Ok(LawEntailment { law: "scale", parameters: vec![("by".to_owned(), format!("[{}, {}]·2^-{}", self.by.lo, self.by.hi, self.by.grain), format!("{field}={value}: the enclosure's square encloses 1/{v}"))], naming_slices: slices.into_iter().filter(|s| s.contains("**-0.5")).collect() });
                    }
                }
            }
        }
        // (ii) `2.0**-0.5` → by² ∋ 1/2
        if slices.iter().any(|s| s.contains("2.0**-0.5")) {
            let target = Rat::new(BigInt::from(1), BigInt::from(2));
            let lo = Rat::from_integer(BigInt::from(self.by.lo)) * pow2(-(self.by.grain as i32));
            let hi = Rat::from_integer(BigInt::from(self.by.hi)) * pow2(-(self.by.grain as i32));
            if &lo * &lo <= target && target <= &hi * &hi {
                return Ok(LawEntailment { law: "scale", parameters: vec![("by".to_owned(), format!("[{}, {}]·2^-{}", self.by.lo, self.by.hi, self.by.grain), "2.0**-0.5 in a resolved slice: the enclosure's square encloses 1/2".to_owned())], naming_slices: slices.into_iter().filter(|s| s.contains("2.0**-0.5")).collect() });
            }
        }
        // (iii) a numeric literal the slice multiplies by: `y = x * 2`, `* 30.0` — the enclosure encloses it
        for slice in &slices {
            for token in slice.split(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == ',').filter(|t| !t.is_empty()) {
                if let Some(literal) = decimal_to_rat(token) {
                    if slice.contains('*') && encloses(&self.by, &literal) {
                        return Ok(LawEntailment { law: "scale", parameters: vec![("by".to_owned(), format!("[{}, {}]·2^-{}", self.by.lo, self.by.hi, self.by.grain), format!("the literal {token} in a resolved slice, enclosed"))], naming_slices: vec![slice.clone()] });
                    }
                }
            }
        }
        // (iv) a stored scalar population named in the testimony: the point enclosure is that codeword
        if let Some((population, shape)) = validation.shapes.iter().find(|(_, s)| s.is_empty() || *s == vec![1]) {
            let attribute = attribute_of(population).to_owned();
            if slices.iter().any(|s| s.contains(&attribute)) && self.by.lo == self.by.hi {
                return Ok(LawEntailment { law: "scale", parameters: vec![("by".to_owned(), format!("[{}, {}]·2^-{}", self.by.lo, self.by.hi, self.by.grain), format!("{population} declared shape {shape:?}: the stored scalar's exact codeword, read at mount"))], naming_slices: slices.into_iter().filter(|s| s.contains(&attribute)).collect() });
            }
        }
        Err(unentailed("scale", "by", format!("[{}, {}]·2^-{}", self.by.lo, self.by.hi, self.by.grain), validation))
    }
}

impl WithdrawColumns {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        if validation.interventions.is_empty() {
            return Err(unentailed("withdraw-columns", "intervention", format!("{}..{}", self.from, self.from + self.span), validation));
        }
        Ok(LawEntailment { law: "withdraw-columns", parameters: vec![("span".to_owned(), format!("{}..{}", self.from, self.from + self.span), format!("the caller's typed intervention: {}", validation.interventions.join(" | ")))], naming_slices: Vec::new() })
    }
}

impl CollapseControl {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        if validation.interventions.is_empty() {
            return Err(unentailed("collapse-control", "intervention", "collapse", validation));
        }
        Ok(LawEntailment { law: "collapse-control", parameters: vec![("control".to_owned(), "midpoint collapse".to_owned(), format!("the caller's typed intervention: {}", validation.interventions.join(" | ")))], naming_slices: Vec::new() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ported_operation::OperationSpecies;
    use crate::source_occurrence::ResolvedSymbol;

    fn validation(slices: &[&str], fields: &[(&str, &str)], shapes: &[(&str, &[usize])]) -> BindingValidation {
        BindingValidation {
            operation: "op".to_owned(),
            species: OperationSpecies::Transport,
            symbols: slices.iter().map(|s| ResolvedSymbol { symbol: format!("X.y ({s})"), path: vec!["X".into(), "y".into()], slice: Some((*s).to_owned()), line: 1 }).collect(),
            fields: fields.iter().map(|(f, v)| ((*f).to_owned(), (*v).to_owned())).collect(),
            shapes: shapes.iter().map(|(p, s)| ((*p).to_owned(), s.to_vec())).collect(),
            interventions: Vec::new(),
        }
    }

    #[test]
    fn decimals_become_exact_rationals() {
        assert_eq!(decimal_to_rat("1e-06"), Some(Rat::new(BigInt::from(1), BigInt::from(1_000_000))));
        assert_eq!(decimal_to_rat("0.044715"), Some(Rat::new(BigInt::from(44715), BigInt::from(1_000_000))));
        assert_eq!(decimal_to_rat("30.0"), Some(Rat::from_integer(BigInt::from(30))));
        assert_eq!(decimal_to_rat("2560"), Some(Rat::from_integer(BigInt::from(2560))));
        assert_eq!(decimal_to_rat("x"), None);
    }

    #[test]
    fn the_source_constants_are_entailed_exactly_and_a_drifted_one_is_not() {
        let eps = Dyadic::of_binary64_bits(0x3eb0c6f7a0b5ed8d).expect("eps");
        assert!(is_nearest_binary64(&eps, &decimal_to_rat("1e-06").unwrap()));
        assert!(!is_nearest_binary64(&eps, &decimal_to_rat("1e-05").unwrap()));
        let c2 = Dyadic::of_binary64_bits(0x3fa6e4e26d4801f7).expect("c2");
        assert!(is_nearest_binary64(&c2, &decimal_to_rat("0.044715").unwrap()));
        let drifted = Dyadic { significand: c2.significand + 1, exponent: c2.exponent };
        assert!(!is_nearest_binary64(&drifted, &decimal_to_rat("0.044715").unwrap()));
        let (lo, hi) = pi_enclosure(40).expect("pi");
        assert!(lo < hi);
        assert!(lo > decimal_to_rat("3.14159265358979").unwrap() && hi < decimal_to_rat("3.1415926535898").unwrap());
    }

    #[test]
    fn an_unrelated_slice_does_not_authenticate_and_a_related_one_does() {
        // q_proj's slice offered for the k_proj contraction refuses; its own slice entails
        let k = Contract { population: "model.language_model.layers.0.self_attn.k_proj.weight".to_owned() };
        let unrelated = validation(&["query_states = self.q_proj(hidden_states).view(hidden_shape)"], &[], &[("model.language_model.layers.0.self_attn.k_proj.weight", &[512, 2560])]);
        assert!(matches!(k.entailment(&unrelated), Err(EntailmentRefusal::SliceDoesNotEntail { .. })));
        let related = validation(&["key_states = self.k_proj(hidden_states).view(hidden_shape)"], &[], &[("model.language_model.layers.0.self_attn.k_proj.weight", &[512, 2560])]);
        assert!(k.entailment(&related).is_ok());
        // the rms rebase: eps, gain shape and the law's own slice
        let eps = Dyadic::of_binary64_bits(0x3eb0c6f7a0b5ed8d).expect("eps");
        let rebase = RmsRebase { group: 2560, gain: Some("model.language_model.layers.0.input_layernorm.weight".to_owned()), eps };
        let ok = validation(&["hidden_states = self.input_layernorm(hidden_states)", "mean_squared = hidden_states.pow(2).mean(-1, keepdim=True) + self.eps"], &[("rms_norm_eps", "1e-06")], &[("model.language_model.layers.0.input_layernorm.weight", &[2560])]);
        let entailed = rebase.entailment(&ok).expect("entailed");
        assert_eq!(entailed.parameters.len(), 3);
        let wrong_group = RmsRebase { group: 256, gain: Some("model.language_model.layers.0.input_layernorm.weight".to_owned()), eps };
        assert!(matches!(wrong_group.entailment(&ok), Err(EntailmentRefusal::ParameterUnentailed { parameter: "group", .. })));
        let wrong_eps = validation(&["hidden_states = self.input_layernorm(hidden_states)", "mean_squared = hidden_states.pow(2).mean(-1, keepdim=True) + self.eps"], &[("rms_norm_eps", "1e-05")], &[("model.language_model.layers.0.input_layernorm.weight", &[2560])]);
        assert!(matches!(rebase.entailment(&wrong_eps), Err(EntailmentRefusal::ParameterUnentailed { parameter: "eps", .. })));
        // enter: the scale is the bfloat16 nearest √hidden_size
        let enter = Enter { population: "rows".to_owned(), scale: Dyadic { significand: 101, exponent: -1 } };
        let ok = validation(&["return super().forward(input_ids) * self.embed_scale.to(self.weight.dtype)"], &[("hidden_size", "2560")], &[]);
        assert!(enter.entailment(&ok).is_ok());
        let other = validation(&["return super().forward(input_ids) * self.embed_scale.to(self.weight.dtype)"], &[("hidden_size", "2048")], &[]);
        assert!(matches!(enter.entailment(&other), Err(EntailmentRefusal::ParameterUnentailed { parameter: "scale", .. })));
        let ple = Enter { population: "rows".to_owned(), scale: Dyadic { significand: 16, exponent: 0 } };
        assert!(ple.entailment(&validation(&["return self.embed_tokens_per_layer(input_ids)"], &[("hidden_size_per_layer_input", "256")], &[])).is_ok());
        // gelu: the two constants against the declared decimal and the certified pi
        let gelu = GeluTanh { c1: Dyadic::of_binary64_bits(0x3fe9884533d43651).unwrap(), c2: Dyadic::of_binary64_bits(0x3fa6e4e26d4801f7).unwrap(), terms: SeriesAperture(14) };
        assert!(gelu.entailment(&validation(&["hidden_states = self.act_fn(hidden_states)"], &[("hidden_activation", "gelu_pytorch_tanh")], &[])).is_ok());
    }
}

impl Standing {
    pub fn entail(&self, validation: &BindingValidation) -> Result<LawEntailment, EntailmentRefusal> {
        let naming_slices = naming("standing", validation, &["decoder_layer(", "shared_kv_states", "hidden_states", "inputs_embeds", "pooler_output", "last_hidden_state"])?;
        Ok(LawEntailment { law: "standing", parameters: vec![("name".to_owned(), self.name.clone(), "the resident standing an earlier passage released under this name".to_owned())], naming_slices })
    }
}
