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
}

impl ResidentMaterial<'_> {
    pub fn empty() -> Self {
        Self { populations: BTreeMap::new(), entering: BTreeMap::new(), bands: BTreeMap::new(), positions: None }
    }

    /// The resident octets of every mounted map, band and position — the source-map residency the
    /// deed requires.
    pub fn resident_octets(&self) -> u64 {
        self.populations.values().map(|p| p.readout.resident_octets() as u64).sum::<u64>()
            + self.bands.values().map(|(b, _)| b.resident_octets()).sum::<u64>()
            + self.positions.as_ref().map(Positions::resident_octets).unwrap_or(0)
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

/// A contraction through a mounted stored map. Species: transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contract {
    pub population: String,
}

impl ResidentLaw for Contract {
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

