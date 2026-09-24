//! Ordered source entering the fixed generator machine as phase-carried moments, and the one
//! retained-comparison object of the incident body.
//!
//! Each occurrence advances every site by its declared finite action and injects its encoded
//! increment, `q⁺ ← L q⁺ + I E(u_k)` (the current carried by the step's linear part; the
//! affine translation acts on configuration only) (`MachineSourceMaps::apply`). No incident word runs
//! between occurrences. Unrolled, the accumulated field is `L^N q₀ + m` with the source moment
//! `m = Σ_k L^(N−1−k) I E(u_k)` carried to the final phase. Directed contacts and the binding's
//! declared offsets enter as one phase-weighted linear condition `c`. The nonlinear incident
//! word then acts once on `(L^N q₀ + I m, b₀; c)`.
//!
//! The moment and the standing term are separate operands. `m` and `c` are properties of the
//! source Holon and the machine phases alone; `L^N q₀` belongs to whichever standing the moment
//! meets. A retained comparison therefore keeps `(m, c)` and its declaration, fixed in `N`, and
//! nothing of the producing cut: no field source, no material view, no anchor or output. When it
//! is observed, the anchor is re-read as `L^N q₀(now) + m` and the one word is evaluated at the
//! contemporary constitution. Its adjoint returns the standing covector to that contemporary
//! `q₀` and one covector per occurrence from the composite coefficients, so no intermediate
//! state exists to retain.
//!
//! [definition] **One retained comparison** (plan phase 12a). Every outstanding comparison of the
//! incident body — a prepared boundary (legacy-slot and direct machine words), an encoded-row
//! passage or a symbol passage — is one [`RetainedComparison`]: its producing operands at the
//! boundary port, the receiver restrictions (`held`, `admitted`) and the material cut id at which
//! it was produced. It is read at the contemporary constitution (`contemporary_word`): the
//! retention law (`Holon/Retention.lean::delayed_read_eq_immediate`). The frozen producing word
//! (`\x01`) and the per-occurrence source tape (`\x02`) are decoded into it (`rest.rs`).
use super::machine_source::{GeneratorSourceClockWitness, MachineSourceMaps};
use super::machine_source_contacts::{
    GeneratorSourceContact, contact_counts, phase_weighted_source_condition, port_symbol_sums,
    pull_back_phase_weighted_source_condition, source_ports,
};
use super::*;

/// The binding, clock origin and declared relation size of one ordered source passage. Fixed
/// in the passage length: the per-edge contact relation is not retained, only how many
/// directed contacts each declared kind port pooled. Ordered offsets are owned by
/// `binding.offsets` alone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSourceMomentMeta {
    pub binding: GeneratorSourceBinding,
    pub start: u64,
    pub rows: usize,
    pub components: usize,
    /// Directed contacts pooled into each `binding.contact_kinds` port, in declared order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub contact_counts: Vec<usize>,
    /// Symbol passages: the encoder alphabet `|A|`. The passage is retained as per-symbol
    /// phase-weighted sums and read through the contemporary encoder table.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub alphabet: Option<usize>,
    /// Symbol passages: the distinct symbols present, sorted. The sums are kept for these
    /// only, so storage is `O(distinct symbols)`, not `O(|A|)`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub present_symbols: Vec<usize>,
}

/// A symbol passage as phase-weighted sums, fixed in `N`: `C` (`|A|·S` rows, `a·S + i`) with
/// `m = Σ_a C_(a,·) I E(a)`, and `D` (`P·|A|·S` rows, `(p·|A| + a)·S + i`) with
/// `c_p = Σ_a D_(p,a,·) I E(a)`.
#[derive(Clone)]
pub(crate) struct SymbolSums<'c> {
    pub(super) moment: Rc<ResidentNormalEnclosureSection<'c>>,
    pub(super) ports: Option<Rc<ResidentNormalEnclosureSection<'c>>>,
}

/// What a retained comparison keeps of its source Holon at the boundary port.
pub(crate) enum ComparisonSource<'c> {
    /// A prepared boundary as its caller supplied it (`prepare_incident_field*`): the source
    /// cells already entered at the boundary. The interior `b` is read at the contemporary field.
    Boundary(Rc<ResidentNormalEnclosure<'c>>),
    /// An encoded-row passage: the moment `m` and condition `c` as produced.
    Rows {
        moment: Rc<ResidentNormalEnclosure<'c>>,
        condition: Option<Rc<ResidentNormalEnclosureSection<'c>>>,
    },
    /// A symbol passage: its phase-weighted sums, read through the contemporary encoder.
    Symbols(SymbolSums<'c>),
}

/// What a generator word keeps of its source Holon: the declaration, the clock witnesses at
/// which the passage was read and its moment `m` on the machine boundary.
#[derive(Clone)]
pub(crate) struct GeneratorSourceMoment<'c> {
    pub(super) meta: GeneratorSourceMomentMeta,
    witnesses: Vec<GeneratorSourceClockWitness>,
    moment: Rc<ResidentNormalEnclosure<'c>>,
    /// Present for a symbol passage: the sums `m` and `c` were read from.
    symbols: Option<SymbolSums<'c>>,
}

/// The declaration of a retained ordered passage: its binding and the clock witnesses at which
/// it was read.
#[derive(Clone)]
pub(crate) struct RetainedPassage {
    meta: GeneratorSourceMomentMeta,
    witnesses: Vec<GeneratorSourceClockWitness>,
}

/// [definition] **An outstanding comparison**: its producing operands (a prepared boundary, or a
/// passage's moment/condition or symbol sums with their declaration), the receiver restrictions
/// and the material cut id it was produced at — fixed in the passage length and holding no field
/// cut, material view, anchor, solver iterate or output. It is read at the contemporary
/// constitution when observed.
pub(crate) struct RetainedComparison<'c> {
    passage: Option<RetainedPassage>,
    source: ComparisonSource<'c>,
    held: Vec<bool>,
    admitted: Vec<Vec<bool>>,
    /// Material cut id at production; the comparison is read at the contemporary one.
    epoch: u64,
}

impl<'c> RetainedComparison<'c> {
    /// The passage declaration; `None` for a prepared boundary.
    pub(super) fn meta(&self) -> Option<&GeneratorSourceMomentMeta> {
        self.passage.as_ref().map(|p| &p.meta)
    }
    pub(super) fn source(&self) -> &ComparisonSource<'c> {
        &self.source
    }
    pub(super) fn held(&self) -> &[bool] {
        &self.held
    }
    pub(super) fn admitted(&self) -> &[Vec<bool>] {
        &self.admitted
    }
    pub(super) fn epoch(&self) -> u64 {
        self.epoch
    }
    pub(super) fn is_passage(&self) -> bool {
        self.passage.is_some()
    }
}

/// A source passage accumulated through the machine's source maps without running the incident
/// word and without changing current or material: `(L^N q₀ + m) ⊕ b₀` at the contemporary
/// field, with `m` also available alone. Its receiving phases are read through the same phase
/// maps as a produced word's (`receive_moment_phases`).
pub struct GeneratorMomentHolon<'c> {
    word: Rc<IncidentWord<'c>>,
    moment: ResidentNormalEnclosure<'c>,
    rows: usize,
}

impl<'c> GeneratorMomentHolon<'c> {
    /// The accumulated joint field `(L^N q₀ + m) ⊕ b₀`, in the real-coded machine image.
    pub fn accumulated(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.word.output.view()
    }
    /// The source moment `m = Σ_k L^(N−1−k) I E(u_k)` alone, on the machine boundary.
    pub fn moment(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.moment.view()
    }
    pub fn source_rows(&self) -> usize {
        self.rows
    }
    /// Receive the accumulated Holon through ordered machine phase ports. The rows use the
    /// same receiving maps and layout as `NativeIncidentGenerated::receive_generator_phases`.
    pub fn receive_moment_phases(
        &self,
        binding: GeneratorPhaseReceiverBinding,
    ) -> Result<NativeGeneratorPhaseReception<'c>, NativeSessionError> {
        NativeIncidentGenerated {
            word: Rc::clone(&self.word),
            comparison: None,
        }
        .receive_generator_phases(binding)
    }
}


impl<'c> IncidentFieldModel<'c> {
    fn source_machine(
        &self,
    ) -> Result<
        &Rc<crate::native::field_geometry::machine::CompiledGeneratorMachine>,
        NativeSessionError,
    > {
        self.layout
            .machine
            .as_ref()
            .ok_or_else(|| invalid("ordered generator source requires its machine"))
    }

    /// Validate a moment declaration against this machine and return its clock witnesses.
    fn validate_source_meta(
        &self,
        meta: &GeneratorSourceMomentMeta,
    ) -> Result<Vec<GeneratorSourceClockWitness>, NativeSessionError> {
        let machine = self.source_machine()?;
        let witnesses = meta
            .binding
            .validate_scope(machine, meta.start, meta.rows)?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.binding.offsets)?;
        if ports.len() != self.layout.source_condition_ports {
            return Err(invalid(
                "source contrast and offset ports differ from declared machine conditions",
            ));
        }
        if meta.contact_counts.len() != meta.binding.contact_kinds.len() {
            return Err(invalid("generator source contact counts"));
        }
        if meta.components
            != meta
                .binding
                .injection_sites
                .len()
                .checked_mul(6)
                .unwrap_or(0)
        {
            return Err(invalid("generator source moment width"));
        }
        Ok(witnesses)
    }

    fn source_maps(
        &self,
        meta: &GeneratorSourceMomentMeta,
        grain: ResidentGrain,
    ) -> Result<MachineSourceMaps<'c>, NativeSessionError> {
        MachineSourceMaps::new_with_enclosure(
            self.field.surface(),
            self.source_machine()?,
            &meta.binding,
            meta.start,
            meta.rows,
            grain,
            self.spec.enclosure_propagation(),
        )
    }

    /// `P((L^N q₀ + m) ⊕ b₀)` at the supplied field: the one anchor a moment word reads.
    fn moment_anchor(
        &self,
        maps: &MachineSourceMaps<'c>,
        source: &NativeFieldCurrentSource<'c>,
        moment: &ResidentNormalEnclosure<'c>,
    ) -> Result<Rc<ResidentNormalEnclosure<'c>>, NativeSessionError> {
        let accumulated = maps.anchor(source.enclosure(), moment.view())?;
        Ok(Rc::new(
            self.project_machine(accumulated.view().as_section()?)?
                .row(0)?
                .to_owned()?,
        ))
    }

    /// A Holon carrying `P((L^N q₀ + m) ⊕ b₀)` at `source`, for reception only.
    fn moment_holon(
        &self,
        maps: &MachineSourceMaps<'c>,
        source: NativeFieldCurrentSource<'c>,
        moment: ResidentNormalEnclosure<'c>,
        rows: usize,
    ) -> Result<GeneratorMomentHolon<'c>, NativeSessionError> {
        let accumulated = self.moment_anchor(maps, &source, &moment)?;
        let held = vec![false; accumulated.view().components() / 2];
        let word = IncidentWord {
            source_moment: None,
            boundary: None,
            external_condition: None,
            machine: self.layout.machine.clone(),
            source,
            material: Vec::new(),
            output: accumulated.view().to_owned()?,
            anchor: accumulated,
            held,
            admitted: Vec::new(),
            steps: Vec::new(),
            epoch: self.epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        };
        Ok(GeneratorMomentHolon {
            word: Rc::new(word),
            moment,
            rows,
        })
    }

    /// Accumulate the passage through the source maps alone and run the incident word once.
    fn evaluate_generator_moment(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        encoded: &ResidentNormalEnclosureSection<'c>,
        binding: GeneratorSourceBinding,
        start: u64,
        contacts: &[GeneratorSourceContact],
        epoch: u64,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let meta = GeneratorSourceMomentMeta {
            contact_counts: contact_counts(&binding.contact_kinds, contacts),
            binding,
            start,
            rows: encoded.rows(),
            components: encoded.components(),
            alphabet: None,
            present_symbols: Vec::new(),
        };
        if meta.rows == 0 {
            return Err(invalid("generator source moment rows"));
        }
        let witnesses = self.validate_source_meta(&meta)?;
        let maps = self.source_maps(&meta, encoded.grain())?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.binding.offsets)?;
        let condition =
            phase_weighted_source_condition(&maps, encoded, &ports, contacts)?.map(Rc::new);
        // Ingestion reads every cell once, through its composite phase `L^(N−1−k)`.
        let moment = Rc::new(maps.moment(encoded)?);
        let anchor = self.moment_anchor(&maps, source, &moment)?;
        let held = vec![false; anchor.view().components() / 2];
        let admitted = self
            .layout
            .sites
            .iter()
            .map(|s| vec![true; s.sources.len()])
            .collect::<Vec<_>>();
        let (steps, output) = self.evaluate(
            source,
            material,
            &anchor,
            &held,
            &admitted,
            condition.as_deref(),
        )?;
        Ok(IncidentWord {
            source_moment: Some(GeneratorSourceMoment {
                meta,
                witnesses,
                moment,
                symbols: None,
            }),
            boundary: None,
            external_condition: condition,
            machine: self.layout.machine.clone(),
            source: source.retained_clone(),
            material: material.to_vec(),
            anchor,
            held,
            admitted,
            steps,
            output,
            epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        })
    }

    /// The form a comparison retains: its producing operands, never its producing cut. A
    /// passage keeps its source Holon (`m`, `c` or the symbol sums, and the declaration); a
    /// prepared word keeps the boundary its caller supplied.
    pub(super) fn retained_comparison(
        &self,
        word: &Rc<IncidentWord<'c>>,
    ) -> Result<RetainedComparison<'c>, NativeSessionError> {
        let (passage, source) = match &word.source_moment {
            None => (
                None,
                ComparisonSource::Boundary(Rc::clone(word.boundary.as_ref().ok_or_else(
                    || invalid("a received moment Holon is not a retainable comparison"),
                )?)),
            ),
            Some(moment) => (
                Some(RetainedPassage {
                    meta: moment.meta.clone(),
                    witnesses: moment.witnesses.clone(),
                }),
                match &moment.symbols {
                    Some(sums) => ComparisonSource::Symbols(sums.clone()),
                    None => ComparisonSource::Rows {
                        moment: Rc::clone(&moment.moment),
                        condition: word.external_condition.clone(),
                    },
                },
            ),
        };
        Ok(RetainedComparison {
            passage,
            source,
            held: word.held.clone(),
            admitted: word.admitted.clone(),
            epoch: word.epoch,
        })
    }

    /// Rebuild a retained comparison from its rest operands, validating its chart against this
    /// body. A passage carries its declaration; a prepared boundary carries none.
    pub(super) fn remount_comparison(
        &self,
        meta: Option<GeneratorSourceMomentMeta>,
        source: ComparisonSource<'c>,
        held: Vec<bool>,
        admitted: Vec<Vec<bool>>,
        epoch: u64,
    ) -> Result<RetainedComparison<'c>, NativeSessionError> {
        let boundary = self
            .layout
            .sites
            .len()
            .checked_mul(self.layout.width)
            .ok_or_else(|| invalid("retained comparison boundary extent"))?;
        if admitted.len() != self.layout.sites.len()
            || admitted
                .iter()
                .zip(&self.layout.sites)
                .any(|(a, site)| a.len() != site.sources.len() || !a.iter().any(|v| *v))
        {
            return Err(invalid("retained comparison admitted contacts"));
        }
        let Some(meta) = meta else {
            let ComparisonSource::Boundary(prepared) = &source else {
                return Err(invalid("a passage comparison requires its declaration"));
            };
            if prepared.view().components() != boundary
                || held.len() < boundary / 2
                || held[boundary / 2..].iter().any(|v| *v)
            {
                return Err(invalid("retained boundary comparison chart"));
            }
            return Ok(RetainedComparison {
                passage: None,
                source,
                held,
                admitted,
                epoch,
            });
        };
        let witnesses = self.validate_source_meta(&meta)?;
        let ports = self.layout.source_condition_ports;
        let s = meta.binding.injection_sites.len();
        let chart = match (&source, meta.alphabet) {
            (ComparisonSource::Rows { moment, condition }, None) => {
                moment.view().components() == boundary
                    && (ports == 0) == condition.is_none()
                    && condition.as_ref().is_none_or(|c| {
                        c.rows() == self.layout.sites.len()
                            && c.components() == self.layout.width * ports
                    })
            }
            (ComparisonSource::Symbols(sums), Some(alphabet)) => {
                let present = &meta.present_symbols;
                let distinct = present.len();
                !present.is_empty()
                    && present.windows(2).all(|w| w[0] < w[1])
                    && present.iter().all(|a| *a < alphabet)
                    && sums.moment.rows() == distinct * s
                    && (ports == 0) == sums.ports.is_none()
                    && sums
                        .ports
                        .as_ref()
                        .is_none_or(|d| d.rows() == ports * distinct * s)
            }
            _ => false,
        };
        if !chart || held.iter().any(|v| *v) {
            return Err(invalid("generator moment comparison chart"));
        }
        Ok(RetainedComparison {
            passage: Some(RetainedPassage { meta, witnesses }),
            source,
            held,
            admitted,
            epoch,
        })
    }

    /// Read a symbol passage's `m` and `c` through the table `E` (`|A| × 6S`).
    fn read_symbol_sums(
        &self,
        maps: &MachineSourceMaps<'c>,
        meta: &GeneratorSourceMomentMeta,
        sums: &SymbolSums<'c>,
        table: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<
        (
            Rc<ResidentNormalEnclosure<'c>>,
            Option<Rc<ResidentNormalEnclosureSection<'c>>>,
        ),
        NativeSessionError,
    > {
        if Some(table.rows()) != meta.alphabet || table.components() != meta.components {
            return Err(invalid(
                "generator encoder table differs from the passage alphabet",
            ));
        }
        let present = &meta.present_symbols;
        let moment = Rc::new(maps.symbol_moment(table, &sums.moment, present)?);
        let condition = sums
            .ports
            .as_ref()
            .map(|d| {
                maps.carry_symbol_table(table, d, self.layout.source_condition_ports, present)
                    .map(Rc::new)
            })
            .transpose()?;
        Ok((moment, condition))
    }

    /// Accumulate a symbol passage through per-symbol sums read at the table `E` and run the
    /// incident word once.
    fn evaluate_generator_symbols(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        table: &ResidentNormalEnclosureSection<'c>,
        symbols: &[usize],
        binding: GeneratorSourceBinding,
        start: u64,
        contacts: &[GeneratorSourceContact],
        epoch: u64,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let meta = GeneratorSourceMomentMeta {
            contact_counts: contact_counts(&binding.contact_kinds, contacts),
            binding,
            start,
            rows: symbols.len(),
            components: table.components(),
            alphabet: Some(table.rows()),
            present_symbols: super::machine_source::present_symbols(symbols),
        };
        if meta.rows == 0 {
            return Err(invalid("generator source moment rows"));
        }
        let witnesses = self.validate_source_meta(&meta)?;
        let sums = self.symbol_sums(&meta, symbols, contacts, table.grain())?;
        let maps = self.source_maps(&meta, table.grain())?;
        let (moment, condition) = self.read_symbol_sums(&maps, &meta, &sums, table)?;
        let anchor = self.moment_anchor(&maps, source, &moment)?;
        let held = vec![false; anchor.view().components() / 2];
        let admitted = self
            .layout
            .sites
            .iter()
            .map(|s| vec![true; s.sources.len()])
            .collect::<Vec<_>>();
        let (steps, output) = self.evaluate(
            source,
            material,
            &anchor,
            &held,
            &admitted,
            condition.as_deref(),
        )?;
        Ok(IncidentWord {
            source_moment: Some(GeneratorSourceMoment {
                meta,
                witnesses,
                moment,
                symbols: Some(sums),
            }),
            boundary: None,
            external_condition: condition,
            machine: self.layout.machine.clone(),
            source: source.retained_clone(),
            material: material.to_vec(),
            anchor,
            held,
            admitted,
            steps,
            output,
            epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        })
    }

    /// The per-symbol sums `C` and per-port sums `D` of a symbol passage, mounted at `grain`.
    fn symbol_sums(
        &self,
        meta: &GeneratorSourceMomentMeta,
        symbols: &[usize],
        contacts: &[GeneratorSourceContact],
        grain: ResidentGrain,
    ) -> Result<SymbolSums<'c>, NativeSessionError> {
        let alphabet = meta
            .alphabet
            .ok_or_else(|| invalid("symbol passage alphabet"))?;
        let maps = self.source_maps(meta, grain)?;
        let (present, sums) = maps.symbol_moment_sums(symbols, alphabet)?;
        if present != meta.present_symbols {
            return Err(invalid(
                "symbol passage presence differs from its declaration",
            ));
        }
        let moment = maps.mount_symbol_sums(&sums, grain)?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.binding.offsets)?;
        let ports = if ports.is_empty() {
            if !contacts.is_empty() {
                return Err(invalid("source contacts require condition ports"));
            }
            None
        } else {
            Some(maps.mount_symbol_sums(
                &port_symbol_sums(&maps, symbols, &present, alphabet, &ports, contacts)?,
                grain,
            )?)
        };
        Ok(SymbolSums { moment, ports })
    }

    /// The one incident word of a retained comparison at the contemporary constitution. A
    /// prepared boundary is read as `P(boundary ⊕ b₀(now))`, exactly as `prepare_incident_field`
    /// reads a fresh boundary. A passage's anchor is re-read as `P((L^N q₀(now) + m) ⊕ b₀(now))`
    /// and a symbol passage re-reads `m` and `c` through the supplied contemporary encoder table,
    /// so `q₀`, `M`, `E` are all read at one cut. The word is evaluated through the contemporary
    /// field and material; its epoch is the contemporary material cut.
    pub(super) fn contemporary_word(
        &mut self,
        comparison: &RetainedComparison<'c>,
        table: Option<&ResidentNormalEnclosureSection<'c>>,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let passage = match (&comparison.passage, &comparison.source) {
            (None, ComparisonSource::Boundary(boundary)) => {
                if table.is_some() {
                    return Err(invalid(
                        "a prepared-boundary comparison has no symbol sums to read a table through",
                    ));
                }
                let width = boundary.view().components() / 2;
                if comparison.held.len() < width {
                    return Err(invalid(
                        "contemporary field differs from the comparison chart",
                    ));
                }
                let boundary = Rc::clone(boundary);
                return self.word_at(
                    boundary.view(),
                    &comparison.held[..width],
                    comparison.admitted.clone(),
                );
            }
            (Some(passage), ComparisonSource::Rows { .. } | ComparisonSource::Symbols(_)) => {
                passage.clone()
            }
            _ => return Err(invalid("retained comparison source/declaration kind")),
        };
        let source = self.field.read_current_source()?;
        let joint = source.boundary_components() + source.internal_components();
        if comparison.held.len() != joint / 2 {
            return Err(invalid(
                "contemporary field differs from the comparison chart",
            ));
        }
        let material = self
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let grain = source.enclosure().grain();
        let maps = self.source_maps(&passage.meta, grain)?;
        let (moment, condition, symbols) = match (&comparison.source, table) {
            (ComparisonSource::Rows { moment, condition }, None) => {
                (Rc::clone(moment), condition.clone(), None)
            }
            (ComparisonSource::Symbols(sums), Some(table)) => {
                let (moment, condition) =
                    self.read_symbol_sums(&maps, &passage.meta, sums, table)?;
                (moment, condition, Some(sums.clone()))
            }
            (ComparisonSource::Symbols(_), None) => {
                return Err(invalid(
                    "a symbol comparison is read through the contemporary encoder table: use contemporary_symbol_comparison",
                ));
            }
            (ComparisonSource::Rows { .. } | ComparisonSource::Boundary(_), Some(_)) => {
                return Err(invalid(
                    "an encoded-row comparison has no symbol sums to read a table through",
                ));
            }
            (ComparisonSource::Boundary(_), None) => {
                return Err(invalid("retained comparison source/declaration kind"));
            }
        };
        let anchor = self.moment_anchor(&maps, &source, &moment)?;
        let (steps, output) = self.evaluate(
            &source,
            &material,
            &anchor,
            &comparison.held,
            &comparison.admitted,
            condition.as_deref(),
        )?;
        Ok(IncidentWord {
            source_moment: Some(GeneratorSourceMoment {
                meta: passage.meta,
                witnesses: passage.witnesses,
                moment,
                symbols,
            }),
            boundary: None,
            external_condition: condition,
            machine: self.layout.machine.clone(),
            source,
            material,
            anchor,
            held: comparison.held.clone(),
            admitted: comparison.admitted.clone(),
            steps,
            output,
            epoch: self.epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        })
    }

    pub(super) fn contemporary_comparison_word(
        &mut self,
        id: u64,
        table: Option<&ResidentNormalEnclosureSection<'c>>,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let comparison = Rc::clone(
            self.comparisons
                .get(&id)
                .ok_or_else(|| invalid("unknown incident comparison"))?,
        );
        self.contemporary_word(&comparison, table)
    }

    /// A retained prepared-boundary comparison read at one contemporary cut through a boundary
    /// its source owner supplies again (for example re-encoded through its contemporary encoder
    /// and the current boundary). The receiver restrictions are the retained ones; `held` must
    /// equal them.
    pub(super) fn contemporary_boundary_word(
        &mut self,
        id: u64,
        boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let comparison = Rc::clone(
            self.comparisons
                .get(&id)
                .ok_or_else(|| invalid("unknown incident comparison"))?,
        );
        let ComparisonSource::Boundary(retained) = &comparison.source else {
            return Err(invalid(
                "a passage comparison is re-read from its moment, not a supplied boundary",
            ));
        };
        let width = retained.view().components() / 2;
        if boundary.components() != retained.view().components()
            || held.len() != width
            || comparison.held[..width] != *held
        {
            return Err(invalid(
                "supplied boundary differs from the retained comparison chart",
            ));
        }
        self.word_at(boundary, held, comparison.admitted.clone())
    }


    /// The one word's adjoint, then the standing adjoint `(L^N)*` to the `q₀` the word read,
    /// one covector per occurrence `I* (L^(N−1−k))* g` and the phase-weighted condition
    /// transpose. `contacts` is the declared per-edge relation of the passage, supplied by the
    /// caller that owns it; its per-kind counts must equal the retained ones.
    pub(super) fn pull_back_with_contacts(
        &self,
        word: &IncidentWord<'c>,
        covector: ResidentNormalEnclosureView<'_, 'c>,
        contacts: &[GeneratorSourceContact],
    ) -> Result<IncidentPullback<'c>, NativeSessionError> {
        let Some(moment) = &word.source_moment else {
            if !contacts.is_empty() {
                return Err(invalid(
                    "source contacts supplied to a word without a source",
                ));
            }
            return self.pull_back_word(word, covector);
        };
        let meta = &moment.meta;
        if moment.symbols.is_some() {
            if !contacts.is_empty()
                && contact_counts(&meta.binding.contact_kinds, contacts) != meta.contact_counts
            {
                return Err(invalid(
                    "supplied source contacts differ from the symbol passage",
                ));
            }
        } else if contact_counts(&meta.binding.contact_kinds, contacts) != meta.contact_counts {
            return Err(invalid(
                "the generator comparison pooled directed source contacts; supply the same declared relation (per-kind counts differ)",
            ));
        }
        let mut returned = self.pull_back_word(word, covector)?;
        let maps = self.source_maps(meta, word.anchor.view().grain())?;
        // g_m: the covector at the accumulated anchor, before the standing adjoint.
        let moment_covector = returned.anchor.view().to_owned()?;
        let gradient = maps.pull_back_standing(returned.anchor.view())?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.binding.offsets)?;
        let condition = if ports.is_empty() {
            None
        } else {
            Some(
                returned
                    .external_covector
                    .take()
                    .ok_or_else(|| invalid("source condition covector absent"))?,
            )
        };
        match &moment.symbols {
            Some(sums) => {
                let alphabet = meta
                    .alphabet
                    .ok_or_else(|| invalid("symbol passage alphabet"))?;
                let mut table_return = maps.pull_back_symbol_moment(
                    moment_covector.view(),
                    &sums.moment,
                    &meta.present_symbols,
                    alphabet,
                )?;
                if let (Some(condition), Some(d)) = (&condition, &sums.ports) {
                    table_return = table_return.sum_same_shape(&maps.pull_back_symbol_table(
                        condition,
                        d,
                        ports.len(),
                        &meta.present_symbols,
                        alphabet,
                    )?)?;
                }
                returned.symbol_covector = Some(table_return);
            }
            None => {
                let mut source_return = maps.pull_back_moment(moment_covector.view())?;
                if let Some(condition) = &condition {
                    source_return = source_return.sum_same_shape(
                        &pull_back_phase_weighted_source_condition(
                            &maps, condition, &ports, contacts,
                        )?,
                    )?;
                }
                returned.source_covector = Some(source_return);
            }
        }
        returned.moment_covector = Some(moment_covector);
        returned.condition_covector = condition;
        returned.anchor = gradient;
        Ok(returned)
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Prepare a complete ordered source passage without changing current or material.
    /// `encoded` has one original complex source row per occurrence. Its count changes the
    /// ingestion reads and the returned source covector, never the machine topology or the
    /// retained comparison. Ordered offsets are `binding.offsets`. Publication uses the
    /// ordinary incident transaction.
    pub fn prepare_generator_episode(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
        start: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid(
                "generator source episode requires its incident body",
            ));
        };
        let source = model.field.read_current_source()?;
        let material = model
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let word = model.evaluate_generator_moment(
            &source,
            &material,
            &encoded,
            binding,
            start,
            &contacts,
            model.epoch,
        )?;
        Ok(NativeIncidentGenerated {
            word: Rc::new(word),
            comparison: None,
        })
    }

    /// Compatibility entry: the offsets are owned by `binding.offsets`; a different separate
    /// list is refused rather than silently preferred.
    pub fn prepare_generator_episode_with_offsets(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
        offsets: Vec<usize>,
        start: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        if offsets != binding.offsets {
            return Err(invalid(
                "generator source offsets are owned by the binding; the separate list differs",
            ));
        }
        self.prepare_generator_episode(encoded, binding, start, contacts)
    }

    /// The word-free moment reading of an encoded passage through the same source maps (not the
    /// target Holon: see `evaluate_target_holon`), without changing current, material or state:
    /// `(L^N q₀ + m) ⊕ b₀` at the contemporary field, projected to the real-coded image. The
    /// clock origin is event 0 of the binding; `start` only names witnesses, not the maps.
    pub fn accumulate_generator_moment(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: &GeneratorSourceBinding,
    ) -> Result<GeneratorMomentHolon<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("generator moment requires its incident body"));
        };
        let machine = Rc::clone(model.source_machine()?);
        let rows = encoded.rows();
        binding.validate_scope(&machine, 0, rows)?;
        let source = model.field.read_current_source()?;
        let maps = MachineSourceMaps::new_with_enclosure(
            model.field.surface(),
            &machine,
            binding,
            0,
            rows,
            encoded.grain(),
            model.spec.enclosure_propagation(),
        )?;
        let moment = maps.moment(&encoded)?;
        model.moment_holon(&maps, source, moment, rows)
    }

    /// The target Holon of retained symbol comparison `id`: the target passage evaluated
    /// through the same machine at the same contemporary cut as `contemporary_symbol_comparison`
    /// — the same current `q₀`, reaction material, contact amplitudes, solver and `ρ` — with
    /// the produced passage's binding and clock origin, through the same encoder `table`, and
    /// received through `receiver`. It is one full incident word, not a word-free moment.
    /// Nothing is committed, retained or published.
    pub fn evaluate_target_holon(
        &mut self,
        id: u64,
        table: &Rc<ResidentNormalEnclosureSection<'c>>,
        target: &[usize],
        contacts: Vec<GeneratorSourceContact>,
        receiver: GeneratorPhaseReceiverBinding,
    ) -> Result<NativeGeneratorPhaseReception<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("target Holon requires its incident body"));
        };
        let meta = model
            .comparisons
            .get(&id)
            .and_then(|c| c.meta())
            .ok_or_else(|| invalid("unknown generator moment comparison"))?
            .clone();
        if meta.alphabet != Some(table.rows()) {
            return Err(invalid(
                "target Holon requires the symbol comparison's encoder alphabet",
            ));
        }
        let source = model.field.read_current_source()?;
        let material = model
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let word = model.evaluate_generator_symbols(
            &source,
            &material,
            table,
            target,
            meta.binding,
            meta.start,
            &contacts,
            model.epoch,
        )?;
        NativeIncidentGenerated {
            word: Rc::new(word),
            comparison: None,
        }
        .receive_generator_phases(receiver)
    }

    /// Receive a moment Holon through ordered machine phase ports.
    pub fn receive_moment_phases(
        &self,
        holon: &GeneratorMomentHolon<'c>,
        binding: GeneratorPhaseReceiverBinding,
    ) -> Result<NativeGeneratorPhaseReception<'c>, NativeSessionError> {
        holon.receive_moment_phases(binding)
    }

    /// A retained comparison read at the contemporary constitution: one incident word through
    /// the current field and material, on `P(boundary ⊕ b₀(now))` for a prepared boundary and on
    /// `P((L^N q₀(now) + m) ⊕ b₀(now); c)` for an encoded-row passage. Receive, compare and pull
    /// back this word to stay at one cut. A delayed comparison read here equals an immediate one
    /// produced from the same operands at this constitution, number for number.
    pub fn contemporary_incident_comparison(
        &mut self,
        id: u64,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident comparison requires its model chart"));
        };
        Ok(NativeIncidentGenerated {
            word: Rc::new(model.contemporary_comparison_word(id, None)?),
            comparison: Some(id),
        })
    }

    /// A retained symbol-passage comparison read at one contemporary cut: `m` and `c` are
    /// re-read from its per-symbol sums through `table` (the encoder `E_now`, `|A| × 6S`),
    /// the anchor at `L^N q₀(now)`, and the one word at the current field and material.
    pub fn contemporary_symbol_comparison(
        &mut self,
        id: u64,
        table: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident comparison requires its model chart"));
        };
        Ok(NativeIncidentGenerated {
            word: Rc::new(model.contemporary_comparison_word(id, Some(table))?),
            comparison: Some(id),
        })
    }

    /// Prepare a symbol passage `u_0..u_(N−1)` (indices into `table`, `|A| × 6S`) without
    /// changing current or material. The passage enters through per-symbol sums
    /// `C_(a,i) = Σ_(k:u_k=a) L_(s_i)^(N−1−k)` and per-port sums `D_(p,a,i)`; a retained
    /// comparison keeps those sums only (fixed in `N`) and is read at the contemporary encoder.
    pub fn prepare_generator_symbol_episode(
        &mut self,
        table: Rc<ResidentNormalEnclosureSection<'c>>,
        symbols: &[usize],
        binding: GeneratorSourceBinding,
        start: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid(
                "generator source episode requires its incident body",
            ));
        };
        let source = model.field.read_current_source()?;
        let material = model
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let word = model.evaluate_generator_symbols(
            &source,
            &material,
            &table,
            symbols,
            binding,
            start,
            &contacts,
            model.epoch,
        )?;
        Ok(NativeIncidentGenerated {
            word: Rc::new(word),
            comparison: None,
        })
    }

    /// The word-free moment reading of a symbol passage: `(L^N q₀ + m) ⊕ b₀` through the same
    /// per-symbol sums and table, from clock 0, without the incident word. This is not the
    /// target Holon (see `evaluate_target_holon`); nothing is changed.
    pub fn accumulate_generator_symbol_moment(
        &mut self,
        table: Rc<ResidentNormalEnclosureSection<'c>>,
        symbols: &[usize],
        binding: &GeneratorSourceBinding,
    ) -> Result<GeneratorMomentHolon<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("generator moment requires its incident body"));
        };
        let machine = Rc::clone(model.source_machine()?);
        let rows = symbols.len();
        binding.validate_scope(&machine, 0, rows)?;
        let source = model.field.read_current_source()?;
        let maps = MachineSourceMaps::new_with_enclosure(
            model.field.surface(),
            &machine,
            binding,
            0,
            rows,
            table.grain(),
            model.spec.enclosure_propagation(),
        )?;
        let (present, sums) = maps.symbol_moment_sums(symbols, table.rows())?;
        let sums = maps.mount_symbol_sums(&sums, table.grain())?;
        let moment = maps.symbol_moment(&table, &sums, &present)?;
        model.moment_holon(&maps, source, moment, rows)
    }

    /// Declaration of a retained generator comparison, without reading any field.
    pub fn generator_comparison_declaration(
        &self,
        id: u64,
    ) -> Result<GeneratorSourceMomentMeta, NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => Ok(model
                .comparisons
                .get(&id)
                .and_then(|c| c.meta())
                .ok_or_else(|| invalid("unknown generator moment comparison"))?
                .clone()),
            _ => Err(invalid("incident comparison requires its model chart")),
        }
    }

    /// Prepare the material return of a generator comparison at the cut of `contemporary`
    /// (from `contemporary_incident_comparison`/`contemporary_output`), with the passage's
    /// declared per-edge contact relation. The same one-cut return as
    /// [`Self::prepare_contemporary_material_return`] for a passage comparison.
    pub fn prepare_generator_material_return(
        &mut self,
        contemporary: &NativeIncidentGenerated<'c>,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
        step_bits: u32,
        contacts: &[GeneratorSourceContact],
    ) -> Result<NativeIncidentMaterialReturn<'c>, NativeSessionError> {
        if contemporary.word.source_moment.is_none() {
            return Err(invalid("unknown generator moment comparison"));
        }
        self.prepare_contemporary_material_return(
            contemporary,
            output_covector,
            step_bits,
            contacts,
        )
    }

    /// Prepare the material return of any retained comparison at the cut of `contemporary` (a
    /// word read at the contemporary constitution: `contemporary_incident_comparison`,
    /// `contemporary_symbol_comparison` or `contemporary_incident_comparison_at`). The cut must
    /// still be current: same material epoch and the same field current. A passage supplies its
    /// declared per-edge contact relation; a prepared boundary supplies none.
    pub fn prepare_contemporary_material_return(
        &mut self,
        contemporary: &NativeIncidentGenerated<'c>,
        output_covector: ResidentNormalEnclosureView<'_, 'c>,
        step_bits: u32,
        contacts: &[GeneratorSourceContact],
    ) -> Result<NativeIncidentMaterialReturn<'c>, NativeSessionError> {
        let id = contemporary
            .comparison
            .ok_or_else(|| invalid("contemporary word has no comparison"))?;
        {
            let BodyState::Incident(model) = self.state_mut()? else {
                return Err(invalid("incident return requires its model chart"));
            };
            let kind_agrees = model.comparisons.get(&id).is_some_and(|comparison| {
                comparison.is_passage() == contemporary.word.source_moment.is_some()
            });
            if !kind_agrees {
                return Err(invalid("unknown incident comparison"));
            }
            let current = model.field.read_current_source()?;
            if contemporary.word.epoch != model.epoch
                || !current.same_owner(&contemporary.word.source)
                || current.enclosure().inspect()?
                    != contemporary.word.source.enclosure().inspect()?
            {
                return Err(invalid(
                    "the comparison was read at an earlier cut; read it again at the contemporary constitution",
                ));
            }
        }
        self.prepare_incident_material_return_at(
            id,
            &contemporary.word,
            output_covector,
            step_bits,
            contacts,
        )
    }

    /// A retained prepared-boundary comparison read at one contemporary cut through a boundary
    /// its source owner supplies again (the session re-encodes its source cells through the
    /// contemporary encoder onto the current boundary). The retained `admitted` restriction
    /// applies; `held` must equal the retained receiver mask.
    pub fn contemporary_incident_comparison_at(
        &mut self,
        id: u64,
        boundary: ResidentNormalEnclosureView<'_, 'c>,
        held: &[bool],
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid("incident comparison requires its model chart"));
        };
        Ok(NativeIncidentGenerated {
            word: Rc::new(model.contemporary_boundary_word(id, boundary, held)?),
            comparison: Some(id),
        })
    }
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'c> NativeIncidentGenerated<'c> {
    /// This retained comparison read at the body's contemporary constitution.
    pub fn contemporary_output(
        &self,
        body: &mut NativeCoupledBody<'c>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let id = self
            .comparison
            .ok_or_else(|| invalid("contemporary reading requires a retained comparison"))?;
        body.contemporary_incident_comparison(id)
    }

    /// This retained symbol comparison read at one contemporary cut through `table`.
    pub fn contemporary_symbol_output(
        &self,
        body: &mut NativeCoupledBody<'c>,
        table: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let id = self
            .comparison
            .ok_or_else(|| invalid("contemporary reading requires a retained comparison"))?;
        body.contemporary_symbol_comparison(id, table)
    }

    /// Per-kind counts of the directed contacts the source passage pooled.
    pub fn generator_source_contact_counts(&self) -> Option<&[usize]> {
        self.word
            .source_moment
            .as_ref()
            .map(|m| m.meta.contact_counts.as_slice())
    }
    /// The per-edge relation is no longer retained by the body; this always returns `None`.
    #[deprecated(note = "the body keeps per-kind counts only; use generator_source_contact_counts")]
    pub fn generator_source_contacts(&self) -> Option<&[GeneratorSourceContact]> {
        None
    }
    pub fn generator_source_binding(&self) -> Option<(&GeneratorSourceBinding, u64, usize, usize)> {
        self.word.source_moment.as_ref().map(|m| {
            (
                &m.meta.binding,
                m.meta.start,
                m.meta.rows,
                m.meta.components,
            )
        })
    }
}

impl<'c> RetainedComparison<'c> {
    #[cfg_attr(not(test), allow(dead_code))]
    /// Resident sections and canonical rest octets this retained comparison holds.
    pub(crate) fn retained_operand_census(&self) -> Result<Value, NativeSessionError> {
        let (first, second) = match &self.source {
            ComparisonSource::Boundary(boundary) => (boundary.rest()?, None),
            ComparisonSource::Rows { moment, condition } => (
                moment.rest()?,
                condition.as_ref().map(|c| c.rest()).transpose()?,
            ),
            ComparisonSource::Symbols(sums) => (
                sums.moment.rest()?,
                sums.ports.as_ref().map(|d| d.rest()).transpose()?,
            ),
        };
        let mut octets = first.canonical_bytes().map_err(invalid)?.len();
        let mut sections = 1usize;
        if let Some(second) = second {
            octets += second.canonical_bytes().map_err(invalid)?.len();
            sections += 1;
        }
        let (rows, alphabet) = match self.meta() {
            Some(meta) => (Some(meta.rows), meta.alphabet),
            None => (None, None),
        };
        Ok(json!({"sections": sections, "octets": octets,
            "solver_iterates": 0, "material_views": 0, "field_cuts": 0,
            "source_rows": rows, "alphabet": alphabet}))
    }
}

impl<'c> NativeCoupledBody<'c> {
    #[cfg_attr(not(test), allow(dead_code))]
    /// Census of a retained comparison: resident sections, rest octets and the producing-cut
    /// objects it holds (always zero solver iterates, material views, field cuts).
    pub(crate) fn generator_comparison_census(&self, id: u64) -> Result<Value, NativeSessionError> {
        match self.state()? {
            BodyState::Incident(model) => model
                .comparisons
                .get(&id)
                .ok_or_else(|| invalid("unknown incident comparison"))?
                .retained_operand_census(),
            _ => Err(invalid("incident comparison requires its model chart")),
        }
    }
}
