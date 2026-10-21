//! One-branch four-class computational input law. Material and prefix provenance
//! live beside the ONE native Resident; there is no mirrored ingress owner.
use super::*;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::paired::PairingDeclaration;
use crate::hnn::physical::action::contextual::{Complex, ContextualBounds, EmpiricalMaterial};
use crate::hnn::word::action::SourceClassPreparation;
use num_traits::{One, Zero};
use std::sync::Arc;
fn refuse(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}
mod framing;
pub use framing::{ContextChart, SourceFraming, PreparedMaterial};
pub const SOURCE_FRAMING_LAW: &str = "prepared-class-source-framing-route-v1";
pub const LAW: &str = "prepared-class-local-retained-v1";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrefixRole {
    Observed,
    Conditioning,
    Hypothesized,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrefixMode {
    Training,
    Forecast,
    /// Applied u=0 intervention, with the learned material and its moments retained.
    ForecastZeroControl,
}
fn unit(k: usize) -> Vec<Rat> {
    (0..4)
        .map(|j| if j == k { Rat::one() } else { Rat::zero() })
        .collect()
}
fn features(history: &[(usize, PrefixRole)], h: &Rat) -> Option<Vec<Complex>> {
    if history.len() != 2 {
        return None;
    }
    let p = unit(history[0].0);
    let c = unit(history[1].0);
    let mut a: Vec<_> = c.iter().zip(&p).map(|(c, p)| c - p).collect();
    a.extend(c);
    a.extend(p);
    let mut f = a.clone();
    f.push(h.clone());
    f.extend(a.iter().map(|v| v * h));
    Some(f.into_iter().map(|q| [q, Rat::zero()]).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedInputCut {
    pub source_cells: u64,
    pub framing: Option<SourceFraming>,
    pub commit: u64,
    pub lift: Vec<BigInt>,
    pub history: Vec<(usize, PrefixRole)>,
    pub context: Rat,
    pub feature: Option<Vec<Complex>>,
    pub control: Option<Vec<Rat>>,
    pub material_observations: u64,
    pub boundary_identity: String,
    pub pairs: Vec<(usize, usize)>,
    pub max_abs_work: Rat,
    pub rational_bits: u64,
}
impl PreparedInputCut {
    pub(crate) fn apply<'a>(
        &self,
        field: &'a Field,
        theta: &Constitution,
        ratio: &PendingRatio,
        mut word: Word<'a>,
    ) -> Result<Word<'a>, HnnError> {
        if ratio.moment().cells() != self.source_cells
            || ratio.anchor() != self.lift
            || ratio.commit() != self.commit
        {
            return Err(refuse(
                "prepared input binds the original ratio/source/lift/commit",
            ));
        }
        if self.framing.map(|f|f.source_cells())!=self.framing.map(|_|self.source_cells){return Err(refuse("prepared framing belongs to original source frontier"));}
        let declared=field.receiving_context(ratio.phases().ring())==Some(crate::hnn::receiving::ObservationPartition::SourceFramingRouteV1);
        if declared!=self.framing.is_some(){return Err(refuse("prepared framing and tree declaration agree"));}
        let pairing = PairingDeclaration::Family {
            table: self.pairs.clone(),
        };
        let boundary = PairedObservation::admit(field, theta, &pairing)?;
        if boundary.immutable_identity_text() != self.boundary_identity {
            return Err(refuse(
                "prepared input's actual source boundary is unchanged",
            ));
        }
        word.bind_source_producer(
            theta,
            &ratio.current(field)?,
            Arc::new(ratio.moment().clone()),
        )?;
        let binding = SourceClassPreparation::at_native_forward(&word, &boundary, 0)?;
        if binding.source_opening()[0] != self.context {
            return Err(refuse(
                "prepared input prefix context belongs to the actual complete source opening",
            ));
        }
        match &self.control {
            Some(u) => Ok(binding
                .apply(word, u, &self.max_abs_work, self.rational_bits)?
                .0),
            None => Ok(word),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialReturn {
    pub cut: PreparedInputCut,
    pub actual: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedInputState {
    pub(crate) mode: PrefixMode,
    pub(crate) forecast_role: PrefixRole,
    pub(crate) pairs: Vec<(usize, usize)>,
    pub(crate) boundary_identity: String,
    pub(crate) bounds: ContextualBounds,
    pub(crate) max_abs_work: Rat,
    pub(crate) history: Vec<(usize, PrefixRole)>,
    pub(crate) material: PreparedMaterial,
    pub(crate) training: u64,
    pub(crate) conditioning: u64,
    pub(crate) generated: u64,
    pub(crate) source_octet: Vec<usize>,
    pub(crate) generated_octet: Vec<usize>,
    pub(crate) pending: BTreeMap<u64, MaterialReturn>,
    pub(crate) fit_proposals: u64,
    pub(crate) last_refusal: Option<String>,
}
impl PreparedInputState {
    pub(crate) fn fresh(
        field: &Field,
        theta: &Constitution,
        pairing: &PairingDeclaration,
    ) -> Result<Self, HnnError> {
        Self::fresh_with_chart(field,theta,pairing,ContextChart::ScalarV1)
    }
    pub(crate) fn fresh_with_chart(field:&Field,theta:&Constitution,pairing:&PairingDeclaration,chart:ContextChart)->Result<Self,HnnError>{
        let framed=field.receivers().iter().all(|r|field.receiving_context(r.ring)==Some(crate::hnn::receiving::ObservationPartition::SourceFramingRouteV1));
        if framed != (chart==ContextChart::SourceFramingRouteV1){return Err(refuse("material context schema matches the freshly declared source framing tree"));}
        if field.alphabet() != 4 || field.sources() != [0] {
            return Err(refuse(
                "prepared language law declares four classes and actual source0",
            ));
        }
        let boundary = PairedObservation::admit(field, theta, pairing)?;
        let pairs = boundary.ports()[0]
            .carrier()
            .sigma()
            .table()
            .iter()
            .enumerate()
            .map(|(a, b)| {
                b.map(|b| (a, b))
                    .ok_or(refuse("complete prepared class pairing"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            mode: PrefixMode::Training,
            forecast_role: PrefixRole::Conditioning,
            pairs,
            boundary_identity: boundary.immutable_identity_text(),
            bounds: ContextualBounds {
                branches: 1,
                pending: 64,
                precision_bits: 20,
                rational_bits: 1024,
                max_features: 25,
                max_scalar_work: 1_000_000,
            },
            max_abs_work: integer(1 << 16),
            history: Vec::new(),
            material: PreparedMaterial::fresh(chart),
            training: 0,
            conditioning: 0,
            generated: 0,
            source_octet: Vec::new(),
            generated_octet: Vec::new(),
            pending: BTreeMap::new(),
            fit_proposals: 0,
            last_refusal: None,
        })
    }
    pub fn law(&self) -> &'static str {
        match self.material.chart(){ContextChart::ScalarV1=>LAW,ContextChart::SourceFramingRouteV1=>SOURCE_FRAMING_LAW}
    }
    pub fn context_chart(&self)->ContextChart{self.material.chart()}
    pub fn mode(&self) -> PrefixMode {
        self.mode
    }
    pub fn material(&self) -> &PreparedMaterial {
        &self.material
    }
    pub fn history(&self) -> &[(usize, PrefixRole)] {
        &self.history
    }
    pub fn frontiers(&self) -> (u64, u64, u64) {
        (self.training, self.conditioning, self.generated)
    }
    pub fn unfinished_generated(&self) -> &[usize] {
        &self.generated_octet
    }
    pub fn outstanding(&self) -> &BTreeMap<u64, MaterialReturn> {
        &self.pending
    }
    pub fn source_cells(&self) -> u64 {
        self.training + self.conditioning + self.generated
    }
    pub(crate) fn seal(
        &self,
        field: &Field,
        theta: &Constitution,
        current: &Current,
        source: &SourceMoment,
    ) -> Result<PreparedInputCut, HnnError> {
        let seal_start=std::time::Instant::now();
        if source.cells() != self.source_cells() {
            return Err(refuse(
                "prepared material/context frontier agrees with the single native source",
            ));
        }
        let framing=match self.context_chart(){ContextChart::ScalarV1=>None,ContextChart::SourceFramingRouteV1=>Some(SourceFraming::at(source))};
        let h = source.open_storage(field, theta, current)?[0][0].clone();
        let f = features(&self.history, &h);
        let control = if let Some(f) = &f {
            let response = if self.mode == PrefixMode::ForecastZeroControl {
                vec![[Rat::zero(), Rat::zero()]; 4]
            } else {
                self.material.part(framing)?.contract(f)?
            };
            if response.iter().any(|z| !z[1].is_zero()) {
                return Err(refuse(
                    "class material uses real coordinates without imaginary projection",
                ));
            }
            Some(response.into_iter().map(|z| z[0].clone()).collect())
        } else {
            None
        };
        crate::hnn::physical::action::contextual::note_fit_work(|w|w.context_seal_and_contract+=seal_start.elapsed());
        Ok(PreparedInputCut {
            source_cells: source.cells(),
            framing,
            commit: theta.commit(),
            lift: current.lift().to_vec(),
            history: self.history.clone(),
            context: h,
            feature: f,
            control,
            material_observations: self.material.part(framing)?.observations(),
            boundary_identity: self.boundary_identity.clone(),
            pairs: self.pairs.clone(),
            max_abs_work: self.max_abs_work.clone(),
            rational_bits: self.bounds.rational_bits,
        })
    }
    fn advance(&mut self, class: usize, role: PrefixRole) -> Result<(), HnnError> {
        if class >= 4 {
            return Err(refuse("four-class prepared input"));
        }
        self.history.push((class, role));
        if self.history.len() > 2 {
            self.history.remove(0);
        }
        self.source_octet.push(class);
        if self.source_octet.len() == 4 {
            self.source_octet.clear();
        }
        match role {
            PrefixRole::Observed => {
                self.training = self
                    .training
                    .checked_add(1)
                    .ok_or(HnnError::CountOverflow)?
            }
            PrefixRole::Conditioning => {
                self.conditioning = self
                    .conditioning
                    .checked_add(1)
                    .ok_or(HnnError::CountOverflow)?
            }
            PrefixRole::Hypothesized => {
                self.generated = self
                    .generated
                    .checked_add(1)
                    .ok_or(HnnError::CountOverflow)?;
                self.generated_octet.push(class);
                if self.generated_octet.len() == 4 {
                    self.generated_octet.clear();
                }
            }
        }
        Ok(())
    }
    pub(crate) fn after_actual(
        &mut self,
        cut: PreparedInputCut,
        class: usize,
    ) -> Result<(), HnnError> {
        if self.mode != PrefixMode::Training
            || cut.source_cells != self.source_cells()
            || class >= 4
        {
            return Err(refuse(
                "one actual prepared return at its original source frontier",
            ));
        }
        if cut.feature.is_some() && self.pending.len() >= self.bounds.pending {
            return Err(refuse("bounded outstanding original material returns"));
        }
        self.advance(class, PrefixRole::Observed)?;
        if cut.feature.is_some() {
            let id = cut.source_cells;
            self.pending
                .insert(id, MaterialReturn { cut, actual: class });
            if let Err(e) = self.form(id) {
                self.last_refusal = Some(e.to_string());
            }
        }
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn code_defer_actual(&mut self,cut:PreparedInputCut,class:usize)->Result<(),HnnError>{
        if cut.source_cells!=self.source_cells()||cut.feature.is_none(){return Err(refuse("CODE delayed return keeps actual original source"));}
        let id=cut.source_cells;self.advance(class,PrefixRole::Observed)?;self.pending.insert(id,MaterialReturn{cut,actual:class});Ok(())
    }
    pub fn form(&mut self, id: u64) -> Result<(), HnnError> {
        if self.mode != PrefixMode::Training {
            return Err(refuse("forecast cannot fit material from hypotheses"));
        }
        let p = self
            .pending
            .get(&id)
            .ok_or(refuse("one original unconsumed material observation"))?;
        let f = p
            .cut
            .feature
            .as_ref()
            .ok_or(refuse("an original complete material feature"))?;
        let c = unit(p.cut.history[1].0);
        let y = unit(p.actual);
        let eta = y
            .iter()
            .zip(c)
            .map(|(y, c)| [y - c, Rat::zero()])
            .collect::<Vec<_>>();
        let framing=p.cut.framing;
        let next = self.material.part(framing)?.stage(f, &eta, &self.bounds)?;
        self.fit_proposals += 1;
        self.material.replace(framing,next)?;
        self.pending.remove(&id);
        self.last_refusal = None;
        Ok(())
    }
    pub(crate) fn after_forecast(&mut self, class: usize) -> Result<(), HnnError> {
        if !matches!(
            self.mode,
            PrefixMode::Forecast | PrefixMode::ForecastZeroControl
        ) {
            return Err(refuse(
                "hypothesized prefix requires an explicit frozen forecast owner",
            ));
        }
        self.advance(class, self.forecast_role)
    }
}
impl Resident {
    pub fn select_prepared_input(&mut self, pairing: &PairingDeclaration) -> Result<(), HnnError> {
        self.select_prepared_input_chart(pairing,ContextChart::ScalarV1)
    }
    pub fn select_source_framing_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{self.select_prepared_input_chart(pairing,ContextChart::SourceFramingRouteV1)}
    fn select_prepared_input_chart(&mut self,pairing:&PairingDeclaration,chart:ContextChart)->Result<(),HnnError>{
        self.admit_exact_current()?;
        if self.prepared_input.is_some()
            || self.moments.len() != 1
            || self.moments.values().next().map(SourceMoment::cells) != Some(0)
            || self.receiving_law() != crate::hnn::receiving::ReceivingLaw::RetainedFibreV1
        {
            return Err(refuse(
                "prepared input is an explicit fresh retained-fibre law",
            ));
        }
        self.prepared_input = Some(PreparedInputState::fresh_with_chart(
            &self.field,
            &self.constitution,
            pairing,chart,
        )?);
        Ok(())
    }
    pub fn prepared_input(&self) -> Option<&PreparedInputState> {
        self.prepared_input.as_ref()
    }
    pub fn freeze_prepared_forecast(&mut self) -> Result<(), HnnError> {
        let p = self
            .prepared_input
            .as_mut()
            .ok_or(refuse("an explicit prepared input model"))?;
        if p.mode == PrefixMode::Training {
            p.mode = PrefixMode::Forecast;
            p.forecast_role = PrefixRole::Conditioning;
        }
        Ok(())
    }
    /// Select u=0 BEFORE any conditioning/hypothesis, without altering trained M/R.
    pub fn zero_prepared_forecast_control(&mut self) -> Result<(), HnnError> {
        let p = self.prepared_input.as_mut().ok_or(refuse(
            "prepared forecast control requires actual learned material",
        ))?;
        if p.mode != PrefixMode::Forecast
            || p.conditioning != 0
            || p.generated != 0
            || !p.pending.is_empty()
        {
            return Err(refuse(
                "zero control is declared before first conditioning on a closed forecast fork",
            ));
        }
        p.mode = PrefixMode::ForecastZeroControl;
        Ok(())
    }
    pub fn begin_hypothesized_output(&mut self) -> Result<(), HnnError> {
        let p = self
            .prepared_input
            .as_mut()
            .ok_or(refuse("an explicit prepared input forecast"))?;
        if !matches!(
            p.mode,
            PrefixMode::Forecast | PrefixMode::ForecastZeroControl
        ) {
            return Err(refuse("freeze material before hypothesized output"));
        }
        p.forecast_role = PrefixRole::Hypothesized;
        Ok(())
    }
}
pub(crate) mod codec;
