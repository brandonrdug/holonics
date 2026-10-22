//! One-branch four-class computational input law. Material and prefix provenance
//! live beside the ONE native Resident; there is no mirrored ingress owner.
use super::*;
use crate::hnn::encoding::observed::PairedObservation;
use crate::hnn::paired::PairingDeclaration;
use crate::hnn::physical::action::contextual::{Complex, ContextualBounds, EmpiricalMaterial};
use crate::hnn::word::action::{SourceClassPreparation,PreparationWorkPolicy,NativeWorkBudget};
use num_traits::{One, Zero};
use std::sync::Arc;
fn refuse(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}
mod framing;
pub use framing::{ContextChart, SourceFraming, PreparedMaterial, LaggedReceiverBoundary};
pub const SOURCE_FRAMING_LAW: &str = "prepared-class-source-framing-route-v1";
pub const REPRESENTED_NATIVE_LAW:&str="prepared-represented-native-passage-v1";
pub const LAGGED_RECEIVER_QUADRATIC_LAW:&str="prepared-native-lagged-receiver-quadratic-work-v1";
pub const LAGGED_RECEIVER_LAW: &str = "prepared-native-lagged-receiver-v1";
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
fn lagged_features(history:&[(usize,PrefixRole)],lag:Option<&LaggedReceiverBoundary>,lift:&[BigInt])->Option<Vec<Complex>>{
    if history.len()!=2{return None;}let lag=lag?;
    if lift.len()!=lag.lift.len(){return None;}
    // The declared ring action transports the original reached vector into this cut's frame.
    let h=lag.field.ring(lag.receiver).rotate(&lag.contrast,&(&lift[lag.receiver]-&lag.lift[lag.receiver]));
    let p=unit(history[0].0);let c=unit(history[1].0);let mut a:Vec<_>=c.iter().zip(&p).map(|(c,p)|c-p).collect();a.extend(c);a.extend(p);
    let mut f=a.clone();f.extend(h.iter().cloned());for value in &h{f.extend(a.iter().map(|v|value*v));}
    Some(f.into_iter().map(|q|[q,Rat::zero()]).collect())
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedInputCut {
    pub source_cells: u64,
    pub(crate) native_lagged: bool,
    pub(crate) lagged: Option<LaggedReceiverBoundary>,
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
    pub work_policy:PreparationWorkPolicy,
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
            Some(u) => Ok(match self.work_policy{
                PreparationWorkPolicy::LegacyCoordinateV1=>binding.apply(word,u,&self.max_abs_work,self.rational_bits)?.0,
                PreparationWorkPolicy::NativeQuadraticV1(b)|PreparationWorkPolicy::RepresentedNativeV1(b)=>binding.apply_quadratic(word,u,&self.max_abs_work,self.rational_bits,b)?.0,
            }),
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
    pub(crate) work_policy:PreparationWorkPolicy,
    pub(crate) history: Vec<(usize, PrefixRole)>,
    pub(crate) material: PreparedMaterial,
    pub(crate) training: u64,
    pub(crate) conditioning: u64,
    pub(crate) generated: u64,
    pub(crate) source_octet: Vec<usize>,
    pub(crate) generated_octet: Vec<usize>,
    pub(crate) pending: BTreeMap<u64, MaterialReturn>,
    pub(crate) fit_proposals: u64,
    pub(crate) lagged: Option<LaggedReceiverBoundary>,
    pub(crate) eligible: [u64;4],
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
        if framed != chart.framed(){return Err(refuse("material context schema matches the freshly declared source framing tree"));}
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
                max_features: chart.features(),
                max_scalar_work: chart.formation_work(),
            },
            max_abs_work: integer(1 << 16),
            work_policy:PreparationWorkPolicy::LegacyCoordinateV1,
            history: Vec::new(),
            material: PreparedMaterial::fresh(chart),
            training: 0,
            conditioning: 0,
            generated: 0,
            source_octet: Vec::new(),
            generated_octet: Vec::new(),
            pending: BTreeMap::new(),
            fit_proposals: 0,
            lagged: None, eligible: [0;4],
            last_refusal: None,
        })
    }
    pub fn law(&self) -> &'static str {
        match self.material.chart(){ContextChart::ScalarV1=>LAW,ContextChart::SourceFramingRouteV1=>SOURCE_FRAMING_LAW,ContextChart::LaggedReceiverBoundaryV1=>if self.work_policy.represented(){REPRESENTED_NATIVE_LAW}else if self.work_policy.native_budget().is_some(){LAGGED_RECEIVER_QUADRATIC_LAW}else{LAGGED_RECEIVER_LAW}}
    }
    pub fn work_receipt_policy(&self)->PreparationWorkPolicy{self.work_policy}
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
    pub fn material_refusal(&self)->Option<&str>{self.last_refusal.as_deref()}
    pub fn outstanding(&self) -> &BTreeMap<u64, MaterialReturn> {
        &self.pending
    }
    pub fn source_cells(&self) -> u64 {
        self.training + self.conditioning + self.generated
    }
    /// No new observation, solve or Word: bounded copy of the actual contraction's inputs.
    pub(crate) fn native_refusal_reading(&self,cut:&PreparedInputCut)->String{
        let m=match self.material.part(cut.framing){Ok(m)=>m,Err(e)=>return format!("material diagnostic unavailable: {e:?}")};
        let bits=m.applied().iter().flatten().flat_map(|z|z.iter()).chain(cut.feature.iter().flatten().flat_map(|z|z.iter())).chain(cut.control.iter().flatten()).chain(std::iter::once(&cut.context)).chain(std::iter::once(m.coefficient_error_upper())).chain(std::iter::once(m.target_energy())).chain(cut.lagged.iter().flat_map(|l|l.contrast.iter())).fold(0u64,|s,q|s.saturating_add(q.numer().bits()).saturating_add(q.denom().bits()));
        let bits=bits.saturating_add(cut.lift.iter().map(|x|x.bits()).sum::<u64>()).saturating_add(cut.lagged.iter().flat_map(|l|l.lift.iter()).map(|x|x.bits()).sum::<u64>());
        if bits>1_048_576||cut.boundary_identity.len()>65536||m.applied().iter().map(Vec::len).sum::<usize>()>4096{return format!("material diagnostic extent refused bits={bits}");}
        let lag=cut.lagged.as_ref().map(|l|(l.receiver,l.source_cells,l.commit,l.tick,&l.lift,&l.contrast,l.role,l.field.rings().iter().map(|r|r.period()).collect::<Vec<_>>()));
        format!("kind=original_material_contraction schema={} source={} commit={} lift={:?} framing={:?} history={:?} lag={lag:?} scalar_open_context={} feature={:?} control={:?} M={:?} M_observations={} coefficient_error={} target_energy={} boundary={} coordinate_bits={} max_abs_work={} material_bounds={:?} numeric_bits={bits}",self.law(),cut.source_cells,cut.commit,cut.lift,cut.framing,cut.history,cut.context,cut.feature,cut.control,m.applied(),m.observations(),m.coefficient_error_upper(),m.target_energy(),cut.boundary_identity,cut.rational_bits,cut.max_abs_work,self.bounds)
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
        let framing=if self.context_chart().framed(){Some(SourceFraming::at(source))}else{None};
        if let Some(lag)=&self.lagged{if lag.field!=*field||lag.source_cells.checked_add(1)!=Some(source.cells())||lag.lift.len()!=current.lift().len()||lag.commit>theta.commit(){return Err(refuse("lagged context keeps its original reached cut and next-source availability"));}}
        let h = source.open_storage(field, theta, current)?[0][0].clone();
        let native_lagged=self.context_chart()==ContextChart::LaggedReceiverBoundaryV1;
        let f = if native_lagged{lagged_features(&self.history,self.lagged.as_ref(),current.lift())}else{features(&self.history, &h)};
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
            native_lagged, lagged:self.lagged.clone(),
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
            work_policy:self.work_policy,
        })
    }
    pub(crate) fn install_reached_lag(&mut self,lag:LaggedReceiverBoundary)->Result<(),HnnError>{
        if self.context_chart()!=ContextChart::LaggedReceiverBoundaryV1 || lag.source_cells.checked_add(1)!=Some(self.source_cells()){return Err(refuse("a reached native context is available only to the NEXT actual or hypothetical preparation"));}
        self.lagged=Some(lag);Ok(())
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
        if cut.native_lagged && cut.feature.is_some(){let part=cut.framing.ok_or(refuse("native original context part"))?.part();self.eligible[part]=self.eligible[part].checked_add(1).ok_or(HnnError::CountOverflow)?;}
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
        if p.cut.native_lagged{
            let work=ContextChart::LaggedReceiverBoundaryV1.formation_work();
            if f.len()!=90||work>self.bounds.max_scalar_work{return Err(refuse("declared bounded native-context normal formation work"));}
        }
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
    /// Fresh native predictor lineage. Legacy receiving/refine entrypoints refuse this scope.
    pub fn select_native_current_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if self.field.receivers().iter().any(|r|self.constitution.receiving_return_policy(r.ring)!=Some(crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1)){return Err(refuse("native F declares a family-local receiving current before input, without repurposing population responsibility"));}
        self.select_prepared_input_chart(pairing,ContextChart::LaggedReceiverBoundaryV1)
    }
    /// Fresh opt-in represented computation. Released feedback tails are reported per Word;
    /// this version does not pretend ReceptionCarry is a residual-vector decoder.
    pub fn select_represented_native_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if self.admitted.iter().any(|r|!self.constitution.native_rational_receiving(r.ring())){return Err(refuse("represented native passage explicitly declares its receiving statistics policy"));}
        self.select_native_current_prepared_input(pairing)?;
        self.prepared_input.as_mut().expect("fresh native owner").work_policy=PreparationWorkPolicy::RepresentedNativeV1(NativeWorkBudget::V1);Ok(())
    }
    pub fn select_native_quadratic_work_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        self.select_native_current_prepared_input(pairing)?;
        self.prepared_input.as_mut().expect("fresh native owner").work_policy=PreparationWorkPolicy::NativeQuadraticV1(NativeWorkBudget::V1);Ok(())
    }
    pub fn select_source_framing_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{self.select_prepared_input_chart(pairing,ContextChart::SourceFramingRouteV1)}
    fn select_prepared_input_chart(&mut self,pairing:&PairingDeclaration,chart:ContextChart)->Result<(),HnnError>{
        self.admit_exact_current()?;
        if self.prepared_input.is_some()
            || self.moments.len() != 1
            || self.moments.values().next().map(SourceMoment::cells) != Some(0)
            || (chart!=ContextChart::LaggedReceiverBoundaryV1 && self.receiving_law() != crate::hnn::receiving::ReceivingLaw::RetainedFibreV1)
        {
            return Err(refuse(
                "prepared input is explicit at a fresh source; the legacy scope additionally requires retained-fibre scoring",
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
