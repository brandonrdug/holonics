use super::*;
use std::fmt::Write;
fn put(out: &mut String, x: impl std::fmt::Display) {
    write!(out, "{x} ").expect("string");
}
fn get<T: std::str::FromStr>(t: &mut std::str::SplitWhitespace<'_>) -> Result<T, HnnError> {
    t.next()
        .and_then(|s| s.parse().ok())
        .ok_or(refuse("complete bounded prepared input fields"))
}
pub(crate) fn hex(s: &str) -> String {
    s.bytes().map(|b| format!("{b:02x}")).collect()
}
pub(crate) fn unhex(s: &str) -> Result<String, HnnError> {
    if s.len() > 16 * 1024 * 1024 || s.len() % 2 != 0 {
        return Err(refuse("bounded prepared input hex"));
    }
    let bytes = s
        .as_bytes()
        .chunks_exact(2)
        .map(|c| {
            let s = std::str::from_utf8(c).map_err(|_| refuse("prepared input hex"))?;
            u8::from_str_radix(s, 16).map_err(|_| refuse("prepared input hex"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    String::from_utf8(bytes).map_err(|_| refuse("prepared input text encoding"))
}
fn role(r: PrefixRole) -> u8 {
    match r {
        PrefixRole::Observed => 0,
        PrefixRole::Conditioning => 1,
        PrefixRole::Hypothesized => 2,
    }
}
fn read_role(t: &mut std::str::SplitWhitespace<'_>) -> Result<PrefixRole, HnnError> {
    match get::<u8>(t)? {
        0 => Ok(PrefixRole::Observed),
        1 => Ok(PrefixRole::Conditioning),
        2 => Ok(PrefixRole::Hypothesized),
        _ => Err(refuse("explicit prepared prefix provenance")),
    }
}
fn history(out: &mut String, h: &[(usize, PrefixRole)]) {
    put(out, h.len());
    for (c, r) in h {
        put(out, c);
        put(out, role(*r));
    }
}
fn read_history(
    t: &mut std::str::SplitWhitespace<'_>,
) -> Result<Vec<(usize, PrefixRole)>, HnnError> {
    let n: usize = get(t)?;
    if n > 2 {
        return Err(refuse("bounded last-two prefix"));
    }
    (0..n)
        .map(|_| {
            let c = get(t)?;
            if c >= 4 {
                return Err(refuse("four-class prefix"));
            }
            Ok((c, read_role(t)?))
        })
        .collect()
}
fn lag(out:&mut String,value:Option<&LaggedReceiverBoundary>){
    put(out,usize::from(value.is_some()));if let Some(v)=value{for n in [v.receiver as u64,v.source_cells,v.commit,v.tick as u64]{put(out,n);}put(out,role(v.role));put(out,v.lift.len());for x in &v.lift{put(out,x);}for x in &v.contrast{put(out,x);}}
}
fn read_lag(field:&Field,t:&mut std::str::SplitWhitespace<'_>)->Result<Option<LaggedReceiverBoundary>,HnnError>{
    match get::<u8>(t)?{0=>Ok(None),1=>{
        let receiver:usize=get(t)?;let source_cells=get(t)?;let commit=get(t)?;let tick=get(t)?;let role=read_role(t)?;
        if receiver>=field.rings().len()||field.ring(receiver).width()!=6||get::<usize>(t)?!=field.rings().len(){return Err(refuse("original lagged receiver and complete frame"));}
        let lift=(0..field.rings().len()).map(|_|get(t)).collect::<Result<Vec<_>,_>>()?;
        let contrast=(0..6).map(|_|get::<Rat>(t)).collect::<Result<Vec<_>,_>>()?;
        if contrast.iter().any(|q|q.numer().bits()>4096||q.denom().bits()>4096){return Err(refuse("bounded exact lagged context"));}
        Ok(Some(LaggedReceiverBoundary{field:field.clone(),receiver,source_cells,commit,tick,lift,contrast,role}))
    },_=>Err(refuse("explicit lag availability"))}
}
fn put_work_policy(o:&mut String,p:PreparationWorkPolicy){if let PreparationWorkPolicy::NativeQuadraticV1(b)=p{put(o,b.aggregate_bits);put(o,b.integer_bits);put(o,b.coordinates);}}
fn read_work_policy(t:&mut std::str::SplitWhitespace<'_>,quadratic:bool)->Result<PreparationWorkPolicy,HnnError>{if quadratic{let b=NativeWorkBudget{aggregate_bits:get(t)?,integer_bits:get(t)?,coordinates:get(t)?};b.admit()?;Ok(PreparationWorkPolicy::NativeQuadraticV1(b))}else{Ok(PreparationWorkPolicy::LegacyCoordinateV1)}}
impl PreparedInputCut {
    pub(crate) fn to_text(&self) -> String {
        let mut o = String::from(if self.native_lagged&&matches!(self.work_policy,PreparationWorkPolicy::NativeQuadraticV1(_)){"prepared-input-cut-native-lagged-quadratic-v1 "}else if self.native_lagged{"prepared-input-cut-native-lagged-v1 "}else if self.framing.is_some(){"prepared-input-cut-framing-v1 "}else{"prepared-input-cut-v1 "});
        put(&mut o, self.source_cells);
        put(&mut o, self.commit);
        put(&mut o, self.material_observations);
        put(&mut o, &self.context);
        put(&mut o, &self.max_abs_work);
        put(&mut o, self.rational_bits);
        put_work_policy(&mut o,self.work_policy);
        if let Some(frame)=self.framing {put(&mut o,frame.source_cells());put(&mut o,frame.part());}
        put(&mut o, hex(&self.boundary_identity));
        history(&mut o, &self.history);
        put(&mut o, self.lift.len());
        for v in &self.lift {
            put(&mut o, v);
        }
        put(&mut o, self.pairs.len());
        for (a, b) in &self.pairs {
            put(&mut o, a);
            put(&mut o, b);
        }
        put(&mut o, usize::from(self.control.is_some()));
        if let Some(u) = &self.control {
            for v in u {
                put(&mut o, v);
            }
        }
        if self.native_lagged{lag(&mut o,self.lagged.as_ref());}
        o
    }
    pub(crate) fn from_text(field:&Field,text: &str) -> Result<Self, HnnError> {
        if text.len() > 1024 * 1024 {
            return Err(refuse("bounded prepared cut"));
        }
        let mut t = text.split_whitespace();
        let (framed,native_lagged,quadratic)=match t.next(){Some("prepared-input-cut-v1")=>(false,false,false),Some("prepared-input-cut-framing-v1")=>(true,false,false),Some("prepared-input-cut-native-lagged-v1")=>(true,true,false),Some("prepared-input-cut-native-lagged-quadratic-v1")=>(true,true,true),_=>return Err(refuse("prepared cut version"))};
        let source_cells = get(&mut t)?;
        let commit = get(&mut t)?;
        let material_observations = get(&mut t)?;
        let context = get(&mut t)?;
        let max_abs_work = get(&mut t)?;
        let rational_bits = get(&mut t)?;
        let work_policy=read_work_policy(&mut t,quadratic)?;
        let framing=if framed{let cells=get(&mut t)?;let part=get(&mut t)?;if cells!=source_cells{return Err(refuse("original framing frontier"));}Some(SourceFraming::restored(cells,part)?)}else{None};
        let boundary_identity = unhex(t.next().ok_or(refuse("prepared boundary identity"))?)?;
        let history = read_history(&mut t)?;
        let n: usize = get(&mut t)?;
        if n == 0 || n > 64 {
            return Err(refuse("prepared source lift shape"));
        }
        let lift = (0..n).map(|_| get(&mut t)).collect::<Result<Vec<_>, _>>()?;
        if get::<usize>(&mut t)? != 4 {
            return Err(refuse("complete four-class pairing"));
        }
        let pairs = (0..4)
            .map(|_| Ok((get(&mut t)?, get(&mut t)?)))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let control = match get::<u8>(&mut t)? {
            0 => None,
            1 => Some((0..4).map(|_| get(&mut t)).collect::<Result<Vec<_>, _>>()?),
            _ => return Err(refuse("prepared control presence")),
        };
        let lagged=if native_lagged{read_lag(field,&mut t)?}else{None};
        if let Some(l)=&lagged{if l.source_cells.checked_add(1)!=Some(source_cells)||l.commit>commit{return Err(refuse("original lag and next prepared source cut"));}}
        if native_lagged && (source_cells>0)!=lagged.is_some(){return Err(refuse("explicit initial lag absence and later reached context"));}
        let feature=if native_lagged{lagged_features(&history,lagged.as_ref(),&lift)}else{features(&history,&context)};
        if feature.is_some() != control.is_some()
            || t.next().is_some()
            || !(64..=4096).contains(&rational_bits)
            || max_abs_work < Rat::zero()
        {
            return Err(refuse("prepared cut complete finite domain"));
        }
        Ok(Self {
            source_cells, native_lagged,lagged,
            framing,
            commit,
            lift,
            history,
            context,
            feature,
            control,
            material_observations,
            boundary_identity,
            pairs,
            max_abs_work,
            rational_bits,work_policy,
        })
    }
}
impl PreparedInputState {
    pub(crate) fn to_text(&self) -> String {
        let mut o = format!("{} ",self.law());
        for v in [
            self.bounds.pending,
            self.bounds.precision_bits as usize,
            self.bounds.rational_bits as usize,
            self.bounds.max_scalar_work as usize,
        ] {
            put(&mut o, v);
        }
        put(&mut o, self.max_abs_work.clone());
        put_work_policy(&mut o,self.work_policy);
        put(
            &mut o,
            match self.mode {
                PrefixMode::Training => 0,
                PrefixMode::Forecast => 1,
                PrefixMode::ForecastZeroControl => 2,
            },
        );
        put(&mut o, role(self.forecast_role));
        for n in [
            self.training,
            self.conditioning,
            self.generated,
            self.fit_proposals,
        ] {
            put(&mut o, n);
        }
        put(&mut o, hex(&self.boundary_identity));
        for (a, b) in &self.pairs {
            put(&mut o, a);
            put(&mut o, b);
        }
        history(&mut o, &self.history);
        for v in [&self.source_octet, &self.generated_octet] {
            put(&mut o, v.len());
            for c in v {
                put(&mut o, c);
            }
        }
        put(&mut o, hex(&self.material.text()));
        put(&mut o, self.pending.len());
        for (id, p) in &self.pending {
            put(&mut o, id);
            put(&mut o, p.actual);
            put(&mut o, hex(&p.cut.to_text()));
        }
        if self.context_chart()==ContextChart::LaggedReceiverBoundaryV1{for count in self.eligible{put(&mut o,count);}lag(&mut o,self.lagged.as_ref());}
        // Refusal diagnostics are exterior, not constitutive retention.
        o
    }
    pub(crate) fn from_text(
        field: &Field,
        theta: &Constitution,
        text: &str,
    ) -> Result<Self, HnnError> {
        if text.len() > 8 * 1024 * 1024 {
            return Err(refuse("bounded prepared continuation"));
        }
        let mut t = text.split_whitespace();
        let tag=t.next();let quadratic=tag==Some(LAGGED_RECEIVER_QUADRATIC_LAW);
        let chart=match tag{Some(LAW)=>ContextChart::ScalarV1,Some(SOURCE_FRAMING_LAW)=>ContextChart::SourceFramingRouteV1,Some(LAGGED_RECEIVER_LAW)|Some(LAGGED_RECEIVER_QUADRATIC_LAW)=>ContextChart::LaggedReceiverBoundaryV1,_=>return Err(refuse("prepared input continuation law identity"))};
        let framed=field.receivers().iter().all(|r|field.receiving_context(r.ring)==Some(crate::hnn::receiving::ObservationPartition::SourceFramingRouteV1));
        if framed!=chart.framed(){return Err(refuse("saved material schema and actual tree framing declaration agree"));}
        let bounds = ContextualBounds {
            branches: 1,
            pending: get(&mut t)?,
            precision_bits: get(&mut t)?,
            rational_bits: get(&mut t)?,
            max_features: chart.features(),
            max_scalar_work: get(&mut t)?,
        };
        bounds.admit()?;
        let max_abs_work = get(&mut t)?;
        let work_policy=read_work_policy(&mut t,quadratic)?;
        let mode = match get::<u8>(&mut t)? {
            0 => PrefixMode::Training,
            1 => PrefixMode::Forecast,
            2 => PrefixMode::ForecastZeroControl,
            _ => return Err(refuse("prepared mode")),
        };
        let forecast_role = read_role(&mut t)?;
        let training = get(&mut t)?;
        let conditioning = get(&mut t)?;
        let generated = get(&mut t)?;
        let fit_proposals = get(&mut t)?;
        let boundary_identity = unhex(t.next().ok_or(refuse("prepared boundary"))?)?;
        let pairs = (0..4)
            .map(|_| Ok((get(&mut t)?, get(&mut t)?)))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let pairing = PairingDeclaration::Family {
            table: pairs.clone(),
        };
        let boundary = PairedObservation::admit(field, theta, &pairing)?;
        if field.alphabet() != 4
            || field.sources() != [0]
            || boundary.immutable_identity_text() != boundary_identity
            || max_abs_work < Rat::zero()
        {
            return Err(refuse(
                "prepared continuation actual source chart/units/domain",
            ));
        }
        let history = read_history(&mut t)?;
        let mut octet = || -> Result<Vec<usize>, HnnError> {
            let n: usize = get(&mut t)?;
            if n > 3 {
                return Err(refuse("unfinished base4 octet"));
            }
            (0..n)
                .map(|_| {
                    let c = get(&mut t)?;
                    if c >= 4 {
                        return Err(refuse("fourclass unfinished octet"));
                    }
                    Ok(c)
                })
                .collect()
        };
        let source_octet = octet()?;
        let generated_octet = octet()?;
        let material = PreparedMaterial::restored(chart,&unhex(t.next().ok_or(refuse("prepared material"))?)?,&bounds)?;
        if material.parts().iter().flat_map(|m|m.normal().iter().chain(m.cross()).chain(m.applied())).flatten().any(|z|!z[1].is_zero()){return Err(refuse("separate real class material"));}
        let n: usize = get(&mut t)?;
        if n > bounds.pending {
            return Err(refuse("bounded original class returns"));
        }
        let mut pending = BTreeMap::new();
        for _ in 0..n {
            let id = get(&mut t)?;
            let actual = get(&mut t)?;
            let cut = PreparedInputCut::from_text(field,&unhex(
                t.next().ok_or(refuse("original prepared material cut"))?,
            )?)?;
            if actual >= 4
                || id != cut.source_cells
                || id >= training
                || cut.boundary_identity != boundary_identity
                || cut.framing.is_some() != chart.framed()
                || cut.native_lagged != (chart==ContextChart::LaggedReceiverBoundaryV1)
                || cut.work_policy != work_policy
                || pending.insert(id, MaterialReturn { cut, actual }).is_some()
            {
                return Err(refuse("original jointly bound class return"));
            }
        }
        if chart==ContextChart::SourceFramingRouteV1{for phase in 0..4usize{
            let reached=training/4+u64::from((phase as u64)<training%4)-u64::from(phase<2&&(phase as u64)<training);
            let pending_count=pending.values().filter(|p|p.cut.framing.map(SourceFraming::part)==Some(phase)).count() as u64;
            if material.parts()[phase].observations().checked_add(pending_count)!=Some(reached){return Err(refuse("original phase material and pending evidence accounting"));}
        }}
        let mut eligible=[0u64;4];let lagged=if chart==ContextChart::LaggedReceiverBoundaryV1{
            for phase in 0..4{eligible[phase]=get(&mut t)?;let pending_count=pending.values().filter(|p|p.cut.framing.map(SourceFraming::part)==Some(phase)).count() as u64;
                if material.parts()[phase].observations().checked_add(pending_count)!=Some(eligible[phase])||eligible[phase]!=training/4+u64::from((phase as u64)<training%4)-u64::from(phase<2&&(phase as u64)<training){return Err(refuse("native material evidence is exactly its originally available feature returns"));}}
            read_lag(field,&mut t)?
        }else{None};
        let total = u64::checked_add(training, conditioning)
            .and_then(|n| n.checked_add(generated))
            .ok_or(HnnError::CountOverflow)?;
        if t.next().is_some()
            || total > field.population()
            || history.len() as u64 != total.min(2)
            || source_octet.len() as u64 != total % 4
            || generated_octet.len() as u64 != generated % 4
            || material.observations() + pending.len() as u64 != if chart==ContextChart::LaggedReceiverBoundaryV1{eligible.iter().sum()}else{training.saturating_sub(2)}
            || mode == PrefixMode::Training
                && (conditioning != 0
                    || generated != 0
                    || history.iter().any(|(_, r)| *r != PrefixRole::Observed))
            || mode != PrefixMode::Training && forecast_role == PrefixRole::Observed
        {
            return Err(refuse(
                "prepared mode/material/actual and hypothesis frontier accounting",
            ));
        }
        if chart==ContextChart::LaggedReceiverBoundaryV1 && (total>0)!=lagged.is_some(){return Err(refuse("cold original lag availability"));}
        if let Some(l)=&lagged{if l.source_cells.checked_add(1)!=Some(total)||l.commit>theta.commit(){return Err(refuse("cold lag keeps its original reached cut and availability"));}}
        Ok(Self {
            mode,
            forecast_role,
            pairs,
            boundary_identity,
            bounds,
            max_abs_work,work_policy,
            history,
            material,
            training,
            conditioning,
            generated,
            source_octet,
            generated_octet,
            pending,
            fit_proposals,lagged,eligible,
            last_refusal: None,
        })
    }
}
