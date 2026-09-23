//! **The rest of the published constitutive continuation** (plan phase 12b).
//!
//! [definition; agent-inferred] Frame v7 is the continuation's retained quotient: the coupled
//! wave rest (its contemporary constitution, family and pending source operands) with the
//! consumed root's address and the two counts. Frames v1–v6 carried a frozen pre-return base, the
//! root comparison's operands and the ordered operation programme; they still decode, and a
//! remount replays that programme **once** through the one-cut continuation (the legacy wire
//! decoder), then writes v7. The replayed numbers are the contemporary-read ones: a later return
//! reads its comparison at the contemporary cut and at its source family's receiver, not at a
//! face imposed at its producing epoch.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, point_bytes, read_blob, read_point,
};
use std::io::{Read, Write};
const MAGIC_V1: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x01";
const MAGIC_V2: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x02";
const MAGIC_V3: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x03";
const MAGIC_V4: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x04";
const MAGIC_V5: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x05";
const MAGIC_V6: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x06";
const MAGIC: &[u8] = b"HOLONIC-COUPLED-CONSTITUTIVE\x07";

#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    prediction: u64,
    material_returns: usize,
    source_passages: usize,
}

/// The rest of a [`ResidentCoupledConstitutive`] (see the module header).
#[derive(Debug, PartialEq, Eq)]
pub struct CoupledConstitutiveRest {
    form: Form,
}
#[derive(Debug, PartialEq, Eq)]
enum Form {
    Published { header: Header, wave: NormalWaveRest },
    Legacy(legacy::LegacyRest),
}
fn invalid(e: impl ToString) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(e.to_string())
}
impl CoupledConstitutiveRest {
    pub fn epoch(&self) -> u64 {
        match &self.form {
            Form::Published { header, .. } => header.epoch,
            Form::Legacy(rest) => rest.epoch(),
        }
    }
    fn wave(&self) -> &NormalWaveRest {
        match &self.form {
            Form::Published { wave, .. } => wave,
            Form::Legacy(rest) => rest.base(),
        }
    }
    pub fn roots(&self) -> usize {
        self.wave().material().roots()
    }
    pub fn members(&self) -> usize {
        self.wave().coupled_members().unwrap_or(0)
    }
    pub fn has_prediction(&self, id: u64) -> bool {
        match &self.form {
            Form::Published { wave, .. } => wave.has_coupled_prediction(id),
            Form::Legacy(rest) => rest.has_prediction(id),
        }
    }
    pub fn consumed_prediction(&self) -> u64 {
        match &self.form {
            Form::Published { header, .. } => header.prediction,
            Form::Legacy(rest) => rest.consumed_prediction(),
        }
    }
    /// Whether this rest is a legacy programme frame (v1–v6) awaiting its one decode.
    pub fn is_legacy_programme(&self) -> bool {
        matches!(self.form, Form::Legacy(_))
    }
    fn validate(header: &Header, wave: &NormalWaveRest) -> Result<(), ConstitutiveFibreError> {
        if !wave.is_coupled()
            || wave.epoch() != header.epoch
            || header.material_returns == 0
            || wave.has_coupled_prediction(header.prediction)
        {
            return Err(invalid("constitutive continuation clock or consumed root"));
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
        match &self.form {
            Form::Legacy(rest) => rest.write(out),
            Form::Published { header, wave } => {
                Self::validate(header, wave)?;
                out.write_all(MAGIC).map_err(invalid)?;
                blob(out, &serde_json::to_vec(header).map_err(invalid)?)?;
                let mut bytes = Vec::new();
                wave.write(&mut bytes)?;
                blob(out, &bytes)
            }
        }
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, ConstitutiveFibreError> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic).map_err(invalid)?;
        if magic != MAGIC {
            let version = [MAGIC_V1, MAGIC_V2, MAGIC_V3, MAGIC_V4, MAGIC_V5, MAGIC_V6]
                .iter()
                .position(|m| *m == magic.as_slice())
                .ok_or_else(|| invalid("dependent continuation magic"))?
                + 1;
            return Ok(Self {
                form: Form::Legacy(legacy::LegacyRest::read(&mut input, version as u8)?),
            });
        }
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let bytes = read_blob(&mut input)?;
        let wave = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if input.limit() != 0 {
            return Err(invalid("trailing constitutive continuation"));
        }
        Self::validate(&header, &wave)?;
        Ok(Self {
            form: Form::Published { header, wave },
        })
    }
    pub fn remount<'c>(
        self,
        s: &'c ResidentSurface<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, ConstitutiveFibreError> {
        match self.form {
            Form::Legacy(rest) => rest.remount(s),
            Form::Published { header, wave } => {
                Self::validate(&header, &wave)?;
                let wave = wave.remount_coupled(s, |_| {})?;
                Ok(ResidentCoupledConstitutive {
                    wave,
                    consumed: header.prediction,
                    material_returns: header.material_returns,
                    source_passages: header.source_passages,
                })
            }
        }
    }
}
impl<'c> ResidentCoupledConstitutive<'c> {
    pub fn rest(&self) -> Result<CoupledConstitutiveRest, ConstitutiveFibreError> {
        let header = Header {
            epoch: self.epoch(),
            prediction: self.consumed,
            material_returns: self.material_returns,
            source_passages: self.source_passages,
        };
        let wave = self.wave.rest()?;
        CoupledConstitutiveRest::validate(&header, &wave)?;
        Ok(CoupledConstitutiveRest {
            form: Form::Published { header, wave },
        })
    }
}

/// The v1–v6 programme frames and their one-time decode.
mod legacy {
    use super::*;

    /// An original producing source address of a legacy programme frame.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(tag = "frame", rename_all = "kebab-case", deny_unknown_fields)]
    pub(super) enum SourceFrame {
        Programme {
            prefix: usize,
            member: usize,
            chart: WaveSourceReceiver,
        },
        Base {
            member: usize,
            chart: WaveSourceReceiver,
        },
    }
    impl SourceFrame {
        fn member(&self) -> usize {
            match self {
                Self::Programme { member, .. } | Self::Base { member, .. } => *member,
            }
        }
        fn chart(&self) -> WaveSourceReceiver {
            match self {
                Self::Programme { chart, .. } | Self::Base { chart, .. } => *chart,
            }
        }
        fn prefix(&self) -> Option<usize> {
            match self {
                Self::Programme { prefix, .. } => Some(*prefix),
                Self::Base { .. } => None,
            }
        }
    }
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    struct ProducingCut {
        prefix: usize,
        member: usize,
        chart: WaveSourceReceiver,
    }
    impl From<ProducingCut> for SourceFrame {
        fn from(c: ProducingCut) -> Self {
            Self::Programme {
                prefix: c.prefix,
                member: c.member,
                chart: c.chart,
            }
        }
    }
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(rename_all = "kebab-case")]
    enum PassageKind {
        #[default]
        Source,
        FieldInteger,
        FieldRational,
        ObserveInteger,
        ObserveRational,
        Advance,
        Return,
        Empirical {
            prediction: u64,
            cut: SourceFrame,
        },
        Condition {
            inputs: u64,
        },
    }
    impl PassageKind {
        fn moves_wave(self) -> bool {
            !matches!(self, Self::Empirical { .. } | Self::Condition { .. })
        }
        fn condition_inputs(self) -> Option<u64> {
            match self {
                Self::Condition { inputs } => Some(inputs),
                _ => None,
            }
        }
        fn empirical_cut(self) -> Option<(u64, SourceFrame)> {
            match self {
                Self::Empirical { prediction, cut } => Some((prediction, cut)),
                _ => None,
            }
        }
    }
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct ReturnedHeader {
        prediction: u64,
        cut: SourceFrame,
    }
    #[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct V3ReturnedHeader {
        prediction: u64,
        cut: ProducingCut,
    }
    #[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct V3SourceHeader {
        member: usize,
        chart: WaveSourceReceiver,
        #[serde(default)]
        kind: PassageKind,
        #[serde(default)]
        returned: Option<V3ReturnedHeader>,
    }
    #[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct V3Header {
        epoch: u64,
        prediction: u64,
        #[serde(alias = "sources")]
        operations: Vec<V3SourceHeader>,
        #[serde(default)]
        pending: BTreeMap<u64, ProducingCut>,
        #[serde(default)]
        released: std::collections::BTreeSet<u64>,
    }
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct SourceHeader {
        member: usize,
        chart: WaveSourceReceiver,
        #[serde(default)]
        kind: PassageKind,
        #[serde(default)]
        returned: Option<ReturnedHeader>,
    }
    impl SourceHeader {
        fn returned_cut(&self) -> Option<(u64, SourceFrame)> {
            self.kind
                .empirical_cut()
                .or_else(|| self.returned.as_ref().map(|r| (r.prediction, r.cut)))
        }
    }
    #[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct ProgrammeHeader {
        epoch: u64,
        prediction: u64,
        #[serde(alias = "sources")]
        operations: Vec<SourceHeader>,
        #[serde(default)]
        pending: BTreeMap<u64, ProducingCut>,
        #[serde(default)]
        released: std::collections::BTreeSet<u64>,
    }
    fn operation_epoch(
        base: u64,
        operations: &[SourceHeader],
        index: usize,
    ) -> Result<u64, ConstitutiveFibreError> {
        let prefix = operations
            .get(..=index)
            .ok_or(ConstitutiveFibreError::Shape)?;
        base.checked_add(1)
            .and_then(|v| v.checked_add(prefix.iter().filter(|p| p.kind.moves_wave()).count() as u64))
            .ok_or(ConstitutiveFibreError::Shape)
    }
    fn owned<'c>(
        source: &mut Option<ResidentSection<'c>>,
    ) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
        source.take().ok_or(ConstitutiveFibreError::Shape)
    }
    fn borrowed<'a, 'c>(
        source: &'a Option<ResidentSection<'c>>,
    ) -> Result<&'a ResidentSection<'c>, ConstitutiveFibreError> {
        source.as_ref().ok_or(ConstitutiveFibreError::Shape)
    }
    /// A v1–v6 programme frame, kept until its one decode.
    #[derive(Debug, PartialEq, Eq)]
    pub(super) struct LegacyRest {
        version: u8,
        header: ProgrammeHeader,
        base: NormalWaveRest,
        observation: ResidentSectionRest,
        receiver: ResidentSectionRest,
        sources: Vec<Option<ResidentSectionRest>>,
        return_faces: Vec<Option<ResidentSectionRest>>,
    }
    impl LegacyRest {
        pub(super) fn epoch(&self) -> u64 {
            self.header.epoch
        }
        pub(super) fn base(&self) -> &NormalWaveRest {
            &self.base
        }
        pub(super) fn consumed_prediction(&self) -> u64 {
            self.header.prediction
        }
        pub(super) fn has_prediction(&self, id: u64) -> bool {
            let returned = self
                .header
                .operations
                .iter()
                .any(|op| op.returned_cut().is_some_and(|r| r.0 == id));
            self.header.pending.contains_key(&id)
                || (!returned
                    && id != self.header.prediction
                    && !self.header.released.contains(&id)
                    && self.base.has_coupled_prediction(id))
        }
        /// Written as the programme writer did: frame v4, v5 or v6 by content.
        pub(super) fn write(&self, out: &mut impl Write) -> Result<(), ConstitutiveFibreError> {
            let ops = &self.header.operations;
            out.write_all(if ops.iter().any(|p| p.kind.condition_inputs().is_some()) {
                MAGIC_V6
            } else if ops.iter().any(|p| p.kind.empirical_cut().is_some()) {
                MAGIC_V5
            } else {
                MAGIC_V4
            })
            .map_err(invalid)?;
            let header = serde_json::to_vec(&self.header).map_err(invalid)?;
            blob(out, &header)?;
            let mut base = Vec::new();
            self.base.write(&mut base)?;
            blob(out, &base)?;
            for packet in std::iter::once(Some(&self.observation))
                .chain(std::iter::once(Some(&self.receiver)))
                .chain(
                    self.sources
                        .iter()
                        .zip(&self.return_faces)
                        .flat_map(|(source, face)| [source.as_ref(), face.as_ref()]),
                )
                .flatten()
            {
                blob(out, &point_bytes(packet)?)?;
            }
            Ok(())
        }
        pub(super) fn read(
            input: &mut std::io::Take<impl Read>,
            version: u8,
        ) -> Result<Self, ConstitutiveFibreError> {
            let header_bytes = read_blob(input)?;
            let header: ProgrammeHeader = if version >= 4 {
                serde_json::from_slice(&header_bytes).map_err(invalid)?
            } else {
                let old: V3Header = serde_json::from_slice(&header_bytes).map_err(invalid)?;
                ProgrammeHeader {
                    epoch: old.epoch,
                    prediction: old.prediction,
                    operations: old
                        .operations
                        .into_iter()
                        .map(|op| SourceHeader {
                            member: op.member,
                            chart: op.chart,
                            kind: op.kind,
                            returned: op.returned.map(|r| ReturnedHeader {
                                prediction: r.prediction,
                                cut: r.cut.into(),
                            }),
                        })
                        .collect(),
                    pending: old.pending,
                    released: old.released,
                }
            };
            if version == 1 && (!header.pending.is_empty() || !header.released.is_empty()) {
                return Err(invalid("pending disposition requires dependent frame v2"));
            }
            let bytes = read_blob(input)?;
            let base = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
            if !base.has_coupled_prediction(header.prediction)
                || header
                    .operations
                    .iter()
                    .filter(|op| op.kind != PassageKind::Advance)
                    .count() as u64
                    > input.limit() / 8
                || base.epoch().checked_add(1).and_then(|v| {
                    v.checked_add(
                        header.operations.iter().filter(|p| p.kind.moves_wave()).count() as u64,
                    )
                }) != Some(header.epoch)
            {
                return Err(invalid("dependent continuation chronology or producing cut"));
            }
            let observation = read_point(&read_blob(input)?)?;
            let receiver = read_point(&read_blob(input)?)?;
            let mut sources = Vec::new();
            let mut return_faces = Vec::new();
            let mut returned_predictions = std::collections::BTreeSet::new();
            for (operation_index, op) in header.operations.iter().enumerate() {
                if version < 5 && op.kind.empirical_cut().is_some() {
                    return Err(invalid("empirical material return requires dependent frame v5"));
                }
                if version < 6 && op.kind.condition_inputs().is_some() {
                    return Err(invalid("known condition input requires dependent frame v6"));
                }
                if op.kind != PassageKind::Return && op.returned.is_some() {
                    return Err(invalid("return metadata on non-return operation"));
                }
                if version <= 2 && op.kind == PassageKind::Return {
                    return Err(invalid("return operation requires dependent frame v4"));
                }
                if version == 1 && op.kind != PassageKind::Source {
                    return Err(invalid("operation requires dependent frame v2"));
                }
                sources.push(if op.kind == PassageKind::Advance {
                    None
                } else {
                    Some(read_point(&read_blob(input)?)?)
                });
                if op.kind == PassageKind::Return || op.kind.empirical_cut().is_some() {
                    let (prediction, cut) =
                        op.returned_cut().ok_or(ConstitutiveFibreError::Shape)?;
                    if !returned_predictions.insert(prediction) || prediction == header.prediction {
                        return Err(invalid("dependent return predecessor cut"));
                    }
                    if op.member != cut.member() || op.chart != cut.chart() {
                        return Err(invalid("dependent return member/chart"));
                    }
                    if let Some(prefix) = cut.prefix() {
                        if prefix >= operation_index
                            || prediction != operation_epoch(base.epoch(), &header.operations, prefix)?
                        {
                            return Err(invalid("dependent return predecessor cut"));
                        }
                        let predecessor = header
                            .operations
                            .get(prefix)
                            .ok_or(ConstitutiveFibreError::Shape)?;
                        if predecessor.kind != PassageKind::Advance
                            || predecessor.member != cut.member()
                            || predecessor.chart != cut.chart()
                        {
                            return Err(invalid(
                                "dependent return does not name its actual operation",
                            ));
                        }
                    } else if !base.has_coupled_prediction(prediction) {
                        return Err(invalid("dependent base return predecessor"));
                    }
                    return_faces.push(if op.kind == PassageKind::Return {
                        Some(read_point(&read_blob(input)?)?)
                    } else {
                        None
                    });
                } else {
                    return_faces.push(None);
                }
            }
            for (id, cut) in &header.pending {
                if returned_predictions.contains(id) {
                    return Err(invalid("returned predecessor remains pending"));
                }
                let op = header
                    .operations
                    .get(cut.prefix)
                    .ok_or(ConstitutiveFibreError::Shape)?;
                if op.kind != PassageKind::Advance
                    || op.member != cut.member
                    || op.chart != cut.chart
                    || operation_epoch(base.epoch(), &header.operations, cut.prefix)? != *id
                {
                    return Err(invalid(
                        "dependent producing cut does not name its actual operation",
                    ));
                }
            }
            if header.released.iter().any(|id| {
                *id == header.prediction
                    || returned_predictions.contains(id)
                    || !base.has_coupled_prediction(*id)
            }) {
                return Err(invalid("released dependent predecessor cut"));
            }
            if input.limit() != 0 {
                return Err(invalid("trailing dependent continuation"));
            }
            Ok(Self {
                version,
                header,
                base,
                observation,
                receiver,
                sources,
                return_faces,
            })
        }
        /// The one decode: return the root at its declared receiver on the remounted base, then
        /// act the ordered programme once through the one-cut continuation. A later return reads
        /// its comparison at the contemporary cut and at its source family's receiver.
        pub(super) fn remount<'c>(
            self,
            s: &'c ResidentSurface<'c>,
        ) -> Result<ResidentCoupledConstitutive<'c>, ConstitutiveFibreError> {
            let LegacyRest {
                header,
                base,
                observation,
                receiver,
                sources,
                ..
            } = self;
            let base_epoch = base.epoch();
            let base = base.remount_coupled(s, |_| {})?;
            let observation = s.mount_section_rest(&observation)?;
            let comparison = base.compare_coupled_prediction(
                header.prediction,
                ResidentConstitutiveCurrent::rational(&observation)?,
            )?;
            let receiver = s.mount_section_rest(&receiver)?;
            let mut model = base
                .into_constitutive_continuation(comparison, receiver)
                .map_err(|r| r.reason)?;
            for (index, (op, source)) in header.operations.iter().zip(sources).enumerate() {
                let id = operation_epoch(base_epoch, &header.operations, index)?;
                let mut source = source
                    .map(|v| s.mount_section_rest(&v).map_err(ConstitutiveFibreError::from))
                    .transpose()?;
                match op.kind {
                    PassageKind::Source => model
                        .actuate_source(op.member, op.chart, owned(&mut source)?)
                        .map_err(|r| r.reason)?,
                    PassageKind::FieldInteger | PassageKind::FieldRational => model
                        .actuate_field(
                            op.member,
                            op.chart,
                            owned(&mut source)?,
                            op.kind == PassageKind::FieldRational,
                        )
                        .map_err(|r| r.reason)?,
                    PassageKind::ObserveInteger | PassageKind::ObserveRational => model
                        .receive_next_current(
                            op.member,
                            op.chart,
                            owned(&mut source)?,
                            op.kind == PassageKind::ObserveRational,
                        )
                        .map_err(|r| r.reason)?,
                    PassageKind::Advance => {
                        let retained = header.pending.contains_key(&id)
                            || header.operations.iter().skip(index + 1).any(|later| {
                                later.returned_cut().and_then(|(_, cut)| cut.prefix()) == Some(index)
                            });
                        if retained {
                            if model.predict_member(op.member, op.chart)? != id {
                                return Err(invalid("legacy programme prediction address"));
                            }
                        } else {
                            model.advance_member(op.member, op.chart)?;
                        }
                    }
                    PassageKind::Return => {
                        let (prediction, _) = op.returned_cut().ok_or(ConstitutiveFibreError::Shape)?;
                        model.incorporate_prediction(
                            prediction,
                            ResidentConstitutiveCurrent::rational(borrowed(&source)?)?,
                        )?;
                    }
                    PassageKind::Empirical { prediction, cut } => {
                        let grain = model
                            .wave()
                            .neighborhood()
                            .predictive_material(cut.member())?
                            .ok_or(ConstitutiveFibreError::Shape)?
                            .grain();
                        let observed = ResidentNormalEnclosureView {
                            surface: s,
                            section: borrowed(&source)?,
                            offset: 0,
                            width: 2 * model.roots(),
                            grain,
                        };
                        model.observe_prediction(prediction, observed)?;
                    }
                    PassageKind::Condition { .. } => {
                        model.receive_condition(ResidentConstitutiveCurrent::rational(borrowed(&source)?)?)?;
                    }
                }
            }
            for id in &header.released {
                model.release_prediction(*id)?;
            }
            if model.epoch() != header.epoch {
                return Err(invalid("legacy programme successor clock"));
            }
            Ok(model)
        }
    }
}
