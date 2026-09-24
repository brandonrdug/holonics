//! Incidence-derived source/condition formation through the same field session and body.
use super::super::{GeometricFieldSpec, NativeFieldGeneratedSection};
use super::*;
use holonic_engine::{
    AnalyticFieldJunctionId,
    native_ecology::constitutive_fibre::{ResidentContextualSection, ResidentNormalInput},
};

/// The analytic source law and participating receiver. Port widths come from the field.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldSourceSpec {
    pub geometry: GeometricFieldSpec,
    pub receiver: AnalyticFieldJunctionId,
}

struct PreparedNativeCut<'c> {
    epoch: u64,
    preparation: ResidentSection<'c>,
    source: ResidentSection<'c>,
    condition: ResidentSection<'c>,
}
/// Native presentation state. Only outstanding pre-target cuts are retained as source packets;
/// completed observations continue in the existing normal moments and compatibility relation.
pub struct NativeFieldSources<'c> {
    spec: NativeFieldSourceSpec,
    incidence: NativeFieldIncidence<'c>,
    pending: BTreeMap<u64, PreparedNativeCut<'c>>,
    next: u64,
}

/// A refused attachment returns the supplied continuing field and source declaration.
pub struct NativeFieldSourceAttachRefusal<'c> {
    pub field: NativeConstitutiveField<'c>,
    pub spec: NativeFieldSourceSpec,
    pub reason: NativeSessionError,
}
impl std::fmt::Debug for NativeFieldSourceAttachRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeFieldSourceAttachRefusal")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}

impl<'c> NativeFieldSession<'c, NativeFieldSources<'c>> {
    /// Attach actual field material and analytic incidence. No alphabet determines a model port,
    /// and no synthetic occurrence is inserted to prime this field.
    pub fn from_native_field(
        surface: &'c ResidentSurface<'c>,
        field: NativeConstitutiveField<'c>,
        spec: NativeFieldSourceSpec,
    ) -> std::result::Result<Self, NativeFieldSourceAttachRefusal<'c>> {
        let prepared = (|| -> Result<_> {
            let source_complex = field
                .nodes()
                .checked_mul(3)
                .ok_or_else(|| invalid("native field width"))?;
            let incidence = NativeFieldIncidence::compile(
                surface,
                &spec.geometry,
                spec.receiver,
                source_complex,
            )?;
            let condition_complex = incidence.condition_complex();
            let features = source_complex
                .checked_mul(condition_complex)
                .and_then(|n| {
                    n.checked_add(source_complex)?
                        .checked_add(condition_complex)
                })
                .ok_or_else(|| invalid("native field feature extent"))?;
            let grain = match field.junction_representation() {
            Some(holonic_engine::native_ecology::constitutive_fibre::NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => ResidentGrain(fractional_bits),
            _ => return Err(invalid("native source session requires the enclosed operative field")),
        };
            let initial = surface
                .mount_exact_rational_packet(&vec![
                    num_rational::BigRational::from_integer(0.into());
                    2 * condition_complex
                ])
                .map_err(invalid)?;
            let law = ResidentConstitutiveFibre::found_bilinear_contact(
                surface,
                source_complex,
                condition_complex,
                source_complex,
            )?;
            let material =
                ResidentNormalMaterial::found_features(surface, features, source_complex, grain)?;
            let mut reaction = ResidentGeneratorNeighborhood::with_shared_condition(
                vec![law],
                ResidentConstitutiveCurrent::rational(&initial)?,
                ConditionContactMetric::UnitAdmittanceRealification,
            )?;
            reaction
                .attach_normal_prediction(0, material)
                .map_err(|r| r.reason)?;
            Ok((incidence, reaction))
        })();
        let (incidence, reaction) = match prepared {
            Ok(p) => p,
            Err(reason) => {
                return Err(NativeFieldSourceAttachRefusal {
                    field,
                    spec,
                    reason,
                });
            }
        };
        let body = match NativeCoupledBody::from_field_with_reaction_port(
            field,
            reaction,
            0,
            NativeFieldReactionPort::IncomingBoundary,
        ) {
            Ok(body) => body,
            Err(refusal) => {
                return Err(NativeFieldSourceAttachRefusal {
                    field: refusal.field,
                    spec,
                    reason: refusal.reason,
                });
            }
        };
        Ok(Self {
            surface,
            body,
            incident: None,
            generator: None,
            presentation: NativeFieldSources {
                spec,
                incidence,
                pending: BTreeMap::new(),
                next: 0,
            },
        })
    }

    pub fn source_spec(&self) -> &NativeFieldSourceSpec {
        &self.presentation.spec
    }
    pub fn incidence(&self) -> &NativeFieldIncidence<'c> {
        &self.presentation.incidence
    }
    pub fn body(&self) -> &NativeCoupledBody<'c> {
        &self.body
    }
    pub fn inspect_material(&mut self) -> Result<Value> {
        self.body.inspect_predictive_material(0)
    }
    pub fn inspect_native_current(&mut self) -> Result<Value> {
        self.body.inspect_current()
    }
    pub fn pending_preparations(&self) -> Vec<u64> {
        self.presentation.pending.keys().copied().collect()
    }

    /// Both restrictions read the same actual packet before a target is accepted. The returned
    /// delivery address is local bookkeeping, never a feature or a native clock.
    pub fn prepare_native(&mut self, preparation: &ResidentSection<'c>) -> Result<u64> {
        let next = self
            .presentation
            .next
            .checked_add(1)
            .ok_or_else(|| invalid("native preparation addresses exhausted"))?;
        let prepared = self.presentation.incidence.prepare(preparation)?;
        let original =
            ResidentConstitutiveCurrent::rational(preparation)?.to_owned(self.surface)?;
        let source = prepared.source()?.to_owned(self.surface)?;
        let condition = prepared.condition()?.to_owned(self.surface)?;
        let id = self.presentation.next;
        self.presentation.pending.insert(
            id,
            PreparedNativeCut {
                epoch: self.body.epoch(),
                preparation: original,
                source,
                condition,
            },
        );
        self.presentation.next = next;
        Ok(id)
    }

    /// Execute the inferred M on the prepared source and its actual incident contrast. The
    /// joint reflection commits its continuing current only when requested.
    pub fn generate_native(
        &mut self,
        preparation: u64,
        commit: bool,
        retain_comparison: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>> {
        let p = self
            .presentation
            .pending
            .get(&preparation)
            .ok_or_else(|| invalid("unknown native preparation"))?;
        let source = ResidentConstitutiveCurrent::rational(&p.source)?;
        let condition = ResidentConstitutiveCurrent::rational(&p.condition)?;
        if commit {
            self.body
                .generate_field(source.into(), condition, retain_comparison)
        } else if retain_comparison {
            Err(invalid(
                "a retained field comparison requires its committed producing section",
            ))
        } else {
            self.body.preview_field(source.into(), condition)
        }
    }

    /// Use the neighborhood's inferred contemporary condition on a new admitted source. The
    /// condition is captured before this invocation; no observation is performed here.
    pub fn generate_native_standing(
        &mut self,
        preparation: u64,
        commit: bool,
        retain_comparison: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>> {
        let p = self
            .presentation
            .pending
            .get(&preparation)
            .ok_or_else(|| invalid("unknown native preparation"))?;
        self.body.generate_field_standing(
            ResidentConstitutiveCurrent::rational(&p.source)?.into(),
            commit,
            retain_comparison,
        )
    }

    /// Deposit a supplied reaction relation, as in a mathematical generator request. The target
    /// is eta before S_D, not a post-reflection output. Delayed returns use the saved s and c.
    pub fn form_native_reaction(
        &mut self,
        preparation: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Value> {
        let p = self
            .presentation
            .pending
            .get(&preparation)
            .ok_or_else(|| invalid("unknown native preparation"))?;
        let producing_epoch = p.epoch;
        self.body.form_field_reaction_at(
            ResidentConstitutiveCurrent::rational(&p.source)?,
            ResidentConstitutiveCurrent::rational(&p.condition)?,
            observed,
        )?;
        // Publication succeeded. Remove before any exterior inspection can fail on retry.
        self.presentation.pending.remove(&preparation);
        Ok(
            json!({"preparation_consumed":preparation,"producing_epoch":producing_epoch,"successor_epoch":self.body.epoch(),"target_port":"reaction before field reflection"}),
        )
    }

    /// Return D_s at this exact source, retaining its entire condition/target fibre.
    pub fn contextual_section(&self, preparation: u64) -> Result<ResidentContextualSection<'c>> {
        let p = self
            .presentation
            .pending
            .get(&preparation)
            .ok_or_else(|| invalid("unknown native preparation"))?;
        self.body
            .field_contextual_section(ResidentConstitutiveCurrent::rational(&p.source)?)
    }
    pub fn condition_family_image(
        &self,
        preparation: u64,
    ) -> Result<holonic_engine::native_ecology::constitutive_fibre::ResidentConditionImage<'c>>
    {
        let p = self
            .presentation
            .pending
            .get(&preparation)
            .ok_or_else(|| invalid("unknown native preparation"))?;
        self.body
            .field_condition_image(ResidentConstitutiveCurrent::rational(&p.source)?)
    }
    pub fn release_native_comparison(&mut self, comparison: u64) -> Result<()> {
        self.body.release(comparison)
    }
    pub fn release_native(&mut self, preparation: u64) -> Result<()> {
        self.presentation
            .pending
            .remove(&preparation)
            .map(|_| ())
            .ok_or_else(|| invalid("unknown native preparation"))
    }
    /// Ordinary observed output: the body re-reads the retained comparison's operands through the
    /// contemporary field `D` and reaction material `M` and returns the complete adjoint at that
    /// cut (the retention law; no producing D/M cut is kept).
    pub fn observe_native_output(
        &mut self,
        comparison: u64,
        target: ResidentNormalInput<'_, 'c>,
        step_bits: u32,
    ) -> Result<Value> {
        self.body.observe_field(comparison, target, step_bits)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativePreparationRest {
    epoch: u64,
    /// Only outstanding source material, before any target. A remount re-executes the same
    /// immutable restrictions, so its saved condition cannot be replaced by contemporary h.
    preparation: Vec<u8>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeSourceHeader {
    spec: NativeFieldSourceSpec,
    next: u64,
    pending: BTreeMap<u64, NativePreparationRest>,
}
/// Durable native source presentation and the existing field body, including its required
/// interior and the producing operands of its pending comparisons (never a producing D/M cut).
/// It contains no text alphabet or replay archive of formed examples.
pub struct NativeSourceSavedSession {
    header: NativeSourceHeader,
    body: SavedCoupledBody,
}
const NATIVE_SOURCE_MAGIC: &[u8] = b"HNA-NATIVE-SOURCE\x01";
impl<'c> NativeFieldSession<'c, NativeFieldSources<'c>> {
    pub fn rest_native(&self) -> Result<NativeSourceSavedSession> {
        let pending = self
            .presentation
            .pending
            .iter()
            .map(|(id, p)| {
                Ok((
                    *id,
                    NativePreparationRest {
                        epoch: p.epoch,
                        preparation: self
                            .surface
                            .detach_section(&p.preparation, 64)
                            .map_err(invalid)?
                            .canonical_bytes()
                            .map_err(invalid)?,
                    },
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        Ok(NativeSourceSavedSession {
            header: NativeSourceHeader {
                spec: self.presentation.spec.clone(),
                next: self.presentation.next,
                pending,
            },
            body: self.body.rest()?,
        })
    }
    pub fn checkpoint_native(&self, path: &Path) -> Result<PublicationReceipt<()>> {
        let mut bytes = Vec::new();
        self.rest_native()?.write(&mut bytes)?;
        Ok(publish_new(path, |out| out.write_all(&bytes))?)
    }
}
impl NativeSourceSavedSession {
    pub fn write(&self, out: &mut impl Write) -> Result<()> {
        let header = serde_json::to_vec(&self.header)?;
        let mut body = Vec::new();
        self.body.write(&mut body)?;
        out.write_all(NATIVE_SOURCE_MAGIC)?;
        for part in [&header, &body] {
            out.write_all(&u64::try_from(part.len()).map_err(invalid)?.to_le_bytes())?;
            out.write_all(part)?;
        }
        Ok(())
    }
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        let extent = file.metadata()?.len();
        Self::read(&mut file.take(extent), extent)
    }
    pub fn read(input: &mut impl Read, extent: u64) -> Result<Self> {
        let mut input = input.take(extent);
        let mut magic = vec![0; NATIVE_SOURCE_MAGIC.len()];
        input.read_exact(&mut magic)?;
        if magic != NATIVE_SOURCE_MAGIC {
            return Err(invalid("unsupported native source rest"));
        }
        fn part(input: &mut std::io::Take<impl Read>) -> Result<Vec<u8>> {
            let mut length = [0; 8];
            input.read_exact(&mut length)?;
            let length = u64::from_le_bytes(length);
            if length > input.limit() {
                return Err(invalid("truncated native source rest"));
            }
            let length = usize::try_from(length).map_err(invalid)?;
            let mut bytes = Vec::new();
            bytes.try_reserve_exact(length).map_err(invalid)?;
            bytes.resize(length, 0);
            input.read_exact(&mut bytes)?;
            Ok(bytes)
        }
        let header: NativeSourceHeader = serde_json::from_slice(&part(&mut input)?)?;
        let bytes = part(&mut input)?;
        let body = SavedCoupledBody::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if input.limit() != 0
            || !matches!(body, SavedCoupledBody::Field(_))
            || header
                .pending
                .iter()
                .any(|(id, p)| *id >= header.next || p.epoch > body.epoch())
        {
            return Err(invalid("native source rest body/preparation mismatch"));
        }
        Ok(Self { header, body })
    }
    pub fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<NativeFieldSession<'c, NativeFieldSources<'c>>> {
        let body = self.body.remount(surface)?;
        let (width, conditions, _, port) = body.field_dimensions()?;
        if port != NativeFieldReactionPort::IncomingBoundary {
            return Err(invalid(
                "native incidence requires incoming source reaction",
            ));
        }
        let incidence = NativeFieldIncidence::compile(
            surface,
            &self.header.spec.geometry,
            self.header.spec.receiver,
            width / 2,
        )?;
        if incidence.condition_complex().checked_mul(2) != Some(conditions) {
            return Err(invalid("native incidence/body condition mismatch"));
        }
        let pending = self
            .header
            .pending
            .into_iter()
            .map(|(id, p)| {
                let preparation = surface
                    .mount_section_rest(
                        &ResidentSectionRest::read(&p.preparation).map_err(invalid)?,
                    )
                    .map_err(invalid)?;
                let prepared = incidence.prepare(&preparation)?;
                Ok((
                    id,
                    PreparedNativeCut {
                        epoch: p.epoch,
                        source: prepared.source()?.to_owned(surface)?,
                        condition: prepared.condition()?.to_owned(surface)?,
                        preparation,
                    },
                ))
            })
            .collect::<Result<BTreeMap<_, _>>>()?;
        Ok(NativeFieldSession {
            surface,
            body,
            incident: None,
            generator: None,
            presentation: NativeFieldSources {
                spec: self.header.spec,
                incidence,
                pending,
                next: self.header.next,
            },
        })
    }
    pub fn with_session<T>(
        self,
        f: impl FnOnce(&mut NativeFieldSession<'_, NativeFieldSources<'_>>) -> Result<T>,
    ) -> Result<T> {
        let readout = ResidentReadout::new().map_err(invalid)?;
        let surface = ResidentSurface::on(&readout).map_err(invalid)?;
        let mut session = self.remount(&surface)?;
        f(&mut session)
    }
}
