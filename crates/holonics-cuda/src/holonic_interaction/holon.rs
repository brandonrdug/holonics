//! **The Holonic Interaction as a core Holon.**
//!
//! [definition] Plan phase 3 ([plan](../../../../docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md),
//! [object](../../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)): the interaction's parts
//! are the facets of one `holonic_core` Holon, and this module builds it without changing any
//! existing declaration, reading or wire.
//!
//! | Interaction part | Core facet |
//! |---|---|
//! | [`super::Medium`] (`G`, `Ω`) and [`super::ReceiverBody`] | storage ports with form `G`; `−Ω` in the skew Dirac part |
//! | [`super::Coupling`] | the off-diagonal skew blocks of the same Dirac part |
//! | [`super::ContactFace`] / [`super::ContactDissipation`] | resistive ports on each face's slip, `f_R = J_f e_S`, `R = ⊕ w_f D_f` |
//! | [`super::SourceCurrent`] | external ports, `f_P = Bᵀ e_S`, `e_P = u` |
//! | [`super::Perspective`] | a passive coholon's linear reading ([`HolonicInteraction::perspective_reader`]) |
//! | participating [`super::ReceiverBody`] | a receiver Holon joined at link ports ([`HolonicInteraction::joined_holon`]) |
//! | [`super::Perturbation`] | a constitution replacement whose storage change is deposition work |
//!
//! [proved-derived; implemented-exact] The skew interconnection on ports
//! `σ (joint chart) ⊕ ρ (face slips) ⊕ π (source ports)` is
//!
//! ```text
//!   f_S = −Ω e_S − Jᵀ e_R − B e_P,     f_R = J e_S,     f_P = Bᵀ e_S
//! ```
//!
//! with `J` the stacked face slips over the joint chart. With `e_S = Gq`, `f_S = −q̇` and
//! `e_R = −R f_R` it reads `q̇ = (Ω − JᵀRJ) G q + B u = (Ω − M_contact) G q + B u`, the
//! interaction's own port-Hamiltonian generator ([`HolonicInteraction::generator`]): the medium of
//! `Holon/Conformance.lean::mediumHolon` (`Holon/Conformance.lean::medium_admits`) with its
//! resistance factored through the slips, each face the resistive element of
//! `Holon/Conformance.lean::pairContact_resistive`. The collocated source output and power are
//! `Holon/Conformance.lean::ssm_port_output`. Its point balance is
//! `Holon/Element.lean::PortHolon.power_balance`.
//!
//! [definition; agent-inferred] **The participating receiver as a joined Holon.** A coupling
//! between the media and the receiver body is the skew block `Ω_mr = X`, `Ω_rm = −Xᵀ`. The core
//! interconnection identifies ports with flows opposite and efforts equal
//! (`Holon/Dirac.lean::link`), which alone cannot place a gyrator, so the receiver Holon carries it
//! at its link ports: `q̇_r = Ω_rr e_r + f_L + B_r u`, `e_L = e_r`, `f_P = B_rᵀ e_r`. The media Holon
//! exposes `f_L = Xᵀ e_m` and receives `X e_L`. Joined (`Holon/Law.lean::PortHolon.interconnect`),
//! `f_L^r = −Xᵀ e_m` and the media receive `X e_r`: exactly the joint structure. A contact face that
//! reaches the receiver's coordinates would couple the two Holons resistively across the link and
//! is refused by name rather than approximated.
//!
//! [definition; agent-inferred] **Motion.** [`HolonLaw`] needs a step, which the interaction does
//! not declare, and returns a borrowed [`Holon`], which the interaction does not store. The law is
//! therefore [`HolonicInteractionLaw`], built by [`HolonicInteraction::law`] at a declared step and
//! scheme and advancing through the core [`ReferenceHolon`] (`Holon/Law.lean::advance_law`). A
//! perturbation commits its storage change as deposition work
//! (`Holon/Deposition.lean::commit_balance`, `Holon/Deposition.lean::deposition_work`) through
//! [`HolonicInteraction::perturbed_commit`].

use num_traits::{One, Zero};
use holonics::geometry::Rat;

use holonics::dirac::DiracStructure;
use holonics::element::{ResistiveRelation, deposition_work};
use holonics::holon::{Holon, HolonError, HolonState, PortCounts, PortHolon, PowerBalance};
use holonics::law::{Advance, EnergyBalance, HolonLaw, ReferenceHolon, Scheme};
use holonics::port::{Bond, Port, PortKind, PortUnits};

use super::{
    Carrier, ClockedEnergy, ContactDissipation, ContactFace, ExactRatMatrix, HolonicInteraction,
    InteractionRefusal, StorageRateReading, SymmetricForm, form_matrix, pairing,
};

/// `rows × columns` from a rule.
fn built(
    rows: usize,
    columns: usize,
    entry: impl Fn(usize, usize) -> Rat,
) -> Result<ExactRatMatrix, InteractionRefusal> {
    Ok(ExactRatMatrix::shaped(
        rows,
        columns,
        (0..rows)
            .map(|row| (0..columns).map(|column| entry(row, column)).collect())
            .collect(),
    )?)
}

fn entry(matrix: &ExactRatMatrix, row: usize, column: usize) -> Rat {
    matrix
        .get(row, column)
        .expect("an index inside a checked shape")
        .clone()
}

/// The stacked slip `J` of a face population over a chart of `extent` coordinates.
fn stacked_slip(
    faces: &[ContactFace],
    extent: usize,
) -> Result<ExactRatMatrix, InteractionRefusal> {
    let mut rows = Vec::new();
    for face in faces {
        if face.dimension() != extent {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a face's slip map against the chart it is stacked over",
                declared: extent,
                found: face.dimension(),
            });
        }
        rows.extend(face.slip().to_rows());
    }
    Ok(ExactRatMatrix::shaped(rows.len(), extent, rows)?)
}

/// `R = ⊕_f w_f D_f`, block diagonal in face order.
fn face_resistance(faces: &[ContactFace]) -> Result<ExactRatMatrix, InteractionRefusal> {
    let extent: usize = faces.iter().map(ContactFace::slip_extent).sum();
    let mut rows = vec![vec![Rat::zero(); extent]; extent];
    let mut offset = 0;
    for face in faces {
        for row in 0..face.slip_extent() {
            for column in 0..face.slip_extent() {
                rows[offset + row][offset + column] =
                    face.weight() * face.response().at(row, column);
            }
        }
        offset += face.slip_extent();
    }
    Ok(ExactRatMatrix::shaped(extent, extent, rows)?)
}

/// **The skew structure of a storage block with port blocks.** `omega` is `n × n` skew; each port
/// block is given by its column map `K` (`n × k`): `J[S, K] = −K`, `J[K, S] = Kᵀ`. The resistive
/// block is `K = Jᵀ` (so `f_R = J e_S`), a source block `K = B`, a link block `K = X`.
fn port_structure(
    omega: &ExactRatMatrix,
    blocks: &[&ExactRatMatrix],
) -> Result<ExactRatMatrix, InteractionRefusal> {
    let n = omega.rows();
    for block in blocks {
        if block.rows() != n {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a port block against the storage chart",
                declared: n,
                found: block.rows(),
            });
        }
    }
    let total = n + blocks.iter().map(|block| block.columns()).sum::<usize>();
    let mut rows = vec![vec![Rat::zero(); total]; total];
    for row in 0..n {
        for column in 0..n {
            rows[row][column] = -entry(omega, row, column);
        }
    }
    let mut offset = n;
    for block in blocks {
        for row in 0..n {
            for column in 0..block.columns() {
                let value = entry(block, row, column);
                rows[row][offset + column] = -value.clone();
                rows[offset + column][row] = value;
            }
        }
        offset += block.columns();
    }
    Ok(ExactRatMatrix::shaped(total, total, rows)?)
}

fn dimensionless_ports(names: Vec<(String, PortKind)>) -> Vec<Port> {
    names
        .into_iter()
        .map(|(name, kind)| Port {
            name,
            kind,
            units: PortUnits::new(
                holonics::port::Dimension::dimensionless(),
                holonics::port::Dimension::dimensionless(),
            ),
        })
        .collect()
}

fn select_rows(
    matrix: &ExactRatMatrix,
    rows: std::ops::Range<usize>,
) -> Result<ExactRatMatrix, InteractionRefusal> {
    built(rows.len(), matrix.columns(), |row, column| {
        entry(matrix, rows.start + row, column)
    })
}

fn submatrix(
    matrix: &ExactRatMatrix,
    rows: std::ops::Range<usize>,
    columns: std::ops::Range<usize>,
) -> Result<ExactRatMatrix, InteractionRefusal> {
    built(rows.len(), columns.len(), |row, column| {
        entry(matrix, rows.start + row, columns.start + column)
    })
}

impl HolonicInteraction {
    /// **The standing interaction as a core Holon** on ports `σ ⊕ ρ ⊕ π`: the joint chart, every
    /// joint face's slip coordinates in [`HolonicInteraction::joint_faces`] order, and the source's
    /// ports. The declared perturbation is not applied, as every other standing reading of this
    /// owner; [`HolonicInteraction::modulated`] gives the modulated unit and its own Holon. The
    /// ports are named (units dimensionless: the interaction declares none; see
    /// [`crate::junction_law::JointUnits::port_units`] for a declared joint).
    pub fn holon(&self) -> Result<Holon, InteractionRefusal> {
        let extent = self.joint_dimension();
        let faces = self.joint_faces()?;
        let slip = stacked_slip(&faces, extent)?;
        let excitation = self.excitation()?;
        let structure =
            port_structure(&self.joint_structure()?, &[&slip.transpose()?, &excitation])?;
        let counts = PortCounts {
            storage: extent,
            resistive: slip.rows(),
            external: excitation.columns(),
            active: 0,
        };
        let port_holon = PortHolon::new(
            DiracStructure::skew_graph(&structure)?,
            counts,
            self.joint_storage()?,
            ResistiveRelation::new(face_resistance(&faces)?)?,
        )?;
        let mut names = self.storage_port_names();
        names.extend(slip_port_names(&faces));
        names.extend(
            self.source
                .ports()
                .iter()
                .map(|port| (port.clone(), PortKind::External)),
        );
        Ok(Holon::new(port_holon)?.with_ports(dimensionless_ports(names))?)
    }

    fn storage_port_names(&self) -> Vec<(String, PortKind)> {
        let mut names = Vec::new();
        for medium in &self.media {
            for coordinate in 0..medium.dimension() {
                names.push((
                    format!("{}|q[{coordinate}]", medium.lineage()),
                    PortKind::Storage,
                ));
            }
        }
        if let Some(body) = self.perspective.body() {
            for coordinate in 0..body.dimension() {
                names.push((
                    format!("{}|q[{coordinate}]", body.lineage()),
                    PortKind::Storage,
                ));
            }
        }
        names
    }

    /// **The point balance through the core** (`Holon/Element.lean::PortHolon.power_balance`) at
    /// the configuration `q` and source input `u`: the motion `q̇ = A q + B u`, the slip flows
    /// `J G q`, the source bond `(Bᵀ G q, u)`. Refused if the core does not admit the point.
    pub fn power_balance_at(
        &self,
        configuration: &[Rat],
        input: &[Rat],
    ) -> Result<PowerBalance, InteractionRefusal> {
        let holon = self.holon()?;
        let port_holon = holon.port_holon();
        let extent = self.joint_dimension();
        if configuration.len() != extent {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a configuration against the joint chart",
                declared: extent,
                found: configuration.len(),
            });
        }
        let excitation = self.excitation()?;
        if input.len() != excitation.columns() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "an input against the source's ports",
                declared: excitation.columns(),
                found: input.len(),
            });
        }
        let effort = form_matrix(&self.joint_storage()?)?.apply(configuration)?;
        let drift = self.generator()?.apply(configuration)?;
        let forcing = excitation.apply(input)?;
        let velocity: Vec<Rat> = drift.iter().zip(&forcing).map(|(a, b)| a + b).collect();
        let slip = stacked_slip(&self.joint_faces()?, extent)?;
        let external = Bond::new(excitation.transpose()?.apply(&effort)?, input.to_vec())?;
        Ok(port_holon.power_balance(
            configuration,
            &velocity,
            &slip.apply(&effort)?,
            &external,
            &Bond::zero(0),
        )?)
    }

    /// **The perspective as a passive coholon's reader** (`Holon/Law.lean::passive_reading`,
    /// `Holon/Conformance.lean::ssm_port_output`): the coholon reads the storage effort `G q`, so
    /// the aperture's reading `C_R q` is `C' (G q)` with `C' = C_R G⁻¹`. Refused when `G` is
    /// singular: the reading then sees configuration the effort does not carry.
    pub fn perspective_reader(&self) -> Result<ExactRatMatrix, InteractionRefusal> {
        let inverse = form_matrix(&self.joint_storage()?)?.inverse()?;
        Ok(self.readout()?.multiply(&inverse)?)
    }

    /// **The Holon of the media alone**, with link ports to a participating receiver body: ports
    /// `σ_m ⊕ ρ ⊕ (π_source? ⊕ π_link)`. Refused when the perspective does not participate, or when
    /// a contact face reaches the receiver's coordinates.
    pub fn media_holon(&self) -> Result<Holon, InteractionRefusal> {
        let split = self.receiver_split()?;
        let omega = self.joint_structure()?;
        let media_omega = submatrix(&omega, 0..split.media, 0..split.media)?;
        let link = submatrix(&omega, 0..split.media, split.media..split.extent)?;
        let faces = self.media_faces(&split)?;
        let slip = stacked_slip(&faces, split.media)?;
        let excitation = self.excitation()?;
        let storage = self.joint_storage()?;
        let media_storage = SymmetricForm::from_rows(
            (0..split.media)
                .map(|row| {
                    (0..split.media)
                        .map(|column| storage.at(row, column).clone())
                        .collect()
                })
                .collect(),
        )?;
        let source_on_media = !matches!(self.source.carrier(), Carrier::Perspective);
        let media_source = if source_on_media {
            select_rows(&excitation, 0..split.media)?
        } else {
            ExactRatMatrix::zero(split.media, 0)?
        };
        let slip_map = slip.transpose()?;
        let structure = port_structure(&media_omega, &[&slip_map, &media_source, &link])?;
        let counts = PortCounts {
            storage: split.media,
            resistive: slip.rows(),
            external: media_source.columns() + link.columns(),
            active: 0,
        };
        let port_holon = PortHolon::new(
            DiracStructure::skew_graph(&structure)?,
            counts,
            media_storage,
            ResistiveRelation::new(face_resistance(&faces)?)?,
        )?;
        Ok(Holon::new(port_holon)?)
    }

    /// **The participating receiver as its own Holon** with the gyrating link ports: ports
    /// `σ_r ⊕ (π_link ⊕ π_source?)`, `q̇_r = Ω_rr e_r + f_L + B_r u`, `e_L = e_r`, `f_P = B_rᵀ e_r`.
    /// `None` when the perspective does not participate.
    pub fn receiver_holon(&self) -> Result<Option<Holon>, InteractionRefusal> {
        let Some(body) = self.perspective.body() else {
            return Ok(None);
        };
        let r = body.dimension();
        let source_on_receiver = matches!(self.source.carrier(), Carrier::Perspective);
        let source = if source_on_receiver {
            self.source.incidence().clone()
        } else {
            ExactRatMatrix::zero(r, 0)?
        };
        let p = source.columns();
        let ports = 2 * r + p;
        let omega = body.structure();
        let one = Rat::one();
        // Constraint rows `F f + E e = 0`, one block per law.
        let flow = built(ports, ports, |row, column| {
            if row < r {
                // f_S + f_L (+ Ω e_S + B e_P in E).
                if column == row || column == r + row {
                    one.clone()
                } else {
                    Rat::zero()
                }
            } else if row >= 2 * r {
                // f_P − Bᵀ e_S (the effort part in E).
                if column == row {
                    one.clone()
                } else {
                    Rat::zero()
                }
            } else {
                Rat::zero()
            }
        })?;
        let effort = built(ports, ports, |row, column| {
            if row < r {
                if column < r {
                    entry(omega, row, column)
                } else if column >= 2 * r {
                    entry(&source, row, column - 2 * r)
                } else {
                    Rat::zero()
                }
            } else if row < 2 * r {
                // e_L − e_S = 0.
                if column == row {
                    one.clone()
                } else if column == row - r {
                    -one.clone()
                } else {
                    Rat::zero()
                }
            } else if column < r {
                -entry(&source, column, row - 2 * r)
            } else {
                Rat::zero()
            }
        })?;
        let port_holon = PortHolon::new(
            DiracStructure::kernel_form(&flow, &effort)?,
            PortCounts {
                storage: r,
                resistive: 0,
                external: r + p,
                active: 0,
            },
            body.storage().clone(),
            ResistiveRelation::new(ExactRatMatrix::zero(0, 0)?)?,
        )?;
        Ok(Some(Holon::new(port_holon)?))
    }

    /// **The media Holon and the receiver Holon joined at their link ports**
    /// (`Holon/Law.lean::PortHolon.interconnect`). Its storage, resistance and external ports are
    /// those of [`HolonicInteraction::holon`] in the same order, and its Dirac structure is the same
    /// subspace; the tests assert both.
    pub fn joined_holon(&self) -> Result<Holon, InteractionRefusal> {
        let split = self.receiver_split()?;
        let media = self.media_holon()?;
        let receiver = self
            .receiver_holon()?
            .expect("receiver_split refused a non-participating perspective");
        let link_offset = media.port_holon().counts().external - split.receiver;
        let joined: Vec<(usize, usize)> = (0..split.receiver)
            .map(|link| (link_offset + link, link))
            .collect();
        Ok(media.interconnect(&receiver, &joined)?)
    }

    fn receiver_split(&self) -> Result<ReceiverSplit, InteractionRefusal> {
        let Some(body) = self.perspective.body() else {
            return Err(InteractionRefusal::Holon(HolonError::Unsupported {
                what: "joining a receiver Holon",
                reason: "the perspective does not participate, so it carries no body to join",
            }));
        };
        let extent = self.joint_dimension();
        Ok(ReceiverSplit {
            extent,
            media: extent - body.dimension(),
            receiver: body.dimension(),
        })
    }

    /// The joint faces restricted to the media coordinates; a face reaching the receiver refuses.
    fn media_faces(&self, split: &ReceiverSplit) -> Result<Vec<ContactFace>, InteractionRefusal> {
        let mut faces = Vec::new();
        for face in self.joint_faces()? {
            let slip = face.slip();
            let reaches = (0..slip.rows()).any(|row| {
                (split.media..split.extent).any(|column| !entry(slip, row, column).is_zero())
            });
            if reaches {
                return Err(InteractionRefusal::Holon(HolonError::Unsupported {
                    what: "joining a receiver Holon",
                    reason: "a contact face reaches the receiver's coordinates and would couple the \
                             two Holons resistively across the link",
                }));
            }
            faces.push(ContactFace::declared(
                face.lineage().to_owned(),
                submatrix(slip, 0..slip.rows(), 0..split.media)?,
                face.response().clone(),
                face.weight().clone(),
            )?);
        }
        Ok(faces)
    }

    /// **The deposition work of the declared perturbation at a configuration**,
    /// `½⟨q, (G' − G) q⟩` (`Holon/Deposition.lean::deposition_work`). A perturbation of the skew
    /// structure or of a face leaves the storage and does no work; none declared is zero.
    pub fn perturbation_deposition_work(
        &self,
        configuration: &[Rat],
    ) -> Result<Rat, InteractionRefusal> {
        let before = self.joint_storage()?;
        let after = self.modulated()?.joint_storage()?;
        Ok(deposition_work(&before, &after, configuration)?)
    }

    /// **The exact law at a declared step and scheme**, advancing through the core
    /// [`ReferenceHolon`].
    pub fn law(
        &self,
        step: Rat,
        scheme: Scheme,
    ) -> Result<HolonicInteractionLaw, InteractionRefusal> {
        Ok(HolonicInteractionLaw {
            lineage: format!("{}|holon-law", self.lineage),
            reference: ReferenceHolon::new(self.holon()?, step, scheme)?,
        })
    }

    /// **One word at the standing law, then the perturbation deposited**
    /// (`Holon/Deposition.lean::commit_balance`): the balance carries
    /// [`HolonicInteraction::perturbation_deposition_work`] at the reached configuration and closes
    /// exactly. Returns the advance and the modulated law, which the next word runs.
    pub fn perturbed_commit(
        &self,
        step: Rat,
        scheme: Scheme,
        state: &HolonState,
        input: &[Rat],
    ) -> Result<(Advance, HolonicInteractionLaw), InteractionRefusal> {
        let standing = self.law(step.clone(), scheme)?;
        let modulated = self.modulated()?;
        let advance = standing.reference.commit(
            state,
            input,
            &self.joint_storage()?,
            &ExactRatMatrix::zero(0, 0)?,
            &modulated.joint_storage()?,
        )?;
        Ok((advance, modulated.law(step, scheme)?))
    }
}

struct ReceiverSplit {
    extent: usize,
    media: usize,
    receiver: usize,
}

fn slip_port_names(faces: &[ContactFace]) -> Vec<(String, PortKind)> {
    faces
        .iter()
        .flat_map(|face| {
            (0..face.slip_extent()).map(move |slip| {
                (
                    format!("{}|slip[{slip}]", face.lineage()),
                    PortKind::Resistive,
                )
            })
        })
        .collect()
}

/// **The Holonic Interaction's exact law** at a declared step and scheme. Serialize-free: it is a
/// motion over a checked declaration, never a wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolonicInteractionLaw {
    lineage: String,
    reference: ReferenceHolon,
}

impl HolonicInteractionLaw {
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The core reference law it advances through.
    pub fn reference(&self) -> &ReferenceHolon {
        &self.reference
    }
}

impl HolonLaw for HolonicInteractionLaw {
    fn holon(&self) -> &Holon {
        self.reference.holon()
    }

    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError> {
        self.reference.advance(state, input)
    }

    /// Two interactions joined at shared source ports: the core interconnection of their Holons.
    fn interact(&self, other: &Self, joined: &[(usize, usize)]) -> Result<Self, HolonError> {
        Ok(Self {
            lineage: format!("{}⋈{}", self.lineage, other.lineage),
            reference: self.reference.interact(&other.reference, joined)?,
        })
    }
}

// ===============================================================================================
// the power readings as views of the core energy balance
// ===============================================================================================

impl ContactDissipation {
    /// **`M_contact` as the core resistive relation** on the motion coordinates
    /// (`Holon/Element.lean::PortHolon.passive` recertifies its positive semidefiniteness).
    pub fn resistive_relation(&self) -> Result<ResistiveRelation, InteractionRefusal> {
        Ok(ResistiveRelation::new(self.matrix()?)?)
    }
}

impl ClockedEnergy {
    /// **The clocked contact word as a core balance.** [definition; agent-inferred] The contact
    /// alone over its declared clock: no port, active or deposited term, the dissipated energy
    /// `⟨δq, M δq⟩/h = h⟨v, M v⟩` at `v = δq/h`, withdrawn from storage. The residual is zero by
    /// construction; the substantive equality — this number is the core resistive dissipation over
    /// the clock — is asserted in the tests through [`ContactDissipation::resistive_relation`].
    pub fn energy_balance(&self) -> EnergyBalance {
        let zero = Rat::zero();
        EnergyBalance::closed(
            -self.energy.clone(),
            self.energy.clone(),
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        )
    }
}

impl StorageRateReading {
    /// **The storage-rate reading at a configuration as a core rate balance** (per unit time, no
    /// source input): `stored_change = ½⟨q, Σ q⟩` from the causal-chord rate form and
    /// `dissipated = −½⟨q, (−2GMG) q⟩ = ⟨Gq, M Gq⟩`. The residual is zero exactly when the rate form
    /// agrees with `−2GMG` along `q`, which [`StorageRateReading::agrees`] certifies everywhere.
    pub fn energy_balance_at(
        &self,
        configuration: &[Rat],
    ) -> Result<EnergyBalance, InteractionRefusal> {
        let two = Rat::from_integer(2.into());
        let predicted = form_matrix(&self.predicted)?;
        if configuration.len() != predicted.rows() {
            return Err(InteractionRefusal::WidthDisagrees {
                what: "a configuration against the predicted rate form",
                declared: predicted.rows(),
                found: configuration.len(),
            });
        }
        let zero = Rat::zero();
        Ok(EnergyBalance::closed(
            self.rate_at(configuration)? / &two,
            -pairing(&predicted, configuration, configuration)? / &two,
            zero.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        ))
    }
}
