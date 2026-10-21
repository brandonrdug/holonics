//! A declared, lossless observation boundary on actual paired source ports.
//!
//! This is not key location and not a claim that an observation is true. The producing operands
//! are the constitution's ports E, their admitted dyads B, and the exact left decoders D.
//! DE=I is required on every `Lock` source port: a singular observation port is refused, never
//! silently quotiented. A founded `Own` ring's port is attached as a phase witness only: it reads
//! the ring's phase, decodes nothing, and is not certified (the decoder reads a `Lock` port).
//! The rotor's reduced action U=DPE carries its FULL residual R=PE-EU, so PE=EU+R.
//!
//! [definition; agent-inferred, October 17] **Admission certifies what DE=I needs, and the decoder
//! follows its read.** A left decoder of E exists exactly when ker E = 0, and then the Gram
//! decoder D=(EᵀE)⁻¹Eᵀ satisfies DE=I identically. So admission certifies the dyad, the rotor and
//! ker E = 0, the last by a maximal minor of E that is nonzero in one prime chart
//! (`ExactRatMatrix::is_injective`), with the exact rank where that chart loses rank. D is a
//! function of E alone; it is formed exactly on its first read (`ObservationPort::decoder`), with
//! the Gram inverted in its paired sectors and DE=I checked there. U and R are functions of D, P
//! and E, formed on their first read (`ObservationPort::square`). A deposit moves E at every taught
//! cell, and no per-cell consumer reads D, U or R, so re-admission pays only the certificate.
//! No zero residual, learned spatial invariance, or inferred latent structure is asserted.
//! The Lean obligation joining these checked identities to observation admission is open (#62): a
//! nonzero image of a maximal minor under a ring hom to a field proves ker E = 0, and ker E = 0
//! gives (EᵀE)⁻¹EᵀE = I.

use super::{Encoded, EncodedChart, EncodingError, PortCell, chart_refusal, holding_sources};
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::paired::{PairedCarrier, PairingDeclaration};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};
use std::sync::{Arc, OnceLock};

/// The rotor's reduced action `U = DPE` and its full residual `R = PE - EU`, so `PE = EU + R`.
#[derive(Clone, Debug, PartialEq)]
pub struct RotorSquare {
    pub reduced: ExactRatMatrix,
    pub residual: ExactRatMatrix,
}

/// Producing operands for one source ring. Residual is retained, not treated as zero.
/// The operands are immutable after admission, so the decoder and the square formed from them on
/// first read are shared by every clone of the admitted port (every passage the boundary encodes
/// carries one).
#[derive(Clone, Debug)]
pub struct ObservationPort {
    carrier: PairedCarrier,
    injection: ExactRatMatrix,
    decoder: Arc<OnceLock<ExactRatMatrix>>,
    rotor: ExactRatMatrix,
    square: Arc<OnceLock<RotorSquare>>,
}

/// Equality is over the admitted operands: the decoder and the square are their functions, so
/// whether either has been read yet never separates two ports.
impl PartialEq for ObservationPort {
    fn eq(&self, other: &Self) -> bool {
        self.carrier == other.carrier
            && self.injection == other.injection
            && self.rotor == other.rotor
    }
}

impl ObservationPort {
    pub fn carrier(&self) -> &PairedCarrier {
        &self.carrier
    }
    pub fn injection(&self) -> &ExactRatMatrix {
        &self.injection
    }
    /// **`D = (EᵀE)⁻¹Eᵀ`**, the exact left decoder, formed from `E` on its first read and checked
    /// there: the Gram inverted in its exact paired sectors and certified on both sides, then
    /// `DE = I` on the complete domain. Admission certified `ker E = 0`, so the Gram is invertible;
    /// a failed formation is returned and never cached.
    pub fn decoder(&self) -> Result<&ExactRatMatrix, EncodingError> {
        if let Some(decoder) = self.decoder.get() {
            return Ok(decoder);
        }
        let transpose = self.injection.transpose()?;
        let gram = transpose.multiply(&self.injection)?;
        let decoder =
            paired_gram_inverse(&gram, self.carrier.sigma().pairs())?.multiply(&transpose)?;
        if decoder.multiply(&self.injection)? != ExactRatMatrix::identity(self.injection.columns())?
        {
            return Err(chart_refusal(
                "the observation decoder does not recover every class",
            ));
        }
        // A concurrent first read forms the same exact decoder; the one that lands first stands.
        Ok(self.decoder.get_or_init(|| decoder))
    }
    pub fn rotor(&self) -> &ExactRatMatrix {
        &self.rotor
    }
    /// The complete rotor square, formed exactly from `D`, `P` and `E` on its first read and
    /// checked on its complete domain there, without dropping the remainder.
    pub fn square(&self) -> Result<&RotorSquare, EncodingError> {
        if let Some(square) = self.square.get() {
            return Ok(square);
        }
        let advanced = self.rotor.multiply(&self.injection)?;
        let reduced = self.decoder()?.multiply(&advanced)?;
        let carried = self.injection.multiply(&reduced)?;
        let residual = advanced.subtract(&carried)?;
        if carried.add(&residual)? != advanced {
            return Err(chart_refusal(
                "the observation rotor square lost its residual",
            ));
        }
        // A concurrent first read forms the same exact square; the one that lands first stands.
        Ok(self
            .square
            .get_or_init(|| RotorSquare { reduced, residual }))
    }
    pub fn reduced(&self) -> Result<&ExactRatMatrix, EncodingError> {
        Ok(&self.square()?.reduced)
    }
    pub fn residual(&self) -> Result<&ExactRatMatrix, EncodingError> {
        Ok(&self.square()?.residual)
    }
}

/// A source ring whose clock does not read its port (an `Own` ring, guard 9): its producing port
/// `E_f` is kept as a witness only, so a changed founded port refuses a stale observation.
#[derive(Clone, Debug, PartialEq)]
pub struct PhaseWitness {
    pub ring: usize,
    pub injection: ExactRatMatrix,
}

/// A checked boundary at a particular material, before any observations enter.
/// Cloneable immutable operands remain attached to every resulting Encoded passage.
/// The boundary's complete producing operands, including sources whose clocks do not read ports.
#[derive(Clone, Debug, PartialEq)]
pub struct PairedObservation {
    classes: usize,
    sources: Vec<(usize, u64)>,
    ports: Vec<ObservationPort>,
    witnesses: Vec<PhaseWitness>,
}

/// Invert the Gram in the exact even/odd sectors of its complete class pairing.
/// A nonpairable matrix uses the original general inverse. The reconstructed inverse
/// is certified on the complete original domain in both directions, as the general
/// inverse is; no approximate inverse or alternative left decoder is substituted.
fn paired_gram_inverse(
    gram: &ExactRatMatrix,
    pairs: &[(usize, usize)],
) -> Result<ExactRatMatrix, crate::ratio::linear::ExactLinearError> {
    let n = gram.rows();
    if gram.columns() != n || pairs.len().checked_mul(2) != Some(n) || n == 0 {
        return gram.inverse();
    }
    let mut covered = vec![false; n];
    for &(a, b) in pairs {
        if a >= n || b >= n || a == b || covered[a] || covered[b] {
            return gram.inverse();
        }
        covered[a] = true;
        covered[b] = true;
    }
    let mut plus = Vec::with_capacity(pairs.len());
    let mut minus = Vec::with_capacity(pairs.len());
    for &(a, b) in pairs {
        let mut positive = Vec::with_capacity(pairs.len());
        let mut negative = Vec::with_capacity(pairs.len());
        for &(c, d) in pairs {
            let ac = gram.get(a, c)?;
            let ad = gram.get(a, d)?;
            if ac != gram.get(b, d)? || ad != gram.get(b, c)? {
                return gram.inverse();
            }
            positive.push(ac + ad);
            negative.push(ac - ad);
        }
        plus.push(positive);
        minus.push(negative);
    }
    let plus = ExactRatMatrix::new(plus)?.inverse()?;
    let minus = ExactRatMatrix::new(minus)?.inverse()?;
    let mut rows = vec![vec![integer(0); n]; n];
    let two = integer(2);
    for (i, &(a, b)) in pairs.iter().enumerate() {
        for (j, &(c, d)) in pairs.iter().enumerate() {
            let same = (plus.get(i, j)? + minus.get(i, j)?) / &two;
            let cross = (plus.get(i, j)? - minus.get(i, j)?) / &two;
            rows[a][c] = same.clone();
            rows[b][d] = same;
            rows[a][d] = cross.clone();
            rows[b][c] = cross;
        }
    }
    let inverse = ExactRatMatrix::new(rows)?;
    let identity = ExactRatMatrix::identity(n)?;
    if gram.multiply(&inverse)? != identity || inverse.multiply(gram)? != identity {
        return Err(crate::ratio::linear::ExactLinearError::InverseCertificateFailure);
    }
    Ok(inverse)
}

impl PairedObservation {
    /// Versioned identity over admitted immutable operands, never lazy decoder/square state.
    pub(crate) fn immutable_identity_text(&self)->String {
        let ports:Vec<_>=self.ports.iter().map(|p|(&p.carrier,&p.injection,&p.rotor)).collect();
        format!("paired-observation-identity-v1|{:?}|{:?}|{:?}|{:?}",self.classes,self.sources,ports,self.witnesses)
    }
    pub fn admit(
        field: &Field,
        material: &impl ConstitutionRead,
        pairing: &PairingDeclaration,
    ) -> Result<Self, EncodingError> {
        let classes = field.alphabet();
        let sources = holding_sources(field, classes)?;
        if sources.is_empty() {
            return Err(chart_refusal("observations require a source ring"));
        }
        let mut ports = Vec::new();
        let mut witnesses = Vec::new();
        for &(ring, _) in &sources {
            let injection = material
                .source_port(ring)
                .ok_or_else(|| chart_refusal("the observation has no producing source port"))?
                .clone();
            if field.ring(ring).advance() == crate::hnn::RingAdvance::Own {
                witnesses.push(PhaseWitness { ring, injection });
                continue;
            }
            let carrier = PairedCarrier::admit(field, ring, pairing, &injection).map_err(|_| {
                chart_refusal("the producing observation port does not carry the declared dyad")
            })?;
            if carrier.sigma().table().iter().any(Option::is_none) {
                return Err(chart_refusal(
                    "the observation pairing covers every boundary class",
                ));
            }
            // `ker E = 0` is what `DE = I` needs; `D` itself is formed on its first read. A port
            // that is not injective has a singular Gram, and is refused as that Gram's inverse is.
            if injection.columns() != classes {
                return Err(chart_refusal(
                    "the observation decoder does not recover every class",
                ));
            }
            if !injection.is_injective()? {
                return Err(crate::ratio::linear::ExactLinearError::SingularMatrix.into());
            }
            let width = carrier.width();
            // Read the actual ring owner's rotor, rather than duplicating its permutation law.
            let columns: Vec<_> = (0..width)
                .map(|column| {
                    let unit: Vec<_> = (0..width)
                        .map(|row| integer(i64::from(row == column)))
                        .collect();
                    field.ring(ring).rotate(&unit, &num_bigint::BigInt::from(1))
                })
                .collect();
            let rotor = ExactRatMatrix::shaped(
                width,
                width,
                (0..width)
                    .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                    .collect(),
            )?;
            ports.push(ObservationPort {
                carrier,
                injection,
                decoder: Arc::new(OnceLock::new()),
                rotor,
                square: Arc::new(OnceLock::new()),
            });
        }
        if ports.is_empty() {
            return Err(chart_refusal("observations require a Lock source ring"));
        }
        Ok(Self {
            classes,
            sources,
            ports,
            witnesses,
        })
    }

    #[cfg(test)]
    fn admit_reference(
        field: &Field,
        material: &impl ConstitutionRead,
        pairing: &PairingDeclaration,
    ) -> Result<Self, EncodingError> {
        let classes = field.alphabet();
        let sources = holding_sources(field, classes)?;
        if sources.is_empty() {
            return Err(chart_refusal("observations require a source ring"));
        }
        let mut ports = Vec::new();
        let mut witnesses = Vec::new();
        for &(ring, _) in &sources {
            let injection = material
                .source_port(ring)
                .ok_or_else(|| chart_refusal("the observation has no producing source port"))?
                .clone();
            if field.ring(ring).advance() == crate::hnn::RingAdvance::Own {
                witnesses.push(PhaseWitness { ring, injection });
                continue;
            }
            let carrier = PairedCarrier::admit(field, ring, pairing, &injection).map_err(|_| {
                chart_refusal("the producing observation port does not carry the declared dyad")
            })?;
            if carrier.sigma().table().iter().any(Option::is_none) {
                return Err(chart_refusal(
                    "the observation pairing covers every boundary class",
                ));
            }
            let transpose = injection.transpose()?;
            let decoder = transpose
                .multiply(&injection)?
                .inverse()?
                .multiply(&transpose)?;
            if decoder.multiply(&injection)? != ExactRatMatrix::identity(classes)? {
                return Err(chart_refusal(
                    "the observation decoder does not recover every class",
                ));
            }
            let width = carrier.width();
            // Read the actual ring owner's rotor, rather than duplicating its permutation law.
            let columns: Vec<_> = (0..width)
                .map(|column| {
                    let unit: Vec<_> = (0..width)
                        .map(|row| integer(i64::from(row == column)))
                        .collect();
                    field.ring(ring).rotate(&unit, &num_bigint::BigInt::from(1))
                })
                .collect();
            let rotor = ExactRatMatrix::shaped(
                width,
                width,
                (0..width)
                    .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                    .collect(),
            )?;
            let advanced = rotor.multiply(&injection)?;
            let reduced = decoder.multiply(&advanced)?;
            let residual = advanced.subtract(&injection.multiply(&reduced)?)?;
            // Both squares checked on their complete domain, without dropping the remainder.
            if injection.multiply(&reduced)?.add(&residual)? != advanced {
                return Err(chart_refusal(
                    "the observation rotor square lost its residual",
                ));
            }
            ports.push(ObservationPort {
                carrier,
                injection,
                decoder: Arc::new(OnceLock::from(decoder)),
                rotor,
                square: Arc::new(OnceLock::from(RotorSquare { reduced, residual })),
            });
        }
        if ports.is_empty() {
            return Err(chart_refusal("observations require a Lock source ring"));
        }
        Ok(Self {
            classes,
            sources,
            ports,
            witnesses,
        })
    }

    pub fn ports(&self) -> &[ObservationPort] {
        &self.ports
    }
    pub fn witnesses(&self) -> &[PhaseWitness] {
        &self.witnesses
    }
    pub fn classes(&self) -> usize {
        self.classes
    }
    /// Boundary class to authored symbol. Class identity is an explicit codec law here.
    pub fn symbol(&self, class: usize) -> Option<usize> {
        (class < self.classes).then_some(class)
    }
    /// A boundary admitted before deposition cannot be reused after its producing port changes.
    pub fn check_material(&self, material: &impl ConstitutionRead) -> Result<(), EncodingError> {
        for port in &self.ports {
            if material.source_port(port.carrier.ring()) != Some(&port.injection) {
                return Err(chart_refusal(
                    "the observation's producing source port changed; re-admit it",
                ));
            }
        }
        for witness in &self.witnesses {
            if material.source_port(witness.ring) != Some(&witness.injection) {
                return Err(chart_refusal(
                    "the observation's producing source port changed; re-admit it",
                ));
            }
        }
        Ok(())
    }

    /// Authored boundary symbols, not KnownTruth. No statistical conclusion is made here.
    /// The caller owns the exterior codec (including label arrival time and spatial coordinates).
    pub fn encode(&self, symbols: &[usize]) -> Result<Encoded, EncodingError> {
        if symbols.iter().any(|&class| class >= self.classes) {
            return Err(chart_refusal(
                "an observation is outside its declared boundary chart",
            ));
        }
        Ok(Encoded {
            placement: None,
            cells: symbols.iter().map(|&class| PortCell { class }).collect(),
            chart: Arc::new(EncodedChart {
                classes: self.classes,
                sources: self.sources.clone(),
                // The public scalar boundary decoder reads source 0 on its first read
                // (`Encoded::decoder`); all source witnesses remain attached, and each `Lock`
                // witness independently satisfies DE=I (an `Own` phase witness decodes nothing).
                decoder: None,
                fibre: Vec::new(),
                labels: (0..self.classes).map(Some).collect(),
                advances: None,
                founded: None,
                observed: Some(Arc::new(self.clone())),
            }),
        })
    }

    /// Attach checked occurrence placement without enlarging the observation alphabet.
    pub fn encode_placed(
        &self,
        symbols: &[usize],
        placement: &super::placement::OccurrencePlacement,
    ) -> Result<Encoded, EncodingError> {
        if symbols.len() != placement.len()
            || self
                .sources
                .iter()
                .any(|&(g, d)| placement.periods().get(g) != Some(&d))
        {
            return Err(chart_refusal(
                "the observation and placement have different extents or source rings",
            ));
        }
        let mut encoded = self.encode(symbols)?;
        encoded.placement = Some(Arc::new(placement.clone()));
        Ok(encoded)
    }

    /// A raster's x/y placement at two actual source rings, not hidden unrelated clocks.
    /// The chart retains its pixel decoder; the encoded passage carries its exact native lifts.
    pub fn encode_raster(
        &self,
        field: &Field,
        current: &crate::hnn::field::Current,
        raster: &crate::geometry::spatial::PlacedRaster,
    ) -> Result<Encoded, EncodingError> {
        let periods = raster.periods();
        if field.rings().len() < 2
            || !field.is_source(0)
            || !field.is_source(1)
            || field.ring(0).period() != periods[0]
            || field.ring(1).period() != periods[1]
        {
            return Err(chart_refusal(
                "the raster's x/y axes must be matching native source rings",
            ));
        }
        let placement =
            super::placement::OccurrencePlacement::at(field, current, raster.phase_prefixes())?;
        let encoded = self.encode_placed(raster.symbols(), &placement)?;
        field.admit(&encoded)?;
        Ok(encoded)
    }

    /// Decode an actual injected amplitude through the first source's exact left decoder.
    pub fn decode(&self, amplitude: &[Rat]) -> Result<Vec<Rat>, EncodingError> {
        Ok(self.ports[0].decoder()?.apply(amplitude)?)
    }
}

impl Encoded {
    pub fn check_observed_material(
        &self,
        material: &impl ConstitutionRead,
    ) -> Result<(), EncodingError> {
        if let Some(observation) = self.observation() {
            observation.check_material(material)?;
        }
        Ok(())
    }
    pub fn observation(&self) -> Option<&PairedObservation> {
        self.chart.observed.as_deref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::Constitution;
    use crate::hnn::field::FieldDeclaration;
    fn fixture() -> (Field, Constitution, PairingDeclaration) {
        let mut declaration = FieldDeclaration::campaign_one(1 << 17);
        declaration.alphabet = 4;
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        // Two independent leader columns, completed by the ACTUAL source reflection.
        let free = ExactRatMatrix::shaped(
            10,
            4,
            (0..10)
                .map(|r| {
                    (0..4)
                        .map(|c| integer(i64::from((r == 2 && c == 0) || (r == 4 && c == 2))))
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let port = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
        let material = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, port, carrier.symmetry())
            .unwrap();
        (field, material, pairing)
    }
    #[test]
    fn observed_source_carries_decoder_dyad_and_complete_rotor_residual() {
        let (field, material, pairing) = fixture();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let port = &boundary.ports()[0];
        assert!(port.decoder.get().is_none(), "admission forms no decoder");
        let charted = boundary.encode(&[1]).unwrap();
        assert_eq!(
            port.decoder().unwrap().multiply(port.injection()).unwrap(),
            ExactRatMatrix::identity(4).unwrap()
        );
        assert!(
            std::ptr::eq(charted.decoder().unwrap(), port.decoder().unwrap()),
            "an encoded passage reads its boundary's one decoder"
        );
        let unread = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let encoded = boundary.encode(&[0]).unwrap();
        assert!(port.square.get().is_none(), "admission forms no square");
        assert_eq!(
            port.rotor().multiply(port.injection()).unwrap(),
            port.injection()
                .multiply(port.reduced().unwrap())
                .unwrap()
                .add(port.residual().unwrap())
                .unwrap()
        );
        assert!(unread.ports()[0].square.get().is_none());
        assert_eq!(
            boundary, unread,
            "reading the square never changes the port's identity"
        );
        assert!(
            encoded.observation().unwrap().ports()[0]
                .square
                .get()
                .is_some(),
            "an encoded passage shares the square its boundary formed"
        );
        assert!(
            port.residual()
                .unwrap()
                .entries()
                .iter()
                .any(|entry| entry != &integer(0)),
            "this fixture has a genuinely nonzero retained rotor residual"
        );
        for column in 0..port.carrier().width() {
            let unit: Vec<_> = (0..port.carrier().width())
                .map(|row| integer(i64::from(row == column)))
                .collect();
            assert_eq!(
                port.rotor().apply(&unit).unwrap(),
                field
                    .ring(port.carrier().ring())
                    .rotate(&unit, &num_bigint::BigInt::from(1))
            );
        }
        for c in 0..4 {
            let unit: Vec<_> = (0..4).map(|i| integer(i64::from(i == c))).collect();
            assert_eq!(
                boundary
                    .decode(&port.injection().apply(&unit).unwrap())
                    .unwrap(),
                unit
            );
        }
        let encoded = boundary.encode(&[3, 0, 2, 1]).unwrap();
        field.admit(&encoded).unwrap();
        assert!(encoded.observation().is_some());
        assert_eq!(encoded.classes_read().collect::<Vec<_>>(), vec![3, 0, 2, 1]);
        assert!(encoded.part(1..3).unwrap().observation().is_some());
        assert!(boundary.encode(&[4]).is_err());
    }
    #[test]
    fn changed_source_material_refuses_stale_observation_before_consumption() {
        use crate::hnn::field::Current;
        use crate::hnn::{ExecutionPort, Reference};
        let (field, material, pairing) = fixture();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let old = boundary.encode(&[0, 1]).unwrap();
        let changed = boundary.ports()[0].injection().scaled(&integer(2));
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &changed).unwrap();
        let successor = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, changed, carrier.symmetry())
            .unwrap();
        assert!(old.check_observed_material(&successor).is_err());
        let fresh = PairedObservation::admit(&field, &successor, &pairing)
            .unwrap()
            .encode(&[0, 1])
            .unwrap();
        fresh.check_observed_material(&successor).unwrap();
        let reference = Reference::new(4, 1 << 40);
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), successor)
            .unwrap();
        let before = reference.read(&resident).unwrap();
        assert!(reference.ingest(&mut resident, None, &old).is_err());
        assert_eq!(
            reference.read(&resident).unwrap(),
            before,
            "stale refusal is before state changes"
        );
        reference.ingest(&mut resident, None, &fresh).unwrap();
    }
    #[test]
    fn occurrence_placement_keeps_repeated_classes_slices_and_exact_winding() {
        use super::super::placement::OccurrencePlacement;
        use crate::hnn::field::Current;
        use num_bigint::BigInt;
        let (field, material, pairing) = fixture();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let turn = BigInt::from(1u64) << 80usize;
        let opening = Current::at(
            &field,
            field
                .rings()
                .iter()
                .map(|r| &turn * r.period() + r.period() - 1)
                .collect(),
        )
        .unwrap();
        let positions: Vec<_> = (0..140)
            .map(|at| vec![(at / 2) % 5, ((at / 2) / 5) % 7])
            .collect();
        let placement = OccurrencePlacement::at(&field, &opening, &positions).unwrap();
        let encoded = boundary.encode_placed(&vec![0; 140], &placement).unwrap();
        assert_eq!(
            encoded.advance(1),
            Some(&[0, 0, 0, 0][..]),
            "the second nibble stays at the first site"
        );
        assert_eq!(
            encoded.advance(2),
            Some(&[1, 0, 0, 0][..]),
            "the next identical nibble moves to the next site"
        );
        assert_ne!(
            encoded.advance(1),
            encoded.advance(2),
            "one class has distinct occurrence transports"
        );
        let mut whole = opening.clone();
        let mut carries = 0;
        for at in 0..encoded.len() {
            carries += usize::from(whole.step(&field, &encoded, at).unwrap().carry_out);
            assert_eq!(whole.phase(&field, 0).unwrap(), positions[at][0]);
            assert_eq!(whole.phase(&field, 1).unwrap(), positions[at][1]);
            assert_eq!(whole.lift(), placement.arrivals()[at]);
        }
        assert!(carries > 0);
        let mut sliced = opening.clone();
        for start in (0..encoded.len()).step_by(13) {
            let part = encoded
                .part(start..(start + 13).min(encoded.len()))
                .unwrap();
            assert_eq!(part.placement().unwrap().opening(), sliced.lift());
            for at in 0..part.len() {
                sliced.step(&field, &part, at).unwrap();
            }
        }
        assert_eq!(whole, sliced);
        let (first, rest) = encoded.clone().split_at(37).unwrap();
        assert_eq!(
            rest.placement().unwrap().opening(),
            first.placement().unwrap().arrivals().last().unwrap()
        );
        let mut wrong = Current::at_rest(&field);
        let before = wrong.clone();
        assert!(wrong.step(&field, &encoded, 0).is_err());
        assert_eq!(
            wrong, before,
            "a placement cannot be silently rebound to another winding"
        );
        assert!(encoded.part(141..141).is_err());
        let mut altered = FieldDeclaration::campaign_one(1 << 17);
        altered.alphabet = 4;
        altered.rings[1].period = 8;
        altered.rings[1].placements = (0..8)
            .map(|n| FieldDeclaration::quarter_turn(n, 8))
            .collect();
        altered.rings[1].reflector = (0..8).map(|n| ((8 - n) % 8) as usize).collect();
        altered.lattice.clear();
        let altered = Field::declare(altered.by_lattice_rule()).unwrap();
        assert_eq!(altered.ring(0).period(), field.ring(0).period());
        assert!(
            altered.admit(&encoded).is_err(),
            "placement binds nonsource carry-frame periods too"
        );
    }
    #[test]
    fn singular_paired_observation_is_refused_not_quotiented() {
        let (field, _, pairing) = fixture();
        let port = ExactRatMatrix::zero(10, 4).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
        let material = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, port, carrier.symmetry())
            .unwrap();
        assert!(PairedObservation::admit(&field, &material, &pairing).is_err());
    }
    #[test]
    fn paired_gram_inverse_matches_general_oracle_and_falls_back() {
        use crate::ratio::rat;
        for n in [2, 4, 6, 10, 16, 32] {
            // Reverse-oriented, non-adjacent pairs: never assume c xor 1.
            let pairs: Vec<_> = (0..n / 2).map(|i| (n - 1 - i, i)).collect();
            let mut rows = vec![vec![integer(0); n]; n];
            for (i, &(a, b)) in pairs.iter().enumerate() {
                for (j, &(c, d)) in pairs.iter().enumerate() {
                    let same = if i == j {
                        integer((n * 4) as i64)
                    } else {
                        rat((i + j + 1) as i64, 8)
                    };
                    let cross = rat((i + j + 2) as i64, 16);
                    rows[a][c] = same.clone();
                    rows[b][d] = same;
                    rows[a][d] = cross.clone();
                    rows[b][c] = cross;
                }
            }
            let gram = ExactRatMatrix::new(rows.clone()).unwrap();
            assert_eq!(
                paired_gram_inverse(&gram, &pairs).unwrap(),
                gram.inverse().unwrap()
            );
            // Break commutation without breaking invertibility: exact generic fallback.
            rows[0][0] += rat(1, 32);
            let unpaired = ExactRatMatrix::new(rows).unwrap();
            assert_eq!(
                paired_gram_inverse(&unpaired, &pairs).unwrap(),
                unpaired.inverse().unwrap()
            );
            assert_eq!(
                paired_gram_inverse(&gram, &[]).unwrap(),
                gram.inverse().unwrap()
            );
            assert_eq!(
                paired_gram_inverse(&gram, &vec![(0, 0); n / 2]).unwrap(),
                gram.inverse().unwrap()
            );
        }
        let zero = ExactRatMatrix::zero(4, 4).unwrap();
        assert_eq!(
            paired_gram_inverse(&zero, &[(0, 1), (2, 3)]),
            zero.inverse()
        );
    }

    #[test]
    fn lazy_square_failure_is_not_cached_and_concurrent_clones_share_success() {
        let (field, material, pairing) = fixture();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let port = &boundary.ports()[0];
        let cloned = port.clone();
        assert!(Arc::ptr_eq(&port.square, &cloned.square));
        std::thread::scope(|scope| {
            let first = scope.spawn(|| port.square().unwrap());
            let second = scope.spawn(|| cloned.square().unwrap());
            assert!(std::ptr::eq(first.join().unwrap(), second.join().unwrap()));
        });
        // Only this owner-module test can forge invalid immutable operands. A shape failure
        // must neither install a partial square nor poison a later read.
        let mut invalid = port.clone();
        invalid.square = Arc::new(OnceLock::new());
        invalid.rotor = ExactRatMatrix::identity(1).unwrap();
        assert!(invalid.square().is_err());
        assert!(invalid.square.get().is_none());
        assert!(invalid.square().is_err());
        invalid.rotor = port.rotor.clone();
        assert_eq!(invalid.square().unwrap(), port.square().unwrap());
    }

    #[test]
    fn lazy_decoder_failure_is_not_cached_and_a_singular_port_is_refused_at_admission() {
        let (field, material, pairing) = fixture();
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let port = &boundary.ports()[0];
        // Only this owner-module test can forge invalid immutable operands. A failed formation
        // must neither install a partial decoder nor poison a later read.
        let mut invalid = port.clone();
        invalid.decoder = Arc::new(OnceLock::new());
        invalid.square = Arc::new(OnceLock::new());
        invalid.injection = ExactRatMatrix::zero(10, 4).unwrap();
        assert!(invalid.decoder().is_err());
        assert!(invalid.decoder.get().is_none());
        assert!(invalid.square().is_err());
        invalid.injection = port.injection.clone();
        assert_eq!(invalid.decoder().unwrap(), port.decoder().unwrap());
        // A port with a kernel is refused before any consumer reads it.
        let mut collapsed = port.injection().to_rows();
        for row in &mut collapsed {
            row[2] = row[0].clone();
            row[3] = row[1].clone();
        }
        let collapsed = ExactRatMatrix::new(collapsed).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &collapsed).unwrap();
        let singular = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, collapsed, carrier.symmetry())
            .unwrap();
        assert_eq!(
            format!(
                "{:?}",
                PairedObservation::admit(&field, &singular, &pairing)
            ),
            format!(
                "{:?}",
                PairedObservation::admit_reference(&field, &singular, &pairing)
            )
        );
        assert!(PairedObservation::admit(&field, &singular, &pairing).is_err());
    }

    #[test]
    fn paired_observation_matches_independent_original_admission() {
        let (field, material, pairing) = fixture();
        let lazy = PairedObservation::admit(&field, &material, &pairing).unwrap();
        let eager = PairedObservation::admit_reference(&field, &material, &pairing).unwrap();
        assert_eq!(lazy, eager);
        assert_eq!(
            lazy.encode(&[0, 1, 2, 3]).unwrap(),
            eager.encode(&[0, 1, 2, 3]).unwrap()
        );
        for (lazy, eager) in lazy.ports().iter().zip(eager.ports()) {
            assert!(lazy.decoder.get().is_none());
            assert!(eager.decoder.get().is_some());
            assert!(lazy.square.get().is_none());
            assert!(eager.square.get().is_some());
            assert_eq!(lazy.decoder().unwrap(), eager.decoder().unwrap());
            assert_eq!(lazy.square().unwrap(), eager.square().unwrap());
        }
        let port = ExactRatMatrix::zero(10, 4).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &port).unwrap();
        let singular = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, port, carrier.symmetry())
            .unwrap();
        assert_eq!(
            format!(
                "{:?}",
                PairedObservation::admit(&field, &singular, &pairing)
            ),
            format!(
                "{:?}",
                PairedObservation::admit_reference(&field, &singular, &pairing)
            )
        );
    }
}
