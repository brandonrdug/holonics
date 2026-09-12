//! Pure exact rational bilinear application; one resident passage, retained product section.
use super::*;
use crate::exact_linear::{BilinearProductCore, BilinearRealization, ExactRatMatrix};
use num_traits::{One, ToPrimitive};
use std::rc::Rc;

fn refusal(what: impl Into<String>) -> ResidentRefusal {
    ResidentRefusal::Declaration {
        operation: "exact-bilinear",
        what: what.into(),
    }
}
fn gcd(mut a: BigInt, mut b: BigInt) -> BigInt {
    while b != BigInt::from(0) {
        let r = a % &b;
        a = b;
        b = r;
    }
    a
}
fn packet(values: &[Rat]) -> Result<Vec<i64>, ResidentRefusal> {
    let mut denominator = BigInt::one();
    for value in values {
        denominator =
            (&denominator / gcd(denominator.clone(), value.denom().clone())) * value.denom();
    }
    let mut words = values
        .iter()
        .map(|v| {
            (v.numer() * (&denominator / v.denom()))
                .to_i64()
                .ok_or_else(|| refusal("exact numerator exceeds signed-word packet carrier"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    words.push(
        denominator.to_i64().ok_or_else(|| {
            refusal("exact common denominator exceeds signed-word packet carrier")
        })?,
    );
    Ok(words)
}
/// A sealed exact coefficient matrix already resident on the device.
///
/// The dimensions are carried separately because a packet is a flat rational word
/// population.  Keeping them here prevents a compiler from accidentally changing the
/// tensor chart while reusing the native packet kernels.
pub(crate) struct MatrixPacket<'c> {
    section: ResidentSection<'c>,
    rows: usize,
    columns: usize,
}
impl<'c> MatrixPacket<'c> {
    fn mount(
        surface: &'c ResidentSurface<'c>,
        matrix: &ExactRatMatrix,
    ) -> Result<Self, ResidentRefusal> {
        if matrix.rows() == 0 || matrix.columns() == 0 {
            return Err(refusal("resident packet matrix requires nonempty ports"));
        }
        let section = surface.mount_exact_rational_packet(matrix.entries())?;
        Ok(Self {
            section,
            rows: matrix.rows(),
            columns: matrix.columns(),
        })
    }

    pub(crate) fn from_resident(
        surface: &'c ResidentSurface<'c>,
        section: ResidentSection<'c>,
        rows: usize,
        columns: usize,
    ) -> Result<Self, ResidentRefusal> {
        if rows == 0 || columns == 0 {
            return Err(refusal("resident coefficient packet requires nonempty dimensions"));
        }
        let entries = rows
            .checked_mul(columns)
            .ok_or_else(|| refusal("resident coefficient dimensions overflow"))?;
        // A coefficient packet is one row of exact words followed by its common denominator.
        surface.validate_packet(&section, entries)?;
        Ok(Self { section, rows, columns })
    }
}

#[derive(Clone)]
enum CoreIdentity {
    Host(std::sync::Arc<BilinearProductCore>),
    Compiled(Rc<()>),
}

impl CoreIdentity {
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Host(a), Self::Host(b)) => std::sync::Arc::ptr_eq(a, b),
            (Self::Compiled(a), Self::Compiled(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

pub struct ResidentBilinearMap<'c> {
    core: CoreIdentity,
    surface: &'c ResidentSurface<'c>,
    left: MatrixPacket<'c>,
    right: MatrixPacket<'c>,
    receiver: MatrixPacket<'c>,
}
pub struct ResidentBilinearReturn<'c> {
    core: CoreIdentity,
    left: ResidentSection<'c>,
    right: ResidentSection<'c>,
    product: ResidentSection<'c>,
    output: ResidentSection<'c>,
}
impl<'c> ResidentBilinearReturn<'c> {
    pub fn left(&self) -> &ResidentSection<'c> {
        &self.left
    }
    pub fn right(&self) -> &ResidentSection<'c> {
        &self.right
    }
    pub fn product(&self) -> &ResidentSection<'c> {
        &self.product
    }
    pub fn output(&self) -> &ResidentSection<'c> {
        &self.output
    }
}
impl<'c> ResidentBilinearMap<'c> {
    pub fn mount(
        surface: &'c ResidentSurface<'c>,
        realization: &BilinearRealization,
    ) -> Result<Self, ResidentRefusal> {
        Ok(Self {
            core: CoreIdentity::Host(std::sync::Arc::clone(realization.core())),
            surface,
            left: MatrixPacket::mount(surface, realization.core().left_forms())?,
            right: MatrixPacket::mount(surface, realization.core().right_forms())?,
            receiver: MatrixPacket::mount(surface, &realization.receiver().particular)?,
        })
    }

    /// Mount three exact A/B/D coefficient packets produced by a resident compiler.
    /// `left_rows/columns`, `right_rows/columns`, and `receiver_rows/columns` are the
    /// declared matrix charts; the packets themselves remain owned by this map.
    pub(crate) fn from_resident_packets(
        surface: &'c ResidentSurface<'c>,
        left: ResidentSection<'c>,
        left_rows: usize,
        left_columns: usize,
        right: ResidentSection<'c>,
        right_rows: usize,
        right_columns: usize,
        receiver: ResidentSection<'c>,
        receiver_rows: usize,
        receiver_columns: usize,
    ) -> Result<Self, ResidentRefusal> {
        let left = MatrixPacket::from_resident(surface, left, left_rows, left_columns)?;
        let right = MatrixPacket::from_resident(surface, right, right_rows, right_columns)?;
        let receiver = MatrixPacket::from_resident(surface, receiver, receiver_rows, receiver_columns)?;
        if left.rows != right.rows || receiver.columns != left.rows {
            return Err(refusal("resident A/B/D coefficient charts do not meet"));
        }
        Ok(Self {
            core: CoreIdentity::Compiled(Rc::new(())),
            surface,
            left,
            right,
            receiver,
        })
    }
    /// Apply this receiver to the retained product occurrence from the same immutable core.
    /// The source products are reused on device; no contractions or source values are replayed.
    pub fn read_product(
        &self,
        source: &ResidentBilinearReturn<'c>,
    ) -> Result<ResidentSection<'c>, ResidentRefusal> {
        if !self.core.same(&source.core) {
            return Err(refusal(
                "receiver and product do not share this core occurrence",
            ));
        }
        let output = self
            .surface
            .fresh_section(1, self.receiver.rows + 1, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface
                .record_packet_contract(&lane, &self.receiver, &source.product, &output)?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(refusal(format!(
                "product receiver: {:?}",
                receipt.obstruction
            )));
        }
        Ok(output)
    }

    pub fn apply(
        &self,
        x: &ResidentSection<'c>,
        z: &ResidentSection<'c>,
    ) -> Result<ResidentBilinearReturn<'c>, ResidentRefusal> {
        self.apply_ports(x, z, false)
    }

    /// Apply a resident compiled family to one shared affine parameter packet.
    pub(crate) fn apply_affine_shared(
        &self,
        parameters: &ResidentSection<'c>,
    ) -> Result<ResidentBilinearReturn<'c>, ResidentRefusal> {
        self.apply_ports(parameters, parameters, true)
    }
    fn apply_ports(
        &self,
        x: &ResidentSection<'c>,
        z: &ResidentSection<'c>,
        affine: bool,
    ) -> Result<ResidentBilinearReturn<'c>, ResidentRefusal> {
        let s = self.surface;
        s.validate_packet(x, self.left.columns - usize::from(affine))?;
        s.validate_packet(z, self.right.columns - usize::from(affine))?;
        let rank = self.left.rows;
        let a = s.fresh_section(1, rank + 1, ResidentGrain(0))?;
        let b = s.fresh_section(1, rank + 1, ResidentGrain(0))?;
        let product = s.fresh_section(1, rank + 1, ResidentGrain(0))?;
        let output = s.fresh_section(1, self.receiver.rows + 1, ResidentGrain(0))?;
        let mut passage = s.begin_passage(&[vec![], vec![], vec![0, 1], vec![2]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_packet_contract_mode(&lane, &self.left, x, &a, affine)?;
        }
        passage.close(0, &a, 64)?;
        {
            let lane = passage.open(1, &[])?;
            s.record_packet_contract_mode(&lane, &self.right, z, &b, affine)?;
        }
        passage.close(1, &b, 64)?;
        {
            let lane = passage.open(2, &[0, 1])?;
            s.record_packet_hadamard(&lane, &a, &b, &product)?;
        }
        passage.close(2, &product, 64)?;
        {
            let lane = passage.open(3, &[2])?;
            s.record_packet_contract(&lane, &self.receiver, &product, &output)?;
        }
        passage.close(3, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(refusal(format!(
                "exact packet passage: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentBilinearReturn {
            core: self.core.clone(),
            left: a,
            right: b,
            product,
            output,
        })
    }
}
impl<'c> ResidentSurface<'c> {
    /// Exterior exact codec: no value rounding. Nonrepresentable word packets return an obstruction.
    pub fn mount_exact_rational_packet(
        &'c self,
        values: &[Rat],
    ) -> Result<ResidentSection<'c>, ResidentRefusal> {
        if values.is_empty() {
            return Err(refusal("empty current packet"));
        }
        let words = packet(values)?;
        let rest = ResidentSectionRest::found(
            1,
            words.len(),
            ResidentGrain(0),
            64,
            words.into_iter().map(|v| (v, v)).collect(),
        )
        .map_err(refusal)?;
        self.mount_section_rest(&rest)
    }
    fn validate_packet(
        &self,
        section: &ResidentSection<'c>,
        width: usize,
    ) -> Result<(), ResidentRefusal> {
        if !std::ptr::eq(section.surface, self)
            || section.rows != 1
            || section.width
                != width
                    .checked_add(1)
                    .ok_or_else(|| refusal("packet extent overflow"))?
            || section.grain.0 != 0
            || width >= u32::MAX as usize
        {
            return Err(refusal(
                "incompatible surface, extent or rational packet grain",
            ));
        }
        Ok(())
    }
    fn packet_shared(&self, width: usize) -> Result<u32, ResidentRefusal> {
        width
            .checked_mul(16)
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(|| refusal("exact packet scratch exceeds declared device aperture"))
    }
    fn record_packet_contract(
        &self,
        lane: &Lane<'_, 'c>,
        matrix: &MatrixPacket<'c>,
        input: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.record_packet_contract_mode(lane, matrix, input, out, false)
    }
    fn record_packet_contract_mode(
        &self,
        lane: &Lane<'_, 'c>,
        matrix: &MatrixPacket<'c>,
        input: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
        affine: bool,
    ) -> Result<(), ResidentRefusal> {
        let size = matrix
            .rows
            .checked_mul(matrix.columns)
            .ok_or_else(|| refusal("matrix extent overflow"))?;
        self.validate_packet(&matrix.section, size)?;
        self.validate_packet(input, matrix.columns - usize::from(affine))?;
        self.validate_packet(out, matrix.rows)?;
        let mut p = Params::new();
        p.ptr(matrix.section.lo.device_ptr())
            .ptr(matrix.section.hi.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(matrix.rows as u32)
            .u32(matrix.columns as u32)
            .u32(u32::from(affine))
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_packet_contract",
            1,
            self.declaration.warp_size.max(1),
            self.packet_shared(matrix.rows)?,
            &mut p,
            "packet-contract",
        )
    }
    fn record_packet_hadamard(
        &self,
        lane: &Lane<'_, 'c>,
        left: &ResidentSection<'c>,
        right: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let width = left
            .width
            .checked_sub(1)
            .ok_or_else(|| refusal("missing packet denominator"))?;
        self.validate_packet(left, width)?;
        self.validate_packet(right, width)?;
        self.validate_packet(out, width)?;
        let mut p = Params::new();
        p.ptr(left.lo.device_ptr())
            .ptr(left.hi.device_ptr())
            .ptr(right.lo.device_ptr())
            .ptr(right.hi.device_ptr())
            .u32(width as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_packet_hadamard",
            1,
            self.declaration.warp_size.max(1),
            self.packet_shared(width)?,
            &mut p,
            "packet-hadamard",
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_linear::{BilinearOperator, BilinearProductCore};
    fn q(n: i64, d: i64) -> Rat {
        Rat::new(n.into(), d.into())
    }
    fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|&v| q(v, 1)).collect())
                .collect(),
        )
        .unwrap()
    }
    fn realize() -> (BilinearRealization, BilinearRealization) {
        let a = matrix(&[&[1, 0], &[0, 1], &[1, 1]]);
        let core = std::sync::Arc::new(BilinearProductCore::new(a.clone(), a).unwrap());
        let c = BilinearOperator::new(2, 2, matrix(&[&[1, 0, 0, -1], &[0, 1, 1, 0]])).unwrap();
        let p = BilinearOperator::new(2, 2, matrix(&[&[1, 0, 0, 0], &[0, 1, 1, 0], &[0, 0, 0, 1]]))
            .unwrap();
        (
            core.bind(&c).unwrap().unwrap(),
            core.bind(&p).unwrap().unwrap(),
        )
    }
    fn read(s: &ResidentSurface<'_>, x: &ResidentSection<'_>) -> Vec<Rat> {
        let words = s.read_out(x).unwrap();
        assert!(words.iter().all(|(a, b)| a == b));
        let den = words.last().unwrap().0;
        assert!(den > 0);
        words[..words.len() - 1]
            .iter()
            .map(|(v, _)| q(*v, den))
            .collect()
    }
    #[test]
    fn exact_packet_codec_preserves_non_dyadic_coefficients_and_refuses_width_overflow() {
        assert_eq!(packet(&[q(1, 3), q(-2, 5)]).unwrap(), vec![5, -6, 15]);
        assert!(packet(&[Rat::from_integer(BigInt::from(i64::MAX) + 1)]).is_err());
    }
    #[test]
    #[ignore = "requires CUDA; exact rational bilinear construction and changed resident receiver"]
    fn native_rational_product_is_reused_without_intermediate_readout() {
        let r = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&r).unwrap();
        let (c, p) = realize();
        let native = ResidentBilinearMap::mount(&s, &c).unwrap();
        let poly = ResidentBilinearMap::mount(&s, &p).unwrap();
        use crate::native_ecology::constitutive_fibre::{
            ConstitutiveReading, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
        };
        let mut downstream = ResidentConstitutiveFibre::found(&s, 2, 1).unwrap();
        downstream.advance(&[1, 0], Some(&[1])).unwrap();
        downstream.advance(&[0, 1], Some(&[0])).unwrap();
        for (left, right) in [
            (vec![q(2, 1), q(3, 1)], vec![q(4, 1), q(5, 1)]),
            (vec![q(2, 3), q(3, 5)], vec![q(4, 7), q(5, 11)]),
        ] {
            let x = s.mount_exact_rational_packet(&left).unwrap();
            let z = s.mount_exact_rational_packet(&right).unwrap();
            let reads = s.census().section_read_outs;
            let result = native.apply(&x, &z).unwrap();
            let second = poly.read_product(&result).unwrap();
            let continued = downstream
                .advance_resident(
                    ResidentConstitutiveCurrent::rational(result.output()).unwrap(),
                    None,
                )
                .unwrap();
            assert_eq!(s.census().section_read_outs, reads);
            assert_eq!(read(&s, result.output()), c.apply(&left, &right).unwrap());
            assert_eq!(read(&s, &second), p.apply(&left, &right).unwrap());
            let ConstitutiveReading::Unique { current } =
                continued.inspect().unwrap().predecessor_reading
            else {
                panic!("complete linear continuation");
            };
            assert_eq!(current, vec![c.apply(&left, &right).unwrap()[0].clone()]);
            assert_eq!(
                read(&s, result.product()),
                c.core().apply(&left, &right).unwrap()
            );
        }
    }
    #[test]
    #[ignore = "requires CUDA; non-dyadic factor and receiver coefficients remain exact"]
    fn native_non_dyadic_coefficients_and_receiver_reuse_are_exact() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let forms = matrix(&[&[1, 0], &[0, 1], &[1, 1]]);
        let core = std::sync::Arc::new(
            BilinearProductCore::new(forms.scaled(&q(1, 3)), forms.scaled(&q(1, 5))).unwrap(),
        );
        let target = BilinearOperator::new(2, 2, matrix(&[&[1, 0, 0, -1], &[0, 1, 1, 0]])).unwrap();
        let first = core.bind(&target).unwrap().unwrap();
        let changed = first
            .then_receiver(&ExactRatMatrix::identity(2).unwrap().scaled(&q(1, 7)))
            .unwrap();
        let a = ResidentBilinearMap::mount(&surface, &first).unwrap();
        let b = ResidentBilinearMap::mount(&surface, &changed).unwrap();
        let x = surface
            .mount_exact_rational_packet(&[q(2, 1), q(3, 1)])
            .unwrap();
        let y = surface
            .mount_exact_rational_packet(&[q(4, 1), q(5, 1)])
            .unwrap();
        let reads = surface.census().section_read_outs;
        let returned = a.apply(&x, &y).unwrap();
        let changed = b.read_product(&returned).unwrap();
        assert_eq!(surface.census().section_read_outs, reads);
        assert_eq!(read(&surface, &changed), vec![q(-1, 1), q(22, 7)]);
        let wrong = surface.mount_exact_rational_packet(&[q(1, 1)]).unwrap();
        assert!(a.apply(&wrong, &y).is_err());
    }
    #[test]
    #[ignore = "requires CUDA; malformed packets and exact arithmetic overflow refuse"]
    fn native_packet_refusal_does_not_publish_a_guessed_face() {
        let r = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&r).unwrap();
        let (c, _) = realize();
        let map = ResidentBilinearMap::mount(&s, &c).unwrap();
        let z = s.mount_exact_rational_packet(&[q(2, 1), q(0, 1)]).unwrap();
        for words in [
            vec![(1, 2), (0, 0), (1, 1)],
            vec![(1, 1), (0, 0), (0, 0)],
            vec![(i64::MAX, i64::MAX), (0, 0), (1, 1)],
        ] {
            let x = s
                .mount_section_rest(
                    &ResidentSectionRest::found(1, 3, ResidentGrain(0), 64, words).unwrap(),
                )
                .unwrap();
            assert!(map.apply(&x, &z).is_err());
        }
        let x = s.mount_exact_rational_packet(&[q(1, 1), q(0, 1)]).unwrap();
        let valid = map.apply(&x, &z).unwrap();
        assert_eq!(read(&s, valid.output()), vec![q(2, 1), q(0, 1)]);
    }
}

/// A resident evaluator of an implicit joint observation fibre. Both affine ports read one
/// parameter occurrence. The output is a residual current, not an automatic material commit.
pub struct ResidentJointBilinearFibre<'c> {
    model: std::sync::Arc<crate::exact_linear::JointBilinearSystem>,
    residual: ResidentBilinearMap<'c>,
}
/// A residual reading retains the actual parameter occurrence and complete implicit model.
/// This borrow does not clone the continuing source or identify it by equal coordinates.
pub struct ResidentJointBilinearEvaluation<'a, 'c> {
    parameters: &'a ResidentSection<'c>,
    model: std::sync::Arc<crate::exact_linear::JointBilinearSystem>,
    returned: ResidentBilinearReturn<'c>,
}
impl<'a, 'c> ResidentJointBilinearEvaluation<'a, 'c> {
    pub fn parameters(&self) -> &'a ResidentSection<'c> {
        self.parameters
    }
    pub fn model(&self) -> &crate::exact_linear::JointBilinearSystem {
        &self.model
    }
    pub fn residual(&self) -> &ResidentBilinearReturn<'c> {
        &self.returned
    }
    pub fn output(&self) -> &ResidentSection<'c> {
        self.returned.output()
    }
}
impl<'c> ResidentJointBilinearFibre<'c> {
    pub fn mount(
        surface: &'c ResidentSurface<'c>,
        model: std::sync::Arc<crate::exact_linear::JointBilinearFibre>,
    ) -> Result<Self, ResidentRefusal> {
        let system = crate::exact_linear::JointBilinearSystem::new(vec![model])
            .map_err(|e| refusal(e.to_string()))?;
        Self::mount_system(surface, std::sync::Arc::new(system))
    }
    pub fn mount_system(
        surface: &'c ResidentSurface<'c>,
        model: std::sync::Arc<crate::exact_linear::JointBilinearSystem>,
    ) -> Result<Self, ResidentRefusal> {
        let residual = ResidentBilinearMap::mount(surface, model.residual_realization())?;
        Ok(Self { model, residual })
    }
    pub fn model(&self) -> &crate::exact_linear::JointBilinearSystem {
        &self.model
    }
    pub fn evaluate<'a>(
        &self,
        parameters: &'a ResidentSection<'c>,
    ) -> Result<ResidentJointBilinearEvaluation<'a, 'c>, ResidentRefusal> {
        self.residual
            .surface
            .validate_packet(parameters, self.model.parameters())?;
        let returned = self.residual.apply_ports(parameters, parameters, true)?;
        Ok(ResidentJointBilinearEvaluation {
            parameters,
            model: std::sync::Arc::clone(&self.model),
            returned,
        })
    }
}

#[cfg(test)]
mod joint_tests {
    use super::*;
    use crate::exact_linear::{
        BilinearOperator, BilinearProductCore, JointBilinearFibre, JointPreimageReduction,
    };
    fn q(n: i64, d: i64) -> Rat {
        Rat::new(n.into(), d.into())
    }
    fn m(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|&v| q(v, 1)).collect())
                .collect(),
        )
        .unwrap()
    }
    fn read(s: &ResidentSurface<'_>, section: &ResidentSection<'_>) -> Vec<Rat> {
        let data = s.read_out(section).unwrap();
        assert!(data.iter().all(|(a, b)| a == b));
        let d = data.last().unwrap().0;
        assert!(d > 0);
        data[..data.len() - 1]
            .iter()
            .map(|(v, _)| q(*v, d))
            .collect()
    }
    #[test]
    #[ignore = "requires CUDA; a joint source/condition keeps shared parameter products and affine anchors"]
    fn joint_parameters_and_condition_slices_reach_native_residuals() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let core = std::sync::Arc::new(BilinearProductCore::new(m(&[&[1]]), m(&[&[1]])).unwrap());
        let action = core
            .bind(&BilinearOperator::new(1, 1, m(&[&[1]])).unwrap())
            .unwrap()
            .unwrap();
        let fibre = std::sync::Arc::new(
            JointBilinearFibre::new(action, m(&[&[1, 0, 0]]), m(&[&[0, 1, 0]]), vec![q(6, 1)])
                .unwrap(),
        );
        let native = ResidentJointBilinearFibre::mount(&s, fibre.clone()).unwrap();
        for theta in [
            vec![q(3, 1), q(2, 1)],
            vec![q(1, 3), q(1, 2)],
            vec![q(-3, 1), q(-2, 1)],
        ] {
            let parameter = s.mount_exact_rational_packet(&theta).unwrap();
            let before = s.census().section_read_outs;
            let returned = native.evaluate(&parameter).unwrap();
            assert_eq!(s.census().section_read_outs, before);
            assert_eq!(read(&s, returned.output()), fibre.evaluate(&theta).unwrap());
        }
        let slice = std::sync::Arc::new(fibre.restrict(&m(&[&[1, 0], &[0, 2], &[0, 1]])).unwrap());
        let JointPreimageReduction::Affine {
            particular,
            directions,
        } = slice.affine_preimage().unwrap()
        else {
            panic!("affine condition slice")
        };
        assert!(directions.is_empty());
        assert_eq!(particular, vec![q(3, 1)]);
        let native = ResidentJointBilinearFibre::mount(&s, slice).unwrap();
        let parameter = s.mount_exact_rational_packet(&particular).unwrap();
        assert_eq!(
            read(&s, native.evaluate(&parameter).unwrap().output()),
            vec![q(0, 1)]
        );
    }
    #[test]
    #[ignore = "requires CUDA; equal marginal families do not erase their joint correlation"]
    fn correlated_and_opposed_conditions_remain_distinct() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let identity = ExactRatMatrix::identity(2).unwrap();
        let core =
            std::sync::Arc::new(BilinearProductCore::new(identity.clone(), identity).unwrap());
        let action = core
            .bind(&BilinearOperator::new(2, 2, m(&[&[1, 0, 0, 1]])).unwrap())
            .unwrap()
            .unwrap();
        let source = m(&[&[1, 0], &[-1, 1]]);
        let correlated = std::sync::Arc::new(
            JointBilinearFibre::new(
                action.clone(),
                source.clone(),
                source.clone(),
                vec![q(1, 1)],
            )
            .unwrap(),
        );
        let opposed = std::sync::Arc::new(
            JointBilinearFibre::new(action, source, m(&[&[-1, 1], &[1, 0]]), vec![q(1, 1)])
                .unwrap(),
        );
        for (model, expected) in [
            (correlated, vec![q(0, 1), q(-4, 9)]),
            (opposed, vec![q(-1, 1), q(-5, 9)]),
        ] {
            let native = ResidentJointBilinearFibre::mount(&s, model).unwrap();
            for (theta, want) in [q(0, 1), q(1, 3)].into_iter().zip(expected) {
                let parameter = s.mount_exact_rational_packet(&[theta]).unwrap();
                assert_eq!(
                    read(&s, native.evaluate(&parameter).unwrap().output()),
                    vec![want]
                );
            }
        }
    }
}

#[cfg(test)]
mod joined_material_tests {
    use super::*;
    use crate::exact_linear::{
        BilinearOperator, BilinearProductCore, JointBilinearFibre, JointBilinearSystem,
    };
    fn q(v: i64) -> Rat {
        Rat::from_integer(v.into())
    }
    fn m(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|r| r.iter().map(|&v| q(v)).collect())
                .collect(),
        )
        .unwrap()
    }
    #[test]
    #[ignore = "requires CUDA; variable material cannot hide an invalid source-condition junction"]
    fn native_shared_junction_preserves_both_constraints() {
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let core = std::sync::Arc::new(BilinearProductCore::new(m(&[&[1]]), m(&[&[1]])).unwrap());
        let action = core
            .bind(&BilinearOperator::new(1, 1, m(&[&[1]])).unwrap())
            .unwrap()
            .unwrap();
        let product = std::sync::Arc::new(
            JointBilinearFibre::with_affine_return(
                action.clone(),
                m(&[&[1, 0, 0, 0, 0]]),
                m(&[&[0, 1, 0, 0, 0]]),
                m(&[&[0, 0, 1, 0, 0]]),
            )
            .unwrap(),
        );
        let material = std::sync::Arc::new(
            JointBilinearFibre::new(
                action,
                m(&[&[0, 0, 0, 1, 0]]),
                m(&[&[0, 0, 1, 0, 0]]),
                vec![q(24)],
            )
            .unwrap(),
        );
        let system =
            std::sync::Arc::new(JointBilinearSystem::new(vec![product, material]).unwrap());
        let native = ResidentJointBilinearFibre::mount_system(&s, system).unwrap();
        for (theta, wanted) in [([2, 3, 6, 4], [0, 0]), ([2, 3, 8, 3], [-2, 0])] {
            let parameters = s.mount_exact_rational_packet(&theta.map(q)).unwrap();
            let before = s.census().section_read_outs;
            let result = native.evaluate(&parameters).unwrap();
            assert_eq!(s.census().section_read_outs, before);
            let data = s.read_out(result.output()).unwrap();
            assert_eq!(data.len(), 3);
            assert!(data.iter().all(|(a, b)| a == b));
            for i in 0..2 {
                assert_eq!(Rat::new(data[i].0.into(), data[2].0.into()), q(wanted[i]));
            }
        }
    }
}
