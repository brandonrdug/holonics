//! Cold decoder of the exact deposit and the retained unrounded-response comparison.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

#[derive(Debug, Serialize)]
pub struct NativeContactDepositReading {
    pub at_cut: usize,
    pub contact_count: usize,
    pub realization: NativeContactRealization,
    pub fractional_bits: u32,
    pub unrounded_covector_radius: Rat,
    /// Oriented Q_F(Ghat)-Ghat, decoded from the immutable factors, in contact birth order.
    pub numerical_projection_residual: Vec<Vec<ExactComplexWaveCurrent>>,
    pub numerical_projection_residual_norm_square: Rat,
    /// Bounds distance from the installed numerical increment to the unrounded covector.
    /// In DyadicDeposit this is a comparison defect, not uncertainty in the new coefficient.
    pub unrounded_response_distance_upper: Rat,
}

impl NativeConstitutiveField<'_> {
    pub fn inspect_contact_deposit(&self, at: usize) -> Result<NativeContactDepositReading, Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        let r = op.returns.get(at).ok_or(Error::ForeignOccurrence)?;
        let read = |s: &ResidentSection<'_>| {
            wides(&self.relation.surface.detach_section(s, 64)?.intervals)
        };
        let ports = read(&r.ports)?;
        let currents = read(&r.currents)?;
        let bounds = read(&r.bounds)?;
        let scale = BigInt::one() << op.grain;
        let scale_ratio = Rat::from_integer(scale.clone());
        let wave = |v: &[i128]| {
            ExactComplexWaveCurrent::new(
                Rat::new(v[0].into(), scale.clone()),
                Rat::new(v[1].into(), scale.clone()),
            )
        };
        let d = 6 * self.nodes();
        let k = r.contact_count;
        let mut residual = Vec::with_capacity(k);
        let mut norm = Rat::zero();
        let mut loss = Rat::zero();
        for i in 0..k {
            let mut row = Vec::with_capacity(d / 2);
            for j in (0..d).step_by(2) {
                let mut value = ExactComplexWaveCurrent::zero();
                for f in 0..2 {
                    value = value.add(&wave(&ports[f * d + j..f * d + j + 2]).multiply(
                        &wave(&currents[2 * (f * k + i)..2 * (f * k + i) + 2]).conjugate(),
                    ));
                }
                let quantize = |x: &Rat| Rat::new((x * &scale_ratio).to_integer(), scale.clone());
                let difference = ExactComplexWaveCurrent::new(
                    quantize(&value.real) - value.real,
                    quantize(&value.imaginary) - value.imaginary,
                );
                norm += difference.norm_square();
                loss += difference.real.abs() + difference.imaginary.abs();
                row.push(difference);
            }
            residual.push(row);
        }
        let radius = Rat::new(bounds[0].into(), scale);
        Ok(NativeContactDepositReading {
            at_cut: r.at_cut,
            contact_count: k,
            realization: r.realization,
            fractional_bits: op.grain,
            unrounded_covector_radius: radius.clone(),
            numerical_projection_residual: residual,
            numerical_projection_residual_norm_square: norm,
            unrounded_response_distance_upper: radius + loss,
        })
    }
}
