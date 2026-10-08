//! Finite contact-to-anchor gain on the actual loaded field (Refs #62 #73).
//!
//! The positive metric here is the declared coordinate norm on the *whole* field:
//! storage and both returned-wave ports, contact `(u/(hG),w/G)`, and loaded-ring
//! `(u/(hY),w/Y)`. All coordinates are in the wave chart; h,G,Y are the fixed
//! producing clock and port declarations, not fitted normalizations.
//! It is not the possibly signed physical storage form. Material and clock remain
//! resident; this transient certificate neither emits a pulse nor replaces them.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::Reach;
use crate::hnn::propagation::Operands;
use crate::holon::deposition::schur_norms;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

fn integer(n: usize) -> Rat {
    Rat::from_integer(BigInt::from(n))
}
fn square(x: &Rat) -> Rat {
    x * x
}
fn norm_squared(matrix: &ExactRatMatrix) -> Rat {
    let (column, row) = schur_norms(matrix);
    column * row
}

/// The ACTUAL local map in the fixed wave chart (e,U=u/(hY),W=w/Y).
/// With q=omega/Y=X(h e/Y-h^2 K U+2C W), its output is
/// (e-2q,U+q,-W+2q). All three ports/states and phase-dependent K are kept.
/// This map is fixed over this consumer's contact-only material ray.
fn loaded_block(inverse: &ExactRatMatrix, capacity: &ExactRatMatrix,
    stiffness: &ExactRatMatrix, h: &Rat, y: &Rat) -> Result<ExactRatMatrix, HnnError>
{
    let n = inverse.rows();
    let extent = n.checked_mul(3).ok_or(HnnError::CountOverflow)?;
    let right = [inverse.scaled(&(h / y)),
        inverse.multiply(stiffness)?.scaled(&(-square(h))),
        inverse.multiply(capacity)?.scaled(&integer(2))];
    let correction = [-integer(2), Rat::one(), integer(2)];
    let diagonal = [Rat::one(), Rat::one(), -Rat::one()];
    let mut rows = vec![vec![Rat::zero(); extent]; extent];
    for a in 0..3 {
        for b in 0..3 {
            for i in 0..n {
                for j in 0..n {
                    rows[a*n+i][b*n+j] = &correction[a] * right[b].get(i,j)?;
                    if a == b && i == j { rows[a*n+i][b*n+j] += &diagonal[a]; }
                }
            }
        }
    }
    Ok(ExactRatMatrix::shaped(extent, extent, rows)?)
}

/// Two sufficient bounds on the SAME executed loaded operator. Taking their
/// minimum retains the prior certificate; it is not a score-descent theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedPhaseBound {
    pub ring: usize,
    pub phase: usize,
    pub triangle: Rat,
    pub schur: Rat,
    pub selected: Rat,
}

/// A sufficient finite product bound, not a global stability or score-decrease claim.
/// `gamma[k]` includes the junction, element, loaded return and contact stage at
/// absolute tick `opened_at+k`. These exact scalar readings are not retained in Theta.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedSpanReading {
    pub opened_at: usize,
    pub stations: Vec<u64>,
    pub gamma: Vec<Rat>,
    pub receiving_projection: Rat,
    pub contact_injection: Vec<Rat>,
    /// Denominators of the declared contact and loaded-ring state coordinates.
    pub contact_coordinates: Vec<(Rat, Rat)>,
    pub ring_coordinates: Vec<Option<(Rat, Rat)>>,
    /// Sum over stations j and contact-response ticks tau<j of the interior product.
    pub station_sum: Rat,
    /// Executed loaded solve columns read once per phase; no whole-field basis runs.
    pub solve_columns: usize,
    /// Fixed phase bounds, including the old certificate and actual operator Schur bound.
    pub loaded_phase_bounds: Vec<LoadedPhaseBound>,
    /// C/K FORM spectral-norm upper bounds over the actual joint FACTOR ray;
    /// c=ray_product(F_C,D_C,eta) bounds ||C_form||2, not its square.
    pub contact_form_norms: Vec<(Rat, Rat)>,
    pub junction_element_bound: Rat,
    pub contact_stage_bound: Rat,
}

/// Bound source-owned by ContactCut's producing Operands, opened clock and station partition.
/// Exact linear execution only: split/chart and quartic returns require their own
/// additional-input/domain certificate and are refused, rather than omitted.
pub(crate) struct FiniteContactSpans {
    opened_at: usize,
    stations: Vec<u64>,
    fixed: Vec<Rat>,
    injection: Vec<Rat>,
    receiving: Rat,
    h2: Rat,
    contact_g2: Vec<Rat>,
    contact_coordinates: Vec<(Rat, Rat)>,
    ring_coordinates: Vec<Option<(Rat, Rat)>>,
    solve_columns: usize,
    loaded_phase_bounds: Vec<LoadedPhaseBound>,
    junction_element_bound: Rat,
}

impl FiniteContactSpans {
    pub(crate) fn of(
        operands: &Operands,
        opened_at: usize,
        reach: &Reach,
    ) -> Result<Self, HnnError> {
        if operands.lattice().is_some()
            || operands.rings().iter().any(|r| r.chart().is_some())
            || operands.contacts().iter().any(|c| c.chart().is_some())
        {
            return Err(HnnError::Realization {
                what: "finite loaded gain requires the exact unsplit producing word",
            });
        }
        let h2 = square(operands.step());
        let top = usize::try_from(reach.stations.iter().max().copied().unwrap_or(0))
            .map_err(|_| HnnError::CountOverflow)?;
        opened_at.checked_add(top).ok_or(HnnError::CountOverflow)?;
        operands
            .rings()
            .get(reach.receiver)
            .ok_or(HnnError::MissingReceivingMap {
                ring: reach.receiver,
            })?;
        let projection = operands.weights(reach.receiver).iter().map(square).sum();
        let mut junction_element = Rat::one();
        let mut loaded_by_ring = Vec::new();
        let mut solve_columns = 0usize;
        let mut ring_coordinates = Vec::new();
        let mut loaded_phase_bounds = Vec::new();
        for (g, ring) in operands.rings().iter().enumerate() {
            // Junction J=2 1 w^T-I; c=(w-e_storage)^T x is a simultaneous
            // output of the same junction, not a fixed external contrast drive.
            let weights = operands.weights(g);
            let p = weights.len();
            let column = weights
                .iter()
                .map(|w| (integer(2) * w - Rat::one()).abs() + integer(2 * (p - 1)) * w.abs())
                .max()
                .unwrap_or_else(Rat::zero);
            let row = weights
                .iter()
                .map(|w| (integer(2) * w - Rat::one()).abs() + integer(2) * (Rat::one() - w))
                .max()
                .unwrap_or_else(Rat::zero);
            let junction = column * row;
            let contrast_projection: Rat = weights
                .iter()
                .enumerate()
                .map(|(j, w)| square(&(w - if j == 0 { Rat::one() } else { Rat::zero() })))
                .sum();
            let solve = ring.solve()?;
            let element = solve
                .scaled(&integer(2))
                .subtract(&ExactRatMatrix::identity(ring.width())?)?;
            let drive = solve.multiply(ring.contrast())?;
            // s'=E b+X Wc c, with every outgoing contact wave kept as well.
            let stage = (integer(2) * norm_squared(&element)).max(Rat::one()) * junction
                + integer(2) * norm_squared(&drive) * contrast_projection;
            junction_element = junction_element.max(stage);
            let Some(resonator) = &operands.resonators()[g] else {
                loaded_by_ring.push(None);
                ring_coordinates.push(None);
                continue;
            };
            if resonator.material().saturation().is_some() || !resonator.charts().is_empty() {
                return Err(HnnError::Realization {
                    what: "finite loaded gain requires a linear exact loaded-ring law",
                });
            }
            let n = resonator.width();
            let capacity = norm_squared(resonator.material().forms().0);
            let y = resonator.admittance();
            ring_coordinates.push(Some((operands.step() * y, y.clone())));
            let decoder = integer(9) / square(y);
            let mut phases = Vec::with_capacity(resonator.phases());
            for phase in 0..resonator.phases() {
                // Read the executed solve, not a separately reconstructed ideal inverse.
                let mut entries = vec![vec![Rat::zero(); n]; n];
                for j in 0..n {
                    let mut basis = vec![Rat::zero(); n];
                    basis[j] = Rat::one();
                    for (i, value) in resonator.solve(phase, &basis)?.into_iter().enumerate() {
                        entries[i][j] = value;
                    }
                    solve_columns = solve_columns
                        .checked_add(1)
                        .ok_or(HnnError::CountOverflow)?;
                }
                let inverse = ExactRatMatrix::shaped(n, n, entries)?;
                let right = &h2
                    + square(&h2) * square(y) * norm_squared(resonator.stiffness(phase))
                    + integer(4) * square(y) * &capacity;
                // [e,u/(hY),w/Y] -> [e,u/(hY),-w/Y] + [-2,1,2] omega/Y.
                let triangle = integer(2) * (Rat::one() + &decoder * norm_squared(&inverse) * right);
                let schur = norm_squared(&loaded_block(&inverse, resonator.material().forms().0,
                    resonator.stiffness(phase), operands.step(), y)?);
                let selected = triangle.clone().min(schur.clone());
                phases.push(selected.clone());
                loaded_phase_bounds.push(LoadedPhaseBound { ring: g, phase,
                    triangle, schur, selected });
            }
            loaded_by_ring.push(Some(phases));
        }
        let fixed = (0..top)
            .map(|k| {
                let loaded = operands
                    .resonators()
                    .iter()
                    .zip(&loaded_by_ring)
                    .filter_map(|(law, bounds)| law.as_ref().zip(bounds.as_ref()))
                    .map(|(law, bounds)| bounds[law.phase_at(opened_at + k)].clone())
                    .max()
                    .unwrap_or_else(Rat::one)
                    .max(Rat::one());
                &junction_element * loaded
            })
            .collect();
        // zeta=m^-1 q decodes to [-zeta/h,+zeta/h,zeta/(2h),zeta/h].
        let injection = operands
            .contacts()
            .iter()
            .map(|_| integer(13) / (integer(4) * &h2))
            .collect();
        let contact_g2 = operands
            .contacts()
            .iter()
            .map(|c| square(c.conductance()))
            .collect();
        let contact_coordinates = operands
            .contacts()
            .iter()
            .map(|c| (operands.step() * c.conductance(), c.conductance().clone()))
            .collect();
        Ok(Self {
            opened_at,
            stations: reach.stations.clone(),
            fixed,
            injection,
            receiving: projection,
            h2,
            contact_g2,
            contact_coordinates,
            ring_coordinates,
            solve_columns,
            loaded_phase_bounds,
            junction_element_bound: junction_element,
        })
    }

    /// C/K form-norm bounds for *all* contacts over the current joint factor ray.
    /// D remains Gram-positive along its entire ray, so m>=I and ||m^-1||<=1;
    /// decreasing D is not assumed to improve the bound.
    pub(crate) fn read(&self, forms: &[(Rat, Rat)]) -> Result<LoadedSpanReading, HnnError> {
        if forms.len() != self.injection.len() {
            return Err(HnnError::Realization {
                what: "finite loaded gain reads every producing contact",
            });
        }
        let contact = forms
            .iter()
            .zip(&self.injection)
            .zip(&self.contact_g2)
            .map(|(((c, k), decoder), g2)| {
                let right = integer(2) * &self.h2
                    + integer(4) * g2 * square(c)
                    + square(&self.h2) * g2 * square(k);
                integer(2) * (Rat::one() + decoder * right)
            })
            .max()
            .unwrap_or_else(Rat::one)
            .max(Rat::one());
        let gamma: Vec<Rat> = self.fixed.iter().map(|bound| bound * &contact).collect();
        // a[j]=sum_(tau<j) product_(tau<k<j) gamma[k]. Thus a[0]=0,
        // a[j]=1+gamma[j-1]a[j-1], with the empty product exactly one.
        let mut sums = vec![Rat::zero()];
        for bound in &gamma {
            sums.push(Rat::one() + bound * sums.last().expect("seeded"));
        }
        let station_sum = self
            .stations
            .iter()
            .map(|&j| sums[j as usize].clone())
            .sum();
        Ok(LoadedSpanReading {
            opened_at: self.opened_at,
            stations: self.stations.clone(),
            gamma,
            receiving_projection: self.receiving.clone(),
            contact_injection: self.injection.clone(),
            contact_coordinates: self.contact_coordinates.clone(),
            ring_coordinates: self.ring_coordinates.clone(),
            station_sum,
            solve_columns: self.solve_columns,
            loaded_phase_bounds: self.loaded_phase_bounds.clone(),
            contact_form_norms: forms.to_vec(),
            junction_element_bound: self.junction_element_bound.clone(),
            contact_stage_bound: contact,
        })
    }
}

impl LoadedSpanReading {
    pub(crate) fn gain(&self, contact: usize, readout_squared: &Rat) -> Rat {
        readout_squared
            * &self.receiving_projection
            * &self.contact_injection[contact]
            * &self.station_sum
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial,
        ResonatorOperands, ResonatorRemainders};
    use crate::holon::parametron::Carrier;
    use crate::ratio::rat;

    #[test]
    fn the_full_loaded_block_matches_actual_ticks_at_nonunit_wave_scales_and_all_phases() {
        let capacity = ExactRatMatrix::new(vec![vec![integer(2), Rat::one()],
            vec![Rat::one(), integer(2)]]).unwrap();
        let stiffness = ExactRatMatrix::new(vec![vec![integer(3), Rat::zero()],
            vec![Rat::zero(), integer(5)]]).unwrap();
        let material = ResonatorMaterial::new(capacity.clone(), stiffness,
            ExactRatMatrix::identity(2).unwrap().scaled(&rat(1, 8)),
            Some(PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap()),
        ).unwrap();
        let h = rat(1, 2);
        let y = integer(3);
        let law = ResonatorOperands::at_cut(0, &material, &y, &h, None).unwrap();
        let mut strict_improvement = false;
        // Visit the same actual phase at two absolute clocks, not a phase-zero idealization.
        for tick in 0..2*law.phases() {
            let phase = law.phase_at(tick);
            let mut inverse = vec![vec![Rat::zero(); 2]; 2];
            for j in 0..2 {
                let mut basis = vec![Rat::zero(); 2];
                basis[j] = Rat::one();
                for (i, value) in law.solve(phase, &basis).unwrap().into_iter().enumerate() {
                    inverse[i][j] = value;
                }
            }
            let inverse = ExactRatMatrix::shaped(2, 2, inverse).unwrap();
            let block = loaded_block(&inverse, &capacity, law.stiffness(phase), &h, &y).unwrap();
            let schur = norm_squared(&block);
            let triangle = integer(2) * (Rat::one() + integer(9)/square(&y)
                * norm_squared(&inverse) * (square(&h) + square(&square(&h))*square(&y)
                    * norm_squared(law.stiffness(phase)) + integer(4)*square(&y)*norm_squared(&capacity)));
            let selected = triangle.clone().min(schur.clone());
            strict_improvement |= selected < triangle;
            let mut inputs: Vec<Vec<Rat>> = (0..6).map(|j| {
                let mut v = vec![Rat::zero(); 6]; v[j] = Rat::one(); v
            }).collect();
            inputs.push(vec![rat(2, 3), rat(-3, 5), rat(4, 7), rat(5, 11), rat(-6, 13), rat(7, 17)]);
            for v in inputs {
                let u: Vec<_> = v[2..4].iter().map(|x| &h*&y*x).collect();
                let w: Vec<_> = v[4..6].iter().map(|x| &y*x).collect();
                // Independent actual native drive/loaded step, including full returned wave.
                let actual = law.step(tick, &v[..2], [&u, &w],
                    &ResonatorRemainders::default(), None).unwrap();
                assert!(actual.closes());
                let normalized: Vec<_> = actual.output.iter().cloned()
                    .chain(actual.state[0].iter().map(|x| x/(&h*&y)))
                    .chain(actual.state[1].iter().map(|x| x/&y)).collect();
                assert_eq!(block.apply(&v).unwrap(), normalized);
                let input: Rat = v.iter().map(square).sum();
                let output: Rat = normalized.iter().map(square).sum();
                assert!(output <= &selected*&input);
                assert!(selected <= triangle && selected <= schur);
            }
        }
        assert!(strict_improvement, "preserving actual matrix cancellations can sharpen the valid fallback");
    }
}
