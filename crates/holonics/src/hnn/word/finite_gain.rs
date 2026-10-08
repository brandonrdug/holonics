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
                phases.push(integer(2) * (Rat::one() + &decoder * norm_squared(&inverse) * right));
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
