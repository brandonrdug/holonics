//! Exact reference for the existing paired producer, including its contact-morphology return.
//! This is cold differential algebra, not another ecology or a native state update. An enclosed
//! operand retains its uncertainty outside this point calculation; its centre is not sealed here.
use super::*;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use num_traits::{One, Zero};

type Wave = ExactComplexWaveCurrent;
type Error = ExactLinearError;

fn dot(a: &[Wave], b: &[Wave]) -> Wave {
    a.iter()
        .zip(b)
        .fold(Wave::zero(), |s, (a, b)| s.add(&a.conjugate().multiply(b)))
}
fn add(a: &[Wave], b: &[Wave]) -> Vec<Wave> {
    a.iter().zip(b).map(|(a, b)| a.add(b)).collect()
}
fn sub(a: &[Wave], b: &[Wave]) -> Vec<Wave> {
    a.iter().zip(b).map(|(a, b)| a.subtract(b)).collect()
}
fn twice(a: &[Wave]) -> Vec<Wave> {
    a.iter()
        .map(|v| v.scaled(&Rat::from_integer(2.into())))
        .collect()
}
fn rows(contacts: &[Vec<Wave>], v: &[Wave]) -> Vec<Wave> {
    contacts.iter().map(|d| dot(d, v)).collect()
}
fn columns(contacts: &[Vec<Wave>], v: &[Wave], width: usize) -> Vec<Wave> {
    let mut out = vec![Wave::zero(); width];
    for (d, v) in contacts.iter().zip(v) {
        for (o, d) in out.iter_mut().zip(d) {
            *o = o.add(&d.multiply(v));
        }
    }
    out
}

/// Cold exact linearization at one declared source/current/contact cut. Contacts are columns
/// d_i, so the producer's row map is R_i=d_i*. The unit metrics are part of this construction.
/// Chronology and admission of variations belong to the caller's actual field passage.
pub struct PairedJunctionLinearization {
    contacts: Vec<Vec<Wave>>,
    incoming_internal: Vec<Wave>,
    inverse: ExactRatMatrix,
    potential: Vec<Wave>,
    outgoing: Vec<Wave>,
    internal: Vec<Wave>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct PairedJunctionTangent {
    pub potential: Vec<Wave>,
    pub outgoing: Vec<Wave>,
    pub internal: Vec<Wave>,
}

/// Contact-column covector G_D=lambda k* + v ell*. Both oriented factors survive even
/// when their sum vanishes. This is not a dense rewritten contact family or a selected cause.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct PairedContactCotangent {
    pub port_factors: [Vec<Wave>; 2],
    pub contact_factors: [Vec<Wave>; 2],
}
impl PairedContactCotangent {
    pub fn contact(&self, at: usize) -> Result<Vec<Wave>, Error> {
        if self.port_factors[0].is_empty()
            || self.port_factors[0].len() != self.port_factors[1].len()
            || self.contact_factors[0].len() != self.contact_factors[1].len()
        {
            return Err(Error::ShapeMismatch);
        }
        if self.contact_factors.iter().any(|v| at >= v.len()) {
            return Err(Error::AddressOutside);
        }
        Ok(self.port_factors[0]
            .iter()
            .zip(&self.port_factors[1])
            .map(|(a, b)| {
                a.multiply(&self.contact_factors[0][at].conjugate())
                    .add(&b.multiply(&self.contact_factors[1][at].conjugate()))
            })
            .collect())
    }
}
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct PairedJunctionCotangent {
    pub source: Vec<Wave>,
    /// Includes a new row's constraint reaction. A row born with zero incoming current
    /// cannot be silently treated as an independently varied pre-birth current.
    pub incoming_internal: Vec<Wave>,
    pub contacts: PairedContactCotangent,
    pub potential_covector: Vec<Wave>,
}

impl PairedJunctionLinearization {
    pub fn potential(&self) -> &[Wave] {
        &self.potential
    }
    pub fn outgoing(&self) -> &[Wave] {
        &self.outgoing
    }
    pub fn internal(&self) -> &[Wave] {
        &self.internal
    }
    pub fn at(contacts: Vec<Vec<Wave>>, source: &[Wave], internal: &[Wave]) -> Result<Self, Error> {
        let n = source.len();
        if n == 0 || contacts.iter().any(|d| d.len() != n) || internal.len() != contacts.len() {
            return Err(Error::ShapeMismatch);
        }
        let d = n.checked_mul(2).ok_or(Error::ExtentOverflow)?;
        let mut a = vec![vec![Rat::zero(); d]; d];
        for i in 0..n {
            for j in 0..n {
                let mut z = if i == j {
                    Wave::new(Rat::one(), Rat::zero())
                } else {
                    Wave::zero()
                };
                for contact in &contacts {
                    z = z.add(&contact[i].multiply(&contact[j].conjugate()));
                }
                a[2 * i][2 * j] = z.real.clone();
                a[2 * i][2 * j + 1] = -&z.imaginary;
                a[2 * i + 1][2 * j] = z.imaginary;
                a[2 * i + 1][2 * j + 1] = z.real;
            }
        }
        let inverse = ExactRatMatrix::new(a)?.inverse()?;
        let mut result = Self {
            contacts,
            incoming_internal: internal.to_vec(),
            inverse,
            potential: vec![],
            outgoing: vec![],
            internal: vec![],
        };
        let h = columns(&result.contacts, internal, n);
        result.potential = result.solve(&twice(&add(source, &h)))?;
        result.outgoing = sub(&result.potential, source);
        result.internal = sub(&rows(&result.contacts, &result.potential), internal);
        Ok(result)
    }
    fn solve(&self, v: &[Wave]) -> Result<Vec<Wave>, Error> {
        let values = v
            .iter()
            .flat_map(|v| [v.real.clone(), v.imaginary.clone()])
            .collect::<Vec<_>>();
        Ok(self
            .inverse
            .apply(&values)?
            .chunks_exact(2)
            .map(|v| Wave::new(v[0].clone(), v[1].clone()))
            .collect())
    }
    pub fn pushforward(
        &self,
        source: &[Wave],
        internal: &[Wave],
        contacts: &[Vec<Wave>],
    ) -> Result<PairedJunctionTangent, Error> {
        let n = self.potential.len();
        let k = self.contacts.len();
        if source.len() != n
            || internal.len() != k
            || contacts.len() != k
            || contacts.iter().any(|d| d.len() != n)
        {
            return Err(Error::ShapeMismatch);
        }
        let k_current = sub(&self.incoming_internal, &self.internal);
        let delta_r_v = rows(contacts, &self.potential);
        let rhs = sub(
            &add(
                &twice(&add(source, &columns(&self.contacts, internal, n))),
                &columns(contacts, &k_current, n),
            ),
            &columns(&self.contacts, &delta_r_v, n),
        );
        let potential = self.solve(&rhs)?;
        let outgoing = sub(&potential, source);
        let internal = sub(
            &add(&delta_r_v, &rows(&self.contacts, &potential)),
            internal,
        );
        Ok(PairedJunctionTangent {
            potential,
            outgoing,
            internal,
        })
    }
    pub fn pullback(
        &self,
        outgoing: &[Wave],
        internal: &[Wave],
    ) -> Result<PairedJunctionCotangent, Error> {
        let n = self.potential.len();
        if outgoing.len() != n || internal.len() != self.contacts.len() {
            return Err(Error::ShapeMismatch);
        }
        let lambda = self.solve(&add(outgoing, &columns(&self.contacts, internal, n)))?;
        let r_lambda = rows(&self.contacts, &lambda);
        Ok(PairedJunctionCotangent {
            source: sub(&twice(&lambda), outgoing),
            incoming_internal: sub(&twice(&r_lambda), internal),
            contacts: PairedContactCotangent {
                port_factors: [lambda.clone(), self.potential.clone()],
                contact_factors: [
                    sub(&self.incoming_internal, &self.internal),
                    sub(internal, &r_lambda),
                ],
            },
            potential_covector: lambda,
        })
    }
}

#[cfg(test)]
mod tests;
