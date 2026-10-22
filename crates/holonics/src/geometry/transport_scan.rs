//! Ordered composition of exact transports, used by the receiving bank's monodromy and its
//! variation. This schedules an existing associative law; it supplies no arithmetic or chart.
//!
//! `compose(earlier, later)` means the transport of the earlier span followed by the later
//! span. The caller supplies a two-sided identity and an associative exact composition. In
//! particular, rounded error-feedback streams and state-selected charts do not meet this
//! contract merely because their unsplit maps do. Such crossings must keep their serial law.

use rayon::prelude::*;

/// A refused scheduling declaration or a refusal from the caller's exact composition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OrderedScanError<E> {
    ZeroPartitions,
    Composition(E),
}

/// Inclusive prefixes of an already ordered list of exact span transports.
///
/// Each chunk reads its own span in order. The chunk totals compose by doubling in order,
/// after which every local prefix receives only the total of its preceding chunks. No input
/// cell, producing operand, or intermediate rounded state is manufactured by this scheduler.
pub(crate) fn ordered_prefixes<T, E, F>(
    transports: &[T],
    identity: &T,
    partitions: usize,
    compose: F,
) -> Result<Vec<T>, OrderedScanError<E>>
where
    T: Clone + Send + Sync,
    E: Send,
    F: Fn(&T, &T) -> Result<T, E> + Sync,
{
    let width = chunk_width(transports.len(), partitions)?;
    if transports.is_empty() {
        return Ok(Vec::new());
    }
    let chunks = transports
        .par_chunks(width)
        .map(|chunk| {
            let mut prefix = identity.clone();
            chunk
                .iter()
                .map(|transport| {
                    prefix = compose(&prefix, transport)?;
                    Ok(prefix.clone())
                })
                .collect::<Result<Vec<T>, E>>()
        })
        .collect::<Result<Vec<_>, E>>()
        .map_err(OrderedScanError::Composition)?;
    let totals: Vec<T> = chunks
        .iter()
        .map(|chunk| chunk.last().expect("nonempty chunk").clone())
        .collect();
    let preceding = scan_totals(totals, &compose).map_err(OrderedScanError::Composition)?;
    chunks
        .into_par_iter()
        .enumerate()
        .map(|(index, prefixes)| {
            if index == 0 {
                Ok(prefixes)
            } else {
                prefixes
                    .iter()
                    .map(|prefix| compose(&preceding[index - 1], prefix))
                    .collect::<Result<Vec<T>, E>>()
            }
        })
        .collect::<Result<Vec<_>, E>>()
        .map(|chunks| chunks.into_iter().flatten().collect())
        .map_err(OrderedScanError::Composition)
}

/// The total transport, using the same ordered chunk-total scan as [`ordered_prefixes`].
/// This avoids retaining every prefix when the receiver consumes only the final transport.
pub(crate) fn ordered_reduce<T, E, F>(
    transports: &[T],
    identity: &T,
    partitions: usize,
    compose: F,
) -> Result<T, OrderedScanError<E>>
where
    T: Clone + Send + Sync,
    E: Send,
    F: Fn(&T, &T) -> Result<T, E> + Sync,
{
    let width = chunk_width(transports.len(), partitions)?;
    let totals = transports
        .par_chunks(width)
        .map(|chunk| {
            chunk
                .iter()
                .try_fold(identity.clone(), |prefix, next| compose(&prefix, next))
        })
        .collect::<Result<Vec<T>, E>>()
        .map_err(OrderedScanError::Composition)?;
    Ok(scan_totals(totals, &compose)
        .map_err(OrderedScanError::Composition)?
        .pop()
        .unwrap_or_else(|| identity.clone()))
}

fn chunk_width<E>(length: usize, partitions: usize) -> Result<usize, OrderedScanError<E>> {
    if partitions == 0 {
        return Err(OrderedScanError::ZeroPartitions);
    }
    Ok(length.div_ceil(partitions.min(length.max(1))).max(1))
}

/// Hillis–Steele inclusive scan. Every stage reads only the previous stage, and composition
/// always puts the earlier span first. Noncommuting transports therefore keep passage order.
fn scan_totals<T, E, F>(mut totals: Vec<T>, compose: &F) -> Result<Vec<T>, E>
where
    T: Clone + Send + Sync,
    E: Send,
    F: Fn(&T, &T) -> Result<T, E> + Sync,
{
    let mut stride = 1;
    while stride < totals.len() {
        totals = (0..totals.len())
            .into_par_iter()
            .map(|index| {
                if index < stride {
                    Ok(totals[index].clone())
                } else {
                    compose(&totals[index - stride], &totals[index])
                }
            })
            .collect::<Result<Vec<T>, E>>()?;
        stride = stride.saturating_mul(2);
    }
    Ok(totals)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::HnnError;
    use crate::hnn::ring::{PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial};
    use crate::holon::parametron::Carrier;
    use crate::ratio::gaussian::GaussianRat;
    use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
    use crate::ratio::{Rat, integer, rat};
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    #[test]
    fn exact_transport_scan_keeps_noncommuting_wide_prefixes_and_refusals() {
        let identity = ExactRatMatrix::identity(2).unwrap();
        let maps: Vec<_> = (0..17)
            .map(|index| {
                let wide = Rat::new(
                    (BigInt::one() << 200) + BigInt::from(index),
                    BigInt::from(2 * index + 3),
                );
                let (upper, lower) = if index % 2 == 0 {
                    (wide, Rat::zero())
                } else {
                    (Rat::zero(), wide)
                };
                ExactRatMatrix::shaped(2, 2, vec![vec![Rat::one(), upper], vec![lower, Rat::one()]])
                    .unwrap()
            })
            .collect();
        assert_ne!(
            maps[0].multiply(&maps[1]).unwrap(),
            maps[1].multiply(&maps[0]).unwrap()
        );
        let mut serial = identity.clone();
        let expected: Vec<_> = maps
            .iter()
            .map(|map| {
                serial = map.multiply(&serial).unwrap();
                serial.clone()
            })
            .collect();
        for partitions in [1, 2, 7, 64] {
            assert_eq!(
                ordered_prefixes(&maps, &identity, partitions, |earlier, later| {
                    later.multiply(earlier)
                })
                .unwrap(),
                expected
            );
            assert_eq!(
                ordered_reduce(&maps, &identity, partitions, |earlier, later| {
                    later.multiply(earlier)
                })
                .unwrap(),
                serial
            );
        }
        let empty: &[ExactRatMatrix] = &[];
        assert_eq!(
            ordered_reduce(empty, &identity, 7, |earlier, later| later
                .multiply(earlier))
            .unwrap(),
            identity
        );
        assert!(
            ordered_prefixes(empty, &identity, 64, |earlier, later| later
                .multiply(earlier))
            .unwrap()
            .is_empty()
        );
        assert_eq!(
            ordered_reduce(&maps, &identity, 0, |earlier, later| later
                .multiply(earlier)),
            Err(OrderedScanError::ZeroPartitions)
        );
        assert_eq!(
            ordered_prefixes(
                &[ExactRatMatrix::identity(3).unwrap()],
                &identity,
                2,
                |earlier, later| later.multiply(earlier)
            ),
            Err(OrderedScanError::Composition(
                ExactLinearError::ShapeMismatch
            ))
        );
    }

    /// This is the declared receiving bank used by the executed-growth controls: its maps
    /// come from the actual pump placement, signed-form check and exact resonator solve.
    fn bank() -> ReceivingBank {
        let identity = ExactRatMatrix::identity(2).unwrap();
        let material = ResonatorMaterial::new(
            identity.clone(),
            identity,
            ExactRatMatrix::zero(2, 2).unwrap(),
            None,
        )
        .unwrap();
        let members = [
            PumpStep::Stand,
            PumpStep::Quarter,
            PumpStep::Half,
            PumpStep::ThreeQuarters,
        ]
        .into_iter()
        .map(|step| {
            PumpDeclaration::new(
                rat(5, 8),
                Carrier::new(Rat::one(), Rat::zero()).unwrap(),
                step,
            )
            .unwrap()
        })
        .collect();
        ReceivingBank::new(material, members, integer(16), Rat::one(), 6).unwrap()
    }

    #[test]
    fn exact_transport_scan_matches_executed_bank_and_reverse_variation() {
        let bank = bank();
        let amplitudes: Vec<_> = (0..8)
            .map(|tick| GaussianRat::new(rat(tick - 3, 16), rat(2 - tick, 32)))
            .collect();
        let direction: Vec<_> = (0..8)
            .map(|tick| GaussianRat::new(rat(2 * tick - 5, 32), rat(3 - tick, 16)))
            .collect();
        for member in 0..4 {
            let (maps, numerator, denominator) = bank
                .turn_monodromy_partitioned(member, &amplitudes, 1)
                .unwrap();
            let identity = ExactRatMatrix::identity(4).unwrap();
            let serial = maps.iter().fold(identity.clone(), |product, map| {
                map.multiply(&product).unwrap()
            });
            let integral_reading = ExactRatMatrix::shaped(
                4,
                4,
                numerator
                    .iter()
                    .map(|row| {
                        row.iter()
                            .map(|entry| Rat::new(entry.clone(), denominator.clone()))
                            .collect()
                    })
                    .collect(),
            )
            .unwrap();
            assert_eq!(integral_reading, serial);
            let variation = bank
                .turn_variation_partitioned(member, &amplitudes, &direction, 1)
                .unwrap();
            assert_eq!(variation.monodromy, serial);
            assert_eq!(variation.forward, variation.reverse);
            for partitions in [1, 2, 7, 64] {
                let (other_maps, other_numerator, other_denominator) = bank
                    .turn_monodromy_partitioned(member, &amplitudes, partitions)
                    .unwrap();
                assert_eq!(other_maps, maps);
                assert_eq!(other_numerator, numerator);
                assert_eq!(other_denominator, denominator);
                assert_eq!(
                    bank.turn_variation_partitioned(member, &amplitudes, &direction, partitions,)
                        .unwrap(),
                    variation
                );
            }
        }
        assert!(matches!(
            bank.turn_monodromy_partitioned(0, &amplitudes, 0),
            Err(HnnError::Unadmitted { .. })
        ));
        assert!(matches!(
            bank.turn_variation_partitioned(0, &amplitudes, &direction[..7], 2),
            Err(HnnError::Unadmitted { .. })
        ));
    }
}
