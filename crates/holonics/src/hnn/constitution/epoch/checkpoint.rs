//! Versioned, exact continuation words for one `EpochLaw`.
//!
//! This is a law-component checkpoint only. It has no filesystem behavior and does
//! not claim to snapshot the listener, its clock, or any surrounding medium.

use super::{CheckpointReadBudget, EpochArray, EpochLaw, EpochSpectral, ceil_log2_count, refused};
use crate::hnn::HnnError;
use crate::hnn::paired::PortSymmetry;
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

const HEADER: &str = "epoch-law-checkpoint-v3";

impl EpochLaw {
    /// Write this law's exact, canonical continuation words.
    pub(crate) fn encode_checkpoint(&self) -> String {
        let mut text = String::new();
        text.push_str(if self.receiving_refinement.is_some() {"epoch-law-receiving-refinement-v1"} else {HEADER});
        text.push('\n');
        text.push_str(&format!("shape {} {}\n", self.map.rows, self.map.columns));
        text.push_str(&format!(
            "clock {} {} {}\n",
            self.receiver_grain, self.map_lattice, self.crossings
        ));
        text.push_str(&format!(
            "source-refinement {}\n",
            u8::from(self.source_refinement)
        ));
        if let Some(cap) = self.receiving_refinement { text.push_str(&format!("receiving-refinement {cap}\n")); }
        write_array(&mut text, "map", &self.map);
        write_array(&mut text, "gram", &self.gram);
        write_array(&mut text, "news", &self.news);
        let (rows, columns, gram_bound, move_bound) = self.spectral.checkpoint_words();
        text.push_str(&format!(
            "spectral {rows} {columns} {gram_bound} {move_bound}\n"
        ));
        write_symmetry(&mut text, self.symmetry.as_ref());
        text
    }

    /// Decode onto a law declaration. Only its stable shape, receiver metric,
    /// lattice, and paired-family declaration are used as the admission context.
    /// No older or unversioned law format is migrated.
    #[cfg(test)]
    pub(crate) fn decode_checkpoint(
        text: &str,
        declaration: &EpochLaw,
        budget: u64,
    ) -> Result<Self, HnnError> {
        let candidate =
            Self::decode_checkpoint_unbound(text, &mut CheckpointReadBudget::new(budget))?;
        validate(&candidate, declaration)?;
        Ok(candidate)
    }

    /// Structural decode for the enclosing native checkpoint parser, which then
    /// binds the field's receiving row declaration before admitting the resident.
    pub(in crate::hnn::constitution) fn decode_checkpoint_unbound(
        text: &str,
        budget: &mut CheckpointReadBudget,
    ) -> Result<Self, HnnError> {
        let mut lines = text.lines();
        let header = take(&mut lines)?;
        if header != HEADER && header != "epoch-law-receiving-refinement-v1" {
            return Err(malformed());
        }
        let shape = words(take(&mut lines)?, "shape", 2)?;
        let rows = parse_usize(&shape[0])?;
        let columns = parse_usize(&shape[1])?;
        let clock = words(take(&mut lines)?, "clock", 3)?;
        let receiver_grain = parse_u32(&clock[0])?;
        let map_lattice = parse_u32(&clock[1])?;
        budget.check(u64::from(map_lattice))?;
        let crossings = parse_u64(&clock[2])?;
        let policy = words(take(&mut lines)?, "source-refinement", 1)?;
        let source_refinement = match policy[0] {
            "0" => false,
            "1" => true,
            _ => return Err(malformed()),
        };
        let receiving_refinement = if header == "epoch-law-receiving-refinement-v1" {
            let cap = parse_u32(words(take(&mut lines)?,"receiving-refinement",1)?[0])?;
            if cap != super::ReceivingRepresentationPolicy::CEILING || source_refinement { return Err(malformed()); }
            Some(cap)
        } else {None};
        let map = read_array(&mut lines, "map", budget)?;
        let gram = read_array(&mut lines, "gram", budget)?;
        let news = read_array(&mut lines, "news", budget)?;
        if (rows, columns) != (map.rows, map.columns) {
            return Err(refused(
                "an epoch checkpoint's header must match its map shape",
            ));
        }
        let spectral = words(take(&mut lines)?, "spectral", 4)?;
        let spectral_rows = parse_usize(&spectral[0])?;
        let spectral_columns = parse_usize(&spectral[1])?;
        let gram_bound = parse_rat(&spectral[2], budget)?;
        let move_bound = parse_rat(&spectral[3], budget)?;
        let symmetry = read_symmetry(&mut lines)?;
        if lines.next().is_some() {
            return Err(malformed());
        }

        let spectral = EpochSpectral::from_checkpoint(
            spectral_rows,
            spectral_columns,
            gram_bound,
            move_bound,
            &map,
        )?;
        let candidate = Self {
            map,
            gram,
            news,
            receiver_grain,
            map_lattice,
            source_refinement,
            receiving_refinement,
            crossings,
            spectral,
            symmetry,
        };
        validate(&candidate, &candidate)?;
        // This rejects alternate whitespace, missing final newline, noncanonical scalar
        // spellings, and any parser form that is not the unique encoder output.
        if candidate.encode_checkpoint() != text {
            return Err(malformed());
        }
        Ok(candidate)
    }
}

pub(super) fn validate(law: &EpochLaw, declaration: &EpochLaw) -> Result<(), HnnError> {
    validate_with_row_binding(law, declaration, true)
}

/// The enclosing native restore knows the receiving law's founding declaration
/// before it has the field. Only its receiving row factors wait for field
/// admission; all shape, metric, lattice and paired-family checks apply now.
pub(super) fn validate_receiving_before_field(
    law: &EpochLaw,
    declaration: &EpochLaw,
) -> Result<(), HnnError> {
    validate_with_row_binding(law, declaration, false)
}

fn validate_with_row_binding(
    law: &EpochLaw,
    declaration: &EpochLaw,
    bind_rows: bool,
) -> Result<(), HnnError> {
    let (rows, columns) = (law.map.rows, law.map.columns);
    if rows == 0
        || columns == 0
        || (rows, columns) != (declaration.map.rows, declaration.map.columns)
        || (
            law.receiver_grain,
            law.source_refinement,
            law.receiving_refinement,
            law.symmetry.as_ref(),
        ) != (
            declaration.receiver_grain,
            declaration.source_refinement,
            declaration.receiving_refinement,
            declaration.symmetry.as_ref(),
        )
    {
        return Err(refused(
            "an epoch checkpoint must match its declared shape, metric, lattice, and paired family",
        ));
    }
    let expected_lattice = law
        .receiver_grain
        .checked_add(ceil_log2_count(
            u64::try_from(columns).map_err(|_| malformed())?,
        ))
        .ok_or_else(malformed)?;
    if (bind_rows && law.news.row_divisors != declaration.news.row_divisors)
        || !law.map.is_dyadic()
        || !law.gram.is_dyadic()
    {
        return Err(refused(
            "an epoch checkpoint must preserve its declared dyadic map/Gram and receiving phase rows",
        ));
    }
    if (if law.source_refinement {
        law.map_lattice < expected_lattice || !law.news.is_dyadic()
    } else if let Some(cap) = law.receiving_refinement {
        cap != super::ReceivingRepresentationPolicy::CEILING || law.map_lattice < expected_lattice || law.map_lattice > cap
    } else {
        law.map_lattice != expected_lattice
    }) || law.map.exponent > law.map_lattice
        || (law.map.rows, law.map.columns) != (rows, columns)
        || (law.news.rows, law.news.columns) != (rows, columns)
        || (law.gram.rows, law.gram.columns) != (columns, columns)
    {
        return Err(refused(
            "an epoch checkpoint's arrays must meet its receiver lattice and normal-locus shape",
        ));
    }
    let mut gram = vec![vec![BigInt::zero(); columns]; columns];
    for i in 0..columns {
        for j in 0..columns {
            let value = &law.gram.values[i * columns + j];
            if value != &law.gram.values[j * columns + i] {
                return Err(refused("an epoch checkpoint's metric must be symmetric"));
            }
            gram[i][j] = value.clone();
        }
    }
    if !positive_definite_integer(gram) {
        return Err(refused(
            "an epoch checkpoint's metric must be positive definite",
        ));
    }
    if let Some(symmetry) = &law.symmetry {
        if symmetry.rows().len() != rows || symmetry.columns().len() != columns {
            return Err(refused(
                "an epoch checkpoint's paired family must fit its map",
            ));
        }
        for i in 0..rows {
            for j in 0..columns {
                if let Some(partner) = symmetry.columns()[j]
                    && (law.map.values[i * columns + partner]
                        != law.map.values[symmetry.rows()[i] * columns + j]
                        || law.news.values[i * columns + partner]
                            != law.news.values[symmetry.rows()[i] * columns + j])
                {
                    return Err(refused(
                        "an epoch checkpoint's map and news must preserve paired symmetry",
                    ));
                }
            }
        }
        for i in 0..columns {
            for j in 0..columns {
                if law.gram.values[i * columns + j]
                    != law.gram.values[symmetry.column(i) * columns + symmetry.column(j)]
                {
                    return Err(refused(
                        "an epoch checkpoint's metric must preserve paired symmetry",
                    ));
                }
            }
        }
        let outside: Vec<usize> = (0..columns)
            .filter(|&column| symmetry.columns()[column].is_none())
            .collect();
        for &outside_column in &outside {
            if (0..rows).any(|row| {
                !law.map.values[row * columns + outside_column].is_zero()
                    || !law.news.values[row * columns + outside_column].is_zero()
            }) {
                return Err(refused(
                    "an epoch checkpoint's outside-family map and news must remain founded zero",
                ));
            }
            for column in 0..columns {
                if symmetry.columns()[column].is_some()
                    && (!law.gram.values[outside_column * columns + column].is_zero()
                        || !law.gram.values[column * columns + outside_column].is_zero())
                {
                    return Err(refused(
                        "an epoch checkpoint's metric must not couple its outside family",
                    ));
                }
            }
            for &other_outside in &outside {
                if !same_dyadic_coordinate(
                    &law.gram,
                    &declaration.gram,
                    outside_column * columns + other_outside,
                ) {
                    return Err(refused(
                        "an epoch checkpoint's inactive outside metric block must keep its founded prior",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn same_dyadic_coordinate(left: &EpochArray, right: &EpochArray, index: usize) -> bool {
    let exponent = left.exponent.max(right.exponent);
    (&left.values[index] << (exponent - left.exponent) as usize)
        == (&right.values[index] << (exponent - right.exponent) as usize)
}

/// Sylvester's criterion with fraction-free Bareiss elimination. The Gram's shared
/// denominator is positive, so its integer numerator has the same definiteness.
fn positive_definite_integer(mut matrix: Vec<Vec<BigInt>>) -> bool {
    let mut previous = BigInt::one();
    for pivot_index in 0..matrix.len() {
        let pivot = matrix[pivot_index][pivot_index].clone();
        if pivot <= BigInt::zero() {
            return false;
        }
        for i in pivot_index + 1..matrix.len() {
            for j in pivot_index + 1..matrix.len() {
                let mut numerator =
                    &matrix[i][j] * &pivot - &matrix[i][pivot_index] * &matrix[pivot_index][j];
                if pivot_index > 0 {
                    let remainder = &numerator % &previous;
                    if !remainder.is_zero() {
                        return false;
                    }
                    numerator /= &previous;
                }
                matrix[i][j] = numerator;
            }
        }
        previous = pivot;
    }
    true
}

fn write_array(text: &mut String, name: &str, array: &EpochArray) {
    text.push_str(&format!(
        "{name} {} {} {}\n",
        array.rows, array.columns, array.exponent
    ));
    write_values(
        text,
        &array
            .row_divisors
            .iter()
            .copied()
            .map(BigInt::from)
            .collect::<Vec<_>>(),
    );
    write_values(text, &array.values);
}

fn write_values(text: &mut String, values: &[BigInt]) {
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            text.push(' ');
        }
        text.push_str(&value.to_string());
    }
    text.push('\n');
}

fn read_array(
    lines: &mut std::str::Lines<'_>,
    name: &str,
    budget: &mut CheckpointReadBudget,
) -> Result<EpochArray, HnnError> {
    let header = words(take(lines)?, name, 3)?;
    let rows = parse_usize(&header[0])?;
    let columns = parse_usize(&header[1])?;
    let exponent = parse_u32(&header[2])?;
    let count = rows.checked_mul(columns).ok_or_else(malformed)?;
    let mut payload = u64::from(exponent)
        .checked_add(1)
        .ok_or_else(malformed)?
        .checked_add(u64::try_from(count).map_err(|_| malformed())?)
        .and_then(|n| n.checked_add(u64::try_from(rows).ok()?))
        .ok_or_else(malformed)?;
    budget.check(payload)?;
    let row_divisors = token_line(take(lines)?, rows)?
        .iter()
        .map(|word| parse_u64(word))
        .collect::<Result<Vec<_>, _>>()?;
    for divisor in &row_divisors {
        payload = payload
            .checked_add(u64::from(u64::BITS - divisor.leading_zeros()).saturating_sub(1))
            .ok_or_else(malformed)?;
    }
    budget.check(payload)?;
    let encoded_values = take(lines)?;
    let mut values = Vec::new();
    for word in encoded_values.split_whitespace() {
        // Four bits per decimal character bounds the parser's temporary integer too. The
        // exact bit count is charged below, so this is an allocation preflight, not rounding.
        let temporary = u64::try_from(word.len())
            .map_err(|_| malformed())?
            .checked_mul(4)
            .and_then(|n| n.checked_add(payload))
            .ok_or_else(malformed)?;
        budget.check(temporary)?;
        let value = word.parse::<BigInt>().map_err(|_| malformed())?;
        if value.to_string() != word {
            return Err(malformed());
        }
        payload = payload.checked_add(value.bits()).ok_or_else(malformed)?;
        budget.check(payload)?;
        values.push(value);
    }
    if values.len() != count {
        return Err(malformed());
    }
    // Canonicality is decided from numerator bits, before 2^exponent exists. In particular an
    // all-zero or reducible array cannot use a giant encoded denominator and cancel it later.
    if exponent != 0
        && values
            .iter()
            .filter(|v| !v.is_zero())
            .map(|v| v.trailing_zeros().unwrap_or(0))
            .min()
            .is_none_or(|zeros| zeros > 0)
    {
        return Err(refused(
            "an epoch checkpoint array must use canonical shared dyadics",
        ));
    }
    budget.charge(payload)?;
    // Canonicality was checked above; move the numerator family rather than retaining a
    // duplicate allocation merely to compare it after the constructor's power-of-two cancel.
    let array = EpochArray::with_row_divisors(rows, columns, exponent, values, row_divisors)?;
    if array.exponent != exponent || array.values.len() != count {
        return Err(refused(
            "an epoch checkpoint array must use canonical shared dyadics",
        ));
    }
    Ok(array)
}

fn write_symmetry(text: &mut String, symmetry: Option<&PortSymmetry>) {
    let Some(symmetry) = symmetry else {
        text.push_str("symmetry none\n");
        return;
    };
    text.push_str(&format!(
        "symmetry {} {} {}\n",
        symmetry.rows().len(),
        symmetry.columns().len(),
        symmetry.pairs().len()
    ));
    write_values(
        text,
        &symmetry
            .rows()
            .iter()
            .map(|&x| BigInt::from(x))
            .collect::<Vec<_>>(),
    );
    for (index, column) in symmetry.columns().iter().enumerate() {
        if index != 0 {
            text.push(' ');
        }
        match column {
            Some(value) => text.push_str(&value.to_string()),
            None => text.push('-'),
        }
    }
    text.push('\n');
    let leaders: Vec<BigInt> = symmetry
        .pairs()
        .iter()
        .map(|(leader, _)| BigInt::from(*leader))
        .collect();
    write_values(text, &leaders);
}

fn read_symmetry(lines: &mut std::str::Lines<'_>) -> Result<Option<PortSymmetry>, HnnError> {
    let header = take(lines)?;
    if header == "symmetry none" {
        return Ok(None);
    }
    let dimensions = words(header, "symmetry", 3)?;
    let rows = parse_usize(&dimensions[0])?;
    let columns = parse_usize(&dimensions[1])?;
    let pairs = parse_usize(&dimensions[2])?;
    let row_words = token_line(take(lines)?, rows)?;
    let row_indices = row_words
        .iter()
        .map(|word| parse_usize(word))
        .collect::<Result<Vec<_>, _>>()?;
    let column_words = token_line(take(lines)?, columns)?;
    let partners = column_words
        .iter()
        .map(|word| {
            if *word == "-" {
                Ok(None)
            } else {
                parse_usize(word).map(Some)
            }
        })
        .collect::<Result<Vec<_>, HnnError>>()?;
    let leaders = token_line(take(lines)?, pairs)?
        .iter()
        .map(|word| parse_usize(word))
        .collect::<Result<Vec<_>, _>>()?;
    let symmetry = PortSymmetry::from_parts(row_indices, partners, &leaders)
        .ok_or_else(|| refused("an epoch checkpoint has an unlawful paired family"))?;
    if symmetry.pairs().len() != pairs {
        return Err(malformed());
    }
    Ok(Some(symmetry))
}

fn token_line(line: &str, count: usize) -> Result<Vec<&str>, HnnError> {
    let words: Vec<_> = line.split_whitespace().collect();
    if words.len() != count {
        return Err(malformed());
    }
    Ok(words)
}

fn words<'a>(line: &'a str, name: &str, count: usize) -> Result<Vec<&'a str>, HnnError> {
    let mut parts = line.split_whitespace();
    if parts.next() != Some(name) {
        return Err(malformed());
    }
    let output: Vec<_> = parts.collect();
    if output.len() != count {
        return Err(malformed());
    }
    Ok(output)
}

fn take<'a>(lines: &mut std::str::Lines<'a>) -> Result<&'a str, HnnError> {
    lines.next().ok_or_else(malformed)
}

fn parse_usize(word: &str) -> Result<usize, HnnError> {
    canonical_number(word)
}

fn parse_u32(word: &str) -> Result<u32, HnnError> {
    canonical_number(word)
}

fn parse_u64(word: &str) -> Result<u64, HnnError> {
    canonical_number(word)
}

fn canonical_number<T>(word: &str) -> Result<T, HnnError>
where
    T: std::str::FromStr + ToString,
{
    let number = word.parse::<T>().map_err(|_| malformed())?;
    if number.to_string() != word {
        return Err(malformed());
    }
    Ok(number)
}

fn parse_rat(word: &str, budget: &mut CheckpointReadBudget) -> Result<Rat, HnnError> {
    budget.check(
        u64::try_from(word.len())
            .map_err(|_| malformed())?
            .checked_mul(4)
            .ok_or_else(malformed)?,
    )?;
    let value = word.parse::<Rat>().map_err(|_| malformed())?;
    if value.is_negative() || value.to_string() != word {
        return Err(refused(
            "an epoch spectral checkpoint has canonical nonnegative scalars",
        ));
    }
    budget.charge(
        value
            .numer()
            .bits()
            .checked_add(value.denom().bits())
            .ok_or_else(malformed)?,
    )?;
    Ok(value)
}

fn malformed() -> HnnError {
    HnnError::ContinuingState {
        what: "an epoch-law checkpoint",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checkpoint_read_budget_refuses_encoded_exponent_before_materialization() {
        let declared = EpochLaw::founded(2, 2, 6, 0).unwrap();
        let text = declared
            .encode_checkpoint()
            .replace("map 2 2 0\n", "map 2 2 4294967295\n");
        // Only the encoded integer is large: no corresponding BigInt is constructed by this
        // fixture or the reader. The declared read budget refuses it at the raw array head.
        let mut budget = CheckpointReadBudget::new(128);
        assert!(matches!(
            EpochLaw::decode_checkpoint_unbound(&text, &mut budget),
            Err(HnnError::ConstitutionBudget { budget: 128, .. })
        ));
        assert_eq!(budget.used, 0);
    }

    #[test]
    fn checkpoint_read_rejects_noncanonical_zero_before_charging_a_denominator() {
        let mut budget = CheckpointReadBudget::new(1 << 20);
        assert!(read_array(&mut "map 1 1 4096\n1\n0\n".lines(), "map", &mut budget).is_err());
        assert_eq!(budget.used, 0);
        assert!(read_array(&mut "map 1 1 4096\n1\n2\n".lines(), "map", &mut budget).is_err());
        assert_eq!(budget.used, 0);
    }

    #[test]
    fn checkpoint_read_budget_also_bounds_the_derived_dense_map_view() {
        let map = EpochArray::new(2, 2, 20, vec![1.into(), 3.into(), 5.into(), 7.into()]).unwrap();
        let mut narrow = CheckpointReadBudget::new(64);
        assert!(matches!(
            narrow.admit_map_view(&map),
            Err(HnnError::ConstitutionBudget { .. })
        ));
        let mut admitted = CheckpointReadBudget::new(256);
        admitted.admit_map_view(&map).unwrap();
        assert_eq!(map.to_matrix().unwrap().rows(), 2);
    }
    use num_traits::Signed;

    fn array(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
        EpochArray::new(
            rows,
            columns,
            exponent,
            values.iter().copied().map(BigInt::from).collect(),
        )
        .unwrap()
    }

    fn sample_flow(epoch: u64) -> super::super::EpochFlow {
        let sample = super::super::EpochSample {
            feature: array(1, 2, 1, &[2, 1]),
            positive: array(2, 1, 0, &[1, 0]),
            foil: super::super::EpochSeries {
                rows: 2,
                columns: 1,
                numerators: vec![BigInt::from(2), BigInt::from(3)],
                denominator: BigInt::from(5),
            },
            metric_weight: super::super::EpochSeries {
                rows: 1,
                columns: 1,
                numerators: vec![BigInt::one()],
                denominator: BigInt::from(3),
            },
        };
        super::super::EpochFlow::from_samples(2, 2, 32, 231, epoch, &[sample]).unwrap()
    }

    fn take_step(law: &EpochLaw, flow: &super::super::EpochFlow) -> EpochLaw {
        let deposit = law.deposit(flow, &array(1, 1, 0, &[1])).unwrap();
        assert!(!deposit.step.is_zero());
        deposit.successor
    }

    #[test]
    fn roundtrip_preserves_spectral_drift_and_the_next_crossing() {
        let declaration = EpochLaw::founded(2, 2, 32, 0).unwrap();
        let first = take_step(&declaration, &sample_flow(0));
        let (_, _, gram_bound, move_bound) = first.spectral.checkpoint_words();
        assert!(gram_bound.is_zero());
        assert!(move_bound.is_positive());

        let text = first.encode_checkpoint();
        let resumed = EpochLaw::decode_checkpoint(&text, &declaration, 1 << 20).unwrap();
        assert_eq!(resumed, first);

        let uninterrupted = take_step(&first, &sample_flow(1));
        let continued = take_step(&resumed, &sample_flow(1));
        assert_eq!(continued, uninterrupted);
        assert_eq!(
            continued.encode_checkpoint(),
            uninterrupted.encode_checkpoint()
        );
    }

    #[test]
    fn large_limbs_and_paired_partial_family_roundtrip_whole() {
        let declaration = EpochLaw::founded(2, 2, 32, 0).unwrap();
        let mut large = declaration.clone();
        let limb = BigInt::one() << 1024usize;
        large.map = EpochArray::new(
            2,
            2,
            0,
            vec![limb.clone(), BigInt::zero(), BigInt::zero(), BigInt::zero()],
        )
        .unwrap();
        large.news = EpochArray::new(
            2,
            2,
            0,
            vec![
                -limb.clone(),
                BigInt::zero(),
                BigInt::zero(),
                BigInt::zero(),
            ],
        )
        .unwrap();
        large.spectral.refresh(&large.map).unwrap();
        let text = large.encode_checkpoint();
        assert_eq!(
            EpochLaw::decode_checkpoint(&text, &declaration, 1 << 20).unwrap(),
            large
        );

        let symmetry =
            PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0), None], &[0]).unwrap();
        let paired = EpochLaw::founded_paired(2, 3, 32, 1, symmetry).unwrap();
        let paired_text = paired.encode_checkpoint();
        assert_eq!(
            EpochLaw::decode_checkpoint(&paired_text, &paired, 1 << 20).unwrap(),
            paired
        );
    }

    #[test]
    fn parser_refuses_truncation_noncanonical_words_and_metadata_mismatches() {
        let declaration = EpochLaw::founded(2, 2, 32, 0).unwrap();
        let text = declaration.encode_checkpoint();
        assert!(
            EpochLaw::decode_checkpoint(&text[..text.len() - 1], &declaration, 1 << 20).is_err()
        );
        assert!(EpochLaw::decode_checkpoint("epoch-law-v0\n", &declaration, 1 << 20).is_err());
        assert!(
            EpochLaw::decode_checkpoint(
                &text.replace("shape 2 2", "shape 02 2"),
                &declaration,
                1 << 20
            )
            .is_err()
        );
        assert!(
            EpochLaw::decode_checkpoint(
                &text.replace("clock 32 33 0", "clock 31 33 0"),
                &declaration,
                1 << 20
            )
            .is_err()
        );
        assert!(
            EpochLaw::decode_checkpoint(
                &text.replace("clock 32 33 0", "clock 32 34 0"),
                &declaration,
                1 << 20
            )
            .is_err()
        );
        assert!(
            EpochLaw::decode_checkpoint(
                &text.replace("gram 2 2 0", "gram 2 3 0"),
                &declaration,
                1 << 20
            )
            .is_err()
        );
        let foreign_metric = EpochLaw::founded(2, 2, 31, 0).unwrap();
        assert!(EpochLaw::decode_checkpoint(&text, &foreign_metric, 1 << 20).is_err());
        let foreign_shape = EpochLaw::founded(1, 2, 32, 0).unwrap();
        assert!(EpochLaw::decode_checkpoint(&text, &foreign_shape, 1 << 20).is_err());

        let mut off_lattice = declaration.clone();
        off_lattice.map = array(2, 2, 100, &[1, 0, 0, 0]);
        off_lattice.spectral.refresh(&off_lattice.map).unwrap();
        assert!(
            EpochLaw::decode_checkpoint(&off_lattice.encode_checkpoint(), &declaration, 1 << 20)
                .is_err()
        );
    }

    #[test]
    fn partial_family_checkpoint_keeps_outside_map_news_and_metric_at_foundation() {
        let symmetry =
            PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0), None], &[0]).unwrap();
        let paired = EpochLaw::founded_paired(2, 3, 32, 1, symmetry).unwrap();

        let mut outside_map = paired.clone();
        outside_map.map = array(2, 3, 0, &[0, 0, 1, 0, 0, 0]);
        outside_map.spectral.refresh(&outside_map.map).unwrap();
        assert!(
            EpochLaw::decode_checkpoint(&outside_map.encode_checkpoint(), &paired, 1 << 20)
                .is_err()
        );

        let mut outside_news = paired.clone();
        outside_news.news = array(2, 3, 0, &[0, 0, 1, 0, 0, 0]);
        assert!(
            EpochLaw::decode_checkpoint(&outside_news.encode_checkpoint(), &paired, 1 << 20)
                .is_err()
        );

        let mut coupled_metric = paired.clone();
        coupled_metric.gram = array(3, 3, 0, &[2, 0, 1, 0, 2, 1, 1, 1, 2]);
        assert!(
            EpochLaw::decode_checkpoint(&coupled_metric.encode_checkpoint(), &paired, 1 << 20)
                .is_err()
        );

        let mut changed_outside_prior = paired.clone();
        changed_outside_prior.gram = array(3, 3, 0, &[2, 0, 0, 0, 2, 0, 0, 0, 4]);
        assert!(
            EpochLaw::decode_checkpoint(
                &changed_outside_prior.encode_checkpoint(),
                &paired,
                1 << 20
            )
            .is_err()
        );
    }
}
