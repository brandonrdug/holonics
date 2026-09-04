use std::env;
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;

use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, Serialize)]
struct PrimePowerRead {
    prime: u64,
    exponent: u32,
}

#[derive(Clone, Debug, Serialize)]
struct DigitContributionRead {
    position: u32,
    digit: u64,
    place_weight_mod_q: u64,
    contribution_mod_q: u64,
}

#[derive(Clone, Debug, Serialize)]
struct RadixMemberRead {
    value: u64,
    digits_least_significant_first: Vec<u64>,
}

#[derive(Clone, Debug, Serialize)]
struct ResidueFiberRead<T> {
    residue: u64,
    count: u64,
    members: Vec<T>,
}

#[derive(Clone, Debug, Serialize)]
struct CharacterCoordinateRead {
    character: u64,
    root_order: u64,
    exponent_coefficients: Vec<u64>,
    cyclotomic_basis_coefficients: Vec<i64>,
}

#[derive(Clone, Debug, Serialize)]
struct CellAcceptanceRead {
    every_word_reconstructs_its_integer: bool,
    every_place_word_reconstructs_its_residue: bool,
    complete_fibers_partition_the_digit_box: bool,
    group_algebra_coefficients_equal_fiber_sizes: bool,
    crt_local_projection_vanishes_after_cutoff: bool,
    crt_coprime_projection_has_declared_period: bool,
    character_inverse_is_licensed_by_exact_orthogonality: bool,
}

#[derive(Clone, Debug, Serialize)]
struct RadixResidueCellRead {
    name: &'static str,
    radix: u64,
    modulus: u64,
    digit_depth: u32,
    total_occurrences: u64,
    q_local: u64,
    q_cyclic: u64,
    local_cutoff: u32,
    cyclic_order: Option<u64>,
    place_weights_mod_q: Vec<u64>,
    phase_class_by_position: Vec<Option<u64>>,
    residue_coefficients: Vec<u64>,
    fibers: Vec<ResidueFiberRead<RadixMemberRead>>,
    character_coordinates: Vec<CharacterCoordinateRead>,
    inverse_character_normalization: String,
    character_orthogonality_matrix: Vec<Vec<u64>>,
    acceptance: CellAcceptanceRead,
}

#[derive(Clone, Debug, Serialize)]
struct SharedOccurrenceRead {
    value: u64,
    residue_mod_5: u64,
    decimal_digits_least_significant_first: Vec<u64>,
    ternary_digits_least_significant_first: Vec<u64>,
    decimal_place_contributions: Vec<DigitContributionRead>,
    ternary_place_contributions: Vec<DigitContributionRead>,
    prime_valuation: Option<Vec<PrimePowerRead>>,
    logarithmic_length: Option<String>,
    mellin_character: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
struct SharedAtlasAcceptanceRead {
    every_occurrence_reconstructs_in_both_radices: bool,
    every_occurrence_has_the_same_residue_in_both_radices: bool,
    complete_residue_fibers_are_identical_after_rechart: bool,
    every_positive_valuation_reconstructs_the_occurrence: bool,
}

#[derive(Clone, Debug, Serialize)]
struct SharedOccurrenceAtlasRead {
    occurrence_set: &'static str,
    receiver: &'static str,
    decimal_place_word: Vec<u64>,
    ternary_place_word: Vec<u64>,
    fibers: Vec<ResidueFiberRead<SharedOccurrenceRead>>,
    residue_coefficients: Vec<u64>,
    character_coordinates: Vec<CharacterCoordinateRead>,
    acceptance: SharedAtlasAcceptanceRead,
}

#[derive(Clone, Debug, Serialize)]
struct GlobalAcceptanceRead {
    decimal_mod_5_is_suffix_local: bool,
    ternary_mod_5_is_period_four_winding: bool,
    decimal_mod_11_is_period_two_alternation: bool,
    all_cells_close_exactly: bool,
    shared_occurrence_atlas_closes_exactly: bool,
    no_floating_point_or_transcendental_evaluation_entered: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    conventions: Vec<&'static str>,
    cells: Vec<RadixResidueCellRead>,
    shared_occurrence_atlas: SharedOccurrenceAtlasRead,
    acceptance: GlobalAcceptanceRead,
    report_sha256_without_digest: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let output = output_path()?;

    let cells = vec![
        build_cell("decimal_mod_5", 10, 5, 2)?,
        build_cell("ternary_mod_5", 3, 5, 4)?,
        build_cell("decimal_mod_11", 10, 11, 2)?,
    ];
    let shared_occurrence_atlas = build_shared_occurrence_atlas()?;

    let decimal_mod_5_is_suffix_local = cells[0].q_local == 5
        && cells[0].q_cyclic == 1
        && cells[0].local_cutoff == 1
        && cells[0].place_weights_mod_q == vec![1, 0];
    let ternary_mod_5_is_period_four_winding = cells[1].q_local == 1
        && cells[1].q_cyclic == 5
        && cells[1].cyclic_order == Some(4)
        && cells[1].place_weights_mod_q == vec![1, 3, 4, 2];
    let decimal_mod_11_is_period_two_alternation = cells[2].q_local == 1
        && cells[2].q_cyclic == 11
        && cells[2].cyclic_order == Some(2)
        && cells[2].place_weights_mod_q == vec![1, 10];
    let all_cells_close_exactly = cells.iter().all(cell_accepted);
    let shared_occurrence_atlas_closes_exactly = shared_atlas_accepted(&shared_occurrence_atlas);
    let accepted = decimal_mod_5_is_suffix_local
        && ternary_mod_5_is_period_four_winding
        && decimal_mod_11_is_period_two_alternation
        && all_cells_close_exactly
        && shared_occurrence_atlas_closes_exactly;

    let acceptance = GlobalAcceptanceRead {
        decimal_mod_5_is_suffix_local,
        ternary_mod_5_is_period_four_winding,
        decimal_mod_11_is_period_two_alternation,
        all_cells_close_exactly,
        shared_occurrence_atlas_closes_exactly,
        no_floating_point_or_transcendental_evaluation_entered: true,
    };
    let mut report = Report {
        schema: "soma.radix-residue-character-transport.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "How does radix presentation change locality and winding while exact residue, character, valuation, and Mellin faces remain related through the same occurrence?",
        conventions: vec![
            "digit words are least-significant-place first",
            "every residue fiber retains every bounded member",
            "finite characters are represented in an exact cyclotomic basis",
            "Mellin faces remain formal products and exponentials of prime-log words",
            "no complex root, logarithm, pi, or floating-point value is evaluated",
        ],
        cells,
        shared_occurrence_atlas,
        acceptance,
        report_sha256_without_digest: String::new(),
    };
    let undigested =
        serde_json::to_vec_pretty(&report).map_err(|error| format!("report encodes: {error}"))?;
    report.report_sha256_without_digest = sha256(&undigested);
    write_new_json(&output, &report)?;
    if !accepted {
        return Err("the exact basis-transport acceptance relation did not close".to_owned());
    }
    Ok(())
}

fn build_cell(
    name: &'static str,
    radix: u64,
    modulus: u64,
    digit_depth: u32,
) -> Result<RadixResidueCellRead, String> {
    if radix < 2 || modulus < 2 || digit_depth == 0 || !is_prime(modulus) {
        return Err(
            "the bounded cells require radix >= 2, prime modulus, and depth >= 1".to_owned(),
        );
    }
    let total_occurrences = checked_pow(radix, digit_depth)?;
    let q_local = local_factor(radix, modulus);
    let q_cyclic = modulus / q_local;
    let local_cutoff = local_cutoff(radix, q_local)?;
    let cyclic_order = (q_cyclic > 1)
        .then(|| multiplicative_order(radix % q_cyclic, q_cyclic))
        .transpose()?;
    let place_weights_mod_q = (0..digit_depth)
        .map(|position| pow_mod(radix, u64::from(position), modulus))
        .collect::<Vec<_>>();
    let phase_class_by_position = (0..digit_depth)
        .map(|position| cyclic_order.map(|order| u64::from(position) % order))
        .collect::<Vec<_>>();

    let mut fibers = (0..modulus)
        .map(|residue| ResidueFiberRead {
            residue,
            count: 0,
            members: Vec::new(),
        })
        .collect::<Vec<_>>();
    let mut every_word_reconstructs_its_integer = true;
    let mut every_place_word_reconstructs_its_residue = true;
    for value in 0..total_occurrences {
        let digits = digits_lsf(value, radix, digit_depth);
        every_word_reconstructs_its_integer &= reconstruct_from_digits(&digits, radix)? == value;
        let place_residue = residue_from_digits(&digits, &place_weights_mod_q, modulus);
        every_place_word_reconstructs_its_residue &= place_residue == value % modulus;
        let fiber = &mut fibers[usize_from_u64(value % modulus)?];
        fiber.count += 1;
        fiber.members.push(RadixMemberRead {
            value,
            digits_least_significant_first: digits,
        });
    }
    let residue_coefficients = fibers.iter().map(|fiber| fiber.count).collect::<Vec<_>>();
    let complete_fibers_partition_the_digit_box =
        residue_coefficients.iter().sum::<u64>() == total_occurrences;
    let group_algebra_coefficients_equal_fiber_sizes = fibers
        .iter()
        .enumerate()
        .all(|(residue, fiber)| residue_coefficients[residue] == fiber.members.len() as u64);
    let crt_local_projection_vanishes_after_cutoff = q_local == 1
        || (local_cutoff..(local_cutoff + digit_depth + 2))
            .all(|position| pow_mod(radix, u64::from(position), q_local) == 0);
    let crt_coprime_projection_has_declared_period = match cyclic_order {
        None => q_cyclic == 1,
        Some(order) => (0..(order * 2 + 2)).all(|position| {
            pow_mod(radix, position + order, q_cyclic) == pow_mod(radix, position, q_cyclic)
        }),
    };
    let character_coordinates = character_coordinates(&residue_coefficients, modulus)?;
    let character_orthogonality_matrix = character_orthogonality(modulus)?;
    let character_inverse_is_licensed_by_exact_orthogonality = character_orthogonality_matrix
        .iter()
        .enumerate()
        .all(|(row, entries)| {
            entries
                .iter()
                .enumerate()
                .all(|(column, value)| *value == if row == column { modulus } else { 0 })
        });

    Ok(RadixResidueCellRead {
        name,
        radix,
        modulus,
        digit_depth,
        total_occurrences,
        q_local,
        q_cyclic,
        local_cutoff,
        cyclic_order,
        place_weights_mod_q,
        phase_class_by_position,
        residue_coefficients,
        fibers,
        character_coordinates,
        inverse_character_normalization: format!("1/{modulus}"),
        character_orthogonality_matrix,
        acceptance: CellAcceptanceRead {
            every_word_reconstructs_its_integer,
            every_place_word_reconstructs_its_residue,
            complete_fibers_partition_the_digit_box,
            group_algebra_coefficients_equal_fiber_sizes,
            crt_local_projection_vanishes_after_cutoff,
            crt_coprime_projection_has_declared_period,
            character_inverse_is_licensed_by_exact_orthogonality,
        },
    })
}

fn build_shared_occurrence_atlas() -> Result<SharedOccurrenceAtlasRead, String> {
    const MODULUS: u64 = 5;
    const MAXIMUM: u64 = 80;
    const DECIMAL_DEPTH: u32 = 2;
    const TERNARY_DEPTH: u32 = 4;

    let decimal_place_word = (0..DECIMAL_DEPTH)
        .map(|position| pow_mod(10, u64::from(position), MODULUS))
        .collect::<Vec<_>>();
    let ternary_place_word = (0..TERNARY_DEPTH)
        .map(|position| pow_mod(3, u64::from(position), MODULUS))
        .collect::<Vec<_>>();
    let mut fibers = (0..MODULUS)
        .map(|residue| ResidueFiberRead {
            residue,
            count: 0,
            members: Vec::new(),
        })
        .collect::<Vec<_>>();
    let mut every_occurrence_reconstructs_in_both_radices = true;
    let mut every_occurrence_has_the_same_residue_in_both_radices = true;
    let mut every_positive_valuation_reconstructs_the_occurrence = true;

    for value in 0..=MAXIMUM {
        let decimal_digits = digits_lsf(value, 10, DECIMAL_DEPTH);
        let ternary_digits = digits_lsf(value, 3, TERNARY_DEPTH);
        every_occurrence_reconstructs_in_both_radices &=
            reconstruct_from_digits(&decimal_digits, 10)? == value
                && reconstruct_from_digits(&ternary_digits, 3)? == value;
        let decimal_residue = residue_from_digits(&decimal_digits, &decimal_place_word, MODULUS);
        let ternary_residue = residue_from_digits(&ternary_digits, &ternary_place_word, MODULUS);
        every_occurrence_has_the_same_residue_in_both_radices &=
            decimal_residue == ternary_residue && decimal_residue == value % MODULUS;

        let valuation = (value > 0).then(|| factor(value));
        if let Some(ref factors) = valuation {
            every_positive_valuation_reconstructs_the_occurrence &=
                reconstruct_from_valuation(factors)? == value;
        }
        let logarithmic_length = valuation.as_ref().map(formal_log_length);
        let mellin_character = valuation.as_ref().map(formal_mellin_character);
        let member = SharedOccurrenceRead {
            value,
            residue_mod_5: value % MODULUS,
            decimal_place_contributions: digit_contributions(
                &decimal_digits,
                &decimal_place_word,
                MODULUS,
            ),
            ternary_place_contributions: digit_contributions(
                &ternary_digits,
                &ternary_place_word,
                MODULUS,
            ),
            decimal_digits_least_significant_first: decimal_digits,
            ternary_digits_least_significant_first: ternary_digits,
            prime_valuation: valuation,
            logarithmic_length,
            mellin_character,
        };
        let fiber = &mut fibers[usize_from_u64(value % MODULUS)?];
        fiber.count += 1;
        fiber.members.push(member);
    }
    let residue_coefficients = fibers.iter().map(|fiber| fiber.count).collect::<Vec<_>>();
    let complete_residue_fibers_are_identical_after_rechart = fibers.iter().all(|fiber| {
        fiber.members.iter().all(|member| {
            residue_from_digits(
                &member.decimal_digits_least_significant_first,
                &decimal_place_word,
                MODULUS,
            ) == fiber.residue
                && residue_from_digits(
                    &member.ternary_digits_least_significant_first,
                    &ternary_place_word,
                    MODULUS,
                ) == fiber.residue
        })
    });

    Ok(SharedOccurrenceAtlasRead {
        occurrence_set: "integers 0 through 80 inclusive",
        receiver: "residue modulo 5",
        decimal_place_word,
        ternary_place_word,
        fibers,
        character_coordinates: character_coordinates(&residue_coefficients, MODULUS)?,
        residue_coefficients,
        acceptance: SharedAtlasAcceptanceRead {
            every_occurrence_reconstructs_in_both_radices,
            every_occurrence_has_the_same_residue_in_both_radices,
            complete_residue_fibers_are_identical_after_rechart,
            every_positive_valuation_reconstructs_the_occurrence,
        },
    })
}

fn character_coordinates(
    residue_coefficients: &[u64],
    modulus: u64,
) -> Result<Vec<CharacterCoordinateRead>, String> {
    if !is_prime(modulus) || residue_coefficients.len() != usize_from_u64(modulus)? {
        return Err(
            "character coordinates require one coefficient per residue and prime modulus"
                .to_owned(),
        );
    }
    let q = usize_from_u64(modulus)?;
    let mut coordinates = Vec::with_capacity(q);
    for character in 0..modulus {
        let mut exponent_coefficients = vec![0_u64; q];
        for (residue, coefficient) in residue_coefficients.iter().enumerate() {
            let exponent = (character * u64::try_from(residue).map_err(debug)?) % modulus;
            exponent_coefficients[usize_from_u64(exponent)?] += coefficient;
        }
        let final_coefficient = i64::try_from(exponent_coefficients[q - 1]).map_err(debug)?;
        let cyclotomic_basis_coefficients = exponent_coefficients[..q - 1]
            .iter()
            .map(|coefficient| {
                i64::try_from(*coefficient)
                    .map(|value| value - final_coefficient)
                    .map_err(debug)
            })
            .collect::<Result<Vec<_>, _>>()?;
        coordinates.push(CharacterCoordinateRead {
            character,
            root_order: modulus,
            exponent_coefficients,
            cyclotomic_basis_coefficients,
        });
    }
    Ok(coordinates)
}

fn character_orthogonality(modulus: u64) -> Result<Vec<Vec<u64>>, String> {
    let q = usize_from_u64(modulus)?;
    let mut matrix = Vec::with_capacity(q);
    for left in 0..modulus {
        let mut row = Vec::with_capacity(q);
        for right in 0..modulus {
            let difference = (left + modulus - right) % modulus;
            let mut exponent_coefficients = vec![0_i64; q];
            for character in 0..modulus {
                let exponent = (character * difference) % modulus;
                exponent_coefficients[usize_from_u64(exponent)?] += 1;
            }
            let final_coefficient = exponent_coefficients[q - 1];
            let reduced = exponent_coefficients[..q - 1]
                .iter()
                .map(|coefficient| coefficient - final_coefficient)
                .collect::<Vec<_>>();
            if reduced.iter().skip(1).any(|coefficient| *coefficient != 0) || reduced[0] < 0 {
                return Err(
                    "character orthogonality did not reduce to an integer scalar".to_owned(),
                );
            }
            row.push(u64::try_from(reduced[0]).map_err(debug)?);
        }
        matrix.push(row);
    }
    Ok(matrix)
}

fn digit_contributions(
    digits: &[u64],
    place_weights: &[u64],
    modulus: u64,
) -> Vec<DigitContributionRead> {
    digits
        .iter()
        .zip(place_weights)
        .enumerate()
        .map(|(position, (digit, weight))| DigitContributionRead {
            position: u32::try_from(position).unwrap_or(u32::MAX),
            digit: *digit,
            place_weight_mod_q: *weight,
            contribution_mod_q: (*digit * *weight) % modulus,
        })
        .collect()
}

fn digits_lsf(mut value: u64, radix: u64, depth: u32) -> Vec<u64> {
    (0..depth)
        .map(|_| {
            let digit = value % radix;
            value /= radix;
            digit
        })
        .collect()
}

fn reconstruct_from_digits(digits: &[u64], radix: u64) -> Result<u64, String> {
    let mut value = 0_u64;
    let mut place = 1_u64;
    for digit in digits {
        value = value
            .checked_add(digit.checked_mul(place).ok_or("digit product overflow")?)
            .ok_or("digit accumulation overflow")?;
        place = place.checked_mul(radix).ok_or("place overflow")?;
    }
    Ok(value)
}

fn residue_from_digits(digits: &[u64], place_weights: &[u64], modulus: u64) -> u64 {
    digits
        .iter()
        .zip(place_weights)
        .fold(0_u64, |residue, (digit, weight)| {
            (residue + (digit * weight) % modulus) % modulus
        })
}

fn local_factor(radix: u64, modulus: u64) -> u64 {
    factor(modulus)
        .into_iter()
        .filter(|factor| radix % factor.prime == 0)
        .fold(1_u64, |product, factor| {
            product * factor.prime.pow(factor.exponent)
        })
}

fn local_cutoff(radix: u64, q_local: u64) -> Result<u32, String> {
    if q_local == 1 {
        return Ok(0);
    }
    let radix_factors = factor(radix);
    let mut cutoff = 0_u32;
    for factor in factor(q_local) {
        let radix_exponent = radix_factors
            .iter()
            .find(|candidate| candidate.prime == factor.prime)
            .map(|candidate| candidate.exponent)
            .ok_or("local prime is absent from radix")?;
        cutoff = cutoff.max(factor.exponent.div_ceil(radix_exponent));
    }
    Ok(cutoff)
}

fn multiplicative_order(value: u64, modulus: u64) -> Result<u64, String> {
    if modulus <= 1 || gcd(value, modulus) != 1 {
        return Err("multiplicative order requires a unit modulo q".to_owned());
    }
    let mut power = 1_u64;
    for order in 1..=modulus {
        power = (power * value) % modulus;
        if power == 1 {
            return Ok(order);
        }
    }
    Err("finite unit failed to return within the group order bound".to_owned())
}

fn factor(mut value: u64) -> Vec<PrimePowerRead> {
    if value <= 1 {
        return Vec::new();
    }
    let mut factors = Vec::new();
    let mut prime = 2_u64;
    while prime <= value / prime {
        if value % prime == 0 {
            let mut exponent = 0_u32;
            while value % prime == 0 {
                value /= prime;
                exponent += 1;
            }
            factors.push(PrimePowerRead { prime, exponent });
        }
        prime += if prime == 2 { 1 } else { 2 };
    }
    if value > 1 {
        factors.push(PrimePowerRead {
            prime: value,
            exponent: 1,
        });
    }
    factors
}

fn reconstruct_from_valuation(factors: &[PrimePowerRead]) -> Result<u64, String> {
    factors.iter().try_fold(1_u64, |product, factor| {
        product
            .checked_mul(
                factor
                    .prime
                    .checked_pow(factor.exponent)
                    .ok_or("valuation power overflow")?,
            )
            .ok_or_else(|| "valuation product overflow".to_owned())
    })
}

fn formal_log_length(factors: &Vec<PrimePowerRead>) -> String {
    if factors.is_empty() {
        return "0".to_owned();
    }
    factors
        .iter()
        .map(|factor| {
            if factor.exponent == 1 {
                format!("log({})", factor.prime)
            } else {
                format!("{}*log({})", factor.exponent, factor.prime)
            }
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

fn formal_mellin_character(factors: &Vec<PrimePowerRead>) -> String {
    if factors.is_empty() {
        return "1".to_owned();
    }
    let product = factors
        .iter()
        .map(|factor| {
            if factor.exponent == 1 {
                format!("{}^(-s)", factor.prime)
            } else {
                format!("{}^(-{}s)", factor.prime, factor.exponent)
            }
        })
        .collect::<Vec<_>>()
        .join("*");
    format!("{product} = exp(-s*({}))", formal_log_length(factors))
}

fn checked_pow(base: u64, exponent: u32) -> Result<u64, String> {
    base.checked_pow(exponent)
        .ok_or_else(|| "bounded digit population overflow".to_owned())
}

fn pow_mod(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    if modulus == 1 {
        return 0;
    }
    base %= modulus;
    let mut result = 1_u64;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exponent >>= 1;
    }
    result
}

fn gcd(mut left: u64, mut right: u64) -> u64 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn is_prime(value: u64) -> bool {
    value >= 2 && factor(value).len() == 1 && factor(value)[0].exponent == 1
}

fn cell_accepted(cell: &RadixResidueCellRead) -> bool {
    let acceptance = &cell.acceptance;
    acceptance.every_word_reconstructs_its_integer
        && acceptance.every_place_word_reconstructs_its_residue
        && acceptance.complete_fibers_partition_the_digit_box
        && acceptance.group_algebra_coefficients_equal_fiber_sizes
        && acceptance.crt_local_projection_vanishes_after_cutoff
        && acceptance.crt_coprime_projection_has_declared_period
        && acceptance.character_inverse_is_licensed_by_exact_orthogonality
}

fn shared_atlas_accepted(atlas: &SharedOccurrenceAtlasRead) -> bool {
    let acceptance = &atlas.acceptance;
    acceptance.every_occurrence_reconstructs_in_both_radices
        && acceptance.every_occurrence_has_the_same_residue_in_both_radices
        && acceptance.complete_residue_fibers_are_identical_after_rechart
        && acceptance.every_positive_valuation_reconstructs_the_occurrence
}

fn output_path() -> Result<PathBuf, String> {
    let mut arguments = env::args_os();
    let _program = arguments.next();
    let output = arguments.next().ok_or_else(usage)?;
    if arguments.next().is_some() {
        return Err(usage());
    }
    Ok(PathBuf::from(output))
}

fn write_new_json<T: Serialize>(output: &PathBuf, value: &T) -> Result<(), String> {
    let mut encoded =
        serde_json::to_vec_pretty(value).map_err(|error| format!("report encodes: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(output)
        .map_err(|error| format!("{} opens exactly once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs: {error}", output.display()))?;
    eprintln!(
        "radix-residue-character transport: accepted · {} bytes · {}",
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn usize_from_u64(value: u64) -> Result<usize, String> {
    usize::try_from(value).map_err(debug)
}

fn usage() -> String {
    "usage: radix_residue_character_transport <new-report.json>".to_owned()
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
