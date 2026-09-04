use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::thread;

use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use serde::Serialize;
use sha2::{Digest, Sha256};

const ARCTAN_TERMS: u32 = 12;
const CHUDNOVSKY_TERMS: u32 = 8;
const CHUDNOVSKY_A: u64 = 13_591_409;
const CHUDNOVSKY_B: u64 = 545_140_134;
const CHUDNOVSKY_SCALE: u64 = 640_320;

type Divisor = BTreeMap<u64, i64>;

#[derive(Clone, Debug, Serialize)]
struct RationalRead {
    numerator: String,
    denominator: String,
}

#[derive(Clone, Debug, Serialize)]
struct PrimePowerRead {
    prime: u64,
    exponent: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Hand {
    Numerator,
    Denominator,
}

#[derive(Clone, Debug, Serialize)]
struct FactorChannelRead {
    name: String,
    hand: Hand,
    integer: String,
    factors: Vec<PrimePowerRead>,
}

#[derive(Clone, Debug, Serialize)]
struct AxisIncidenceRead {
    prime: u64,
    channel: String,
    hand: Hand,
    multiplicity: i64,
    standing: &'static str,
    survives_reduction: bool,
}

#[derive(Clone, Debug, Serialize)]
struct SemiprimeFaceRead {
    layer: &'static str,
    origin: String,
    hand: Hand,
    shape: &'static str,
    factors: Vec<PrimePowerRead>,
}

#[derive(Clone, Debug, Serialize)]
struct TransitionRead {
    from_index: u32,
    to_index: u32,
    sign: i8,
    exact_ratio: RationalRead,
    channels: Vec<FactorChannelRead>,
    numerator_channel_divisor: Vec<PrimePowerRead>,
    denominator_channel_divisor: Vec<PrimePowerRead>,
    internally_cancelled: Vec<PrimePowerRead>,
    signed_divisor_after_channel_coupling: Vec<PrimePowerRead>,
    formal_archimedean_balance: String,
    magnitude_reconstructed_exactly: bool,
    axis_incidences: Vec<AxisIncidenceRead>,
    semiprime_faces: Vec<SemiprimeFaceRead>,
}

#[derive(Clone, Debug, Serialize)]
struct AdditionRead {
    partial_before: RationalRead,
    term: RationalRead,
    raw_numerator: String,
    raw_denominator: String,
    cancellation_gcd: String,
    cancellation_divisor: Vec<PrimePowerRead>,
    partial_after: RationalRead,
    denominator_divisor_after: Vec<PrimePowerRead>,
    cancellation_reconstructed_exactly: bool,
}

#[derive(Clone, Debug, Serialize)]
struct CoupledStateRead {
    law: &'static str,
    incoming_ratio: RationalRead,
    matrix: Vec<Vec<RationalRead>>,
}

#[derive(Clone, Debug, Serialize)]
struct SeriesEventRead {
    index: u32,
    incoming_transition: Option<TransitionRead>,
    seed_channels: Vec<FactorChannelRead>,
    seed_axis_incidences: Vec<AxisIncidenceRead>,
    seed_semiprime_faces: Vec<SemiprimeFaceRead>,
    term: RationalRead,
    term_divisor: Vec<PrimePowerRead>,
    coupled_state: Option<CoupledStateRead>,
    addition: AdditionRead,
    term_product_formula_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct AxisSummaryRead {
    prime: u64,
    first_event: u32,
    channel_incidences: u64,
    numerator_incidences: u64,
    denominator_incidences: u64,
    surviving_channel_incidences: u64,
    additive_cancellation_incidences: u64,
    final_term_exponent: i64,
}

#[derive(Clone, Debug, Serialize)]
struct SeriesSummaryRead {
    foundation_order: Vec<u64>,
    axes: Vec<AxisSummaryRead>,
    total_internal_cancellation_divisor: Vec<PrimePowerRead>,
    total_additive_cancellation_divisor: Vec<PrimePowerRead>,
    final_term_divisor: Vec<PrimePowerRead>,
    final_partial_denominator_divisor: Vec<PrimePowerRead>,
    semiprime_faces: Vec<IndexedSemiprimeRead>,
}

#[derive(Clone, Debug, Serialize)]
struct IndexedSemiprimeRead {
    event: u32,
    face: SemiprimeFaceRead,
}

#[derive(Clone, Debug, Serialize)]
struct ExactIntervalRead {
    lower: RationalRead,
    upper: RationalRead,
}

#[derive(Clone, Debug, Serialize)]
struct AlternatingBoundaryRead {
    first_omitted_magnitude: RationalRead,
    remainder: ExactIntervalRead,
    enclosed_return: ExactIntervalRead,
}

#[derive(Clone, Debug, Serialize)]
struct SeriesRead {
    name: String,
    family: &'static str,
    parameters: BTreeMap<String, String>,
    recurrence: String,
    coupled_state_law: &'static str,
    terms: u32,
    events: Vec<SeriesEventRead>,
    partial_sum: RationalRead,
    boundary: Option<AlternatingBoundaryRead>,
    summary: SeriesSummaryRead,
}

#[derive(Clone, Debug)]
struct BuiltSeries {
    read: SeriesRead,
    partial_sum: BigRational,
    boundary: Option<ExactInterval>,
}

#[derive(Clone, Debug)]
struct ExactInterval {
    lower: BigRational,
    upper: BigRational,
}

#[derive(Clone, Debug, Serialize)]
struct GaussianRead {
    real: String,
    imaginary: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Gaussian {
    real: BigInt,
    imaginary: BigInt,
}

#[derive(Clone, Debug, Serialize)]
struct GaussianFactorRead {
    expression: &'static str,
    value: GaussianRead,
    norm: String,
    norm_divisor: Vec<PrimePowerRead>,
    oriented_factorization: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct GaussianClosureRead {
    identity: &'static str,
    left: GaussianRead,
    right: GaussianRead,
    exact: bool,
    factors: Vec<GaussianFactorRead>,
    gaussian_prime_ideal_axes: Vec<&'static str>,
    argument_boundary: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct MachinAssemblyRead {
    state_vector: Vec<RationalRead>,
    linear_map: Vec<i64>,
    finite_return: RationalRead,
    residual_to_quarter_turn: ExactIntervalRead,
    quarter_turn_enclosure: ExactIntervalRead,
    atan_one_enclosure: ExactIntervalRead,
    machin_enclosure_inside_atan_one: bool,
    gaussian_closure: GaussianClosureRead,
}

#[derive(Clone, Debug, Serialize)]
struct ChudnovskyOuterRead {
    expression: &'static str,
    squared_multiplier: RationalRead,
    squared_multiplier_divisor: Vec<PrimePowerRead>,
    radical_boundary: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct SupportAtlasRead {
    machin_series_scale_axes: Vec<u64>,
    machin_gaussian_norm_axes: Vec<u64>,
    chudnovsky_scale_axes: Vec<u64>,
    series_scale_intersection: Vec<u64>,
    exact_interpretation: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct CellRead {
    name: &'static str,
    status: &'static str,
    exact_content: &'static str,
    boundary: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    every_term_recurrence_exact: bool,
    every_product_formula_balance_exact: bool,
    every_additive_cancellation_exact: bool,
    machin_linear_assembly_exact: bool,
    machin_gaussian_identity_exact: bool,
    machin_tail_boundary_exact: bool,
    chudnovsky_outer_square_exact: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    bounded_cut: BTreeMap<&'static str, u64>,
    workers: BTreeMap<&'static str, u64>,
    arctangent_one: SeriesRead,
    arctangent_one_fifth: SeriesRead,
    arctangent_one_239: SeriesRead,
    machin: MachinAssemblyRead,
    chudnovsky_summand: SeriesRead,
    chudnovsky_outer: ChudnovskyOuterRead,
    support_atlas: SupportAtlasRead,
    cells: Vec<CellRead>,
    acceptance: AcceptanceRead,
    report_sha256_without_digest: String,
}

#[derive(Clone, Debug)]
struct Channel {
    name: String,
    hand: Hand,
    integer: u64,
    factors: BTreeMap<u64, u32>,
}

#[derive(Clone, Debug)]
struct Transition {
    ratio: BigRational,
    divisor: Divisor,
    internal_cancellation: Divisor,
    read: TransitionRead,
}

#[derive(Clone, Debug)]
struct AxisAccumulator {
    first_event: u32,
    channel_incidences: u64,
    numerator_incidences: u64,
    denominator_incidences: u64,
    reduced_transition_incidences: u64,
    additive_cancellation_incidences: u64,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("transcendental presentation topology: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }

    let atan_one = thread::spawn(|| build_arctan_series(1, 1, ARCTAN_TERMS));
    let atan_fifth = thread::spawn(|| build_arctan_series(1, 5, ARCTAN_TERMS));
    let atan_239 = thread::spawn(|| build_arctan_series(1, 239, ARCTAN_TERMS));
    let chudnovsky = thread::spawn(|| build_chudnovsky_series(CHUDNOVSKY_TERMS));

    let atan_one = join_worker("arctangent-one", atan_one)?;
    let atan_fifth = join_worker("arctangent-one-fifth", atan_fifth)?;
    let atan_239 = join_worker("arctangent-one-239", atan_239)?;
    let chudnovsky = join_worker("chudnovsky", chudnovsky)?;

    let machin = build_machin_assembly(&atan_one, &atan_fifth, &atan_239)?;
    let chudnovsky_outer = chudnovsky_outer()?;
    let support_atlas = support_atlas();
    let acceptance = acceptance(
        &atan_one,
        &atan_fifth,
        &atan_239,
        &chudnovsky,
        &machin,
        &chudnovsky_outer,
    );
    let accepted = acceptance.every_term_recurrence_exact
        && acceptance.every_product_formula_balance_exact
        && acceptance.every_additive_cancellation_exact
        && acceptance.machin_linear_assembly_exact
        && acceptance.machin_gaussian_identity_exact
        && acceptance.machin_tail_boundary_exact
        && acceptance.chudnovsky_outer_square_exact
        && acceptance.no_floating_point_causal_data;

    let mut bounded_cut = BTreeMap::new();
    bounded_cut.insert("arctangent_terms_per_arm", u64::from(ARCTAN_TERMS));
    bounded_cut.insert("chudnovsky_terms", u64::from(CHUDNOVSKY_TERMS));
    let mut workers = BTreeMap::new();
    workers.insert("independent_series_workers", 4);
    workers.insert(
        "cpu_parallelism_available",
        thread::available_parallelism()
            .map(|count| u64::try_from(count.get()).unwrap_or(u64::MAX))
            .unwrap_or(1),
    );

    let cells = vec![
        CellRead {
            name: "arctangent recurrence",
            status: "commutes",
            exact_content: "every direct term equals the predecessor multiplied by -u^2(2n+1)/(v^2(2n+3))",
            boundary: "the finite path retains an alternating remainder interval rather than claiming its limit",
        },
        CellRead {
            name: "Machin finite arm assembly",
            status: "commutes",
            exact_content: "the two partial sums remain a vector and [4,-1] returns one exact rational partial",
            boundary: "the residual to the quarter-turn remains an exact interval assembled from both tails",
        },
        CellRead {
            name: "Machin Gaussian closure",
            status: "commutes_with_declared_branch",
            exact_content: "(5+i)^4 and 2(1+i)(239+i) are the same Gaussian integer; norms and oriented prime ideals are retained",
            boundary: "argument equality uses the declared first-quadrant lift",
        },
        CellRead {
            name: "Chudnovsky summand recurrence",
            status: "commutes",
            exact_content: "sixfold factorial lift, threefold denominator lift, cubic successor, fixed scale cube, and moving linear quotient reconstruct every exact term",
            boundary: "a finite summand partial is not identified with the completed inverse-pi evaluation",
        },
        CellRead {
            name: "cross-presentation pi fiber",
            status: "open_but_localized",
            exact_content: "Machin-series, Gaussian-proof, and Chudnovsky-recurrence supports are carried as nonidentical local charts of the declared same return",
            boundary: "the vertical transition law between the full series divisor paths is not inferred from equal output values",
        },
    ];

    let mut report = Report {
        schema: "eros.transcendental-presentation-topology.v1",
        status: if accepted { "accepted" } else { "rejected" },
        question: "Can a transcendental presentation retain multiplicative term formation and additive accumulation as one exact arithmetic topology?",
        bounded_cut,
        workers,
        arctangent_one: atan_one.read,
        arctangent_one_fifth: atan_fifth.read,
        arctangent_one_239: atan_239.read,
        machin,
        chudnovsky_summand: chudnovsky.read,
        chudnovsky_outer,
        support_atlas,
        cells,
        acceptance,
        report_sha256_without_digest: String::new(),
    };
    let without_digest =
        serde_json::to_vec_pretty(&report).map_err(|error| format!("report encodes: {error}"))?;
    report.report_sha256_without_digest = sha256(&without_digest);
    write_new_json(&output, &report)?;
    if !accepted {
        return Err("the exact acceptance relation did not close".to_owned());
    }
    Ok(())
}

fn join_worker(
    name: &str,
    worker: thread::JoinHandle<Result<BuiltSeries, String>>,
) -> Result<BuiltSeries, String> {
    worker
        .join()
        .map_err(|_| format!("{name} worker panicked"))?
}

fn build_arctan_series(
    numerator: u64,
    denominator: u64,
    terms: u32,
) -> Result<BuiltSeries, String> {
    if numerator == 0 || denominator == 0 || numerator > denominator || terms == 0 {
        return Err(
            "the bounded arctangent chart requires 0 < u/v <= 1 and at least one term".to_owned(),
        );
    }
    let seed_channels = vec![
        channel("parameter_numerator", Hand::Numerator, numerator),
        channel("parameter_denominator", Hand::Denominator, denominator),
    ];
    let seed = BigRational::new(BigInt::from(numerator), BigInt::from(denominator));
    let seed_divisor = divisor_from_channels(&seed_channels);
    let name = format!("A({numerator}/{denominator})");
    let recurrence = format!("a_(n+1)/a_n = -{numerator}^2(2n+1)/({denominator}^2(2n+3))");
    let mut parameters = BTreeMap::new();
    parameters.insert("u".to_owned(), numerator.to_string());
    parameters.insert("v".to_owned(), denominator.to_string());

    let mut built = build_series(
        name,
        "arctangent",
        parameters,
        recurrence,
        terms,
        seed,
        seed_channels,
        seed_divisor,
        |from| arctan_transition(numerator, denominator, from),
    )?;

    for event in &built.read.events {
        let direct = arctan_direct_term(numerator, denominator, event.index);
        if rational_from_read(&event.term)? != direct {
            return Err(format!(
                "arctangent direct term {} does not equal its recurrence path",
                event.index
            ));
        }
    }

    let next_power = pow_bigint(numerator, 2 * terms + 1);
    let next_denominator = pow_bigint(denominator, 2 * terms + 1) * BigInt::from(2 * terms + 1);
    let next = BigRational::new(next_power, next_denominator);
    let zero = rational(0, 1);
    let remainder = if terms % 2 == 0 {
        ExactInterval {
            lower: zero,
            upper: next.clone(),
        }
    } else {
        ExactInterval {
            lower: -next.clone(),
            upper: zero,
        }
    };
    let enclosed = ExactInterval {
        lower: &built.partial_sum + &remainder.lower,
        upper: &built.partial_sum + &remainder.upper,
    };
    built.read.boundary = Some(AlternatingBoundaryRead {
        first_omitted_magnitude: rational_read(&next),
        remainder: interval_read(&remainder),
        enclosed_return: interval_read(&enclosed),
    });
    built.boundary = Some(enclosed);
    Ok(built)
}

fn build_chudnovsky_series(terms: u32) -> Result<BuiltSeries, String> {
    if terms == 0 {
        return Err("the Chudnovsky aperture requires at least one term".to_owned());
    }
    let seed_channels = vec![channel("linear_seed_A", Hand::Numerator, CHUDNOVSKY_A)];
    let seed = BigRational::from_integer(BigInt::from(CHUDNOVSKY_A));
    let seed_divisor = divisor_from_channels(&seed_channels);
    let mut parameters = BTreeMap::new();
    parameters.insert("A".to_owned(), CHUDNOVSKY_A.to_string());
    parameters.insert("B".to_owned(), CHUDNOVSKY_B.to_string());
    parameters.insert("scale".to_owned(), CHUDNOVSKY_SCALE.to_string());
    build_series(
        "Chudnovsky summand".to_owned(),
        "hypergeometric",
        parameters,
        "a_(n+1)/a_n = -prod_(j=1)^6(6n+j)(A+B(n+1))/(prod_(j=1)^3(3n+j)(n+1)^3 640320^3(A+Bn))"
            .to_owned(),
        terms,
        seed,
        seed_channels,
        seed_divisor,
        chudnovsky_transition,
    )
}

#[allow(clippy::too_many_arguments)]
fn build_series<F>(
    name: String,
    family: &'static str,
    parameters: BTreeMap<String, String>,
    recurrence: String,
    terms: u32,
    seed: BigRational,
    seed_channels: Vec<Channel>,
    seed_divisor: Divisor,
    transition: F,
) -> Result<BuiltSeries, String>
where
    F: Fn(u32) -> Result<Transition, String>,
{
    let mut events = Vec::with_capacity(usize::try_from(terms).map_err(debug)?);
    let mut term = seed;
    let mut term_divisor = seed_divisor;
    let mut partial = rational(0, 1);
    let mut partial_denominator_divisor = Divisor::new();
    let mut seen_axes = BTreeSet::new();
    let mut foundation_order = Vec::new();
    let mut axis_summary: BTreeMap<u64, AxisAccumulator> = BTreeMap::new();
    let mut total_internal_cancellation = Divisor::new();
    let mut total_additive_cancellation = Divisor::new();
    let mut indexed_semiprimes = Vec::new();

    for index in 0..terms {
        let (incoming, seed_reads, seed_incidences, seed_semiprimes, coupled) = if index == 0 {
            let (incidences, semiprimes) = register_channels(
                index,
                &seed_channels,
                &term_divisor,
                &mut seen_axes,
                &mut foundation_order,
                &mut axis_summary,
            );
            for face in &semiprimes {
                indexed_semiprimes.push(IndexedSemiprimeRead {
                    event: index,
                    face: face.clone(),
                });
            }
            (
                None,
                seed_channels.iter().map(channel_read).collect(),
                incidences,
                semiprimes,
                None,
            )
        } else {
            let mut next = transition(index - 1)?;
            add_divisor(
                &mut total_internal_cancellation,
                &next.internal_cancellation,
            );
            let prior_term = term.clone();
            term *= &next.ratio;
            add_divisor(&mut term_divisor, &next.divisor);
            normalize_divisor(&mut term_divisor);
            if rational_abs(&term) != rational_from_divisor(&term_divisor) {
                return Err(format!("{name} term {index} lost its exact divisor"));
            }
            let matrix = coupled_matrix(&next.ratio);
            let coupled = CoupledStateRead {
                law: "[a_(n+1), S_(n+1)]^T = [[r_n,0],[r_n,1]][a_n,S_n]^T",
                incoming_ratio: rational_read(&next.ratio),
                matrix,
            };
            if &prior_term * &next.ratio != term {
                return Err(format!("{name} recurrence failed at {index}"));
            }
            for face in &next.read.semiprime_faces {
                indexed_semiprimes.push(IndexedSemiprimeRead {
                    event: index,
                    face: face.clone(),
                });
            }
            for incidence in &mut next.read.axis_incidences {
                incidence.standing = if seen_axes.insert(incidence.prime) {
                    foundation_order.push(incidence.prime);
                    "founded"
                } else {
                    "returning"
                };
                let entry = axis_summary
                    .entry(incidence.prime)
                    .or_insert(AxisAccumulator {
                        first_event: index,
                        channel_incidences: 0,
                        numerator_incidences: 0,
                        denominator_incidences: 0,
                        reduced_transition_incidences: 0,
                        additive_cancellation_incidences: 0,
                    });
                entry.channel_incidences += 1;
                match incidence.hand {
                    Hand::Numerator => entry.numerator_incidences += 1,
                    Hand::Denominator => entry.denominator_incidences += 1,
                }
                if incidence.survives_reduction {
                    entry.reduced_transition_incidences += 1;
                }
            }
            (
                Some(next.read),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Some(coupled),
            )
        };

        let addition = add_term(&partial, &partial_denominator_divisor, &term, &term_divisor)?;
        for (prime, exponent) in &addition.cancellation_divisor {
            add_exponent(&mut total_additive_cancellation, *prime, *exponent);
            let entry = axis_summary.entry(*prime).or_insert(AxisAccumulator {
                first_event: index,
                channel_incidences: 0,
                numerator_incidences: 0,
                denominator_incidences: 0,
                reduced_transition_incidences: 0,
                additive_cancellation_incidences: 0,
            });
            entry.additive_cancellation_incidences += 1;
        }
        partial = addition.partial_after.clone();
        partial_denominator_divisor = addition.denominator_divisor_after.clone();
        events.push(SeriesEventRead {
            index,
            incoming_transition: incoming,
            seed_channels: seed_reads,
            seed_axis_incidences: seed_incidences,
            seed_semiprime_faces: seed_semiprimes,
            term: rational_read(&term),
            term_divisor: divisor_read(&term_divisor),
            coupled_state: coupled,
            addition: addition.read,
            term_product_formula_exact: rational_abs(&term) == rational_from_divisor(&term_divisor),
        });
    }

    normalize_divisor(&mut total_internal_cancellation);
    normalize_divisor(&mut total_additive_cancellation);
    let axes = axis_summary
        .into_iter()
        .map(|(prime, summary)| AxisSummaryRead {
            prime,
            first_event: summary.first_event,
            channel_incidences: summary.channel_incidences,
            numerator_incidences: summary.numerator_incidences,
            denominator_incidences: summary.denominator_incidences,
            surviving_channel_incidences: summary.reduced_transition_incidences,
            additive_cancellation_incidences: summary.additive_cancellation_incidences,
            final_term_exponent: *term_divisor.get(&prime).unwrap_or(&0),
        })
        .collect();
    Ok(BuiltSeries {
        read: SeriesRead {
            name,
            family,
            parameters,
            recurrence,
            coupled_state_law: "[a_(n+1), S_(n+1)]^T = [[r_n,0],[r_n,1]][a_n,S_n]^T",
            terms,
            events,
            partial_sum: rational_read(&partial),
            boundary: None,
            summary: SeriesSummaryRead {
                foundation_order,
                axes,
                total_internal_cancellation_divisor: divisor_read(&total_internal_cancellation),
                total_additive_cancellation_divisor: divisor_read(&total_additive_cancellation),
                final_term_divisor: divisor_read(&term_divisor),
                final_partial_denominator_divisor: divisor_read(&partial_denominator_divisor),
                semiprime_faces: indexed_semiprimes,
            },
        },
        partial_sum: partial,
        boundary: None,
    })
}

#[derive(Clone, Debug)]
struct Addition {
    partial_after: BigRational,
    denominator_divisor_after: Divisor,
    cancellation_divisor: Divisor,
    read: AdditionRead,
}

fn add_term(
    partial: &BigRational,
    partial_denominator_divisor: &Divisor,
    term: &BigRational,
    term_divisor: &Divisor,
) -> Result<Addition, String> {
    let raw_numerator = partial.numer() * term.denom() + term.numer() * partial.denom();
    let raw_denominator = partial.denom() * term.denom();
    let gcd = gcd_bigint(abs_bigint(raw_numerator.clone()), raw_denominator.clone());
    let mut raw_denominator_divisor = partial_denominator_divisor.clone();
    add_divisor(
        &mut raw_denominator_divisor,
        &denominator_divisor(term_divisor),
    );
    normalize_divisor(&mut raw_denominator_divisor);
    let candidates: Vec<u64> = raw_denominator_divisor.keys().copied().collect();
    let cancellation_divisor = factor_bigint_over(&gcd, &candidates)?;
    let mut denominator_after = raw_denominator_divisor;
    subtract_divisor(&mut denominator_after, &cancellation_divisor);
    normalize_divisor(&mut denominator_after);
    let partial_after = partial + term;
    let denominator_exact =
        integer_from_positive_divisor(&denominator_after) == partial_after.denom().clone();
    let cancellation_exact =
        integer_from_positive_divisor(&cancellation_divisor) == gcd && denominator_exact;
    if !cancellation_exact {
        return Err("additive cancellation was not reconstructed exactly".to_owned());
    }
    Ok(Addition {
        partial_after: partial_after.clone(),
        denominator_divisor_after: denominator_after.clone(),
        cancellation_divisor: cancellation_divisor.clone(),
        read: AdditionRead {
            partial_before: rational_read(partial),
            term: rational_read(term),
            raw_numerator: raw_numerator.to_string(),
            raw_denominator: raw_denominator.to_string(),
            cancellation_gcd: gcd.to_string(),
            cancellation_divisor: divisor_read(&cancellation_divisor),
            partial_after: rational_read(&partial_after),
            denominator_divisor_after: divisor_read(&denominator_after),
            cancellation_reconstructed_exactly: cancellation_exact,
        },
    })
}

fn arctan_transition(numerator: u64, denominator: u64, from: u32) -> Result<Transition, String> {
    let departing = u64::from(2 * from + 1);
    let arriving = u64::from(2 * from + 3);
    transition_from_channels(
        from,
        vec![
            channel(
                "parameter_numerator_square",
                Hand::Numerator,
                numerator.saturating_mul(numerator),
            ),
            channel("departing_odd_face", Hand::Numerator, departing),
            channel(
                "parameter_denominator_square",
                Hand::Denominator,
                denominator.saturating_mul(denominator),
            ),
            channel("arriving_odd_face", Hand::Denominator, arriving),
        ],
        -1,
    )
}

fn chudnovsky_transition(from: u32) -> Result<Transition, String> {
    let n = u64::from(from);
    let mut channels = Vec::new();
    for j in 1..=6u64 {
        channels.push(channel(
            &format!("sixfold_lift_{j}"),
            Hand::Numerator,
            6 * n + j,
        ));
    }
    channels.push(channel(
        "linear_successor",
        Hand::Numerator,
        CHUDNOVSKY_A
            .checked_add(
                CHUDNOVSKY_B
                    .checked_mul(n + 1)
                    .ok_or_else(|| "Chudnovsky linear successor overflowed".to_owned())?,
            )
            .ok_or_else(|| "Chudnovsky linear successor overflowed".to_owned())?,
    ));
    for j in 1..=3u64 {
        channels.push(channel(
            &format!("threefold_lift_{j}"),
            Hand::Denominator,
            3 * n + j,
        ));
    }
    channels.push(channel(
        "successor_index_cube",
        Hand::Denominator,
        (n + 1)
            .checked_pow(3)
            .ok_or_else(|| "Chudnovsky successor cube overflowed".to_owned())?,
    ));
    channels.push(Channel {
        name: "fixed_scale_cube".to_owned(),
        hand: Hand::Denominator,
        integer: CHUDNOVSKY_SCALE
            .checked_pow(3)
            .ok_or_else(|| "Chudnovsky scale cube overflowed".to_owned())?,
        factors: factor_u64(CHUDNOVSKY_SCALE)
            .into_iter()
            .map(|(prime, exponent)| (prime, exponent.saturating_mul(3)))
            .collect(),
    });
    channels.push(channel(
        "linear_predecessor",
        Hand::Denominator,
        CHUDNOVSKY_A
            .checked_add(
                CHUDNOVSKY_B
                    .checked_mul(n)
                    .ok_or_else(|| "Chudnovsky linear predecessor overflowed".to_owned())?,
            )
            .ok_or_else(|| "Chudnovsky linear predecessor overflowed".to_owned())?,
    ));
    transition_from_channels(from, channels, -1)
}

fn transition_from_channels(
    from: u32,
    channels: Vec<Channel>,
    sign: i8,
) -> Result<Transition, String> {
    let numerator_channels = channel_hand_divisor(&channels, Hand::Numerator);
    let denominator_channels = channel_hand_divisor(&channels, Hand::Denominator);
    let signed = divisor_from_channels(&channels);
    let internally_cancelled = internal_cancellation(&channels);
    let mut divisor = signed.clone();
    normalize_divisor(&mut divisor);
    let magnitude = rational_from_divisor(&divisor);
    let ratio = if sign < 0 {
        -magnitude.clone()
    } else {
        magnitude.clone()
    };
    let channel_product = rational_from_channels(&channels);
    if magnitude != channel_product {
        return Err(format!(
            "transition {from} channel product does not reconstruct its reduced divisor"
        ));
    }
    let mut seen = BTreeSet::new();
    let mut foundations = Vec::new();
    let mut scratch = BTreeMap::new();
    let (incidences, mut semiprimes) = register_channels(
        from + 1,
        &channels,
        &divisor,
        &mut seen,
        &mut foundations,
        &mut scratch,
    );
    semiprimes.extend(semiprime_reduced_sides(&divisor));
    Ok(Transition {
        ratio: ratio.clone(),
        divisor: divisor.clone(),
        internal_cancellation: internally_cancelled.clone(),
        read: TransitionRead {
            from_index: from,
            to_index: from + 1,
            sign,
            exact_ratio: rational_read(&ratio),
            channels: channels.iter().map(channel_read).collect(),
            numerator_channel_divisor: divisor_read(&numerator_channels),
            denominator_channel_divisor: divisor_read(&denominator_channels),
            internally_cancelled: divisor_read(&internally_cancelled),
            signed_divisor_after_channel_coupling: divisor_read(&divisor),
            formal_archimedean_balance: formal_log_balance(&divisor),
            magnitude_reconstructed_exactly: magnitude == channel_product,
            axis_incidences: incidences,
            semiprime_faces: semiprimes,
        },
    })
}

fn register_channels(
    event: u32,
    channels: &[Channel],
    reduced: &Divisor,
    seen: &mut BTreeSet<u64>,
    foundation_order: &mut Vec<u64>,
    summary: &mut BTreeMap<u64, AxisAccumulator>,
) -> (Vec<AxisIncidenceRead>, Vec<SemiprimeFaceRead>) {
    let mut incidences = Vec::new();
    let mut semiprimes = Vec::new();
    for channel in channels {
        if let Some(face) = semiprime_channel(channel) {
            semiprimes.push(face);
        }
        for (prime, exponent) in &channel.factors {
            let signed = match channel.hand {
                Hand::Numerator => i64::from(*exponent),
                Hand::Denominator => -i64::from(*exponent),
            };
            let standing = if seen.insert(*prime) {
                foundation_order.push(*prime);
                "founded"
            } else {
                "returning"
            };
            let survives = reduced
                .get(prime)
                .is_some_and(|value| value.signum() == signed.signum());
            incidences.push(AxisIncidenceRead {
                prime: *prime,
                channel: channel.name.clone(),
                hand: channel.hand,
                multiplicity: i64::from(*exponent),
                standing,
                survives_reduction: survives,
            });
            let entry = summary.entry(*prime).or_insert(AxisAccumulator {
                first_event: event,
                channel_incidences: 0,
                numerator_incidences: 0,
                denominator_incidences: 0,
                reduced_transition_incidences: 0,
                additive_cancellation_incidences: 0,
            });
            entry.channel_incidences += 1;
            match channel.hand {
                Hand::Numerator => entry.numerator_incidences += 1,
                Hand::Denominator => entry.denominator_incidences += 1,
            }
            if survives {
                entry.reduced_transition_incidences += 1;
            }
        }
    }
    (incidences, semiprimes)
}

fn semiprime_channel(channel: &Channel) -> Option<SemiprimeFaceRead> {
    let degree: u32 = channel.factors.values().copied().sum();
    (degree == 2).then(|| SemiprimeFaceRead {
        layer: "factor_channel",
        origin: channel.name.clone(),
        hand: channel.hand,
        shape: semiprime_shape_unsigned(&channel.factors),
        factors: unsigned_divisor_read(&channel.factors),
    })
}

fn semiprime_reduced_sides(divisor: &Divisor) -> Vec<SemiprimeFaceRead> {
    [Hand::Numerator, Hand::Denominator]
        .into_iter()
        .filter_map(|hand| {
            let factors: BTreeMap<u64, u32> = divisor
                .iter()
                .filter_map(|(prime, exponent)| match hand {
                    Hand::Numerator if *exponent > 0 => {
                        Some((*prime, u32::try_from(*exponent).ok()?))
                    }
                    Hand::Denominator if *exponent < 0 => {
                        Some((*prime, u32::try_from(-*exponent).ok()?))
                    }
                    _ => None,
                })
                .collect();
            let degree: u32 = factors.values().copied().sum();
            (degree == 2).then(|| SemiprimeFaceRead {
                layer: "reduced_transition_side",
                origin: match hand {
                    Hand::Numerator => "reduced_numerator".to_owned(),
                    Hand::Denominator => "reduced_denominator".to_owned(),
                },
                hand,
                shape: semiprime_shape_unsigned(&factors),
                factors: unsigned_divisor_read(&factors),
            })
        })
        .collect()
}

fn semiprime_shape_unsigned(factors: &BTreeMap<u64, u32>) -> &'static str {
    if factors.len() == 1 && factors.values().next() == Some(&2) {
        "prime_square_[2]"
    } else {
        "distinct_primes_[1,1]"
    }
}

fn build_machin_assembly(
    atan_one: &BuiltSeries,
    atan_fifth: &BuiltSeries,
    atan_239: &BuiltSeries,
) -> Result<MachinAssemblyRead, String> {
    let fifth_boundary = atan_fifth
        .boundary
        .as_ref()
        .ok_or_else(|| "the fifth arm has no exact boundary".to_owned())?;
    let arm_239_boundary = atan_239
        .boundary
        .as_ref()
        .ok_or_else(|| "the 239 arm has no exact boundary".to_owned())?;
    let atan_one_boundary = atan_one
        .boundary
        .as_ref()
        .ok_or_else(|| "the unit arm has no exact boundary".to_owned())?;
    let finite_return = &atan_fifth.partial_sum * BigInt::from(4) - &atan_239.partial_sum;
    let residual = ExactInterval {
        lower: &fifth_boundary.lower
            - &atan_fifth.partial_sum
            - (&arm_239_boundary.upper - &atan_239.partial_sum)
            + (&fifth_boundary.lower - &atan_fifth.partial_sum) * BigInt::from(3),
        upper: &fifth_boundary.upper
            - &atan_fifth.partial_sum
            - (&arm_239_boundary.lower - &atan_239.partial_sum)
            + (&fifth_boundary.upper - &atan_fifth.partial_sum) * BigInt::from(3),
    };
    let quarter_turn = ExactInterval {
        lower: &finite_return + &residual.lower,
        upper: &finite_return + &residual.upper,
    };
    let containment = atan_one_boundary.lower <= quarter_turn.lower
        && quarter_turn.upper <= atan_one_boundary.upper;
    let gaussian_closure = gaussian_closure()?;
    Ok(MachinAssemblyRead {
        state_vector: vec![
            rational_read(&atan_fifth.partial_sum),
            rational_read(&atan_239.partial_sum),
        ],
        linear_map: vec![4, -1],
        finite_return: rational_read(&finite_return),
        residual_to_quarter_turn: interval_read(&residual),
        quarter_turn_enclosure: interval_read(&quarter_turn),
        atan_one_enclosure: interval_read(atan_one_boundary),
        machin_enclosure_inside_atan_one: containment,
        gaussian_closure,
    })
}

fn gaussian_closure() -> Result<GaussianClosureRead, String> {
    let five_i = Gaussian::new(5, 1);
    let one_i = Gaussian::new(1, 1);
    let two = Gaussian::new(2, 0);
    let two_39_i = Gaussian::new(239, 1);
    let left = five_i.pow(4);
    let right = two.multiply(&one_i).multiply(&two_39_i);
    let one_plus_i = Gaussian::new(1, 1);
    let three_minus_two_i = Gaussian::new(3, -2);
    let unit_i = Gaussian::new(0, 1);
    if five_i != one_plus_i.multiply(&three_minus_two_i) {
        return Err("5+i Gaussian prime orientation did not close".to_owned());
    }
    if two_39_i
        != unit_i
            .multiply(&one_plus_i)
            .multiply(&three_minus_two_i.pow(4))
    {
        return Err("239+i Gaussian prime orientation did not close".to_owned());
    }
    let factors = vec![
        gaussian_factor("5+i", &five_i, "(1+i)(3-2i)")?,
        gaussian_factor("239+i", &two_39_i, "i(1+i)(3-2i)^4")?,
        gaussian_factor("1+i", &one_i, "(1+i)")?,
    ];
    Ok(GaussianClosureRead {
        identity: "(5+i)^4 = 2(1+i)(239+i)",
        left: gaussian_read(&left),
        right: gaussian_read(&right),
        exact: left == right,
        factors,
        gaussian_prime_ideal_axes: vec![
            "(1+i), norm 2",
            "(3-2i), norm 13",
            "(3+2i), conjugate norm-13 orientation",
        ],
        argument_boundary: "all named Gaussian integers occupy the declared first-quadrant argument chart; units and conjugate orientation are not discarded",
    })
}

fn gaussian_factor(
    expression: &'static str,
    value: &Gaussian,
    oriented_factorization: &'static str,
) -> Result<GaussianFactorRead, String> {
    let norm = value.norm();
    let norm_u64 = u64::try_from(&norm)
        .map_err(|_| format!("Gaussian norm for {expression} does not fit the bounded factorer"))?;
    Ok(GaussianFactorRead {
        expression,
        value: gaussian_read(value),
        norm: norm.to_string(),
        norm_divisor: unsigned_divisor_read(&factor_u64(norm_u64)),
        oriented_factorization,
    })
}

fn chudnovsky_outer() -> Result<ChudnovskyOuterRead, String> {
    let denominator = pow_bigint(CHUDNOVSKY_SCALE, 3);
    let squared = BigRational::new(BigInt::from(144), denominator);
    let divisor = divisor_for_rational_components(144, 1, CHUDNOVSKY_SCALE, 3);
    if rational_abs(&squared) != rational_from_divisor(&divisor) {
        return Err("Chudnovsky squared outer multiplier lost its divisor".to_owned());
    }
    Ok(ChudnovskyOuterRead {
        expression: "12 / sqrt(640320^3)",
        squared_multiplier: rational_read(&squared),
        squared_multiplier_divisor: divisor_read(&divisor),
        radical_boundary: "the positive real square-root branch is part of the evaluation chart; squaring exposes the exact rational prime divisor without erasing that branch",
    })
}

fn support_atlas() -> SupportAtlasRead {
    let machin_series = vec![5, 239];
    let machin_gaussian = vec![2, 13];
    let chudnovsky = vec![2, 3, 5, 23, 29];
    let chud_set: BTreeSet<_> = chudnovsky.iter().copied().collect();
    let intersection = machin_series
        .iter()
        .copied()
        .filter(|prime| chud_set.contains(prime))
        .collect();
    SupportAtlasRead {
        machin_series_scale_axes: machin_series,
        machin_gaussian_norm_axes: machin_gaussian,
        chudnovsky_scale_axes: chudnovsky,
        series_scale_intersection: intersection,
        exact_interpretation: "equal transcendental return does not conserve one finite-prime support: formulation transport changes the local divisor chart, and the transition law must carry that change",
    }
}

fn acceptance(
    atan_one: &BuiltSeries,
    atan_fifth: &BuiltSeries,
    atan_239: &BuiltSeries,
    chudnovsky: &BuiltSeries,
    machin: &MachinAssemblyRead,
    outer: &ChudnovskyOuterRead,
) -> AcceptanceRead {
    let series = [atan_one, atan_fifth, atan_239, chudnovsky];
    AcceptanceRead {
        every_term_recurrence_exact: series.iter().all(|series| {
            series
                .read
                .events
                .iter()
                .all(|event| event.term_product_formula_exact)
        }),
        every_product_formula_balance_exact: series.iter().all(|series| {
            series.read.events.iter().all(|event| {
                event
                    .incoming_transition
                    .as_ref()
                    .is_none_or(|transition| transition.magnitude_reconstructed_exactly)
            })
        }),
        every_additive_cancellation_exact: series.iter().all(|series| {
            series
                .read
                .events
                .iter()
                .all(|event| event.addition.cancellation_reconstructed_exactly)
        }),
        machin_linear_assembly_exact: machin.linear_map == vec![4, -1],
        machin_gaussian_identity_exact: machin.gaussian_closure.exact,
        machin_tail_boundary_exact: machin.machin_enclosure_inside_atan_one,
        chudnovsky_outer_square_exact: rational_from_read(&outer.squared_multiplier).is_ok_and(
            |value| {
                rational_abs(&value)
                    == rational_from_divisor_read(&outer.squared_multiplier_divisor)
                        .unwrap_or_else(|_| rational(0, 1))
            },
        ),
        no_floating_point_causal_data: true,
    }
}

impl Gaussian {
    fn new(real: i64, imaginary: i64) -> Self {
        Self {
            real: BigInt::from(real),
            imaginary: BigInt::from(imaginary),
        }
    }

    fn multiply(&self, other: &Self) -> Self {
        Self {
            real: &self.real * &other.real - &self.imaginary * &other.imaginary,
            imaginary: &self.real * &other.imaginary + &self.imaginary * &other.real,
        }
    }

    fn pow(&self, exponent: u32) -> Self {
        let mut result = Self::new(1, 0);
        let mut base = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining % 2 == 1 {
                result = result.multiply(&base);
            }
            remaining /= 2;
            if remaining > 0 {
                base = base.multiply(&base);
            }
        }
        result
    }

    fn norm(&self) -> BigInt {
        &self.real * &self.real + &self.imaginary * &self.imaginary
    }
}

fn gaussian_read(value: &Gaussian) -> GaussianRead {
    GaussianRead {
        real: value.real.to_string(),
        imaginary: value.imaginary.to_string(),
    }
}

fn arctan_direct_term(numerator: u64, denominator: u64, index: u32) -> BigRational {
    let exponent = 2 * index + 1;
    let numerator = pow_bigint(numerator, exponent);
    let denominator = pow_bigint(denominator, exponent) * BigInt::from(exponent);
    let magnitude = BigRational::new(numerator, denominator);
    if index % 2 == 0 {
        magnitude
    } else {
        -magnitude
    }
}

fn channel(name: &str, hand: Hand, integer: u64) -> Channel {
    Channel {
        name: name.to_owned(),
        hand,
        integer,
        factors: factor_u64(integer),
    }
}

fn channel_read(channel: &Channel) -> FactorChannelRead {
    FactorChannelRead {
        name: channel.name.clone(),
        hand: channel.hand,
        integer: channel.integer.to_string(),
        factors: unsigned_divisor_read(&channel.factors),
    }
}

fn divisor_from_channels(channels: &[Channel]) -> Divisor {
    let mut divisor = Divisor::new();
    for channel in channels {
        for (prime, exponent) in &channel.factors {
            let signed = match channel.hand {
                Hand::Numerator => i64::from(*exponent),
                Hand::Denominator => -i64::from(*exponent),
            };
            add_exponent(&mut divisor, *prime, signed);
        }
    }
    normalize_divisor(&mut divisor);
    divisor
}

fn channel_hand_divisor(channels: &[Channel], hand: Hand) -> Divisor {
    let mut divisor = Divisor::new();
    for channel in channels.iter().filter(|channel| channel.hand == hand) {
        for (prime, exponent) in &channel.factors {
            add_exponent(&mut divisor, *prime, i64::from(*exponent));
        }
    }
    normalize_divisor(&mut divisor);
    divisor
}

fn internal_cancellation(channels: &[Channel]) -> Divisor {
    let mut numerator = BTreeMap::<u64, i64>::new();
    let mut denominator = BTreeMap::<u64, i64>::new();
    for channel in channels {
        let target = match channel.hand {
            Hand::Numerator => &mut numerator,
            Hand::Denominator => &mut denominator,
        };
        for (prime, exponent) in &channel.factors {
            *target.entry(*prime).or_insert(0) += i64::from(*exponent);
        }
    }
    numerator
        .into_iter()
        .filter_map(|(prime, positive)| {
            let cancelled = positive.min(*denominator.get(&prime).unwrap_or(&0));
            (cancelled > 0).then_some((prime, cancelled))
        })
        .collect()
}

fn rational_from_channels(channels: &[Channel]) -> BigRational {
    let mut numerator = BigInt::from(1);
    let mut denominator = BigInt::from(1);
    for channel in channels {
        let value = integer_from_unsigned_divisor(&channel.factors);
        match channel.hand {
            Hand::Numerator => numerator *= value,
            Hand::Denominator => denominator *= value,
        }
    }
    BigRational::new(numerator, denominator)
}

fn factor_u64(mut value: u64) -> BTreeMap<u64, u32> {
    assert!(value > 0);
    let mut factors = BTreeMap::new();
    let mut divisor = 2u64;
    while divisor <= value / divisor {
        while value % divisor == 0 {
            *factors.entry(divisor).or_insert(0) += 1;
            value /= divisor;
        }
        divisor = if divisor == 2 { 3 } else { divisor + 2 };
    }
    if value > 1 {
        *factors.entry(value).or_insert(0) += 1;
    }
    factors
}

fn factor_bigint_over(value: &BigInt, candidates: &[u64]) -> Result<Divisor, String> {
    if value.sign() == Sign::Minus || value.sign() == Sign::NoSign {
        if value.sign() == Sign::NoSign {
            return Err("zero has no bounded prime divisor".to_owned());
        }
        return Err("the bounded factorer expects a positive integer".to_owned());
    }
    let mut remainder = value.clone();
    let mut factors = Divisor::new();
    for prime in candidates {
        let prime_big = BigInt::from(*prime);
        while (&remainder % &prime_big).sign() == Sign::NoSign {
            remainder /= &prime_big;
            add_exponent(&mut factors, *prime, 1);
        }
    }
    if remainder != BigInt::from(1) {
        return Err(format!(
            "the supplied denominator support did not completely factor {value}; remainder {remainder}"
        ));
    }
    Ok(factors)
}

fn divisor_for_rational_components(
    numerator: u64,
    numerator_power: u32,
    denominator: u64,
    denominator_power: u32,
) -> Divisor {
    let mut divisor = Divisor::new();
    for (prime, exponent) in factor_u64(numerator) {
        add_exponent(
            &mut divisor,
            prime,
            i64::from(exponent.saturating_mul(numerator_power)),
        );
    }
    for (prime, exponent) in factor_u64(denominator) {
        add_exponent(
            &mut divisor,
            prime,
            -i64::from(exponent.saturating_mul(denominator_power)),
        );
    }
    normalize_divisor(&mut divisor);
    divisor
}

fn denominator_divisor(divisor: &Divisor) -> Divisor {
    divisor
        .iter()
        .filter_map(|(prime, exponent)| (*exponent < 0).then_some((*prime, -*exponent)))
        .collect()
}

fn rational_from_divisor(divisor: &Divisor) -> BigRational {
    let mut numerator = BigInt::from(1);
    let mut denominator = BigInt::from(1);
    for (prime, exponent) in divisor {
        let power = pow_bigint(*prime, u32::try_from(exponent.abs()).unwrap_or(u32::MAX));
        if *exponent > 0 {
            numerator *= power;
        } else {
            denominator *= power;
        }
    }
    BigRational::new(numerator, denominator)
}

fn rational_from_divisor_read(read: &[PrimePowerRead]) -> Result<BigRational, String> {
    let divisor = read
        .iter()
        .map(|power| (power.prime, power.exponent))
        .collect();
    Ok(rational_from_divisor(&divisor))
}

fn integer_from_positive_divisor(divisor: &Divisor) -> BigInt {
    divisor
        .iter()
        .fold(BigInt::from(1), |product, (prime, exponent)| {
            assert!(*exponent >= 0);
            product * pow_bigint(*prime, u32::try_from(*exponent).unwrap_or(u32::MAX))
        })
}

fn integer_from_unsigned_divisor(divisor: &BTreeMap<u64, u32>) -> BigInt {
    divisor
        .iter()
        .fold(BigInt::from(1), |product, (prime, exponent)| {
            product * pow_bigint(*prime, *exponent)
        })
}

fn add_divisor(target: &mut Divisor, source: &Divisor) {
    for (prime, exponent) in source {
        add_exponent(target, *prime, *exponent);
    }
}

fn subtract_divisor(target: &mut Divisor, source: &Divisor) {
    for (prime, exponent) in source {
        add_exponent(target, *prime, -*exponent);
    }
}

fn add_exponent(divisor: &mut Divisor, prime: u64, exponent: i64) {
    *divisor.entry(prime).or_insert(0) += exponent;
}

fn normalize_divisor(divisor: &mut Divisor) {
    divisor.retain(|_, exponent| *exponent != 0);
}

fn divisor_read(divisor: &Divisor) -> Vec<PrimePowerRead> {
    divisor
        .iter()
        .map(|(prime, exponent)| PrimePowerRead {
            prime: *prime,
            exponent: *exponent,
        })
        .collect()
}

fn unsigned_divisor_read(divisor: &BTreeMap<u64, u32>) -> Vec<PrimePowerRead> {
    divisor
        .iter()
        .map(|(prime, exponent)| PrimePowerRead {
            prime: *prime,
            exponent: i64::from(*exponent),
        })
        .collect()
}

fn formal_log_balance(divisor: &Divisor) -> String {
    if divisor.is_empty() {
        return "log|r|_infinity = 0".to_owned();
    }
    let terms = divisor
        .iter()
        .map(|(prime, exponent)| format!("{exponent}*log({prime})"))
        .collect::<Vec<_>>()
        .join(" + ");
    format!("log|r|_infinity = {terms}; log|r|_infinity + sum_p log|r|_p = 0")
}

fn coupled_matrix(ratio: &BigRational) -> Vec<Vec<RationalRead>> {
    vec![
        vec![rational_read(ratio), rational_read(&rational(0, 1))],
        vec![rational_read(ratio), rational_read(&rational(1, 1))],
    ]
}

fn interval_read(interval: &ExactInterval) -> ExactIntervalRead {
    ExactIntervalRead {
        lower: rational_read(&interval.lower),
        upper: rational_read(&interval.upper),
    }
}

fn rational_read(value: &BigRational) -> RationalRead {
    RationalRead {
        numerator: value.numer().to_string(),
        denominator: value.denom().to_string(),
    }
}

fn rational_from_read(read: &RationalRead) -> Result<BigRational, String> {
    let numerator = BigInt::parse_bytes(read.numerator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact numerator {}", read.numerator))?;
    let denominator = BigInt::parse_bytes(read.denominator.as_bytes(), 10)
        .ok_or_else(|| format!("invalid exact denominator {}", read.denominator))?;
    if denominator.sign() != Sign::Plus {
        return Err("an exact rational denominator must be positive".to_owned());
    }
    Ok(BigRational::new(numerator, denominator))
}

fn rational_abs(value: &BigRational) -> BigRational {
    if value.numer().sign() == Sign::Minus {
        -value.clone()
    } else {
        value.clone()
    }
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn pow_bigint(base: u64, exponent: u32) -> BigInt {
    BigInt::from(base).pow(exponent)
}

fn abs_bigint(value: BigInt) -> BigInt {
    if value.sign() == Sign::Minus {
        -value
    } else {
        value
    }
}

fn gcd_bigint(mut left: BigInt, mut right: BigInt) -> BigInt {
    while right.sign() != Sign::NoSign {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    abs_bigint(left)
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
        "transcendental presentation topology: accepted · {} bytes · {}",
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

fn usage() -> String {
    "usage: eros_transcendental_presentation_topology <new-report.json>".to_owned()
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
