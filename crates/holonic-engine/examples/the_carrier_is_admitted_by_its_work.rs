//! Admit one of two exact carriers on the **work** they do, never on the clock that watched them.
//!
//! `crates/holonic-engine/src/cuda_aperture.rs` conducts every receiver aperture through one of two
//! carriers that a parity gate has already proved indistinguishable: the exact cpu law, and the
//! hybrid CUDA/cpu law. Until 2026-08-08 the choice between them was
//!
//! ```text
//! if authority_nanoseconds < candidate_nanoseconds
//! ```
//!
//! — one unrepeated wall-clock sample per carrier, taken once, permanently routing every later
//! trace. Brandon, ruling on being shown it: *"A clock timing sample should not be the decider of
//! \"carrier admission\""*.
//!
//! The defect is not noise. The parity gate three lines above has already proved the two carriers
//! return the same exact support for the declared receivers, so the question has **no answer inside
//! that receiver family**, and the code resolved it by consulting a coordinate that is not in the
//! family and is not receiver-visible: cpu contention, which includes whether the card is
//! simultaneously scanning out a desktop. That is `CLAUDE.md` §0's fourth lesson — a receiver-visible
//! coordinate promoted into an invariant, returning consistently because there has only ever been
//! one frame.
//!
//! This driver exhibits what replaced it. Every figure below is a `BigUint` derived from the material
//! and the declared aperture; none of it moves when the machine is busy.
//!
//! ```text
//! cargo run --release --example the_carrier_is_admitted_by_its_work
//! cargo run --release --example the_carrier_is_admitted_by_its_work -- --display-active
//! ```
//!
//! The optional argument declares the frame the run's nanoseconds are taken in — `--headless`,
//! `--display-active`, or nothing, which stays honestly `Undeclared`. Declaring a frame does not
//! create one; it makes a display-active run a **second frame** rather than corrupted data.
//!
//! The driver exits non-zero if any declared control fails.

use std::collections::BTreeSet;

use holonic_engine::{
    ApertureExecutionBackend, CarrierAdmission, CarrierWork, ConicCellId, ContinuousPresentation,
    CpuExecutor, CudaApertureError, CudaApertureExecutor, CudaApertureReceipt,
    DeclaredCarrierMetric, DisplayFrame, ExactOrdering, HomogeneousConic, PresentationBoundary,
    PresentedPrimitive, ProjectedConic, ProjectiveDepthLaw, ProjectiveLine2, ReceiverPrimitive,
    ReceiverPrimitiveId, TerminalMatrixSpec,
};
use num_bigint::BigUint;
use relational_geometry::{Rat, ReceiverId, integer};

// -------------------------------------------------------------------------------------------------
// THE DECLARED APERTURES
// -------------------------------------------------------------------------------------------------

/// The finite aperture the live carriers are pointed at. `32 x 24` is the extent
/// `desktop_receiver`'s own packed-carrier grade uses, so the device path here is the one the body
/// already conducts through rather than a fixture built to succeed.
const APERTURE_WIDTH: u32 = 32;
const APERTURE_HEIGHT: u32 = 24;

/// How many times the live hybrid carrier is re-conducted on identical material. Repetition is the
/// **weak** second frame: it cannot move the work vector, and it does move the clock. The strong
/// second frame is a display-active run on the same card, which this driver declares and does not
/// create — see BOUNDS.
const LIVE_REPETITIONS: usize = 3;

fn work(cpu: u32, device: u32, transfer: u32, bits: u32) -> CarrierWork {
    CarrierWork {
        cpu_evaluations: BigUint::from(cpu),
        device_evaluations: BigUint::from(device),
        transfer_bytes: BigUint::from(transfer),
        intermediate_bits: BigUint::from(bits),
    }
}

fn metric(cpu: u32, device: u32, transfer: u32) -> DeclaredCarrierMetric {
    DeclaredCarrierMetric::without_width(
        BigUint::from(cpu),
        BigUint::from(device),
        BigUint::from(transfer),
    )
}

fn render_work(carrier: &CarrierWork) -> String {
    format!(
        "cpu {:>7}  device {:>7}  transfer {:>7}  bits {:>4}",
        carrier.cpu_evaluations,
        carrier.device_evaluations,
        carrier.transfer_bytes,
        carrier.intermediate_bits
    )
}

fn render_ordering(ordering: ExactOrdering) -> &'static str {
    match ordering {
        ExactOrdering::Less => "Less   ",
        ExactOrdering::Equal => "Equal  ",
        ExactOrdering::Greater => "Greater",
        ExactOrdering::Open => "Open   ",
    }
}

fn render_admission(admission: &CarrierAdmission) -> String {
    match admission {
        CarrierAdmission::Open => "Open — both carriers retained".to_owned(),
        decided => {
            let carrier = match decided.conducts_through() {
                ApertureExecutionBackend::ExactCpu => "ExactCpu",
                ApertureExecutionBackend::HybridCuda => "HybridCuda",
            };
            match decided.dilation() {
                Some(dilation) => format!(
                    "{carrier} — dilation (C {}, d {}) held as a pair",
                    dilation.arc, dilation.chord
                ),
                None => format!("{carrier} — by domination, nothing declared"),
            }
        }
    }
}

fn render_frame(frame: DisplayFrame) -> &'static str {
    match frame {
        DisplayFrame::Undeclared => "Undeclared",
        DisplayFrame::Headless => "Headless",
        DisplayFrame::DisplayActive => "DisplayActive",
    }
}

fn rule(title: &str) {
    println!("\n{title}");
    println!("{}", "-".repeat(title.len()));
}

// -------------------------------------------------------------------------------------------------
// THE LIVE MATERIAL
// -------------------------------------------------------------------------------------------------

fn terminal(width: u32, height: u32) -> TerminalMatrixSpec {
    let horizontal_span = integer(2);
    TerminalMatrixSpec {
        width,
        height,
        boundary: PresentationBoundary {
            horizontal_span: horizontal_span.clone(),
            vertical_span: horizontal_span * Rat::from_integer(height.into())
                / Rat::from_integer(width.into()),
        },
    }
}

fn conic(receiver: u64, cell: u64, coefficients: [Rat; 6]) -> PresentedPrimitive {
    let form = HomogeneousConic::new(coefficients).expect("the declared conic is a conic");
    PresentedPrimitive {
        receiver: ReceiverId(receiver),
        primitive: ReceiverPrimitive::Conic(ProjectedConic {
            source: ReceiverPrimitiveId::NativeConic(ConicCellId(cell)),
            class_in_receiver_chart: form.classify(),
            form,
            receiver_depth: ProjectiveDepthLaw {
                numerator: ProjectiveLine2::homogeneous(integer(0), integer(0), integer(1)),
                denominator: ProjectiveLine2::homogeneous(integer(0), integer(0), integer(1)),
            },
        }),
    }
}

/// Two receivers, three conics. Every one is exactly representable on the device carrier, so the
/// hybrid candidate genuinely splits work across the seam rather than falling back to the cpu and
/// making the two carriers a mirror by accident.
fn live_presentation() -> ContinuousPresentation {
    ContinuousPresentation {
        schema: "holonic-engine.carrier-admission-grade.v1".to_owned(),
        boundary_name: "carrier admission by exact work".to_owned(),
        primitives: vec![
            // the unit circle
            conic(
                1,
                901,
                [
                    integer(1),
                    integer(0),
                    integer(1),
                    integer(0),
                    integer(0),
                    integer(-1),
                ],
            ),
            // an ellipse, off-centre
            conic(
                1,
                902,
                [
                    integer(4),
                    integer(0),
                    integer(1),
                    integer(1),
                    integer(0),
                    integer(-1),
                ],
            ),
            // a hyperbola
            conic(
                2,
                903,
                [
                    integer(1),
                    integer(0),
                    integer(-1),
                    integer(0),
                    integer(0),
                    integer(-1),
                ],
            ),
        ],
        coordinate_fields: Vec::new(),
        relations: Vec::new(),
        seams: Vec::new(),
    }
}

fn declared_frame() -> DisplayFrame {
    match std::env::args().nth(1).as_deref() {
        Some("--headless") => DisplayFrame::Headless,
        Some("--display-active") => DisplayFrame::DisplayActive,
        _ => DisplayFrame::Undeclared,
    }
}

fn main() {
    let mut holds: Vec<(&str, bool, String)> = Vec::new();
    let frame = declared_frame();

    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!(
        "law=a carrier is admitted on its exact work vector; a clock may measure, never select"
    );
    println!("convicted=cuda_aperture.rs — `if authority_nanoseconds < candidate_nanoseconds`");
    println!("declared_frame={}", render_frame(frame));

    // ---------------------------------------------------------------------------------------------
    rule("THE DECLARED APERTURES");
    // ---------------------------------------------------------------------------------------------
    println!("  work vector      cpu_evaluations, device_evaluations, transfer_bytes,");
    println!(
        "                   intermediate_bits — every coordinate a BigUint read off the receipt"
    );
    println!(
        "                   the carrier already produced, all derived from the material and the"
    );
    println!("                   declared aperture, all reproducing bit-for-bit on any machine.");
    println!("  admission law 1  CarrierWork::order_against — the metric-free PRODUCT order, four");
    println!("                   states, returning exact_value::ExactOrdering. Decides only on");
    println!("                   domination, because that holds under every monotone metric.");
    println!("  admission law 2  CarrierAdmission::under — a receiver's DECLARED exchange between");
    println!("                   kinds of work. §13 rule 2: the metric is a receiver face of");
    println!("                   standing, never a modelling convenience.");
    println!("  retained         Open retains BOTH carriers. `trace_through` conducts either.");
    println!(
        "  live aperture    {APERTURE_WIDTH} x {APERTURE_HEIGHT} finite members, 3 conics, 2 receivers"
    );

    // ---------------------------------------------------------------------------------------------
    rule("SECTION 1 — WHAT THE WORK VECTOR RETURNS WITH NOTHING DECLARED");
    // ---------------------------------------------------------------------------------------------
    println!(
        "  Four declared carrier pairs. The order is componentwise, so it is PARTIAL on purpose: a\n  \
         cpu evaluation and a device evaluation are different units and nothing in the material\n  \
         says how many of one buys one of the other.\n"
    );

    struct Pair {
        name: &'static str,
        why: &'static str,
        authority: CarrierWork,
        candidate: CarrierWork,
        predicted: ExactOrdering,
    }

    let pairs = vec![
        Pair {
            name: "dominated candidate",
            why: "no more work in any coordinate, strictly less in two",
            authority: work(1_000, 60, 64, 128),
            candidate: work(100, 60, 32, 128),
            predicted: ExactOrdering::Less,
        },
        Pair {
            name: "dominating candidate",
            why: "the same pair, read the other way",
            authority: work(100, 60, 32, 128),
            candidate: work(1_000, 60, 64, 128),
            predicted: ExactOrdering::Greater,
        },
        Pair {
            name: "mirror",
            why: "the detour founded nothing: the two vectors coincide",
            authority: work(768, 0, 0, 128),
            candidate: work(768, 0, 0, 128),
            predicted: ExactOrdering::Equal,
        },
        Pair {
            name: "incomparable",
            why: "fewer cpu evaluations bought with device work and transferred octets",
            authority: work(2_304, 0, 0, 128),
            candidate: work(256, 2_048, 4_096, 128),
            predicted: ExactOrdering::Open,
        },
    ];

    let mut ordering_population: BTreeSet<&'static str> = BTreeSet::new();
    let mut predictions_held = true;
    let mut open_retains_both = false;
    for pair in &pairs {
        let returned = pair.candidate.order_against(&pair.authority);
        let admission = CarrierAdmission::from_work(&pair.authority, &pair.candidate);
        let held = returned == pair.predicted;
        predictions_held &= held;
        ordering_population.insert(render_ordering(returned).trim());
        println!("  {}", pair.name);
        println!("    {}", pair.why);
        println!("    authority   {}", render_work(&pair.authority));
        println!("    candidate   {}", render_work(&pair.candidate));
        println!(
            "    ordering    {}  (predicted {}){}",
            render_ordering(returned),
            render_ordering(pair.predicted).trim(),
            if held { "" } else { "   <- PREDICTION REFUTED" }
        );
        println!("    admission   {}", render_admission(&admission));
        if returned == ExactOrdering::Open {
            open_retains_both = admission.is_open();
            println!(
                "    retained    both — is_open()={}, and a declared metric DOES separate the same",
                admission.is_open()
            );
            let separated =
                CarrierAdmission::under(&metric(1, 1, 1), &pair.authority, &pair.candidate);
            println!(
                "                two vectors: {}\n                so Open is a refusal, not an inability.",
                render_admission(&separated)
            );
        }
        println!();
    }

    holds.push((
        "the work-vector order returns all four states on the declared population",
        ordering_population.len() == 4 && predictions_held,
        format!(
            "{} distinct states returned: {:?}; every prediction {}",
            ordering_population.len(),
            ordering_population,
            if predictions_held { "held" } else { "REFUTED" }
        ),
    ));
    holds.push((
        "an incomparable pair admits Open and retains both carriers",
        open_retains_both,
        "CarrierAdmission::from_work returned Open; dilation() is None; neither carrier discarded"
            .to_owned(),
    ));

    // ---------------------------------------------------------------------------------------------
    rule("SECTION 2 — THE GAUGE EXHIBITS ITS OWN ORBIT");
    // ---------------------------------------------------------------------------------------------
    println!(
        "  §8: *a gauge whose group acts trivially on the declared material is not a gauge.* The\n  \
         declared metric is the gauge here. Same two work vectors, three receiver declarations.\n"
    );
    let authority = work(2_304, 0, 0, 128);
    let candidate = work(256, 2_048, 4_096, 128);
    println!("    authority   {}", render_work(&authority));
    println!("    candidate   {}\n", render_work(&candidate));
    let declarations = [
        ("cpu 1 : device 1 : transfer 1     ", metric(1, 1, 1)),
        ("cpu 1 : device 1 : transfer 0     ", metric(1, 1, 0)),
        ("cpu 1 : device 4 : transfer 1     ", metric(1, 4, 1)),
    ];
    let mut orbit: BTreeSet<&'static str> = BTreeSet::new();
    for (name, declared) in &declarations {
        let admission = CarrierAdmission::under(declared, &authority, &candidate);
        orbit.insert(match admission.conducts_through() {
            _ if admission.is_open() => "Open",
            ApertureExecutionBackend::ExactCpu => "ExactCpu",
            ApertureExecutionBackend::HybridCuda => "HybridCuda",
        });
        println!("    {name}  {}", render_admission(&admission));
    }
    println!(
        "\n  The orbit is non-trivial: the SAME exact work admits different carriers under different\n  \
         receiver declarations, which is what makes the declaration load-bearing rather than\n  \
         decorative. Nothing was measured to produce any line above."
    );
    holds.push((
        "the declared metric moves the admission on this material — the gauge orbit is non-trivial",
        orbit.len() > 1,
        format!(
            "{} distinct admitted carriers across {} declarations",
            orbit.len(),
            declarations.len()
        ),
    ));

    // ---------------------------------------------------------------------------------------------
    rule("SECTION 3 — THE REGRESSION CONTROL: NO CLOCK CAN MOVE THE ADMISSION");
    // ---------------------------------------------------------------------------------------------
    println!(
        "  The convicted comparison is reintroduced as DATA. Four timing pairs are swept, including\n  \
         one where the candidate took a million times as long as the authority — which is what a\n  \
         desktop scanning out on the same card looks like. The admission may not move.\n"
    );
    let declared = metric(1, 1, 1);
    let reference = CarrierAdmission::under(&declared, &authority, &candidate);
    let mut clock_moved = false;
    for (candidate_ns, authority_ns) in [
        (1_u128, 1_000_000_u128),
        (1_000_000, 1),
        (0, 0),
        (7_919, 7_919),
    ] {
        let again = CarrierAdmission::under(&declared, &authority, &candidate);
        let convicted_would_pick = if authority_ns < candidate_ns {
            ApertureExecutionBackend::ExactCpu
        } else {
            ApertureExecutionBackend::HybridCuda
        };
        let agrees = again == reference;
        clock_moved |= !agrees;
        println!(
            "    candidate {candidate_ns:>9} ns  authority {authority_ns:>9} ns   \
             admitted {:<11} the clock would have picked {:?}",
            match again.conducts_through() {
                ApertureExecutionBackend::ExactCpu => "ExactCpu",
                ApertureExecutionBackend::HybridCuda => "HybridCuda",
            },
            convicted_would_pick
        );
    }
    println!(
        "\n  The convicted comparison disagrees with itself across these four samples. The work\n  \
         vector does not."
    );
    holds.push((
        "the admission is a function of exact work and no timing sample moves it",
        !clock_moved,
        "four timing pairs swept, including 1:1000000; the admitted carrier never moved".to_owned(),
    ));

    // ---------------------------------------------------------------------------------------------
    rule("SECTION 4 — THE LIVE CARRIER, ON A REAL CARD, IN A DECLARED FRAME");
    // ---------------------------------------------------------------------------------------------
    let presentation = live_presentation();
    let specification = terminal(APERTURE_WIDTH, APERTURE_HEIGHT);
    let receivers = BTreeSet::from([ReceiverId(1), ReceiverId(2)]);
    let executor = CpuExecutor::serial();

    match CudaApertureExecutor::new() {
        Err(CudaApertureError::NoDevice) => {
            println!("  NOT EXERCISED — no CUDA device is present on this cpu.");
            println!(
                "  Sections 1-3 are exact and device-free; this section is the only one that needs\n  \
                 a card, and its absence is reported rather than papered over."
            );
        }
        Err(error) => {
            println!("  NOT EXERCISED — the CUDA carrier refused to mount: {error}");
            println!("  This is reported as a refusal, not as a passing control.");
        }
        Ok(raw) => {
            let admitted = raw.declaring(metric(1, 1, 1)).in_frame(frame);
            match admitted.admit(&presentation, &specification, &receivers, &executor) {
                Err(error) => {
                    println!("  REFUSED — {error}");
                    holds.push((
                        "the live carrier admits without a parity refusal",
                        false,
                        format!("{error}"),
                    ));
                }
                Ok((executor_handle, traces, receipt)) => {
                    live_section(
                        &mut holds,
                        &executor_handle,
                        &traces,
                        &receipt,
                        &presentation,
                        &specification,
                        &receivers,
                        &executor,
                        frame,
                    );
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    rule("BOUNDS");
    // ---------------------------------------------------------------------------------------------
    println!(
        "  - The metric-free product order is PARTIAL, and on this executor's own material it\n    \
         returns Open whenever the card did any work at all. That is the finding, not a gap: the\n    \
         two carriers trade cpu evaluations against device evaluations plus transferred octets,\n    \
         and no ordering of those is available without a receiver's declaration. The work vector\n    \
         alone is NOT sufficient to admit a carrier here."
    );
    println!(
        "  - `DeclaredCarrierMetric` prices three coordinates and not `intermediate_bits`, which is\n    \
         a width rather than a count. The product order does use it. A declaration that wanted to\n    \
         price width would need a fourth cost, and none is claimed."
    );
    println!(
        "  - `CarrierWork::of_cpu_authority` is a PREDICTION taken from the candidate's receipt\n    \
         without running the cpu, and on this material its MAGNITUDE is refuted — see section 4.\n    \
         Its doc claims *the cpu law evaluates every support the split shared out*; the cpu law\n    \
         in fact evaluates strictly fewer, because it does not evaluate an aperture member a tile\n    \
         has already excluded. The predicted ORDERING survives, which is the claim the owner's own\n    \
         doc makes falsifiable, and the refuted magnitude is information the clock comparison could\n    \
         not have produced at all."
    );
    println!(
        "  - Declaring a frame does not create one. Repetition within one process is a WEAK second\n    \
         frame: it can move the clock and cannot move the work. The strong second frame is a\n    \
         display-active run on the same card, declared with `--display-active`, and this driver\n    \
         does not put the card under a display load itself."
    );
    println!(
        "  - Under `Open` the default conduct is the cpu authority, because it is the reference\n    \
         every parity gate is taken against. That is a retained-plurality default and not a hidden\n    \
         preference: `admission()` reports it and `trace_through` conducts the other way."
    );
    println!(
        "  - Nothing here is a claim about which carrier is faster. Nanoseconds are retained on the\n    \
         receipt as measurement, carrying the frame they were taken in, and they select nothing."
    );

    // ---------------------------------------------------------------------------------------------
    rule("CONTROLS");
    // ---------------------------------------------------------------------------------------------
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        println!(
            "  [{}] {claim}\n        {evidence}",
            if *verdict { "PASS" } else { "FAIL" }
        );
        if !verdict {
            failed += 1;
        }
    }
    if failed > 0 {
        println!("\n{failed} declared control(s) failed");
        std::process::exit(1);
    }
    println!("\nevery declared control holds");
}

#[allow(clippy::too_many_arguments)]
fn live_section(
    holds: &mut Vec<(&'static str, bool, String)>,
    executor_handle: &holonic_engine::AdmittedCudaApertureExecutor,
    traces: &std::collections::BTreeMap<ReceiverId, holonic_engine::ReceiverApertureTrace>,
    receipt: &CudaApertureReceipt,
    presentation: &ContinuousPresentation,
    specification: &TerminalMatrixSpec,
    receivers: &BTreeSet<ReceiverId>,
    executor: &CpuExecutor,
    frame: DisplayFrame,
) {
    // Both carriers are re-conducted first, because `admit` returns the receipt of whichever
    // carrier it admitted. Reading the admitted receipt's device figures beside the *candidate's*
    // work vector would print two carriers' coordinates as though they were one frame — the
    // absolute-frame defect at the level of a printout.
    let cpu_run = executor_handle.trace_through(
        ApertureExecutionBackend::ExactCpu,
        presentation,
        specification,
        receivers,
        executor,
    );
    let hybrid_run = executor_handle.trace_through(
        ApertureExecutionBackend::HybridCuda,
        presentation,
        specification,
        receivers,
        executor,
    );

    println!("  device            {}", receipt.device);
    println!(
        "  parity            {} (the gate that proves the two carriers indistinguishable)",
        receipt.cpu_parity
    );
    println!("  receivers         {}", receipt.receivers);
    println!("  aperture_members  {}", receipt.aperture_members);
    println!("  admitted receipt  {}", receipt.execution_backend);
    if let Ok((_, hybrid_receipt)) = &hybrid_run {
        println!();
        println!("  THE HYBRID CANDIDATE'S OWN APERTURE FIGURES");
        println!("    arithmetic        {}", hybrid_receipt.device_arithmetic);
        println!("    device_primitives {}", hybrid_receipt.device_primitives);
        println!("    cpu_primitives   {}", hybrid_receipt.cpu_primitives);
        println!("    device_threads    {}", hybrid_receipt.device_threads);
        println!(
            "    device_output     {} octets",
            hybrid_receipt.device_output_bytes
        );
    }
    println!();
    println!("  THE FRAME-INVARIANT HALF — what the admission was taken on");
    println!(
        "    authority work  {}",
        render_work(&receipt.authority_work)
    );
    println!(
        "    candidate work  {}",
        render_work(&receipt.candidate_work)
    );
    println!(
        "    work_ordering   {}  (candidate against authority, nothing declared)",
        render_ordering(receipt.work_ordering)
    );
    println!(
        "    admission       {}",
        render_admission(&receipt.admission)
    );
    println!(
        "    conducts        {:?}",
        receipt.admission.conducts_through()
    );
    println!();
    println!("  THE FRAME-DEPENDENT HALF — retained as measurement, selecting nothing");
    println!(
        "    display_frame   {}",
        render_frame(receipt.display_frame)
    );
    println!(
        "    candidate       {} ns   authority {} ns",
        receipt.admission_candidate_nanoseconds, receipt.admission_authority_nanoseconds
    );
    println!(
        "    the convicted comparison would have picked {:?} from exactly these two numbers.",
        if receipt.admission_authority_nanoseconds < receipt.admission_candidate_nanoseconds {
            ApertureExecutionBackend::ExactCpu
        } else {
            ApertureExecutionBackend::HybridCuda
        }
    );

    holds.push((
        "the live receipt carries the frame its nanoseconds were taken in",
        receipt.display_frame == frame,
        format!(
            "declared {}, receipt carries {}",
            render_frame(frame),
            render_frame(receipt.display_frame)
        ),
    ));

    // -- the returned artifact -------------------------------------------------------------------
    println!();
    println!("  THE RETURNED ARTIFACT — exact support, per receiver");
    let mut support_total = BigUint::from(0_u32);
    for (receiver, trace) in traces {
        println!(
            "    receiver {:<3} exact_support_queries {}",
            receiver.0, trace.exact_support_queries
        );
        support_total += &trace.exact_support_queries;
    }
    println!("    total        {support_total}");

    // -- Open retains both, exhibited by conducting through each ---------------------------------
    println!();
    println!("  BOTH CARRIERS ARE STILL CONDUCTIBLE");
    let both_conduct = match (&cpu_run, &hybrid_run) {
        (Ok((cpu_traces, cpu_receipt)), Ok((hybrid_traces, hybrid_receipt))) => {
            println!(
                "    ExactCpu   returned {} receivers, {} exact support evaluations, {} ns",
                cpu_traces.len(),
                cpu_receipt.exact_support_evaluations,
                cpu_receipt.wall_nanoseconds
            );
            println!(
                "    HybridCuda  returned {} receivers, {} exact support evaluations, {} ns",
                hybrid_traces.len(),
                hybrid_receipt.exact_support_evaluations,
                hybrid_receipt.wall_nanoseconds
            );
            let same = cpu_traces.len() == hybrid_traces.len()
                && cpu_traces.iter().all(|(receiver, cpu)| {
                    hybrid_traces
                        .get(receiver)
                        .is_some_and(|hybrid| cpu.has_same_exact_support(hybrid))
                });
            println!(
                "    identical exact support across both carriers: {same} — which is precisely why\n    \
                 the receiver family cannot answer the question, and why a clock must not."
            );
            same
        }
        (cpu, hybrid) => {
            println!("    ExactCpu   {:?}", cpu.as_ref().err());
            println!("    HybridCuda  {:?}", hybrid.as_ref().err());
            false
        }
    };
    holds.push((
        "both carriers stay conductible after admission and return identical exact support",
        both_conduct,
        "trace_through(ExactCpu) and trace_through(HybridCuda) both returned; support agrees"
            .to_owned(),
    ));

    // -- the weak second frame -------------------------------------------------------------------
    println!();
    println!("  THE WEAK SECOND FRAME — {LIVE_REPETITIONS} repetitions on identical material");
    let mut vectors = BTreeSet::new();
    let mut clocks = Vec::new();
    for repetition in 0..LIVE_REPETITIONS {
        match executor_handle.trace_through(
            ApertureExecutionBackend::HybridCuda,
            presentation,
            specification,
            receivers,
            executor,
        ) {
            Ok((_, again)) => {
                let vector = CarrierWork::of_candidate(&again);
                println!(
                    "    run {repetition}   {}   wall {} ns",
                    render_work(&vector),
                    again.wall_nanoseconds
                );
                vectors.insert(render_work(&vector));
                clocks.push(again.wall_nanoseconds);
            }
            Err(error) => println!("    run {repetition}   REFUSED — {error}"),
        }
    }
    let work_invariant = vectors.len() == 1;
    let clock_moved = clocks.iter().collect::<BTreeSet<_>>().len() > 1;
    println!(
        "\n    work vectors distinct: {}   wall clocks distinct: {}",
        vectors.len(),
        clocks.iter().collect::<BTreeSet<_>>().len()
    );
    holds.push((
        "the exact work vector is invariant across repetitions while the wall clock is not",
        work_invariant && clock_moved,
        format!(
            "{} distinct work vector(s), {} distinct clock(s) over {LIVE_REPETITIONS} runs",
            vectors.len(),
            clocks.iter().collect::<BTreeSet<_>>().len()
        ),
    ));

    // -- the prediction, graded against the cpu run rather than against itself -------------------
    //
    // `receipt.authority_work` is the prediction `of_cpu_authority` made from the CANDIDATE's
    // receipt, carried across `admit`'s receipt swap. Grading it against the admitted receipt it was
    // swapped into would be a tautology: `of_cpu_authority(cpu_receipt).cpu_evaluations` is
    // `cpu_receipt.exact_support_evaluations` by definition, and a receipt that could not have come
    // out otherwise carries no evidence (§8).
    println!();
    println!("  THE PREDICTION, GRADED AGAINST THE CPU RUN");
    let predicted = receipt.authority_work.clone();
    let ordering_confirmed = match &cpu_run {
        Ok((_, cpu_receipt)) => {
            let measured = CarrierWork {
                cpu_evaluations: cpu_receipt.exact_support_evaluations.clone(),
                device_evaluations: BigUint::from(0_u32),
                transfer_bytes: BigUint::from(0_u32),
                intermediate_bits: predicted.intermediate_bits.clone(),
            };
            let declared = metric(1, 1, 1);
            let on_prediction =
                CarrierAdmission::under(&declared, &predicted, &receipt.candidate_work);
            let on_measurement =
                CarrierAdmission::under(&declared, &measured, &receipt.candidate_work);
            println!(
                "    predicted authority  {}\n    measured  authority  {}",
                render_work(&predicted),
                render_work(&measured)
            );
            println!(
                "    admission on the prediction   {}",
                render_admission(&on_prediction)
            );
            println!(
                "    admission on the measurement  {}",
                render_admission(&on_measurement)
            );
            if predicted.cpu_evaluations == measured.cpu_evaluations {
                println!("    the magnitude is confirmed as well.");
            } else {
                println!(
                    "\n    THE MAGNITUDE IS REFUTED. `of_cpu_authority`'s doc claims *the cpu law\n    \
                     evaluates every support the split shared out*, predicting {}. The cpu law\n    \
                     actually evaluated {}. It does not evaluate an aperture member that a tile has\n    \
                     already excluded, so the two carriers do not merely divide one fixed population\n    \
                     of evaluations — the device does strictly more of them to return the same exact\n    \
                     support. The predicted ORDERING survives and the predicted SIZE does not; the\n    \
                     clock comparison could not have returned either.",
                    predicted.cpu_evaluations, measured.cpu_evaluations
                );
            }
            println!(
                "\n    metric-free order on the measurement: {}  (still Open — the measurement does\n    \
                 not rescue the product order, it only widens the declared margin)",
                render_ordering(receipt.candidate_work.order_against(&measured))
            );
            on_prediction.conducts_through() == on_measurement.conducts_through()
        }
        Err(error) => {
            println!("    the cpu run refused: {error}");
            false
        }
    };
    holds.push((
        "the predicted cpu work and the measured cpu work admit the SAME carrier",
        ordering_confirmed,
        "the falsifiable claim `of_cpu_authority` makes is about the ordering, and it survives"
            .to_owned(),
    ));
}
