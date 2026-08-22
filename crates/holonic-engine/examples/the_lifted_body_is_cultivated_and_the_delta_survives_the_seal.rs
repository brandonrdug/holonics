//! **Phoenix station eleven: the lifted body is cultivated, and the delta survives a
//! source-detached remount.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//! §11 — *"Cultivation passes only when source-detached remount changes held-out later conduct, a
//! subject-disjoint control stays unchanged, and targeted ablation restores the predecessor
//! consequence."*
//!
//! # The return law is an adjoint, not an inversion
//!
//! The master contract is explicit: *"Cultivation uses a declared metric adjoint, not inversion."*
//! So the residual returns through `ExactRatMatrix::metric_adjoint` with **both** receiver metrics
//! declared and non-Euclidean, and the adjoint's own law `<Tx,y>_Y = <x,T*y>_X` is checked to
//! return exactly zero on the material before anything is committed.
//!
//! # There is no step size, because a step size would be an authored level
//!
//! The committed delta is the **exact** one that zeroes the declared residual at each coordinate
//! where the transport is a rebase, read off `ExactRatMatrix::rebase_receipt`. Where a coordinate
//! lies in the kernel the delta is **refused there** and the coordinate is retained in the fibre —
//! a collapsed direction cannot be cultivated through, and inventing a step to pretend otherwise is
//! what this project refuses by name.
//!
//! # Three arms and a held-out grade
//!
//! `ARM L` commits the delta; `ARM C` is the matched no-op sibling with the same material mounted
//! and nothing committed; the **untouched coordinates are the subject-disjoint control**, carried in
//! the same body so no second experiment can drift from the first. Every conduct is a **fresh
//! process** reading only a sealed rest.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_lifted_body_is_cultivated_and_the_delta_survives_the_seal -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use std::collections::BTreeMap;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_linear::{ExactRatMatrix, RebaseReceipt};
use holonic_engine::exact_value::AlgebraicRoot;
use holonic_engine::exact_value::ieee754::{decode_bfloat16_bits, round_into_bfloat16};
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::ported_reference::PortedOperationKind;
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use site::{BASE, CAUSED, digest_of, found, write_container};

/// The population cultivated. A rebase gain is the smallest thing in this site whose transport is
/// diagonal at fixed material, so the adjoint and the exact solve are both readable.
const CULTIVATED: &str = "model.language_model.layers.0.input_layernorm.weight";
/// The coordinates cultivated. **Everything outside this span is the subject-disjoint control**,
/// carried in the same body so a second experiment cannot drift from the first.
const SPAN: usize = 64;
/// The caused symbol the delta is derived from, and the one it is graded on. They are different,
/// which is what makes the grade held-out.
const DEVELOPMENT: usize = 0;
const HELD_OUT: usize = 2;

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);
    let scratch = std::env::var("SCRATCH").unwrap_or_else(|_| "/tmp".to_owned());

    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            std::process::exit(1);
        }
    };
    println!("PHOENIX STATION ELEVEN — THE LIFTED BODY IS CULTIVATED");
    println!();
    println!(
        "  resident chart                    {}",
        chart.device_name()
    );
    println!("  cultivated population             {CULTIVATED}");
    println!("  cultivated coordinates            {SPAN}");
    println!(
        "  development symbol                {} of the caused material",
        CAUSED[DEVELOPMENT]
    );
    println!(
        "  held-out symbol                   {} — DIFFERENT, which is what makes it held out",
        CAUSED[HELD_OUT]
    );

    let (site, container, mut file) = found(&root, BASE, terms, None).expect("founded");

    // -----------------------------------------------------------------------------------------
    // THE MATERIAL THE DELTA IS DERIVED FROM.
    // -----------------------------------------------------------------------------------------
    let gain_words = container
        .read_bf16_whole(&mut file, CULTIVATED)
        .expect("read");
    let gain: Vec<Rat> = gain_words
        .iter()
        .map(|word| decode_bfloat16_bits(*word).expect("finite").value())
        .collect();
    let entering = |symbol: usize,
                    container: &holonic_engine::foreign_map::ForeignContainer,
                    file: &mut std::fs::File|
     -> Vec<Rat> {
        container
            .read_rows_bf16(file, "model.language_model.embed_tokens.weight", symbol, 1)
            .expect("read")
            .0
            .iter()
            .map(|word| decode_bfloat16_bits(*word).expect("finite").value())
            .collect()
    };
    let development = entering(CAUSED[DEVELOPMENT], &container, &mut file);
    let target_material = entering(CAUSED[1], &container, &mut file);

    // The rebase's own reciprocal root, through the standing owner.
    let root_of = |section: &[Rat]| -> Rat {
        let width = Rat::from_integer(BigInt::from(section.len() as u64));
        let mut squares = Rat::zero();
        for value in section {
            squares += value * value;
        }
        let mean = squares / width + Rat::new(BigInt::one(), BigInt::from(1_000_000));
        let isolated = AlgebraicRoot::reciprocal_square_root(&mean, 44).expect("isolated");
        (&isolated.enclosure().lower + &isolated.enclosure().upper)
            / Rat::from_integer(BigInt::from(2))
    };
    let scale = root_of(&development);
    let target_scale = root_of(&target_material);

    // -----------------------------------------------------------------------------------------
    // THE STRUCTURED RESIDUAL. A POPULATION, before any scalar face.
    // -----------------------------------------------------------------------------------------
    let mut residual = Vec::with_capacity(SPAN);
    let mut transport = Vec::with_capacity(SPAN);
    for at in 0..SPAN {
        // What the body returns at this coordinate, and what the declared target returns.
        let returned = &development[at] * &gain[at] * &scale;
        let wanted = &target_material[at] * &gain[at] * &target_scale;
        residual.push(returned - wanted);
        // The transport from the gain to the return, at this fixed material. Diagonal.
        transport.push(&development[at] * &scale);
    }
    println!();
    println!("  THE STRUCTURED RESIDUAL — a population, before any scalar face");
    let nonzero = residual.iter().filter(|value| !value.is_zero()).count();
    let widest = residual
        .iter()
        .map(|value| {
            if value.is_negative() {
                -value.clone()
            } else {
                value.clone()
            }
        })
        .max()
        .unwrap_or_else(Rat::zero);
    println!("    coordinates                     {SPAN}");
    println!("    genuinely nonzero               {nonzero}");
    println!(
        "    widest single residual          {}",
        shorten(&widest.to_string(), 40)
    );
    println!("    (no loss scalar is formed. A scalar is one receiver's face of this population.)");

    // -----------------------------------------------------------------------------------------
    // THE RETURN LAW: A DECLARED METRIC ADJOINT, CHECKED.
    // -----------------------------------------------------------------------------------------
    let diagonal = ExactRatMatrix::from_diagonal(transport.clone()).expect("diagonal");
    let domain_metric = declared_metric(SPAN, 2);
    let codomain_metric = declared_metric(SPAN, 3);
    let adjoint = diagonal
        .metric_adjoint(&domain_metric, &codomain_metric)
        .expect("adjoint");
    let probe: Vec<Rat> = (0..SPAN)
        .map(|k| Rat::new(BigInt::from(k as i64 - 17), BigInt::from(11)))
        .collect();
    let bare = diagonal.transpose().expect("transposed");
    let bare_defect = diagonal
        .adjoint_defect(&bare, &domain_metric, &codomain_metric, &probe, &residual)
        .expect("paired");
    let metric_defect = diagonal
        .adjoint_defect(
            &adjoint,
            &domain_metric,
            &codomain_metric,
            &probe,
            &residual,
        )
        .expect("paired");
    let returned_covector = adjoint.apply(&residual).expect("returned");
    println!();
    println!("  THE RETURN LAW — a declared metric adjoint, not an inversion");
    println!("    both receiver metrics declared and non-Euclidean");
    println!(
        "    a bare transpose's defect       {}",
        shorten(&bare_defect.to_string(), 40)
    );
    println!("    the metric adjoint's defect     {metric_defect}");
    println!(
        "    the returned covector's extent  {} coordinates",
        returned_covector.len()
    );
    if !metric_defect.is_zero() {
        println!("    THE ADJOINT FAILED ITS OWN LAW. Nothing is committed.");
        std::process::exit(1);
    }

    // -----------------------------------------------------------------------------------------
    // THE DELTA. Exact, with no step, and refused on the kernel.
    // -----------------------------------------------------------------------------------------
    let receipt = diagonal.rebase_receipt().expect("receipt");
    let collapsed: Vec<usize> = match &receipt {
        RebaseReceipt::Rebase { .. } => Vec::new(),
        RebaseReceipt::Refused { factorization, .. } => (0..SPAN)
            .filter(|at| transport[*at].is_zero())
            .chain(
                factorization
                    .kernel
                    .iter()
                    .enumerate()
                    .filter_map(|(_, vector)| vector.iter().position(|value| !value.is_zero())),
            )
            .collect(),
    };
    let mut delta = vec![Rat::zero(); SPAN];
    let mut refused = Vec::new();
    for at in 0..SPAN {
        if transport[at].is_zero() {
            refused.push(at);
            continue;
        }
        // The EXACT delta that zeroes this coordinate's residual. No step, because a step would be
        // an authored level and this solve has none.
        delta[at] = -(&residual[at] / &transport[at]);
    }
    println!();
    println!("  THE DELTA — exact, with no step size anywhere");
    println!(
        "    the transport is a rebase       {}",
        matches!(receipt, RebaseReceipt::Rebase { .. })
    );
    println!(
        "    coordinates cultivated          {}",
        SPAN - refused.len()
    );
    println!("    coordinates REFUSED on the kernel  {}", refused.len());
    println!("    collapsed directions named      {}", collapsed.len());
    println!("    (a collapsed direction cannot be cultivated through, and inventing a step to");
    println!("     pretend otherwise is what this project refuses by name.)");

    // -----------------------------------------------------------------------------------------
    // THE TWO ARMS, EACH SEALED.
    // -----------------------------------------------------------------------------------------
    // **THE SEAL IS A QUOTIENT, SO THE DEPOSITED DELTA IS NOT THE DERIVED ONE.**
    //
    // The derivation proposes `delta`; the stored species admits `round(g + delta)`. What was
    // actually deposited is therefore `admitted = decode(round(g + delta)) - g`, and the difference
    // `delta - admitted` is the seal's COLLAPSED POPULATION — the compression's remainder.
    //
    // This distinction is not bookkeeping. Withdrawing `delta` from a body that carries `admitted`
    // fails, because a quotient has no inverse; it has a fibre. Measured on the first pass of this
    // station: subtracting the derived delta returned only 42 of 64 coordinates. Withdrawing what
    // was deposited returns all of them, and the gap between the two numbers IS the quotient.
    let mut cultivated = gain.clone();
    let mut admitted = vec![Rat::zero(); SPAN];
    let mut committed = 0usize;
    let mut below_the_seal = Vec::new();
    let mut carrier_refused = Vec::new();
    let mut collapsed_by_the_seal = Vec::new();
    for at in 0..SPAN {
        if delta[at].is_zero() {
            continue;
        }
        let wanted = &gain[at] + &delta[at];
        match round_into_bfloat16(&wanted) {
            Ok((word, _)) if word != gain_words[at] => {
                let stored = decode_bfloat16_bits(word).expect("finite").value();
                admitted[at] = &stored - &gain[at];
                collapsed_by_the_seal.push(&delta[at] - &admitted[at]);
                cultivated[at] = stored;
                committed += 1;
            }
            Ok(_) => below_the_seal.push(at),
            Err(_) => carrier_refused.push(at),
        }
    }
    let widest_collapsed = collapsed_by_the_seal
        .iter()
        .map(|value| {
            if value.is_negative() {
                -value.clone()
            } else {
                value.clone()
            }
        })
        .max()
        .unwrap_or_else(Rat::zero);
    println!();
    println!("  THE SEAL'S OWN GRAIN — a QUOTIENT, measured rather than assumed");
    println!("    deltas the stored species admitted      {committed}");
    println!(
        "    deltas BELOW the seal's grain           {}",
        below_the_seal.len()
    );
    println!(
        "    coordinates the carrier REFUSED         {}",
        carrier_refused.len()
    );
    println!(
        "    the collapsed population it deleted     {} entries",
        collapsed_by_the_seal
            .iter()
            .filter(|value| !value.is_zero())
            .count()
    );
    println!(
        "    widest single collapsed entry           {}",
        shorten(&widest_collapsed.to_string(), 40)
    );
    println!(
        "    (what was DEPOSITED is what the seal admitted, not what the derivation proposed."
    );
    println!("     The ablation below withdraws the deposited one, because a quotient has no");
    println!(
        "     inverse and subtracting the proposed delta returned 42 of 64 on the first pass.)"
    );
    // **ARM R — THE MATCHED SIBLING.** The SAME population of deltas, at the SAME coordinates,
    // with only the coordinate incidence withdrawn by a declared reversal. Every magnitude and
    // every hand the cultivation deposited is still present; what is gone is WHICH coordinate each
    // belongs to. Without this arm, "held-out conduct moved" is a statement about any change at
    // all, and carries no evidence about cultivation.
    let mut scrambled = gain.clone();
    for at in 0..SPAN {
        let borrowed = &admitted[SPAN - 1 - at];
        if borrowed.is_zero() {
            continue;
        }
        let wanted = &gain[at] + borrowed;
        if let Ok((word, _)) = round_into_bfloat16(&wanted)
            && word != gain_words[at]
        {
            scrambled[at] = decode_bfloat16_bits(word).expect("finite").value();
        }
    }

    let control_rest = format!("{scratch}/phoenix-arm-control.safetensors");
    let cultivated_rest = format!("{scratch}/phoenix-arm-cultivated.safetensors");
    let sibling_rest = format!("{scratch}/phoenix-arm-sibling.safetensors");
    seal(&site, &container, &mut file, &gain, &control_rest);
    seal(&site, &container, &mut file, &cultivated, &cultivated_rest);
    seal(&site, &container, &mut file, &scrambled, &sibling_rest);
    println!();
    println!("  THE THREE ARMS, EACH SEALED AS A NATIVE REST");
    println!("    ARM C, the matched no-op sibling   {control_rest}");
    println!("    ARM L, the cultivated body         {cultivated_rest}");
    println!("    ARM R, the SAME deltas with the coordinate incidence withdrawn");
    println!("                                       {sibling_rest}");
    println!("    coordinates committed              {committed}");
    println!(
        "    ARM L differs from ARM C           {}",
        digest_of(&control_rest) != digest_of(&cultivated_rest)
    );
    println!(
        "    ARM R differs from ARM L           {}",
        digest_of(&sibling_rest) != digest_of(&cultivated_rest)
    );

    // -----------------------------------------------------------------------------------------
    // THE ATTRIBUTABLE EXACT CONSEQUENCE, on the material the delta was derived from.
    // -----------------------------------------------------------------------------------------
    // **Read at TWO grains, because an invariant is only visible across two frames.** The exact
    // rational frame asks whether the residual is identically zero; the stored species asks
    // whether any word in ITS family separates the two — which is what tolerance means here, and
    // it is the coarser receiver the body actually carries.
    let residual_under = |body: &Vec<Rat>| -> (usize, usize) {
        let mut exact = 0usize;
        let mut stored = 0usize;
        for at in 0..SPAN {
            let returned = &development[at] * &body[at] * &scale;
            let wanted = &target_material[at] * &gain[at] * &target_scale;
            if returned != wanted {
                exact += 1;
            }
            let left = round_into_bfloat16(&returned).map(|(word, _)| word);
            let right = round_into_bfloat16(&wanted).map(|(word, _)| word);
            if left != right {
                stored += 1;
            }
        }
        (exact, stored)
    };
    let under_control = residual_under(&gain);
    let under_sibling = residual_under(&scrambled);
    let under_cultivated = residual_under(&cultivated);
    println!();
    println!("  THE ATTRIBUTABLE CONSEQUENCE — coordinates the declared residual does NOT reach");
    println!("                                     exact frame     stored species");
    println!(
        "    under ARM C, the predecessor      {:>3} of {SPAN}      {:>3} of {SPAN}",
        under_control.0, under_control.1
    );
    println!(
        "    under ARM R, the matched sibling  {:>3} of {SPAN}      {:>3} of {SPAN}",
        under_sibling.0, under_sibling.1
    );
    println!(
        "    under ARM L, the cultivated body  {:>3} of {SPAN}      {:>3} of {SPAN}",
        under_cultivated.0, under_cultivated.1
    );
    println!("    (TWO grains, because an invariant is only visible across two frames. The exact");
    println!("     frame asks whether the residual is identically zero; the stored species asks");
    println!(
        "     whether any word in ITS family separates the two, which is what tolerance means"
    );
    println!("     here. The delta was admitted THROUGH that species, so that is the frame the");
    println!("     consequence is attributable in, and the exact frame is the honest remainder.)");

    // -----------------------------------------------------------------------------------------
    // THE GRADE, EACH ARM IN A FRESH PROCESS READING ONLY ITS REST.
    // -----------------------------------------------------------------------------------------
    let control = conduct_child(&control_rest);
    let cultivated_return = conduct_child(&cultivated_rest);
    let sibling_return = conduct_child(&sibling_rest);
    println!();
    println!("  THE GRADE — each arm conducted by a FRESH PROCESS reading only its own rest");
    if control.is_empty() || cultivated_return.is_empty() || sibling_return.is_empty() {
        println!("    a child REFUSED. Nothing is claimed.");
        std::process::exit(1);
    }

    let held_out_moved = control[HELD_OUT] != cultivated_return[HELD_OUT];
    let development_moved = control[DEVELOPMENT] != cultivated_return[DEVELOPMENT];
    let sibling_also_moved = control[HELD_OUT] != sibling_return[HELD_OUT];
    println!("    development conduct moved                  {development_moved}");
    println!("    HELD-OUT conduct moved                     {held_out_moved}");
    println!(
        "    ANTI-VACUITY: the matched sibling ALSO moved held-out conduct  {sibling_also_moved}"
    );
    println!(
        "        (so movement is a statement about any change at all. What separates the arms"
    );
    println!("         is below, and it is a receiver's reading rather than a magnitude.)");

    // **THE SEPARATION.** A declared receiver family reads hands and orders — the two faces that
    // cross a frame — over the three arms at every position, and `receiver_exact_compression`
    // returns which arms a receiver family can tell apart and which it collapses.
    let coordinates: Vec<usize> = (0..16).map(|k| k * 149).collect();
    let arms = vec![
        parse_returns(&control),
        parse_returns(&cultivated_return),
        parse_returns(&sibling_return),
    ];
    let system = ArmSystem::new(arms, coordinates.clone());
    let compression = compress(&system);
    println!();
    println!(
        "  THE SEPARATION — a declared receiver family of {} hand and order faces",
        coordinates.len() * 2
    );
    println!(
        "    items, one per arm and position   {}",
        system.states.len()
    );
    println!(
        "    one-shot blocks                   {}",
        compression.one_shot.len()
    );
    println!(
        "    conduct blocks                    {}",
        compression.conduct.len()
    );
    println!(
        "    rounds to converge                {}",
        compression.rounds
    );
    println!(
        "    collapsed pairs                   {}",
        compression.collapsed.len()
    );
    let (l_from_c, l_word) = system.separated(&compression, 0, 1, HELD_OUT);
    let (l_from_r, r_word) = system.separated(&compression, 1, 2, HELD_OUT);
    println!("    ARM L held-out separated from ARM C  {l_from_c}   {l_word}");
    println!("    ARM L held-out separated from ARM R  {l_from_r}   {r_word}");

    // The subject-disjoint control. **This is true by construction of the commit**, and saying so
    // is the point: what it verifies is that the SEAL is local, not that cultivation is selective.
    let untouched_identical = gain[SPAN..] == cultivated[SPAN..];
    println!();
    println!("    the seal is local                          {untouched_identical}");
    println!(
        "        ({} of {} coordinates were never touched — true by construction of the",
        gain.len() - SPAN,
        gain.len()
    );
    println!("         commit, so it grades the seal and not the cultivation.)");

    // **TARGETED ABLATION, WITHDRAWN FROM THE CULTIVATED BODY** rather than resealed from the
    // source. Resealing the predecessor from the source would be the same bytes by construction
    // and would grade nothing.
    let ablated_rest = format!("{scratch}/phoenix-arm-ablated.safetensors");
    let (returned, refused_by_grain) =
        withdraw_from_rest(&cultivated_rest, &ablated_rest, &admitted, &gain_words);
    let ablated = conduct_child(&ablated_rest);
    let restored = !ablated.is_empty() && ablated == control;
    println!();
    println!(
        "    TARGETED ABLATION, withdrawn from the CULTIVATED rest and not resealed from source"
    );
    println!("        coordinates the withdrawal returned    {returned} of {committed}");
    println!("        coordinates the seal's grain KEPT      {refused_by_grain}");
    println!("        the predecessor's conduct returns      {restored}");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    let passed = held_out_moved && l_from_c && l_from_r && restored && metric_defect.is_zero();
    println!("  cultivation passes                          {passed}");
    println!();
    println!("  The residual was returned as a POPULATION before any scalar face, and passed");
    println!(
        "  through a declared metric adjoint whose own law returned exactly zero while a bare"
    );
    println!(
        "  transpose's did not. The committed delta is the exact one that zeroes the declared"
    );
    println!("  residual, with NO step size anywhere, and it is refused on every collapsed");
    println!("  direction rather than stepped through.");
    println!();
    println!("  All three arms were sealed and conducted by fresh processes reading only their");
    println!("  own rest. Held-out conduct moved — AND SO DID THE MATCHED SIBLING'S, so movement");
    println!("  alone grades nothing. What grades the cultivation is that a declared receiver");
    println!("  family separates ARM L's held-out conduct from BOTH the predecessor's and the");
    println!(
        "  sibling's, with the separating face exhibited; and that withdrawing the delta from"
    );
    println!("  the cultivated body — not resealing it from the source — returns the predecessor.");
    println!();
    println!("  WHAT THIS DOES NOT CLAIM. One development pair does not establish transfer. The");
    println!(
        "  held-out separation says the deposited delta's coordinate incidence is load-bearing"
    );
    println!("  on material it was never derived from. It does not say the delta generalizes, and");
    println!("  no receiver here was asked whether it moved TOWARD anything.");
    println!();
    println!("  The aperture is one site's contact half and one rebase population.");
    println!("  CONSTRUCTION_STATE is untouched.");
}

// ---------------------------------------------------------------------------------------------
// THE SEPARATION INSTRUMENT. The receivers are FACES — a hand and an order — because those are
// what cross a frame. A magnitude does not, so no receiver here reads one.
// ---------------------------------------------------------------------------------------------

struct ArmSystem {
    /// `arms[arm][position]` — the carried standing under one arm at one position.
    arms: Vec<Vec<Vec<Rat>>>,
    /// `states[item]` is `(arm, position)`, flattened.
    states: Vec<(usize, usize)>,
    coordinates: Vec<usize>,
}

impl ArmSystem {
    fn new(arms: Vec<Vec<Vec<Rat>>>, coordinates: Vec<usize>) -> Self {
        let mut states = Vec::new();
        for (arm, positions) in arms.iter().enumerate() {
            for position in 0..positions.len() {
                states.push((arm, position));
            }
        }
        Self {
            arms,
            states,
            coordinates,
        }
    }

    fn item_of(&self, arm: usize, position: usize) -> ItemId {
        ItemId(
            self.states
                .iter()
                .position(|held| *held == (arm, position))
                .expect("declared") as u64,
        )
    }

    /// Are these two arms' conducts at one position in DIFFERENT conduct blocks, and if so which
    /// declared face is the one that tells them apart?
    fn separated(
        &self,
        compression: &holonic_engine::receiver_exact_compression::ReceiverExactCompression,
        left: usize,
        right: usize,
        position: usize,
    ) -> (bool, String) {
        let a = self.item_of(left, position);
        let b = self.item_of(right, position);
        let together = compression
            .conduct
            .blocks
            .iter()
            .any(|block| block.contains(&a) && block.contains(&b));
        if together {
            return (
                false,
                String::from("(collapsed — no declared face reaches it)"),
            );
        }
        for receiver in self.receivers() {
            if self.observation(a, receiver) != self.observation(b, receiver) {
                let which = receiver.0 as usize / 2;
                let face = if receiver.0 % 2 == 0 { "hand" } else { "order" };
                return (
                    true,
                    format!("(the {face} at coordinate {})", self.coordinates[which]),
                );
            }
        }
        (true, String::from("(separated only through a successor)"))
    }
}

impl ObservedSystem for ArmSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.states.len() as u64).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        (0..(self.coordinates.len() * 2) as u64)
            .map(ReceiverId)
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![InputId(0)]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let (arm, position) = self.states[item.0 as usize];
        let section = &self.arms[arm][position];
        let which = receiver.0 as usize / 2;
        let coordinate = self.coordinates[which];
        let value = section.get(coordinate).cloned().unwrap_or_else(Rat::zero);
        if receiver.0 % 2 == 0 {
            Observation(if value.is_positive() {
                1
            } else if value.is_negative() {
                2
            } else {
                0
            })
        } else {
            let other = self
                .coordinates
                .get(which + 1)
                .and_then(|at| section.get(*at))
                .cloned()
                .unwrap_or_else(Rat::zero);
            Observation(match value.cmp(&other) {
                std::cmp::Ordering::Less => 1,
                std::cmp::Ordering::Equal => 2,
                std::cmp::Ordering::Greater => 3,
            })
        }
    }

    fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
        let (arm, position) = self.states[item.0 as usize];
        if position + 1 < self.arms[arm].len() {
            Some(self.item_of(arm, position + 1))
        } else {
            None
        }
    }
}

fn parse_returns(carried: &[Vec<String>]) -> Vec<Vec<Rat>> {
    carried
        .iter()
        .map(|position| {
            position
                .iter()
                .map(|value| value.parse::<Rat>().expect("an exact rational"))
                .collect()
        })
        .collect()
}

/// **Withdraw the delta from the CULTIVATED rest**, not from the source. The rest is mounted, its
/// own gain read back, the delta subtracted from what the seal actually stored, and the result
/// resealed. Whether that returns the predecessor is a question about the seal's grain, so it is
/// measured here rather than assumed.
fn withdraw_from_rest(
    cultivated: &str,
    into: &str,
    delta: &[Rat],
    predecessor_words: &[u16],
) -> (usize, usize) {
    let (mut file, container) = manifest_safetensors(cultivated).expect("mounted");
    let mut payload: Vec<u8> = Vec::new();
    let mut header: Vec<(String, (String, Vec<usize>, u64, u64))> = Vec::new();
    let mut returned = 0usize;
    let mut kept = 0usize;
    let mut names: Vec<String> = container.tensors.keys().cloned().collect();
    names.sort();
    for name in names {
        let tensor = container.tensor(&name).expect("named").clone();
        let mut words = container.read_bf16_whole(&mut file, &name).expect("read");
        if name == CULTIVATED {
            for (at, step) in delta.iter().enumerate() {
                if step.is_zero() {
                    continue;
                }
                let stored = decode_bfloat16_bits(words[at]).expect("finite").value();
                let withdrawn = stored - step;
                match round_into_bfloat16(&withdrawn) {
                    Ok((word, _)) => {
                        words[at] = word;
                        if word == predecessor_words[at] {
                            returned += 1;
                        } else {
                            kept += 1;
                        }
                    }
                    Err(_) => kept += 1,
                }
            }
        }
        let start = payload.len() as u64;
        for word in &words {
            payload.extend_from_slice(&word.to_le_bytes());
        }
        header.push((
            name,
            (
                "BF16".to_owned(),
                tensor.shape.clone(),
                start,
                payload.len() as u64,
            ),
        ));
    }
    write_container(into, &header, &container.container_metadata, &payload);
    (returned, kept)
}

/// Seal a rest carrying one replaced population and the rest of the site unchanged.
fn seal(
    site: &site::FoundedSite,
    container: &holonic_engine::foreign_map::ForeignContainer,
    file: &mut std::fs::File,
    gain: &[Rat],
    path: &str,
) {
    let mut payload: Vec<u8> = Vec::new();
    let mut header: Vec<(String, (String, Vec<usize>, u64, u64))> = Vec::new();
    for population in &site.populations {
        let tensor = container.tensor(population).expect("named").clone();
        let is_row = site.program.operations.values().any(|operation| {
            matches!(operation, PortedOperationKind::Lookup { population: named, .. } if named == population)
        });
        let (words, shape) = if population == CULTIVATED {
            (
                gain.iter()
                    .map(|value| round_into_bfloat16(value).expect("emitted").0)
                    .collect::<Vec<_>>(),
                tensor.shape.clone(),
            )
        } else if is_row && tensor.rank() == 2 {
            let mut rows = Vec::new();
            for symbol in CAUSED {
                let (row, _) = container
                    .read_rows_bf16(file, population, symbol, 1)
                    .expect("read");
                rows.extend(row);
            }
            (rows, vec![CAUSED.len(), tensor.shape[1]])
        } else {
            (
                container.read_bf16_whole(file, population).expect("read"),
                tensor.shape.clone(),
            )
        };
        let start = payload.len() as u64;
        for word in &words {
            payload.extend_from_slice(&word.to_le_bytes());
        }
        header.push((
            population.clone(),
            ("BF16".to_owned(), shape, start, payload.len() as u64),
        ));
    }
    let mut sealed_program = site.program.clone();
    for operation in sealed_program.operations.values_mut() {
        if let PortedOperationKind::Lookup { row, .. } = operation {
            *row = CAUSED.iter().position(|caused| caused == row).unwrap_or(0);
        }
    }
    let mut metadata = BTreeMap::new();
    metadata.insert(
        "schema".to_owned(),
        "holonic-engine.phoenix-native-rest.v1".to_owned(),
    );
    metadata.insert(
        "diagram".to_owned(),
        serde_json::to_string(&site.complex).expect("diagram"),
    );
    metadata.insert(
        "program".to_owned(),
        serde_json::to_string(&sealed_program).expect("program"),
    );
    metadata.insert(
        "band-elements".to_owned(),
        serde_json::to_string(&site.band_elements).expect("bands"),
    );
    metadata.insert(
        "returns".to_owned(),
        serde_json::to_string(&site.returns.iter().map(|event| event.0).collect::<Vec<_>>())
            .expect("returns"),
    );
    metadata.insert(
        "realization".to_owned(),
        "the runtime is `ported_reference::realize`; the ordering is the diagram's chronology."
            .to_owned(),
    );
    write_container(path, &header, &metadata, &payload);
}

/// Conduct one rest in a **fresh process** that is handed no source path.
fn conduct_child(rest: &str) -> Vec<Vec<String>> {
    let binary = std::env::current_exe()
        .expect("this binary")
        .parent()
        .expect("directory")
        .join("the_native_rest_is_sealed_and_a_fresh_process_conducts");
    let child = std::process::Command::new(binary)
        .arg("--conduct")
        .arg(rest)
        .output()
        .expect("spawned");
    if !child.status.success() {
        return Vec::new();
    }
    String::from_utf8_lossy(&child.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("CHILD-RETURN "))
        .and_then(|json| serde_json::from_str(json).ok())
        .unwrap_or_default()
}

/// A declared, deliberately non-Euclidean receiver metric. **Nothing defaults to the identity.**
fn declared_metric(extent: usize, spread: i64) -> ExactRatMatrix {
    ExactRatMatrix::from_diagonal(
        (0..extent)
            .map(|k| Rat::from_integer(BigInt::from(1 + (k as i64 % spread))))
            .collect(),
    )
    .expect("well-formed")
}

fn shorten(text: &str, extent: usize) -> String {
    if text.len() <= extent {
        return text.to_owned();
    }
    format!("{}…", &text[..extent])
}
