use super::*;

// --- the atlas -------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BandReceipt {
    pub ordinal: usize,
    /// The base config with its Euler--Maclaurin start **derived** from this band's receiver box:
    /// the least start whose certified remainder is under `2^-grain_bits`. Re-derived and required
    /// equal on verification, so the level is checkable rather than declared.
    pub config: ExactSeriesConfig,
    pub winding: WindingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RefinementStep {
    pub grain: u32,
    pub split: Rat,
    pub left: WindingReceipt,
    pub right: WindingReceipt,
    pub selected: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ZeroLineage {
    pub ordinal: usize,
    /// The root band's derived config, carried by every refinement and the midpoint current.
    pub config: ExactSeriesConfig,
    pub root: WindingReceipt,
    pub refinements: Vec<RefinementStep>,
    pub final_receiver: ComplexReceiverBox,
    pub midpoint_current: EtaCurrentReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntervalRelation {
    pub kind: String,
    pub members: Vec<usize>,
    pub value: RatInterval,
    pub common_continued_fraction: Vec<BigInt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReciprocalMoment {
    pub order: u32,
    pub value: RatInterval,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaRatioAtlas {
    pub schema: String,
    pub arithmetic: String,
    pub source_function: String,
    pub receiver_law: String,
    pub symmetry_read: String,
    /// Which apparatus supplied the boundary jets. Testimony about the realization; the receipts
    /// verify under one law whichever it was.
    pub apparatus: String,
    pub scan: ComplexReceiverBox,
    /// The base config. Its `euler_maclaurin_start` is not used by any band; each derives its own.
    pub config: ExactSeriesConfig,
    /// The one declared receiver coordinate of the derivation.
    pub grain_bits: u32,
    pub max_depth: u32,
    pub physical_workers: usize,
    pub elapsed_milliseconds: u64,
    pub bands: Vec<BandReceipt>,
    pub zero_lineages: Vec<ZeroLineage>,
    pub interval_relations: Vec<IntervalRelation>,

    pub reciprocal_moments: Vec<ReciprocalMoment>,
}

pub fn receiver_band(tau: RatInterval) -> ComplexReceiverBox {
    ComplexReceiverBox::new(RatInterval::new(rat(2, 5), rat(3, 5)), tau)
}

/// The atlas's base config, unchanged since 2026-08-08 except that its start is now derived.
pub fn atlas_base_config() -> ExactSeriesConfig {
    ExactSeriesConfig {
        dyadic_bits: 96,
        euler_maclaurin_start: 12,
        euler_maclaurin_order: 10,
        log_terms: 28,
        exponential_terms: 18,
        trigonometric_terms: 16,
    }
}

/// Run `work` over `items` on `workers` threads, each owning one mounted source.
pub(super) fn pooled<J, M, T, R, W>(
    items: Vec<T>,
    workers: usize,
    mount: &M,
    work: W,
) -> Result<Vec<R>, String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
    T: Send + Sync,
    R: Send,
    W: Fn(&mut J, &T) -> Result<R, String> + Sync,
{
    let items = Arc::new(items);
    let next = Arc::new(AtomicUsize::new(0));
    let (sender, receiver_channel) = mpsc::channel::<(usize, Result<R, String>)>();
    let workers = workers.max(1).min(items.len().max(1));
    thread::scope(|scope| {
        for _ in 0..workers {
            let items = Arc::clone(&items);
            let next = Arc::clone(&next);
            let sender = sender.clone();
            let work = &work;
            scope.spawn(move || {
                let mut source = match mount() {
                    Ok(source) => source,
                    Err(error) => {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let _ = sender.send((index, Err(format!("mount failed: {error}"))));
                        return;
                    }
                };
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(item) = items.get(index) else {
                        break;
                    };
                    let result = work(&mut source, item);
                    if sender.send((index, result)).is_err() {
                        break;
                    }
                }
            });
        }
    });
    drop(sender);
    let mut collected: Vec<Option<R>> = (0..items.len()).map(|_| None).collect();
    for (index, result) in receiver_channel {
        if index < collected.len() {
            collected[index] = Some(result?);
        } else {
            result?;
        }
    }
    collected
        .into_iter()
        .enumerate()
        .map(|(index, slot)| slot.ok_or_else(|| format!("item {index} returned nothing")))
        .collect()
}

pub fn scan_integer_bands<J, M>(
    lower: i64,
    upper: i64,
    workers: usize,
    config: &ExactSeriesConfig,
    grain_bits: u32,
    max_depth: u32,
    mount: &M,
) -> Result<Vec<BandReceipt>, String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
{
    let bands: Vec<i64> = (lower..upper).collect();
    pooled(bands, workers, mount, |source: &mut J, &tau_lower: &i64| {
        let band_receiver =
            receiver_band(RatInterval::new(integer(tau_lower), integer(tau_lower + 1)));
        let band_config = derive_euler_maclaurin_start(&band_receiver, config, grain_bits)
            .map_err(|error| format!("band [{tau_lower},{}] start: {error}", tau_lower + 1))?;
        let winding = boundary_winding(source, Field::Eta, &band_receiver, &band_config, max_depth)
            .map_err(|error| format!("band [{tau_lower},{}] failed: {error}", tau_lower + 1))?;
        Ok(BandReceipt {
            ordinal: (tau_lower - lower) as usize,
            config: band_config,
            winding,
        })
    })
}

/// Refine one root into its lineages.
///
/// A band whose boundary winds `k` times holds `k` zeros. The descent splits along the cut; a
/// split whose children both wind is a **separation** and the lineage branches, each child
/// carrying the shared history with its own selection; a child that winds once continues as a
/// single closure until `grains` refinements stand. Every lineage returned ends at a box of
/// winding one, and there are exactly `k` of them.
#[allow(clippy::too_many_arguments)]
pub(super) fn descend<J: HeadSource + ?Sized>(
    source: &mut J,
    root: &WindingReceipt,
    current: WindingReceipt,
    history: Vec<RefinementStep>,
    grains: u32,
    separation_limit: u32,
    config: &ExactSeriesConfig,
    max_depth: u32,
    ordinal: usize,
    out: &mut Vec<ZeroLineage>,
) -> Result<(), String> {
    if current.winding < 1 {
        return Err(format!(
            "lineage {ordinal}: descended into a box of winding {}",
            current.winding
        ));
    }
    let steps = history.len() as u32;
    if current.winding == 1 && steps >= grains {
        let final_receiver = current.receiver.clone();
        let midpoint_current =
            eta_partial_current(rat(1, 2), final_receiver.tau.midpoint(), 96, config)
                .map_err(|error| format!("lineage {ordinal} current failed: {error}"))?;
        out.push(ZeroLineage {
            ordinal,
            config: config.clone(),
            root: root.clone(),
            refinements: history,
            final_receiver,
            midpoint_current,
        });
        return Ok(());
    }
    if steps >= grains.saturating_add(separation_limit) {
        return Err(format!(
            "lineage {ordinal}: {} closures were not separated within {separation_limit} splits beyond the grains",
            current.winding,
        ));
    }
    let lower = current.receiver.tau.lower.clone();
    let upper = current.receiver.tau.upper.clone();
    let extent = &upper - &lower;
    let candidate_splits = [rat(1, 2), rat(2, 5), rat(3, 5)];
    let mut chosen: Option<(Rat, WindingReceipt, WindingReceipt)> = None;
    let mut fallback: Option<(Rat, WindingReceipt, WindingReceipt)> = None;
    for fraction in &candidate_splits {
        let split = &lower + &extent * fraction;
        let Ok((left, right)) =
            split_winding(source, Field::Eta, &current, &split, config, max_depth)
        else {
            continue;
        };
        if left.winding < 0 || right.winding < 0 || left.winding + right.winding != current.winding
        {
            continue;
        }
        if current.winding == 1 {
            if matches!((left.winding, right.winding), (1, 0) | (0, 1)) {
                chosen = Some((split, left, right));
                break;
            }
            continue;
        }
        if left.winding > 0 && right.winding > 0 {
            chosen = Some((split, left, right));
            break;
        }
        if fallback.is_none() {
            fallback = Some((split, left, right));
        }
    }
    let Some((split, left, right)) = chosen.or(fallback) else {
        return Err(format!(
            "lineage {ordinal} could not certify a lawful split at step {}",
            steps + 1
        ));
    };
    for (child, selected) in [(&left, "left"), (&right, "right")] {
        if child.winding == 0 {
            continue;
        }
        let mut next = history.clone();
        next.push(RefinementStep {
            grain: steps + 1,
            split: split.clone(),
            left: left.clone(),
            right: right.clone(),
            selected: selected.to_owned(),
        });
        descend(
            source,
            root,
            child.clone(),
            next,
            grains,
            separation_limit,
            config,
            max_depth,
            ordinal,
            out,
        )?;
    }
    Ok(())
}

pub fn refine_root<J: HeadSource + ?Sized>(
    source: &mut J,
    ordinal: usize,
    root: WindingReceipt,
    grains: u32,
    separation_limit: u32,
    config: &ExactSeriesConfig,
    max_depth: u32,
) -> Result<Vec<ZeroLineage>, String> {
    if root.winding < 1 {
        return Err(format!(
            "lineage {ordinal} cannot refine winding {}",
            root.winding
        ));
    }
    let mut out = Vec::new();
    descend(
        source,
        &root,
        root.clone(),
        Vec::new(),
        grains,
        separation_limit,
        config,
        max_depth,
        ordinal,
        &mut out,
    )?;
    if out.len() != root.winding as usize {
        return Err(format!(
            "lineage {ordinal}: winding {} returned {} closures",
            root.winding,
            out.len()
        ));
    }
    Ok(out)
}

pub fn refine_lineages<J, M>(
    roots: Vec<(usize, WindingReceipt, ExactSeriesConfig)>,
    grains: u32,
    separation_limit: u32,
    max_depth: u32,
    workers: usize,
    mount: &M,
) -> Result<Vec<ZeroLineage>, String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
{
    let mut lineages: Vec<ZeroLineage> = pooled(
        roots,
        workers,
        mount,
        |source: &mut J, (ordinal, root, config): &(usize, WindingReceipt, ExactSeriesConfig)| {
            refine_root(
                source,
                *ordinal,
                root.clone(),
                grains,
                separation_limit,
                config,
                max_depth,
            )
        },
    )?
    .into_iter()
    .flatten()
    .collect();
    lineages.sort_by(|left, right| {
        left.final_receiver
            .tau
            .lower
            .cmp(&right.final_receiver.tau.lower)
    });
    for (ordinal, lineage) in lineages.iter_mut().enumerate() {
        lineage.ordinal = ordinal;
    }
    Ok(lineages)
}

/// Continue every lineage's descent from its stored final box until `grains` refinements stand.
///
/// A lineage ends at a winding-one box; the descent that produced it can simply go on, splitting
/// along the cut and reusing the certified sides, so sharpening a zero from width `2^-6` to
/// `2^-12` costs six more cut edges and no rebuild. The root, the config and the additive chain
/// are unchanged; the verifier's law is the same.
pub fn regrain_atlas<J, M>(
    atlas: &mut EtaRatioAtlas,
    grains: u32,
    workers: usize,
    mount: &M,
) -> Result<(), String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
{
    let max_depth = atlas.max_depth;
    let lineages = std::mem::take(&mut atlas.zero_lineages);
    let mut sharpened: Vec<ZeroLineage> = pooled(
        lineages,
        workers,
        mount,
        |source: &mut J, lineage: &ZeroLineage| {
            if lineage.refinements.len() as u32 >= grains {
                return Ok(lineage.clone());
            }
            let current = match lineage.refinements.last() {
                Some(step) => {
                    if step.selected == "left" {
                        step.left.clone()
                    } else {
                        step.right.clone()
                    }
                }
                None => lineage.root.clone(),
            };
            let mut out = Vec::new();
            descend(
                source,
                &lineage.root,
                current,
                lineage.refinements.clone(),
                grains,
                atlas.grain_bits,
                &lineage.config,
                max_depth,
                lineage.ordinal,
                &mut out,
            )?;
            if out.len() != 1 {
                return Err(format!(
                    "lineage {} did not continue as one closure",
                    lineage.ordinal
                ));
            }
            Ok(out.remove(0))
        },
    )?;
    sharpened.sort_by(|left, right| {
        left.final_receiver
            .tau
            .lower
            .cmp(&right.final_receiver.tau.lower)
    });
    for (ordinal, lineage) in sharpened.iter_mut().enumerate() {
        lineage.ordinal = ordinal;
    }
    let (relations, moments) = derive_relations(&sharpened)?;
    atlas.zero_lineages = sharpened;
    atlas.interval_relations = relations;
    atlas.reciprocal_moments = moments;
    Ok(())
}

pub fn read_atlas(path: &Path) -> Result<EtaRatioAtlas, String> {
    let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
    ron::from_str(&encoded).map_err(|error| error.to_string())
}

pub(super) fn positive_ratio(
    numerator: &RatInterval,
    denominator: &RatInterval,
) -> Result<RatInterval, String> {
    numerator
        .divide(denominator)
        .map_err(|error| error.to_string())
}

pub(super) fn interval_power(value: &RatInterval, exponent: u32) -> RatInterval {
    let mut result = RatInterval::point(Rat::one());
    for _ in 0..exponent {
        result = result.multiply(value);
    }
    result
}

pub(super) fn relation(kind: &str, members: Vec<usize>, value: RatInterval) -> IntervalRelation {
    IntervalRelation {
        kind: kind.to_owned(),
        members,
        common_continued_fraction: if value.lower.is_positive() {
            interval_common_continued_fraction(&value, 16)
        } else {
            Vec::new()
        },
        value,
    }
}

pub fn derive_relations(
    lineages: &[ZeroLineage],
) -> Result<(Vec<IntervalRelation>, Vec<ReciprocalMoment>), String> {
    let ordinates = lineages
        .iter()
        .map(|lineage| lineage.final_receiver.tau.clone())
        .collect::<Vec<_>>();
    derive_ordinate_relations(&ordinates)
}

/// Read ordered interval marks through the atlas's existing gap and Swing receivers.
/// A caller may transport the marks to another chart without cloning zero certificates or
/// claiming that the transported chart is a freshly certified zero atlas.
pub fn derive_ordinate_relations(
    ordinates: &[RatInterval],
) -> Result<(Vec<IntervalRelation>, Vec<ReciprocalMoment>), String> {
    let mut relations = Vec::new();
    for index in 0..ordinates.len().saturating_sub(1) {
        let gap = ordinates[index + 1].subtract(&ordinates[index]);
        relations.push(relation("successive_gap", vec![index, index + 1], gap));
        relations.push(relation(
            "successive_ordinate_ratio",
            vec![index, index + 1],
            positive_ratio(&ordinates[index + 1], &ordinates[index])?,
        ));
    }
    for index in 0..ordinates.len().saturating_sub(2) {
        let first = ordinates[index + 1].subtract(&ordinates[index]);
        let second = ordinates[index + 2].subtract(&ordinates[index + 1]);
        relations.push(relation(
            "successive_gap_ratio",
            vec![index, index + 1, index + 2],
            positive_ratio(&second, &first)?,
        ));
    }
    for index in 0..ordinates.len().saturating_sub(3) {
        let a_minus_c = ordinates[index].subtract(&ordinates[index + 2]);
        let b_minus_d = ordinates[index + 1].subtract(&ordinates[index + 3]);
        let a_minus_d = ordinates[index].subtract(&ordinates[index + 3]);
        let b_minus_c = ordinates[index + 1].subtract(&ordinates[index + 2]);
        let cross_ratio = a_minus_c
            .multiply(&b_minus_d)
            .divide(&a_minus_d.multiply(&b_minus_c))
            .map_err(|error| error.to_string())?;
        relations.push(relation(
            "ordered_projective_cross_ratio",
            vec![index, index + 1, index + 2, index + 3],
            cross_ratio,
        ));
    }
    let mut moments = Vec::new();
    for order in 1..=4u32 {
        let mut sum = RatInterval::point(Rat::zero());
        for ordinate in ordinates {
            let powered = interval_power(ordinate, 2 * order);
            sum = sum.add(
                &RatInterval::point(Rat::one())
                    .divide(&powered)
                    .map_err(|error| error.to_string())?,
            );
        }
        moments.push(ReciprocalMoment { order, value: sum });
    }
    Ok((relations, moments))
}

#[cfg(test)]
mod ordinate_receiver_tests {
    use super::*;

    #[test]
    fn swung_intervals_reverse_gaps_and_preserve_projective_reading() {
        let marks = [1, 3, 7, 12].map(|n| RatInterval::new(integer(n), integer(n) + rat(1, 8)));
        let swung = marks.each_ref().map(RatInterval::neg);
        let (before, _) = derive_ordinate_relations(&marks).unwrap();
        let (after, _) = derive_ordinate_relations(&swung).unwrap();
        for (left, right) in before.iter().zip(after.iter()) {
            assert_eq!(left.members, right.members);
            if left.kind == "successive_gap" {
                assert_eq!(left.value.neg(), right.value);
            } else {
                assert_eq!(left.value, right.value);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn build_atlas<J, M>(
    lower: i64,
    upper: i64,
    workers: usize,
    grains: u32,
    grain_bits: u32,
    max_depth: u32,
    config: &ExactSeriesConfig,
    apparatus: &str,
    mount: &M,
) -> Result<EtaRatioAtlas, String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
{
    if lower >= upper {
        return Err("the scan height must have positive extent".to_owned());
    }
    let started = Instant::now();
    let bands = scan_integer_bands(lower, upper, workers, config, grain_bits, max_depth, mount)?;
    let roots = bands
        .iter()
        .filter(|band| band.winding.winding != 0)
        .map(|band| (band.ordinal, band.winding.clone(), band.config.clone()))
        .collect::<Vec<_>>();
    let zero_lineages = refine_lineages(roots, grains, grain_bits, max_depth, workers, mount)?;
    let (interval_relations, reciprocal_moments) = derive_relations(&zero_lineages)?;
    Ok(EtaRatioAtlas {
        schema: ATLAS_SCHEMA.to_owned(),
        arithmetic: "BigInt/BigRational only; every transcendental is a rational series enclosure; every grain projection rounds outwards".to_owned(),
        source_function: "eta(s)=sum_(n>=1)(-1)^(n-1)n^(-s)=(1-2^(1-s))zeta(s)".to_owned(),
        receiver_law: "each rational sigma/tau box is mapped through Euler--Maclaurin with exact Bernoulli corrections and a rational remainder, at a start derived from the box; its boundary winding is invariant under the certified nonzero segment homotopies; refinement certifies only the cut and reuses the parent's sides".to_owned(),
        symmetry_read: "a reflection-symmetric receiver containing exactly one nontrivial zeta zero fixes that zero under rho -> 1-conjugate(rho), hence sigma=1/2".to_owned(),
        apparatus: apparatus.to_owned(),
        scan: receiver_band(RatInterval::new(integer(lower), integer(upper))),
        config: config.clone(),
        grain_bits,
        max_depth,
        physical_workers: workers.max(1),
        elapsed_milliseconds: started.elapsed().as_millis().min(u128::from(u64::MAX)) as u64,
        bands,
        zero_lineages,
        interval_relations,
        reciprocal_moments,
    })
}

pub fn write_atlas(atlas: &EtaRatioAtlas, path: &Path) -> Result<(), String> {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    // compact: the pretty form of one sixty-four-band range was 266 MB against 19 MB, and the
    // artifact is read by the verifier, not by eyes
    let encoded = ron::ser::to_string(atlas).map_err(|error| error.to_string())?;
    fs::write(path, encoded).map_err(|error| error.to_string())
}

pub fn atlas_summary(atlas: &EtaRatioAtlas) -> String {
    let mut out = format!(
        "exact eta atlas: apparatus={} bands={} closures={} workers={} grain_bits={} elapsed_ms={}\n",
        atlas.apparatus,
        atlas.bands.len(),
        atlas.zero_lineages.len(),
        atlas.physical_workers,
        atlas.grain_bits,
        atlas.elapsed_milliseconds
    );
    for band in &atlas.bands {
        out.push_str(&format!(
            "band tau=[{},{}] derived_start={} winding={} crossings={} boundary_points={}\n",
            band.winding.receiver.tau.lower,
            band.winding.receiver.tau.upper,
            band.config.euler_maclaurin_start,
            band.winding.winding,
            band.winding.crossings.total(),
            band.winding.polygon.len()
        ));
    }
    for lineage in &atlas.zero_lineages {
        let (mut discarded, mut cancelling, mut crossings_dropped) = (0usize, 0usize, 0usize);
        for step in &lineage.refinements {
            let dropped = if step.selected == "left" {
                &step.right
            } else {
                &step.left
            };
            discarded += 1;
            crossings_dropped += dropped.crossings.total();
            if dropped.crossings.cancels() {
                cancelling += 1;
            }
        }
        out.push_str(&format!(
            "zero {} tau={} root_winding={} refinement_grains={} discarded={} of_which_cancelling={} crossings_in_discarded={}\n",
            lineage.ordinal,
            lineage.final_receiver.tau,
            lineage.root.winding,
            lineage.refinements.len(),
            discarded,
            cancelling,
            crossings_dropped
        ));
    }
    for relation in &atlas.interval_relations {
        out.push_str(&format!(
            "{} {:?}={} cf={:?}\n",
            relation.kind, relation.members, relation.value, relation.common_continued_fraction
        ));
    }
    out
}
