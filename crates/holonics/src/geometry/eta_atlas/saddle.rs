use super::*;

// --- the saddle atlas: derivative windings on each side of the mirror -------------------------

pub const SADDLE_SCHEMA: &str = "laboratory.holonic-saddle-atlas.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaddleBand {
    pub ordinal: usize,
    pub config: ExactSeriesConfig,
    /// The derivative's winding around `[1/10, 1/2] x [tau, tau+1]`: saddles left of the mirror
    /// down to `sigma = 1/10`.
    pub left: WindingReceipt,
    /// Around `[1/2, 3] x [tau, tau+1]`: saddles right of the mirror. The derivative has no zero
    /// with `sigma >= 3` (its Dirichlet series is dominated by its first term there), so this is
    /// the whole population on the right.
    pub right: WindingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaddleAtlas {
    pub schema: String,
    pub field: String,
    pub reading: String,
    pub apparatus: String,
    pub scan: ComplexReceiverBox,
    pub config: ExactSeriesConfig,
    pub grain_bits: u32,
    pub max_depth: u32,
    pub physical_workers: usize,
    pub elapsed_milliseconds: u64,
    pub bands: Vec<SaddleBand>,
}

pub const SADDLE_LEFT_SIGMA: (i64, i64) = (1, 10);
pub const SADDLE_RIGHT_SIGMA: (i64, i64) = (3, 1);

pub(super) fn saddle_boxes(
    tau_lower: i64,
) -> (ComplexReceiverBox, ComplexReceiverBox, ComplexReceiverBox) {
    let tau = RatInterval::new(integer(tau_lower), integer(tau_lower + 1));
    let left = rat(SADDLE_LEFT_SIGMA.0, SADDLE_LEFT_SIGMA.1);
    let right = rat(SADDLE_RIGHT_SIGMA.0, SADDLE_RIGHT_SIGMA.1);
    (
        ComplexReceiverBox::new(RatInterval::new(left.clone(), rat(1, 2)), tau.clone()),
        ComplexReceiverBox::new(RatInterval::new(rat(1, 2), right.clone()), tau.clone()),
        // the box the start is derived from: both halves at once
        ComplexReceiverBox::new(RatInterval::new(left, right), tau),
    )
}

#[allow(clippy::too_many_arguments)]
pub fn build_saddle_atlas<J, M>(
    lower: i64,
    upper: i64,
    workers: usize,
    grain_bits: u32,
    max_depth: u32,
    config: &ExactSeriesConfig,
    apparatus: &str,
    mount: &M,
) -> Result<SaddleAtlas, String>
where
    J: HeadSource,
    M: Fn() -> Result<J, String> + Sync,
{
    if lower >= upper {
        return Err("the scan height must have positive extent".to_owned());
    }
    let started = Instant::now();
    let bands: Vec<i64> = (lower..upper).collect();
    let bands = pooled(bands, workers, mount, |source: &mut J, &tau_lower: &i64| {
        let (left_box, right_box, whole) = saddle_boxes(tau_lower);
        let band_config = derive_euler_maclaurin_start(&whole, config, grain_bits)
            .map_err(|error| format!("band [{tau_lower},{}] start: {error}", tau_lower + 1))?;
        let left =
            boundary_winding(source, Field::ZetaPrime, &left_box, &band_config, max_depth)
                .map_err(|error| format!("band [{tau_lower},{}] left: {error}", tau_lower + 1))?;
        let right = boundary_winding(
            source,
            Field::ZetaPrime,
            &right_box,
            &band_config,
            max_depth,
        )
        .map_err(|error| format!("band [{tau_lower},{}] right: {error}", tau_lower + 1))?;
        Ok(SaddleBand {
            ordinal: (tau_lower - lower) as usize,
            config: band_config,
            left,
            right,
        })
    })?;
    Ok(SaddleAtlas {
        schema: SADDLE_SCHEMA.to_owned(),
        field: "the derivative of the Riemann zeta function; its zeros are the saddles of log|zeta| between the zeros' basins".to_owned(),
        reading: "Speiser (1934): the Riemann hypothesis holds iff the derivative of zeta has no zero with 0 < sigma < 1/2; the left box's winding is that population for 1/10 <= sigma < 1/2 inside the scanned strip, exactly; the right box holds every saddle with sigma >= 1/2".to_owned(),
        apparatus: apparatus.to_owned(),
        scan: receiver_band(RatInterval::new(integer(lower), integer(upper))),
        config: config.clone(),
        grain_bits,
        max_depth,
        physical_workers: workers.max(1),
        elapsed_milliseconds: started.elapsed().as_millis().min(u128::from(u64::MAX)) as u64,
        bands,
    })
}

pub fn write_saddle_atlas(atlas: &SaddleAtlas, path: &Path) -> Result<(), String> {
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    let encoded = ron::ser::to_string(atlas).map_err(|error| error.to_string())?;
    fs::write(path, encoded).map_err(|error| error.to_string())
}

pub fn saddle_summary(atlas: &SaddleAtlas) -> String {
    let left: i32 = atlas.bands.iter().map(|band| band.left.winding).sum();
    let right: i32 = atlas.bands.iter().map(|band| band.right.winding).sum();
    let mut out = format!(
        "saddle atlas: apparatus={} bands={} left_of_mirror={} right_of_mirror={} grain_bits={} elapsed_ms={}\n",
        atlas.apparatus,
        atlas.bands.len(),
        left,
        right,
        atlas.grain_bits,
        atlas.elapsed_milliseconds
    );
    for band in &atlas.bands {
        out.push_str(&format!(
            "band tau=[{},{}] start={} left_winding={} left_points={} right_winding={} right_points={}\n",
            band.left.receiver.tau.lower,
            band.left.receiver.tau.upper,
            band.config.euler_maclaurin_start,
            band.left.winding,
            band.left.polygon.len(),
            band.right.winding,
            band.right.polygon.len()
        ));
    }
    out
}

pub fn verify_saddle_artifact(path: &Path) -> Result<String, String> {
    let encoded = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let atlas: SaddleAtlas = ron::from_str(&encoded).map_err(|error| error.to_string())?;
    require(
        atlas.schema == SADDLE_SCHEMA,
        "unexpected saddle atlas schema",
    )?;
    require(!atlas.bands.is_empty(), "atlas contains no bands")?;
    for (index, band) in atlas.bands.iter().enumerate() {
        require(
            band.ordinal == index,
            format!("band {index}: ordinal discontinuity"),
        )?;
        let tau_lower = &atlas.scan.tau.lower + integer(index as i64);
        let expected = RatInterval::new(tau_lower.clone(), &tau_lower + integer(1));
        let (left_box, right_box, whole) = saddle_boxes(
            tau_lower
                .to_integer()
                .try_into()
                .map_err(|_| format!("band {index}: height beyond i64"))?,
        );
        require(
            band.left.receiver == left_box && band.right.receiver == right_box,
            format!("band {index}: receivers are not the two half boxes of the band"),
        )?;
        let _ = expected;
        let derived = derive_euler_maclaurin_start(&whole, &atlas.config, atlas.grain_bits)
            .map_err(|error| format!("band {index}: start derivation failed: {error}"))?;
        require(
            derived == band.config,
            format!("band {index}: stored start is not the derived start"),
        )?;
        verify_winding(&band.left, &format!("band {index} left"))?;
        verify_winding(&band.right, &format!("band {index} right"))?;
        require(
            band.left.winding >= 0 && band.right.winding >= 0,
            format!(
                "band {index}: a negative winding would be a pole, and the derivative is entire here"
            ),
        )?;
    }
    let expected_upper = &atlas.scan.tau.lower + integer(atlas.bands.len() as i64);
    require(
        expected_upper == atlas.scan.tau.upper,
        "bands do not cover the declared scan",
    )?;
    Ok(format!(
        "VERIFIED schema={} apparatus={} bands={} left_of_mirror={} right_of_mirror={}\n",
        atlas.schema,
        atlas.apparatus,
        atlas.bands.len(),
        atlas
            .bands
            .iter()
            .map(|band| band.left.winding)
            .sum::<i32>(),
        atlas
            .bands
            .iter()
            .map(|band| band.right.winding)
            .sum::<i32>(),
    ))
}
