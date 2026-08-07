//! The mounted out-of-place REGISTER recast transaction.
//!
//! This is CUDA boundary apparatus, not body law. It only names and launches the already-built
//! two-entry ABI: immutable old OWN, a newly zeroed destination, old/new lane layouts, immutable
//! requests, a separately seeded completion aperture, and launch parameters.

use crate::cuda::LaunchCensus;
use crate::{
    Context, CudaError, DeviceBuffer, RegisterRecastArguments, RegisterRecastFinishKernel,
    RegisterRecastKernel, RegisterSpan, Result,
};

pub use soma_abi::register::{
    LANE_WORDS as REGISTER_LANE_WORDS, RECAST_INCOMPLETE as REGISTER_RECAST_INCOMPLETE,
    STATUS_COMPLETE as REGISTER_RECAST_COMPLETE, STATUS_WORDS as REGISTER_STATUS_WORDS,
};

/// The device buffers and structural extents carried by one out-of-place REGISTER recast.
///
/// `fresh_own_words` is an aggregate destination extent derived by the caller from `new_lanes`.
/// The helper allocates and zeroes that destination itself, so partially occupied storage cannot
/// masquerade as a fresh recast face.
pub struct RegisterOwnRecast<'a> {
    pub old_owns: &'a DeviceBuffer<u32>,
    pub old_lanes: &'a DeviceBuffer<u32>,
    pub new_lanes: &'a DeviceBuffer<u32>,
    pub requests: &'a DeviceBuffer<u32>,
    pub lane_count: usize,
    pub max_old_capacity: usize,
    pub fresh_own_words: usize,
}

/// The fresh aggregate OWN allocation after both ordered recast entries have completed.
pub struct RegisterOwnRecastOutput {
    pub owns: DeviceBuffer<u32>,
    pub completion: Vec<u32>,
}

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("REGISTER_RECAST_BOUNDARY"),
        message: message.into(),
        context,
    }
}

fn exact_product(left: usize, right: usize, face: &'static str) -> Result<usize> {
    left.checked_mul(right)
        .ok_or_else(|| boundary("register recast layout", format!("{face} overflows usize")))
}

fn validate_extents(
    lane_count: usize,
    max_old_capacity: usize,
    fresh_own_words: usize,
    old_own_words: usize,
    old_lane_words: usize,
    new_lane_words: usize,
    request_words: usize,
) -> Result<(u32, u32, u64)> {
    if lane_count == 0 || max_old_capacity == 0 || fresh_own_words == 0 || old_own_words == 0 {
        return Err(boundary(
            "register recast layout",
            "lane, old-capacity, old-OWN, and fresh-OWN extents must be positive",
        ));
    }
    let expected_lanes = exact_product(lane_count, REGISTER_LANE_WORDS, "lane rows")?;
    if old_lane_words != expected_lanes || new_lane_words != expected_lanes {
        return Err(boundary(
            "register recast layout",
            format!(
                "old/new lane rows must each carry {expected_lanes} words, got {old_lane_words}/{new_lane_words}"
            ),
        ));
    }
    let expected_requests = exact_product(lane_count, REGISTER_STATUS_WORDS, "request rows")?;
    if request_words != expected_requests {
        return Err(boundary(
            "register recast layout",
            format!("request rows must carry {expected_requests} words, got {request_words}"),
        ));
    }
    let lanes = u32::try_from(lane_count).map_err(|_| {
        boundary(
            "register recast layout",
            "lane count exceeds the CUDA parameter wire",
        )
    })?;
    let old_capacity = u32::try_from(max_old_capacity).map_err(|_| {
        boundary(
            "register recast layout",
            "old capacity exceeds the CUDA parameter wire",
        )
    })?;
    fresh_own_words
        .checked_mul(core::mem::size_of::<u32>())
        .ok_or_else(|| {
            boundary(
                "register recast layout",
                "fresh OWN byte extent overflows usize",
            )
        })?;
    let work = (lane_count as u64)
        .checked_mul(max_old_capacity as u64)
        .ok_or_else(|| boundary("register recast layout", "cell work extent overflows u64"))?;
    Ok((lanes, old_capacity, work))
}

/// Launch the cell move and the ordered finish entry, then return only a fully completed fresh OWN
/// aggregate. Any malformed structural extent, driver failure, or nonterminal completion is a
/// typed boundary error; this helper never retries, shrinks, or reuses the old allocation.
pub fn launch_register_own_recast(
    context: &Context,
    cells: &RegisterRecastKernel<'_>,
    finish: &RegisterRecastFinishKernel<'_>,
    census: LaunchCensus,
    recast: RegisterOwnRecast<'_>,
) -> Result<RegisterOwnRecastOutput> {
    let (lane_count, max_old_capacity, work) = validate_extents(
        recast.lane_count,
        recast.max_old_capacity,
        recast.fresh_own_words,
        recast.old_owns.len(),
        recast.old_lanes.len(),
        recast.new_lanes.len(),
        recast.requests.len(),
    )?;

    let owns = DeviceBuffer::<u32>::alloc_zeroed(recast.fresh_own_words)?;
    let completion = DeviceBuffer::<u32>::alloc(recast.lane_count)?;
    completion.copy_from_slice(&vec![REGISTER_RECAST_INCOMPLETE; recast.lane_count])?;

    let cell_launch = cells.linear_launch(census, work)?;
    let cell_params = [lane_count, max_old_capacity, cell_launch.x_stride];
    let cell_params_buffer = DeviceBuffer::alloc(cell_params.len())?;
    cell_params_buffer.copy_from_slice(&cell_params)?;

    cells.launch(
        cell_launch.grid,
        cell_launch.block,
        RegisterRecastArguments {
            old_owns: RegisterSpan::whole(recast.old_owns),
            fresh_owns: RegisterSpan::whole(&owns),
            old_lanes: RegisterSpan::whole(recast.old_lanes),
            new_lanes: RegisterSpan::whole(recast.new_lanes),
            requests: RegisterSpan::whole(recast.requests),
            completions: RegisterSpan::whole(&completion),
            params: RegisterSpan::whole(&cell_params_buffer),
        },
    )?;

    let finish_launch = finish.linear_launch(census, recast.lane_count as u64)?;
    let finish_params = [lane_count, max_old_capacity, finish_launch.x_stride];
    let finish_params_buffer = DeviceBuffer::alloc(finish_params.len())?;
    finish_params_buffer.copy_from_slice(&finish_params)?;
    finish.launch(
        finish_launch.grid,
        finish_launch.block,
        RegisterRecastArguments {
            old_owns: RegisterSpan::whole(recast.old_owns),
            fresh_owns: RegisterSpan::whole(&owns),
            old_lanes: RegisterSpan::whole(recast.old_lanes),
            new_lanes: RegisterSpan::whole(recast.new_lanes),
            requests: RegisterSpan::whole(recast.requests),
            completions: RegisterSpan::whole(&completion),
            params: RegisterSpan::whole(&finish_params_buffer),
        },
    )?;
    context.synchronize()?;

    let mut returned = vec![REGISTER_RECAST_INCOMPLETE; recast.lane_count];
    completion.copy_to_slice(&mut returned)?;
    if returned
        .iter()
        .any(|word| *word != REGISTER_RECAST_COMPLETE)
    {
        return Err(boundary(
            "register recast completion",
            format!("one or more lanes did not complete: {returned:?}"),
        ));
    }

    Ok(RegisterOwnRecastOutput {
        owns,
        completion: returned,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_plural_layout_names_the_seven_pair_abi() {
        assert_eq!(
            validate_extents(3, 64, 12_345, 9_876, 30, 30, 9).unwrap(),
            (3, 64, 192)
        );
    }

    #[test]
    fn partial_lane_or_request_rows_are_rejected() {
        assert!(validate_extents(3, 64, 12_345, 9_876, 29, 30, 9).is_err());
        assert!(validate_extents(3, 64, 12_345, 9_876, 30, 29, 9).is_err());
        assert!(validate_extents(3, 64, 12_345, 9_876, 30, 30, 8).is_err());
    }

    #[test]
    fn empty_and_unrepresentable_extents_are_rejected() {
        assert!(validate_extents(0, 64, 1, 1, 0, 0, 0).is_err());
        assert!(validate_extents(1, 0, 1, 1, 10, 10, 3).is_err());
        assert!(validate_extents(1, 1, 0, 1, 10, 10, 3).is_err());
        assert!(validate_extents(1, 1, 1, 0, 10, 10, 3).is_err());
        assert!(validate_extents(1, 1, usize::MAX, 1, 10, 10, 3).is_err());
        if usize::BITS > u32::BITS {
            assert!(validate_extents(u32::MAX as usize + 1, 1, 1, 1, 0, 0, 0).is_err());
            assert!(validate_extents(1, u32::MAX as usize + 1, 1, 1, 10, 10, 3).is_err());
        }
    }
}
