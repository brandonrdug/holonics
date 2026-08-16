//! Device-local rebasing of complete REGISTER carrier rows.
//!
//! The cpu reads only the three-word substrate status and constructs the next physical lane
//! layout.  The live carrier body never returns to cpu memory: one CUDA worker moves each exact
//! row into a fresh allocation and the old allocation remains immutable until completion.

use crate::cuda::LaunchCensus;
use crate::{
    Context, CudaError, DeviceBuffer, RegisterCarrierRebaseArguments, RegisterCarrierRebaseKernel,
    RegisterSpan, Result,
};
use body::manifold;
use soma_abi::register;

pub struct RegisterCarrierRebase<'a> {
    pub old_carriers: &'a DeviceBuffer<u32>,
    pub old_lanes: &'a DeviceBuffer<u32>,
    pub old_lane_words: &'a [u32],
    pub request_words: &'a [u32],
    pub lane_count: usize,
}

pub struct RegisterCarrierRebaseOutput {
    pub carriers: DeviceBuffer<u32>,
    pub lanes: DeviceBuffer<u32>,
    pub lane_words: Vec<u32>,
    pub completion: Vec<u32>,
}

fn boundary(context: &'static str, message: impl Into<String>) -> CudaError {
    CudaError {
        code: -1,
        name: String::from("REGISTER_CARRIER_REBASE_BOUNDARY"),
        message: message.into(),
        context,
    }
}

fn planned_lanes(
    old: &[u32],
    requests: &[u32],
    lanes: usize,
    old_carrier_words: usize,
) -> Result<(Vec<u32>, usize)> {
    let lane_words = lanes
        .checked_mul(register::LANE_WORDS)
        .ok_or_else(|| boundary("carrier lane layout", "lane extent overflows usize"))?;
    let request_extent = lanes
        .checked_mul(register::STATUS_WORDS)
        .ok_or_else(|| boundary("carrier request layout", "request extent overflows usize"))?;
    if lanes == 0 || old.len() != lane_words || requests.len() != request_extent {
        return Err(boundary(
            "carrier rebase layout",
            "lane and request rows must be exact and nonempty",
        ));
    }

    let mut next = old.to_vec();
    let mut old_end = 0usize;
    let mut new_end = 0usize;
    for lane in 0..lanes {
        let at = lane * register::LANE_WORDS;
        let request = lane * register::STATUS_WORDS;
        let old_base = old[at + register::LANE_CARRIER_WORD_BASE] as usize;
        let old_words = old[at + register::LANE_CARRIER_ROW_WORDS] as usize;
        if old_base != old_end
            || manifold::carrier_row_words(manifold::carrier_row_depth(old_words)) != old_words
        {
            return Err(boundary(
                "carrier rebase layout",
                format!("lane {lane} does not name the next complete canonical row extent"),
            ));
        }
        old_end = old_end
            .checked_add(old_words)
            .ok_or_else(|| boundary("carrier rebase layout", "old carrier extent overflows"))?;

        let kind = register::StatusKind::from_word(requests[request + register::STATUS_KIND])
            .ok_or_else(|| boundary("carrier rebase request", "unknown status kind"))?;
        let new_words = if kind == register::StatusKind::NeedsCarrierRebase {
            let required = requests[request + register::STATUS_OLD_AXIS] as u64
                | ((requests[request + register::STATUS_NEW_AXIS] as u64) << 32);
            let required = usize::try_from(required).map_err(|_| {
                boundary(
                    "carrier rebase request",
                    "required carrier depth exceeds the cpu extent wire",
                )
            })?;
            let old_depth = manifold::carrier_row_depth(old_words);
            if required
                != old_depth.checked_add(1).ok_or_else(|| {
                    boundary("carrier rebase request", "required carrier depth overflows")
                })?
            {
                return Err(boundary(
                    "carrier rebase request",
                    format!("lane {lane} requests depth {required} after {old_depth}"),
                ));
            }
            manifold::carrier_row_words(required)
        } else {
            old_words
        };
        next[at + register::LANE_CARRIER_WORD_BASE] = u32::try_from(new_end).map_err(|_| {
            boundary(
                "carrier rebase layout",
                "aggregate carrier base exceeds the current lane ABI",
            )
        })?;
        next[at + register::LANE_CARRIER_ROW_WORDS] = u32::try_from(new_words).map_err(|_| {
            boundary(
                "carrier rebase layout",
                "carrier row extent exceeds the current lane ABI",
            )
        })?;
        new_end = new_end
            .checked_add(new_words)
            .ok_or_else(|| boundary("carrier rebase layout", "new carrier extent overflows"))?;
    }
    if old_end != old_carrier_words {
        return Err(boundary(
            "carrier rebase layout",
            format!("lane rows cover {old_end} carrier words, allocation has {old_carrier_words}"),
        ));
    }
    Ok((next, new_end))
}

pub fn launch_register_carrier_rebase(
    context: &Context,
    kernel: &RegisterCarrierRebaseKernel<'_>,
    census: LaunchCensus,
    rebase: RegisterCarrierRebase<'_>,
) -> Result<RegisterCarrierRebaseOutput> {
    if rebase.old_lanes.len() != rebase.old_lane_words.len() {
        return Err(boundary(
            "carrier rebase layout",
            "cpu and device old-lane extents differ",
        ));
    }
    let (lane_words, fresh_words) = planned_lanes(
        rebase.old_lane_words,
        rebase.request_words,
        rebase.lane_count,
        rebase.old_carriers.len(),
    )?;
    let lanes = DeviceBuffer::alloc(lane_words.len())?;
    lanes.copy_from_slice(&lane_words)?;
    let requests = DeviceBuffer::alloc(rebase.request_words.len())?;
    requests.copy_from_slice(rebase.request_words)?;
    let carriers = DeviceBuffer::<u32>::alloc_zeroed(fresh_words)?;
    let completions = DeviceBuffer::<u32>::alloc(rebase.lane_count)?;
    completions.copy_from_slice(&vec![register::RECAST_INCOMPLETE; rebase.lane_count])?;

    let launch = kernel.linear_launch(census, rebase.lane_count as u64)?;
    let params = [
        u32::try_from(rebase.lane_count).map_err(|_| {
            boundary(
                "carrier rebase launch",
                "lane count exceeds the CUDA parameter wire",
            )
        })?,
        launch.x_stride,
    ];
    let params_buffer = DeviceBuffer::alloc(params.len())?;
    params_buffer.copy_from_slice(&params)?;
    kernel.launch(
        launch.grid,
        launch.block,
        RegisterCarrierRebaseArguments {
            old_carriers: RegisterSpan::whole(rebase.old_carriers),
            fresh_carriers: RegisterSpan::whole(&carriers),
            old_lanes: RegisterSpan::whole(rebase.old_lanes),
            new_lanes: RegisterSpan::whole(&lanes),
            requests: RegisterSpan::whole(&requests),
            completions: RegisterSpan::whole(&completions),
            params: RegisterSpan::whole(&params_buffer),
        },
    )?;
    context.synchronize()?;

    let mut completion = vec![register::RECAST_INCOMPLETE; rebase.lane_count];
    completions.copy_to_slice(&mut completion)?;
    if completion
        .iter()
        .any(|&word| word != register::STATUS_COMPLETE)
    {
        return Err(boundary(
            "carrier rebase completion",
            format!("one or more device rows did not complete: {completion:?}"),
        ));
    }
    Ok(RegisterCarrierRebaseOutput {
        carriers,
        lanes,
        lane_words,
        completion,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plural_layout_grows_only_the_pressured_lane() {
        let mut lanes = vec![0u32; 2 * register::LANE_WORDS];
        let first = manifold::carrier_row_words(1);
        let second = manifold::carrier_row_words(3);
        lanes[register::LANE_CARRIER_ROW_WORDS] = first as u32;
        let at = register::LANE_WORDS;
        lanes[at + register::LANE_CARRIER_WORD_BASE] = first as u32;
        lanes[at + register::LANE_CARRIER_ROW_WORDS] = second as u32;
        let requests = [
            register::STATUS_NEEDS_CARRIER_REBASE,
            2,
            0,
            register::STATUS_CONTINUE,
            0,
            0,
        ];
        let (next, words) = planned_lanes(&lanes, &requests, 2, first + second).unwrap();
        assert_eq!(
            next[register::LANE_CARRIER_ROW_WORDS] as usize,
            manifold::carrier_row_words(2)
        );
        assert_eq!(
            next[at + register::LANE_CARRIER_WORD_BASE] as usize,
            manifold::carrier_row_words(2)
        );
        assert_eq!(next[at + register::LANE_CARRIER_ROW_WORDS] as usize, second);
        assert_eq!(words, manifold::carrier_row_words(2) + second);
    }
}
