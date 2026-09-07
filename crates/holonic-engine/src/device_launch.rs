//! Device-neutral launch geometry derived from device and kernel admissions.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivedLaunch {
    pub block_x: u32,
    pub max_grid_x: u32,
    pub warp: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GridApertureError {
    ExtentOverflow,
}

impl DerivedLaunch {
    pub(crate) fn from_admissions(
        device_block: u32,
        kernel_block: u32,
        max_grid_x: u32,
        warp: u32,
    ) -> Self {
        let warp = warp.max(1);
        let admitted = device_block.min(kernel_block);
        Self {
            block_x: (admitted / warp).max(1) * warp,
            max_grid_x,
            warp,
        }
    }

    pub(crate) fn grid_for(&self, work: u32) -> Result<u32, GridApertureError> {
        let blocks = work.div_ceil(self.block_x.max(1));
        if blocks > self.max_grid_x {
            return Err(GridApertureError::ExtentOverflow);
        }
        Ok(blocks)
    }
}

#[cfg(test)]
mod tests {
    use super::{DerivedLaunch, GridApertureError};

    #[test]
    fn derives_whole_warp_block_from_device_and_kernel_admissions() {
        let launch = DerivedLaunch::from_admissions(257, 129, 17, 32);
        assert_eq!(launch.block_x, 128);
        assert_eq!(launch.max_grid_x, 17);
        assert_eq!(launch.warp, 32);
        assert_eq!(launch.grid_for(129), Ok(2));
    }

    #[test]
    fn refuses_work_past_the_declared_grid() {
        let launch = DerivedLaunch::from_admissions(64, 64, 2, 32);
        assert_eq!(launch.grid_for(129), Err(GridApertureError::ExtentOverflow));
    }

    #[test]
    fn zero_warp_and_zero_admission_keep_a_positive_minimum_block() {
        let launch = DerivedLaunch::from_admissions(0, 0, 1, 0);
        assert_eq!(launch.block_x, 1);
        assert_eq!(launch.grid_for(1), Ok(1));
    }
}
