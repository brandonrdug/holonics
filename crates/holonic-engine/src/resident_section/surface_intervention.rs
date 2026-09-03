//! The intervention on the excited current: a declared site population withdrawn from a carrier.
//!
//! A site mask is one resident word per site (column), nonzero for withdrawn.  It is mounted once
//! and read by every withdrawal that shares it; a tiled carrier reads its own span of the mask
//! through an offset.  The withdrawal is out of place: the predecessor is what the caller still
//! holds, so the intervened carrier and the actual one coexist on the card.

use mount::DeviceBuffer;

use super::*;

/// One resident site mask: `sites` words, `withdrawn` of them nonzero.
pub struct SiteMask<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    buffer: DeviceBuffer<u32>,
    sites: usize,
    withdrawn: usize,
}

impl SiteMask<'_> {
    pub fn sites(&self) -> usize {
        self.sites
    }

    pub fn withdrawn(&self) -> usize {
        self.withdrawn
    }

    fn device_ptr_at(&self, offset: usize) -> u64 {
        self.buffer.device_ptr() + (offset * std::mem::size_of::<u32>()) as u64
    }
}

impl Drop for SiteMask<'_> {
    fn drop(&mut self) {
        self.surface
            .released_octets((self.sites.max(1) * std::mem::size_of::<u32>()) as u64);
    }
}

impl<'chart> ResidentSurface<'chart> {
    /// Mount a site mask from the declared population: `true` withdraws the site.
    pub fn mount_site_mask(
        &'chart self,
        withdrawn: &[bool],
    ) -> Result<SiteMask<'chart>, ResidentRefusal> {
        let words: Vec<u32> = withdrawn.iter().map(|site| u32::from(*site)).collect();
        let buffer = self.alloc::<u32>(words.len())?;
        if !words.is_empty() {
            buffer.copy_from_slice(&words)?;
        }
        Ok(SiteMask {
            surface: self,
            buffer,
            sites: words.len(),
            withdrawn: withdrawn.iter().filter(|site| **site).count(),
        })
    }

    /// The intervention: the sites flagged in a mask withdrawn from every row, out of place.
    pub fn shape_withdraw_sites(
        &self,
        rows: usize,
        width: usize,
        input_octaves: u32,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "withdraw-sites";
        let count = (rows * width) as u64;
        let mut work = ExactWork::nothing();
        work.entries_written = BigUint::from(2 * count);
        work.resident(2 * count);
        work.peak_bits = BigUint::from(u64::from(input_octaves));
        work.stepped();
        self.flat_shape(OPERATION, rows, width, input_octaves, work, Vec::new())
    }

    /// Record the withdrawal of the sites flagged at `mask[offset..offset + width]`.
    pub fn record_withdraw_sites(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        mask: &SiteMask<'chart>,
        offset: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows != input.rows || out.width != input.width {
            return Err(ResidentRefusal::Declaration {
                operation: "withdraw-sites",
                what: "the output does not carry the predecessor's face".to_owned(),
            });
        }
        if offset + input.width > mask.sites {
            return Err(ResidentRefusal::Declaration {
                operation: "withdraw-sites",
                what: format!(
                    "the mask carries {} sites but the carrier reads {} from {offset}",
                    mask.sites, input.width
                ),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(mask.device_ptr_at(offset))
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_withdraw_sites",
            input.count(),
            &mut params,
            "withdraw-sites",
        )
    }
}
