// **The intervention on the excited current: a declared site population withdrawn.**
//
// Included by `exact_resident_section.cu` after its helpers.  One kernel: the sites (columns)
// flagged in a resident mask — one word per site, nonzero for withdrawn — are zeroed at every row,
// out of place.  This is the `withdraw` of the excitation-founded quotient read on a carrier: the
// state at a withdrawn site is zero and every other site is carried exactly.  The mask is read
// through a pointer the caller may offset, so each tile of a tiled carrier reads its own span of
// one mask.

extern "C" __global__ void section_withdraw_sites(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, const uint32_t *mask,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t c = flat % width;
    int withdrawn = mask[c] != 0;
    out_lo[flat] = withdrawn ? 0 : lo[flat];
    out_hi[flat] = withdrawn ? 0 : hi[flat];
}
