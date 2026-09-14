// Pack the actual outgoing junction current and every retained operative internal b coordinate
// into one outer enclosure. The source report and operative sections remain separate witnesses.
extern "C" __global__ void section_field_current_source(
    const int64_t *current_lo, const int64_t *current_hi,
    const int64_t *b_lo, const int64_t *b_hi,
    const int64_t *bounds_lo, const int64_t *bounds_hi,
    uint32_t d, uint32_t count,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!d || (d & 1u) || count > UINT32_MAX / 4u) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    const size_t report_stride = (size_t)d + 1u;
    const size_t output_width = (size_t)d + 2u * count + 1u;
    const wide *current_l = (const wide *)current_lo;
    const wide *current_h = (const wide *)current_hi;
    const wide *b_l = (const wide *)b_lo;
    const wide *b_h = (const wide *)b_hi;
    const wide *bounds_l = (const wide *)bounds_lo;
    const wide *bounds_h = (const wide *)bounds_hi;
    wide *out_l = (wide *)output_lo;
    wide *out_h = (wide *)output_hi;
    for(uint32_t j=0;j<=d;++j)if(current_l[report_stride+j]!=current_h[report_stride+j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    for(uint32_t j=0;j<2u*count;++j)if(b_l[j]!=b_h[j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    if(bounds_l[1]!=bounds_h[1]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for (uint32_t j = 0; j < d; ++j) {
        out_l[j] = current_l[report_stride + j];
        out_h[j] = current_h[report_stride + j];
    }
    for (uint32_t j = 0; j < 2u * count; ++j) {
        out_l[d + j] = b_l[j];
        out_h[d + j] = b_h[j];
    }
    wide outgoing_radius_l = current_l[2u * report_stride - 1u];
    wide outgoing_radius_h = current_h[2u * report_stride - 1u];
    wide internal_radius_l = bounds_l[1];
    wide internal_radius_h = bounds_h[1];
    if (outgoing_radius_l < 0 || outgoing_radius_h < 0 ||
        internal_radius_l < 0 || internal_radius_h < 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide radius=add_checked(outgoing_radius_l,internal_radius_l,slot);
    if(*slot)return;
    out_l[output_width - 1u] = out_h[output_width - 1u] = radius;
}
