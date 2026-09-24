// A declared receiver holds selected complex coordinates from one source and receives the
// remaining coordinates from a generated enclosure. The original operands retain their
// relation; this returned Euclidean ball bounds the indicated affine receiver.
extern "C" __global__ void section_normal_held_section(
    const int64_t *given, const int64_t *given_hi, uint32_t ga,
    const int64_t *generated, const int64_t *generated_hi, uint32_t xa,
    const int64_t *held, const int64_t *held_hi, uint32_t complexes, uint32_t aliased,
    int64_t *out, int64_t *out_hi, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count) {
    if (blockIdx.x || threadIdx.x || upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!complexes || complexes > UINT32_MAX / 2u) {
        atomicOr(slot, REFUSED_MALFORMED); return;
    }
    if((ga&1u)||(xa&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
    given+=ga;given_hi+=ga;generated+=xa;generated_hi+=xa;
    const uint32_t width = 2u * complexes;
    for (size_t i = 0; i < 2u * ((size_t)width + 1u); ++i) {
        if (given[i] != given_hi[i] || generated[i] != generated_hi[i]) {
            atomicOr(slot, REFUSED_MALFORMED); return;
        }
    }
    for (uint32_t i = 0; i < complexes; ++i) {
        if (held[i] != held_hi[i] || (held[i] != 0 && held[i] != 1)) {
            atomicOr(slot, REFUSED_MALFORMED); return;
        }
    }
    const wide *g = (const wide *)given, *x = (const wide *)generated;
    wide *y = (wide *)out;
    if (g[width] < 0 || x[width] < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    bool any_held = false, any_free = false;
    for (uint32_t i = 0; i < complexes; ++i) {
        const bool h = held[i] != 0;
        any_held |= h; any_free |= !h;
        y[2u * i] = h ? g[2u * i] : x[2u * i];
        y[2u * i + 1u] = h ? g[2u * i + 1u] : x[2u * i + 1u];
    }
    if (aliased) y[width] = any_held || any_free ? g[width] : 0;
    else {
        wide radius = 0;
        if (any_held) radius = add_checked(radius, g[width], slot);
        if (any_free) radius = add_checked(radius, x[width], slot);
        y[width] = radius;
    }
    if (*slot) return;
    for (size_t i = 0; i < 2u * ((size_t)width + 1u); ++i) out_hi[i] = out[i];
}
