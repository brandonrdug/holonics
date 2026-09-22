// Resident affine action on the fixed complex3 geometry chart.
//
// A row carries a real 3x3 matrix followed by a real 3-vector bias.  The matrix
// acts on both halves of a complex3 source; the bias is added to the real half
// only.  `project` is the receiving geometry face: it deliberately erases the
// imaginary output before the packet is sealed.  The map and source are balls,
// so every product and sum stays an outward interval at the declared grain.

__device__ MaterialInterval affine_ball(const wide *v, uint32_t d, uint32_t j,
                                        uint32_t *status) {
    return {sub_checked(v[j], v[d], status), add_checked(v[j], v[d], status)};
}

__device__ void affine_pack(wide *lo, wide *hi, uint32_t d, uint32_t *status) {
    wide radius = 0;
    for (uint32_t j = 0; j < d; ++j) {
        if (hi[j] < lo[j]) {
            atomicOr(status, REFUSED_INVERTED);
            return;
        }
        wide r = add_checked(sub_checked(hi[j], lo[j], status), 1, status) >> 1;
        lo[j] = add_checked(lo[j], r, status);
        radius = add_checked(radius, r, status);
    }
    lo[d] = radius;
}

// A bound on the real 3x3 operator and its complexification.  For a permutation
// or identity it is exactly one; duplicating real/imaginary charts does not change it.
__device__ wide affine_operator_bound(const wide *m, uint32_t *status) {
    wide row_max=0,column_max=0;
    for(uint32_t i=0;i<3u;++i){
        wide r=0,c=0;
        for(uint32_t j=0;j<3u;++j){
            r=add_checked(r,ft_abs(m[3u*i+j],status),status);
            c=add_checked(c,ft_abs(m[3u*j+i],status),status);
        }
        if(r>row_max)row_max=r;
        if(c>column_max)column_max=c;
    }
    return history_norm_ceiling(history_integer(row_max)*history_integer(column_max),status);
}
__device__ wide affine_joint_radius(const wide *m,const wide *x,uint32_t grain,
                                    bool project,bool bias,uint32_t *status){
    wide radius=ft_ceil_product(affine_operator_bound(m,status),x[6],grain,status);
    if(m[12]){
        wide projected[6]={x[0],0,x[2],0,x[4],0};
        wide size=add_checked(complete_norm(project?projected:x,6u,status),x[6],status);
        if(bias)size=add_checked(size,((wide)1)<<grain,status);
        radius=add_checked(radius,ft_ceil_product(m[12],size,grain,status),status);
    }
    return radius;
}

// `indices` is an exact width-one section.  `maps` is an enclosure section with
// twelve coefficients per row: R00..R22,b0..b2.
extern "C" __global__ void section_affine_geometry_forward(
    const int64_t *source, const int64_t *source_hi,
    const int64_t *indices, const int64_t *indices_hi,
    const int64_t *maps, const int64_t *maps_hi,
    uint32_t input_rows, uint32_t rows, uint32_t grain, uint32_t project, uint32_t joint,
    int64_t *out, int64_t *out_hi, int64_t *flags,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count) {
    if (threadIdx.x) return;
    uint32_t row = blockIdx.x;
    if (row >= rows) return;
    uint32_t *status = ec_status(flags, row);
    if (upstream_refused(census, lineage, lineage_count, status)) return;
    if(joint>1u || grain<1u || grain>120u){atomicOr(status,REFUSED_MALFORMED);return;}

    const int64_t *index = indices + row;
    const int64_t *index_hi = indices_hi + row;
    if (*index != *index_hi || *index < 0 || (uint64_t)*index >= input_rows) {
        atomicOr(status, REFUSED_MALFORMED);
        return;
    }
    const size_t source_stride = 2u * (6u + 1u);
    const size_t map_stride = 2u * (12u + 1u);
    const int64_t *source_row = source + source_stride * (size_t)*index;
    const int64_t *source_row_hi = source_hi + source_stride * (size_t)*index;
    const int64_t *map_row = maps + map_stride * row;
    const int64_t *map_row_hi = maps_hi + map_stride * row;
    if (!ec_ball(source_row, source_row_hi, 6u, status) ||
        !ec_ball(map_row, map_row_hi, 12u, status)) return;

    const wide *x = (const wide *)source_row;
    const wide *m = (const wide *)map_row;
    wide *y = (wide *)(out + source_stride * row);
    wide *yh = (wide *)(out_hi + source_stride * row);
    for (uint32_t j = 0; j < 6u; ++j) {
        y[j] = 0;
        yh[j] = 0;
    }

    for (uint32_t i = 0; i < 3u; ++i) {
        MaterialInterval real = joint ? mp_point(m[9u+i]) : affine_ball(m, 12u, 9u + i, status);
        MaterialInterval imag = mp_point(0);
        for (uint32_t j = 0; j < 3u; ++j) {
            MaterialInterval coefficient = joint ? mp_point(m[3u*i+j]) : affine_ball(m, 12u, 3u * i + j, status);
            real = mp_add(real,
                          mp_mul(coefficient, joint ? mp_point(x[2u*j]) : affine_ball(x, 6u, 2u * j, status),
                                 grain, status),
                          status);
            imag = mp_add(imag,
                          mp_mul(coefficient, joint ? mp_point(x[2u*j+1u]) : affine_ball(x, 6u, 2u * j + 1u, status),
                                 grain, status),
                          status);
        }
        y[2u * i] = real.lo;
        yh[2u * i] = real.hi;
        if (project) {
            y[2u * i + 1u] = 0;
            yh[2u * i + 1u] = 0;
        } else {
            y[2u * i + 1u] = imag.lo;
            yh[2u * i + 1u] = imag.hi;
        }
    }
    affine_pack(y, yh, 6u, status);
    if(joint)y[6]=add_checked(y[6],affine_joint_radius(m,x,grain,project,true,status),status);
    ec_seal((int64_t *)y, (int64_t *)(out_hi + source_stride * row), 6u, status);
}

// The reverse uses the same producing coefficient packet.  It returns one
// gathered source covector per affine row; the Rust owner then invokes the
// existing phase scatter adjoint with identity phases, including repeated
// source indices and their radius joins.
extern "C" __global__ void section_affine_geometry_adjoint(
    const int64_t *maps, const int64_t *maps_hi,
    const int64_t *gy, const int64_t *gy_hi,
    uint32_t rows, uint32_t grain, uint32_t project, uint32_t joint,
    int64_t *out, int64_t *out_hi, int64_t *flags,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count) {
    if (threadIdx.x) return;
    uint32_t row = blockIdx.x;
    if (row >= rows) return;
    uint32_t *status = ec_status(flags, row);
    if (upstream_refused(census, lineage, lineage_count, status)) return;
    if(joint>1u || grain<1u || grain>120u){atomicOr(status,REFUSED_MALFORMED);return;}

    const size_t map_stride = 2u * (12u + 1u);
    const size_t chart_stride = 2u * (6u + 1u);
    const int64_t *map_row = maps + map_stride * row;
    const int64_t *map_row_hi = maps_hi + map_stride * row;
    const int64_t *gy_row = gy + chart_stride * row;
    const int64_t *gy_row_hi = gy_hi + chart_stride * row;
    if (!ec_ball(map_row, map_row_hi, 12u, status) ||
        !ec_ball(gy_row, gy_row_hi, 6u, status)) return;

    const wide *m = (const wide *)map_row;
    const wide *g = (const wide *)gy_row;
    wide *y = (wide *)(out + chart_stride * row);
    wide *yh = (wide *)(out_hi + chart_stride * row);
    for (uint32_t j = 0; j < 6u; ++j) {
        y[j] = 0;
        yh[j] = 0;
    }
    for (uint32_t j = 0; j < 3u; ++j) {
        MaterialInterval real = mp_point(0);
        MaterialInterval imag = mp_point(0);
        for (uint32_t i = 0; i < 3u; ++i) {
            MaterialInterval coefficient = joint ? mp_point(m[3u*i+j]) : affine_ball(m, 12u, 3u * i + j, status);
            real = mp_add(real,
                          mp_mul(coefficient, joint ? mp_point(g[2u*i]) : affine_ball(g, 6u, 2u * i, status),
                                 grain, status),
                          status);
            if (!project) {
                imag = mp_add(imag,
                              mp_mul(coefficient,
                                     joint ? mp_point(g[2u*i+1u]) : affine_ball(g, 6u, 2u * i + 1u, status),
                                     grain, status),
                              status);
            }
        }
        y[2u * j] = real.lo;
        yh[2u * j] = real.hi;
        if (project) {
            y[2u * j + 1u] = 0;
            yh[2u * j + 1u] = 0;
        } else {
            y[2u * j + 1u] = imag.lo;
            yh[2u * j + 1u] = imag.hi;
        }
    }
    affine_pack(y, yh, 6u, status);
    if(joint)y[6]=add_checked(y[6],affine_joint_radius(m,g,grain,project,false,status),status);
    ec_seal((int64_t *)y, (int64_t *)(out_hi + chart_stride * row), 6u, status);
}

// Realification of an even realified complex chart.  The packet radius is a
// whole-ball radius and therefore travels unchanged; inserted/erased
// imaginary coordinates are exact zeroes. Modes: 0 = encode, 1 = decode,
// 2 = project real.
extern "C" __global__ void section_realification(
    const int64_t *input, const int64_t *input_hi,
    uint32_t rows, uint32_t input_components, uint32_t output_components,
    uint32_t mode, int64_t *out, int64_t *out_hi, int64_t *flags,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count) {
    if (threadIdx.x) return;
    uint32_t row = blockIdx.x;
    if (row >= rows) return;
    uint32_t *status = ec_status(flags, row);
    if (upstream_refused(census, lineage, lineage_count, status)) return;
    if (!input_components || (input_components & 1u) || !output_components ||
        mode > 2u) {
        atomicOr(status, REFUSED_MALFORMED);
        return;
    }
    const size_t input_stride = 2u * ((size_t)input_components + 1u);
    const size_t output_stride = 2u * ((size_t)output_components + 1u);
    const int64_t *input_row = input + input_stride * row;
    const int64_t *input_row_hi = input_hi + input_stride * row;
    if (!ec_ball(input_row, input_row_hi, input_components, status)) return;
    const wide *x = (const wide *)input_row;
    wide *y = (wide *)(out + output_stride * row);
    wide *yh = (wide *)(out_hi + output_stride * row);
    for (uint32_t j = 0; j < output_components; ++j) {
        y[j] = 0;
        yh[j] = 0;
    }
    if (mode == 0u) {
        if (output_components != 2u * input_components) {
            atomicOr(status, REFUSED_MALFORMED);
            return;
        }
        for (uint32_t j = 0; j < input_components; ++j) {
            y[2u * j] = x[j];
            y[2u * j + 1u] = 0;
        }
    } else if (mode == 1u) {
        if (input_components != 2u * output_components) {
            atomicOr(status, REFUSED_MALFORMED);
            return;
        }
        for (uint32_t j = 0; j < output_components; ++j) y[j] = x[2u * j];
    } else {
        if (output_components != input_components) {
            atomicOr(status, REFUSED_MALFORMED);
            return;
        }
        for (uint32_t j = 0; j < output_components; j += 2u) {
            y[j] = x[j];
            y[j + 1u] = 0;
        }
    }
    y[output_components] = x[input_components];
    ec_seal((int64_t *)y, (int64_t *)(out_hi + output_stride * row), output_components, status);
}
