#include <stdint.h>

struct ExactCoefficient {
    uint64_t lower;
    uint64_t upper;
    uint32_t negative;
    uint32_t reserved;

    __device__ operator signed __int128() const {
        unsigned __int128 magnitude =
            (static_cast<unsigned __int128>(upper) << 64) | lower;
        signed __int128 signed_magnitude =
            static_cast<signed __int128>(magnitude);
        return negative == 0 ? signed_magnitude : -signed_magnitude;
    }
};

struct ExactConic {
    ExactCoefficient xx;
    ExactCoefficient xy;
    ExactCoefficient yy;
    ExactCoefficient x;
    ExactCoefficient y;
    ExactCoefficient constant;
    uint32_t primitive;
    uint32_t reserved;
};

struct ExactSegment {
    ExactCoefficient line_a;
    ExactCoefficient line_b;
    ExactCoefficient line_c;
    uint32_t bound_left;
    uint32_t bound_top;
    uint32_t bound_right;
    uint32_t bound_bottom;
    uint32_t primitive;
    uint32_t reserved;
};

template <int LimbCount>
struct ExactInteger {
    static constexpr int LIMBS = LimbCount;
    uint32_t limb[LIMBS];
    bool negative;
    bool overflow;

    __device__ ExactInteger() : limb{}, negative(false), overflow(false) {}

    __device__ ExactInteger(int64_t value)
        : limb{}, negative(value < 0), overflow(false) {
        uint64_t magnitude = value < 0
            ? uint64_t(-(value + 1)) + 1ULL
            : uint64_t(value);
        limb[0] = uint32_t(magnitude);
        limb[1] = uint32_t(magnitude >> 32);
        if (magnitude == 0) {
            negative = false;
        }
    }

    __device__ ExactInteger(ExactCoefficient value)
        : limb{}, negative(value.negative != 0), overflow(false) {
        limb[0] = uint32_t(value.lower);
        limb[1] = uint32_t(value.lower >> 32);
        limb[2] = uint32_t(value.upper);
        limb[3] = uint32_t(value.upper >> 32);
        if (is_zero()) {
            negative = false;
        }
    }

    __device__ bool is_zero() const {
        for (int index = 0; index < LIMBS; ++index) {
            if (limb[index] != 0) {
                return false;
            }
        }
        return true;
    }
};

template <int LimbCount>
__device__ int compare_magnitude(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    for (int index = ExactInteger<LimbCount>::LIMBS - 1; index >= 0; --index) {
        if (left.limb[index] < right.limb[index]) {
            return -1;
        }
        if (left.limb[index] > right.limb[index]) {
            return 1;
        }
    }
    return 0;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> add_magnitude(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    ExactInteger<LimbCount> result;
    uint64_t carry = 0;
    for (int index = 0; index < ExactInteger<LimbCount>::LIMBS; ++index) {
        uint64_t sum =
            uint64_t(left.limb[index]) + right.limb[index] + carry;
        result.limb[index] = uint32_t(sum);
        carry = sum >> 32;
    }
    result.overflow = left.overflow || right.overflow || carry != 0;
    return result;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> subtract_magnitude(
    const ExactInteger<LimbCount> &larger,
    const ExactInteger<LimbCount> &smaller
) {
    ExactInteger<LimbCount> result;
    uint64_t borrow = 0;
    for (int index = 0; index < ExactInteger<LimbCount>::LIMBS; ++index) {
        uint64_t left = larger.limb[index];
        uint64_t right = uint64_t(smaller.limb[index]) + borrow;
        result.limb[index] = uint32_t(left - right);
        borrow = left < right;
    }
    result.overflow = larger.overflow || smaller.overflow || borrow != 0;
    return result;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator-(
    const ExactInteger<LimbCount> &value
) {
    ExactInteger<LimbCount> result = value;
    if (!result.is_zero()) {
        result.negative = !result.negative;
    }
    return result;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator+(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    if (left.negative == right.negative) {
        ExactInteger<LimbCount> result = add_magnitude(left, right);
        result.negative = left.negative && !result.is_zero();
        return result;
    }
    int ordering = compare_magnitude(left, right);
    if (ordering == 0) {
        ExactInteger<LimbCount> result;
        result.overflow = left.overflow || right.overflow;
        return result;
    }
    if (ordering > 0) {
        ExactInteger<LimbCount> result = subtract_magnitude(left, right);
        result.negative = left.negative;
        return result;
    }
    ExactInteger<LimbCount> result = subtract_magnitude(right, left);
    result.negative = right.negative;
    return result;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator-(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return left + (-right);
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator*(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    ExactInteger<LimbCount> result;
    for (int left_index = 0;
         left_index < ExactInteger<LimbCount>::LIMBS;
         ++left_index) {
        uint64_t carry = 0;
        for (int right_index = 0;
             right_index + left_index < ExactInteger<LimbCount>::LIMBS;
             ++right_index) {
            int output = left_index + right_index;
            uint64_t product =
                uint64_t(left.limb[left_index]) * right.limb[right_index]
                + result.limb[output] + carry;
            result.limb[output] = uint32_t(product);
            carry = product >> 32;
        }
        if (carry != 0) {
            result.overflow = true;
        }
        for (int right_index =
                 ExactInteger<LimbCount>::LIMBS - left_index;
             right_index < ExactInteger<LimbCount>::LIMBS;
             ++right_index) {
            if (left.limb[left_index] != 0
                && right.limb[right_index] != 0) {
                result.overflow = true;
            }
        }
    }
    result.negative =
        left.negative != right.negative && !result.is_zero();
    result.overflow =
        result.overflow || left.overflow || right.overflow;
    return result;
}

template <int LimbCount>
__device__ int compare_signed(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    if (left.negative != right.negative) {
        return left.negative ? -1 : 1;
    }
    int magnitude = compare_magnitude(left, right);
    return left.negative ? -magnitude : magnitude;
}

template <int LimbCount>
__device__ bool operator<(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return compare_signed(left, right) < 0;
}

template <int LimbCount>
__device__ bool operator<=(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return compare_signed(left, right) <= 0;
}

template <int LimbCount>
__device__ bool operator>=(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return compare_signed(left, right) >= 0;
}

template <int LimbCount>
__device__ bool operator==(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return compare_signed(left, right) == 0;
}

template <int LimbCount>
__device__ bool operator!=(
    const ExactInteger<LimbCount> &left,
    const ExactInteger<LimbCount> &right
) {
    return !(left == right);
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator+(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left + ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator+(
    int64_t left,
    const ExactInteger<LimbCount> &right
) {
    return ExactInteger<LimbCount>(left) + right;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator-(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left - ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator-(
    int64_t left,
    const ExactInteger<LimbCount> &right
) {
    return ExactInteger<LimbCount>(left) - right;
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator*(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left * ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ ExactInteger<LimbCount> operator*(
    int64_t left,
    const ExactInteger<LimbCount> &right
) {
    return ExactInteger<LimbCount>(left) * right;
}

template <int LimbCount>
__device__ bool operator<(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left < ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ bool operator<=(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left <= ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ bool operator>=(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left >= ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ bool operator==(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left == ExactInteger<LimbCount>(right);
}

template <int LimbCount>
__device__ bool operator!=(
    const ExactInteger<LimbCount> &left,
    int64_t right
) {
    return left != ExactInteger<LimbCount>(right);
}

constexpr uint32_t TILE_EDGE = 16;

template <typename Intermediate>
__device__ Intermediate evaluate(
    const ExactConic &conic,
    int64_t horizontal,
    int64_t vertical
) {
    Intermediate h = horizontal;
    Intermediate v = vertical;
    return Intermediate(conic.xx) * h * h
        + Intermediate(conic.xy) * h * v
        + Intermediate(conic.yy) * v * v
        + Intermediate(conic.x) * h
        + Intermediate(conic.y) * v
        + Intermediate(conic.constant);
}

template <typename Intermediate>
__device__ void receive_sign(
    Intermediate numerator,
    Intermediate denominator,
    bool &nonpositive,
    bool &nonnegative
) {
    if (denominator < 0) {
        numerator = -numerator;
    }
    if (numerator <= 0) {
        nonpositive = true;
    }
    if (numerator >= 0) {
        nonnegative = true;
    }
}

template <typename Intermediate>
__device__ bool ratio_inside(
    Intermediate numerator,
    Intermediate denominator,
    int64_t lower,
    int64_t upper
) {
    if (denominator < 0) {
        numerator = -numerator;
        denominator = -denominator;
    }
    return numerator >= lower * denominator
        && numerator <= upper * denominator;
}

template <typename Intermediate>
__device__ bool conic_crosses_region(
    const ExactConic &conic,
    int64_t left,
    int64_t top,
    int64_t right,
    int64_t bottom
) {
    bool nonpositive = false;
    bool nonnegative = false;

    receive_sign(
        evaluate<Intermediate>(conic, left, top),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        evaluate<Intermediate>(conic, right, top),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        evaluate<Intermediate>(conic, right, bottom),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        evaluate<Intermediate>(conic, left, bottom),
        Intermediate(1),
        nonpositive,
        nonnegative
    );

    if (conic.yy != 0) {
        Intermediate denominator = 2 * Intermediate(conic.yy);
        for (int edge = 0; edge < 2; ++edge) {
            int64_t horizontal = edge == 0 ? left : right;
            Intermediate linear =
                Intermediate(conic.xy) * horizontal + conic.y;
            Intermediate numerator = -linear;
            if (ratio_inside(numerator, denominator, top, bottom)) {
                Intermediate constant =
                    Intermediate(conic.xx) * horizontal * horizontal
                    + Intermediate(conic.x) * horizontal + conic.constant;
                Intermediate value_numerator =
                    4 * Intermediate(conic.yy) * constant - linear * linear;
                receive_sign(
                    value_numerator,
                    4 * Intermediate(conic.yy),
                    nonpositive,
                    nonnegative
                );
            }
        }
    }

    if (conic.xx != 0) {
        Intermediate denominator = 2 * Intermediate(conic.xx);
        for (int edge = 0; edge < 2; ++edge) {
            int64_t vertical = edge == 0 ? top : bottom;
            Intermediate linear =
                Intermediate(conic.xy) * vertical + conic.x;
            Intermediate numerator = -linear;
            if (ratio_inside(numerator, denominator, left, right)) {
                Intermediate constant =
                    Intermediate(conic.yy) * vertical * vertical
                    + Intermediate(conic.y) * vertical + conic.constant;
                Intermediate value_numerator =
                    4 * Intermediate(conic.xx) * constant - linear * linear;
                receive_sign(
                    value_numerator,
                    4 * Intermediate(conic.xx),
                    nonpositive,
                    nonnegative
                );
            }
        }
    }

    Intermediate determinant =
        4 * Intermediate(conic.xx) * conic.yy
        - Intermediate(conic.xy) * conic.xy;
    if (determinant != 0) {
        Intermediate horizontal_numerator =
            Intermediate(conic.xy) * conic.y
            - 2 * Intermediate(conic.yy) * conic.x;
        Intermediate vertical_numerator =
            Intermediate(conic.xy) * conic.x
            - 2 * Intermediate(conic.xx) * conic.y;
        if (ratio_inside(horizontal_numerator, determinant, left, right)
            && ratio_inside(vertical_numerator, determinant, top, bottom)) {
            Intermediate value_numerator =
                Intermediate(conic.xx)
                    * horizontal_numerator * horizontal_numerator
                + Intermediate(conic.xy)
                    * horizontal_numerator * vertical_numerator
                + Intermediate(conic.yy)
                    * vertical_numerator * vertical_numerator
                + Intermediate(conic.x)
                    * horizontal_numerator * determinant
                + Intermediate(conic.y)
                    * vertical_numerator * determinant
                + Intermediate(conic.constant)
                    * determinant * determinant;
            receive_sign(
                value_numerator,
                determinant * determinant,
                nonpositive,
                nonnegative
            );
        }
    }
    return nonpositive && nonnegative;
}

template <typename Intermediate>
__device__ void conic_support_work(
    const ExactConic *conics,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t conic_count,
    uint32_t work
) {
    uint32_t tile_columns = (width + TILE_EDGE - 1) / TILE_EDGE;
    uint32_t tile_rows = (height + TILE_EDGE - 1) / TILE_EDGE;
    uint32_t tile_count = tile_columns * tile_rows;
    uint32_t work_count = tile_count * conic_count;
    if (work >= work_count) {
        return;
    }
    uint32_t conic_index = work / tile_count;
    uint32_t tile = work % tile_count;
    uint32_t tile_column = tile % tile_columns;
    uint32_t tile_row = tile / tile_columns;
    int64_t left = int64_t(tile_column * TILE_EDGE);
    int64_t top = int64_t(tile_row * TILE_EDGE);
    int64_t right = left + TILE_EDGE < width ? left + TILE_EDGE : width;
    int64_t bottom = top + TILE_EDGE < height ? top + TILE_EDGE : height;
    const ExactConic &conic = conics[conic_index];
    atomicAdd(&query_count[conic.primitive], 1ULL);
    if (!conic_crosses_region<Intermediate>(
        conic, left, top, right, bottom
    )) {
        return;
    }

    uint32_t pixel_count = width * height;
    uint32_t word_count =
        pixel_count / 32U + (pixel_count % 32U == 0U ? 0U : 1U);
    for (int64_t vertical = top; vertical < bottom; ++vertical) {
        for (int64_t horizontal = left; horizontal < right; ++horizontal) {
            atomicAdd(&query_count[conic.primitive], 1ULL);
            if (conic_crosses_region<Intermediate>(
                conic,
                horizontal,
                vertical,
                horizontal + 1,
                vertical + 1
            )) {
                uint32_t pixel = uint32_t(vertical) * width + uint32_t(horizontal);
                atomicOr(
                    &support_words[
                        conic.primitive * word_count + pixel / 32U
                    ],
                    1U << (pixel % 32U)
                );
            }
        }
    }
}

template <typename Intermediate>
__device__ Intermediate line_orientation(
    const ExactSegment &segment,
    int64_t horizontal,
    int64_t vertical
) {
    return Intermediate(segment.line_a) * horizontal
        + Intermediate(segment.line_b) * vertical
        + Intermediate(segment.line_c);
}

template <typename Intermediate>
__device__ bool segment_crosses_region(
    const ExactSegment &segment,
    int64_t left,
    int64_t top,
    int64_t right,
    int64_t bottom
) {
    bool horizontal_overlap =
        right > segment.bound_left && left <= segment.bound_right;
    bool vertical_overlap =
        bottom > segment.bound_top && top <= segment.bound_bottom;
    if (!horizontal_overlap || !vertical_overlap) {
        return false;
    }
    bool nonpositive = false;
    bool nonnegative = false;
    receive_sign(
        line_orientation<Intermediate>(segment, left, top),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        line_orientation<Intermediate>(segment, right, top),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        line_orientation<Intermediate>(segment, right, bottom),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    receive_sign(
        line_orientation<Intermediate>(segment, left, bottom),
        Intermediate(1),
        nonpositive,
        nonnegative
    );
    return nonpositive && nonnegative;
}

template <typename Intermediate>
__device__ void segment_support_work(
    const ExactSegment *segments,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t segment_count,
    uint32_t work
) {
    uint32_t tile_columns = (width + TILE_EDGE - 1) / TILE_EDGE;
    uint32_t tile_rows = (height + TILE_EDGE - 1) / TILE_EDGE;
    uint32_t tile_count = tile_columns * tile_rows;
    uint32_t work_count = tile_count * segment_count;
    if (work >= work_count) {
        return;
    }
    uint32_t segment_index = work / tile_count;
    uint32_t tile = work % tile_count;
    uint32_t tile_column = tile % tile_columns;
    uint32_t tile_row = tile / tile_columns;
    int64_t left = int64_t(tile_column * TILE_EDGE);
    int64_t top = int64_t(tile_row * TILE_EDGE);
    int64_t right = left + TILE_EDGE < width ? left + TILE_EDGE : width;
    int64_t bottom = top + TILE_EDGE < height ? top + TILE_EDGE : height;
    const ExactSegment &segment = segments[segment_index];
    atomicAdd(&query_count[segment.primitive], 1ULL);
    if (!segment_crosses_region<Intermediate>(
        segment, left, top, right, bottom
    )) {
        return;
    }

    uint32_t pixel_count = width * height;
    uint32_t word_count =
        pixel_count / 32U + (pixel_count % 32U == 0U ? 0U : 1U);
    for (int64_t vertical = top; vertical < bottom; ++vertical) {
        for (int64_t horizontal = left; horizontal < right; ++horizontal) {
            atomicAdd(&query_count[segment.primitive], 1ULL);
            if (segment_crosses_region<Intermediate>(
                segment,
                horizontal,
                vertical,
                horizontal + 1,
                vertical + 1
            )) {
                uint32_t pixel = uint32_t(vertical) * width + uint32_t(horizontal);
                atomicOr(
                    &support_words[
                        segment.primitive * word_count + pixel / 32U
                    ],
                    1U << (pixel % 32U)
                );
            }
        }
    }
}

extern "C" __global__ void exact_conic_support(
    const ExactConic *conics,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t conic_count
) {
    conic_support_work<ExactInteger<12>>(
        conics,
        support_words,
        query_count,
        width,
        height,
        conic_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_conic_support_i192(
    const ExactConic *conics,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t conic_count
) {
    conic_support_work<ExactInteger<6>>(
        conics,
        support_words,
        query_count,
        width,
        height,
        conic_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_conic_support_i256(
    const ExactConic *conics,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t conic_count
) {
    conic_support_work<ExactInteger<8>>(
        conics,
        support_words,
        query_count,
        width,
        height,
        conic_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_conic_support_i128(
    const ExactConic *conics,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t conic_count
) {
    conic_support_work<signed __int128>(
        conics,
        support_words,
        query_count,
        width,
        height,
        conic_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_segment_support(
    const ExactSegment *segments,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t segment_count
) {
    segment_support_work<ExactInteger<12>>(
        segments,
        support_words,
        query_count,
        width,
        height,
        segment_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_segment_support_i192(
    const ExactSegment *segments,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t segment_count
) {
    segment_support_work<ExactInteger<6>>(
        segments,
        support_words,
        query_count,
        width,
        height,
        segment_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_segment_support_i256(
    const ExactSegment *segments,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t segment_count
) {
    segment_support_work<ExactInteger<8>>(
        segments,
        support_words,
        query_count,
        width,
        height,
        segment_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}

extern "C" __global__ void exact_segment_support_i128(
    const ExactSegment *segments,
    uint32_t *support_words,
    unsigned long long *query_count,
    uint32_t width,
    uint32_t height,
    uint32_t segment_count
) {
    segment_support_work<signed __int128>(
        segments,
        support_words,
        query_count,
        width,
        height,
        segment_count,
        blockIdx.x * blockDim.x + threadIdx.x
    );
}
