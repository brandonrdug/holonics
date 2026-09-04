#include <stdint.h>

struct RelationPair {
    uint32_t left;
    uint32_t right;
};

struct RelationWindow {
    uint64_t prefix;
    uint32_t left;
    uint32_t right_start;
    uint32_t right_count;
};

__device__ uint64_t exact_absolute_difference(int64_t left, int64_t right) {
    // Unsigned subtraction supplies the exact magnitude even across the
    // signed carrier's zero seam; the selected order prevents underflow.
    return left >= right
        ? uint64_t(left) - uint64_t(right)
        : uint64_t(right) - uint64_t(left);
}

__device__ uint64_t pair_prefix(uint64_t left, uint64_t extent) {
    return left * (2ULL * extent - left - 1ULL) / 2ULL;
}

__device__ RelationPair pair_at(uint64_t address, uint32_t extent) {
    uint64_t low = 0;
    uint64_t high = uint64_t(extent) - 2ULL;
    while (low < high) {
        uint64_t middle = low + (high - low + 1ULL) / 2ULL;
        if (pair_prefix(middle, extent) <= address) {
            low = middle;
        } else {
            high = middle - 1ULL;
        }
    }
    uint64_t prefix = pair_prefix(low, extent);
    return RelationPair{
        uint32_t(low),
        uint32_t(low + 1ULL + address - prefix),
    };
}

__device__ RelationPair window_pair_at(
    uint64_t address,
    const uint32_t *order,
    const RelationWindow *windows,
    uint32_t window_count
) {
    uint32_t low = 0;
    uint32_t high = window_count - 1U;
    while (low < high) {
        uint32_t middle = low + (high - low + 1U) / 2U;
        if (windows[middle].prefix <= address) {
            low = middle;
        } else {
            high = middle - 1U;
        }
    }
    RelationWindow window = windows[low];
    uint64_t offset = address - window.prefix;
    uint32_t right = order[uint64_t(window.right_start) + offset];
    return RelationPair{
        window.left < right ? window.left : right,
        window.left < right ? right : window.left,
    };
}

__device__ uint8_t classify_difference(
    const int64_t *points,
    RelationPair pair,
    const uint64_t *positive,
    const uint64_t *negative,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count
) {
    bool in_positive = false;
    for (uint32_t front = 0; front < positive_count; ++front) {
        bool admitted = true;
        for (uint32_t coordinate = 0; coordinate < dimension; ++coordinate) {
            uint64_t difference = exact_absolute_difference(
                points[uint64_t(pair.left) * dimension + coordinate],
                points[uint64_t(pair.right) * dimension + coordinate]
            );
            if (difference > positive[uint64_t(front) * dimension + coordinate]) {
                admitted = false;
                break;
            }
        }
        if (admitted) {
            in_positive = true;
            break;
        }
    }

    bool in_negative = false;
    for (uint32_t front = 0; front < negative_count; ++front) {
        bool admitted = true;
        for (uint32_t coordinate = 0; coordinate < dimension; ++coordinate) {
            uint64_t difference = exact_absolute_difference(
                points[uint64_t(pair.left) * dimension + coordinate],
                points[uint64_t(pair.right) * dimension + coordinate]
            );
            if (difference < negative[uint64_t(front) * dimension + coordinate]) {
                admitted = false;
                break;
            }
        }
        if (admitted) {
            in_negative = true;
            break;
        }
    }

    // Wire order: together, apart, open, conflicted.
    if (in_positive && in_negative) {
        return 3;
    }
    if (in_positive) {
        return 0;
    }
    if (in_negative) {
        return 1;
    }
    return 2;
}

__device__ bool positive_state(uint8_t state) {
    return state == 0 || state == 3;
}

__device__ int8_t grade_obstruction_kind(uint8_t state, bool returned_together) {
    if (state == 3) {
        return 3;
    }
    if (returned_together && state == 1) {
        return 0;
    }
    if (returned_together && state == 2) {
        return 1;
    }
    if (!returned_together && state == 0) {
        return 2;
    }
    return -1;
}

__device__ uint64_t block_sum_u64(uint64_t value, uint64_t *warp_sums) {
    const uint32_t lane = threadIdx.x & 31U;
    const uint32_t warp = threadIdx.x >> 5U;
    const uint32_t warp_count = (blockDim.x + 31U) >> 5U;
    for (uint32_t offset = 16U; offset != 0; offset >>= 1U) {
        value += __shfl_down_sync(0xffffffffU, value, offset);
    }
    if (lane == 0) {
        warp_sums[warp] = value;
    }
    __syncthreads();
    if (warp == 0) {
        value = lane < warp_count ? warp_sums[lane] : 0;
        for (uint32_t offset = 16U; offset != 0; offset >>= 1U) {
            value += __shfl_down_sync(0xffffffffU, value, offset);
        }
        if (lane == 0) {
            warp_sums[0] = value;
        }
    }
    __syncthreads();
    return warp_sums[0];
}

extern "C" __global__ void exact_relation_all_pairs(
    const int64_t *points,
    const uint64_t *positive,
    const uint64_t *negative,
    uint8_t *states,
    uint32_t point_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count,
    uint64_t pair_count
) {
    uint64_t address = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    states[address] = classify_difference(
        points,
        pair_at(address, point_count),
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
}

extern "C" __global__ void exact_relation_addressed_pairs(
    const int64_t *points,
    const RelationPair *pairs,
    const uint64_t *positive,
    const uint64_t *negative,
    uint8_t *states,
    uint32_t pair_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count
) {
    uint32_t address = blockIdx.x * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    states[address] = classify_difference(
        points,
        pairs[address],
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
}

extern "C" __global__ void exact_relation_count_addressed_positive(
    const int64_t *points,
    const RelationPair *pairs,
    const uint64_t *positive,
    const uint64_t *negative,
    uint64_t *positive_count_out,
    uint32_t pair_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count
) {
    uint32_t address = blockIdx.x * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    uint8_t state = classify_difference(
        points,
        pairs[address],
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
    if (positive_state(state)) {
        atomicAdd((unsigned long long *)positive_count_out, 1ULL);
    }
}

extern "C" __global__ void exact_relation_emit_addressed_positive(
    const int64_t *points,
    const RelationPair *pairs,
    const uint64_t *positive,
    const uint64_t *negative,
    RelationPair *positive_pairs,
    uint8_t *positive_states,
    uint64_t *positive_count_out,
    uint32_t pair_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count
) {
    uint32_t address = blockIdx.x * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    RelationPair pair = pairs[address];
    uint8_t state = classify_difference(
        points,
        pair,
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
    if (positive_state(state)) {
        uint64_t output = atomicAdd((unsigned long long *)positive_count_out, 1ULL);
        positive_pairs[output] = pair;
        positive_states[output] = state;
    }
}

extern "C" __global__ void exact_relation_count_window_positive(
    const int64_t *points,
    const uint32_t *order,
    const RelationWindow *windows,
    const uint64_t *positive,
    const uint64_t *negative,
    uint64_t *positive_count_out,
    uint32_t window_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count,
    uint64_t pair_count
) {
    uint64_t address = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    RelationPair pair = window_pair_at(address, order, windows, window_count);
    uint8_t state = classify_difference(
        points,
        pair,
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
    if (positive_state(state)) {
        atomicAdd((unsigned long long *)positive_count_out, 1ULL);
    }
}

extern "C" __global__ void exact_relation_emit_window_positive(
    const int64_t *points,
    const uint32_t *order,
    const RelationWindow *windows,
    const uint64_t *positive,
    const uint64_t *negative,
    RelationPair *positive_pairs,
    uint8_t *positive_states,
    uint64_t *positive_count_out,
    uint32_t window_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count,
    uint64_t pair_count
) {
    uint64_t address = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (address >= pair_count) {
        return;
    }
    RelationPair pair = window_pair_at(address, order, windows, window_count);
    uint8_t state = classify_difference(
        points,
        pair,
        positive,
        negative,
        dimension,
        positive_count,
        negative_count
    );
    if (positive_state(state)) {
        uint64_t output = atomicAdd((unsigned long long *)positive_count_out, 1ULL);
        positive_pairs[output] = pair;
        positive_states[output] = state;
    }
}

extern "C" __global__ void exact_relation_grade_all_pairs(
    const int64_t *points,
    const uint64_t *positive,
    const uint64_t *negative,
    const uint64_t *membership,
    uint64_t *grade_counts,
    uint64_t *obstruction_count,
    uint32_t point_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count,
    uint64_t pair_count
) {
    constexpr uint32_t items_per_thread = 8U;
    uint64_t local[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    uint64_t local_obstructions = 0;
    uint64_t tile = uint64_t(blockDim.x) * items_per_thread;
    uint64_t first =
        uint64_t(blockIdx.x) * tile + uint64_t(threadIdx.x) * items_per_thread;
    for (uint32_t item = 0; item < items_per_thread; ++item) {
        uint64_t address = first + item;
        if (address >= pair_count) {
            break;
        }
        RelationPair pair = pair_at(address, point_count);
        uint8_t state = classify_difference(
            points,
            pair,
            positive,
            negative,
            dimension,
            positive_count,
            negative_count
        );
        bool together = membership[pair.left] == membership[pair.right];
        if (together) {
            ++local[0];
            if (state == 0) {
                ++local[2];
            } else if (state == 1) {
                ++local[5];
            } else if (state == 2) {
                ++local[4];
            } else {
                ++local[7];
            }
        } else {
            ++local[1];
            if (state == 0) {
                ++local[6];
            } else if (state == 1) {
                ++local[3];
            } else if (state == 3) {
                ++local[7];
            }
        }
        if (grade_obstruction_kind(state, together) >= 0) {
            ++local_obstructions;
        }
    }

    __shared__ uint64_t warp_sums[32];
    for (uint32_t count = 0; count < 8; ++count) {
        uint64_t block_total = block_sum_u64(local[count], warp_sums);
        if (threadIdx.x == 0 && block_total != 0) {
            atomicAdd((unsigned long long *)&grade_counts[count], block_total);
        }
    }
    uint64_t obstruction_total = block_sum_u64(local_obstructions, warp_sums);
    if (threadIdx.x == 0 && obstruction_total != 0) {
        atomicAdd((unsigned long long *)obstruction_count, obstruction_total);
    }
}

extern "C" __global__ void exact_relation_emit_grade_obstructions(
    const int64_t *points,
    const uint64_t *positive,
    const uint64_t *negative,
    const uint64_t *membership,
    RelationPair *obstruction_pairs,
    uint8_t *obstruction_kinds,
    uint64_t *obstruction_count,
    uint32_t point_count,
    uint32_t dimension,
    uint32_t positive_count,
    uint32_t negative_count,
    uint64_t pair_count
) {
    constexpr uint32_t items_per_thread = 8U;
    uint64_t tile = uint64_t(blockDim.x) * items_per_thread;
    uint64_t first =
        uint64_t(blockIdx.x) * tile + uint64_t(threadIdx.x) * items_per_thread;
    for (uint32_t item = 0; item < items_per_thread; ++item) {
        uint64_t address = first + item;
        if (address >= pair_count) {
            break;
        }
        RelationPair pair = pair_at(address, point_count);
        uint8_t state = classify_difference(
            points,
            pair,
            positive,
            negative,
            dimension,
            positive_count,
            negative_count
        );
        bool together = membership[pair.left] == membership[pair.right];
        int8_t kind = grade_obstruction_kind(state, together);
        if (kind >= 0) {
            uint64_t output = atomicAdd((unsigned long long *)obstruction_count, 1ULL);
            obstruction_pairs[output] = pair;
            obstruction_kinds[output] = uint8_t(kind);
        }
    }
}
