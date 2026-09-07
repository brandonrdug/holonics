// A checked numerical factorization, not a new current law. For each of three complex banks,
// B(c,z_0,...,z_(k-1)) has pairs (c-z_i,z_i). Its Gram matrix has G00=k, G0i=-1, Gii=2.
// Both complex components are retained. The full root covariance, report and residual remain
// unchanged in shape. If the full covariance/RHS do not admit this factorization, use the full
// solver. No current or contact is discarded to make the condition hold.

__device__ __forceinline__ uint32_t field_bank_row(uint32_t nodes, uint32_t bank, uint32_t port) {
    return bank < 2u ? 4u * port + 2u * bank : 4u * nodes + 2u * port;
}

__device__ __forceinline__ bool field_factor_sum(wide a, wide b, wide *out) {
    const uwide limit = (uwide)1 << 126;
    if (magnitude(a) >= limit || magnitude(b) >= limit) return false;
    if ((a < 0) == (b < 0)) {
        uwide value = magnitude(a) + magnitude(b);
        if (value >= limit) return false;
        *out = a < 0 ? -(wide)value : (wide)value;
    } else {
        *out = a + b; // opposite signs cannot overflow
    }
    return true;
}

__device__ __forceinline__ bool field_factor_product(wide a, wide b, wide *out) {
    const uwide limit = (uwide)1 << 126;
    uwide left = magnitude(a), right = magnitude(b);
    if (left >= limit || right >= limit) return false;
    uwide high, low;
    mul_magnitude_256(left, right, &high, &low);
    if (high || low >= limit) return false;
    *out = (a < 0) != (b < 0) ? -(wide)low : (wide)low;
    return true;
}

// Return 0 for full factorization, 1 for the B factorization, and 2 for exact C=0 identity.
// Only scratch is written. A failed eligibility or scratch bound leaves no refusal flag behind.
__device__ __forceinline__ uint32_t field_balanced_prepare(
    const int64_t *covariance, uint32_t nodes, uint32_t grain,
    const wide *u, const wide *h, wide *matrix, wide *rhs
) {
    const uint32_t dimension = 6u * nodes;
    const size_t count = (size_t)dimension * dimension;
    bool zero = true;
    for (size_t i = 0; i < count; ++i) if (covariance[i]) { zero = false; break; }
    if (zero) return 2u;
    if (!nodes || (nodes & 1u)) return 0u;
    const uint32_t pairs = nodes / 2u, bank_width = pairs + 1u;
    const uint32_t reduced = 3u * bank_width;
    const wide cden = (wide)covariance[count];
    // Real Hermitian coefficients: the same real matrix acts on both complex components.
    for (uint32_t i = 0; i < dimension; i += 2u) {
        for (uint32_t j = 0; j < dimension; j += 2u) {
            if (covariance[(size_t)i * dimension + j + 1u]
                || covariance[(size_t)(i + 1u) * dimension + j]
                || covariance[(size_t)i * dimension + j] != covariance[(size_t)(i + 1u) * dimension + j + 1u]) return 0u;
        }
    }
    // Exact covariance range membership, independently for every root column.
    for (uint32_t bank = 0; bank < 3u; ++bank) {
        for (uint32_t column = 0; column < dimension; column += 2u) {
            uint32_t first = field_bank_row(nodes, bank, 0u), second = field_bank_row(nodes, bank, 1u);
            wide common = (wide)covariance[(size_t)first * dimension + column]
                + (wide)covariance[(size_t)second * dimension + column];
            for (uint32_t bit = 1u; bit < pairs; ++bit) {
                uint32_t left = field_bank_row(nodes, bank, 2u * bit), right = field_bank_row(nodes, bank, 2u * bit + 1u);
                wide sum = (wide)covariance[(size_t)left * dimension + column]
                    + (wide)covariance[(size_t)right * dimension + column];
                if (sum != common) return 0u;
            }
        }
        for (uint32_t plane = 0; plane < 2u; ++plane) {
            for (uint32_t which = 0; which < 2u; ++which) {
                const wide *input = which ? h : u;
                wide common;
                if (!field_factor_sum(input[field_bank_row(nodes, bank, 0u) + plane],
                    input[field_bank_row(nodes, bank, 1u) + plane], &common)) return 0u;
                for (uint32_t bit = 1u; bit < pairs; ++bit) {
                    wide sum;
                    if (!field_factor_sum(input[field_bank_row(nodes, bank, 2u * bit) + plane],
                        input[field_bank_row(nodes, bank, 2u * bit + 1u) + plane], &sum) || sum != common) return 0u;
                }
            }
        }
    }
    // B^T (C_num + Cden I) B. Unscaled sums fit signed wide: dimension^2 <= UINT32_MAX
    // was checked by the caller and every covariance coefficient is an int64 word.
    for (uint32_t i = 0; i < reduced; ++i) {
        uint32_t ibank = i / bank_width, ilocal = i % bank_width;
        for (uint32_t j = 0; j < reduced; ++j) {
            uint32_t jbank = j / bank_width, jlocal = j % bank_width;
            wide value = 0;
            uint32_t icount = ilocal ? 2u : pairs, jcount = jlocal ? 2u : pairs;
            for (uint32_t a = 0; a < icount; ++a) {
                uint32_t ip = ilocal ? 2u * (ilocal - 1u) + a : 2u * a;
                int isign = ilocal && a == 0u ? -1 : 1;
                uint32_t ir = field_bank_row(nodes, ibank, ip);
                for (uint32_t b = 0; b < jcount; ++b) {
                    uint32_t jp = jlocal ? 2u * (jlocal - 1u) + b : 2u * b;
                    int jsign = jlocal && b == 0u ? -1 : 1;
                    uint32_t jr = field_bank_row(nodes, jbank, jp);
                    wide entry = (wide)covariance[(size_t)ir * dimension + jr] + (ir == jr ? cden : 0);
                    value += (isign == jsign) ? entry : -entry;
                }
            }
            if (!field_factor_product(value, (wide)1 << grain, &matrix[(size_t)i * reduced + j])) return 0u;
        }
    }
    // Two RHS vectors, real then imaginary: 2 Cden B^T (Uhat+Hhat).
    for (uint32_t plane = 0; plane < 2u; ++plane) for (uint32_t i = 0; i < reduced; ++i) {
        uint32_t bank = i / bank_width, local = i % bank_width;
        uint32_t extent = local ? 2u : pairs;
        wide value = 0;
        for (uint32_t a = 0; a < extent; ++a) {
            uint32_t port = local ? 2u * (local - 1u) + a : 2u * a;
            uint32_t row = field_bank_row(nodes, bank, port) + plane;
            wide sum;
            if (!field_factor_sum(u[row], h[row], &sum)) return 0u;
            if (local && a == 0u) sum = -sum;
            if (!field_factor_sum(value, sum, &value)) return 0u;
        }
        if (!field_factor_product(value, cden, &value) || !field_factor_product(value, 2, &value)) return 0u;
        rhs[(size_t)plane * reduced + i] = value;
    }
    return 1u;
}
