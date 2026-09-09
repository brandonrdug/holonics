#pragma once
#include <stdint.h>
#include <limits.h>

// Shared exact signed-magnitude arithmetic, extracted without changing the conic operators.
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

template <int LimbCount>
struct ExactInteger {
    static constexpr int LIMBS = LimbCount;
    static constexpr int LIMB_BITS = sizeof(uint32_t) * CHAR_BIT;
    static constexpr int BITS = LIMBS * LIMB_BITS;
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

// Magnitude long division with a positive divisor. One extra limb carries the doubled
// remainder; the quotient has the numerator's sign and truncates toward zero. This extends
// the same recurrence to each declared integer carrier instead of encoding a fixed bit width.
template <int LimbCount>
__device__ ExactInteger<LimbCount> exact_divide_positive(
    const ExactInteger<LimbCount> &numerator,const ExactInteger<LimbCount> &denominator,
    bool *has_remainder
){
    using Integer=ExactInteger<LimbCount>;
    Integer result;*has_remainder=false;
    if(numerator.overflow || denominator.overflow || denominator.negative || denominator.is_zero()){
        result.overflow=true;return result;
    }
    ExactInteger<LimbCount+1> remainder,divisor;
    for(int i=0;i<LimbCount;++i)divisor.limb[i]=denominator.limb[i];
    for(int bit=Integer::BITS-1;bit>=0;--bit){
        uint32_t carry=(numerator.limb[bit/Integer::LIMB_BITS]>>(bit%Integer::LIMB_BITS))&1u;
        for(int i=0;i<LimbCount+1;++i){
            uint32_t next=remainder.limb[i]>>(Integer::LIMB_BITS-1);
            remainder.limb[i]=(remainder.limb[i]<<1)|carry;carry=next;
        }
        if(compare_magnitude(remainder,divisor)>=0){
            remainder=subtract_magnitude(remainder,divisor);
            result.limb[bit/Integer::LIMB_BITS]|=(uint32_t)1u<<(bit%Integer::LIMB_BITS);
        }
    }
    *has_remainder=!remainder.is_zero();
    result.negative=numerator.negative && !result.is_zero();return result;
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
