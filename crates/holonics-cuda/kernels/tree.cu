// **The landmark tree on the card, stored at the faces where paths part** (campaign 2, Decision 37;
// #73 with #76; owner `src/hnn/tree.rs`).
//
// The receiving parametron's storage as a tree of landmarks (`holonics::hnn::landmark`), mirrored
// on the card: the all-class face read of a phase (the digit-0 split at every splitting dyadic
// cell, each branch's opened path and the join) and the opened-path update of a deposit (each
// mixing chain's β step, a parting chain's split, the founding of the upper part and the leaf, the
// label run, the masses), with the host's exact integer law: every path face a numerator of
// `2^(−M_p)`, every β an odd/odd ratio of `W` bits with its binary exponent, every product and
// quotient in 128-bit words, the carrier's rebase past `u128` at `R` bits (Lean `HNN/LandmarkTree`
// §6′, `HNN/LandmarkCarrier`), and each split's two ratios formed exactly on 512-bit integers and
// carried once at `W` bits (Lean `HNN/LandmarkCompaction.chain_split`). No float. The mirror carries
// what the reads need (the masses, the charts' β and stop weights, the topology, the labels); the
// certificates stay with the host's constitution, whose tree is the owner.
//
// [definition] **The arena** (the host's layout, `hnn::landmark`'s "The arena"; Decision 37): nodes
// numbered in founding order, each a stored chain; `roots[t]` the root of tree `t = branch · 2^B +
// h` (`TREE_NONE` unfounded); the child table an open-addressing hash from `(parent << 32) | letter`
// to the child (linear probing, `TABLE_EMPTY` free); each node's depth word (its bottom depth, its
// branch in the top bit), its label end (one past its bottom's letter in the label pool), its two
// half-unit masses and its chart `(β_n, β_d, β_e, λ̂)`; each join's chart; the label pool; the
// counts `(nodes, letters)`; each branch's summed rungs from the root (a forced depth's rung `0`);
// and the founding chart at each depth (the declared stop prior's `β₀ = 2^(j_d) − 1`).

#include <stdint.h>

typedef unsigned __int128 u128;

#define TREE_NONE 0xffffffffu
#define TABLE_EMPTY 0xffffffffffffffffull
#define TREE_MAX_DEPTH 64
#define TREE_BRANCH_BIT 0x80000000u
#define TREE_MAX_DIGITS 32
// The split's integers: `5W + 3S + 5` bits at most (`src/hnn/tree.rs` refuses a declaration past
// them), in 64-bit limbs.
#define BIG_LIMBS 8

struct TreeChart {
    uint64_t numerator;
    uint64_t denominator;
    int64_t exponent;
    uint64_t stop;
};

struct TreeLaw {
    uint64_t table_mask;
    uint32_t face;
    uint32_t carrier;
    uint32_t rebase;
    uint32_t branches;
    uint32_t depth0;
    uint32_t depth1;
    uint32_t forced0;
    uint32_t forced1;
    uint32_t cells;
    uint32_t stride;
    uint32_t log_stride;
    uint32_t sums_stride;
};

struct TreeArena {
    uint32_t* roots;
    uint64_t* keys;
    uint32_t* values;
    uint32_t* words;
    uint32_t* ends;
    uint32_t* halves;
    TreeChart* charts;
    TreeChart* joins;
    uint32_t* pool;
    uint32_t* counts;
    const uint32_t* sums;
    const TreeChart* founding;
};

// -------------------------------------------------------------------------------------------------
// 128-bit words
// -------------------------------------------------------------------------------------------------

__device__ __forceinline__ uint32_t tree_bits(u128 x) {
    uint64_t hi = (uint64_t)(x >> 64), lo = (uint64_t)x;
    return hi != 0 ? 128u - (uint32_t)__clzll((long long)hi) : (lo != 0 ? 64u - (uint32_t)__clzll((long long)lo) : 0u);
}

__device__ __forceinline__ uint32_t tree_ctz(u128 x) {
    uint64_t lo = (uint64_t)x;
    if (lo != 0) return (uint32_t)__ffsll((long long)lo) - 1u;
    uint64_t hi = (uint64_t)(x >> 64);
    return hi != 0 ? 64u + (uint32_t)__ffsll((long long)hi) - 1u : 128u;
}

// The greatest common divisor of two odd words (binary: subtract, then shed twos).
__device__ u128 tree_odd_gcd(u128 a, u128 b) {
    while (a != b) {
        if (a > b) {
            a -= b;
            a >>= tree_ctz(a);
        } else {
            b -= a;
            b >>= tree_ctz(b);
        }
    }
    return a;
}

// `⟦2^M u/v⟧`: the lattice numerator nearest `u/v` (ties up), inside `[1, 2^M − 1]`.
__device__ __forceinline__ uint64_t tree_round(u128 numerator, u128 denominator, uint32_t face) {
    u128 rounded = (2 * numerator + denominator) / (2 * denominator);
    uint64_t full = 1ull << face;
    uint64_t r = (uint64_t)rounded;
    if (rounded >= (u128)full) r = full - 1;
    if (r < 1) r = 1;
    if (r > full - 1) r = full - 1;
    return r;
}

// **The stop weight** `λ̂ = ⟦β/(1 + β)⟧` on `2^(−M)` (`landmark::Beta::stop_weight`), decided
// before any division once `|e| > M + W` (the single division's realization, whose operands the
// mirror admits: `2W + M + 3 ≤ 128`).
__device__ uint64_t tree_stop_weight(uint64_t numerator, uint64_t denominator, int64_t exponent,
                                     uint32_t face, uint32_t width) {
    uint64_t full = 1ull << face;
    uint64_t reach = (uint64_t)face + width + 1;
    u128 a = numerator, b = denominator;
    u128 twice = ((u128)1) << (face + 1);
    if (exponent >= 0) {
        if ((uint64_t)exponent >= reach) return full;
        u128 g = (a << exponent) + b;
        u128 t = twice * b;
        u128 up = t <= g ? 0 : (t - g + 2 * g - 1) / (2 * g);
        return full - (uint64_t)up;
    } else {
        uint64_t shift = (uint64_t)(-exponent);
        if (shift >= reach) return 0;
        u128 h = a + (b << shift);
        return (uint64_t)((twice * a + h) / (2 * h));
    }
}

// **One step of the carried ratio with the carrier's rebase** (`landmark::Beta::step`).
__device__ TreeChart tree_beta_step(u128 numerator, u128 denominator, int64_t exponent,
                                    uint32_t width, uint32_t rebase, uint32_t face) {
    uint32_t twos_n = tree_ctz(numerator), twos_d = tree_ctz(denominator);
    u128 a = numerator >> twos_n, b = denominator >> twos_d;
    exponent += (int64_t)twos_n - (int64_t)twos_d;
    bool released = false;
    if (width + tree_bits(b) > 128u) {
        uint32_t e = tree_bits(b) - rebase;
        u128 kept = b >> e;
        released = (kept << e) != b;
        b = kept;
        exponent -= (int64_t)e;
        uint32_t t = tree_ctz(b);
        b >>= t;
        exponent -= (int64_t)t;
    }
    u128 common = tree_odd_gcd(a, b);
    a /= common;
    b /= common;
    TreeChart chart;
    if (tree_bits(a) <= width && tree_bits(b) <= width && !released) {
        chart.numerator = (uint64_t)a;
        chart.denominator = (uint64_t)b;
        chart.exponent = exponent;
    } else {
        int64_t shift = (int64_t)width - ((int64_t)tree_bits(a) - (int64_t)tree_bits(b));
        u128 mantissa = shift >= 0 ? (a << shift) / b : a / (b << (uint32_t)(-shift));
        if (tree_bits(mantissa) > width) {
            shift -= 1;
            mantissa = shift >= 0 ? (a << shift) / b : a / (b << (uint32_t)(-shift));
        }
        uint32_t twos = tree_ctz(mantissa);
        chart.numerator = (uint64_t)(mantissa >> twos);
        chart.denominator = 1;
        chart.exponent = exponent - shift + (int64_t)twos;
    }
    chart.stop = tree_stop_weight(chart.numerator, chart.denominator, chart.exponent, face, width);
    return chart;
}

// -------------------------------------------------------------------------------------------------
// the split's integers: 512 bits in 64-bit limbs, least significant first
// -------------------------------------------------------------------------------------------------

struct Big {
    uint64_t w[BIG_LIMBS];
};

__device__ __forceinline__ void big_set(Big& a, u128 x) {
    a.w[0] = (uint64_t)x;
    a.w[1] = (uint64_t)(x >> 64);
    for (int i = 2; i < BIG_LIMBS; ++i) a.w[i] = 0;
}

__device__ __forceinline__ uint32_t big_bits(const Big& a) {
    for (int i = BIG_LIMBS - 1; i >= 0; --i) {
        if (a.w[i] != 0) return 64u * (uint32_t)i + 64u - (uint32_t)__clzll((long long)a.w[i]);
    }
    return 0;
}

__device__ __forceinline__ uint32_t big_ctz(const Big& a) {
    for (int i = 0; i < BIG_LIMBS; ++i) {
        if (a.w[i] != 0) return 64u * (uint32_t)i + (uint32_t)__ffsll((long long)a.w[i]) - 1u;
    }
    return 64u * BIG_LIMBS;
}

__device__ __forceinline__ int big_cmp(const Big& a, const Big& b) {
    for (int i = BIG_LIMBS - 1; i >= 0; --i) {
        if (a.w[i] != b.w[i]) return a.w[i] > b.w[i] ? 1 : -1;
    }
    return 0;
}

__device__ void big_shl(Big& a, uint32_t k) {
    uint32_t limbs = k / 64, bits = k % 64;
    for (int i = BIG_LIMBS - 1; i >= 0; --i) {
        int from = i - (int)limbs;
        uint64_t hi = from >= 0 ? a.w[from] : 0;
        uint64_t lo = from - 1 >= 0 ? a.w[from - 1] : 0;
        a.w[i] = bits == 0 ? hi : (hi << bits) | (lo >> (64 - bits));
    }
}

__device__ void big_shr(Big& a, uint32_t k) {
    uint32_t limbs = k / 64, bits = k % 64;
    for (int i = 0; i < BIG_LIMBS; ++i) {
        int from = i + (int)limbs;
        uint64_t lo = from < BIG_LIMBS ? a.w[from] : 0;
        uint64_t hi = from + 1 < BIG_LIMBS ? a.w[from + 1] : 0;
        a.w[i] = bits == 0 ? lo : (lo >> bits) | (hi << (64 - bits));
    }
}

__device__ __forceinline__ void big_add(Big& a, const Big& b) {
    uint64_t carry = 0;
    for (int i = 0; i < BIG_LIMBS; ++i) {
        u128 sum = (u128)a.w[i] + b.w[i] + carry;
        a.w[i] = (uint64_t)sum;
        carry = (uint64_t)(sum >> 64);
    }
}

// `a − b`, with `a ≥ b`.
__device__ __forceinline__ void big_sub(Big& a, const Big& b) {
    uint64_t borrow = 0;
    for (int i = 0; i < BIG_LIMBS; ++i) {
        uint64_t x = a.w[i], y = b.w[i];
        uint64_t d = x - y - borrow;
        borrow = (x < y || (x == y && borrow)) ? 1 : 0;
        a.w[i] = d;
    }
}

__device__ __forceinline__ void big_mul64(Big& a, uint64_t m) {
    uint64_t carry = 0;
    for (int i = 0; i < BIG_LIMBS; ++i) {
        u128 product = (u128)a.w[i] * m + carry;
        a.w[i] = (uint64_t)product;
        carry = (uint64_t)(product >> 64);
    }
}

// `2^k − 1`.
__device__ void big_ladder(Big& a, uint32_t rung) {
    for (int i = 0; i < BIG_LIMBS; ++i) {
        uint32_t low = 64u * (uint32_t)i;
        a.w[i] = rung >= low + 64 ? ~0ull : (rung > low ? (1ull << (rung - low)) - 1 : 0);
    }
}

// The greatest common divisor of two odd integers (binary: subtract, then shed twos).
__device__ void big_odd_gcd(Big a, Big b, Big& g) {
    int order = big_cmp(a, b);
    while (order != 0) {
        if (order > 0) {
            big_sub(a, b);
            big_shr(a, big_ctz(a));
        } else {
            big_sub(b, a);
            big_shr(b, big_ctz(b));
        }
        order = big_cmp(a, b);
    }
    g = a;
}

// `⌊num/den⌋` for a quotient below `2^127` (shift and subtract).
__device__ u128 big_quotient(const Big& num, const Big& den) {
    if (big_cmp(num, den) < 0) return 0;
    uint32_t k = big_bits(num) - big_bits(den);
    Big d = den, r = num;
    big_shl(d, k);
    u128 q = 0;
    for (int i = (int)k; i >= 0; --i) {
        q <<= 1;
        if (big_cmp(r, d) >= 0) {
            big_sub(r, d);
            q |= 1;
        }
        big_shr(d, 1);
    }
    return q;
}

// **A positive ratio `(N/D) 2^e` carried at width `W`** (`landmark::carry_ratio`): its twos moved
// into the exponent and its odd parts reduced, exact when both fit `W` bits, otherwise its `W`-bit
// floor mantissa `m' ∈ [2^(W−1), 2^W)` (unique for the ratio, so read from the unreduced parts).
__device__ void big_carry(Big n, Big d, int64_t exponent, uint32_t width, uint64_t& numerator,
                          uint64_t& denominator, int64_t& carried) {
    uint32_t tn = big_ctz(n), td = big_ctz(d);
    big_shr(n, tn);
    big_shr(d, td);
    exponent += (int64_t)tn - (int64_t)td;
    uint32_t bn = big_bits(n), bd = big_bits(d);
    // Reduced parts within `W` bits need `N, D < 2^W g` with `g ≤ min(N, D)`: decided otherwise.
    if (bd <= bn + width && bn <= bd + width) {
        Big g;
        big_odd_gcd(n, d, g);
        Big reach = g;
        big_shl(reach, width);
        if (big_cmp(n, reach) < 0 && big_cmp(d, reach) < 0) {
            numerator = (uint64_t)big_quotient(n, g);
            denominator = (uint64_t)big_quotient(d, g);
            carried = exponent;
            return;
        }
    }
    int64_t shift = (int64_t)width - ((int64_t)bn - (int64_t)bd);
    Big num = n, den = d;
    if (shift >= 0) {
        big_shl(num, (uint32_t)shift);
    } else {
        big_shl(den, (uint32_t)(-shift));
    }
    u128 m = big_quotient(num, den);
    if (tree_bits(m) > width) {
        shift -= 1;
        m >>= 1;
    }
    uint32_t twos = tree_ctz(m);
    numerator = (uint64_t)(m >> twos);
    denominator = 1;
    carried = exponent - shift + (int64_t)twos;
}

// **A chain's split ratios** (`landmark::Beta::split`; Lean `HNN/LandmarkCompaction.chain_split`):
// `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)` and `β_u = (2^(S_up) − 1) 2^(S_low) β/(β (2^(S_low) − 1) +
// 2^S − 1)`, `β = (n/d) 2^e`, each formed exactly and carried once at `W` bits. [proved-derived;
// agent-inferred] Past `e ≥ E* = 2W + 2S + 4` the carried `β_u` no longer moves with `e` (its
// mantissa branch is decided, and `β_u` lies within a part of `2^(−W)` below the limit whose
// fraction's denominator is below `2^(S+2)`), and past `−e ≥ F* = 3W + 2S + 4` it moves only by its
// exponent, `2^(e + F*)`; so the integers are formed at the capped exponent and hold `5W + 3S + 5`
// bits (the host's exact `BigUint` split is the parity target, `hnn_tree_split_ratios`).
__device__ void tree_split(uint64_t n, uint64_t d, int64_t e, uint32_t upper_rung,
                           uint32_t lower_rung, uint32_t width, TreeChart& upper,
                           TreeChart& lower) {
    uint32_t whole = upper_rung + lower_rung;
    Big up, low, all;
    big_ladder(up, upper_rung);
    big_ladder(low, lower_rung);
    big_ladder(all, whole);
    Big ln = low, td = all;
    big_mul64(ln, n);
    big_mul64(td, d);
    big_carry(ln, td, e, width, lower.numerator, lower.denominator, lower.exponent);
    Big un = up;
    big_mul64(un, n);
    Big numerator = un, denominator;
    int64_t released = 0;
    if (e >= 0) {
        int64_t cap = 2 * (int64_t)width + 2 * (int64_t)whole + 4;
        uint32_t at = (uint32_t)(e < cap ? e : cap);
        big_shl(numerator, lower_rung + at);
        denominator = ln;
        big_shl(denominator, at);
        big_add(denominator, td);
    } else {
        int64_t cap = 3 * (int64_t)width + 2 * (int64_t)whole + 4;
        int64_t f = -e;
        uint32_t at = (uint32_t)(f < cap ? f : cap);
        released = f - (int64_t)at;
        big_shl(numerator, lower_rung);
        denominator = td;
        big_shl(denominator, at);
        big_add(denominator, ln);
    }
    big_carry(numerator, denominator, 0, width, upper.numerator, upper.denominator,
              upper.exponent);
    upper.exponent -= released;
}

// -------------------------------------------------------------------------------------------------
// the arena
// -------------------------------------------------------------------------------------------------

__device__ __forceinline__ uint64_t tree_hash(uint64_t key) {
    uint64_t z = key + 0x9E3779B97F4A7C15ull;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

// The slot holding `(parent, letter)`, or `TABLE_EMPTY` (as a slot: none).
__device__ uint64_t tree_slot(const uint64_t* keys, uint64_t mask, uint32_t parent,
                              uint32_t letter) {
    uint64_t key = ((uint64_t)parent << 32) | letter;
    uint64_t slot = tree_hash(key) & mask;
    while (true) {
        uint64_t found = keys[slot];
        if (found == key) return slot;
        if (found == TABLE_EMPTY) return TABLE_EMPTY;
        slot = (slot + 1) & mask;
    }
}

__device__ uint32_t tree_child(const uint64_t* keys, const uint32_t* values, uint64_t mask,
                               uint32_t parent, uint32_t letter) {
    uint64_t slot = tree_slot(keys, mask, parent, letter);
    return slot == TABLE_EMPTY ? TREE_NONE : values[slot];
}

// Insert a new child: the slot it took.
__device__ uint64_t tree_insert(uint64_t* keys, uint32_t* values, uint64_t mask, uint32_t parent,
                                uint32_t letter, uint32_t child) {
    uint64_t key = ((uint64_t)parent << 32) | letter;
    uint64_t slot = tree_hash(key) & mask;
    while (true) {
        unsigned long long previous =
            atomicCAS((unsigned long long*)&keys[slot], (unsigned long long)TABLE_EMPTY,
                      (unsigned long long)key);
        if (previous == TABLE_EMPTY) {
            values[slot] = child;
            return slot;
        }
        slot = (slot + 1) & mask;
    }
}

__device__ __forceinline__ uint32_t tree_bottom(const uint32_t* words, uint32_t node) {
    return words[node] & ~TREE_BRANCH_BIT;
}

// **The chart a chain of summed rung `S ≥ 1` is founded with** (`landmark::Law::chain`):
// `2^S − 1`, carried as `(2^W − 1) 2^(S − W)` past `W` bits.
__device__ TreeChart tree_chain(uint32_t rung, uint32_t face, uint32_t width) {
    TreeChart chart;
    if (rung <= width) {
        chart.numerator = (1ull << rung) - 1;
        chart.exponent = 0;
    } else {
        chart.numerator = (1ull << width) - 1;
        chart.exponent = (int64_t)(rung - width);
    }
    chart.denominator = 1;
    chart.stop = tree_stop_weight(chart.numerator, 1, chart.exponent, face, width);
    return chart;
}

// One branch's read: the stored nodes its walk opened with each level's bottom depth (the parting
// chain's the depth where it parts), where it stops, the parting chain's two parts, and the digit-0
// faces `q̂_ℓ(0)` at the levels `ℓ = 0, …, top`.
struct TreeRead {
    uint32_t nodes[TREE_MAX_DEPTH + 1];
    uint8_t bottoms[TREE_MAX_DEPTH + 1];
    uint64_t faces[TREE_MAX_DEPTH + 1];
    uint32_t count;
    uint32_t leaf;
    uint32_t parting;
    uint32_t has_lower;
    TreeChart upper;
    TreeChart lower;
};

// **A chain's split at `depth`** (`landmark::Law::part`): the stored chain `node` from `top` parts
// at `depth`; above the forced depths its upper part passes its face (the founding chart), above a
// leaf it is founded at `2^(S_up) − 1`, above an internal bottom both parts' ratios are formed.
__device__ void tree_part(const TreeLaw& law, const TreeArena& a, uint32_t branch, uint32_t top,
                          uint32_t node, uint32_t depth, TreeRead& read) {
    const uint32_t* sums = a.sums + (uint64_t)branch * law.sums_stride;
    uint32_t branch_depth = branch == 0 ? law.depth0 : law.depth1;
    uint32_t bottom = tree_bottom(a.words, node);
    uint32_t upper_rung = sums[depth + 1] - sums[top];
    read.has_lower = 0;
    if (upper_rung == 0) {
        read.upper = a.founding[depth];
        return;
    }
    if (bottom == branch_depth) {
        read.upper = tree_chain(upper_rung, law.face, law.carrier);
        return;
    }
    uint32_t lower_rung = sums[bottom + 1] - sums[depth + 1];
    TreeChart chart = a.charts[node];
    tree_split(chart.numerator, chart.denominator, chart.exponent, upper_rung, lower_rung,
               law.carrier, read.upper, read.lower);
    read.upper.stop = tree_stop_weight(read.upper.numerator, read.upper.denominator,
                                       read.upper.exponent, law.face, law.carrier);
    read.lower.stop = tree_stop_weight(read.lower.numerator, read.lower.denominator,
                                       read.lower.exponent, law.face, law.carrier);
    read.has_lower = 1;
}

// **One branch's read** (`landmark::Law::read`): the walk from the root, each stored node's label
// compared letter by letter below its top to its bottom; the first letter that differs parts the
// path at the depth above it (the chain splits there, `tree_part`); a leaf at `D` stops the walk at
// its own face; a missing child stops it at the prior `½`. Then the faces bottom-up: a level above
// the forced depths passes its child's face, a mixing level reads `⟦λ̂ k(0) + (1 − λ̂) q̂'(0)⟧`.
__device__ void tree_read(const TreeLaw& law, const TreeArena& a, uint32_t branch,
                          uint32_t dyadic, const uint32_t* letters, TreeRead& read) {
    uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
    uint32_t forced = branch == 0 ? law.forced0 : law.forced1;
    uint64_t full = 1ull << law.face;
    read.count = 0;
    read.leaf = 0;
    read.parting = TREE_NONE;
    read.has_lower = 0;
    uint32_t node = a.roots[branch * law.cells + dyadic];
    uint32_t top = 0;
    while (node != TREE_NONE) {
        uint32_t bottom = tree_bottom(a.words, node);
        read.nodes[read.count] = node;
        read.bottoms[read.count] = (uint8_t)bottom;
        read.count++;
        if (bottom > top) {
            uint32_t end = a.ends[node];
            uint32_t d = top + 1;
            for (; d <= bottom; ++d) {
                if (a.pool[end + d - 1 - bottom] != letters[d - 1]) break;
            }
            if (d <= bottom) {
                read.parting = d - 1;
                break;
            }
        }
        if (bottom == depth) {
            read.leaf = 1;
            break;
        }
        node = tree_child(a.keys, a.values, law.table_mask, node, letters[bottom]);
        top = bottom + 1;
    }
    if (read.parting != TREE_NONE) {
        uint32_t last = read.count - 1;
        tree_part(law, a, branch, top, read.nodes[last], read.parting, read);
        read.bottoms[last] = (uint8_t)read.parting;
    }
    uint32_t level_top = read.leaf ? read.count - 1 : read.count;
    if (read.leaf) {
        uint32_t leaf = read.nodes[level_top];
        u128 u = a.halves[2 * leaf], v = (u128)a.halves[2 * leaf] + a.halves[2 * leaf + 1];
        read.faces[level_top] = tree_round(u << law.face, v, law.face);
    } else {
        read.faces[level_top] = full / 2;
    }
    for (int level = (int)level_top - 1; level >= 0; --level) {
        if (read.bottoms[level] < forced) {
            read.faces[level] = read.faces[level + 1];
        } else {
            uint32_t at = read.nodes[level];
            u128 u = a.halves[2 * at], v = (u128)a.halves[2 * at] + a.halves[2 * at + 1];
            u128 stop = (read.parting != TREE_NONE && (uint32_t)level + 1 == read.count)
                            ? read.upper.stop
                            : a.charts[at].stop;
            u128 numerator =
                ((stop * u) << law.face) + ((u128)full - stop) * read.faces[level + 1] * v;
            read.faces[level] = tree_round(numerator, v << law.face, law.face);
        }
    }
}

__device__ __forceinline__ uint64_t tree_side(uint64_t zero, uint32_t symbol, uint32_t face) {
    return symbol == 0 ? zero : (1ull << face) - zero;
}

// -------------------------------------------------------------------------------------------------
// the all-class read
// -------------------------------------------------------------------------------------------------
//
// [definition] **`hnn_tree_splits`**: for phase `blockIdx.x` and each splitting dyadic cell
// `h = splitting[i]`, the digit-0 face `q̂_h`: each branch's opened path read bottom-up
// (`landmark::Law::read`) and, in an enlarged tree, their join `⟦λ̂_h q̂_cells + (1 − λ̂_h)
// q̂_bundles⟧`. Realization: one block per phase; thread `t` takes the cells `i ≡ t mod
// blockDim.x`, each cell's paths serial in its thread (at most `D_b + 1` stored chains and `D_b`
// letters compared a branch, and at most one split's ratios). Every thread reads the shared
// immutable arena and writes its own output word: the regions commute.
extern "C" __global__ void hnn_tree_splits(TreeLaw law, TreeArena arena, const uint32_t* splitting,
                                           uint32_t count, const uint32_t* letters,
                                           uint64_t* out) {
    uint32_t phase = blockIdx.x;
    const uint32_t* address = letters + (uint64_t)phase * law.branches * law.stride;
    for (uint32_t i = threadIdx.x; i < count; i += blockDim.x) {
        uint32_t h = splitting[i];
        TreeRead cells;
        tree_read(law, arena, 0, h, address, cells);
        uint64_t face = cells.faces[0];
        if (law.branches > 1) {
            TreeRead bundles;
            tree_read(law, arena, 1, h, address + law.stride, bundles);
            u128 stop = arena.joins[h].stop;
            u128 full = (u128)1 << law.face;
            face = tree_round(stop * cells.faces[0] + (full - stop) * bundles.faces[0], full,
                              law.face);
        }
        out[(uint64_t)phase * count + i] = face;
    }
}

// -------------------------------------------------------------------------------------------------
// the opened-path update
// -------------------------------------------------------------------------------------------------
//
// [definition] **`hnn_tree_deposit`**: one cell's deposit (`landmark::Law::apply` without the
// certificates, which the host's tree keeps). Thread `i` takes the `i`-th opened digit
// `(h, b) = digits[i]` and reads each branch's path at the standing. The block then holds each
// branch's label run (the address's letters below the shallowest leaf this cell founds in that
// branch, at the pool's end: the least leaf top a block minimum, the letters copied by every
// thread) and numbers the nodes to found in the host's order (digit by digit, then branch by
// branch, a parting chain's upper part before the leaf: a block prefix sum). Each thread then steps
// its paths' mixing chains' β by `k(b)/q̂_(ℓ+1)(b)` bottom-up (a parting chain's upper part on its
// split chart), splits the parting chain (the lower part keeps its counts at `β_ℓ`, the upper part
// is founded with the chain's counts and its stepped chart, the parent relinked to it, the lower
// part linked below it by its letter at `k + 1`), founds its leaf labelled to `D`, counts the digit,
// and steps the join's β by `q̂_cells(b)/q̂_bundles(b)`. The digits of one cell descend different
// dyadic cells, so their trees are disjoint: the threads write disjoint nodes, slots and joins,
// their insertions take distinct keys by `atomicCAS`, and their founded numbers are disjoint. With
// `logging`, each thread writes what it overwrote into its own stride of the undo log.
//
// The undo log, per digit: the walks' nodes with their old masses and charts (stride
// `law.log_stride`), the slots inserted (4), the slots relinked with their old children (2), the
// roots set with their old roots (2), and the join's old chart; its counts
// `(logged, inserted, relinked, rooted)` per digit and, after them, the arena's counts before.
struct TreeLog {
    uint32_t* nodes;
    uint32_t* halves;
    TreeChart* charts;
    uint64_t* slots;
    uint64_t* relinked;
    uint32_t* children;
    uint32_t* trees;
    uint32_t* roots;
    TreeChart* joins;
    uint32_t* counts;
};

#define LOG_SLOTS 4
#define LOG_RELINKS 2
#define LOG_ROOTS 2

extern "C" __global__ void hnn_tree_deposit(TreeLaw law, TreeArena a, const uint32_t* letters,
                                            const uint32_t* digits, uint32_t count, TreeLog log,
                                            uint32_t logging) {
    __shared__ uint32_t founding[2 * TREE_MAX_DIGITS];
    __shared__ uint32_t run_top[2];
    __shared__ uint32_t run_start[2];
    __shared__ uint32_t base;
    uint32_t i = threadIdx.x;
    TreeRead reads[2];
    uint32_t need[2] = {0, 0};
    uint32_t h = 0, symbol = 0;
    if (i < 2) run_top[i] = TREE_NONE;
    __syncthreads();
    if (i < count) {
        h = digits[2 * i];
        symbol = digits[2 * i + 1];
        for (uint32_t branch = 0; branch < law.branches; ++branch) {
            TreeRead& read = reads[branch];
            tree_read(law, a, branch, h, letters + branch * law.stride, read);
            need[branch] = (read.parting != TREE_NONE ? 1u : 0u) + (read.leaf ? 0u : 1u);
            if (!read.leaf) {
                uint32_t top = read.count == 0 ? 0 : read.bottoms[read.count - 1] + 1u;
                atomicMin(&run_top[branch], top);
            }
        }
    }
    if (i < TREE_MAX_DIGITS) {
        founding[2 * i] = i < count ? need[0] : 0;
        founding[2 * i + 1] = i < count ? need[1] : 0;
    }
    __syncthreads();
    if (i == 0) {
        base = a.counts[0];
        uint32_t held = a.counts[1];
        if (logging) {
            log.counts[4 * TREE_MAX_DIGITS] = base;
            log.counts[4 * TREE_MAX_DIGITS + 1] = held;
        }
        uint32_t running = 0;
        for (uint32_t k = 0; k < 2 * count; ++k) {
            uint32_t n = founding[k];
            founding[k] = running;
            running += n;
        }
        a.counts[0] = base + running;
        for (uint32_t branch = 0; branch < law.branches; ++branch) {
            uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
            run_start[branch] = held;
            if (run_top[branch] != TREE_NONE) held += depth - run_top[branch];
        }
        a.counts[1] = held;
    }
    __syncthreads();
    // The label runs, copied by every thread: letter `top + k` of the branch at the run's `k`.
    for (uint32_t branch = 0; branch < law.branches; ++branch) {
        uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
        uint32_t top = run_top[branch];
        if (top == TREE_NONE) continue;
        for (uint32_t k = i; k < depth - top; k += blockDim.x) {
            a.pool[run_start[branch] + k] = letters[branch * law.stride + top + k];
        }
    }
    if (i >= count) return;
    uint64_t full = 1ull << law.face;
    uint32_t logged = 0, inserted = 0, relinked = 0, rooted = 0;
    uint64_t sides[2] = {0, 0};
    uint32_t next = base + founding[2 * i];
    for (uint32_t branch = 0; branch < law.branches; ++branch) {
        TreeRead& read = reads[branch];
        const uint32_t* flat = letters + branch * law.stride;
        uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
        uint32_t forced = branch == 0 ? law.forced0 : law.forced1;
        uint32_t tree = branch * law.cells + h;
        uint32_t word_bit = branch == 1 ? TREE_BRANCH_BIT : 0u;
        sides[branch] = tree_side(read.faces[0], symbol, law.face);
        // Log every stored node the walk opened: its masses and its chart (a parting chain's is
        // replaced by its lower part's).
        if (logging) {
            for (uint32_t k = 0; k < read.count; ++k) {
                uint32_t node = read.nodes[k];
                uint32_t at = i * law.log_stride + logged++;
                log.nodes[at] = node;
                log.halves[2 * at] = a.halves[2 * node];
                log.halves[2 * at + 1] = a.halves[2 * node + 1];
                log.charts[at] = a.charts[node];
            }
        }
        // The β steps, bottom-up over the stored levels past the forced depths.
        uint32_t level_top = read.leaf ? read.count - 1 : read.count;
        bool parts = read.parting != TREE_NONE;
        for (int level = (int)read.count - 1; level >= 0; --level) {
            if (read.bottoms[level] < forced) break;
            if ((uint32_t)level >= level_top) continue;
            uint32_t node = read.nodes[level];
            u128 u = a.halves[2 * node + symbol];
            u128 v = (u128)a.halves[2 * node] + a.halves[2 * node + 1];
            u128 below = tree_side(read.faces[level + 1], symbol, law.face);
            bool upper = parts && (uint32_t)level + 1 == read.count;
            TreeChart chart = upper ? read.upper : a.charts[node];
            TreeChart stepped = tree_beta_step((u128)chart.numerator * u,
                                               (u128)chart.denominator * v * below,
                                               chart.exponent + (int64_t)law.face, law.carrier,
                                               law.rebase, law.face);
            if (upper) {
                read.upper = stepped;
            } else {
                a.charts[node] = stepped;
            }
        }
        // The parting chain splits: its upper part is founded above its lower part.
        if (parts) {
            uint32_t last = read.count - 1;
            uint32_t chain = read.nodes[last];
            uint32_t at = read.parting;
            uint32_t chain_top = last > 0 ? read.bottoms[last - 1] + 1u : 0u;
            uint32_t bottom = tree_bottom(a.words, chain);
            uint32_t end = a.ends[chain];
            uint32_t key = a.pool[end - 1 - (bottom - (at + 1))];
            uint32_t upper = next++;
            a.words[upper] = at | word_bit;
            a.ends[upper] = end - (bottom - at);
            if (at >= forced) {
                a.halves[2 * upper] = a.halves[2 * chain];
                a.halves[2 * upper + 1] = a.halves[2 * chain + 1];
            } else {
                a.halves[2 * upper] = 1;
                a.halves[2 * upper + 1] = 1;
            }
            a.charts[upper] = read.upper;
            if (read.has_lower) a.charts[chain] = read.lower;
            if (last > 0) {
                uint64_t slot = tree_slot(a.keys, law.table_mask, read.nodes[last - 1],
                                          flat[chain_top - 1]);
                if (logging) {
                    log.relinked[i * LOG_RELINKS + relinked] = slot;
                    log.children[i * LOG_RELINKS + relinked] = a.values[slot];
                }
                relinked++;
                a.values[slot] = upper;
            } else {
                if (logging) {
                    log.trees[i * LOG_ROOTS + rooted] = tree;
                    log.roots[i * LOG_ROOTS + rooted] = a.roots[tree];
                }
                rooted++;
                a.roots[tree] = upper;
            }
            uint64_t slot = tree_insert(a.keys, a.values, law.table_mask, upper, key, chain);
            if (logging) log.slots[i * LOG_SLOTS + inserted] = slot;
            inserted++;
            read.nodes[last] = upper;
        }
        // The arrival founds its leaf, labelled to the declared depth.
        if (!read.leaf) {
            uint32_t leaf_top = read.count == 0 ? 0 : read.bottoms[read.count - 1] + 1u;
            uint32_t leaf = next++;
            a.words[leaf] = depth | word_bit;
            a.ends[leaf] = run_start[branch] + (depth - run_top[branch]);
            a.halves[2 * leaf] = 1;
            a.halves[2 * leaf + 1] = 1;
            a.charts[leaf] = a.founding[depth];
            if (read.count > 0) {
                uint64_t slot = tree_insert(a.keys, a.values, law.table_mask,
                                            read.nodes[read.count - 1], flat[leaf_top - 1], leaf);
                if (logging) log.slots[i * LOG_SLOTS + inserted] = slot;
                inserted++;
            } else {
                if (logging) {
                    log.trees[i * LOG_ROOTS + rooted] = tree;
                    log.roots[i * LOG_ROOTS + rooted] = a.roots[tree];
                }
                rooted++;
                a.roots[tree] = leaf;
            }
            read.nodes[read.count] = leaf;
            read.bottoms[read.count] = (uint8_t)depth;
            read.count++;
        }
        for (uint32_t k = 0; k < read.count; ++k) {
            if (read.bottoms[k] >= forced) a.halves[2 * read.nodes[k] + symbol] += 2;
        }
    }
    if (law.branches > 1) {
        TreeChart chart = a.joins[h];
        if (logging) log.joins[i] = chart;
        a.joins[h] = tree_beta_step((u128)chart.numerator * sides[0],
                                    (u128)chart.denominator * sides[1], chart.exponent,
                                    law.carrier, law.rebase, law.face);
    }
    if (logging) {
        log.counts[4 * i] = logged;
        log.counts[4 * i + 1] = inserted;
        log.counts[4 * i + 2] = relinked;
        log.counts[4 * i + 3] = rooted;
    }
    (void)full;
}

// [definition] **`hnn_tree_undo`**: restore what one logged deposit overwrote: thread `i` restores
// its digit's nodes (in reverse), the children it relinked, the roots it set and the join, and frees
// the slots it inserted; thread 0 restores the arena's counts (the founded nodes and the held
// letters past them are then unread). The logged deposit's digits are disjoint, so the threads
// commute; the deposits of a window are undone in reverse, so the table returns slot for slot.
extern "C" __global__ void hnn_tree_undo(TreeLaw law, TreeArena a, const uint32_t* digits,
                                         uint32_t count, TreeLog log) {
    uint32_t i = threadIdx.x;
    if (i < count) {
        uint32_t logged = log.counts[4 * i], inserted = log.counts[4 * i + 1];
        uint32_t relinked = log.counts[4 * i + 2], rooted = log.counts[4 * i + 3];
        for (int k = (int)logged - 1; k >= 0; --k) {
            uint32_t at = i * law.log_stride + (uint32_t)k;
            uint32_t node = log.nodes[at];
            a.halves[2 * node] = log.halves[2 * at];
            a.halves[2 * node + 1] = log.halves[2 * at + 1];
            a.charts[node] = log.charts[at];
        }
        for (uint32_t k = 0; k < relinked; ++k) {
            a.values[log.relinked[i * LOG_RELINKS + k]] = log.children[i * LOG_RELINKS + k];
        }
        for (uint32_t k = 0; k < inserted; ++k) {
            a.keys[log.slots[i * LOG_SLOTS + k]] = TABLE_EMPTY;
        }
        for (int k = (int)rooted - 1; k >= 0; --k) {
            a.roots[log.trees[i * LOG_ROOTS + k]] = log.roots[i * LOG_ROOTS + k];
        }
        if (law.branches > 1) a.joins[digits[2 * i]] = log.joins[i];
    }
    if (i == 0) {
        a.counts[0] = log.counts[4 * TREE_MAX_DIGITS];
        a.counts[1] = log.counts[4 * TREE_MAX_DIGITS + 1];
    }
}

// [definition] **`hnn_tree_gather`**: the parity read of a deposit's touched nodes and joins
// (`CardTree::agrees_at`, the per-deposit lockstep): thread `i` copies node `nodes[i]`'s two
// half-unit masses, its chart `(β, λ̂)`, its depth word and its label end into output row `i`, and
// join `dyadic[i]`'s chart into its join row `i`. It reads the shared arena and writes only its own
// rows, so the threads commute.
extern "C" __global__ void hnn_tree_gather(TreeArena a, const uint32_t* nodes, uint32_t node_count,
                                           const uint32_t* dyadic, uint32_t dyadic_count,
                                           uint32_t* out_halves, TreeChart* out_charts,
                                           uint32_t* out_words, TreeChart* out_joins) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < node_count) {
        uint32_t node = nodes[i];
        out_halves[2 * i] = a.halves[2 * node];
        out_halves[2 * i + 1] = a.halves[2 * node + 1];
        out_charts[i] = a.charts[node];
        out_words[2 * i] = a.words[node];
        out_words[2 * i + 1] = a.ends[node];
    }
    if (i < dyadic_count) out_joins[i] = a.joins[dyadic[i]];
}

// [definition] **`hnn_tree_beta_steps`**: the card's β step (`tree_beta_step`, the carrier's rebase
// included) on `count` operand pairs, one thread each, for its parity against the host's
// `landmark::Beta::step`. Operands as 64-bit halves: `N = n_hi 2^64 + n_lo`, likewise `D`.
extern "C" __global__ void hnn_tree_beta_steps(const uint64_t* operands, const int64_t* exponents,
                                               uint32_t count, uint32_t width, uint32_t rebase,
                                               uint32_t face, TreeChart* out) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= count) return;
    u128 numerator = ((u128)operands[4 * i] << 64) | operands[4 * i + 1];
    u128 denominator = ((u128)operands[4 * i + 2] << 64) | operands[4 * i + 3];
    out[i] = tree_beta_step(numerator, denominator, exponents[i], width, rebase, face);
}

// [definition] **`hnn_tree_split_ratios`**: the card's split (`tree_split`, each ratio's stop
// weight) on `count` charts `(β_n, β_d, β_e)` with rungs `(S_up, S_low)`, one thread each, for its
// parity against the host's `landmark::Beta::split`: row `i` of `out` holds the upper part's chart,
// then the lower part's.
extern "C" __global__ void hnn_tree_split_ratios(const uint64_t* charts, const int64_t* exponents,
                                                 const uint32_t* rungs, uint32_t count,
                                                 uint32_t width, uint32_t face, TreeChart* out) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= count) return;
    TreeChart upper, lower;
    tree_split(charts[2 * i], charts[2 * i + 1], exponents[i], rungs[2 * i], rungs[2 * i + 1],
               width, upper, lower);
    upper.stop = tree_stop_weight(upper.numerator, upper.denominator, upper.exponent, face, width);
    lower.stop = tree_stop_weight(lower.numerator, lower.denominator, lower.exponent, face, width);
    out[2 * i] = upper;
    out[2 * i + 1] = lower;
}
