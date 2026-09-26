// **The landmark tree on the card** (campaign 2, #73 with #76; owner `src/hnn/tree.rs`).
//
// The receiving parametron's storage as a tree of landmarks (`holonics::hnn::landmark`), mirrored
// on the card: the all-class face read of a phase (the digit-0 split at every splitting dyadic
// cell, each branch's opened path and the join) and the opened-path update of a deposit (each
// mixing node's β step, the founding of the missing nodes, the masses), with the host's exact
// integer law: every path face a numerator of `2^(−M_p)`, every β an odd/odd ratio of `W` bits
// with its binary exponent, every product and quotient in 128-bit words, the carrier's rebase past
// `u128` at `R` bits (Lean `HNN/LandmarkTree` §6′, `HNN/LandmarkCarrier`). No float. The mirror
// carries what the reads need (the masses, the charts' β and stop weights, the topology); the
// certificates stay with the host's constitution, whose tree is the owner.
//
// [definition] **The arena** (the host's layout, `hnn::landmark`'s "The arena"): nodes numbered in
// founding order; `roots[t]` the root of tree `t = branch · 2^B + h` (`TREE_NONE` unfounded); the
// child table an open-addressing hash from `(parent << 32) | letter` to the child (linear probing,
// `TABLE_EMPTY` free); each node's two half-unit masses; each node's and each join's chart
// `(β_n, β_d, β_e, λ̂)`.

#include <stdint.h>

typedef unsigned __int128 u128;

#define TREE_NONE 0xffffffffu
#define TABLE_EMPTY 0xffffffffffffffffull
#define TREE_MAX_DEPTH 64

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
    uint32_t pad;
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

// **The stop weight** `λ̂ = ⟦β/(1 + β)⟧` on `2^(−M)` (`landmark::Beta::stop_weight`).
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
// the arena
// -------------------------------------------------------------------------------------------------

__device__ __forceinline__ uint64_t tree_hash(uint64_t key) {
    uint64_t z = key + 0x9E3779B97F4A7C15ull;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

__device__ uint32_t tree_child(const uint64_t* keys, const uint32_t* values, uint64_t mask,
                               uint32_t parent, uint32_t letter) {
    uint64_t key = ((uint64_t)parent << 32) | letter;
    uint64_t slot = tree_hash(key) & mask;
    while (true) {
        uint64_t found = keys[slot];
        if (found == key) return values[slot];
        if (found == TABLE_EMPTY) return TREE_NONE;
        slot = (slot + 1) & mask;
    }
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

// One branch's read: the founded nodes along its letters and the digit-0 faces `q̂_d(0)`.
struct TreeRead {
    uint32_t nodes[TREE_MAX_DEPTH + 1];
    uint64_t faces[TREE_MAX_DEPTH + 1];
    uint32_t founded;
};

__device__ void tree_read(const TreeLaw& law, uint32_t branch, uint32_t dyadic,
                          const uint32_t* roots, const uint64_t* keys, const uint32_t* values,
                          const uint32_t* halves, const TreeChart* charts,
                          const uint32_t* letters, TreeRead& read) {
    uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
    uint32_t forced = branch == 0 ? law.forced0 : law.forced1;
    uint64_t full = 1ull << law.face;
    uint32_t count = 0;
    uint32_t root = roots[branch * law.cells + dyadic];
    if (root != TREE_NONE) {
        read.nodes[count++] = root;
        for (uint32_t i = 0; i < depth && count < depth + 1; ++i) {
            uint32_t child =
                tree_child(keys, values, law.table_mask, read.nodes[count - 1], letters[i]);
            if (child == TREE_NONE) break;
            read.nodes[count++] = child;
        }
    }
    read.founded = count;
    uint32_t top = count < depth ? count : depth;
    if (count == depth + 1) {
        uint32_t node = read.nodes[depth];
        u128 u = halves[2 * node], v = (u128)halves[2 * node] + halves[2 * node + 1];
        read.faces[top] = tree_round(u << law.face, v, law.face);
    } else {
        read.faces[top] = full / 2;
    }
    for (int d = (int)top - 1; d >= 0; --d) {
        if ((uint32_t)d < forced) {
            read.faces[d] = read.faces[d + 1];
        } else {
            uint32_t node = read.nodes[d];
            u128 u = halves[2 * node], v = (u128)halves[2 * node] + halves[2 * node + 1];
            u128 stop = charts[node].stop;
            u128 numerator = ((stop * u) << law.face) + ((u128)full - stop) * read.faces[d + 1] * v;
            read.faces[d] = tree_round(numerator, v << law.face, law.face);
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
// blockDim.x`, each cell's paths serial in its thread (at most `D_b + 1` hash lookups a branch).
// Every thread reads the shared immutable arena and writes its own output word: the regions
// commute.
extern "C" __global__ void hnn_tree_splits(TreeLaw law, const uint32_t* roots,
                                           const uint64_t* keys, const uint32_t* values,
                                           const uint32_t* halves, const TreeChart* charts,
                                           const TreeChart* joins, const uint32_t* splitting,
                                           uint32_t count, const uint32_t* letters,
                                           uint64_t* out) {
    uint32_t phase = blockIdx.x;
    const uint32_t* address = letters + (uint64_t)phase * law.branches * law.stride;
    for (uint32_t i = threadIdx.x; i < count; i += blockDim.x) {
        uint32_t h = splitting[i];
        TreeRead cells;
        tree_read(law, 0, h, roots, keys, values, halves, charts, address, cells);
        uint64_t face = cells.faces[0];
        if (law.branches > 1) {
            TreeRead bundles;
            tree_read(law, 1, h, roots, keys, values, halves, charts, address + law.stride,
                      bundles);
            u128 stop = joins[h].stop;
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
// certificates, which the host's tree keeps): thread `i` takes the `i`-th opened digit
// `(h, b) = digits[i]`, reads each branch's path at the standing, steps each founded mixing node's
// β by `k(b)/q̂_(d+1)(b)` bottom-up with its stop weight, founds the path's missing nodes at the
// numbers the host founds them (digit by digit, then branch by branch: a block prefix sum), counts
// the digit, and steps the join's β by `q̂_cells(b)/q̂_bundles(b)`. The digits of one cell descend
// different dyadic cells, so their trees are disjoint: the threads write disjoint nodes and joins,
// their insertions take distinct keys by `atomicCAS`, and their founded numbers are disjoint. With
// `logging`, each thread writes what it overwrote into its own stride of the undo log.
//
// The undo log, per digit (stride `law.log_stride` entries): the nodes stepped or counted with
// their old masses and charts, the slots inserted, the roots founded, and the join's old chart.
struct TreeLog {
    uint32_t* nodes;
    uint32_t* halves;
    TreeChart* charts;
    uint64_t* slots;
    uint32_t* roots;
    TreeChart* joins;
    uint32_t* counts;
};

extern "C" __global__ void hnn_tree_deposit(TreeLaw law, uint32_t* roots, uint64_t* keys,
                                            uint32_t* values, uint32_t* halves,
                                            TreeChart* charts, TreeChart* joins,
                                            uint32_t* nodes_count, const uint32_t* letters,
                                            const uint32_t* digits, uint32_t count, TreeLog log,
                                            uint32_t logging) {
    __shared__ uint32_t founding[64];
    __shared__ uint32_t base;
    uint32_t i = threadIdx.x;
    TreeRead reads[2];
    uint32_t need[2] = {0, 0};
    uint32_t h = 0, symbol = 0;
    if (i < count) {
        h = digits[2 * i];
        symbol = digits[2 * i + 1];
        for (uint32_t branch = 0; branch < law.branches; ++branch) {
            uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
            tree_read(law, branch, h, roots, keys, values, halves, charts,
                      letters + branch * law.stride, reads[branch]);
            need[branch] = depth + 1 - reads[branch].founded;
        }
    }
    if (i < 32) {
        founding[2 * i] = i < count ? need[0] : 0;
        founding[2 * i + 1] = i < count ? need[1] : 0;
    }
    if (i == 0) base = *nodes_count;
    __syncthreads();
    if (i == 0) {
        uint32_t running = 0;
        for (uint32_t k = 0; k < 2 * count; ++k) {
            uint32_t n = founding[k];
            founding[k] = running;
            running += n;
        }
        if (logging) log.counts[64] = base;
        *nodes_count = base + running;
    }
    __syncthreads();
    if (i >= count) return;
    uint64_t full = 1ull << law.face;
    uint32_t logged = 0, slots = 0;
    uint64_t sides[2] = {0, 0};
    for (uint32_t branch = 0; branch < law.branches; ++branch) {
        TreeRead& read = reads[branch];
        uint32_t depth = branch == 0 ? law.depth0 : law.depth1;
        uint32_t forced = branch == 0 ? law.forced0 : law.forced1;
        sides[branch] = tree_side(read.faces[0], symbol, law.face);
        // Log every existing node this deposit writes: its masses (counted from `forced`) and its
        // chart (stepped below `depth`).
        if (logging) {
            for (uint32_t d = 0; d < read.founded; ++d) {
                uint32_t node = read.nodes[d];
                uint32_t at = i * law.log_stride + logged++;
                log.nodes[at] = node;
                log.halves[2 * at] = halves[2 * node];
                log.halves[2 * at + 1] = halves[2 * node + 1];
                log.charts[at] = charts[node];
            }
        }
        for (int d = (int)read.founded - 1; d >= (int)forced; --d) {
            if ((uint32_t)d < depth) {
                uint32_t node = read.nodes[d];
                u128 u = halves[2 * node + symbol];
                u128 v = (u128)halves[2 * node] + halves[2 * node + 1];
                u128 below = tree_side(read.faces[d + 1], symbol, law.face);
                TreeChart chart = charts[node];
                charts[node] = tree_beta_step((u128)chart.numerator * u,
                                              (u128)chart.denominator * v * below,
                                              chart.exponent + (int64_t)law.face, law.carrier,
                                              law.rebase, law.face);
            }
        }
        // Found the missing nodes at the host's numbers, then count the digit.
        uint32_t next = base + founding[2 * i + branch];
        uint32_t tree = branch * law.cells + h;
        uint32_t path_len = read.founded;
        uint32_t root_founded = TREE_NONE;
        if (path_len == 0) {
            uint32_t node = next++;
            halves[2 * node] = 1;
            halves[2 * node + 1] = 1;
            charts[node] = TreeChart{1, 1, 0, full / 2};
            roots[tree] = node;
            root_founded = tree;
            read.nodes[path_len++] = node;
        }
        const uint32_t* letters_b = letters + branch * law.stride;
        while (path_len < depth + 1) {
            uint32_t parent = read.nodes[path_len - 1];
            uint32_t node = next++;
            halves[2 * node] = 1;
            halves[2 * node + 1] = 1;
            charts[node] = TreeChart{1, 1, 0, full / 2};
            uint64_t slot =
                tree_insert(keys, values, law.table_mask, parent, letters_b[path_len - 1], node);
            if (logging) log.slots[i * law.log_stride + slots++] = slot;
            read.nodes[path_len++] = node;
        }
        if (logging) log.roots[i * 2 + branch] = root_founded;
        for (uint32_t d = forced; d < path_len; ++d) {
            halves[2 * read.nodes[d] + symbol] += 2;
        }
    }
    if (law.branches > 1) {
        TreeChart chart = joins[h];
        if (logging) log.joins[i] = chart;
        joins[h] = tree_beta_step((u128)chart.numerator * sides[0],
                                  (u128)chart.denominator * sides[1], chart.exponent,
                                  law.carrier, law.rebase, law.face);
    }
    if (logging) {
        log.counts[2 * i] = logged;
        log.counts[2 * i + 1] = slots;
    }
}

// [definition] **`hnn_tree_undo`**: restore what one logged deposit overwrote, in reverse: thread
// `i` restores its digit's nodes, joins, roots and inserted slots; thread 0 restores the count.
// The logged deposit's digits are disjoint, so the threads commute.
extern "C" __global__ void hnn_tree_undo(TreeLaw law, uint32_t* roots, uint64_t* keys,
                                         uint32_t* halves, TreeChart* charts, TreeChart* joins,
                                         uint32_t* nodes_count, const uint32_t* digits,
                                         uint32_t count, TreeLog log) {
    uint32_t i = threadIdx.x;
    if (i < count) {
        uint32_t logged = log.counts[2 * i], slots = log.counts[2 * i + 1];
        for (int k = (int)logged - 1; k >= 0; --k) {
            uint32_t at = i * law.log_stride + (uint32_t)k;
            uint32_t node = log.nodes[at];
            halves[2 * node] = log.halves[2 * at];
            halves[2 * node + 1] = log.halves[2 * at + 1];
            charts[node] = log.charts[at];
        }
        for (uint32_t k = 0; k < slots; ++k) {
            keys[log.slots[i * law.log_stride + k]] = TABLE_EMPTY;
        }
        for (uint32_t branch = 0; branch < law.branches; ++branch) {
            uint32_t tree = log.roots[i * 2 + branch];
            if (tree != TREE_NONE) roots[tree] = TREE_NONE;
        }
        if (law.branches > 1) joins[digits[2 * i]] = log.joins[i];
    }
    if (i == 0) *nodes_count = log.counts[64];
}

// [definition] **`hnn_tree_gather`**: the parity read of a deposit's touched nodes and joins
// (`CardTree::agrees_at`, the per-deposit lockstep): thread `i` copies node `nodes[i]`'s two
// half-unit masses and its chart `(β, λ̂)` into output row `i`, and join `dyadic[i]`'s chart into
// its join row `i`. It reads the shared arena and writes only its own rows, so the threads commute.
extern "C" __global__ void hnn_tree_gather(const uint32_t* halves, const TreeChart* charts,
                                           const TreeChart* joins, const uint32_t* nodes,
                                           uint32_t node_count, const uint32_t* dyadic,
                                           uint32_t dyadic_count, uint32_t* out_halves,
                                           TreeChart* out_charts, TreeChart* out_joins) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < node_count) {
        uint32_t node = nodes[i];
        out_halves[2 * i] = halves[2 * node];
        out_halves[2 * i + 1] = halves[2 * node + 1];
        out_charts[i] = charts[node];
    }
    if (i < dyadic_count) out_joins[i] = joins[dyadic[i]];
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
