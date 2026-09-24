//! D3 — the generated section triple at the CUDA execution seam.
//!
//! [definition] A section operator is performed on device as three arms: a **gather** by declared
//! region incidence into a local tile, a **local application** of a material operator inside each
//! tile, and a **transposed scatter** back into the global field.  This module owns the wire the
//! two sides share: the entry symbols, their parameter-word counts, the name of the dynamic shared
//! tile, and — the substantive part — **the exact arithmetic itself**.
//!
//! [definition] The device arithmetic is the finite field `Z/(2^61 - 1)`, a Mersenne prime.  It is
//! chosen so that the whole ring operation is exact with no division: a 128-bit product folds back
//! by shift-and-mask.  Addition in it is associative and commutative, which is precisely the
//! property an accumulating scatter needs and which floating-point addition does not have; the
//! Lean owner `Soma.Holonics.Foundation.SectionLayout` states every law over a `CommSemiring`, and
//! `ZMod (2^61 - 1)` is one.
//!
//! [definition] **One mouth.**  [`add`], [`mul`] and [`reduce`] are compiled for `nvptx64` by
//! `accelerators/cuda-kernel` and for the host by `crates/holonics-cuda`'s exact reference, so the
//! bit-for-bit agreement the device tests assert is a property of one piece of code rather than of
//! two transcriptions.

/// The gather arm's entry symbol.
pub const GATHER_ENTRY_SYMBOL: &str = "section_gather";
/// The local-application arm's entry symbol.
pub const APPLY_ENTRY_SYMBOL: &str = "section_apply";
/// The scatter arm's entry symbol under an **injective** incidence: plain stores.
pub const SCATTER_STORE_ENTRY_SYMBOL: &str = "section_scatter_store";
/// The scatter arm's entry symbol under a declared exact accumulation, launched colour by colour.
pub const SCATTER_ADD_ENTRY_SYMBOL: &str = "section_scatter_add";

/// The name of the dynamic shared tile the local-application entry addresses.  The entry declares
/// it `.extern .shared`; the octet extent is supplied per launch by `cuLaunchKernel`'s
/// `sharedMemBytes`, which the launch law derives from the declared tile width.
pub const SHARED_TILE_SYMBOL: &str = "section_tile";

/// The exact modulus: the Mersenne prime `2^61 - 1`.
pub const MODULUS: u64 = (1u64 << 61) - 1;

/// One entry of the generated section triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Entry {
    /// `section_gather`.
    Gather,
    /// `section_apply`.
    Apply,
    /// `section_scatter_store`.
    ScatterStore,
    /// `section_scatter_add`.
    ScatterAdd,
}

impl Entry {
    /// Every entry of the triple, in launch order.
    pub const ALL: [Entry; 4] = [
        Entry::Gather,
        Entry::Apply,
        Entry::ScatterStore,
        Entry::ScatterAdd,
    ];

    /// The entry's PTX symbol.
    pub const fn symbol(self) -> &'static str {
        match self {
            Entry::Gather => GATHER_ENTRY_SYMBOL,
            Entry::Apply => APPLY_ENTRY_SYMBOL,
            Entry::ScatterStore => SCATTER_STORE_ENTRY_SYMBOL,
            Entry::ScatterAdd => SCATTER_ADD_ENTRY_SYMBOL,
        }
    }

    /// How many `.param` words the lowered entry carries: one per pointer, one per extent, one per
    /// declared scalar.  Asserted against the committed PTX artifact by `mount`'s own test, so a
    /// signature change on either side is a failing test rather than a silent parameter-block
    /// mismatch.
    pub const fn cuda_parameter_words(self) -> usize {
        match self {
            // (source, len) (index, len) (local, len) + slots
            Entry::Gather => 7,
            // (local, len) (offsets, len) (coeff, len) + regions + tile_width
            Entry::Apply => 8,
            // (local, len) (index, len) (target, len) + slots
            Entry::ScatterStore => 7,
            // (local, len) (index, len) (offsets, len) (colour_regions, len) (target, len) + count
            Entry::ScatterAdd => 11,
        }
    }
}

/// Fold **any** 128-bit word back into `[0, MODULUS)`.
///
/// `2^61 ≡ 1 (mod 2^61 - 1)`, so `x ≡ (x & (2^61 - 1)) + (x >> 61)` for every `x`, and the fold may
/// be iterated.  Both folds are performed **in `u128`**, which is what makes the total domain a
/// theorem rather than a precondition:
///
/// * `product < 2^128`, so `product >> 61 < 2^67` — the shifted half does **not** fit `u64` in
///   general, and narrowing it before the fold is exactly the truncation this reduction must not
///   commit.  `product & MODULUS < 2^61`, so
///   `once = (product & MODULUS) + (product >> 61) < 2^61 + 2^67 < 2^68`.
/// * `once < 2^68`, so `once >> 61 < 2^7` and `once & MODULUS < 2^61`, so
///   `twice = (once & MODULUS) + (once >> 61) < 2^61 + 2^7`.  That is below `2^64`, so the narrowing
///   to `u64` here is exact, and it is below `2 · MODULUS`, so one conditional subtraction lands in
///   `[0, MODULUS)`.
///
/// No division, no wrapping, and no operand precondition: the widest intermediate is `2^68`, held
/// in the 128-bit word the product already occupies.
#[inline(always)]
pub const fn reduce(product: u128) -> u64 {
    let once = (product & (MODULUS as u128)) + (product >> 61);
    let twice = ((once & (MODULUS as u128)) + (once >> 61)) as u64;
    if twice >= MODULUS { twice - MODULUS } else { twice }
}

/// The canonical residue of an arbitrary 64-bit word.
#[inline(always)]
pub const fn canonical(value: u64) -> u64 {
    reduce(value as u128)
}

/// Exact addition in `Z/(2^61 - 1)`, **total over every pair of `u64` words**.  Associative and
/// commutative, which is what makes the accumulating scatter order-independent.
///
/// The sum is formed in `u128` — `a + b < 2^65` — so no `u64` overflow is reachable and no
/// canonicality precondition is carried.  `reduce` then lands it in `[0, MODULUS)`.
#[inline(always)]
pub const fn add(a: u64, b: u64) -> u64 {
    reduce((a as u128) + (b as u128))
}

/// Exact multiplication in `Z/(2^61 - 1)`, **total over every pair of `u64` words**: the product of
/// two arbitrary 64-bit words is below `2^128`, which is [`reduce`]'s proved domain.
#[inline(always)]
pub const fn mul(a: u64, b: u64) -> u64 {
    reduce((a as u128) * (b as u128))
}

/// Whether a word is already the canonical residue of its own class, i.e. lies in `[0, MODULUS)`.
///
/// The arithmetic above no longer needs this — it is total — but the staging boundary does: a
/// declared coefficient outside `[0, MODULUS)` is a malformed declaration, and the host refuses it
/// there rather than reducing it silently.
#[inline(always)]
pub const fn is_canonical(value: u64) -> bool {
    value < MODULUS
}
