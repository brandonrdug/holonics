//! `overture_founding FILE LAYER WIDTH HEADS KV_HEADS HEAD_DIM THETA SITES FOIL_THETA`: the overture's step 2
//! (#146; record `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §6) over one released
//! `safetensors` file. Layer `LAYER`'s attention block (its input norm's gain and its query, key,
//! value and output projections, stored under the Llama names) is read exactly at the boundary and
//! founds level 0's participation of a one-level tower (`Tower::found_attention`). `SITES` declared
//! inputs of unit power (each coordinate `±1`, its sign a fixed bit mix of its site and place) are
//! then read by the founded level and by the source's block computed once at the boundary
//! (`AttentionBlock::reference`), and the check (`Tower::attention_check`) prints each head's and
//! the read's largest difference beside its largest component, both on `2^(−40)`, with the
//! founding's release receipts and each head's participation entropy at the last site. The
//! acceptance, fixed before the build: every head and the read within `2^(−8)` of their largest
//! component. The foil founds the same block on the rotary base `FOIL_THETA` and is checked against
//! the same reference: it fails where the frames carry the source's place. It runs no model and
//! trains nothing.
use holonics::hnn::overture::{AttentionBlock, AttentionShape, Released, Safetensors, REFERENCE_BITS};
use holonics::hnn::tower::participation::ParticipationDeclaration;
use holonics::hnn::tower::{ContactLaw, Tower, TowerDeclaration, FACE_BITS};

/// The sign of input coordinate `(site, place)`: the top bit of a fixed mix of the two.
fn negative(site: usize, place: usize) -> bool {
    let mut z = (site as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (place as u64).wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    (z ^ (z >> 31)) >> 63 == 1
}

fn receipt(name: &str, r: Released) {
    println!("OVERTURE_RELEASED part={name} coefficients={} remaindered={} zeroed={} remainder_sum_on_2^-128={}", r.coefficients, r.remaindered, r.zeroed, r.remainder);
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    let [_, path, layer, width, heads, kv_heads, head_dim, theta, sites, foil_theta] = &args[..] else {
        return Err("overture_founding FILE LAYER WIDTH HEADS KV_HEADS HEAD_DIM THETA SITES FOIL_THETA".into());
    };
    let (layer, sites): (usize, usize) = (layer.parse()?, sites.parse()?);
    let shape = AttentionShape { width: width.parse()?, heads: heads.parse()?, kv_heads: kv_heads.parse()?, head_dim: head_dim.parse()?, theta: theta.parse()? };
    let started = std::time::Instant::now();
    // The exterior boundary reads the file; nothing inside the machinery does (guard 7).
    #[allow(clippy::disallowed_methods)]
    let bytes = std::fs::read(path)?;
    let file = Safetensors::read(&bytes)?;
    let name = |part: &str| format!("model.layers.{layer}.{part}.weight");
    let names = [name("input_layernorm"), name("self_attn.q_proj"), name("self_attn.k_proj"), name("self_attn.v_proj"), name("self_attn.o_proj")];
    let block = AttentionBlock::read(&file, [&names[0], &names[1], &names[2], &names[3], &names[4]], shape)?;
    let read_ms = started.elapsed().as_millis();

    let AttentionShape { width: w, heads: h, head_dim: d, .. } = shape;
    let declaration = TowerDeclaration { alphabet: sites.max(2), width: w, modes: h * d, contacts: 1, levels: 1, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
    // The founding's own key stream for the material the block does not determine (the encoding,
    // which the check replaces, and the level's contacts).
    let keys: Vec<u8> = (0..(8 * h * d * w + sites.max(2) * w + 4096) as u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect();
    let mut tower = Tower::found(declaration, &keys)?;
    let beta_shift = d.isqrt().trailing_zeros();
    tower.join_participation(ParticipationDeclaration::new(vec![d; h], sites, beta_shift)?)?;
    let mut foil = tower.clone();
    let founding = tower.found_attention(0, &block)?;
    foil.found_attention(0, &AttentionBlock { shape: AttentionShape { theta: foil_theta.parse()?, ..shape }, ..block.clone() })?;
    let found_ms = started.elapsed().as_millis();
    receipt("charts", founding.charts);
    receipt("read", founding.read);

    let inputs: Vec<Vec<i32>> = (0..sites).map(|u| (0..w).map(|i| if negative(u, i) { -(1 << FACE_BITS) } else { 1 << FACE_BITS }).collect()).collect();
    let wide: Vec<Vec<i64>> = inputs.iter().map(|r| r.iter().map(|&v| v as i64).collect()).collect();
    let reference = block.reference(&wide, FACE_BITS)?;
    let reference_ms = started.elapsed().as_millis();
    let check = tower.attention_check(&inputs, &reference)?;
    let check_ms = started.elapsed().as_millis();
    let bits = |g: holonics::hnn::tower::overture::Gap| -> String {
        // The difference's place below the largest component, in whole bits (floor).
        if g.difference == 0 { "exact".into() } else { format!("{}", (128 - g.largest.leading_zeros()) as i32 - (128 - g.difference.leading_zeros()) as i32 - 1) }
    };
    let foiled = foil.attention_check(&inputs, &reference)?;
    for (name, c) in [("founded", &check), ("foil", &foiled)] {
        for (head, g) in c.heads.iter().enumerate() {
            println!("OVERTURE_CHECK founding={name} part=head{head} largest_difference={} largest_component={} grain_bits={REFERENCE_BITS} bits_below_at_least={} within_2^-8={} entropy_last_site_on_2^-20={}", g.difference, g.largest, bits(*g), g.within(8), c.entropies[head]);
        }
        let g = c.read;
        println!("OVERTURE_CHECK founding={name} part=read largest_difference={} largest_component={} grain_bits={REFERENCE_BITS} bits_below_at_least={} within_2^-8={}", g.difference, g.largest, bits(g), g.within(8));
    }
    println!("OVERTURE_FOUNDING layer={layer} sites={} beta_shift={beta_shift} accepted={} foil_theta={foil_theta} foil_accepted={} read_ms={read_ms} found_ms={found_ms} reference_ms={reference_ms} check_ms={check_ms}", check.sites, check.within(8), foiled.within(8));
    Ok(())
}
