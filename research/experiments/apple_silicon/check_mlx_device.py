"""Exterior Apple apparatus check; this does not implement or certify native HNA.

Run with the environment described in docs/DEVELOPMENT.md. Integer reference
arithmetic is an observer, and all readback follows both dependent GPU kernels.
"""

import json

import mlx.core as mx


def main():
    if not mx.metal.is_available():
        raise RuntimeError("Metal GPU unavailable; no CPU fallback")
    # Each row is an unsigned 64-bit integer in two little-endian 32-bit limbs.
    # The separate overflow word prevents an overflowing sum looking exact.
    kernel = mx.fast.metal_kernel(
        name="holonics_apparatus_add_u64",
        input_names=["a", "b"],
        output_names=["sum", "overflow"],
        source="""
            uint i = thread_position_in_grid.x;
            uint low = a[2*i] + b[2*i];
            uint carry = uint(low < a[2*i]);
            uint high = a[2*i+1] + b[2*i+1];
            uint top = uint(high < a[2*i+1]);
            uint carried = high + carry;
            top |= uint(carried < high);
            sum[2*i] = low;
            sum[2*i+1] = carried;
            overflow[i] = top;
        """,
    )
    values = [0, 1, (1 << 32) - 1, 1 << 32, (1 << 63) - 1,
              1 << 63, (1 << 64) - 2, (1 << 64) - 1]
    pairs = [(a, b) for a in values for b in values]
    mask = (1 << 64) - 1

    def limbs(numbers):
        return mx.array([[n & 0xffffffff, n >> 32] for n in numbers], dtype=mx.uint32)

    a = limbs([a for a, _ in pairs])
    b = limbs([b for _, b in pairs])
    one = limbs([1] * len(pairs))
    first_stream, second_stream = mx.new_stream(mx.gpu), mx.new_stream(mx.gpu)

    def add(a, b, stream):
        return kernel(inputs=[a, b], grid=(len(pairs), 1, 1),
                      threadgroup=(1, 1, 1),
                      output_shapes=[(len(pairs), 2), (len(pairs),)],
                      output_dtypes=[mx.uint32, mx.uint32], stream=stream)

    # One thread per group is a declared smoke-test aperture, not a device tuning rule.
    first, first_overflow = add(a, b, first_stream)
    second, second_overflow = add(first, one, second_stream)
    mx.eval(first, first_overflow, second, second_overflow)
    returned = [x.tolist() for x in (first, first_overflow, second, second_overflow)]
    for i, (a_value, b_value) in enumerate(pairs):
        total = a_value + b_value
        next_total = (total & mask) + 1
        for rows, overflows, expected in (
            (returned[0], returned[1], total),
            (returned[2], returned[3], next_total),
        ):
            actual = rows[i][0] | (rows[i][1] << 32)
            if actual != expected & mask or overflows[i] != expected >> 64:
                raise AssertionError((i, actual, expected, overflows[i]))
    print(json.dumps({
        "scope": "exterior custom-Metal arithmetic and dependent-stream apparatus",
        "native_hna": False,
        "mlx_version": mx.__version__,
        "device": mx.device_info(),
        "input_pairs": len(pairs),
        "dependent_dispatches": 2,
        "checked_results": len(pairs) * 2,
        "integer_limb_and_overflow_parity": True,
        "readback": "after both dependent dispatches",
    }, indent=2))


if __name__ == "__main__":
    main()
