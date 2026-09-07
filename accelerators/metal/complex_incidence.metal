// Exact signed-word complex incidence contraction.  One Metal thread owns the complete
// output section; this preserves the CUDA kernel's ordered integer accumulation while the
// mount boundary retains allocation and command-buffer ownership.
#include <metal_stdlib>
using namespace metal;

kernel void conduct_complex_incidence(
    device const long *incidence [[buffer(0)]],
    device const long *coefficient_real [[buffer(1)]],
    device const long *coefficient_imaginary [[buffer(2)]],
    device long *section_real [[buffer(3)]],
    device long *section_imaginary [[buffer(4)]],
    constant uint &branch_count [[buffer(5)]],
    constant uint &node_count [[buffer(6)]],
    constant uint &front_count [[buffer(7)]],
    uint tid [[thread_position_in_grid]]) {
    if (tid != 0) return;
    const ulong extent = (ulong)front_count * (ulong)branch_count;
    for (ulong at = 0; at < extent; ++at) {
        const uint front = (uint)(at / (ulong)branch_count);
        const uint branch = (uint)(at % (ulong)branch_count);
        const ulong incidence_at = (ulong)branch * (ulong)node_count;
        const ulong coefficient_at = (ulong)front * (ulong)node_count;
        long real = 0;
        long imaginary = 0;
        for (uint node = 0; node < node_count; ++node) {
            real += incidence[incidence_at + (ulong)node]
                * coefficient_real[coefficient_at + (ulong)node];
            imaginary += incidence[incidence_at + (ulong)node]
                * coefficient_imaginary[coefficient_at + (ulong)node];
        }
        section_real[at] = real;
        section_imaginary[at] = imaginary;
    }
}
