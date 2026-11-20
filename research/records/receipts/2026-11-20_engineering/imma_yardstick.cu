// A yardstick of the card's eight-bit integer tensor products (mma.sync m16n8k32 s8.s8.s32), and of the same products on the CUDA cores
// (dp4a), each thread's fragments held in registers so the loop is the products alone. Prints products a second.
#include <cstdio>
#include <cstdint>
__global__ void imma_loop(int iters, int *out) {
    uint32_t a0 = threadIdx.x * 0x01010101u, a1 = a0 ^ 0x5a5a5a5au, a2 = a0 + 7, a3 = a0 * 3;
    uint32_t b0 = blockIdx.x * 0x01030507u, b1 = b0 ^ 0x33333333u;
    int c0 = 0, c1 = 0, c2 = 0, c3 = 0, d0 = 0, d1 = 0, d2 = 0, d3 = 0;
    for (int i = 0; i < iters; i++) {
        asm volatile("mma.sync.aligned.m16n8k32.row.col.s32.s8.s8.s32 {%0,%1,%2,%3}, {%4,%5,%6,%7}, {%8,%9}, {%0,%1,%2,%3};\n"
                     : "+r"(c0), "+r"(c1), "+r"(c2), "+r"(c3) : "r"(a0), "r"(a1), "r"(a2), "r"(a3), "r"(b0), "r"(b1));
        asm volatile("mma.sync.aligned.m16n8k32.row.col.s32.s8.s8.s32 {%0,%1,%2,%3}, {%4,%5,%6,%7}, {%8,%9}, {%0,%1,%2,%3};\n"
                     : "+r"(d0), "+r"(d1), "+r"(d2), "+r"(d3) : "r"(a1), "r"(a0), "r"(a3), "r"(a2), "r"(b1), "r"(b0));
    }
    out[blockIdx.x * blockDim.x + threadIdx.x] = c0 + c1 + c2 + c3 + d0 + d1 + d2 + d3;
}
__global__ void dp4a_loop(int iters, int *out) {
    int a = threadIdx.x * 0x01010101, b = blockIdx.x * 0x01030507;
    int c0 = 0, c1 = 0, c2 = 0, c3 = 0;
    for (int i = 0; i < iters; i++) {
        c0 = __dp4a(a, b, c0); c1 = __dp4a(a ^ c0, b, c1); c2 = __dp4a(a, b ^ c1, c2); c3 = __dp4a(a + c2, b, c3);
    }
    out[blockIdx.x * blockDim.x + threadIdx.x] = c0 + c1 + c2 + c3;
}
int main() {
    int *out; cudaMalloc(&out, 80 * 64 * 256 * sizeof(int));
    cudaEvent_t s, e; cudaEventCreate(&s); cudaEventCreate(&e);
    const int blocks = 80 * 8, threads = 256, iters = 100000;
    imma_loop<<<blocks, threads>>>(10, out); cudaDeviceSynchronize();
    cudaEventRecord(s); imma_loop<<<blocks, threads>>>(iters, out); cudaEventRecord(e); cudaEventSynchronize(e);
    float ms; cudaEventElapsedTime(&ms, s, e);
    // each warp's mma is 16x8x32 = 4096 products; two a loop.
    double warps = blocks * threads / 32.0, prods = warps * iters * 2 * 4096.0;
    printf("IMMA_S8 products_a_second=%.4g ms=%.1f\n", prods / (ms / 1e3), ms);
    dp4a_loop<<<blocks, threads>>>(10, out); cudaDeviceSynchronize();
    cudaEventRecord(s); dp4a_loop<<<blocks, threads>>>(iters, out); cudaEventRecord(e); cudaEventSynchronize(e);
    cudaEventElapsedTime(&ms, s, e);
    prods = (double)blocks * threads * iters * 4 * 4.0;
    printf("DP4A_S8 products_a_second=%.4g ms=%.1f\n", prods / (ms / 1e3), ms);
    printf("ERR %s\n", cudaGetErrorString(cudaGetLastError()));
    return 0;
}
