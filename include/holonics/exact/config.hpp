#pragma once

#if defined(__CUDACC__)
#define HOLONICS_CALLABLE __host__ __device__
#else
#define HOLONICS_CALLABLE
#endif
