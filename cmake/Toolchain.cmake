set(CMAKE_CXX_COMPILER "/usr/bin/g++" CACHE FILEPATH "Pinned host compiler")
set(CMAKE_CUDA_COMPILER "/opt/cuda/bin/nvcc" CACHE FILEPATH "Pinned device compiler")
set(CMAKE_CUDA_HOST_COMPILER "/usr/bin/g++" CACHE FILEPATH "Pinned CUDA host compiler")

set(CMAKE_CXX_STANDARD 23 CACHE STRING "Pinned host language level")
set(CMAKE_CXX_STANDARD_REQUIRED ON CACHE BOOL "Require the pinned host language level")
set(CMAKE_CXX_EXTENSIONS OFF CACHE BOOL "Disable host language extensions")

set(CMAKE_CUDA_STANDARD 20 CACHE STRING "Pinned device language level")
set(CMAKE_CUDA_STANDARD_REQUIRED ON CACHE BOOL "Require the pinned device language level")
set(CMAKE_CUDA_EXTENSIONS OFF CACHE BOOL "Disable device language extensions")
set(CMAKE_CUDA_ARCHITECTURES 89 CACHE STRING "Pinned device architecture")
set(CMAKE_CUDA_FLAGS_INIT "--std=c++20")
