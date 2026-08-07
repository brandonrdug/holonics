function(holonics_require_file_hash path expected label)
  if(NOT EXISTS "${path}")
    message(FATAL_ERROR "Pinned ${label} is absent: ${path}")
  endif()
  file(SHA256 "${path}" actual)
  if(NOT actual STREQUAL expected)
    message(FATAL_ERROR
      "Pinned ${label} hash mismatch at ${path}: expected ${expected}, found ${actual}")
  endif()
endfunction()

function(holonics_verify_toolchain)
  if(NOT CMAKE_GENERATOR STREQUAL "Ninja")
    message(FATAL_ERROR "R0 requires the pinned Ninja generator")
  endif()
  if(NOT CMAKE_VERSION VERSION_EQUAL "4.3.2")
    message(FATAL_ERROR "R0 requires CMake 4.3.2; found ${CMAKE_VERSION}")
  endif()
  if(NOT CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL "16.1.1")
    message(FATAL_ERROR
      "R0 requires GCC 16.1.1; found ${CMAKE_CXX_COMPILER_VERSION}")
  endif()
  if(NOT CMAKE_CUDA_COMPILER_VERSION VERSION_EQUAL "13.2.78")
    message(FATAL_ERROR
      "R0 requires CUDA 13.2.78; found ${CMAKE_CUDA_COMPILER_VERSION}")
  endif()
  if(NOT CMAKE_CUDA_ARCHITECTURES STREQUAL "89")
    message(FATAL_ERROR
      "R0 requires CUDA architecture 89; found ${CMAKE_CUDA_ARCHITECTURES}")
  endif()

  file(REAL_PATH "${CMAKE_CXX_COMPILER}" actual_host_compiler)
  file(REAL_PATH "/usr/bin/g++" required_host_compiler)
  if(NOT actual_host_compiler STREQUAL required_host_compiler)
    message(FATAL_ERROR
      "R0 requires /usr/bin/g++; configured ${CMAKE_CXX_COMPILER}")
  endif()
  file(REAL_PATH "${CMAKE_CUDA_COMPILER}" actual_device_compiler)
  file(REAL_PATH "/opt/cuda/bin/nvcc" required_device_compiler)
  if(NOT actual_device_compiler STREQUAL required_device_compiler)
    message(FATAL_ERROR
      "R0 requires /opt/cuda/bin/nvcc; configured ${CMAKE_CUDA_COMPILER}")
  endif()
  file(REAL_PATH "${CMAKE_CUDA_HOST_COMPILER}" actual_device_host_compiler)
  if(NOT actual_device_host_compiler STREQUAL required_host_compiler)
    message(FATAL_ERROR
      "R0 requires /usr/bin/g++ as the CUDA host compiler; configured ${CMAKE_CUDA_HOST_COMPILER}")
  endif()
  file(REAL_PATH "${CMAKE_MAKE_PROGRAM}" actual_build_executor)
  file(REAL_PATH "/usr/bin/ninja" required_build_executor)
  if(NOT actual_build_executor STREQUAL required_build_executor)
    message(FATAL_ERROR
      "R0 requires /usr/bin/ninja; configured ${CMAKE_MAKE_PROGRAM}")
  endif()

  holonics_require_file_hash(
    "/usr/bin/g++"
    "4a12d04f0ea1294c3c11617032acdb83c042360010d0d314b283f968f56a615b"
    "host compiler")
  holonics_require_file_hash(
    "/opt/cuda/bin/nvcc"
    "02afd6a20bd29fae33bf278fa847a4e9711db25afec4a1bf648be81a3b210af0"
    "device compiler")
  holonics_require_file_hash(
    "/usr/lib/libstdc++.so.6"
    "9e4e018f08bf15a2eca390765d79f499738f8b899a563eddfa979756f5a8ff45"
    "host standard library")
  holonics_require_file_hash(
    "/usr/bin/cmake"
    "b40409e0ee2a7257d6399fba01f800e2aded3ad5d8db27f4efdd51c0ac01d7d3"
    "build configurator")
  holonics_require_file_hash(
    "/usr/bin/ninja"
    "f1c4d25e6f5719c2596c5996c37e838f9d0460b93f4d34baa1a61d90eaee14a2"
    "build executor")
  holonics_require_file_hash(
    "/usr/bin/objcopy"
    "616ec2a7cee37e710b555b36311144af2819f1402f9945f96808d1e7f2732cc3"
    "object normalizer")
  holonics_require_file_hash(
    "/opt/cuda/bin/nvdisasm"
    "69b72119d112b04b76af340cad187f3f1bced1f425e62cac4b664c4e3699d363"
    "device binary inspector")
endfunction()
