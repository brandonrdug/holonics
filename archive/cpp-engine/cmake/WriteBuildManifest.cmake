cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

foreach(required SOURCE_ROOT BUILD_ROOT OUTPUT HOST_BINARY DEVICE_OBJECT DEVICE_PTX DEVICE_CUBIN)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "WriteBuildManifest requires ${required}")
  endif()
endforeach()

execute_process(
  COMMAND git rev-parse HEAD
  WORKING_DIRECTORY "${SOURCE_ROOT}"
  OUTPUT_VARIABLE source_commit
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)

execute_process(
  COMMAND git status --porcelain --untracked-files=all
  WORKING_DIRECTORY "${SOURCE_ROOT}"
  OUTPUT_VARIABLE source_status
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)
if(source_status STREQUAL "")
  set(source_status "clean")
endif()

set(authority_files
    .gitignore
    AGENTS.md
    CONSTRUCTION_STATE.md
    canon/EPISTEMIC_GRADES.md
    canon/00_PURE_HOLONICS.md
    canon/01_CAUSAL_CALCULUS.md
    canon/03_CONDITIONING_AND_LEARNING.md
    canon/08_CORE_MATHEMATICAL_INSTRUMENTS.md
    blueprint/PURE_HOLONIC_ENGINE.md
    blueprint/CPP_GPU_FOUNDATION.md
    blueprint/COMPLETE_CPP_ENGINE_ROADMAP.md
    formal/elementary-holonics/ElementaryHolonics/Algorithm/Transition.lean
    formal/elementary-holonics/ElementaryHolonics/Algorithm/Rebase.lean
    formal/elementary-holonics/lakefile.toml
    formal/elementary-holonics/lake-manifest.json
    formal/elementary-holonics/lean-toolchain
    provenance/HARDWARE_RECEIPT.txt
    CMakeLists.txt)
file(GLOB_RECURSE implementation_files
     RELATIVE "${SOURCE_ROOT}"
     "${SOURCE_ROOT}/cmake/*.cmake"
     "${SOURCE_ROOT}/include/*.h"
     "${SOURCE_ROOT}/include/*.hpp"
     "${SOURCE_ROOT}/include/*.cuh"
     "${SOURCE_ROOT}/src/*.cc"
     "${SOURCE_ROOT}/src/*.cpp"
     "${SOURCE_ROOT}/src/*.cxx"
     "${SOURCE_ROOT}/cuda/*.cuh"
     "${SOURCE_ROOT}/cuda/*.cu"
     "${SOURCE_ROOT}/apparatus/*.h"
     "${SOURCE_ROOT}/apparatus/*.hpp"
     "${SOURCE_ROOT}/apparatus/*.cuh"
     "${SOURCE_ROOT}/apparatus/*.cc"
     "${SOURCE_ROOT}/apparatus/*.cpp"
     "${SOURCE_ROOT}/apparatus/*.cxx"
     "${SOURCE_ROOT}/apparatus/*.cu"
     "${SOURCE_ROOT}/tests/compile_contracts/*.cpp"
     "${SOURCE_ROOT}/tests/compile_contracts/*.cu"
     "${SOURCE_ROOT}/tests/conformance/*.cpp"
     "${SOURCE_ROOT}/tests/fixtures/*.hcodec"
     "${SOURCE_ROOT}/tests/model/*.hpp"
     "${SOURCE_ROOT}/tests/model/*.cpp"
     "${SOURCE_ROOT}/tests/audit_fixtures/*.hpp")
list(APPEND authority_files ${implementation_files})
list(REMOVE_DUPLICATES authority_files)
list(SORT authority_files)

set(source_entries "")
foreach(relative IN LISTS authority_files)
  set(path "${SOURCE_ROOT}/${relative}")
  if(NOT EXISTS "${path}")
    message(FATAL_ERROR "Manifest input is absent: ${path}")
  endif()
  file(SHA256 "${path}" digest)
  string(APPEND source_entries "source_sha256=${digest}  ${relative}\n")
endforeach()
string(SHA256 source_aperture_sha256 "${source_entries}")

set(tool_paths
    /usr/bin/g++
    /opt/cuda/bin/nvcc
    /usr/lib/libstdc++.so.6
    /usr/bin/cmake
    /usr/bin/ninja
    /usr/bin/objcopy
    /opt/cuda/bin/nvdisasm)
set(tool_entries "")
foreach(path IN LISTS tool_paths)
  file(SHA256 "${path}" digest)
  string(APPEND tool_entries "tool_sha256=${digest}  ${path}\n")
endforeach()

set(artifact_paths
    "${HOST_BINARY}"
    "${DEVICE_OBJECT}"
    "${DEVICE_PTX}"
    "${DEVICE_CUBIN}")
if(DEFINED EXTRA_ARTIFACTS AND NOT EXTRA_ARTIFACTS STREQUAL "")
  string(REPLACE "|" ";" extra_artifact_paths "${EXTRA_ARTIFACTS}")
  list(APPEND artifact_paths ${extra_artifact_paths})
endif()
set(artifact_entries "")
foreach(path IN LISTS artifact_paths)
  if(NOT EXISTS "${path}")
    message(FATAL_ERROR "Build artifact is absent: ${path}")
  endif()
  file(SHA256 "${path}" digest)
  file(RELATIVE_PATH relative "${BUILD_ROOT}" "${path}")
  string(APPEND artifact_entries "artifact_sha256=${digest}  ${relative}\n")
endforeach()

set(compile_commands_path "${BUILD_ROOT}/compile_commands.json")
if(NOT EXISTS "${compile_commands_path}")
  message(FATAL_ERROR "compile_commands.json is absent")
endif()
file(READ "${compile_commands_path}" compile_commands)
string(REPLACE "${BUILD_ROOT}" "<BUILD>" compile_commands "${compile_commands}")
string(REPLACE "${SOURCE_ROOT}" "<SOURCE>" compile_commands "${compile_commands}")
string(REPLACE "/opt/cuda/bin/nvcc" "<CUDA_COMPILER>" compile_commands "${compile_commands}")
string(REPLACE "/usr/bin/g++" "<HOST_COMPILER>" compile_commands "${compile_commands}")

set(declared_commands_path "${BUILD_ROOT}/generated/declared_commands.txt")
file(READ "${declared_commands_path}" declared_commands)
string(REPLACE "${BUILD_ROOT}" "<BUILD>" declared_commands "${declared_commands}")
string(REPLACE "${SOURCE_ROOT}" "<SOURCE>" declared_commands "${declared_commands}")
string(REPLACE "/opt/cuda/bin/nvcc" "<CUDA_COMPILER>" declared_commands "${declared_commands}")

execute_process(
  COMMAND /usr/bin/ninja -t commands
  WORKING_DIRECTORY "${BUILD_ROOT}"
  OUTPUT_VARIABLE build_commands
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)
string(REPLACE "${BUILD_ROOT}" "<BUILD>" build_commands "${build_commands}")
string(REPLACE "${SOURCE_ROOT}" "<SOURCE>" build_commands "${build_commands}")
string(REPLACE "/opt/cuda/bin/nvcc" "<CUDA_COMPILER>" build_commands "${build_commands}")
string(REPLACE "/usr/bin/g++" "<HOST_COMPILER>" build_commands "${build_commands}")

execute_process(
  COMMAND /usr/bin/g++ --version
  OUTPUT_VARIABLE host_version
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)
string(REGEX REPLACE "\n.*" "" host_version "${host_version}")
execute_process(
  COMMAND /opt/cuda/bin/nvcc --version
  OUTPUT_VARIABLE device_version
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)
string(REGEX MATCH "release [0-9.]+, V[0-9.]+" device_version "${device_version}")

get_filename_component(output_directory "${OUTPUT}" DIRECTORY)
file(MAKE_DIRECTORY "${output_directory}")
file(WRITE "${OUTPUT}"
"grade=established-bounded\n"
"evidence=implemented-exact\n"
"construction_phase=${CONSTRUCTION_PHASE}\n"
"aperture=current admitted source and generated host/device artifacts\n"
"source_commit=${source_commit}\n"
"source_status_begin\n${source_status}\nsource_status_end\n"
"source_aperture_sha256=${source_aperture_sha256}\n"
"generator=Ninja 1.13.2\n"
"configurator=CMake 4.3.2\n"
"host_profile=${host_version}; C++23\n"
"device_profile=${device_version}; C++20; sm_89\n"
"${tool_entries}"
"${source_entries}"
"${artifact_entries}"
"declared_commands_begin\n${declared_commands}declared_commands_end\n"
"compile_commands_begin\n${compile_commands}\ncompile_commands_end\n")
file(APPEND "${OUTPUT}" "build_commands_begin\n${build_commands}\nbuild_commands_end\n")
