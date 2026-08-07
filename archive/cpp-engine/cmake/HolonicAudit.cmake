cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

if(NOT DEFINED SOURCE_ROOT)
  message(FATAL_ERROR "HolonicAudit requires SOURCE_ROOT")
endif()
if(NOT DEFINED SCAN_ROOT)
  set(SCAN_ROOT "${SOURCE_ROOT}")
endif()

include("${SOURCE_ROOT}/cmake/HolonicArchitecture.cmake")

set(scan_patterns
    "${SCAN_ROOT}/src/include/holonics/*.h"
    "${SCAN_ROOT}/src/include/holonics/*.hpp"
    "${SCAN_ROOT}/src/include/holonics/*.cuh"
    "${SCAN_ROOT}/src/*.cc"
    "${SCAN_ROOT}/src/*.cpp"
    "${SCAN_ROOT}/src/*.cxx"
    "${SCAN_ROOT}/src/cuda/*.cuh"
    "${SCAN_ROOT}/src/cuda/*.cu"
    "${SCAN_ROOT}/src/apparatus/*.h"
    "${SCAN_ROOT}/src/apparatus/*.hpp"
    "${SCAN_ROOT}/src/apparatus/*.cuh"
    "${SCAN_ROOT}/src/apparatus/*.cc"
    "${SCAN_ROOT}/src/apparatus/*.cpp"
    "${SCAN_ROOT}/src/apparatus/*.cxx"
    "${SCAN_ROOT}/src/apparatus/*.cu")
file(GLOB_RECURSE production_files LIST_DIRECTORIES false ${scan_patterns})
list(SORT production_files)

if(production_files STREQUAL "" AND NOT ALLOW_EMPTY_SCAN)
  message(FATAL_ERROR "architecture audit found no production files under ${SCAN_ROOT}")
endif()

set(forbidden_carrier
    "(^|[^A-Za-z0-9_])(float|double|half|half2|__half|__half2|__nv_bfloat16|nv_bfloat16|__nv_bfloat162|tf32|__nv_fp8_e4m3|__nv_fp8_e5m2)([^A-Za-z0-9_]|$)")
set(forbidden_literal "(^|[^A-Za-z0-9_])[0-9]+\\.[0-9]+([fFlL]?)([^A-Za-z0-9_]|$)")
set(forbidden_float_intrinsic
    "(__f(add|sub|mul|div)|__d(add|sub|mul|div)|__float2|__double2|std::(sqrt|sin|cos|tan|exp|log|pow|fma))")
set(forbidden_container
    "std::(vector|map|unordered_map|set|unordered_set|queue|deque|list)[ \\t]*<")
set(forbidden_compatibility
    "(^|[^A-Za-z0-9_])(compat|compatibility|legacy|fallback|dual_schema|defaulting_decoder)(_|[^A-Za-z0-9]|$)")
set(forbidden_semantic_chart
    "(^|[^A-Za-z0-9_])(Lean|lean|Language|language|Repository|repository|CPU|cpu|Gpu|GPU|gpu|Filename|filename|Display|display)(_|[^A-Za-z0-9]|$)")
set(forbidden_identity_derivation
    "(^|[^A-Za-z0-9_])(address_identity|lane_identity|path_identity|digest_identity)([^A-Za-z0-9_]|$)")

foreach(path IN LISTS production_files)
  file(READ "${path}" contents)
  file(STRINGS "${path}" lines)
  list(LENGTH lines line_count)
  if(line_count GREATER HOLONICS_MAX_PRODUCTION_FILE_LINES)
    message(FATAL_ERROR
      "file-size law failed: ${path} has ${line_count} lines; budget is ${HOLONICS_MAX_PRODUCTION_FILE_LINES}")
  endif()

  if(contents MATCHES "${forbidden_carrier}" OR
     contents MATCHES "${forbidden_literal}" OR
     contents MATCHES "${forbidden_float_intrinsic}")
    message(FATAL_ERROR "no-float source audit failed: ${path}")
  endif()
  if(contents MATCHES "${forbidden_container}")
    message(FATAL_ERROR "public-container ownership audit failed: ${path}")
  endif()
  if(contents MATCHES "${forbidden_compatibility}")
    message(FATAL_ERROR "compatibility-route audit failed: ${path}")
  endif()
  if(contents MATCHES "${forbidden_identity_derivation}")
    message(FATAL_ERROR "derived-identity audit failed: ${path}")
  endif()

  file(RELATIVE_PATH relative "${SCAN_ROOT}" "${path}")
  set(owner "")
  # Most specific first. A header under src/include/holonics/<owner>/ names its
  # own owner; everything under src/cuda/ and src/apparatus/ is apparatus, which
  # is the only owner permitted to name a semantic chart.
  if(relative MATCHES "^src/include/holonics/([^/]+)/")
    set(owner "${CMAKE_MATCH_1}")
  elseif(relative MATCHES "^src/cuda/")
    set(owner apparatus)
  elseif(relative MATCHES "^src/apparatus/")
    set(owner apparatus)
  endif()

  if(owner STREQUAL "")
    message(FATAL_ERROR "owner audit could not classify ${relative}")
  endif()
  if(NOT owner IN_LIST HOLONICS_OWNERS)
    message(FATAL_ERROR "owner audit found undeclared owner '${owner}' in ${relative}")
  endif()

  if(NOT owner STREQUAL apparatus AND contents MATCHES "${forbidden_semantic_chart}")
    message(FATAL_ERROR "semantic-chart identifier audit failed: ${path}")
  endif()

  file(STRINGS "${path}" owner_includes REGEX "^#[ \\t]*include[ \\t]*<holonics/")
  foreach(include_line IN LISTS owner_includes)
    string(REGEX REPLACE ".*<holonics/([^/]+)/.*" "\\1" dependency "${include_line}")
    if(NOT dependency STREQUAL owner AND
       NOT dependency IN_LIST HOLONICS_OWNER_DEPENDENCIES_${owner})
      message(FATAL_ERROR
        "owner dependency audit failed: ${owner} cannot depend on ${dependency} in ${relative}")
    endif()
  endforeach()
endforeach()

foreach(owner IN LISTS HOLONICS_OWNERS)
  foreach(dependency IN LISTS HOLONICS_OWNER_DEPENDENCIES_${owner})
    list(FIND HOLONICS_OWNERS "${owner}" owner_index)
    list(FIND HOLONICS_OWNERS "${dependency}" dependency_index)
    if(dependency_index EQUAL -1)
      message(FATAL_ERROR "owner DAG names unknown dependency ${dependency}")
    endif()
    if(dependency_index GREATER_EQUAL owner_index)
      message(FATAL_ERROR "owner DAG is not acyclic at ${owner} -> ${dependency}")
    endif()
  endforeach()
endforeach()

if(DEFINED MANIFEST)
  foreach(required_artifact HOST_BINARY DEVICE_OBJECT DEVICE_PTX DEVICE_CUBIN)
    if(NOT DEFINED ${required_artifact})
      message(FATAL_ERROR "binary audit requires ${required_artifact}")
    endif()
  endforeach()
  if(NOT EXISTS "${MANIFEST}")
    message(FATAL_ERROR "build manifest audit failed: ${MANIFEST} is absent")
  endif()
  file(READ "${MANIFEST}" manifest_contents)
  set(all_artifacts "${HOST_BINARY}" "${DEVICE_OBJECT}" "${DEVICE_PTX}" "${DEVICE_CUBIN}")
  if(DEFINED EXTRA_ARTIFACTS AND NOT EXTRA_ARTIFACTS STREQUAL "")
    string(REPLACE "|" ";" extra_artifact_paths "${EXTRA_ARTIFACTS}")
    list(APPEND all_artifacts ${extra_artifact_paths})
  endif()
  foreach(required_manifest_field
      IN ITEMS
        "grade=established-bounded"
        "evidence=implemented-exact"
        "source_commit="
        "source_aperture_sha256="
        "device_profile=release 13.2, V13.2.78; C++20; sm_89"
        "declared_commands_begin"
        "compile_commands_begin"
        "build_commands_begin")
    string(FIND "${manifest_contents}" "${required_manifest_field}" field_position)
    if(field_position EQUAL -1)
      message(FATAL_ERROR "build manifest omits ${required_manifest_field}")
    endif()
  endforeach()
  foreach(artifact IN LISTS all_artifacts)
    if(NOT EXISTS "${artifact}")
      message(FATAL_ERROR "binary audit artifact is absent: ${artifact}")
    endif()
    file(SHA256 "${artifact}" digest)
    string(FIND "${manifest_contents}" "artifact_sha256=${digest}" digest_position)
    if(digest_position EQUAL -1)
      message(FATAL_ERROR "build manifest omits artifact hash for ${artifact}")
    endif()
  endforeach()

  set(all_device_ptx "${DEVICE_PTX}")
  if(DEFINED EXTRA_DEVICE_PTX AND NOT EXTRA_DEVICE_PTX STREQUAL "")
    string(REPLACE "|" ";" extra_device_ptx_paths "${EXTRA_DEVICE_PTX}")
    list(APPEND all_device_ptx ${extra_device_ptx_paths})
  endif()
  foreach(ptx IN LISTS all_device_ptx)
    file(READ "${ptx}" ptx_contents)
    if(ptx_contents MATCHES "\\.(f16|f16x2|f32|f64|bf16|bf16x2|tf32)([^A-Za-z0-9_]|$)")
      message(FATAL_ERROR "PTX no-float audit failed: ${ptx}")
    endif()
  endforeach()

  find_program(NVDISASM nvdisasm HINTS /opt/cuda/bin REQUIRED NO_CACHE)
  set(all_device_cubins "${DEVICE_CUBIN}")
  if(DEFINED EXTRA_DEVICE_CUBIN AND NOT EXTRA_DEVICE_CUBIN STREQUAL "")
    string(REPLACE "|" ";" extra_device_cubin_paths "${EXTRA_DEVICE_CUBIN}")
    list(APPEND all_device_cubins ${extra_device_cubin_paths})
  endif()
  foreach(cubin IN LISTS all_device_cubins)
    execute_process(
      COMMAND "${NVDISASM}" "${cubin}"
      RESULT_VARIABLE disassembly_result
      OUTPUT_VARIABLE sass_contents
      ERROR_VARIABLE disassembly_error)
    if(NOT disassembly_result EQUAL 0)
      message(FATAL_ERROR "device binary disassembly failed: ${disassembly_error}")
    endif()
    if(sass_contents MATCHES
       "(^|[ \\t])(FADD|FADD32I|FMUL|FMUL32I|FFMA|FSET|FSETP|FSWZADD|F2F|F2FP|F2I|F2IP|I2F|I2FP|DADD|DMUL|DFMA|DSET|DSETP|D2I|I2D|HADD2|HMUL2|HFMA2|HSET2|HSETP2|HMMA|DMMA|MUFU|RRO)([^A-Za-z0-9_]|$)" OR
       sass_contents MATCHES "\\.(F16|F16X2|F32|F64|BF16|BF16X2|TF32)([^A-Za-z0-9_]|$)")
      message(FATAL_ERROR "SASS no-float audit failed: ${cubin}")
    endif()
    if(DEFINED BUILD_ROOT)
      get_filename_component(cubin_name "${cubin}" NAME_WE)
      file(WRITE "${BUILD_ROOT}/generated/${cubin_name}.sass" "${sass_contents}")
    endif()
  endforeach()
endif()

message(STATUS "holonic-audit passed for ${SCAN_ROOT}")
