cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS OUTPUT COMPARISON SOURCE_AUDIT DEED REST SOURCE OLEAN
    FOIL_SOURCE FOIL_STDOUT ATLAS DOSSIER)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R30 seal comparison requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS SOURCE_AUDIT DEED REST SOURCE OLEAN FOIL_SOURCE
    FOIL_STDOUT ATLAS DOSSIER)
  if(NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R30 seal comparison requires existing ${required}")
  endif()
endforeach()
set(sealed_paths "${DEED}" "${REST}" "${SOURCE}" "${OLEAN}" "${FOIL_SOURCE}"
  "${FOIL_STDOUT}" "${ATLAS}" "${DOSSIER}" "${SOURCE_AUDIT}")
set(before "")
foreach(path IN LISTS sealed_paths)
  file(SHA256 "${path}" digest)
  get_filename_component(name "${path}" NAME)
  string(APPEND before "${digest}  ${name}\n")
  list(APPEND before_digests "${digest}")
endforeach()
file(WRITE "${COMPARISON}" [=[# R30 exterior post-seal mechanism comparison

## Matching/Jacobian mechanism

**Truth status:** `interpretation`.

The sealed bounded return and OpenAI *Ten Advances in Mathematics and Theoretical Computer
Science*, Chapter 5 section 9, share an explicit mechanism: marked-subset coefficient rows,
forbidden-coordinate injection sums, evaluation matrices, a row-scaled Kronecker Jacobian, and
nonzero Vandermonde factors. This is a structure-preserving comparison inside R30's fixed
`n=13`, 49-coefficient aperture. It is not the chapter's asymptotic permanent lower bound and
does not promote bounded computation into that theorem.

## Saturated-matrix/cover mechanism

**Truth status:** `interpretation`.

The sealed three-row binary matrix, all 70 four-column saturation witnesses, exceptional words,
and 64 two-sided coordinate witnesses instantiate the finite mechanism used in Chapter 9 section
2. The comparison does not claim the chapter's recursive Ramsey construction or asymptotics.

## Prior-work boundary

**Truth status:** `historical`.

R21's released Chapters 2 and 7 mechanisms, R22's unit-distance/CM return, and the laboratory's
Erdos-183 corollary remain regression evidence only; none is counted as an R30 return.

Official benchmark: https://cdn.openai.com/pdf/ten-proofs-oai.pdf
]=])
set(index 0)
foreach(path IN LISTS sealed_paths)
  file(SHA256 "${path}" after_digest)
  list(GET before_digests ${index} before_digest)
  if(NOT after_digest STREQUAL before_digest)
    message(FATAL_ERROR "R30 post-seal comparison changed ${path}")
  endif()
  math(EXPR index "${index} + 1")
endforeach()
file(SHA256 "${COMPARISON}" comparison_digest)
file(WRITE "${OUTPUT}"
  "truth_status=established-bounded\n"
  "evidence=implemented-exact,computational-witness\n"
  "sealed_before_comparison=1\n"
  "sealed_after_comparison=1\n"
  "comparison_truth_status=interpretation\n"
  "comparison_sha256=${comparison_digest}\n"
  "sealed_artifacts_begin\n${before}sealed_artifacts_end\n")
