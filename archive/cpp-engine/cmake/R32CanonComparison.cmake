cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS SEAL DOSSIER SOURCE C0 C1 C3 C4 OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R32 canon comparison requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS SEAL DOSSIER SOURCE C0 C1 C3 C4)
  if(NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R32 canon comparison requires ${required}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_before)
file(READ "${DOSSIER}" returned)
file(READ "${SOURCE}" formal)
foreach(canon IN ITEMS C0 C1 C3 C4)
  file(READ "${${canon}}" ${canon}_text)
endforeach()
foreach(required_return IN ITEMS "An occurrence is not its payload" "Composition is determined"
    "Observation is a partition" "Local rechart transport" "Reusable changed conduct")
  string(FIND "${returned}" "${required_return}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R32 dossier omits ${required_return}")
  endif()
endforeach()
foreach(pair IN ITEMS "C0_text;occurrence" "C1_text;receiver" "C3_text;detached"
    "C4_text;holonomy")
  list(GET pair 0 text_name)
  list(GET pair 1 needle)
  string(FIND "${${text_name}}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "canon comparison cannot locate ${needle}")
  endif()
endforeach()
string(FIND "${formal}" "generated_elementary_causal_calculus" formal_position)
if(formal_position EQUAL -1)
  message(FATAL_ERROR "R32 formal return missing")
endif()
file(SHA256 "${SEAL}" seal_after)
if(NOT seal_before STREQUAL seal_after)
  message(FATAL_ERROR "R32 seal changed during canon comparison")
endif()
file(WRITE "${OUTPUT}" "# R32 post-seal canon comparison\n\n"
  "**Truth status:** `interpretation`.\n\n"
  "The comparison opened the four declared canon files only after the computational return, "
  "formal source, dossier, source audit, deterministic replay, and native rests were sealed. "
  "The seal remained byte-identical (`${seal_before}`).\n\n"
  "| Returned exact mechanism | Exterior canon relation | Comparison |\n"
  "|---|---|---|\n"
  "| Five-coordinate situated key; equal payload countermodel | occurrence is situated and lineaged | agreement in the finite aperture |\n"
  "| Complete-successor signatures | seriality, interchange, interaction, obstruction, co-presence | agreement; returned signature grammar is bounded |\n"
  "| Finite fiber factorization and reopening | receiver-indexed fibers and lawful condensation | agreement in a six-source finite receiver family |\n"
  "| Unequal path products and closed-word return | local transport, holonomy and curvature obstruction | agreement for rank-two integral charts |\n"
  "| Returned/detached conduct predicate with lookup controls | conditioning and learning boundary | agreement for the eight declared observations |\n\n"
  "The derived presentation is computational and finite. This comparison does not establish a "
  "unique ontology, arbitrary categorical semantics, or unrestricted self-derivation.\n")
