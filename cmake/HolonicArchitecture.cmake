set(HOLONICS_OWNERS
    exact
    structure
    body
    receiver
    organ
    codec
    event
    current
    apparatus)

set(HOLONICS_OWNER_DEPENDENCIES_exact "")
set(HOLONICS_OWNER_DEPENDENCIES_structure exact)
set(HOLONICS_OWNER_DEPENDENCIES_body exact structure)
set(HOLONICS_OWNER_DEPENDENCIES_receiver exact structure)
set(HOLONICS_OWNER_DEPENDENCIES_organ exact structure)
set(HOLONICS_OWNER_DEPENDENCIES_codec exact structure)
set(HOLONICS_OWNER_DEPENDENCIES_event exact structure body receiver organ codec)
set(HOLONICS_OWNER_DEPENDENCIES_current exact structure body event)
set(HOLONICS_OWNER_DEPENDENCIES_apparatus
    exact structure body event current receiver organ codec)

set(HOLONICS_MAX_PRODUCTION_FILE_LINES 240)

function(holonics_define_owner_targets)
  foreach(owner IN LISTS HOLONICS_OWNERS)
    add_library(holonics_${owner} INTERFACE)
    add_library(holonics::${owner} ALIAS holonics_${owner})
    target_include_directories(
      holonics_${owner}
      INTERFACE
        $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>)

    foreach(dependency IN LISTS HOLONICS_OWNER_DEPENDENCIES_${owner})
      target_link_libraries(holonics_${owner} INTERFACE holonics::${dependency})
    endforeach()
  endforeach()
endfunction()
