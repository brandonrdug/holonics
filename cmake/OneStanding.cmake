add_executable(one_standing_deed apparatus/host/one_standing_deed.cpp)
target_include_directories(
  one_standing_deed PRIVATE "${PROJECT_SOURCE_DIR}/apparatus/host")
target_link_libraries(
  one_standing_deed PRIVATE holonics::apparatus holonics_contract_options)

set(ONE_STANDING_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/ONE_STANDING_DEED.txt")
add_test(NAME standing.one_standing_deed COMMAND one_standing_deed "${ONE_STANDING_ARTIFACT}")
