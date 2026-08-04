#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/structure/occurrence.hpp>

namespace holonics::organ {

inline constexpr std::size_t mathematical_term_capacity = 24;
inline constexpr std::size_t mathematical_declaration_capacity = 10;
inline constexpr std::size_t mathematical_dependency_capacity = 24;
inline constexpr std::size_t mathematical_neighborhood_capacity = 10;

enum class term_constructor : std::uint8_t {
  sort,
  constant,
  bound_variable,
  application,
  implication,
  lambda,
  proof
};

enum class dependency_role : std::uint8_t {
  type_incidence,
  definition_incidence,
  lemma_transport,
  proof_support
};

enum class mathematical_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  missing_incidence,
  type_mismatch,
  unsolved_goal,
  capacity_refused
};

struct mathematical_term final {
  exact::word identity{};
  exact::word type_identity{};
  exact::word provenance{};
  term_constructor constructor{term_constructor::constant};
  std::uint16_t left_slot{};
  std::uint16_t right_slot{};
  bool has_left{};
  bool has_right{};
};

struct mathematical_declaration final {
  exact::word identity{};
  exact::word provenance{};
  std::uint16_t type_slot{};
  std::uint16_t value_slot{};
  std::uint16_t dependency_begin{};
  std::uint16_t dependency_count{};
  bool has_value{};
  bool inherited_checked_example{};
};

struct mathematical_dependency final {
  std::uint16_t target_slot{};
  dependency_role role{dependency_role::type_incidence};
  exact::word port{};
  exact::word lineage{};
};

struct mathematical_foundation final {
  exact::word environment{};
  exact::word kernel_declarations{};
  exact::word provenance{};
  exact::word source_material_testimony{};
  std::uint16_t term_count{};
  std::uint16_t declaration_count{};
  std::uint16_t dependency_count{};
  mathematical_term terms[mathematical_term_capacity]{};
  mathematical_declaration declarations[mathematical_declaration_capacity]{};
  mathematical_dependency dependencies[mathematical_dependency_capacity]{};
};

struct mathematical_goal final {
  exact::word identity{};
  exact::word receiver{};
  std::uint16_t anchor_slot{};
  exact::word target_type{};
  exact::word hypothesis_type{};
  exact::word metavariable{};
  bool request_generated_closure{};
};

}  // namespace holonics::organ
