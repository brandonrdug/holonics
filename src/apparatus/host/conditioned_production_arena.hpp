#pragma once

#include <cstdint>

#include <holonics/event/conditioned_production.hpp>
#include <holonics/event/text_conditioning.hpp>

/// Host storage for one conditioned production current.
///
/// The arenas are the same ones the resident mount forms; only the pages differ,
/// and the residency crossing is graded by its own deed. What matters here is
/// that **excluding an occurrence re-forms the ecology over the smaller
/// population** rather than marking anything.
struct production_arena final {
  static constexpr std::uint32_t surface_extent = 16384;
  static constexpr std::uint32_t occurrence_extent = 64;
  static constexpr std::uint32_t caused_extent = 64;
  static constexpr std::uint32_t state_extent = 32768;
  static constexpr std::uint32_t transition_extent = 131072;
  static constexpr std::uint32_t incidence_extent = 16384;
  static constexpr std::uint32_t scratch_extent = 256;
  static constexpr std::uint32_t route_extent = 32;

  holonics::codec::text_arena text{};
  holonics::organ::suffix_arena suffix{};
  holonics::organ::incidence_arena incidence{};
  holonics::organ::training_ecology<route_extent> routes{2, 8};
  holonics::organ::suffix_symbol scratch[scratch_extent]{};

  std::uint32_t mounted_occurrences{};
  std::uint32_t mounted_states{};
  std::uint32_t conditioned_occurrences{};
  std::uint32_t conditioned_states{};

  unsigned char* surface_pages{};
  holonics::codec::text_occurrence* occurrence_pages{};
  std::uint32_t* caused_pages{};
  holonics::organ::suffix_state* state_pages{};
  holonics::organ::suffix_transition* transition_pages{};
  std::uint32_t* next_pages{};
  holonics::organ::source_occurrence* staged_pages{};
  std::uint32_t* staged_next_pages{};
  std::uint32_t* ordered_pages{};
  holonics::organ::source_span* span_pages{};
  std::uint32_t* head_pages{};
  std::uint32_t* child_pages{};
  std::uint32_t* sibling_pages{};
  std::uint32_t* stack_pages{};

  [[nodiscard]] bool open() {
    using namespace holonics;
    surface_pages = new unsigned char[surface_extent];
    occurrence_pages = new codec::text_occurrence[occurrence_extent];
    caused_pages = new std::uint32_t[caused_extent];
    state_pages = new organ::suffix_state[state_extent];
    transition_pages = new organ::suffix_transition[transition_extent];
    next_pages = new std::uint32_t[transition_extent];
    staged_pages = new organ::source_occurrence[incidence_extent];
    staged_next_pages = new std::uint32_t[incidence_extent];
    ordered_pages = new std::uint32_t[incidence_extent];
    span_pages = new organ::source_span[state_extent];
    head_pages = new std::uint32_t[state_extent];
    child_pages = new std::uint32_t[state_extent];
    sibling_pages = new std::uint32_t[state_extent];
    stack_pages = new std::uint32_t[state_extent];
    text.surface = {surface_pages, surface_extent};
    text.occurrences = {occurrence_pages, occurrence_extent};
    text.caused = {caused_pages, caused_extent};
    suffix.states = {state_pages, state_extent};
    suffix.transitions = {transition_pages, transition_extent};
    suffix.next = {next_pages, transition_extent};
    incidence.staged = {staged_pages, incidence_extent};
    incidence.staged_next = {staged_next_pages, incidence_extent};
    incidence.ordered_sources = {ordered_pages, incidence_extent};
    incidence.spans = {span_pages, state_extent};
    incidence.direct_head = {head_pages, state_extent};
    incidence.first_child = {child_pages, state_extent};
    incidence.next_sibling = {sibling_pages, state_extent};
    incidence.walk_stack = {stack_pages, state_extent};
    return true;
  }

  [[nodiscard]] bool admit(
      std::uint32_t container,
      const unsigned char* octets,
      std::uint32_t extent) {
    const auto state = holonics::codec::text_law::try_admit(text, container, 0,
        holonics::codec::text_role::document, holonics::codec::text_phase::received,
        octets, extent, nullptr, 0);
    return state == holonics::codec::text_admission::founded;
  }

  [[nodiscard]] bool emanate(
      std::uint32_t container,
      const unsigned char* octets,
      std::uint32_t extent,
      const std::uint32_t* caused_by,
      std::uint32_t caused_count) {
    const auto state = holonics::event::production_law::emanate(
        text, container, octets, extent, caused_by, caused_count);
    return state == holonics::codec::text_admission::founded;
  }

  /// Re-form the whole ecology over the current occurrence population. The
  /// suffix arena is refounded from the root, so an excluded occurrence leaves
  /// no state, no transition, and no incidence behind.
  [[nodiscard]] bool condition() {
    using namespace holonics;
    if (!organ::suffix_law::try_found_root(suffix) ||
        !organ::incidence_law::try_open(incidence)) {
      return false;
    }
    const auto returned = event::condition_text(text, suffix, incidence, 512);
    if (mounted_occurrences == 0) {
      mounted_occurrences = text.occurrences_used;
      mounted_states = suffix.states_used;
    }
    conditioned_occurrences = text.occurrences_used;
    conditioned_states = suffix.states_used;
    return returned.complete;
  }

  /// Remove the most recently admitted occurrence from the standing. Its surface
  /// leaves with it; nothing about it survives to be reached.
  void exclude_emanated() {
    if (text.occurrences_used == 0) {
      return;
    }
    const auto& held = text.occurrences.at(text.occurrences_used - 1U);
    text.surface_used = held.surface_start;
    text.caused_used = held.caused_start;
    text.occurrences_used = text.occurrences_used - 1U;
  }

  void observe(const holonics::organ::transduction_fiber& fiber) {
    const auto proposal = routes.propose(&fiber, 1);
    static_cast<void>(routes.commit(proposal));
  }

  [[nodiscard]] bool ablate(const holonics::organ::transduction_fiber& fiber) {
    return routes.ablate(fiber);
  }

  /// Read the reached material's leading token out of the standing itself. The
  /// span names which occurrence carries it; the surface supplies the octets.
  /// Nothing is copied from the query.
  [[nodiscard]] std::uint32_t retained_name(
      const holonics::event::reached_name& found,
      unsigned char* out,
      std::uint32_t capacity) const {
    const auto span = holonics::organ::incidence_law::span(incidence, found.state);
    if (span.length == 0) {
      return 0;
    }
    const std::uint32_t source = incidence.ordered_sources.at(span.start);
    if (source >= text.occurrences_used) {
      return 0;
    }
    const auto& held = text.occurrences.at(source);
    std::uint32_t written = 0;
    while (written < held.surface_extent && written < capacity) {
      const unsigned char octet = holonics::codec::text_law::octet(text, held, written);
      if (octet == ' ') {
        break;
      }
      out[written] = octet;
      written = written + 1U;
    }
    return written;
  }
};
