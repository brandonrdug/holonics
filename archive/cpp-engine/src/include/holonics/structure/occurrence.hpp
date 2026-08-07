#pragma once

#include <concepts>

#include <holonics/structure/port.hpp>

namespace holonics::structure {

struct occurrence_identity_owner final {};
struct event_identity_owner final {};
struct source_identity_owner final {};
struct event_cut_identity_owner final {};
struct lineage_identity_owner final {};
struct region_identity_owner final {};

struct situated_occurrence_marker final {};

template<class Occurrence>
concept situated_occurrence = requires {
  typename Occurrence::holonics_situated_occurrence;
  typename Occurrence::identity_type;
  typename Occurrence::source_type;
  typename Occurrence::event_cut_type;
  typename Occurrence::port_type;
  typename Occurrence::payload_type;
  typename Occurrence::lineage_type;
} && std::same_as<
    typename Occurrence::holonics_situated_occurrence,
    situated_occurrence_marker>
  && typed_port<typename Occurrence::port_type>;

template<class Payload, typed_port Port>
struct occurrence final {
  using holonics_situated_occurrence = situated_occurrence_marker;
  using identity_type = identity<occurrence_identity_owner>;
  using source_type = identity<source_identity_owner>;
  using event_cut_type = identity<event_cut_identity_owner>;
  using port_type = Port;
  using payload_type = Payload;
  using lineage_type = identity<lineage_identity_owner>;
};

}  // namespace holonics::structure
