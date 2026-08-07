#pragma once

#include <cstddef>

#include <holonics/receiver/geometry_receipt.hpp>

namespace holonics::receiver {

[[nodiscard]] HOLONICS_CALLABLE constexpr sameness_receipt distinguish_sameness(
    const sameness_program& program) noexcept {
  sameness_receipt result{};
  result.occurrence_equal = program.occurrences[0] == program.occurrences[1];
  result.marked_diagram_isomorphic = program.diagram_bijection &&
      program.diagram_incidence[0] == program.diagram_incidence[1] &&
      program.diagram_marks[0] == program.diagram_marks[1];
  result.doctrinal_equivalent =
      program.quasi_inverse && program.unit_witness && program.counit_witness;
  result.observationally_equivalent = true;
  for (std::size_t receiver = 0; receiver < sameness_receiver_capacity; ++receiver) {
    result.observationally_equivalent &=
        program.receiver_faces[0][receiver] == program.receiver_faces[1][receiver] &&
        program.receiver_successors[0][receiver] == program.receiver_successors[1][receiver];
  }
  result.receiver_face_equal = program.receiver_faces[0][0] == program.receiver_faces[1][0];
  result.presentation_equal = program.presentations[0] == program.presentations[1];
  result.byte_equal = program.encodings[0] == program.encodings[1];
  const std::uint64_t digest_left =
      program.encodings[0].value() & program.digest_mask.value();
  const std::uint64_t digest_right =
      program.encodings[1].value() & program.digest_mask.value();
  result.digest_equal = digest_left == digest_right;
  result.equal_face_distinct_occurrence = result.receiver_face_equal && !result.occurrence_equal;
  result.equal_bytes_distinct_soul = result.byte_equal && !result.occurrence_equal;
  result.digest_collision_retained =
      program.collision_encodings[0] != program.collision_encodings[1] &&
      (program.collision_encodings[0].value() & program.digest_mask.value()) ==
          (program.collision_encodings[1].value() & program.digest_mask.value());
  result.byte_implies_digest = !result.byte_equal || result.digest_equal;
  return result;
}

}  // namespace holonics::receiver
