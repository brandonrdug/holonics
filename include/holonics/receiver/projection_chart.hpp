#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/receiver/chart_contract.hpp>
#include <holonics/structure/identity_mint.hpp>

namespace holonics::receiver {

inline constexpr std::size_t projection_face_count = 256;
inline constexpr std::size_t projection_word_capacity = 256;

class resident_projection_chart final {
 public:
  resident_projection_chart() = delete;
  resident_projection_chart(const resident_projection_chart&) = delete;
  resident_projection_chart& operator=(const resident_projection_chart&) = delete;
  resident_projection_chart(resident_projection_chart&&) = delete;
  resident_projection_chart& operator=(resident_projection_chart&&) = delete;

  HOLONICS_CALLABLE resident_projection_chart(
      std::uint64_t owner_seed,
      std::size_t occurrence_count) noexcept
      : chart_mint_(owner_seed), projection_identity_(chart_mint_.mint()),
        sequence_identity_(chart_mint_.mint()), occurrence_count_(occurrence_count),
        word_count_((occurrence_count + 63U) / 64U) {}

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted() const noexcept {
    return word_count_ <= projection_word_capacity;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t projection_serial() const noexcept {
    return projection_identity_.serial().value();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t sequence_serial() const noexcept {
    return sequence_identity_.serial().value();
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t word_count() const noexcept {
    return word_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE constexpr std::size_t occurrence_count() const noexcept {
    return occurrence_count_;
  }
  [[nodiscard]] HOLONICS_CALLABLE std::uint64_t* word_address(
      std::uint8_t face,
      std::size_t word_slot) noexcept {
    return &words_[static_cast<std::size_t>(face) * projection_word_capacity + word_slot];
  }
  [[nodiscard]] HOLONICS_CALLABLE std::uint64_t word(
      std::uint8_t face,
      std::size_t word_slot) const noexcept {
    return words_[static_cast<std::size_t>(face) * projection_word_capacity + word_slot];
  }

 private:
  structure::identity_mint<chart_identity_owner> chart_mint_;
  chart_contract::identity_type projection_identity_;
  chart_contract::identity_type sequence_identity_;
  std::size_t occurrence_count_{};
  std::size_t word_count_{};
  std::uint64_t words_[projection_face_count * projection_word_capacity];
};

}  // namespace holonics::receiver
