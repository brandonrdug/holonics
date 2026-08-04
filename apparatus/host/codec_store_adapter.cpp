#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>

#include <holonics/apparatus/codec_store_adapter.hpp>
#include <holonics/codec/reflection_law.hpp>

namespace holonics::apparatus {
namespace {

void mix(std::uint64_t& fold, std::uint64_t value) noexcept {
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t octet = 0; octet < 8; ++octet) {
    fold ^= value & 255U;
    fold *= prime;
    value >>= 8U;
  }
}

[[nodiscard]] bool read_values(
    const char* path,
    std::uint64_t (&values)[21],
    codec_store_receipt& receipt) noexcept {
  std::ifstream input{path, std::ios::binary};
  if (!input) { receipt.state = codec_store_status::open_refused; return false; }
  char byte = 0;
  std::uint64_t material = 14'695'981'039'346'656'037ULL;
  while (input.get(byte)) { mix(material, static_cast<unsigned char>(byte)); }
  if (!input.eof()) { receipt.state = codec_store_status::schema_refused; return false; }
  input.close();
  input.open(path);
  for (auto& value : values) {
    if (!(input >> value)) { receipt.state = codec_store_status::schema_refused; return false; }
  }
  std::string trailing{};
  if (input >> trailing) { receipt.state = codec_store_status::schema_refused; return false; }
  receipt.material_testimony = exact::word{material};
  return true;
}

[[nodiscard]] codec::codec_program program_from(
    const std::uint64_t* values) noexcept {
  codec::codec_program result{};
  result.identity = exact::word{values[0]};
  result.version = exact::word{values[1]};
  result.face.identity = exact::word{values[2]};
  result.face.exterior_port = exact::word{values[3]};
  result.face.body_port = exact::word{values[4]};
  result.face.form = static_cast<codec::codec_form>(values[5]);
  result.scale = exact::word{values[6]};
  result.bias = exact::word{values[7]};
  result.inherited_lineage = exact::word{values[8]};
  return result;
}

}  // namespace

codec_store_result mount_codec_store(const char* path) noexcept {
  codec_store_result result{};
  if (!result.environment.admitted() || path == nullptr) { return result; }
  std::uint64_t values[21]{};
  if (!read_values(path, values, result.receipt)) { return result; }
  auto& environment = result.environment.value();
  environment.identity = exact::word{values[0]};
  environment.inherited_provenance = exact::word{values[1]};
  environment.core_occurrence = exact::word{values[2]};
  environment.operative = program_from(values + 3);
  environment.unrelated = program_from(values + 12);
  environment.source_material_testimony = result.receipt.material_testimony;
  std::uint64_t path_fold = 14'695'981'039'346'656'037ULL;
  for (const char* cursor = path; *cursor != '\0'; ++cursor) {
    mix(path_fold, static_cast<unsigned char>(*cursor));
  }
  environment.storage_lineage = exact::word{path_fold};
  result.receipt.path_testimony = exact::word{path_fold};
  result.receipt.inherited_provenance = environment.inherited_provenance;
  result.receipt.state = codec::valid_environment(environment)
      ? codec_store_status::exact : codec_store_status::schema_refused;
  return result;
}

codec_store_result mount_relocated_codec_store(
    const char* path,
    const char* destination) noexcept {
  namespace fs = std::filesystem;
  std::error_code error{};
  fs::create_directories(destination, error);
  if (error) {
    codec_store_result refused{};
    refused.receipt.state = codec_store_status::relocation_refused;
    return refused;
  }
  const fs::path relocated = fs::path{destination} / "renamed_codec_surface.hcodec";
  fs::copy_file(path, relocated, fs::copy_options::overwrite_existing, error);
  if (error) {
    codec_store_result refused{};
    refused.receipt.state = codec_store_status::relocation_refused;
    return refused;
  }
  return mount_codec_store(relocated.c_str());
}

bool same_codec_material(
    const codec::mounted_codec_environment& left,
    const codec::mounted_codec_environment& right) noexcept {
  if (!left.admitted() || !right.admitted()) { return false; }
  const auto& a = left.value();
  const auto& b = right.value();
  return a.identity == b.identity && a.inherited_provenance == b.inherited_provenance &&
      a.core_occurrence == b.core_occurrence && codec::equal_program(a.operative, b.operative) &&
      codec::equal_program(a.unrelated, b.unrelated) &&
      a.source_material_testimony == b.source_material_testimony &&
      a.storage_lineage != b.storage_lineage;
}

}  // namespace holonics::apparatus
