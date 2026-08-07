#include <fcntl.h>
#include <fstream>
#include <string>
#include <unistd.h>

#include <holonics/apparatus/elementary_calculus_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] bool opened(const char *path) noexcept {
  const int descriptor = ::open(path,O_RDONLY); return descriptor >= 0 && ::close(descriptor) == 0;
}
[[nodiscard]] bool metadata(std::istream &in, organ::cultivation_card_metadata &out) noexcept {
  std::uint64_t schema=0,occurrence=0,incoming=0,returned=0,lineage=0;
  if (!(in>>schema>>occurrence>>incoming>>returned>>lineage)) return false;
  out={exact::word{schema},exact::word{occurrence},exact::word{incoming},
       exact::word{returned},exact::word{lineage},true}; return true;
}
[[nodiscard]] bool exhausted(std::istream &in) noexcept { std::string excess{}; return !(in>>excess); }
[[nodiscard]] cultivated_store_receipt finish(bool exact,std::uint64_t bytes) noexcept {
  cultivated_store_receipt out{}; out.state=exact?cultivated_store_status::returned:
      cultivated_store_status::transfer_refused; out.bytes=exact::word{bytes};
  out.transfer_calls=exact::word{1}; out.integrity_exact=exact; return out;
}
[[nodiscard]] bool bit(std::istream &in,std::uint8_t &out) noexcept {
  std::int16_t value=0; const bool exact=static_cast<bool>(in>>value)&&value>=0&&value<=1;
  out=static_cast<std::uint8_t>(value); return exact;
}
[[nodiscard]] bool boolean(std::istream &in,bool &out) noexcept {
  std::uint8_t value=0; const bool exact=bit(in,value); out=value!=0; return exact;
}
[[nodiscard]] bool matrix(std::istream &in,organ::exact_matrix2 &out) noexcept {
  bool exact=true; for(auto &value:out.value) exact=exact&&static_cast<bool>(in>>value); return exact;
}
}  // namespace

cultivated_store_receipt read_occurrence_incidence_card(const char *path,
    organ::occurrence_incidence_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; std::uint16_t count=0;
  bool ok=aperture&&in.good()&&metadata(in,card.metadata)&&static_cast<bool>(in>>count)&&count==6;
  card.occurrence_count=static_cast<std::uint8_t>(count);
  for(std::uint8_t row=0;ok&&row<card.occurrence_count;++row){
    for(auto &value:card.coordinates[row]) ok=ok&&static_cast<bool>(in>>value);
    ok=ok&&static_cast<bool>(in>>card.payload[row]);
  }
  for(auto &row:card.boundary_one) for(auto &value:row){
    std::int16_t parsed=0; ok=ok&&static_cast<bool>(in>>parsed)&&parsed>=-1&&parsed<=1;
    value=static_cast<std::int8_t>(parsed);
  }
  for(auto &row:card.boundary_two) for(auto &value:row){
    std::int16_t parsed=0; ok=ok&&static_cast<bool>(in>>parsed)&&parsed>=-1&&parsed<=1;
    value=static_cast<std::int8_t>(parsed);
  }
  ok=ok&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

cultivated_store_receipt read_composition_card(const char *path,
    organ::composition_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; std::uint16_t count=0;
  bool ok=aperture&&in.good()&&metadata(in,card.metadata)&&static_cast<bool>(in>>count)&&count==5;
  card.case_count=static_cast<std::uint8_t>(count);
  for(std::uint8_t row=0;ok&&row<card.case_count;++row){ auto &item=card.cases[row];
    std::uint16_t visible=0; ok=ok&&static_cast<bool>(in>>visible)&&visible<=2;
    item.visible=static_cast<std::uint8_t>(visible);
    ok=ok&&boolean(in,item.contact)&&boolean(in,item.predecessor_link)&&
       boolean(in,item.forward_available)&&boolean(in,item.reverse_available);
    for(auto &value:item.forward) ok=ok&&static_cast<bool>(in>>value);
    for(auto &value:item.reverse) ok=ok&&static_cast<bool>(in>>value);
  }
  ok=ok&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

cultivated_store_receipt read_receiver_card(const char *path,organ::receiver_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; std::uint16_t count=0;
  bool ok=aperture&&in.good()&&metadata(in,card.metadata)&&static_cast<bool>(in>>count)&&count==6;
  card.source_count=static_cast<std::uint8_t>(count);
  for(auto &value:card.coarse) ok=ok&&static_cast<bool>(in>>value);
  for(auto &value:card.fine) ok=ok&&static_cast<bool>(in>>value);
  for(auto &value:card.first_consequence) ok=ok&&static_cast<bool>(in>>value);
  for(auto &value:card.strict_consequence) ok=ok&&static_cast<bool>(in>>value);
  ok=ok&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

cultivated_store_receipt read_local_chart_card(const char *path,
    organ::local_chart_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; bool ok=aperture&&in.good()&&
      metadata(in,card.metadata)&&matrix(in,card.first)&&matrix(in,card.second)&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

cultivated_store_receipt read_return_conduct_card(const char *path,
    organ::return_conduct_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; std::uint16_t count=0;
  bool ok=aperture&&in.good()&&metadata(in,card.metadata)&&static_cast<bool>(in>>count)&&count==8;
  card.case_count=static_cast<std::uint8_t>(count);
  for(std::uint8_t row=0;ok&&row<card.case_count;++row){
    for(auto &value:card.cases[row].fields) ok=ok&&bit(in,value);
    ok=ok&&boolean(in,card.cases[row].changed_conduct);
  }
  ok=ok&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

cultivated_store_receipt read_heldout_triangle_card(const char *path,
    organ::heldout_triangle_card &card) noexcept {
  const bool aperture=opened(path); std::ifstream in{path}; std::uint16_t horizon=0,slot=0;
  bool ok=aperture&&in.good()&&metadata(in,card.metadata)&&
      static_cast<bool>(in>>horizon>>slot>>card.changed_value)&&horizon==8&&slot<4;
  card.maximum_horizon=static_cast<std::uint8_t>(horizon);
  card.changed_slot=static_cast<std::uint8_t>(slot);
  for(auto &edge:card.edges) ok=ok&&matrix(in,edge);
  ok=ok&&exhausted(in);
  if(!ok) card.metadata.parsed=false;
  return finish(ok,sizeof(card));
}

}  // namespace holonics::apparatus
