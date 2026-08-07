#include <holonics/apparatus/elementary_current_set.hpp>

namespace holonics::apparatus {

void close_elementary_currents(elementary_current_set &set) noexcept {
  for(auto &stream:set.currents) if(stream) cudaStreamDestroy(stream);
  set={};
}
bool open_elementary_currents(elementary_current_set &set) noexcept {
  for(auto &stream:set.currents)if(cudaStreamCreateWithFlags(&stream,cudaStreamNonBlocking)!=cudaSuccess){
    close_elementary_currents(set);return false;}
  return true;
}
bool join_elementary_currents(const elementary_current_set &set) noexcept {
  for(const auto stream:set.currents)
    if(cudaStreamSynchronize(stream)!=cudaSuccess) return false;
  return true;
}
bool open_heldout_currents(heldout_current_set &set) noexcept {
  if(cudaStreamCreateWithFlags(&set.source,cudaStreamNonBlocking)!=cudaSuccess)return false;
  if(cudaStreamCreateWithFlags(&set.organ,cudaStreamNonBlocking)!=cudaSuccess){
    close_heldout_currents(set);return false;}
  return true;
}
void close_heldout_currents(heldout_current_set &set) noexcept {
  if(set.source) cudaStreamDestroy(set.source);
  if(set.organ) cudaStreamDestroy(set.organ);
  set={};
}

}  // namespace holonics::apparatus
