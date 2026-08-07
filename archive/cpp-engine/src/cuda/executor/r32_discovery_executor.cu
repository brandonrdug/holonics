#include <holonics/apparatus/elementary_calculus_executor.hpp>
#include <holonics/apparatus/elementary_current_set.hpp>

namespace holonics::apparatus {
namespace {
struct discovery_storage final {
  elementary_discovery_mount *mount{}; unsigned char *resident{};
  event::elementary_calculus_observation *observation{}; event::elementary_calculus_observation *returned{};
  organ::elementary_workspace *workspace{}; event::checker_raw_return *raw{};
  event::elementary_calculus_rest_record *rest{}; event::elementary_calculus_rest_record *handoff{};
};
void release_one(void *value)noexcept{if(value)static_cast<void>(cudaFree(value));}
void release(discovery_storage&s)noexcept{release_one(s.handoff);release_one(s.rest);release_one(s.raw);
  release_one(s.workspace);release_one(s.returned);release_one(s.observation);release_one(s.resident);
  release_one(s.mount);s={};}
[[nodiscard]] bool allocate(discovery_storage&s)noexcept{return
  cudaMalloc(reinterpret_cast<void**>(&s.mount),sizeof(*s.mount))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.resident),sizeof(event::resident_elementary_calculus))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.observation),sizeof(*s.observation))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.returned),sizeof(*s.returned))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.workspace),sizeof(*s.workspace))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.raw),sizeof(*s.raw))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.rest),sizeof(*s.rest))==cudaSuccess&&
  cudaMalloc(reinterpret_cast<void**>(&s.handoff),sizeof(*s.handoff))==cudaSuccess;}
[[nodiscard]] bool initialize(const elementary_discovery_mount&m,discovery_storage&s)noexcept{return
  cudaMemcpy(s.mount,&m,sizeof(m),cudaMemcpyHostToDevice)==cudaSuccess&&
  cudaMemset(s.resident,0,sizeof(event::resident_elementary_calculus))==cudaSuccess&&
  cudaMemset(s.observation,0,sizeof(*s.observation))==cudaSuccess&&
  cudaMemset(s.returned,0,sizeof(*s.returned))==cudaSuccess&&
  cudaMemset(s.workspace,0,sizeof(*s.workspace))==cudaSuccess&&cudaMemset(s.raw,0,sizeof(*s.raw))==cudaSuccess&&
  cudaMemset(s.rest,0,sizeof(*s.rest))==cudaSuccess&&cudaMemset(s.handoff,0,sizeof(*s.handoff))==cudaSuccess;}
[[nodiscard]] bool device(elementary_executor_receipt&r)noexcept{int count=0,major=0,minor=0;
  if(cudaGetDeviceCount(&count)!=cudaSuccess||count<=0||cudaSetDevice(0)!=cudaSuccess||
    cudaDeviceGetAttribute(&major,cudaDevAttrComputeCapabilityMajor,0)!=cudaSuccess||
    cudaDeviceGetAttribute(&minor,cudaDevAttrComputeCapabilityMinor,0)!=cudaSuccess)return false;
  r.device_major=static_cast<std::uint32_t>(major);r.device_minor=static_cast<std::uint32_t>(minor);return true;}
}  // namespace

elementary_executor_receipt execute_elementary_discovery(const elementary_discovery_mount&mount,
    const lean_process_configuration&process,event::elementary_calculus_observation&observation,
    organ::elementary_workspace&workspace,event::elementary_calculus_rest_record&handoff)noexcept{
  elementary_executor_receipt receipt{};
  if(mount.inherited.integrity!=event::cultivated_organ_rest_integrity(mount.inherited))return receipt;
  if(!device(receipt)){receipt.state=elementary_executor_status::device_unavailable;return receipt;}
  discovery_storage s{};if(!allocate(s)){release(s);receipt.state=elementary_executor_status::allocation_refused;return receipt;}
  if(!initialize(mount,s)||launch_elementary_mount(s.mount,s.resident,s.observation)!=cudaSuccess||
      cudaDeviceSynchronize()!=cudaSuccess){release(s);receipt.state=elementary_executor_status::transfer_refused;return receipt;}
  elementary_current_set currents{};bool exact=open_elementary_currents(currents);
  for(std::uint8_t i=0;exact&&i<5;++i)exact=launch_elementary_source(s.mount,s.observation,i,currents.currents[i])==cudaSuccess;
  exact=exact&&join_elementary_currents(currents);close_elementary_currents(currents);
  if(!exact||launch_elementary_close(s.mount,s.observation,s.workspace)!=cudaSuccess||
      launch_elementary_form(reinterpret_cast<event::resident_elementary_calculus*>(s.resident),s.observation)!=cudaSuccess||
      cudaDeviceSynchronize()!=cudaSuccess||cudaMemcpy(&observation,s.observation,sizeof(observation),cudaMemcpyDeviceToHost)!=cudaSuccess||
      !observation.inquiry.theory_formed){release(s);receipt.state=elementary_executor_status::formation_refused;return receipt;}
  event::checker_raw_return raw{};const lean_source_view source{observation.passage.formal.passage,
      observation.passage.formal.identity,observation.passage.formal.bytes,observation.passage.formal.byte_count};
  receipt.checker=run_lean_checker_source(source,observation.passage.outbound,process,raw);
  if(!receipt.checker.returned()){release(s);receipt.state=elementary_executor_status::checker_process_refused;return receipt;}
  if(cudaMemcpy(s.raw,&raw,sizeof(raw),cudaMemcpyHostToDevice)!=cudaSuccess||
      launch_elementary_resume(s.raw,reinterpret_cast<event::resident_elementary_calculus*>(s.resident),s.observation)!=cudaSuccess||
      launch_elementary_rest(reinterpret_cast<event::resident_elementary_calculus*>(s.resident),s.rest,s.handoff,s.observation)!=cudaSuccess||
      launch_elementary_observe(s.observation,s.returned)!=cudaSuccess||cudaDeviceSynchronize()!=cudaSuccess||
      cudaMemcpy(&observation,s.returned,sizeof(observation),cudaMemcpyDeviceToHost)!=cudaSuccess||
      cudaMemcpy(&workspace,s.workspace,sizeof(workspace),cudaMemcpyDeviceToHost)!=cudaSuccess||
      cudaMemcpy(&handoff,s.handoff,sizeof(handoff),cudaMemcpyDeviceToHost)!=cudaSuccess){
    release(s);receipt.state=elementary_executor_status::checker_return_refused;return receipt;}
  const std::uint64_t bytes=sizeof(mount)+sizeof(event::resident_elementary_calculus)+2U*sizeof(observation)+
      sizeof(workspace)+sizeof(raw)+2U*sizeof(handoff);release(s);
  if(observation.passage.typed.state!=event::checker_return_status::accepted||!observation.rest.returned||
      !observation.remount.laws_preserved||!observation.handoff.returned){receipt.state=elementary_executor_status::rest_refused;return receipt;}
  receipt.state=elementary_executor_status::returned;receipt.bytes_to_device=exact::word{sizeof(mount)+sizeof(raw)};
  receipt.bytes_from_device=exact::word{sizeof(observation)+sizeof(workspace)+sizeof(handoff)};
  receipt.resident_bytes=exact::word{bytes};receipt.kernel_launches=exact::word{12};
  receipt.launched_threads=exact::word{12};receipt.semantic_threads=exact::word{10};
  receipt.source_currents=exact::word{5};receipt.dependency_barriers=exact::word{1};
  receipt.physical.resident_bytes={telemetry_status::calibrated_interval,exact::word{bytes},exact::word{bytes},exact::word{1}};
  return receipt;
}

}  // namespace holonics::apparatus
