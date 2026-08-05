#include <new>

#include <holonics/apparatus/elementary_calculus_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void elementary_mount_kernel(const elementary_discovery_mount *mount,
    unsigned char *storage,event::elementary_calculus_observation *out){if(blockIdx.x||threadIdx.x)return;
  ::new(static_cast<void *>(storage))event::resident_elementary_calculus(
      mount->cards,mount->inherited,out->predecessor_remount);}
__global__ void elementary_source_kernel(const elementary_discovery_mount *mount,
    event::elementary_calculus_observation *out,std::uint8_t source){if(blockIdx.x||threadIdx.x)return;
  if(source==0)organ::occurrence_incidence_detail::derive(mount->cards.occurrence,out->inquiry.occurrence);
  else if(source==1)organ::composition_receiver_detail::derive_composition(
      mount->cards.composition,out->inquiry.composition);
  else if(source==2)organ::composition_receiver_detail::derive_receiver(
      mount->cards.receiver,out->inquiry.receiver);
  else if(source==3)organ::chart_conduct_detail::derive_chart(mount->cards.chart,out->inquiry.chart);
  else organ::chart_conduct_detail::derive_conduct(mount->cards.conduct,out->inquiry.conduct);}
__global__ void elementary_close_kernel(const elementary_discovery_mount *mount,
    event::elementary_calculus_observation *out,
    organ::elementary_workspace *workspace){if(blockIdx.x||threadIdx.x)return;
  const exact::word ports[5]{mount->cards.occurrence.metadata.lineage,
      mount->cards.composition.metadata.lineage,mount->cards.receiver.metadata.lineage,
      mount->cards.chart.metadata.lineage,mount->cards.conduct.metadata.lineage};
  out->inquiry.development_ports_distinct=true;
  for(std::uint8_t i=0;i<5;++i)for(std::uint8_t j=i+1U;j<5;++j)
    out->inquiry.development_ports_distinct=out->inquiry.development_ports_distinct&&ports[i]!=ports[j];
  organ::self_holonomy_detail::close(out->inquiry,*workspace);}
__global__ void elementary_form_kernel(unsigned char *storage,
    event::elementary_calculus_observation *out){if(!blockIdx.x&&!threadIdx.x)static_cast<void>(
      reinterpret_cast<event::resident_elementary_calculus *>(storage)->form_calculus(*out));}
__global__ void elementary_resume_kernel(const event::checker_raw_return *raw,unsigned char *storage,
    event::elementary_calculus_observation *out){if(!blockIdx.x&&!threadIdx.x)static_cast<void>(
      reinterpret_cast<event::resident_elementary_calculus *>(storage)->resume_calculus(*raw,*out));}
__global__ void elementary_rest_kernel(unsigned char *storage,event::elementary_calculus_rest_record *rest,
    event::elementary_calculus_rest_record *handoff,event::elementary_calculus_observation *out){
  if(blockIdx.x||threadIdx.x)return;
  auto *resident=reinterpret_cast<event::resident_elementary_calculus *>(storage);
  out->rest=resident->rest(*rest);event::elementary_calculus_remount_receipt remount{};
  auto *resumed=::new(static_cast<void *>(storage))event::resident_elementary_calculus(*rest,remount);
  out->remount=remount;out->final_head=resumed->head();out->final_continuation=resumed->continuation();
  out->final_can_continue=resumed->can_continue();out->handoff=resumed->rest(*handoff);}
__global__ void elementary_observe_kernel(const event::elementary_calculus_observation *source,
    event::elementary_calculus_observation *out){if(!blockIdx.x&&!threadIdx.x)*out=*source;}

__global__ void heldout_mount_kernel(const elementary_application_mount *mount,unsigned char *storage,
    event::heldout_holonomy_observation *out){if(blockIdx.x||threadIdx.x)return;
  ::new(static_cast<void *>(storage))event::resident_elementary_calculus(
      mount->inherited,out->predecessor_remount);}
__global__ void heldout_source_kernel(const elementary_application_mount *mount,
    organ::heldout_workspace *workspace,event::heldout_holonomy_observation *out){
  if(!blockIdx.x&&!threadIdx.x)organ::self_holonomy_detail::derive_source(mount->heldout,*workspace,out->inquiry);}
__global__ void heldout_predict_kernel(unsigned char *storage,event::heldout_holonomy_observation *out){
  if(blockIdx.x||threadIdx.x)return;
  auto *resident=reinterpret_cast<event::resident_elementary_calculus *>(storage);
  organ::self_holonomy_detail::predict(resident->self_organ(),out->inquiry);}
__global__ void heldout_compare_kernel(unsigned char *storage,const organ::heldout_workspace *workspace,
    event::heldout_holonomy_observation *out){if(blockIdx.x||threadIdx.x)return;
  auto *resident=reinterpret_cast<event::resident_elementary_calculus *>(storage);
  organ::self_holonomy_detail::compare(resident->self_organ(),*workspace,out->inquiry);}
__global__ void heldout_form_kernel(unsigned char *storage,event::heldout_holonomy_observation *out){
  if(!blockIdx.x&&!threadIdx.x)static_cast<void>(reinterpret_cast<event::resident_elementary_calculus *>(storage)->form_heldout(*out));}
__global__ void heldout_resume_kernel(const event::checker_raw_return *raw,unsigned char *storage,
    event::heldout_holonomy_observation *out){if(blockIdx.x||threadIdx.x)return;
  auto *resident=reinterpret_cast<event::resident_elementary_calculus *>(storage);
  static_cast<void>(resident->resume_heldout(*raw,*out));static_cast<void>(codec::render_elementary_dossier(
      event::rested_elementary_surface(resident->laws()),event::heldout_surface(out->inquiry,resident->self_organ()),out->dossier));}
__global__ void heldout_rest_kernel(unsigned char *storage,event::elementary_calculus_rest_record *rest,
    event::elementary_calculus_rest_record *handoff,event::heldout_holonomy_observation *out){
  if(blockIdx.x||threadIdx.x)return;
  auto *resident=reinterpret_cast<event::resident_elementary_calculus *>(storage);
  out->rest=resident->rest(*rest);event::elementary_calculus_remount_receipt remount{};
  auto *resumed=::new(static_cast<void *>(storage))event::resident_elementary_calculus(*rest,remount);
  out->remount=remount;out->final_head=resumed->head();out->final_continuation=resumed->continuation();
  out->final_can_continue=resumed->can_continue();out->handoff=resumed->rest(*handoff);}
__global__ void heldout_observe_kernel(const event::heldout_holonomy_observation *source,
    event::heldout_holonomy_observation *out){if(!blockIdx.x&&!threadIdx.x)*out=*source;}
}  // namespace

cudaError_t launch_elementary_mount(const elementary_discovery_mount*m,unsigned char*s,event::elementary_calculus_observation*o)noexcept{elementary_mount_kernel<<<1,1>>>(m,s,o);return cudaGetLastError();}
cudaError_t launch_elementary_source(const elementary_discovery_mount*m,event::elementary_calculus_observation*o,std::uint8_t i,cudaStream_t s)noexcept{elementary_source_kernel<<<1,1,0,s>>>(m,o,i);return cudaGetLastError();}
cudaError_t launch_elementary_close(const elementary_discovery_mount*m,event::elementary_calculus_observation*o,organ::elementary_workspace*w)noexcept{elementary_close_kernel<<<1,1>>>(m,o,w);return cudaGetLastError();}
cudaError_t launch_elementary_form(event::resident_elementary_calculus*r,event::elementary_calculus_observation*o)noexcept{elementary_form_kernel<<<1,1>>>(reinterpret_cast<unsigned char*>(r),o);return cudaGetLastError();}
cudaError_t launch_elementary_resume(const event::checker_raw_return*x,event::resident_elementary_calculus*r,event::elementary_calculus_observation*o)noexcept{elementary_resume_kernel<<<1,1>>>(x,reinterpret_cast<unsigned char*>(r),o);return cudaGetLastError();}
cudaError_t launch_elementary_rest(event::resident_elementary_calculus*r,event::elementary_calculus_rest_record*a,event::elementary_calculus_rest_record*b,event::elementary_calculus_observation*o)noexcept{elementary_rest_kernel<<<1,1>>>(reinterpret_cast<unsigned char*>(r),a,b,o);return cudaGetLastError();}
cudaError_t launch_elementary_observe(const event::elementary_calculus_observation*s,event::elementary_calculus_observation*o)noexcept{elementary_observe_kernel<<<1,1>>>(s,o);return cudaGetLastError();}
cudaError_t launch_heldout_mount(const elementary_application_mount*m,unsigned char*s,event::heldout_holonomy_observation*o)noexcept{heldout_mount_kernel<<<1,1>>>(m,s,o);return cudaGetLastError();}
cudaError_t launch_heldout_source(const elementary_application_mount*m,organ::heldout_workspace*w,event::heldout_holonomy_observation*o,cudaStream_t s)noexcept{heldout_source_kernel<<<1,1,0,s>>>(m,w,o);return cudaGetLastError();}
cudaError_t launch_heldout_predict(event::resident_elementary_calculus*r,event::heldout_holonomy_observation*o,cudaStream_t s)noexcept{heldout_predict_kernel<<<1,1,0,s>>>(reinterpret_cast<unsigned char*>(r),o);return cudaGetLastError();}
cudaError_t launch_heldout_compare(event::resident_elementary_calculus*r,const organ::heldout_workspace*w,event::heldout_holonomy_observation*o)noexcept{heldout_compare_kernel<<<1,1>>>(reinterpret_cast<unsigned char*>(r),w,o);return cudaGetLastError();}
cudaError_t launch_heldout_form(event::resident_elementary_calculus*r,event::heldout_holonomy_observation*o)noexcept{heldout_form_kernel<<<1,1>>>(reinterpret_cast<unsigned char*>(r),o);return cudaGetLastError();}
cudaError_t launch_heldout_resume(const event::checker_raw_return*x,event::resident_elementary_calculus*r,event::heldout_holonomy_observation*o)noexcept{heldout_resume_kernel<<<1,1>>>(x,reinterpret_cast<unsigned char*>(r),o);return cudaGetLastError();}
cudaError_t launch_heldout_rest(event::resident_elementary_calculus*r,event::elementary_calculus_rest_record*a,event::elementary_calculus_rest_record*b,event::heldout_holonomy_observation*o)noexcept{heldout_rest_kernel<<<1,1>>>(reinterpret_cast<unsigned char*>(r),a,b,o);return cudaGetLastError();}
cudaError_t launch_heldout_observe(const event::heldout_holonomy_observation*s,event::heldout_holonomy_observation*o)noexcept{heldout_observe_kernel<<<1,1>>>(s,o);return cudaGetLastError();}

}  // namespace holonics::apparatus
