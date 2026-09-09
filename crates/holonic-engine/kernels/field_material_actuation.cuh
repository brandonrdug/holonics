// A material actuation is a tensor-basis realization of a retained packet face.
// It retains the source edge but contributes no new observed relation to fit.
extern "C" __global__ void section_field_material_actuation(
    const int64_t *incoming,uint32_t nodes,uint32_t targets,uint32_t width,uint32_t grain,
    uint32_t quadrature,uint32_t coordinate,int64_t *lo,int64_t *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!nodes||width<2u||nodes%width||quadrature>1u||coordinate>=targets||grain<1u||grain>120u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t address=coordinate;
    for(uint32_t f=0;f<nodes/width;++f){
        uint32_t selected=address%width;address/=width;
        for(uint32_t j=0;j<width;++j){
            const int64_t *v=incoming+3u*(f*width+j);
            if(v[2]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
            if(j!=selected){if(v[0]||v[1]){atomicOr(slot,REFUSED_BOUND);return;}}
            else{HistoryInteger r(v[0]),i(v[1]),d(v[2]);if(r*r+i*i!=d*d){atomicOr(slot,REFUSED_BOUND);return;}}
        }
    }
    if(address){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *v=(wide *)lo,radius=0;contextual_tensor_target(incoming,nodes,width,targets,grain,v,&radius,slot);v[2u*targets]=radius;
    if(*slot)return;
    MomentInteger r=moment_lift(history_integer(radius)),error=MomentInteger(2)*r*r;
    for(uint32_t j=0;j<targets;++j)if(j!=coordinate){
        HistoryInteger gap=history_integer(v[2u*coordinate+quadrature])-history_integer(v[2u*j+quadrature]);
        MomentInteger g=moment_lift(gap);
        if(gap<=0 || g*g<=error){atomicOr(slot,REFUSED_BOUND);return;}
    }
    for(uint32_t j=0;j<4u*targets+2u;++j)hi[j]=lo[j];
}
