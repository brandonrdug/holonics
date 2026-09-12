// Exact point-current packet operations. Last word is one positive common denominator.
// These compose the existing checked wide arithmetic and rational normalization owners.
extern "C" __global__ void section_packet_contract(
 const int64_t *ml,const int64_t *mh,const int64_t *xl,const int64_t *xh,
 uint32_t rows,uint32_t cols,uint32_t affine,int64_t *ol,int64_t *oh,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
 if(blockIdx.x||threadIdx.x) return;
 if(upstream_refused(census,lineage,lineage_count,slot)) return;
 if(!rows||!cols||affine>1u) {atomicOr(slot,REFUSED_MALFORMED);return;}
 uint32_t size=rows*cols;
 wide md=fibre_current_denominator(ml,mh,size,UINT32_MAX,slot);
 uint32_t input_width=cols-affine;
 wide xd=fibre_current_denominator(xl,xh,input_width,UINT32_MAX,slot);
 if(*slot)return;
 for(uint32_t i=0;i<size;++i)if(ml[i]!=mh[i])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<input_width;++i)if(xl[i]!=xh[i])atomicOr(slot,REFUSED_MALFORMED);
 if(*slot)return;
 extern __shared__ wide scratch[];
 wide den=product_checked(md,xd,slot);
 for(uint32_t r=0;r<rows;++r){
  wide sum=0;
  for(uint32_t c=0;c<cols;++c)sum=add_checked(sum,product_checked(ml[r*cols+c],(affine && c==input_width)?xd:xl[c],slot),slot);
  scratch[r]=sum;
 }
 if(*slot)return;
 fibre_normalize(scratch,rows,&den,slot);
 for(uint32_t r=0;r<rows;++r)to_word(scratch[r],slot);
 to_word(den,slot);if(*slot)return;
 for(uint32_t r=0;r<rows;++r)ol[r]=oh[r]=(int64_t)scratch[r];
 ol[rows]=oh[rows]=(int64_t)den;
}
extern "C" __global__ void section_packet_hadamard(
 const int64_t *al,const int64_t *ah,const int64_t *bl,const int64_t *bh,
 uint32_t width,int64_t *ol,int64_t *oh,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
 if(blockIdx.x||threadIdx.x)return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 if(!width){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide ad=fibre_current_denominator(al,ah,width,UINT32_MAX,slot);
 wide bd=fibre_current_denominator(bl,bh,width,UINT32_MAX,slot);
 if(*slot)return;
 extern __shared__ wide scratch[];
 for(uint32_t i=0;i<width;++i){
  if(al[i]!=ah[i]||bl[i]!=bh[i])atomicOr(slot,REFUSED_MALFORMED);
  scratch[i]=product_checked(al[i],bl[i],slot);
 }
 wide den=product_checked(ad,bd,slot);if(*slot)return;
 fibre_normalize(scratch,width,&den,slot);
 for(uint32_t i=0;i<width;++i)to_word(scratch[i],slot);
 to_word(den,slot);if(*slot)return;
 for(uint32_t i=0;i<width;++i)ol[i]=oh[i]=(int64_t)scratch[i];
 ol[width]=oh[width]=(int64_t)den;
}
