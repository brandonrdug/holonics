// Lift an actual source (c-p,c,p) and its complete local difference family to the
// joined arrival family (c,c+eta). The source and offered joint are independent retained
// operands, never reconstructed from a residual query prefix.
extern "C" __global__ void section_wave_source_arrival(
 const int64_t *s,const int64_t *shi,uint32_t at,uint32_t den,uint32_t disposition,
 const int64_t *f,const int64_t *fhi,uint32_t fs,uint32_t n,uint32_t receiver,
 int64_t *snap,int64_t *snaphi,int64_t *offered,int64_t *offeredhi,int64_t *out,int64_t *outhi,
 int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t r=2u*n,w=2u*r,fk=fs+r,k=2u+w;
 if(!n||receiver>1u){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide sd=fibre_current_denominator(s,shi,den,disposition,slot);if(*slot)return;
 for(uint32_t i=0;i<3u*r;++i)if(s[at+i]!=shi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<r;++i)if((wide)s[at+i]!=(wide)s[at+r+i]-(wide)s[at+2u*r+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(receiver){wide a=0,b=0;for(uint32_t i=0;i<n;++i){a=add_checked(a,s[at+r+2u*i],slot);b=add_checked(b,s[at+2u*r+2u*i],slot);}
   if(*slot)return;if(a!=sd||b!=sd){atomicOr(slot,REFUSED_MALFORMED);return;}}
 for(size_t i=0;i<(size_t)fk+4u+(size_t)r*r;++i)if(f[i]!=fhi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide fd=f[fk];uint32_t status=(uint32_t)f[fk+1u];
 if(fd<=0||status>2u){atomicOr(slot,REFUSED_MALFORMED);return;}
 to_word(sd,slot);if(*slot)return;
 for(uint32_t i=0;i<3u*r;++i)snap[i]=snaphi[i]=s[at+i];snap[3u*r]=snaphi[3u*r]=(int64_t)sd;
 for(uint32_t i=0;i<r;++i){offered[i]=offeredhi[i]=s[at+2u*r+i];offered[r+i]=offeredhi[r+i]=s[at+r+i];}
 offered[w]=offeredhi[w]=(int64_t)sd;
 for(size_t i=0;i<(size_t)k+4u+(size_t)w*w;++i)out[i]=outhi[i]=0;
 out[k]=outhi[k]=1;out[k+1u]=outhi[k+1u]=status;out[k+2u]=outhi[k+2u]=-1;
 if(status==1u)return;
 wide *v=(wide*)workspace,od=fibre_lcm(sd,fd,slot);if(*slot)return;
 v[0]=0;v[1]=0;
 for(uint32_t i=0;i<r;++i){v[2u+i]=product_checked(s[at+r+i],od/sd,slot);v[2u+r+i]=add_checked(v[2u+i],product_checked(f[fs+i],od/fd,slot),slot);}
 if(*slot)return;fibre_normalize(v,k,&od,slot);to_word(od,slot);
 for(uint32_t i=0;i<k;++i)to_word(v[i],slot);if(*slot)return;
 for(uint32_t i=0;i<k;++i)out[i]=outhi[i]=(int64_t)v[i];out[k]=outhi[k]=(int64_t)od;
 uint32_t rank=1;
 for(uint32_t i=0;i<r;++i){if(f[fk+4u+(size_t)i*r+i])++rank;
  for(uint32_t j=0;j<r;++j){size_t o=k+4u+(size_t)(r+i)*w+r+j;out[o]=outhi[o]=f[fk+4u+(size_t)i*r+j];}}
 out[k+3u]=outhi[k+3u]=rank;
}

// Exact graph of the source union y+Aq, founded by the declared actual reaction.
// Only current coordinates move; lambda and the complete original anchor remain.
extern "C" __global__ void section_wave_source_map(
 const int64_t *reaction,const int64_t *hi,uint32_t n,int64_t *basis,int64_t *basis_hi,int64_t *workspace,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t w=4u*n,z=2u+w,q=z+w,k=2u*q;
 for(uint32_t i=0;i<5u*w+2u;++i)if(reaction[i]!=hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 // Empty learned evidence preserves the actual offered current. It does not assert a
 // zero learned difference or a compatible arrival; its original prediction remains retained.
 if(reaction[5u*w+1u]<0||reaction[5u*w+1u]>1){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide den=fibre_current_denominator(reaction,hi,5u*w,UINT32_MAX,slot);if(*slot)return;
 if(reaction[5u*w+1u]==1){
   for(uint32_t i=0;i<w;++i)if(reaction[w+i]!=reaction[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
   for(uint32_t i=2u*w;i<5u*w;++i)if(reaction[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 }
 wide *row=(wide*)workspace,*d=row+k,dd=0,gap=0;
 for(uint32_t i=0;i<w;++i){wide x=reaction[i],y=reaction[w+i];d[i]=sub_checked(x,y,slot);
   dd=add_checked(dd,product_checked(d[i],d[i],slot),slot);
   gap=add_checked(gap,sub_checked(product_checked(y,y,slot),product_checked(x,x,slot),slot),slot);}
 if(*slot)return;wide D=add_checked(dd,(gap<0?sub_checked(0,gap,slot):gap),slot);if(*slot)return;
 for(size_t i=0;i<(size_t)k*k;++i)basis[i]=basis_hi[i]=0;
 for(uint32_t col=0;col<q;++col){
   for(uint32_t j=0;j<k;++j)row[j]=0;
   if(col<z){row[col]=row[q+col]=col==0?den:1;
     if(col==0)for(uint32_t i=0;i<w;++i)row[q+z+i]=reaction[w+i];
   }else{uint32_t j=col-z;row[col]=D?D:1;
     for(uint32_t i=0;i<w;++i)row[q+z+i]=D?sub_checked(i==j?D:0,product_checked(2,product_checked(d[i],d[j],slot),slot),slot):(i==j?1:0);}
   if(*slot)return;condition_stage_row(basis,basis_hi,k,row,slot);if(*slot)return;
 }
 // Every input pivot exists: this source passage is total and preserves anchor support.
 for(uint32_t i=0;i<q;++i)if(basis[(size_t)i*k+i]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
}

// Every adjacent pair in a supplied field, including its final pair. No outside endpoint
// or observed successor is invented. This only prepares source incidence on device.
extern "C" __global__ void section_wave_source_pairs(
 const int64_t *field,const int64_t *hi,uint32_t width,uint32_t stride,uint32_t rational,uint32_t rows,
 int64_t *out,int64_t *out_hi,int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 uint32_t row=blockIdx.x*blockDim.x+threadIdx.x;if(row>=rows)return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t a=row*stride,b=a+stride,w=3u*width;
 wide pd=fibre_current_denominator(field,hi,rational?a+width:UINT32_MAX,UINT32_MAX,slot);
 wide cd=fibre_current_denominator(field,hi,rational?b+width:UINT32_MAX,UINT32_MAX,slot);
 if(*slot)return;wide den=fibre_lcm(pd,cd,slot);wide *values=(wide*)workspace+(size_t)row*w;
 for(uint32_t j=0;j<width;++j){
   if(field[a+j]!=hi[a+j]||field[b+j]!=hi[b+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
   values[width+j]=product_checked(field[b+j],den/cd,slot);
   values[2u*width+j]=product_checked(field[a+j],den/pd,slot);
   values[j]=sub_checked(values[width+j],values[2u*width+j],slot);
 }
 if(*slot)return;fibre_normalize(values,w,&den,slot);to_word(den,slot);
 for(uint32_t j=0;j<w;++j)to_word(values[j],slot);if(*slot)return;
 for(uint32_t j=0;j<w;++j)out[(size_t)row*(w+1u)+j]=out_hi[(size_t)row*(w+1u)+j]=(int64_t)values[j];
 out[(size_t)row*(w+1u)+w]=out_hi[(size_t)row*(w+1u)+w]=(int64_t)den;
}

// A checked total source graph maps every affine generator independently. This is the
// same exact image as general relation elimination, without solving a new joining system.
extern "C" __global__ void section_wave_source_image_rows(
 const int64_t *basis,const int64_t *basis_hi,const int64_t *family,const int64_t *family_hi,
 uint32_t ps,uint32_t q,uint32_t validate_only,int64_t *admitted,int64_t *admitted_hi,int64_t *mapped,int64_t *mapped_hi,int64_t *out,int64_t *out_hi,int64_t *workspace,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 uint32_t row=blockIdx.x*blockDim.x+threadIdx.x;if(row>q||(validate_only&&row))return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t k=2u*q,pk=ps+q,ok=3u*q;
 if(family[pk]<=0||family[pk+1u]<0||family[pk+1u]>2){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(validate_only){
   for(size_t i=0;i<(size_t)k*k;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
   for(size_t i=0;i<(size_t)pk+4u+(size_t)q*q;++i)if(family[i]!=family_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
   for(uint32_t i=0;i<k;++i){
     if(i<q&&basis[(size_t)i*k+i]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
     for(uint32_t j=0;j<(i<q?i:k);++j)if(basis[(size_t)i*k+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
   }
   for(uint32_t i=0;i<ok+4u;++i)out[i]=out_hi[i]=0;
   out[ok]=out_hi[ok]=1;out[ok+1u]=out_hi[ok+1u]=family[pk+1u]==1?1:0;
   out[ok+2u]=out_hi[ok+2u]=-1;
   admitted[0]=admitted_hi[0]=1;return;
 }
 if(family[pk+1u]==1){if(row)for(uint32_t i=0;i<q;++i)mapped[(size_t)(row-1u)*q+i]=mapped_hi[(size_t)(row-1u)*q+i]=0;return;}
 wide *query=(wide*)workspace+(size_t)row*k,den=row?1:family[pk];
 for(uint32_t i=0;i<k;++i)query[i]=i<q?(row?family[pk+4u+(size_t)(row-1u)*q+i]:family[ps+i]):0;
 uint32_t status=0,rank=0;
 fibre_query(basis,q,k,query,&den,nullptr,-1,&status,&rank,slot);if(*slot)return;
 if(status!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<q;++i)query[q+i]=sub_checked(0,query[q+i],slot);
 // Directions may be rescaled: retain their complete rational span, not a parameter scale.
 fibre_normalize(query+q,q,row?nullptr:&den,slot);if(!row)to_word(den,slot);
 for(uint32_t i=0;i<q;++i)to_word(query[q+i],slot);if(*slot)return;
 if(row){for(uint32_t i=0;i<q;++i)mapped[(size_t)(row-1u)*q+i]=mapped_hi[(size_t)(row-1u)*q+i]=(int64_t)query[q+i];}
 else{for(uint32_t i=0;i<q;++i)out[k+i]=out_hi[k+i]=(int64_t)query[q+i];out[ok]=out_hi[ok]=(int64_t)den;}
}
extern "C" __global__ void section_wave_source_image_finish(
 const int64_t *mapped,const int64_t *mapped_hi,uint32_t q,int64_t *basis,int64_t *basis_hi,
 int64_t *out,int64_t *out_hi,int64_t *coverage,int64_t *coverage_hi,int64_t *workspace,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t ok=3u*q;wide *row=(wide*)workspace;
 for(size_t i=0;i<(size_t)q*q;++i){if(mapped[i]!=mapped_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}basis[i]=basis_hi[i]=0;}
 for(uint32_t i=0;i<4u+3u*q;++i)coverage[i]=coverage_hi[i]=0;
 coverage[1]=coverage_hi[1]=-1;coverage[2]=coverage_hi[2]=coverage[3u+q]=coverage_hi[3u+q]=1;
 if(out[ok+1u]!=1)for(uint32_t p=0;p<q;++p){
   for(uint32_t j=0;j<q;++j)row[j]=mapped[(size_t)p*q+j];
   condition_stage_row(basis,basis_hi,q,row,slot);if(*slot)return;
 }
 uint32_t rank=0;for(uint32_t p=0;p<q;++p)if(basis[(size_t)p*q+p])++rank;
 if(out[ok+1u]==1)coverage[0]=coverage_hi[0]=3;
 else out[ok+1u]=out_hi[ok+1u]=rank?2:0;
 out[ok+3u]=out_hi[ok+3u]=rank;
 for(size_t i=0;i<(size_t)q*q;++i)out[ok+4u+i]=out_hi[ok+4u+i]=basis[i];
}
