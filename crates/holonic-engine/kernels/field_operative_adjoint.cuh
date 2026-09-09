// Recover a producing prefix by undoing later journaled numerical increments exactly.
// Each increment is rounded by the same operation that installed it; no inverse of a
// semantic quotient is asserted. The historical radius is retained by the Rust owner.
extern "C" __global__ void section_field_operative_producing_map(
    const int64_t *current,const int64_t *journal,uint32_t returns,uint32_t d,uint32_t k,uint32_t grain,
    int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!k){if(!blockIdx.x&&!threadIdx.x)for(uint32_t j=0;j<2u*d;++j)lo[j]=hi[j]=0;return;}
    size_t row=blockIdx.x*blockDim.x+threadIdx.x;if(row>=(size_t)k*(d/2u))return;
    uint32_t contact=row/(d/2u),j=2u*(row%(d/2u));
    wide re=((const wide *)current)[(size_t)contact*d+j],im=((const wide *)current)[(size_t)contact*d+j+1];
    for(uint32_t a=returns;a>0;--a){
        const int64_t *entry=journal+3u*(size_t)(a-1u);uint32_t count=(uint32_t)entry[2];if(contact>=count)continue;
        const wide *p=(const wide *)(uintptr_t)entry[0],*r=(const wide *)(uintptr_t)entry[1];
        HistoryInteger dr,di;wide omitted=0;
        for(uint32_t f=0;f<2;++f)history_complex_add_product(dr,di,r[2u*((size_t)f*count+contact)],r[2u*((size_t)f*count+contact)+1],p[(size_t)f*d+j],p[(size_t)f*d+j+1],true);
        re=sub_checked(re,operative_grid(dr,grain,&omitted,slot),slot);im=sub_checked(im,operative_grid(di,grain,&omitted,slot),slot);
    }
    ((wide *)lo)[(size_t)contact*d+j]=re;((wide *)lo)[(size_t)contact*d+j+1]=im;
    if(!*slot)for(uint32_t a=0;a<4;++a)hi[2u*((size_t)contact*d+j)+a]=lo[2u*((size_t)contact*d+j)+a];
}
__device__ wide oa_mid(wide lo,wide hi,wide *error,uint32_t *slot){
    if(lo>hi){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    wide distance=sub_checked(hi,lo,slot),mid=add_checked(lo,distance/2,slot);
    *error=add_checked(*error,div_ceil(distance,2,slot),slot);return mid;
}
// Extend only along actual later births. The historical response has no fictitious
// covector on a contact that did not exist at its producing cut.
extern "C" __global__ void section_field_operative_extend_response(
    const int64_t *input,uint32_t old_count,uint32_t count,int64_t *lo,int64_t *hi,int64_t *db_lo,int64_t *db_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t j=blockIdx.x*blockDim.x+threadIdx.x;if(j>=8u*(count?count:1u))return;
    uint32_t factor=j/(4u*(count?count:1u)),within=j%(4u*(count?count:1u));
    lo[j]=hi[j]=within<4u*old_count?input[4u*old_count*factor+within]:0;
    if(j<4u*(count?count:1u))db_lo[j]=db_hi[j]=0;
}
// Exact original paired producer: lambda=(I+DD*)^-1(go+D gb),
// G_D=lambda (D*v-2bplus)* + v(gb-D*lambda)*. Only D is free in the
// constrained contact response; all incoming-current reactions are still returned below.
extern "C" __global__ __launch_bounds__(512) void section_field_operative_material_adjoint(
    const int64_t *map_wire,const int64_t *b_wire,const int64_t *bounds_wire,const int64_t *cov_wire,
    const int64_t *moment_bounds,const int64_t *forward_wire,const int64_t *query_wire,
    uint32_t n,uint32_t k,uint32_t grain,
    int64_t *ports_lo,int64_t *ports_hi,int64_t *currents_lo,int64_t *currents_hi,
    int64_t *db_lo,int64_t *db_hi,int64_t *de_lo,int64_t *de_hi,int64_t *out_lo,int64_t *out_hi,
    wide *workspace,int64_t *dots,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=6u*n,m=d/2u;const wide S=(wide)1<<grain;
    const wide *D=(const wide *)map_wire,*b=(const wide *)b_wire,*e=(const wide *)bounds_wire,
        *C=(const wide *)cov_wire,*mb=(const wide *)moment_bounds,*v=(const wide *)forward_wire,*query=(const wide *)query_wire;
    wide *p=(wide *)ports_lo,*f=(wide *)currents_lo,*out=(wide *)out_lo,*ex=out+2u*d+4u*k;
    wide *matrix=workspace,*diagonal=matrix+(size_t)d*d,*rhs=diagonal+d,*go=rhs+d,*gb=go+d,
        *rounds=gb+2u*k; // 2k dot rounding counters, then scalar scratch.
    if(threadIdx.x==0){
        for(uint32_t j=0;j<8;++j)ex[j]=0;
        if(!n||grain<1||grain>120||e[0]<0||e[1]<0||v[d]<0||mb[2]<0)atomicOr(slot,REFUSED_MALFORMED);
        wide eo=0,eb=0;
        for(uint32_t j=0;j<d;++j)go[j]=oa_mid(query[2u*(4u*n+j)],query[2u*(4u*n+j)+1u],&eo,slot);
        for(uint32_t j=0;j<2u*k;++j)gb[j]=oa_mid(query[2u*(10u*n+j)],query[2u*(10u*n+j)+1u],&eb,slot);
        rounds[2u*k]=eo;rounds[2u*k+1u]=eb;
        for(uint32_t j=0;j<2u*k;++j)((wide *)db_lo)[j]=0;
        ((wide *)de_lo)[0]=((wide *)de_lo)[1]=0;
        if(!k){((wide *)db_lo)[0]=((wide *)db_lo)[1]=0;for(uint32_t j=0;j<4;++j)f[j]=0;}
    }
    __syncthreads();if(*slot)return;
    for(size_t ij=threadIdx.x;ij<(size_t)d*d;ij+=blockDim.x){
        uint32_t i=ij/d,j=ij%d;size_t a=2u*((size_t)(i/2u)*m+j/2u);
        wide value=((i&1u)==(j&1u))?C[a]:((i&1u)?C[a+1u]:sub_checked(0,C[a+1u],slot));
        matrix[ij]=i==j?add_checked(value,S,slot):value;
    }
    for(uint32_t i=threadIdx.x;i<m;i+=blockDim.x){
        HistoryInteger re,im;wide unused=0;
        for(uint32_t row=0;row<k;++row)history_complex_add_product(re,im,D[(size_t)row*d+2u*i],D[(size_t)row*d+2u*i+1u],gb[2u*row],gb[2u*row+1u],false);
        rhs[2u*i]=add_checked(go[2u*i],operative_grid(re,grain,&unused,slot),slot);
        rhs[2u*i+1u]=add_checked(go[2u*i+1u],operative_grid(im,grain,&unused,slot),slot);
    }
    __syncthreads();if(*slot)return;
    field_enclosed_factor(matrix,diagonal,d,grain,slot);if(*slot)return;
    if(threadIdx.x==0&&! *slot)field_enclosed_solve(matrix,diagonal,d,grain,rhs,p,slot);
    __syncthreads();if(*slot)return;
    for(uint32_t row=threadIdx.x;row<k;row+=blockDim.x){
        HistoryInteger lr,li,vr,vi;wide el=0,ev=0;
        for(uint32_t j=0;j<d;j+=2u){
            history_complex_add_product(lr,li,D[(size_t)row*d+j],D[(size_t)row*d+j+1u],p[j],p[j+1u],true);
            history_complex_add_product(vr,vi,D[(size_t)row*d+j],D[(size_t)row*d+j+1u],v[j],v[j+1u],true);
        }
        history_write_integer(lr,dots+10u*(size_t)row,dots+10u*(size_t)row,slot);
        history_write_integer(li,dots+10u*(size_t)row+5u,dots+10u*(size_t)row+5u,slot);
        wide ar=operative_grid(lr,grain,&el,slot),ai=operative_grid(li,grain,&el,slot);
        f[2u*row]=sub_checked(operative_grid(vr,grain,&ev,slot),product_checked(2,b[2u*row],slot),slot);
        f[2u*row+1u]=sub_checked(operative_grid(vi,grain,&ev,slot),product_checked(2,b[2u*row+1u],slot),slot);
        f[2u*(k+row)]=sub_checked(gb[2u*row],ar,slot);f[2u*(k+row)+1u]=sub_checked(gb[2u*row+1u],ai,slot);
        out[d+2u*row]=sub_checked(product_checked(2,ar,slot),gb[2u*row],slot);
        out[d+2u*row+1u]=sub_checked(product_checked(2,ai,slot),gb[2u*row+1u],slot);
        rounds[2u*row]=el;rounds[2u*row+1u]=ev;
    }
    __syncthreads();if(*slot)return;
    // Certify the complete skew-adjoint block B=[I,-D;D*,I], z=(lambda,ell).
    // B*B>=I and 2B^-1-I is unitary. Splitting these rows into independent D-amplified
    // bounds destroys that contraction. Keep both oriented residual rows here.
    for(uint32_t i=threadIdx.x;i<m;i+=blockDim.x){
        HistoryInteger re=history_integer(S)*history_integer(sub_checked(p[2u*i],go[2u*i],slot));
        HistoryInteger im=history_integer(S)*history_integer(sub_checked(p[2u*i+1u],go[2u*i+1u],slot));
        for(uint32_t row=0;row<k;++row){
            HistoryInteger dr,di;history_complex_add_product(dr,di,D[(size_t)row*d+2u*i],D[(size_t)row*d+2u*i+1u],f[2u*(k+row)],f[2u*(k+row)+1u],false);
            re=re-dr;im=im-di;
        }
        wide omitted=0;out[d+2u*k+2u*i]=operative_grid(re,grain,&omitted,slot);
        out[d+2u*k+2u*i+1u]=operative_grid(im,grain,&omitted,slot);rhs[i]=omitted;
    }
    for(uint32_t row=threadIdx.x;row<k;row+=blockDim.x){
        HistoryInteger re=history_read_integer(dots+10u*(size_t)row,slot)+history_integer(S)*history_integer(sub_checked(f[2u*(k+row)],gb[2u*row],slot));
        HistoryInteger im=history_read_integer(dots+10u*(size_t)row+5u,slot)+history_integer(S)*history_integer(sub_checked(f[2u*(k+row)+1u],gb[2u*row+1u],slot));
        wide omitted=0;out[2u*d+2u*k+2u*row]=operative_grid(re,grain,&omitted,slot);
        out[2u*d+2u*k+2u*row+1u]=operative_grid(im,grain,&omitted,slot);rounds[2u*row]=omitted;
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide eo=rounds[2u*k],eb=rounds[2u*k+1u],evq=0,er=0,nd=mb[2],ed=e[0];
        for(uint32_t i=0;i<k;++i){er=add_checked(er,rounds[2u*i],slot);evq=add_checked(evq,rounds[2u*i+1u],slot);}
        for(uint32_t i=0;i<m;++i)er=add_checked(er,rhs[i],slot);
        wide rn=add_checked(complete_norm(out+d+2u*k,d+2u*k,slot),er,slot),nl=complete_norm(p,d,slot),nv=complete_norm(v,d,slot);
        wide nk=complete_norm(f,2u*k,slot),nell=complete_norm(f+2u*k,2u*k,slot);
        wide nz=history_norm_ceiling(history_integer(nl)*history_integer(nl)+history_integer(nell)*history_integer(nell),slot);
        wide nw=history_norm_ceiling(history_integer(nv)*history_integer(nv)+history_integer(nk)*history_integer(nk),slot);
        wide ein=history_norm_ceiling(history_integer(eo)*history_integer(eo)+history_integer(eb)*history_integer(eb),slot);
        wide defect=add_checked(rn,ft_ceil_product(ed,nz,grain,slot),slot),ez=add_checked(ein,defect,slot);
        wide ev=v[d],ek=add_checked(evq,add_checked(ft_ceil_product(nd,ev,grain,slot),
            add_checked(ft_ceil_product(ed,add_checked(nv,ev,slot),grain,slot),product_checked(2,e[1],slot),slot),slot),slot);
        wide ew=history_norm_ceiling(history_integer(ev)*history_integer(ev)+history_integer(ek)*history_integer(ek),slot);
        wide eg=add_checked(ft_ceil_product(ez,add_checked(nw,ew,slot),grain,slot),ft_ceil_product(nz,ew,grain,slot),slot);
        wide reaction_error=add_checked(ein,product_checked(2,defect,slot),slot);
        ex[0]=ez;ex[1]=reaction_error;ex[2]=reaction_error;ex[3]=ek;ex[4]=ez;ex[5]=eg;ex[6]=rn;ex[7]=nd;
        ((wide *)de_lo)[0]=eg;
        for(uint32_t j=0;j<d;++j){p[d+j]=v[j];out[j]=sub_checked(product_checked(2,p[j],slot),go[j],slot);}
    }
    __syncthreads();if(*slot)return;
    operative_copy_point(ports_lo,ports_hi,4u*d);operative_copy_point(currents_lo,currents_hi,8u*(k?k:1u));
    operative_copy_point(db_lo,db_hi,4u*(k?k:1u));operative_copy_point(de_lo,de_hi,4);
    operative_copy_point(out_lo,out_hi,2u*(2u*d+4u*k+8u));
}
