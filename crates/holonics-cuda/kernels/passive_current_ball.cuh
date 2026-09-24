// The existing PassiveContact map, now over complete Euclidean current balls.
// F(x,y,q)=y+(I-2dd'/D)(q-x), d=x-y, D=|d|^2+||y|^2-|x|^2|.
// Every founding pair gives a non-expansive query map. Parameter uncertainty is retained.
// Source union uses F(x,y,x+q)=y+Aq with the SAME x, cancelling its shared occurrence symbolically.
__device__ wide passive_moment_ratio(MomentInteger numerator,const MomentInteger &denominator,
    bool ceiling,bool *rounded,uint32_t *slot){
    MomentInteger quotient=exact_divide_positive(numerator,denominator,rounded);
    if(quotient.overflow || (ceiling&&numerator.negative)){atomicOr(slot,REFUSED_CARRIER);return 0;}
    wide value=normal_grid(quotient,0,false,slot);
    return ceiling&&*rounded?add_checked(value,1,slot):value;
}
__device__ void passive_current_ball(const wide *x,const wide *y,const wide *q,wide *out,
    uint32_t width,uint32_t grain,bool source_union,uint32_t *slot){
    __shared__ int64_t shared_moments[2*MOMENT_WIRE_WORDS];
    __shared__ wide radius;
    __shared__ unsigned long long rounds;
    if(!threadIdx.x){
        rounds=0;MomentInteger dd,gap,dot;
        wide nx=0,ny=0,nd=0,nqx=0,rx=x[width],ry=y[width],rq=q[width];
        if(rx<0||ry<0||rq<0)atomicOr(slot,REFUSED_MALFORMED);
        for(uint32_t j=0;j<width&&! *slot;++j){
            wide d=sub_checked(x[j],y[j],slot),v=source_union?q[j]:sub_checked(q[j],x[j],slot);
            dd=dd+normal_wide(d)*normal_wide(d);
            gap=gap+normal_wide(y[j])*normal_wide(y[j])-normal_wide(x[j])*normal_wide(x[j]);
            dot=dot+normal_wide(d)*normal_wide(v);
            nx=add_checked(nx,ft_abs(x[j],slot),slot);ny=add_checked(ny,ft_abs(y[j],slot),slot);
            nd=add_checked(nd,ft_abs(d,slot),slot);nqx=add_checked(nqx,ft_abs(v,slot),slot);
        }
        MomentInteger denominator=dd+normal_abs(gap);
        wide h=add_checked(rx,ry,slot),S=(wide)1<<grain,L=0;
        if(h){
            MomentInteger eh=(MomentInteger(2)*normal_wide(nd)+normal_wide(h))*normal_wide(h);
            MomentInteger eg=(MomentInteger(2)*normal_wide(nx)+normal_wide(rx))*normal_wide(rx)
                +(MomentInteger(2)*normal_wide(ny)+normal_wide(ry))*normal_wide(ry);
            MomentInteger ed=eh+eg,lower=denominator-ed;
            L=product_checked(2,S,slot);
            if(!lower.negative&&!lower.is_zero()){
                MomentInteger numerator=MomentInteger(2)*normal_wide(S)*(eh+ed);
                // Compare before division, so an irrelevant larger ratio cannot overflow a word.
                if(numerator<normal_wide(L)*lower){bool rounded=false;L=passive_moment_ratio(numerator,lower,true,&rounded,slot);}
            }
            if(eh.overflow||eg.overflow||ed.overflow||lower.overflow)atomicOr(slot,REFUSED_CARRIER);
        }
        radius=add_checked(add_checked(rq,source_union?ry:h,slot),normal_grid(normal_wide(L)*normal_wide(nqx),grain,true,slot),slot);
        operative_write_moment(denominator,shared_moments,shared_moments,slot);
        operative_write_moment(dot,shared_moments+MOMENT_WIRE_WORDS,shared_moments+MOMENT_WIRE_WORDS,slot);
    }
    __syncthreads();if(*slot)return;
    const MomentInteger denominator=normal_read(shared_moments,slot),dot=normal_read(shared_moments+MOMENT_WIRE_WORDS,slot);
    for(uint32_t j=threadIdx.x;j<width;j+=blockDim.x){
        wide value=add_checked(q[j],source_union?y[j]:sub_checked(y[j],x[j],slot),slot);
        if(!denominator.is_zero()){
            wide d=sub_checked(x[j],y[j],slot);bool rounded=false;
            wide correction=passive_moment_ratio(MomentInteger(2)*normal_wide(d)*dot,denominator,false,&rounded,slot);
            value=sub_checked(value,correction,slot);
            if(rounded)atomicAdd(&rounds,1ull);
        }
        out[j]=value;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x)out[width]=add_checked(radius,(wide)rounds,slot);
    __syncthreads();
}
