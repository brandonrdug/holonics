// Accumulated complex normal material. H=I+sum xx*, B=sum yx*, C=sum |y|².
// Exact moment numerators use the common scale S²; the material matrix uses S.
// Four retained scalar moments are EH, EB, C and EC. No floating-point arithmetic.
// The paired source consists of the outgoing and held root branches and a target port.
// Report roles and wire words are separate charts even when their cardinalities coincide.
enum NormalSourcePort { NORMAL_OUTGOING_PORT, NORMAL_HELD_PORT, NORMAL_TARGET_PORT, NORMAL_SOURCE_PORT_COUNT };
enum NormalReportBall { NORMAL_FORWARD, NORMAL_SOURCE_FORWARD, NORMAL_OBSERVED,
    NORMAL_RETURNED_DIFFERENCE, NORMAL_CHRONOLOGY, NORMAL_CONTEMPORARY_DIFFERENCE, NORMAL_BALL_COUNT };
enum NormalStatistic { NORMAL_SOURCE_ERROR, NORMAL_CROSS_ERROR, NORMAL_TARGET_ENERGY,
    NORMAL_TARGET_ENERGY_ERROR, NORMAL_STATISTIC_COUNT };
enum NormalBound { NORMAL_COEFFICIENT_RADIUS, NORMAL_RESIDUAL_BOUND, NORMAL_COEFFICIENT_NORM,
    NORMAL_SOURCE_NORMAL_BOUND, NORMAL_CROSS_SOURCE_BOUND, NORMAL_BOUND_COUNT };
constexpr size_t NORMAL_MATRIX_BOUNDS = NORMAL_COEFFICIENT_NORM + 1;
constexpr size_t NORMAL_WIDE_WORDS = sizeof(wide) / sizeof(int64_t);
constexpr uint32_t NORMAL_QUADRATURES = 2; // real and imaginary components of one complex current
__device__ uint32_t normal_sources(uint32_t roots){return NORMAL_SOURCE_PORT_COUNT*roots;}
__device__ uint32_t normal_source_components(uint32_t roots){return NORMAL_QUADRATURES*normal_sources(roots);}
__device__ size_t normal_ball_stride(uint32_t targets);
__device__ size_t normal_source_at(uint32_t targets);
// Generic direct-material charts carry their actual complex source count.  Legacy
// field/wave charts continue to derive three ports per root through the wrappers above.
__device__ size_t normal_matrix_words_sources(uint32_t m,uint32_t t){return NORMAL_WIDE_WORDS*(NORMAL_QUADRATURES*(size_t)m*t+NORMAL_MATRIX_BOUNDS);}
__device__ size_t normal_stat_values_sources(uint32_t m,uint32_t t){return NORMAL_QUADRATURES*(size_t)m*(m+t)+NORMAL_STATISTIC_COUNT;}
__device__ size_t normal_state_words_sources(uint32_t m,uint32_t t){return normal_matrix_words_sources(m,t)+MOMENT_WIRE_WORDS*normal_stat_values_sources(m,t);}
__device__ size_t normal_metadata_at_sources(uint32_t m,uint32_t targets){return normal_source_at(targets)+NORMAL_QUADRATURES*m+1u;}
__device__ size_t normal_report_base_sources(uint32_t m,uint32_t t){return NORMAL_WIDE_WORDS*(normal_metadata_at_sources(m,t)+NORMAL_BOUND_COUNT);}
__device__ size_t normal_report_words_sources(uint32_t m,uint32_t t){return normal_report_base_sources(m,t)+NORMAL_STATISTIC_COUNT*MOMENT_WIRE_WORDS;}
__device__ size_t normal_ball_stride(uint32_t targets){return NORMAL_QUADRATURES*(size_t)targets+1;}
__device__ size_t normal_source_at(uint32_t targets){return NORMAL_BALL_COUNT*normal_ball_stride(targets);}
__device__ size_t normal_metadata_at(uint32_t roots,uint32_t targets){return normal_metadata_at_sources(normal_sources(roots),targets);}
__device__ size_t normal_matrix_words(uint32_t n,uint32_t t){return normal_matrix_words_sources(normal_sources(n),t);}
__device__ size_t normal_stat_values(uint32_t n,uint32_t t){return normal_stat_values_sources(normal_sources(n),t);}
__device__ size_t normal_state_words(uint32_t n,uint32_t t){return normal_state_words_sources(normal_sources(n),t);}
__device__ size_t normal_report_base(uint32_t n,uint32_t t){return normal_report_base_sources(normal_sources(n),t);}
__device__ size_t normal_report_words(uint32_t n,uint32_t t){return normal_report_words_sources(normal_sources(n),t);}
__device__ MomentInteger normal_read(const int64_t *p,uint32_t *slot){
    MomentInteger a;
    for(uint32_t j=0;j<MomentInteger::LIMBS;++j){if(p[j]<0 || (uint64_t)p[j]>UINT32_MAX)atomicOr(slot,REFUSED_MALFORMED);a.limb[j]=(uint32_t)p[j];}
    if(p[MomentInteger::LIMBS]!=0 && p[MomentInteger::LIMBS]!=1)atomicOr(slot,REFUSED_MALFORMED);
    if(p[MomentInteger::LIMBS] && a.is_zero())atomicOr(slot,REFUSED_MALFORMED);
    a.negative=p[MomentInteger::LIMBS]!=0;return a;
}
__device__ MomentInteger normal_wide(wide x){return moment_lift(history_integer(x));}
__device__ MomentInteger normal_abs(MomentInteger x){x.negative=false;return x;}
__device__ wide normal_grid(MomentInteger x,uint32_t shift,bool ceiling,uint32_t *slot){
    wide omitted=0,value=operative_moment_grid(x,shift,&omitted,slot);
    if(ceiling && x.negative){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    return ceiling?add_checked(value,omitted,slot):value;
}
// Diagnostic-only chart, never an operand of the normal law. Preserve the legacy
// nonnegative dyadic numerator when it fits. A negative code -e denotes 2^e/S;
// e>=127 distinguishes this outward bound from every valid signed-wide numerator.
// Exact EH/EB remain in the moment state; a narrow display must not refuse that state.
__device__ wide normal_diagnostic_upper(const MomentInteger &x,uint32_t grain,uint32_t *slot){
    if(x.negative||x.overflow){atomicOr(slot,REFUSED_CARRIER);return 0;}
    const wide maximum=(wide)(((uwide)1<<127)-1u);
    MomentInteger limit=normal_wide(maximum)*normal_wide((wide)1<<grain);
    if(x<=limit)return normal_grid(x,grain,true,slot);
    uint32_t bits=0,nonzero_limbs=0;bool single_bit=false;
    for(uint32_t j=0;j<MomentInteger::LIMBS;++j)if(x.limb[j]){
        bits=32u*j+32u-__clz(x.limb[j]);++nonzero_limbs;
        single_bit=(x.limb[j]&(x.limb[j]-1u))==0;
    }
    uint32_t exponent=bits-grain-(nonzero_limbs==1u&&single_bit?1u:0u);
    return -(wide)exponent;
}
__device__ void normal_product(MomentInteger &re,MomentInteger &im,
    const MomentInteger &ar,const MomentInteger &ai,const MomentInteger &br,const MomentInteger &bi,bool conjugate){
    if(conjugate){re=re+ar*br+ai*bi;im=im+ai*br-ar*bi;}
    else{re=re+ar*br-ai*bi;im=im+ar*bi+ai*br;}
}

// A rounded, strictly positive proposal is solved using the existing LDL owner. The
// residual is then evaluated against the EXACT H and B, not the proposal's normal system.
__device__ void normal_fit_sources(int64_t *state,uint32_t m,uint32_t targets,uint32_t grain,
    int64_t *workspace,wide *diagnostic,uint32_t *slot){
    uint32_t d=NORMAL_QUADRATURES*m;size_t matrices=(size_t)m*m,coefficients=(size_t)m*targets;
    wide *M=(wide *)state,*a=(wide *)workspace,*diag=a+(size_t)d*d,*rhs=diag+d;
    int64_t *row_residual=(int64_t *)(rhs+(size_t)d*targets);
    wide *row_norm=(wide *)(row_residual+MOMENT_WIRE_WORDS*targets);
    const int64_t *H=state+normal_matrix_words_sources(m,targets),*B=H+COMPLEX_MOMENT_WIRE_WORDS*matrices,*scalars=B+COMPLEX_MOMENT_WIRE_WORDS*coefficients;
    for(size_t ij=threadIdx.x;ij<(size_t)d*d;ij+=blockDim.x){
        uint32_t i=ij/d,j=ij%d;const int64_t *h=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)(i/2u)*m+j/2u);
        wide value=normal_grid(normal_read(h+((i&1u)==(j&1u)?0u:MOMENT_WIRE_WORDS),slot),grain,false,slot);
        if(!(i&1u) && (j&1u))value=sub_checked(0,value,slot);
        // Each real-block entry loses less than one grain unit. This diagonal majorant
        // makes the proposal positive; its difference from H is paid by the residual.
        a[ij]=i==j?add_checked(value,(wide)d,slot):value;
    }
    __syncthreads();if(*slot)return;
    // Compile the actual proposal into its coupled coordinate block and independent
    // diagonal remainder. All H/B statistics stay in their original chart, and the exact
    // WH-B residual below still certifies the COMPLETE normal problem. A later observation
    // can couple any of these coordinates; the decomposition is rebuilt for that successor.
    __shared__ uint32_t coupled_dimension;
    for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x){
        bool coupled=false;
        for(uint32_t j=0;j<d&&!coupled;++j)if(i!=j&&a[(size_t)i*d+j]!=0)coupled=true;
        diag[i]=coupled?1:0;
    }
    __syncthreads();
    if(!threadIdx.x){
        uint32_t count=0;
        // In-place compaction writes only flags already consumed by this traversal.
        for(uint32_t i=0;i<d;++i)if(diag[i])diag[count++]=(wide)i;
        coupled_dimension=count;
    }
    __syncthreads();
    const uint32_t f=coupled_dimension;
    // For f<d the unused square tail has at least f words. Its map survives factorization.
    wide *coordinate_map=f<d?a+(size_t)f*f:nullptr;
    if(f<d){
        for(uint32_t j=threadIdx.x;j<f;j+=blockDim.x)coordinate_map[j]=diag[j];
        __syncthreads();
        for(size_t ij=threadIdx.x;ij<(size_t)f*f;ij+=blockDim.x){
            uint32_t i=(uint32_t)coordinate_map[ij/f],j=(uint32_t)coordinate_map[ij%f];
            const int64_t *h=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)(i/2u)*m+j/2u);
            wide value=normal_grid(normal_read(h+((i&1u)==(j&1u)?0u:MOMENT_WIRE_WORDS),slot),grain,false,slot);
            if(!(i&1u)&&(j&1u))value=sub_checked(0,value,slot);
            // Use the ORIGINAL d majorant, so this is the same numerical proposal.
            a[ij]=i==j?add_checked(value,(wide)d,slot):value;
        }
        __syncthreads();if(*slot)return;
    }
    if(f)field_enclosed_factor(a,diag,f,grain,slot);
    __syncthreads();if(*slot)return;
    // Rows with the same complete B wire have the same exact solve and residual.  Keep the
    // representative index in row_norm while fitting; the existing row-norm slot is reused
    // after fitting, so this adds no workspace or state words.  Compare the entire moment wire,
    // including every signed moment carrier word, rather than a narrowed value.
    const size_t b_row_words=(size_t)m*COMPLEX_MOMENT_WIRE_WORDS;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        const int64_t *brow=B+(size_t)row*b_row_words;uint32_t representative=row;
        for(uint32_t prior=0;prior<row;++prior){
            const int64_t *candidate=B+(size_t)prior*b_row_words;bool same=true;
            for(size_t word=0;word<b_row_words;++word)if(brow[word]!=candidate[word]){same=false;break;}
            if(same){representative=prior;break;}
        }
        row_norm[row]=(wide)representative;
    }
    __syncthreads();
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        if((uint32_t)row_norm[row]!=row)continue;
        wide *r=rhs+(size_t)row*d,*out=M+(size_t)row*d;bool nonzero=false;
        for(uint32_t j=0;j<d;++j)out[j]=0;
        for(uint32_t j=0;j<f;++j){
            uint32_t original=f==d?j:(uint32_t)coordinate_map[j];
            MomentInteger b=normal_read(B+MOMENT_WIRE_WORDS*((size_t)row*d+original),slot);
            nonzero=nonzero||!b.is_zero();
            r[j]=normal_grid((original&1u)?-b:b,grain,false,slot);
        }
        if(nonzero&&f){
            field_enclosed_solve(a,diag,f,grain,r,out,slot);
            // Ordered indices satisfy map[j]>=j. Reverse scattering therefore preserves
            // every not-yet-consumed compressed coefficient without another matrix buffer.
            for(uint32_t j=f;j-->0;){
                uint32_t original=f==d?j:(uint32_t)coordinate_map[j];wide value=out[j];
                if(original!=j)out[j]=0;
                out[original]=(original&1u)?sub_checked(0,value,slot):value;
            }
        }
        if(f<d){
            uint32_t active=0;
            for(uint32_t j=0;j<d;++j){
                if(active<f&&(uint32_t)coordinate_map[active]==j){++active;continue;}
                MomentInteger b=normal_read(B+MOMENT_WIRE_WORDS*((size_t)row*d+j),slot);
                if(b.is_zero())continue;
                nonzero=true;
                const int64_t *h=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)(j/2u)*m+j/2u);
                wide isolated_diagonal=add_checked(normal_grid(normal_read(h,slot),grain,false,slot),(wide)d,slot);
                wide single_rhs=normal_grid((j&1u)?-b:b,grain,false,slot),solved=0;
                field_enclosed_solve(&isolated_diagonal,&isolated_diagonal,1,grain,&single_rhs,&solved,slot);
                out[j]=(j&1u)?sub_checked(0,solved,slot):solved;
            }
        }
        MomentInteger residual;wide norm=0;
        for(uint32_t j=0;j<d;++j)norm=add_checked(norm,ft_abs(out[j],slot),slot);
        uint32_t contributing=0;
        if(nonzero)for(uint32_t k=0;k<m;++k)if(out[2u*k]!=0||out[2u*k+1u]!=0)r[contributing++]=(wide)k;
        if(nonzero)for(uint32_t j=0;j<m;++j){
            MomentInteger re,im;
            for(uint32_t at=0;at<contributing;++at){uint32_t k=(uint32_t)r[at];const int64_t *h=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)k*m+j);
                normal_product(re,im,normal_wide(out[2u*k]),normal_wide(out[2u*k+1u]),normal_read(h,slot),normal_read(h+MOMENT_WIRE_WORDS,slot),false);}
            const int64_t *b=B+COMPLEX_MOMENT_WIRE_WORDS*((size_t)row*m+j);MomentInteger S=moment_lift(complete_power(grain,slot));
            re=re-S*normal_read(b,slot);im=im-S*normal_read(b+MOMENT_WIRE_WORDS,slot);
            residual=residual+normal_abs(re)+normal_abs(im);
        }
        operative_write_moment(residual,row_residual+MOMENT_WIRE_WORDS*row,row_residual+MOMENT_WIRE_WORDS*row,slot);
        // rhs is dead after the solve.  Preserve the representative norm there while row_norm
        // continues to carry the representative index for the duplicate-copy pass.
        rhs[(size_t)row*d]=norm;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        uint32_t representative=(uint32_t)row_norm[row];
        if(representative!=row){
            for(uint32_t j=0;j<d;++j)M[(size_t)row*d+j]=M[(size_t)representative*d+j];
            for(uint32_t j=0;j<MOMENT_WIRE_WORDS;++j)
                row_residual[MOMENT_WIRE_WORDS*(size_t)row+j]=row_residual[MOMENT_WIRE_WORDS*(size_t)representative+j];
        }
        row_norm[row]=rhs[(size_t)representative*d];
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        MomentInteger residual;wide norm=0;
        for(uint32_t row=0;row<targets;++row){residual=residual+normal_read(row_residual+MOMENT_WIRE_WORDS*row,slot);norm=add_checked(norm,row_norm[row],slot);}
        MomentInteger eh=normal_read(scalars,slot),eb=normal_read(scalars+MOMENT_WIRE_WORDS,slot),S=moment_lift(complete_power(grain,slot));
        if(eh.negative||eb.negative)atomicOr(slot,REFUSED_MALFORMED);
        MomentInteger bound=residual+normal_wide(norm)*eh+S*eb;
        // Pair P(I+sum f f*)=W0+sum y f* with P. Cauchy on (P,Pf) and (W0,y)
        // bounds the fitted energy, hence ||P||_F^2, by C=||W0||_F^2+Q_data.
        // AccumulatedNormalResponse proves this matrix-to-energy and Cauchy chain.
        // Therefore ||M-P|| <= ||M||_1+sqrt(C+EC),
        // independently of source conditioning. Keep the tighter of two valid bounds.
        // Reuse the exact integer norm owner for an outward square root. The energy
        // numerator is at S^2, so its root is already at S. Compare before narrowing:
        // an irrelevant unrepresentable cap must not refuse a smaller residual bound.
        MomentInteger energy=normal_read(scalars+NORMAL_TARGET_ENERGY*MOMENT_WIRE_WORDS,slot);
        MomentInteger energy_error=normal_read(scalars+NORMAL_TARGET_ENERGY_ERROR*MOMENT_WIRE_WORDS,slot);
        if(energy.negative||energy_error.negative)atomicOr(slot,REFUSED_MALFORMED);
        energy=energy+energy_error;
        const wide maximum=(wide)(((uwide)1<<127)-1u);
        MomentInteger root_limit=normal_wide(maximum)*normal_wide(maximum);
        if(!energy.overflow&&energy<=root_limit){
            HistoryInteger energy_square;
            for(uint32_t j=0;j<HistoryInteger::LIMBS;++j)energy_square.limb[j]=energy.limb[j];
            wide root=history_norm_ceiling(energy_square,slot);
            MomentInteger energy_bound=(normal_wide(norm)+normal_wide(root))*S*S;
            if(!energy_bound.overflow&&(bound.overflow||energy_bound<bound))bound=energy_bound;
        }
        M[2u*coefficients]=normal_grid(bound,2u*grain,true,slot);
        M[2u*coefficients+1u]=normal_grid(residual,2u*grain,true,slot);M[2u*coefficients+2u]=norm;
        if(diagnostic){diagnostic[0]=M[2u*coefficients];diagnostic[1]=normal_grid(residual,2u*grain,true,slot);diagnostic[2]=norm;
            diagnostic[3]=normal_diagnostic_upper(eh,grain,slot);diagnostic[4]=normal_diagnostic_upper(eb,grain,slot);}
    }
    __syncthreads();
}

__device__ void normal_fit(int64_t *state,uint32_t roots,uint32_t targets,uint32_t grain,
    int64_t *workspace,wide *diagnostic,uint32_t *slot){
    normal_fit_sources(state,normal_sources(roots),targets,grain,workspace,diagnostic,slot);
}

// Add/subtract an actual observation's exact sufficient-statistic increment.
__device__ void normal_increment_sources(int64_t *stats,const wide *x,const wide *y,const int64_t *errors,
    uint32_t m,uint32_t targets,bool subtract,uint32_t *slot){
    size_t hh=2u*m*m,bb=2u*m*targets;
    for(size_t at=threadIdx.x;at<hh+bb+NORMAL_STATISTIC_COUNT;at+=blockDim.x){
        MomentInteger value;
        if(at<hh){size_t i=(at/2u)/m,j=(at/2u)%m;if((!x[2u*i]&&!x[2u*i+1u])||(!x[2u*j]&&!x[2u*j+1u]))continue;MomentInteger re,im;
            normal_product(re,im,normal_wide(x[2u*i]),normal_wide(x[2u*i+1u]),normal_wide(x[2u*j]),normal_wide(x[2u*j+1u]),true);value=(at&1u)?im:re;
        }else if(at<hh+bb){size_t ij=(at-hh)/2u,i=ij/m,j=ij%m;if((!y[2u*i]&&!y[2u*i+1u])||(!x[2u*j]&&!x[2u*j+1u]))continue;MomentInteger re,im;
            normal_product(re,im,normal_wide(y[2u*i]),normal_wide(y[2u*i+1u]),normal_wide(x[2u*j]),normal_wide(x[2u*j+1u]),true);value=(at&1u)?im:re;
        }else value=normal_read(errors+MOMENT_WIRE_WORDS*(at-hh-bb),slot);
        if(value.overflow){atomicOr(slot,REFUSED_CARRIER);continue;}
        if(value.is_zero())continue;
        MomentInteger old=normal_read(stats+MOMENT_WIRE_WORDS*at,slot);value=subtract?old-value:old+value;
        operative_write_moment(value,stats+MOMENT_WIRE_WORDS*at,stats+MOMENT_WIRE_WORDS*at,slot);
    }
    __syncthreads();
}

__device__ void normal_increment(int64_t *stats,const wide *x,const wide *y,const int64_t *errors,
    uint32_t roots,uint32_t targets,bool subtract,uint32_t *slot){
    normal_increment_sources(stats,x,y,errors,normal_sources(roots),targets,subtract,slot);
}

// Refine only the numerical realization. Every exact moment and family bound retains
// its exact value; the same normal solver recomputes its proposal at the finer dyadic grain.
__device__ void normal_refine_execute(
    const int64_t *old,uint32_t source_complex,uint32_t targets,uint32_t old_grain,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *workspace,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!source_complex||!targets||grain<=old_grain||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
    size_t matrix_words=normal_matrix_words_sources(source_complex,targets),state_words=normal_state_words_sources(source_complex,targets);
    for(size_t i=threadIdx.x;i<matrix_words;i+=blockDim.x)next[i]=0;
    MomentInteger scale=moment_lift(complete_power(2u*(grain-old_grain),slot));
    for(size_t i=threadIdx.x;i<normal_stat_values_sources(source_complex,targets);i+=blockDim.x){
        MomentInteger value=normal_read(old+matrix_words+MOMENT_WIRE_WORDS*i,slot)*scale;
        operative_write_moment(value,next+matrix_words+MOMENT_WIRE_WORDS*i,next+matrix_words+MOMENT_WIRE_WORDS*i,slot);
    }
    __syncthreads();if(*slot)return;
    normal_fit_sources(next,source_complex,targets,grain,workspace,nullptr,slot);
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<state_words;i+=blockDim.x)next_hi[i]=next[i];
}

extern "C" __global__ __launch_bounds__(512) void section_normal_refine(
    const int64_t *old,uint32_t n,uint32_t targets,uint32_t old_grain,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *workspace,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    normal_refine_execute(old,normal_sources(n),targets,old_grain,grain,next,next_hi,workspace,slot,census,lineage,lineage_count);
}

extern "C" __global__ __launch_bounds__(512) void section_normal_refine_sources(
    const int64_t *old,uint32_t source_complex,uint32_t targets,uint32_t old_grain,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *workspace,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    normal_refine_execute(old,source_complex,targets,old_grain,grain,next,next_hi,workspace,slot,census,lineage,lineage_count);
}

// The source and target may be correlated members of a shared return. These bounds use
// the complete supplied radii and do not assume independence or select their centres.
__device__ void normal_observation_moments_sources(const wide *x,const wide *y,uint32_t m,uint32_t targets,
    int64_t *report,uint32_t *slot){
    uint32_t d=NORMAL_QUADRATURES*m,R=NORMAL_QUADRATURES*targets;
    wide ey=y[R];
            wide ex=x[d],nx=complete_norm(x,d,slot),ny=complete_norm(y,R,slot);
            if(ex<0||ey<0)atomicOr(slot,REFUSED_MALFORMED);
            MomentInteger eh=(MomentInteger(2)*normal_wide(nx)+normal_wide(ex))*normal_wide(ex);
            MomentInteger eb=normal_wide(ny)*normal_wide(ex)+normal_wide(nx)*normal_wide(ey)+normal_wide(ex)*normal_wide(ey),cy;
            for(uint32_t j=0;j<R;++j)cy=cy+normal_wide(y[j])*normal_wide(y[j]);
            MomentInteger ec=(MomentInteger(2)*normal_wide(ny)+normal_wide(ey))*normal_wide(ey);
            int64_t *e=report+normal_report_base_sources(m,targets);
            operative_write_moment(eh,e,e,slot);operative_write_moment(eb,e+MOMENT_WIRE_WORDS,e+MOMENT_WIRE_WORDS,slot);
            operative_write_moment(cy,e+NORMAL_TARGET_ENERGY*MOMENT_WIRE_WORDS,e+NORMAL_TARGET_ENERGY*MOMENT_WIRE_WORDS,slot);operative_write_moment(ec,e+NORMAL_TARGET_ENERGY_ERROR*MOMENT_WIRE_WORDS,e+NORMAL_TARGET_ENERGY_ERROR*MOMENT_WIRE_WORDS,slot);
}

__device__ void normal_observation_moments(const wide *x,const wide *y,uint32_t roots,uint32_t targets,
    int64_t *report,uint32_t *slot){
    normal_observation_moments_sources(x,y,normal_sources(roots),targets,report,slot);
}

// One observation's bounded source/target geometry, shared by field and direct section intake.
// Called by one thread; the enclosing passage supplies synchronization and publication.
__device__ void normal_observation_frame_sources_with_ball(const wide *origin_current,const int64_t *incoming,
    uint32_t m,uint32_t targets,uint32_t linked,uint32_t grain,uint32_t factor_width,uint32_t target_roots,
    int64_t *report,uint32_t *slot,const wide *target_ball){
    uint32_t d=NORMAL_QUADRATURES*m,R=NORMAL_QUADRATURES*targets;
    size_t stride=normal_ball_stride(targets),gain=normal_source_at(targets);
    wide *out=(wide *)report;wide S=(wide)1<<grain;
        wide *y=out+NORMAL_OBSERVED*stride,ey=0;
        if(!*slot && factor_width){ if(!target_roots)atomicOr(slot,REFUSED_MALFORMED); else contextual_tensor_target(incoming,target_roots,factor_width,targets,grain,y,&ey,slot); }
        else if(!*slot&&target_ball){
            for(uint32_t j=0;j<R;++j)y[j]=target_ball[j];
            ey=target_ball[R];if(ey<0)atomicOr(slot,REFUSED_MALFORMED);
        }
        else if(!*slot)for(uint32_t j=0;j<R;++j){const int64_t *v=incoming+3u*(j/2u);if(v[2]<=0){atomicOr(slot,REFUSED_MALFORMED);break;}
            wide lo=signed_product_divide_2(v[j%2u],S/2,v[2],0,slot),hi=signed_product_divide_2(v[j%2u],S/2,v[2],1,slot);y[j]=v[j%2u]<0?hi:lo;if(lo!=hi)ey=add_checked(ey,1,slot);}
        y[R]=ey;
        if(linked&&! *slot){
            const wide *x=origin_current+d+1u;for(uint32_t j=0;j<=d;++j)out[gain+j]=x[j];
            normal_observation_moments_sources(x,y,m,targets,report,slot);
        }
}

__device__ void normal_observation_frame(const wide *origin_current,const int64_t *incoming,
    uint32_t roots,uint32_t targets,uint32_t linked,uint32_t grain,uint32_t factor_width,
    int64_t *report,uint32_t *slot){
    normal_observation_frame_sources_with_ball(origin_current,incoming,normal_sources(roots),targets,linked,grain,factor_width,roots,report,slot,0);
}

__device__ void field_normal_material_prepare_sources_with_ball(const int64_t *old,const wide *origin_current,const wide *origin_forward,
    const wide *current,const int64_t *incoming,uint32_t m,uint32_t linked,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,int64_t *workspace,
    uint32_t targets,uint32_t factor_width,uint32_t target_roots,const wide *target_ball,uint32_t *slot){
    uint32_t d=NORMAL_QUADRATURES*m,R=NORMAL_QUADRATURES*targets;size_t stride=normal_ball_stride(targets),gain=normal_source_at(targets),extra=normal_metadata_at_sources(m,targets);
    size_t state_words=normal_state_words_sources(m,targets),report_words=normal_report_words_sources(m,targets);
    wide *out=(wide *)report;const wide *M=(const wide *)old;wide S=(wide)1<<grain;
    for(size_t i=threadIdx.x;i<state_words;i+=blockDim.x)next[i]=old[i];
    for(size_t i=threadIdx.x;i<report_words;i+=blockDim.x)report[i]=report_hi[i]=0;
    __syncthreads();
    if(!threadIdx.x){
        if(!m||!targets||!workspace||grain<1||grain>120||linked>1||(linked&&(!origin_current||!origin_forward)))atomicOr(slot,REFUSED_MALFORMED);
        normal_observation_frame_sources_with_ball(origin_current,incoming,m,targets,linked,grain,factor_width,target_roots,report,slot,target_ball);
    }
    __syncthreads();if(*slot)return;
    if(linked){normal_increment_sources(next+normal_matrix_words_sources(m,targets),out+gain,out+NORMAL_OBSERVED*stride,report+normal_report_base_sources(m,targets),m,targets,false,slot);
        if(*slot)return;normal_fit_sources(next,m,targets,grain,workspace,out+extra,slot);}
    __syncthreads();if(*slot)return;
    // Prediction rows are independent; preserve the existing ordered complex products.
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide oldnorm=0,newnorm=0;for(uint32_t j=0;j<d;++j){oldnorm=add_checked(oldnorm,ft_abs(M[(size_t)row*d+j],slot),slot);newnorm=add_checked(newnorm,ft_abs(((wide *)next)[(size_t)row*d+j],slot),slot);}
        // Row scratch is separate from the eventual output and exact normal-fit residual.
        wide *scratch=(wide *)workspace;
        scratch[4u*row]=oldnorm;scratch[4u*row+1u]=newnorm;
        scratch[4u*row+2u]=linked?linear_material_row(M,nullptr,origin_current+d+1u,row,m,grain,out+stride,slot):0;
        scratch[4u*row+3u]=linear_material_row((wide *)next,nullptr,current+d+1u,row,m,grain,out,slot);
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide oldnorm=0,newnorm=0,ro=0,rn=0;wide *scratch=(wide *)workspace;
        for(uint32_t row=0;row<targets;++row){oldnorm=add_checked(oldnorm,scratch[4u*row],slot);newnorm=add_checked(newnorm,scratch[4u*row+1u],slot);ro=add_checked(ro,scratch[4u*row+2u],slot);rn=add_checked(rn,scratch[4u*row+3u],slot);}
        wide error=((wide *)next)[(size_t)R*m];
        out[R]=ft_prediction_error(error,newnorm,current+d+1u,d,current[2u*(d+1u)-1u],rn,grain,slot);
        if(linked){
            wide pe=ft_prediction_error(M[(size_t)R*m],oldnorm,origin_current+d+1u,d,origin_current[2u*(d+1u)-1u],ro,grain,slot);out[2u*stride-1u]=pe;
            for(uint32_t j=0;j<R;++j){out[3u*stride+j]=sub_checked(out[2u*stride+j],origin_forward[j],slot);out[4u*stride+j]=sub_checked(out[stride+j],origin_forward[j],slot);out[5u*stride+j]=sub_checked(out[2u*stride+j],out[stride+j],slot);}
            out[4u*stride-1u]=add_checked(out[3u*stride-1u],origin_forward[R],slot);out[5u*stride-1u]=add_checked(pe,origin_forward[R],slot);out[6u*stride-1u]=add_checked(out[3u*stride-1u],pe,slot);
        }else{out[extra]=error;out[extra+1u]=M[(size_t)R*m+1u];out[extra+2u]=newnorm;const int64_t *e=next+normal_state_words_sources(m,targets)-NORMAL_STATISTIC_COUNT*MOMENT_WIRE_WORDS;out[extra+3u]=normal_grid(normal_read(e,slot),grain,true,slot);out[extra+4u]=normal_grid(normal_read(e+MOMENT_WIRE_WORDS,slot),grain,true,slot);}
    }
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<state_words;i+=blockDim.x)next_hi[i]=next[i];
    for(size_t i=threadIdx.x;i<report_words;i+=blockDim.x)report_hi[i]=report[i];
}

__device__ void field_normal_material_prepare(const int64_t *old,const wide *origin_current,const wide *origin_forward,
    const wide *current,const int64_t *incoming,uint32_t roots,uint32_t linked,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,int64_t *workspace,
    uint32_t targets,uint32_t factor_width,uint32_t *slot){
    field_normal_material_prepare_sources_with_ball(old,origin_current,origin_forward,current,incoming,
        normal_sources(roots),linked,grain,next,next_hi,report,report_hi,workspace,targets,factor_width,roots,0,slot);
}

__device__ void normal_observation_frame_sources(const wide *origin_current,const int64_t *incoming,
    uint32_t m,uint32_t targets,uint32_t linked,uint32_t grain,uint32_t factor_width,uint32_t target_roots,
    int64_t *report,uint32_t *slot){
    normal_observation_frame_sources_with_ball(origin_current,incoming,m,targets,linked,grain,factor_width,target_roots,report,slot,0);
}

__device__ void field_normal_material_prepare_sources(const int64_t *old,const wide *origin_current,const wide *origin_forward,
    const wide *current,const int64_t *incoming,uint32_t m,uint32_t linked,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,int64_t *workspace,
    uint32_t targets,uint32_t factor_width,uint32_t target_roots,uint32_t *slot){
    field_normal_material_prepare_sources_with_ball(old,origin_current,origin_forward,current,incoming,m,linked,grain,
        next,next_hi,report,report_hi,workspace,targets,factor_width,target_roots,0,slot);
}

// Decode an older normal operator by subtracting exactly the later observed increments.
extern "C" __global__ __launch_bounds__(512) void section_field_normal_material_prefix(
    const int64_t *current,const int64_t *journal,uint32_t later,uint32_t n,uint32_t targets,uint32_t grain,
    int64_t *out,int64_t *hi,int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    size_t words=normal_state_words(n,targets);
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out[j]=current[j];
    __syncthreads();
    for(uint32_t j=later;j>0;--j)if(journal[2u*(j-1u)+1u]){
        const int64_t *r=(const int64_t *)(uintptr_t)journal[2u*(j-1u)];const wide *v=(const wide *)r;size_t stride=normal_ball_stride(targets);
        normal_increment(out+normal_matrix_words(n,targets),v+normal_source_at(targets),v+NORMAL_OBSERVED*stride,r+normal_report_base(n,targets),n,targets,true,slot);if(*slot)return;
    }
    normal_fit(out,n,targets,grain,workspace,nullptr,slot);if(*slot)return;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)hi[j]=out[j];
}
