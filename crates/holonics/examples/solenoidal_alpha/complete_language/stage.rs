//! Pinned exterior continuation of the existing native training loop. No new learner.
use super::*;
use std::collections::BTreeSet;

pub(super) const COMMAND: &str = "stage-adaptive-family-local-arrival-held-v1";
const MANIFEST: &str = "complete-language-stage-v1";
const RECEIPT: &str = "complete-language-stage-complete-v1";

fn table(bytes: &[u8], header: &str) -> Result<BTreeMap<String,String>> {
    let text=std::str::from_utf8(bytes)?;
    let mut lines=text.lines();
    if lines.next()!=Some(header) || !text.ends_with('\n') {return Err("versioned stage table".into());}
    let mut out=BTreeMap::new();
    for l in lines {
        let (k,v)=l.split_once('\t').ok_or("stage table key/value")?;
        if k.is_empty() || v.is_empty() || v.contains('\t') || out.insert(k.to_owned(),v.to_owned()).is_some() {return Err("unique nonempty stage table keys/values".into());}
    }
    Ok(out)
}
fn word<'a>(m:&'a BTreeMap<String,String>,k:&str)->Result<&'a str>{Ok(m.get(k).ok_or("missing stage field")?)}
fn number(m:&BTreeMap<String,String>,k:&str)->Result<usize>{let s=word(m,k)?;let n:usize=s.parse()?;if n.to_string()!=s{return Err("canonical stage counter".into());}Ok(n)}
fn emit(header:&str,fields:&[(&str,String)])->Result<Vec<u8>> {
    let mut s=format!("{header}\n");
    for(k,v)in fields {if v.contains(['\t','\n','\r']){return Err("single-line stage field".into());}s+=&format!("{k}\t{v}\n");}
    Ok(s.into_bytes())
}
fn write_durable(path:&Path,bytes:&[u8])->Result<()> {write_new(path,bytes)?;std::fs::File::open(path.parent().ok_or("stage parent directory")?)?.sync_all()?;Ok(())}
fn executable_digest()->Result<String>{
    let p=std::env::current_exe()?;if std::fs::metadata(&p)?.len()>READ_BUDGET{return Err("stage executable read budget".into());}sha256(&std::fs::read(p)?)
}

pub(super) struct Stage {
    pub(super) checkpoint: Option<Checkpoint>,
    pub(super) accepted: usize,
    pub(super) epoch_start: usize,
    snapshots:BTreeSet<usize>,
    stop_at:usize,
    cooperative_ns:u64,
    id:String,
    source:String,
    source_bytes:usize,
    manifest_sha:String,
    source_identity:String,
    binary_sha:String,
    parent_sha:String,
    provenance_line:String,
    framing:String,
    source_order_sha:String,
}
impl Stage {
    /// Authenticate every parent/source/cursor binding before output creation or ingress.
    pub(super) fn open(args:&[String],data:&[u8],cells:&[usize],backend:&str,scope:ObservedEpochDepositionScope)->Result<Self>{
        if args.len()!=12 || args[0]!=COMMAND {return Err("stage BACKEND CORPUS SHA CUTS CUTSHA HORIZON CELLS EPOCHS OUT MANIFEST SHA".into());}
        let m=table(&pinned_read(&args[10],&args[11],1<<20)?,MANIFEST)?;
        let keys=["stage_id","mode","global_accepted","next_unread","parent_checkpoint","parent_checkpoint_sha256","parent_receipt","parent_receipt_sha256","previous_source","previous_source_sha256","source_sha256","source_bytes","stop_accepted","cooperative_stop_ns","hard_training_guard_ns","snapshot_offsets","native_source_identity","execution_binary_sha256","source_framing","source_order_manifest","source_order_manifest_sha256"];
        if m.len()!=keys.len() || keys.iter().any(|k|!m.contains_key(*k)){return Err("exact stage manifest fields".into());}
        pinned_read(word(&m,"source_order_manifest")?,word(&m,"source_order_manifest_sha256")?,1<<20)?;
        let framing=word(&m,"source_framing")?.to_owned();
        let source_order_sha=word(&m,"source_order_manifest_sha256")?.to_owned();
        let id=word(&m,"stage_id")?.to_owned();
        if id.is_empty()||id.len()>64||!id.bytes().all(|b|b.is_ascii_alphanumeric()||b==b'-'){return Err("bounded stage identity".into());}
        if word(&m,"source_sha256")?!=args[3] || number(&m,"source_bytes")?!=data.len(){return Err("stage full source identity".into());}
        let accepted=number(&m,"global_accepted")?;
        if accepted!=number(&m,"next_unread")? || accepted>=cells.len(){return Err("stage global unread cursor before incomplete source end".into());}
        let stop_at=if word(&m,"stop_accepted")?=="-"{cells.len()}else{number(&m,"stop_accepted")?};
        if stop_at<=accepted || stop_at>cells.len(){return Err("stage accepted stop belongs to this unread source".into());}
        let cooperative_ns:u64=word(&m,"cooperative_stop_ns")?.parse()?;
        let hard:u64=word(&m,"hard_training_guard_ns")?.parse()?;
        if cooperative_ns>=hard || hard>1_500_000_000_000{return Err("cooperative stop precedes separately enforced <=1500s hard training guard".into());}
        let mut snapshots=BTreeSet::new();
        if word(&m,"snapshot_offsets")?!="-" {
            let mut prior=None;
            for token in word(&m,"snapshot_offsets")?.split(',') {
                let n:usize=token.parse()?;
                if n.to_string()!=token || n<accepted || n>cells.len() || prior.is_some_and(|p|p>=n){return Err("sorted distinct global snapshot offsets".into());}
                snapshots.insert(n);prior=Some(n);
            }
        }
        let binary_sha=executable_digest()?;
        if word(&m,"execution_binary_sha256")?!=binary_sha{return Err("stage execution binary identity".into());}
        let source_identity=word(&m,"native_source_identity")?.to_owned();
        if source_identity.len()>128{return Err("bounded native source identity".into());}
        let mode=word(&m,"mode")?;
        let (checkpoint,epoch_start,parent_sha)=match mode {
            "fresh"=>{
                if accepted!=0 || ["parent_checkpoint","parent_checkpoint_sha256","parent_receipt","parent_receipt_sha256","previous_source","previous_source_sha256"].iter().any(|k|word(&m,k).ok()!=Some("-")){return Err("fresh stage has no parent or accepted history".into());}
                (None,0,"-".to_owned())
            },
            "resume"=>{
                let parent_sha=word(&m,"parent_checkpoint_sha256")?.to_owned();
                pinned_read(word(&m,"parent_checkpoint")?,&parent_sha,READ_BUDGET as usize)?;
                let (cp,hash)=Checkpoint::load(word(&m,"parent_checkpoint")?,READ_BUDGET)?;
                if hash!=parent_sha{return Err("pinned stage parent checkpoint".into());}
                let receipt=table(&pinned_read(word(&m,"parent_receipt")?,word(&m,"parent_receipt_sha256")?,1<<20)?,RECEIPT)?;
                for(k,expected)in [("checkpoint_sha256",parent_sha.as_str()),("backend",backend),("native_source_identity",source_identity.as_str()),("execution_binary_sha256",binary_sha.as_str()),("training_complete","false"),("source_framing",framing.as_str())] {
                    if word(&receipt,k)?!=expected{return Err("clean parent stage identity/closure".into());}
                }
                let previous=pinned_read(word(&m,"previous_source")?,word(&m,"previous_source_sha256")?,1<<20)?;
                if word(&receipt,"source_sha256")?!=word(&m,"previous_source_sha256")? || number(&receipt,"source_bytes")?!=previous.len()
                    || !data.starts_with(&previous) || previous.len().checked_mul(4).ok_or("prefix extent")?<accepted{return Err("whole admitted source prefix/framing identity".into());}
                let expected_line=format!("durable-stage-v1 source={} stage={} manifest={}",word(&receipt,"source_sha256")?,word(&receipt,"stage_id")?,word(&receipt,"stage_manifest_sha256")?);
                if word(&receipt,"provenance_line")?!=expected_line{return Err("parent belongs to a clean durable stage, not an abandoned run".into());}
                let prepared=cp.stream.resident().prepared_input().ok_or("stage prepared input owner")?;
                let published=total(cp.stream.resident())?;
                if prepared.mode()!=holonics::hnn::reference::prepared_input::PrefixMode::Training
                    || prepared.frontiers()!=(published as u64,0,0) || !prepared.outstanding().is_empty() {
                    return Err("training resumes actual input only, never generated/conditioning hypotheses".into());
                }
                if cp.population!=args[6].parse()? || cp.stream.scope()!=scope || !cp.adaptive_receiving() || !cp.source_framed()
                    || cp.stream.resident().receiving_law()!=holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1
                    || cp.stream.accepted_cells()?!=accepted as u64 || published.checked_add(cp.stream.pending_classes().len())!=Some(accepted)
                    || published%10!=0 || number(&receipt,"accepted")?!=accepted || number(&receipt,"published")?!=published
                    || number(&receipt,"pending")?!=cp.stream.pending_classes().len() || number(&receipt,"next_unread")?!=accepted
                    || number(&receipt,"global_epochs")?!=published/10
                    || word(&receipt,"horizon")?!=args[6]
                    || cp.stream.pending_classes()!=&cells[published..accepted]
                    || cp.provenance.lines().last()!=Some(word(&receipt,"provenance_line")?) {
                    return Err("actual stage parent, pending history and global offset agree before ingress".into());
                }
                (Some(cp),published/10,parent_sha)
            },
            _=>return Err("explicit fresh or clean resume stage".into()),
        };
        let provenance_line=format!("durable-stage-v1 source={} stage={} manifest={}",args[3],id,args[11]);
        Ok(Self{checkpoint,accepted,epoch_start,snapshots,stop_at,cooperative_ns,id,source:args[3].clone(),source_bytes:data.len(),manifest_sha:args[11].clone(),source_identity,binary_sha,parent_sha,provenance_line,framing,source_order_sha})
    }
    pub(super) fn append_provenance(&self,cp:&mut Checkpoint){cp.provenance.push('\n');cp.provenance.push_str(&self.provenance_line);}
    pub(super) fn stop_reason(&self,at:usize,elapsed:std::time::Duration)->Option<&'static str>{
        if at>=self.stop_at{Some("declared_accepted_stop")}else if elapsed.as_nanos()>=u128::from(self.cooperative_ns){Some("cooperative_elapsed_stop")}else{None}
    }
    pub(super) fn next_boundary(&self,at:usize,end:usize)->usize{self.snapshots.range((at+1)..).next().copied().unwrap_or(end).min(self.stop_at).min(end)}
    pub(super) fn snapshot(&self,cp:&Checkpoint,out:&Path,at:usize)->Result<()>{
        if !self.snapshots.contains(&at){return Ok(());}
        let file=out.join(format!("snapshot-{at:06}.state"));let (bytes,hash)=cp.publish(file.to_str().ok_or("snapshot path")?)?;
        write_durable(&out.join(format!("snapshot-{at:06}.json")),object(&[("kind",quoted("snapshot-only; no causal cut, next target, Word or model observation")),("accepted",at.to_string()),("published",total(cp.stream.resident())?.to_string()),("pending",cp.stream.pending_classes().len().to_string()),("sha256",quoted(&hash)),("bytes",bytes.to_string())]).as_bytes())
    }
    pub(super) fn seal(&self,cp:&Checkpoint,out:&Path,backend:&str,at:usize,epochs:usize,elapsed:std::time::Duration,reason:&str,complete:bool)->Result<()> {
        let save_started=Instant::now();
        let published=total(cp.stream.resident())?;
        if cp.stream.accepted_cells()?!=at as u64 || at!=published+cp.stream.pending_classes().len() || epochs!=published/10{return Err("stage publication preserves global accepted/published/pending lineage".into());}
        let file=out.join(if complete{"trained.state"}else{"stage.state"});
        let (bytes,hash)=if file.exists(){(std::fs::metadata(&file)?.len()as usize,sha256(&std::fs::read(&file)?)?)}else{cp.publish(file.to_str().ok_or("stage path")?)?};
        let (cold,cold_hash)=Checkpoint::load(file.to_str().ok_or("stage path")?,READ_BUDGET)?;
        if cold_hash!=hash || cold.bytes()?!=cp.bytes()?{return Err("complete stage native/M/crib/pending cold readback differs".into());}
        let publication_elapsed=save_started.elapsed();
        let through_readback=elapsed.checked_add(publication_elapsed).ok_or("stage timer extent")?;
        let fields=[("stage_id",self.id.clone()),("checkpoint",file.to_str().ok_or("stage path")?.to_owned()),("checkpoint_sha256",hash.clone()),("checkpoint_bytes",bytes.to_string()),("accepted",at.to_string()),("published",published.to_string()),("pending",cp.stream.pending_classes().len().to_string()),("next_unread",at.to_string()),("global_epochs",epochs.to_string()),("stage_epochs",(epochs-self.epoch_start).to_string()),("accepted_at_start",self.accepted.to_string()),("source_sha256",self.source.clone()),("source_bytes",self.source_bytes.to_string()),("source_framing",self.framing.clone()),("source_order_manifest_sha256",self.source_order_sha.clone()),("horizon",cp.population.to_string()),("parent_checkpoint_sha256",self.parent_sha.clone()),("stage_manifest_sha256",self.manifest_sha.clone()),("native_source_identity",self.source_identity.clone()),("execution_binary_sha256",self.binary_sha.clone()),("backend",backend.to_owned()),("provenance_line",self.provenance_line.clone()),("stop_reason",reason.to_owned()),("elapsed_ns",through_readback.as_nanos().to_string()),("cooperative_stop_observed_ns",elapsed.as_nanos().to_string()),("checkpoint_publish_cold_ns",publication_elapsed.as_nanos().to_string()),("training_complete",complete.to_string()),("cold_exact","true".into()),("flush","false".into())];
        write_durable(&out.join("STAGE_COMPLETE.tsv"),&emit(RECEIPT,&fields)?)?;
        write_durable(&out.join("STAGE_COMPLETE.json"),object(&[("kind",quoted(if complete{"TRAINING_COMPLETE"}else{"STAGE_COMPLETE"})),("stage_id",quoted(&self.id)),("accepted",at.to_string()),("published",published.to_string()),("pending",cp.stream.pending_classes().len().to_string()),("next_unread",at.to_string()),("global_epochs",epochs.to_string()),("parent_checkpoint_sha256",quoted(&self.parent_sha)),("checkpoint_sha256",quoted(&hash)),("training_complete",complete.to_string()),("stop_reason",quoted(reason)),("elapsed_ns",through_readback.as_nanos().to_string()),("checkpoint_publish_cold_ns",publication_elapsed.as_nanos().to_string()),("cold_exact","true".into()),("flush","false".into())]).as_bytes())
    }
}

#[cfg(test)]
fn code_manifest(path:&Path,stage_id:&str,data:&Path,corpus_sha:&str,parent:Option<&Path>,offset:usize,stop:usize,snapshots:&str)->Result<String> {
    let order=data.with_extension("order.tsv");
    let order_bytes=format!("synthetic-source-order-v1\nsource_sha256\t{corpus_sha}\nbytes\t{}\n",std::fs::metadata(data)?.len()).into_bytes();
    if order.exists(){assert_eq!(std::fs::read(&order)?,order_bytes);}else{write_new(&order,&order_bytes)?;}
    let fields=[("stage_id",stage_id.to_owned()),("mode",if parent.is_some(){"resume"}else{"fresh"}.into()),("global_accepted",offset.to_string()),("next_unread",offset.to_string()),
        ("parent_checkpoint",parent.map_or_else(||"-".into(),|p|p.join("stage.state").to_str().unwrap().to_owned())),
        ("parent_checkpoint_sha256",parent.map_or_else(||Ok("-".into()),|p|sha256(&std::fs::read(p.join("stage.state"))?))?),
        ("parent_receipt",parent.map_or_else(||"-".into(),|p|p.join("STAGE_COMPLETE.tsv").to_str().unwrap().to_owned())),
        ("parent_receipt_sha256",parent.map_or_else(||Ok("-".into()),|p|sha256(&std::fs::read(p.join("STAGE_COMPLETE.tsv"))?))?),
        ("previous_source",parent.map_or_else(||"-".into(),|p|p.parent().unwrap().join(if offset==13{"prefix.bin"}else{"full.bin"}).to_str().unwrap().to_owned())),
        ("previous_source_sha256",parent.map_or_else(||Ok("-".into()),|p|sha256(&std::fs::read(p.parent().unwrap().join(if offset==13{"prefix.bin"}else{"full.bin"}))?))?),
        ("source_sha256",corpus_sha.into()),("source_bytes",std::fs::metadata(data)?.len().to_string()),("stop_accepted",stop.to_string()),
        ("cooperative_stop_ns","60000000000".into()),("hard_training_guard_ns","90000000000".into()),("snapshot_offsets",snapshots.into()),
        ("native_source_identity","synthetic-CODE-unsealed-a26".into()),("execution_binary_sha256",executable_digest()?),
        ("source_framing","synthetic-bytes-CODE-v1".into()),("source_order_manifest",order.to_str().unwrap().into()),("source_order_manifest_sha256",sha256(&order_bytes)?)];
    let bytes=emit(MANIFEST,&fields)?;write_new(path,&bytes)?;sha256(&bytes)
}

/// One connected synthetic source, not a dataset/pilot. The four class byte chart
/// and true ten-cell section cross nonbyte13 and whole20 with pending retained.
#[cfg(test)]
pub(super) fn exercise(execution:&dyn ObservedEpochExecution,backend:CompleteLanguageTrainingBackend,root:&Path)->Result<(Vec<u8>,String)> {
    std::fs::create_dir(root)?;
    let full=root.join("full.bin");let prefix=root.join("prefix.bin");
    write_new(&full,&[0x1b;10])?;write_new(&prefix,&[0x1b;5])?;
    let cutfull=root.join("cuts-full.tsv");let cutprefix=root.join("cuts-prefix.tsv");
    write_new(&cutfull,b"0\topening\n40\tclosed\n")?;write_new(&cutprefix,b"0\topening\n20\tclosed\n")?;
    let fullsha=sha256(&std::fs::read(&full)?)?;let prefixsha=sha256(&std::fs::read(&prefix)?)?;
    let call=|command:&str,data:&Path,data_sha:&str,cuts:&Path,cells:usize,out:&Path,manifest:Option<(&Path,&str)>|->Result<()> {
        let mut args=vec![command.into(),backend.as_str().into(),data.to_str().unwrap().into(),data_sha.into(),cuts.to_str().unwrap().into(),sha256(&std::fs::read(cuts)?)?,"16384".into(),cells.to_string(),(cells/10).to_string(),out.to_str().unwrap().into()];
        if let Some((p,h))=manifest{args.push(p.to_str().unwrap().into());args.push(h.into());}
        run_with_execution(&args,execution,backend)
    };
    let continuous=root.join("continuous");
    call("train-adaptive-family-local-arrival-held-v1",&full,&fullsha,&cutfull,40,&continuous,None)?;
    let first=root.join("stage1");let m1=root.join("stage1.tsv");let h1=code_manifest(&m1,"s1",&prefix,&prefixsha,None,0,13,"3,13")?;
    call(COMMAND,&prefix,&prefixsha,&cutprefix,20,&first,Some((&m1,&h1)))?;
    assert!(!first.join("TRAINING_COMPLETE.json").exists());assert!(!first.join("cut-00013.json").exists());
    assert!(first.join("snapshot-000003.state").exists());
    let (cp1,hash1)=Checkpoint::load(first.join("stage.state").to_str().unwrap(),READ_BUDGET)?;
    assert_eq!(cp1.stream.accepted_cells()?,13);assert_eq!(total(cp1.stream.resident())?,10);assert_eq!(cp1.stream.pending_classes().len(),3);
    let receipt1=table(&std::fs::read(first.join("STAGE_COMPLETE.tsv"))?,RECEIPT)?;assert_eq!(word(&receipt1,"checkpoint_sha256")?,hash1);
    // Refusal controls call the same public command. They may cold-read the parent,
    // but no new input is admitted and no output directory is created.
    let m2=root.join("stage2.tsv");let h2=code_manifest(&m2,"s2",&full,&fullsha,Some(&first),13,20,"20")?;
    for (label,old,new) in [("wrong-offset","global_accepted\t13".to_owned(),"global_accepted\t14".to_owned()),("wrong-parent",format!("parent_checkpoint_sha256\t{hash1}"),"parent_checkpoint_sha256\t0000000000000000000000000000000000000000000000000000000000000000".to_owned())] {
        let data=String::from_utf8(std::fs::read(&m2)?)?.replace(&old,&new);let file=root.join(format!("{label}.tsv"));write_new(&file,data.as_bytes())?;let out=root.join(format!("refused-{label}"));
        assert!(call(COMMAND,&full,&fullsha,&cutfull,40,&out,Some((&file,&sha256(data.as_bytes())?))).is_err());assert!(!out.exists());
    }
    let bad=root.join("bad-prefix.bin");let mut badbytes=std::fs::read(&full)?;badbytes[0]^=1;write_new(&bad,&badbytes)?;let badsha=sha256(&badbytes)?;
    let bmanifest=root.join("bad-prefix.tsv");let bh=code_manifest(&bmanifest,"bad",&bad,&badsha,Some(&first),13,20,"-")?;let bout=root.join("refused-prefix");
    assert!(call(COMMAND,&bad,&badsha,&cutfull,40,&bout,Some((&bmanifest,&bh))).is_err());assert!(!bout.exists());
    assert_eq!(sha256(&std::fs::read(first.join("stage.state"))?)?,hash1);
    // A late publication/readback fault is terminal, never a clean resume parent.
    let fault=root.join("publication-refusal");std::fs::create_dir(&fault)?;write_new(&fault.join("stage.state"),b"not-a-native-checkpoint")?;
    let manifest_args=vec![COMMAND.into(),backend.as_str().into(),full.to_str().unwrap().into(),fullsha.clone(),cutfull.to_str().unwrap().into(),sha256(&std::fs::read(&cutfull)?)?,"16384".into(),"40".into(),"4".into(),fault.to_str().unwrap().into(),m2.to_str().unwrap().into(),h2.clone()];
    let capable=Stage::open(&manifest_args,&std::fs::read(&full)?,&digits(&std::fs::read(&full)?),backend.as_str(),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    let parent_bytes=cp1.bytes()?;
    assert!(capable.seal(&cp1,&fault,backend.as_str(),13,1,std::time::Duration::ZERO,"synthetic-publication-fault",false).is_err());
    assert!(!fault.join("STAGE_COMPLETE.tsv").exists());assert_eq!(parent_bytes,cp1.bytes()?);
    let second=root.join("stage2");call(COMMAND,&full,&fullsha,&cutfull,40,&second,Some((&m2,&h2)))?;
    let (cp2,_)=Checkpoint::load(second.join("stage.state").to_str().unwrap(),READ_BUDGET)?;
    assert_eq!(cp2.stream.accepted_cells()?,20);assert_eq!(total(cp2.stream.resident())?,20);assert!(cp2.stream.pending_classes().is_empty());
    let m3=root.join("stage3.tsv");let h3=code_manifest(&m3,"s3",&full,&fullsha,Some(&second),20,40,"30")?;
    let third=root.join("stage3");call(COMMAND,&full,&fullsha,&cutfull,40,&third,Some((&m3,&h3)))?;
    assert!(third.join("TRAINING_COMPLETE.json").exists());
    let (mut a,_)=Checkpoint::load(continuous.join("trained.state").to_str().unwrap(),READ_BUDGET)?;
    let (mut b,_)=Checkpoint::load(third.join("trained.state").to_str().unwrap(),READ_BUDGET)?;
    assert_eq!(b.stream.accepted_cells()?,40);assert_eq!(total(b.stream.resident())?,40);assert!(b.stream.pending_classes().is_empty());
    assert_eq!(a.stream.resident().prepared_input().unwrap().frontiers(),(40,0,0));
    a.provenance.clear();b.provenance.clear();assert_eq!(a.bytes()?,b.bytes()?,"complete native/M/tree/population/crib/pending equality; no reset or duplicated ingress");
    let mut lines=Vec::new();
    for (folder,expected)in [(&first,vec![1]),(&second,vec![2]),(&third,vec![3,4])] {
        let text=std::fs::read_to_string(folder.join("epochs.jsonl"))?;
        for n in expected{assert!(text.contains(&format!("\\\"epoch\\\":{n}"))||text.contains(&format!("\"epoch\":{n}")));}
        lines.push(format!("{} {}",folder.file_name().unwrap().to_str().unwrap(),text.lines().count()));
    }
    // Cooperative elapsed stop at the already bound fresh opening, no ingress.
    let mt=root.join("clock-stop.tsv");let ht=code_manifest(&mt,"clock",&full,&fullsha,None,0,40,"-")?;
    let mut bytes=String::from_utf8(std::fs::read(&mt)?)?;bytes=bytes.replace("cooperative_stop_ns\t60000000000","cooperative_stop_ns\t0");
    let clock_manifest=root.join("clock-stop-zero.tsv");write_new(&clock_manifest,bytes.as_bytes())?;
    let clock_out=root.join("clock-stop");
    // Host-only: zero dispatch is an explicitly empty stage, not CUDA fallback.
    if backend==CompleteLanguageTrainingBackend::HostReference {
        call(COMMAND,&full,&fullsha,&cutfull,40,&clock_out,Some((&clock_manifest,&sha256(bytes.as_bytes())?)))?;
        let r=table(&std::fs::read(clock_out.join("STAGE_COMPLETE.tsv"))?,RECEIPT)?;assert_eq!(number(&r,"accepted")?,0);assert_eq!(word(&r,"stop_reason")?,"cooperative_elapsed_stop");
    }
    let _=ht;
    Ok((b.bytes()?,format!("DURABLE_CONTINUATION backend={} continuous40==split13+7+20=true parent13published10pending3=true whole20=true prefix20to40=true snapshot3-no-diagnostic=true global-epochs={lines:?} wrongparent/prefix/offset-beforeingress=true coldexact=true",backend.as_str())))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn same_training_loop_durable_split_and_prefix_cold() {
        let root=std::env::var_os("V93_DURABLE_FIXTURE_DIR").map(std::path::PathBuf::from).unwrap_or_else(||std::env::temp_dir().join(format!("v93-durable-{}",std::process::id())));
        std::fs::create_dir_all(&root).unwrap();
        let (_,receipt)=exercise(&HostObservedEpochExecution,CompleteLanguageTrainingBackend::HostReference,&root.join("host")).unwrap();println!("{receipt}");
    }
}
