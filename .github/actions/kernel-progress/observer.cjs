// Only first-party code runs in the long-lived observer. npm is loaded by upload.cjs alone.
const fs=require('node:fs');
const path=require('node:path');
const {snapshot,observe,runUpload}=require('./progress.cjs');
(async()=>{
  const [workspace,directory]=process.argv.slice(2);
  const identity=JSON.parse(fs.readFileSync(path.join(directory,'identity.json'),'utf8'));
  const status={...identity,acceptance:false,last_confirmed_artifact:null,failed_uploads:0};
  let offsets={};
  fs.writeFileSync(path.join(directory,'started'),'');
  await observe(async(sequence,final)=>{
    const name=`kernel-progress-${identity.run_attempt}-${String(sequence).padStart(3,'0')}`;
    const staging=path.join(directory,name);
    const captured=snapshot(path.join(workspace,'build/kernel-ci'),staging,offsets,
      {...identity,sequence,stop_requested:final});
    if(await runUpload(staging,name)) {offsets=captured.next;status.last_confirmed_artifact=name;}
    else status.failed_uploads++;
    status.last_attempt_at=new Date().toISOString();
    fs.writeFileSync(path.join(directory,'status.json'),JSON.stringify(status,null,2)+'\n');
    // Only remove this task's direct staging files. Original diagnostic files are untouched.
    if(path.dirname(staging)!==directory) throw new Error('Invalid staging path');
    for(const entry of fs.readdirSync(staging)) fs.unlinkSync(path.join(staging,entry));
    fs.rmdirSync(staging);
  },()=>fs.existsSync(path.join(directory,'stop')));
  fs.writeFileSync(path.join(directory,'finished'),'');
})().catch(error=>{console.error('Observer stopped:',error.message);process.exitCode=1;});
