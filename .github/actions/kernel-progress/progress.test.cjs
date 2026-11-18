const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const {EventEmitter} = require('node:events');
const {snapshot, observe, runUpload, MAX_FILE_BYTES, MAX_UPLOADS, INTERVAL_MS} = require('./progress.cjs');
function fixture(t) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'kernel-progress-test-'));
  t.after(() => fs.rmSync(root, {recursive:true, force:true}));
  const source = path.join(root, 'source'); fs.mkdirSync(source);
  return {root, source, dest: n => path.join(root, 'chunk-'+n)};
}
test('observer uploads during the job, then a final chunk when stopped',async()=>{
  let stop=false;const calls=[];
  await observe(async(sequence,final)=>{calls.push(final);if(sequence===2)stop=true;},()=>stop,{intervalMs:5,pollMs:1});
  assert.deepEqual(calls,[false,false,true]);
});
test('failed uploads do not overlap or prevent later diagnostic attempts',async()=>{
  let stop=false,calls=0,active=0,peak=0;
  await observe(async()=>{active++;peak=Math.max(peak,active);calls++;
    await new Promise(r=>setTimeout(r,1));active--;if(calls===2)stop=true;throw new Error('offline');},
    ()=>stop,{intervalMs:5,pollMs:1});
  assert.equal(peak,1);assert.equal(calls,3);
});
test('observer limits remote operations independently of kernel execution',async()=>{
  let calls=0;await observe(async()=>{calls++;},()=>false,{intervalMs:1,pollMs:1,maxUploads:2});
  assert.equal(calls,2);assert.ok(MAX_UPLOADS+10<500);assert.equal(INTERVAL_MS,120000);
});
test('upload subprocess is killed after a bounded timeout', async () => {
  const child=new EventEmitter(); let killed;
  child.kill = signal => {killed=signal; setImmediate(()=>child.emit('exit',null,signal));};
  assert.equal(await runUpload('unused','unused',{spawnImpl:()=>child,timeoutMs:5}),false);
  assert.equal(killed,'SIGKILL');
});
test('only confirmed uploader completion is successful', async () => {
  for (const code of [0,1]) {
    const child=new EventEmitter(); child.kill=()=>{};
    setImmediate(()=>child.emit('exit',code,null));
    assert.equal(await runUpload('unused','unused',{spawnImpl:()=>child,timeoutMs:100}),code===0);
  }
});
test('complete JSONL chunks have exact ranges and do not consume an unfinished line', t => {
  const f=fixture(t), name='root-build-memory.jsonl';
  fs.writeFileSync(path.join(f.source,name),'{"n":1}\n{"n":');
  const first=snapshot(f.source,f.dest(1),{}, {run_id:'123',checkout_sha:'a'.repeat(40)});
  assert.equal(fs.readFileSync(path.join(f.dest(1),name),'utf8'),'{"n":1}\n');
  assert.equal(first.next[name],8); assert.equal(first.manifest.acceptance,false);
  assert.equal(first.manifest.files[0].remaining_bytes,5);
  fs.appendFileSync(path.join(f.source,name),'2}\n');
  const second=snapshot(f.source,f.dest(2),first.next,{});
  assert.equal(fs.readFileSync(path.join(f.dest(2),name),'utf8'),'{"n":2}\n');
  assert.equal(second.manifest.files[0].start,8);
  const retry=snapshot(f.source,f.dest(3),first.next,{});
  assert.equal(retry.manifest.files[0].sha256,second.manifest.files[0].sha256);
});
test('partial sample never appears in an artifact',t=>{
  const f=fixture(t); fs.writeFileSync(path.join(f.source,'kernel-audit-memory.jsonl'),'{"unfinished":');
  assert.equal(snapshot(f.source,f.dest(1),{},{}).manifest.files.length,0);
});
test('bounded chunks declare the unuploaded remainder',t=>{
  const f=fixture(t), name='root-build-memory.jsonl';
  fs.writeFileSync(path.join(f.source,name),'{}\n'.repeat(MAX_FILE_BYTES));
  const result=snapshot(f.source,f.dest(1),{},{});
  assert.ok(result.manifest.files[0].end<=MAX_FILE_BYTES);
  assert.ok(result.manifest.files[0].remaining_bytes>0);
});
test('file reset is explicit and unrelated files are never selected',t=>{
  const f=fixture(t), name='root-build-memory.jsonl';
  fs.writeFileSync(path.join(f.source,name),'{}\n');
  fs.writeFileSync(path.join(f.source,'audit.json'),'not diagnostic');
  fs.writeFileSync(path.join(f.source,'compile.log'),'not diagnostic');
  const result=snapshot(f.source,f.dest(1),{[name]:999},{});
  assert.equal(result.manifest.files.length,1); assert.equal(result.manifest.files[0].reset,true);
});
test('symlinked inputs are refused', {skip:process.platform==='win32'}, t=>{
  const f=fixture(t); const outside=path.join(f.root,'outside'); fs.writeFileSync(outside,'secret');
  fs.symlinkSync(outside,path.join(f.source,'swap-status.json'));
  assert.throws(()=>snapshot(f.source,f.dest(1),{},{}),/Non-regular/);
});
test('workflow keeps ordinary kernel commands even if optional diagnostics fail',()=>{
  const repo=path.resolve(__dirname,'../../..');
  const workflow=fs.readFileSync(path.join(repo,'.github/workflows/kernel-lean.yml'),'utf8');
  const steps=workflow.split(/^      - name: /m).slice(1);
  for(const name of ['Install and test optional resource uploader','Start optional resource uploader','Stop optional resource uploader']){
    const step=steps.find(s=>s.startsWith(name));assert.ok(step.includes('continue-on-error: true'));
  }
  assert.ok(steps.find(s=>s.startsWith('Build all kernel modules')).includes('run: python -B scripts/check_kernel.py --phase build'));
  assert.ok(steps.find(s=>s.startsWith('Replay all kernel proofs')).includes('run: python -B scripts/check_kernel.py --phase audit --base-report build/kernel-ci/base-audit.json'));
  assert.ok(steps.find(s=>s.startsWith('Replay all kernel proofs')).includes("LEAN_NUM_THREADS: '1'"));
  for(const name of ['Build all kernel modules','Replay all kernel proofs']){
    const step=steps.find(s=>s.startsWith(name));assert.ok(!step.includes('progress_start'));assert.ok(!step.includes('continue-on-error'));
  }
  assert.ok(workflow.includes('Periodic resource uploads unavailable.'));
  assert.ok(workflow.includes('node --test .github/actions/kernel-progress/progress.test.cjs'));
});
test('only the disposable upload child imports the locked artifact client',()=>{
  for(const file of ['index.cjs','observer.cjs','progress.cjs']){
    const text=fs.readFileSync(path.join(__dirname,file),'utf8');
    for(const match of text.matchAll(/require\(['"]([^'"]+)['"]\)/g))
      assert.ok(match[1].startsWith('node:') || match[1]==='./progress.cjs',file+': '+match[1]);
  }
  const contract=JSON.parse(fs.readFileSync(path.resolve(__dirname,'../../../KERNEL_CONTRACT.json'),'utf8'));
  for(const file of ['index.cjs','observer.cjs','progress.cjs','upload.cjs','package-lock.json'])
    assert.ok(contract.files['.github/actions/kernel-progress/'+file]);
});
test('upload child receives only staging paths and no workflow command files',async()=>{
  const child=new EventEmitter();child.kill=()=>{};let captured;
  const result=runUpload('/temporary/snapshot','kernel-progress-1-001',{spawnImpl:(exe,args,options)=>{
    captured={args,options};setImmediate(()=>child.emit('exit',0,null));return child;}});
  assert.equal(await result,true);assert.equal(captured.options.cwd,'/temporary/snapshot');
  assert.equal(captured.options.env.GITHUB_WORKSPACE,'/temporary/snapshot');
  assert.equal(captured.options.env.ACTIONS_ARTIFACT_UPLOAD_CONCURRENCY,'1');
  for(const key of ['GITHUB_ENV','GITHUB_OUTPUT','GITHUB_PATH','GITHUB_STATE','GITHUB_STEP_SUMMARY'])
    assert.equal(captured.options.env[key],undefined);
});

test('separate start and stop steps preserve an uploaded chunk while a kernel stand-in runs',async t=>{
  const {spawn,spawnSync}=require('node:child_process');
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'kernel-observer-integration-'));
  const workspace=path.join(root,'workspace'), action=path.join(root,'action'), remote=path.join(root,'remote');
  for(const dir of [workspace,action,remote])fs.mkdirSync(dir);
  for(const file of ['index.cjs','observer.cjs','progress.cjs'])fs.copyFileSync(path.join(__dirname,file),path.join(action,file));
  fs.writeFileSync(path.join(action,'upload.cjs'),`
    const fs=require('node:fs'),path=require('node:path');
    const [directory,name]=process.argv.slice(2);
    if(process.env.GITHUB_ENV)throw new Error('command-file credential leaked');
    fs.copyFileSync(path.join(directory,'manifest.json'),path.join(process.env.TEST_REMOTE_DIR,name+'.json'));
  `);
  for(const args of [['init','-q',workspace],['-C',workspace,'-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','--allow-empty','-qm','fixture']]){
    const result=spawnSync('git',args,{encoding:'utf8'});assert.equal(result.status,0,result.stderr);
  }
  fs.mkdirSync(path.join(workspace,'build/kernel-ci'),{recursive:true});
  fs.writeFileSync(path.join(workspace,'build/kernel-ci/root-build-memory.jsonl'),'{}\n');
  const envFile=path.join(root,'env'),summary=path.join(root,'summary');
  fs.writeFileSync(envFile,'');fs.writeFileSync(summary,'');
  const env={...process.env,INPUT_MODE:'start',GITHUB_WORKSPACE:workspace,RUNNER_TEMP:fs.realpathSync(root),
    GITHUB_RUN_ATTEMPT:'1',GITHUB_RUN_ID:'123',GITHUB_SHA:'a'.repeat(40),GITHUB_ENV:envFile,
    GITHUB_STEP_SUMMARY:summary,TEST_REMOTE_DIR:remote};
  const kernel=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{stdio:'ignore'});
  let observerDirectory;
  t.after(async()=>{
    kernel.kill('SIGKILL');
    if(observerDirectory&&fs.existsSync(observerDirectory))fs.writeFileSync(path.join(observerDirectory,'stop'),'');
    await new Promise(r=>setTimeout(r,1500));fs.rmSync(root,{recursive:true,force:true});
  });
  const started=spawnSync(process.execPath,[path.join(action,'index.cjs')],{cwd:workspace,env,encoding:'utf8',timeout:10000});
  assert.equal(started.status,0,started.stderr);
  observerDirectory=fs.readFileSync(envFile,'utf8').trim().split('=',2)[1];
  for(let i=0;i<100&&!fs.readdirSync(remote).length;i++)await new Promise(r=>setTimeout(r,50));
  assert.ok(fs.readdirSync(remote).length);assert.equal(kernel.exitCode,null);
  const first=JSON.parse(fs.readFileSync(path.join(remote,fs.readdirSync(remote)[0]),'utf8'));
  assert.equal(first.files[0].name,'root-build-memory.jsonl');assert.equal(first.acceptance,false);
  const stopped=spawnSync(process.execPath,[path.join(action,'index.cjs')],{cwd:workspace,
    env:{...env,INPUT_MODE:'stop',KERNEL_PROGRESS_DIR:observerDirectory},encoding:'utf8',timeout:10000});
  assert.equal(stopped.status,0,stopped.stderr);
  assert.equal(kernel.exitCode,null,'Stopping telemetry must not stop the kernel command');
  assert.equal(JSON.parse(fs.readFileSync(path.join(workspace,'build/kernel-ci/periodic-upload-status.json'),'utf8')).observer_finished,true);
});
