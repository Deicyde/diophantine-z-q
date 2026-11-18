// No npm imports here. This action never starts, stops or replaces a kernel command.
const fs = require('node:fs');
const path = require('node:path');
const {spawn, execFileSync} = require('node:child_process');
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
async function main() {
  const mode = process.env.INPUT_MODE;
  if (mode === 'start') {
    const workspace = fs.realpathSync(process.env.GITHUB_WORKSPACE);
    const attempt = process.env.GITHUB_RUN_ATTEMPT;
    if (!/^[0-9]+$/.test(attempt)) throw new Error('Invalid run attempt');
    const directory = fs.mkdtempSync(path.join(process.env.RUNNER_TEMP, 'kernel-progress-'));
    const identity = {run_id: process.env.GITHUB_RUN_ID, run_attempt: attempt,
      event_sha: process.env.GITHUB_SHA,
      checkout_sha: execFileSync('git', ['rev-parse','HEAD'],{cwd:workspace,encoding:'utf8'}).trim()};
    fs.writeFileSync(path.join(directory,'identity.json'),JSON.stringify(identity));
    const log = fs.openSync(path.join(directory,'observer.log'),'a');
    const child = spawn(process.execPath,[path.join(__dirname,'observer.cjs'),workspace,directory],
      {detached:true,stdio:['ignore',log,log]});
    // Persist the directory before returning so the later stop step can signal it.
    fs.appendFileSync(process.env.GITHUB_ENV,'KERNEL_PROGRESS_DIR='+directory+'\n');
    child.unref(); fs.closeSync(log);
    // Confirm the observer started, not that the remote service accepted an upload.
    for(let i=0;i<50;i++) {
      if(fs.existsSync(path.join(directory,'started'))) return;
      await sleep(100);
    }
    throw new Error('Background observer did not acknowledge startup');
  }
  if(mode!=='stop') throw new Error('Invalid observer mode');
  const directory=process.env.KERNEL_PROGRESS_DIR;
  if(!directory) return;
  const parent=fs.realpathSync(process.env.RUNNER_TEMP);
  if(path.dirname(directory)!==parent || !/^kernel-progress-[A-Za-z0-9]+$/.test(path.basename(directory)))
    throw new Error('Invalid observer directory');
  fs.writeFileSync(path.join(directory,'stop'),'');
  for(let i=0;i<60;i++) {
    if(fs.existsSync(path.join(directory,'finished'))) break;
    await sleep(1000);
  }
  const source=path.join(directory,'status.json');
  const status=fs.existsSync(source)?JSON.parse(fs.readFileSync(source,'utf8')):{};
  status.observer_finished=fs.existsSync(path.join(directory,'finished'));
  fs.mkdirSync('build/kernel-ci',{recursive:true});
  fs.writeFileSync('build/kernel-ci/periodic-upload-status.json',JSON.stringify(status,null,2)+'\n');
  const message=status.last_confirmed_artifact
    ? 'Periodic resource evidence uploaded through '+status.last_confirmed_artifact+'.'
    : 'No periodic resource upload was confirmed. Inspect the ordinary final artifacts.';
  fs.appendFileSync(process.env.GITHUB_STEP_SUMMARY,message+'\n');
}
main().catch(error=>{console.error('::warning::Optional resource observer: '+error.message);process.exitCode=1;});
