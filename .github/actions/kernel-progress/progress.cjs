const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const {spawn} = require('node:child_process');

const INTERVAL_MS = 120_000;
const UPLOAD_TIMEOUT_MS = 45_000;
const MAX_UPLOADS = 200; // At most 200 across the job, below the job's 500 limit.
const MAX_FILE_BYTES = 2 * 1024 * 1024;
const MAX_CHUNK_BYTES = 8 * 1024 * 1024;
const allowed = /^(?:(?:root-build|modules-\d+|kernel-audit)-(?:memory\.jsonl|timing\.json|resource-usage\.txt)|swap-status\.json|build-complete\.json)$/;

function snapshot(source, destination, offsets, identity) {
  fs.mkdirSync(destination, {recursive: true});
  const next = {...offsets};
  const rows = [];
  let remaining = MAX_CHUNK_BYTES;
  // Refuse a symlinked output directory. Upload only named diagnostic files.
  if (fs.existsSync(source)) {
    if (fs.realpathSync(source) !== path.resolve(source)) throw new Error('Symlinked diagnostic directory');
    for (const name of fs.readdirSync(source).filter(n => allowed.test(n)).sort()) {
      const file = path.join(source, name);
      const info = fs.lstatSync(file);
      if (!info.isFile() || info.isSymbolicLink()) throw new Error('Non-regular diagnostic file');
      const lineStream = name.endsWith('.jsonl');
      const previous = offsets[name] || 0;
      const start = lineStream && previous <= info.size ? previous : 0;
      const wanted = Math.min(info.size - start, MAX_FILE_BYTES, remaining);
      if (wanted <= 0) continue;
      const descriptor = fs.openSync(file, 'r');
      let data;
      try {
        const buffer = Buffer.alloc(wanted);
        data = buffer.subarray(0, fs.readSync(descriptor, buffer, 0, wanted, start));
      } finally { fs.closeSync(descriptor); }
      if (lineStream) data = data.subarray(0, data.lastIndexOf(10) + 1);
      if (!data.length) continue;
      const end = start + data.length;
      fs.writeFileSync(path.join(destination, name), data);
      rows.push({name, start, end, observed_size: info.size,
        remaining_bytes: info.size - end, reset: lineStream && previous > info.size,
        sha256: crypto.createHash('sha256').update(data).digest('hex')});
      next[name] = lineStream ? end : 0;
      remaining -= data.length;
    }
  }
  const manifest = {schema: 'kernel-progress/v1', ...identity,
    captured_at: new Date().toISOString(), acceptance: false,
    description: 'Partial diagnostic evidence only; not a successful build or audit.',
    per_file_byte_limit: MAX_FILE_BYTES, per_chunk_byte_limit: MAX_CHUNK_BYTES, files: rows};
  fs.writeFileSync(path.join(destination, 'manifest.json'), JSON.stringify(manifest, null, 2)+'\n');
  return {next, manifest};
}

function runUpload(directory, name, {spawnImpl = spawn, timeoutMs = UPLOAD_TIMEOUT_MS} = {}) {
  return new Promise(resolve => {
    const env = {...process.env, GITHUB_WORKSPACE: directory,
      ACTIONS_ARTIFACT_UPLOAD_CONCURRENCY: '1', ACTIONS_ARTIFACT_UPLOAD_TIMEOUT_MS: '30000'};
    for (const key of ['GITHUB_ENV','GITHUB_OUTPUT','GITHUB_PATH','GITHUB_STATE','GITHUB_STEP_SUMMARY']) delete env[key];
    const child = spawnImpl(process.execPath, [path.join(__dirname, 'upload.cjs'), directory, name],
      {cwd: directory, stdio: ['ignore', 'inherit', 'inherit'], env});
    let finished = false;
    let timer;
    const finish = result => { if (!finished) {finished = true; clearTimeout(timer); resolve(result);} };
    child.once('error', () => finish(false));
    child.once('exit', (code, signal) => finish(code === 0 && !signal));
    timer = setTimeout(() => {
      console.log('::warning::Resource upload timed out; its completion is unknown. Later chunks use new names.');
      child.kill('SIGKILL');
      finish(false);
    }, timeoutMs);
  });
}

async function observe(captureAndUpload, stopping, {
  intervalMs = INTERVAL_MS, pollMs = 1000, maxUploads = MAX_UPLOADS,
  sleep = milliseconds => new Promise(resolve => setTimeout(resolve, milliseconds))
} = {}) {
  for (let sequence = 1; sequence <= maxUploads; sequence++) {
    const final = stopping();
    try { await captureAndUpload(sequence, final); }
    catch (error) { console.log('Resource evidence unavailable: '+error.message); }
    if (final) return;
    const deadline = Date.now() + intervalMs;
    while (!stopping() && Date.now() < deadline) await sleep(Math.min(pollMs, deadline-Date.now()));
  }
  console.log('Periodic resource upload limit reached; normal final uploads remain.');
}

module.exports = {snapshot, runUpload, observe, INTERVAL_MS, MAX_UPLOADS,
  MAX_FILE_BYTES, MAX_CHUNK_BYTES};
