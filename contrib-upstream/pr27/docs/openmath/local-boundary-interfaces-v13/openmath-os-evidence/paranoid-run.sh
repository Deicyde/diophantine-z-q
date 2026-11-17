#!/bin/sh
set -eu
export PATH="$PWD/.checks/tool-bin:$PATH"
export TMPDIR="$PWD/.checks/tmp"
export TMP="$TMPDIR"
export TEMP="$TMPDIR"
set -x
PROJECT="$PWD/lean/.checks/openmath-local-boundary"
EVIDENCE="$PWD/docs/openmath/local-boundary-interfaces-v13/openmath-os-evidence"
cd "$PROJECT"
sha256sum -c MANIFEST.sha256 > "$EVIDENCE/generated-manifest.stdout.txt" 2> "$EVIDENCE/generated-manifest.stderr.txt"
lean --version > "$EVIDENCE/lean-version.txt"
lake --version > "$EVIDENCE/lake-version.txt"
set +e
lake build > "$EVIDENCE/lake-build.stdout.txt" 2> "$EVIDENCE/lake-build.stderr.txt"
status=$?
set -e
printf '%s\n' "$status" > "$EVIDENCE/lake-build-exit-code.txt"
if [ "$status" -ne 0 ]; then
  cat "$EVIDENCE/lake-build.stderr.txt"
  exit "$status"
fi
set +e
python3 - > "$EVIDENCE/export.stdout.txt" 2> "$EVIDENCE/export.stderr.txt" <<'PY'
from pathlib import Path
import hashlib, json, subprocess
roots=Path('roots.txt').read_text().splitlines()
if len(roots) != 41 or len(set(roots)) != 41:
    raise SystemExit('Expected exactly 41 distinct proof roots')
if roots != json.loads(Path('TARGETS.json').read_text())['proof_roots']:
    raise SystemExit('Root list differs from the frozen selection')
evidence=Path('openmath-evidence')
evidence.mkdir(exist_ok=False)
argv=['lake','env','leanexport','Packet','--',*roots]
with (evidence/'packet.ndjson').open('wb') as out, (evidence/'export.stderr.txt').open('wb') as err:
    result=subprocess.run(argv, stdout=out, stderr=err)
receipt={'command':argv,'exit_code':result.returncode,
    'export_sha256':hashlib.sha256((evidence/'packet.ndjson').read_bytes()).hexdigest(),
    'roots':roots,'export_bytes':(evidence/'packet.ndjson').stat().st_size}
(evidence/'export.json').write_text(json.dumps(receipt,indent=2)+'\n')
if result.returncode:
    raise SystemExit('Export failed; retained failure evidence')
print(json.dumps(receipt))
PY
status=$?
set -e
printf '%s\n' "$status" > "$EVIDENCE/export-exit-code.txt"
if [ "$status" -ne 0 ]; then
  cat "$EVIDENCE/export.stdout.txt"
  cat "$EVIDENCE/export.stderr.txt"
  exit "$status"
fi
cp openmath-evidence/packet.ndjson "$EVIDENCE/packet.ndjson"
cp openmath-evidence/export.json "$EVIDENCE/EXPORT_REPLAY_INPUT.json"
cp openmath-evidence/export.stderr.txt "$EVIDENCE/export.stderr.txt"
set +e
lake check --from-export openmath-evidence/packet.ndjson --paranoid > "$EVIDENCE/paranoid.stdout.txt" 2> "$EVIDENCE/paranoid.stderr.txt"
status=$?
set -e
printf '%s\n' "$status" > "$EVIDENCE/paranoid-exit-code.txt"
python3 - <<'PY'
from pathlib import Path
import hashlib,json,shutil,subprocess
root=Path.cwd()
center=Path('../../../docs/openmath/local-boundary-interfaces-v13/openmath-os-evidence').resolve()
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
artifacts=[]
for base in (root/'.lake/build/lib/lean', root/'openmath-evidence'):
    if base.is_dir():
        for p in sorted(base.rglob('*')):
            if p.is_file() and p.suffix in {'.olean','.trace','.ilean'}:
                artifacts.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
artifacts.append({'path':str(center/'packet.ndjson'),'sha256':sha(center/'packet.ndjson'),'bytes':(center/'packet.ndjson').stat().st_size})
assert artifacts
prefix=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())
tools={}
for name in ('lean','lake','leanexport','leanchecker','leanchecker-paranoid','lean4lean','nanoda_bin','con-leche','con-ron'):
    candidate=prefix/'bin'/name
    if not candidate.exists():
        resolved=shutil.which(name)
        candidate=Path(resolved) if resolved else None
    tools[name]=({'path':str(candidate),'sha256':sha(candidate)} if candidate and candidate.exists() else {'found':False})
report={'compiled_artifact_hashes':artifacts,'tool_versions':tools,
        'paranoid_exit_code':int((center/'paranoid-exit-code.txt').read_text())}
(center/'ARTIFACTS_AND_TOOLS.json').write_text(json.dumps(report,indent=2)+'\n')
native=Path('../pr2-native-independent')
for filename in ('RESULT.json','commands.json','axioms-and-statements.stdout.txt','axioms-and-statements.stderr.txt','Audit.lean'):
    if (native/filename).exists():
        shutil.copy2(native/filename,center/'native-'+filename)
print(json.dumps({'artifacts':len(artifacts),'tools':tools}))
PY
status=$?
set -e
printf '%s\n' "$status" > "$EVIDENCE/artifact-audit-exit-code.txt"
if [ "$status" -ne 0 ]; then
  exit "$status"
fi
cd "$OLDPWD"
git status --short > "$EVIDENCE/git-status.txt"
printf '%s\n' 'Paranoid process finished. Read its actual exit code/stderr in the evidence.'
printf 'paranoid_exit='
cat "$EVIDENCE/paranoid-exit-code.txt"
