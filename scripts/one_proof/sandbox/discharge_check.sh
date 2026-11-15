#!/usr/bin/env bash
# The discharge check. It runs in the fork's workflow .github/workflows/contrib-discharges.yml, on a
# GitHub-hosted runner, at the root of the pull request's checkout; never run it on a project machine: it builds
# outside code, and Lean runs code while it elaborates. See README.md in this directory.
#
# Usage: discharge_check.sh scope BASE HEAD
#        discharge_check.sh [build|report|all|measure]   (default: all)
#
#   scope    runs scan_contrib.py on BASE and HEAD (git objects only, before anything is built), writes
#            .sandbox/out/scan.json and, in scope, .sandbox/manifest.json {base, head, added}. Exit status 0 in
#            scope, 2 out of scope, 1 on error.
#   build    reads .sandbox/manifest.json and builds +ZInQKernel.OneProof.Main, +ZInQKernel.OneProof.Discharges
#            and each added module; writes .sandbox/out/build.log and the build's status and time.
#   report   needs DISCHARGE_NONCE (the workflow sets it from a fresh random value in this step only). Runs
#            `#discharges` from a generated .sandbox/Check.lean for display, with the nonce removed from its
#            environment (its imports can still read it from this process), then the trusted reporter
#            DischargesJson.lean through a generated .sandbox/Report.lean, runs render_open.py --check for
#            information, and writes .sandbox/out/check.log and .sandbox/out/result.json. Exit status 0 on
#            pass, 1 on fail.
#   all      build, then report.
#   measure  with no contribution: builds +ZInQKernel.OneProof.Main alone under /usr/bin/time -v when GNU time
#            is present, records df and free before and after, and writes .sandbox/out/result.json with the
#            commit, wall-clock, peak memory and Lake job count.
# A build stops after 270 minutes, inside the workflow's 300-minute job limit.
set -uo pipefail

mode="${1:-all}"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
cd "$root" || exit 1

sb=.sandbox
out="$sb/out"
manifest="$sb/manifest.json"
mkdir -p "$out"

# GNU time gives peak memory; elsewhere the build runs without it.
timer=()
if /usr/bin/time -v true >/dev/null 2>&1; then
  timer=(/usr/bin/time -v -o "$out/time.txt")
fi

# Leave 30 minutes of the job limit for the setup, the reporter, the summary and the upload.
limit=()
if command -v timeout >/dev/null 2>&1; then
  limit=(timeout 270m)
fi

if [ "$mode" = scope ]; then
  if [ $# -ne 3 ]; then
    echo "usage: discharge_check.sh scope BASE HEAD" >&2
    exit 1
  fi
  rm -f "$manifest"
  scan_status=0
  python3 -I "$here/scan_contrib.py" "$2" "$3" --json "$out/scan.json" || scan_status=$?
  if [ "$scan_status" -ne 0 ]; then
    exit "$scan_status"
  fi
  python3 -I - "$out/scan.json" "$manifest" <<'PY'
import json, sys
scan = json.load(open(sys.argv[1]))
if scan.get('scope_ok') is not True:
    sys.exit('discharge_check: the scan does not report scope_ok')
manifest = {'base': scan['base'], 'head': scan['head'], 'added': [f['path'] for f in scan['files']]}
with open(sys.argv[2], 'w') as fh:
    json.dump(manifest, fh, indent=2)
    fh.write('\n')
PY
  exit $?
fi

if [ "$mode" = measure ]; then
  df -k / > "$out/df-before.txt" 2>&1
  free -k > "$out/free-before.txt" 2>&1
  start=$(date +%s)
  echo "== lake build +ZInQKernel.OneProof.Main (measurement)"
  ${limit[@]+"${limit[@]}"} ${timer[@]+"${timer[@]}"} lake build +ZInQKernel.OneProof.Main 2>&1 | tee "$out/build.log"
  build_status=${PIPESTATUS[0]}
  seconds=$(( $(date +%s) - start ))
  df -k / > "$out/df-after.txt" 2>&1
  free -k > "$out/free-after.txt" 2>&1
  commit="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
  python3 -I "$here/discharges_log.py" --measure "$out" --result "$out/result.json" \
    --build-status "$build_status" --seconds "$seconds" --commit "$commit"
  exit 0
fi

case "$mode" in
  build|report|all) ;;
  *) echo "usage: discharge_check.sh scope BASE HEAD | discharge_check.sh [build|report|all|measure]" >&2
     exit 1 ;;
esac

if [ ! -f "$manifest" ]; then
  echo "discharge_check: no $manifest; run discharge_check.sh scope first" >&2
  exit 1
fi

# Module names of the added Lean files, checked again here although the scope gate already did.
modules="$(python3 -I - "$manifest" <<'PY'
import json, re, sys
m = json.load(open(sys.argv[1]))
ok = re.compile(r'ZInQKernel/Contrib/OneProof/(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean\Z')
for p in m.get('added', []):
    if p.endswith('.lean'):
        if not ok.match(p):
            sys.exit('discharge_check: bad module path in the manifest: %r' % p)
        print(p[:-5].replace('/', '.'))
PY
)" || exit 1

if [ "$mode" != report ]; then
  if [ "$mode" = all ] && [ -z "${DISCHARGE_NONCE:-}" ]; then
    echo "discharge_check: DISCHARGE_NONCE is not set" >&2
    exit 1
  fi
  targets="+ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges"
  for m in $modules; do
    targets="$targets +$m"
  done
  echo "== lake build $targets"
  date +%s > "$out/start"
  build_start=$(date +%s)
  # The nonce is never visible to the build.
  env -u DISCHARGE_NONCE ${limit[@]+"${limit[@]}"} ${timer[@]+"${timer[@]}"} lake build $targets 2>&1 \
    | tee "$out/build.log"
  build_status=${PIPESTATUS[0]}
  echo "$build_status" > "$out/build.status"
  echo "$(( $(date +%s) - build_start ))" > "$out/build.seconds"
  echo "$targets" > "$out/targets"
  if [ "$mode" = build ]; then
    exit "$build_status"
  fi
fi

# report
nonce="${DISCHARGE_NONCE:-}"
if [ -z "$nonce" ]; then
  echo "discharge_check: DISCHARGE_NONCE is not set; the report step needs it" >&2
  exit 1
fi
build_status="$(cat "$out/build.status" 2>/dev/null || echo 1)"
build_seconds="$(cat "$out/build.seconds" 2>/dev/null || echo 0)"
start="$(cat "$out/start" 2>/dev/null || date +%s)"
targets="$(cat "$out/targets" 2>/dev/null || echo unknown)"
num() { case "$1" in ''|*[!0-9]*) return 1 ;; esac; }
if ! num "$build_status" || ! num "$build_seconds" || ! num "$start"; then
  echo "discharge_check: unreadable build status files" >&2
  build_status=1
  build_seconds=0
  start="$(date +%s)"
fi

: > "$out/discharges.log"
: > "$out/report.log"
lean_args=""
lean_status="not run"
text_status="not run"
if [ "$build_status" -eq 0 ]; then
  {
    echo "import ZInQKernel.OneProof.Main"
    echo "import ZInQKernel.OneProof.Discharges"
    for m in $modules; do
      echo "import $m"
    done
  } > "$sb/imports.lean"
  { cat "$sb/imports.lean"; echo; echo "#discharges"; } > "$sb/Check.lean"
  { cat "$sb/imports.lean"; echo; grep -v '^import ' "$here/DischargesJson.lean"; } > "$sb/Report.lean"
  cp "$sb/Check.lean" "$sb/Report.lean" "$out/"
  echo "== lake env lean $sb/Check.lean (text output, display only)"
  env -u DISCHARGE_NONCE lake env lean "$sb/Check.lean" 2>&1 | tee "$out/discharges.log"
  text_status=${PIPESTATUS[0]}
  echo "== lake env lean $sb/Report.lean (the reporter)"
  lake env lean "$sb/Report.lean" > "$out/report.log" 2>&1
  lean_status=$?
  cat "$out/report.log"
  lean_args="--lean-status $lean_status"
fi

echo "== python3 scripts/one_proof/render_open.py --check (information only)"
env -u DISCHARGE_NONCE python3 -I scripts/one_proof/render_open.py --check 2>&1 | tee "$out/render.log"
render_status=${PIPESTATUS[0]}
seconds=$(( $(date +%s) - start ))

{
  echo "discharge check"
  cat "$manifest"
  echo
  echo "== lake build $targets (exit status $build_status, $build_seconds s)"
  cat "$out/build.log" 2>/dev/null
  echo "== #discharges, text output for display (exit status $text_status)"
  cat "$out/discharges.log"
  echo "== the reporter (exit status $lean_status)"
  cat "$out/report.log"
  echo "== render_open.py --check, information only (exit status $render_status)"
  cat "$out/render.log"
  echo "== total wall-clock: $seconds s"
} > "$out/check.log"

python3 -I "$here/discharges_log.py" "$out/report.log" --nonce "$nonce" --result "$out/result.json" \
  --manifest "$manifest" --build-log "$out/build.log" --build-status "$build_status" $lean_args \
  --text-log "$out/discharges.log" --time-file "$out/time.txt" \
  --render-status "$render_status" --seconds "$seconds" --build-seconds "$build_seconds" \
  | tee -a "$out/check.log"
exit "${PIPESTATUS[0]}"
