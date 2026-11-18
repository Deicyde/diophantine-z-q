#!/usr/bin/env bash
# Run from an isolated checkout of the fold. With a warm checkout argument,
# reuse its built imports and keep compiled modules in a private overlay.
# Pass --built if the two Lake targets have already been built in this checkout.
set -euo pipefail

field=deRhamVpAbVarDirect
root=$(git rev-parse --show-toplevel)
cd "$root"
git_dir=$(git rev-parse --absolute-git-dir)
if [[ -n ${ZQ_FOLD_EVIDENCE:-} ]]; then
  mkdir -p "$ZQ_FOLD_EVIDENCE"
  out=$(cd "$ZQ_FOLD_EVIDENCE" && pwd)
else
  out=$(mktemp -d "$git_dir/derham-verify.XXXXXX")
fi
base=dcc3d7723c0cfe485cb9dbc05ff821533e7504d2
printf 'Checking %s (evidence: %s)\n' "$(git rev-parse HEAD)" "$out"

cat > "$out/ProofAxioms.lean" <<'LEAN'
import ZInQKernel.OneProof.Main

#print axioms ZInQ.OneProof.frozenTarget
#print axioms HDec.HSyn.sixContactMin_of_open85
#print axioms HDec.HSyn.openResearchLeaves65_of_OpenResearchLeaves66
#check @ZInQ.OneProof.frozenTarget
LEAN

if [[ $# -eq 1 && $1 != --built ]]; then
  warm=$(cd "$1" && pwd)
  warm_commit=$(git -C "$warm" rev-parse HEAD)
  paths=(ZInQKernel ZInQKernel.lean lean ThirdParty lakefile.toml lake-manifest.json lean-toolchain)
  git diff --exit-code "$base" "$warm_commit" -- "${paths[@]}"
  git -C "$warm" diff HEAD --exit-code -- "${paths[@]}"
  test -f "$warm/.lake/build/lib/lean/ZInQKernel/OneProof/H/TailZ91.olean"
  test -f "$warm/.lake/build/lib/lean/ZInQKernel/OneProof/Discharges.olean"
  overlay="$out/oleans"
  mkdir -p "$overlay/ZInQKernel/OneProof/H"
  (
    cd "$warm"
    lake env bash -euo pipefail -c '
      cd "$1"
      export LEAN_PATH="$2:${LEAN_PATH:?missing path from Lake}"
      lean -o "$2/ZInQKernel/OneProof/H/TailZ92.olean" ZInQKernel/OneProof/H/TailZ92.lean
      lean -o "$2/ZInQKernel/OneProof/Main.olean" ZInQKernel/OneProof/Main.lean
      lean "$3/ProofAxioms.lean" | tee "$3/axioms.txt"
      lean scripts/one_proof/OpenStatements.lean
      lean scratch/contrib-kit/DischargesTest.lean > "$3/discharges.txt"
    ' _ "$root" "$overlay" "$out"
  ) 2>&1 | tee "$out/lean.txt"
elif [[ $# -eq 0 || ( $# -eq 1 && $1 == --built ) ]]; then
  if [[ $# -eq 0 ]]; then
    lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges 2>&1 | tee "$out/build.txt"
  fi
  lake env lean "$out/ProofAxioms.lean" | tee "$out/axioms.txt"
  lake env lean scripts/one_proof/OpenStatements.lean
  lake env lean scratch/contrib-kit/DischargesTest.lean > "$out/discharges.txt"
else
  echo "Usage: $0 [warm-checkout | --built]" >&2
  exit 2
fi

for thm in ZInQ.OneProof.frozenTarget HDec.HSyn.sixContactMin_of_open85 \
    HDec.HSyn.openResearchLeaves65_of_OpenResearchLeaves66; do
  python3 -I scripts/one_proof/check_axioms.py "$out/axioms.txt" "$thm"
done
git show "$base:docs/one-proof/open-statements.json" > "$out/baseline.json"
python3 -I - "$out/baseline.json" "$field" <<'PY'
import json
import sys
from pathlib import Path

baseline = json.loads(Path(sys.argv[1]).read_text())
current = json.loads(Path("docs/one-proof/open-statements.json").read_text())
removed = sys.argv[2]
rows = baseline["hypotheses"]
assert sum(row["field"] == removed for row in rows) == 1
expected = [
    dict(row, bundle="OpenResearchLeaves66") if row["bundle"] == "OpenResearchLeaves65" else row
    for row in rows if row["field"] != removed
]
assert current["root"] == baseline["root"]
assert current["hypotheses"] == expected
assert current["count"] == len(expected) == baseline["count"] - 1
print(f"Verified in Lean: only {removed} removed ({baseline['count']} → {current['count']} total).")
PY
test "$(grep -Fc '#discharges: 34 open hypotheses' "$out/discharges.txt")" -gt 0
cp "$out/discharges.txt" scratch/contrib-kit/DischargesTest-output.txt
python3 -I - "$field" <<'PY'
import sys
from pathlib import Path

path = Path("docs/one-proof/kinds.tsv")
rows = path.read_text().splitlines(keepends=True)
kept = [row for row in rows if row.split("\t", 2)[1] != sys.argv[1]]
assert len(rows) - len(kept) == 1
path.write_text("".join(kept))
PY
python3 scripts/one_proof/render_open.py
python3 scripts/one_proof/render_open.py --check
if grep -Fiq "$field" docs/one-proof/frontier-crosswalk.tsv; then
  echo "An existing frontier ID references $field. Check the crosswalk." >&2
  exit 1
fi
git diff --check
git diff --stat
git diff --binary > "$out/generated.patch"
