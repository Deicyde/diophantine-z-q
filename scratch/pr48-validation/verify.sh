#!/usr/bin/env bash
# Run in an isolated Linux checkout with the pinned main build restored.
# Writes the fold to that checkout only after checking the witness.
set -euo pipefail

mkdir -p "$1"
out=$(cd "$1" && pwd)
check_dir=scratch/pr48-validation
witness=ZInQ.Contrib.CloudB3SC5DeligneSerre.dsThm966Printed
entry=ZInQKernel.Contrib.OneProof.DSThm966PrintedProof
main=ZInQKernel.OneProof.Main
reporter=ZInQKernel.OneProof.Discharges

git rev-parse HEAD > "$out/source-commit.txt"
git show HEAD:docs/one-proof/open-statements.json > "$out/before.json"

/usr/bin/time -v -o "$out/witness-build.time.txt" \
  lake --fail-fast build "+$entry" "+$main" "+$reporter" 2>&1 | tee "$out/witness-build.log"

lake env lean "$check_dir/Axioms.lean" 2>&1 | tee "$out/witness-axioms.txt"
for theorem in "$witness" ZInQ.Contrib.CloudB3SC5DeligneSerre.dsThm966_proof; do
  python3 -I scripts/one_proof/check_axioms.py "$out/witness-axioms.txt" "$theorem"
done
lake env lean "$check_dir/Discharges.lean" > "$out/discharges.txt"

python3 -I - "$out/discharges.txt" "$witness" <<'PY'
import re
import sys
from pathlib import Path

log = " ".join(Path(sys.argv[1]).read_text().split())
theorem = re.escape(sys.argv[2])
pattern = r"DISCHARGES \[[^]]*\.dsThm966Printed(?:[,\]])[^[]*? by " + theorem
pattern += r" still assumes: \[\]"
if not re.search(pattern, log):
    raise SystemExit("The witness did not discharge dsThm966Printed without another premise.")
print("Lean verified the exact hypothesis discharge with no new premise.")
PY

lake env lean scratch/one-proof/DumpCompact.lean > "$out/before-hash-report.txt"
cp scratch/one-proof/compact_hashes.txt "$out/hashes-before.txt"

python3 -B scripts/one_proof/autofold.py "$check_dir/fold.json" | tee "$out/autofold.txt"
/usr/bin/time -v -o "$out/fold-build.time.txt" \
  lake --fail-fast build "+$main" "+$reporter" 2>&1 | tee "$out/fold-build.log"

printf '%s\n' "import $main" '#print axioms ZInQ.OneProof.frozenTarget' > "$out/Headline.lean"
lake env lean "$out/Headline.lean" 2>&1 | tee "$out/headline-axioms.txt"
python3 -I scripts/one_proof/check_axioms.py "$out/headline-axioms.txt"
lake env lean scratch/one-proof/DumpCompact.lean > "$out/after-hash-report.txt"
cp scratch/one-proof/compact_hashes.txt "$out/hashes-after.txt"
python3 -I - "$out/hashes-before.txt" "$out/hashes-after.txt" <<'PY'
import sys
from pathlib import Path

def hashes(file):
    return dict(line.split(maxsplit=1) for line in Path(file).read_text().splitlines() if line)

before, after = [hashes(file) for file in sys.argv[1:]]
target = "ZInQ.OneProof.frozenTarget"
assert target in before and target in after and before[target] != after[target]
different = sorted(name for name in before if before[name] != after.get(name))
if different != [target]:
    raise SystemExit("Unexpected changes in existing OneProof declarations: " + ", ".join(different))
print("Only frozenTarget changed among existing OneProof declarations.")
PY

lake env lean scripts/one_proof/OpenStatements.lean
cp docs/one-proof/open-statements.json "$out/after.json"

python3 -I - "$out/before.json" "$out/after.json" <<'PY'
import json
import sys
from pathlib import Path

before, after = [json.loads(Path(file).read_text()) for file in sys.argv[1:]]
rows = before["hypotheses"]
removed = "dsThm966Printed"
assert sum(row["field"] == removed for row in rows) == 1
expected = [
    dict(row, bundle="OpenResearchLeaves70") if row["bundle"] == "OpenResearchLeaves69" else row
    for row in rows if row["field"] != removed
]
assert before["root"] == after["root"]
assert after["hypotheses"] == expected
assert before["count"] == len(rows) == after["count"] + 1 == 32
assert after["count"] == len(expected)
print(f"Verified catalog: {before['count']} to {after['count']} open hypotheses; removed only {removed}.")
PY

python3 -B scripts/one_proof/render_open.py
python3 -B scripts/one_proof/render_open.py --check
git add -N ZInQKernel/OneProof/H/TailZ96.lean
git diff --check
git diff --binary -- ZInQKernel/OneProof docs/one-proof > "$out/fold.patch"
