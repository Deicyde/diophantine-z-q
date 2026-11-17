#!/usr/bin/env bash
# lane74b item 1: the chain gate's autofold check on the new Main (run after `lake build +ZInQKernel.OneProof.Main`).
#
# usage: bash scratch/lane74/gate.sh [REPO-DIR]
#
# 1. `autofold.py <spec> --dry-run` with a no-op spec (no discharge): it must parse Main.lean (frozenTarget written as
#    `theorem _root_.ZInQ.OneProof.frozenTarget` ... `) :` newline `ZInQ.FrozenTarget`, H bundles as `HDec.HSyn` binders,
#    one `ZInQKernel.OneProof.H.TailZ<k>` import), switch it (autofold re-parses the switched text and checks that the
#    other imports, e.g. MainGreenTao and DeRhamRange, and the binders survive) and write nothing to the tree.
# 2. The printed fold module (stdout without its first line) must compile against the built TailZ<k> and its top
#    theorem must have only the three standard axioms.
# Prints AUTOFOLD-DRYRUN-EXIT, TREE-UNCHANGED, GATEFOLD-EXIT, GATEFOLD-AXIOMS and finally GATE=ok or GATE=FAIL.
set -u
cd "${1:-.}" || exit 2
tmp="$(mktemp -d)"
echo '{"name": "gate-noop", "imports": [], "discharges": []}' > "$tmp/spec.json"
before="$(git status --porcelain)"
python3 scripts/one_proof/autofold.py "$tmp/spec.json" --dry-run > "$tmp/out.txt" 2> "$tmp/main-after.txt"
rc=$?; echo "AUTOFOLD-DRYRUN-EXIT=$rc"
after="$(git status --porcelain)"
if [ "$before" = "$after" ]; then echo "TREE-UNCHANGED=yes"; else echo "TREE-UNCHANGED=NO"; rc=1; fi
if [ $rc -ne 0 ]; then cat "$tmp/out.txt" "$tmp/main-after.txt" | tail -5; echo GATE=FAIL; exit 1; fi
tail -n +2 "$tmp/out.txt" > "$tmp/GateFold.lean"
lake env lean "$tmp/GateFold.lean" > "$tmp/lean.txt" 2>&1
lrc=$?; echo "GATEFOLD-EXIT=$lrc"
if grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$tmp/lean.txt" && ! grep -qi "sorry\|error" "$tmp/lean.txt"; then
  echo "GATEFOLD-AXIOMS=standard"
else
  echo "GATEFOLD-AXIOMS=NOT-STANDARD"; cat "$tmp/lean.txt" | head -20; lrc=1
fi
echo "(files in $tmp)"
if [ $lrc -eq 0 ]; then echo GATE=ok; else echo GATE=FAIL; exit 1; fi
