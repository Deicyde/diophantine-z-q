#!/bin/bash
# usage: gen-json.sh N REF [discharges]  — in ~/dzq-check2 at REF: build OneProof Main+Discharges, run OpenStatements.lean
# (copy to ~/dzq-runs/wN-gen/open-statements.json), optionally DischargesTest.lean, and #check frozenTarget.
# Holds chain.lock; one Lean job at a time, MemoryMax=60G. Run from a tmux window.
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
N="$1"; REF="$2"; D=$HOME/dzq-runs/w$N-gen; mkdir -p $D; rm -f $D/status
exec 9> "$HOME/dzq-runs/chain.lock"; flock -n 9 || { echo "chain lock held" > $D/status; exit 1; }
cd $HOME/dzq-check2 && git checkout -q -f --detach "$REF" || { echo checkout-failed > $D/status; exit 1; }
git log --oneline -1 > $D/head.txt
S="systemd-run --user --scope -q -p MemoryMax=60G env LEAN_NUM_THREADS=16"
$S lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges > $D/build.log 2>&1; echo "BUILD-EXIT=$?" >> $D/build.log
$S lake env lean scripts/one_proof/OpenStatements.lean > $D/openstatements.log 2>&1; echo "OS-EXIT=$?" >> $D/openstatements.log
cp docs/one-proof/open-statements.json $D/open-statements.json
if [ "$3" = discharges ]; then
  $S lake env lean scratch/contrib-kit/DischargesTest.lean > $D/DischargesTest-output.txt 2>&1; echo "$?" > $D/dt-exit
fi
printf 'import ZInQKernel.OneProof.Main\n#check @ZInQ.OneProof.frozenTarget\n' > scratch/gen-json-check.lean
$S lake env lean scratch/gen-json-check.lean > $D/check.log 2>&1; echo "CHK-EXIT=$?" >> $D/check.log
rm -f scratch/gen-json-check.lean
git checkout -q -- docs/one-proof/open-statements.json
echo done > $D/status
