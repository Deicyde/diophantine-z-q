#!/bin/bash
# fold-b116: the post-fold checks, one Lean process at a time (adapted from fold-b105/igusa-drop run_checks.sh).
# Usage, from the repository root after `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges <new modules>`:
#   bash scratch/fold-b116/run_checks.sh K PREV      (K = fold number; PREV = previous dump in /tmp/fb116, e.g. hashes_fold0.txt)
set -u
K=$1; PREV=$2
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
D=scratch/fold-b116
mkdir -p /tmp/fb116
lake env lean $D/DumpCompact.lean > /tmp/fb116/dump$K.txt 2>&1; tail -1 /tmp/fb116/dump$K.txt
mv $D/compact_hashes.txt /tmp/fb116/hashes_fold$K.txt
cp /tmp/fb116/$PREV $D/_a.txt; cp /tmp/fb116/hashes_fold$K.txt $D/_b.txt
python3 $D/cmp_hashes.py _a.txt _b.txt > $D/cmp_fold$K.txt; rm $D/_a.txt $D/_b.txt; head -20 $D/cmp_fold$K.txt
lake env lean $D/FoldCheck.lean > $D/FoldCheck-fold$K.txt 2>&1; grep "axioms\|closure\|contains\|error\|field check\|type differs" $D/FoldCheck-fold$K.txt
lake env lean scripts/one_proof/OpenStatements.lean > $D/OpenStatements-fold$K.txt 2>&1; tail -3 $D/OpenStatements-fold$K.txt
python3 scripts/one_proof/render_open.py | tail -1
lake env lean scratch/contrib-kit/DischargesTest.lean > scratch/contrib-kit/DischargesTest-output.txt 2>&1; grep -c DISCHARGES scratch/contrib-kit/DischargesTest-output.txt; grep -n "error" scratch/contrib-kit/DischargesTest-output.txt | head -3
python3 scripts/one_proof/render_open.py | tail -1
python3 scripts/one_proof/render_open.py --check | tail -1
python3 scripts/one_proof/frontier_crosswalk.py | head -1
python3 scripts/one_proof/frontier_crosswalk.py --check | tail -1
timeout 1100 uvx --offline --from git+https://github.com/facebookresearch/autoform-bot.git@46b46d6defaa19c618341e05c4cc0d819072a03d autoform check blueprint --lean-root . > $D/autoform-check-fold$K.txt 2>&1; echo "autoform exit $?"; tail -3 $D/autoform-check-fold$K.txt
bash scratch/lane74/gate.sh 2>&1 | tail -6 | tee $D/gate-fold$K.txt
