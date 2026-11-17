#!/bin/bash
# igusa-drop: the post-fold checks, one Lean process at a time (adapted from scratch/fold-b105/run_checks.sh).
# Usage, from the repository root after `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`:
#   bash scratch/igusa-drop/run_checks.sh BASE_BUILD_DIR
# BASE_BUILD_DIR = a worktree root whose .lake/build holds the base (pre-fold) oleans, for the hash guard's base dump.
set -u
BASE=$1
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
D=scratch/igusa-drop
# hash guard: base dump against the base oleans, then the folded dump
LP=$(lake env printenv LEAN_PATH | sed "s#$PWD/.lake/build#$BASE/.lake/build#g")
LEAN_PATH=$LP lean $D/DumpCompact.lean > $D/dump-base.txt 2>&1; tail -1 $D/dump-base.txt
mv $D/compact_hashes.txt $D/hashes_base.txt
lake env lean $D/DumpCompact.lean > $D/dump-fold.txt 2>&1; tail -1 $D/dump-fold.txt
mv $D/compact_hashes.txt $D/hashes_fold.txt
python3 $D/cmp_hashes.py hashes_base.txt hashes_fold.txt > $D/cmp_hashes.txt; cat $D/cmp_hashes.txt
lake env lean $D/FoldCheck.lean > $D/FoldCheck.txt 2>&1; grep "axioms\|closure\|contains\|error" $D/FoldCheck.txt
lake env lean scripts/one_proof/OpenStatements.lean > $D/OpenStatements.txt 2>&1; tail -3 $D/OpenStatements.txt
python3 scripts/one_proof/render_open.py | tail -1
lake env lean scratch/contrib-kit/DischargesTest.lean > scratch/contrib-kit/DischargesTest-output.txt 2>&1; grep -c DISCHARGES scratch/contrib-kit/DischargesTest-output.txt; grep -n "error" scratch/contrib-kit/DischargesTest-output.txt | head -3
python3 scripts/one_proof/render_open.py | tail -1
python3 scripts/one_proof/render_open.py --check | tail -1
python3 scripts/one_proof/frontier_crosswalk.py | head -1
python3 scripts/one_proof/frontier_crosswalk.py --check | tail -1
timeout 1100 uvx --offline --from git+https://github.com/facebookresearch/autoform-bot.git@46b46d6defaa19c618341e05c4cc0d819072a03d autoform check blueprint --lean-root . > $D/autoform-check.txt 2>&1; echo "autoform exit $?"; tail -3 $D/autoform-check.txt
