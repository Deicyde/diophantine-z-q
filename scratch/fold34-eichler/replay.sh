#!/bin/bash
# fold34-eichler: replay the gonzalezRotgerProp56X6 fold (eichler-bound bypass) on a head that has further folds.
# Run from the repository root on a clean tree whose Main.lean does not yet contain the fold, with the Contrib files
# ZInQKernel/Contrib/OneProof/{R5fpCountLe,R5fpCountLeHF,GR56Lattice,EichlerBound/*}.lean present (merged from
# wip/fold34-eichler). One Lean process at a time. Steps:
#   1. build Main (the head) and the Contrib module;
#   2. the taint list of the head (every declaration of frozenTarget's proof that reads a count field or takes a
#      bundle carrying one; also every structure with a count field, used or not);
#   3. gen.py: OneProof/H/EichlerBoundCopy.lean (the copy, count fields typed GR56.R5fpCountLe);
#   4. top.py: the next TailZ module (research bundle without gonzalezRotgerProp56X6) and the Main patch;
#   5. kinds.tsv / claims.tsv rows dropped;
#   6. build; then the usual checks (scratch/fold34-eichler/checks.sh TAG, render_open.py, frontier_crosswalk.py,
#      autoform check blueprint).
set -eu
cd "$(git rev-parse --show-toplevel)"
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
O=scratch/fold34-eichler
lake build +ZInQKernel.OneProof.Main ZInQKernel.Contrib.OneProof.R5fpCountLeHF
lake env lean $O/Taint.lean > $O/taint_replay.txt 2>&1
python3 $O/gen/gen.py $O/taint_replay.txt ZInQKernel/OneProof/H/EichlerBoundCopy.lean
python3 $O/gen/top.py
sed -i '/^research\tgonzalezRotgerProp56X6\t/d' docs/one-proof/kinds.tsv
sed -i '/^gonzalezRotgerProp56X6\t/d' docs/one-proof/claims.tsv
NEW=$(grep -oE '^import ZInQKernel\.OneProof\.H\.TailZ[0-9]+' ZInQKernel/OneProof/Main.lean | sed 's/^import //')
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.EichlerBoundCopy $NEW
echo "replayed: $NEW"
