#!/bin/bash
# usage: additive-fold.sh N HEADSHA EXPECTED_COUNT MSGFILE
# Make ~/dzq-wt/integrate-wN at HEADSHA, merge origin/main, append an AllContrib import for every .lean the branch adds
# under ZInQKernel/Contrib/ (vs its merge base with main), check render/gen unchanged, commit with MSGFILE. Does not push.
set -e
N=$1; H=$2; EXP=$3; MSG=$4; W=$HOME/dzq-wt/integrate-w$N
cd $HOME/dzq
git worktree add -q -b wip/integrate-w$N $W $H
cd $W
MB=$(git merge-base origin/main $H)
git diff --name-only --diff-filter=A $MB $H -- 'ZInQKernel/Contrib/*.lean' | sed 's#[.]lean$##; s#/#.#g' > /tmp/w$N-mods.txt
C=$(wc -l < /tmp/w$N-mods.txt); [ "$C" = "$EXP" ] || { echo "COUNT MISMATCH: $C vs $EXP"; exit 3; }
git merge -q --no-edit -m "Merge fork main $(git rev-parse --short=9 origin/main) into w$N" origin/main
F=ZInQKernel/Contrib/AllContrib.lean
while read m; do grep -qx "import $m" $F && { echo "ALREADY: $m"; exit 4; }; echo "import $m" >> $F; done < /tmp/w$N-mods.txt
python3 -I scripts/one_proof/render_open.py > /dev/null 2>&1 || true
python3 -I scripts/one_proof/vault_chapter/gen.py > /dev/null
echo "changed besides AllContrib:"; git status --short | grep -v "AllContrib.lean" || true
python3 -I scripts/one_proof/render_open.py --check | tail -1
git add $F && git commit -q -F $MSG
git log --format='%h %p %s' -1 | cut -c1-120
echo "added $C imports"
