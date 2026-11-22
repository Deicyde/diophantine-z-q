#!/bin/bash
# Re-cut on a build host from current fork main onto upstream 964d7dd71 + #168 (dbaa4736f). Pushes nothing.
# Layout: ~/recut/cut (scripts), ~/recut/cutrepo (full clone of the fork), ~/recut/tauceti.
set -eu
export https_proxy=http://fwdproxy:8080 http_proxy=http://fwdproxy:8080
export PATH="$HOME/recut/pybin:$HOME/bin:$HOME/.elan/bin:$PATH"
C=~/recut/cut; R=~/recut/cutrepo; T=~/recut/tauceti  # C holds these tools
TAU=86b925445ee0dd6b6fa26d67fc45cfeb6fcdc60f
UP=964d7dd71f253091dbc5eac793b78cc56d1fcc73
PR168=dbaa4736f16fc9025040095728fb6fc5f66147b7
[ -d $R ] || git clone -q https://github.com/Deicyde/diophantine-z-q $R
[ -d $T ] || git clone -q https://github.com/Deicyde/TauCeti $T
git -C $T fetch -q origin $TAU 2>/dev/null || true
git -C $R fetch -q origin main recut/stack-1120 contract-clean/main-c1e4ed1b
git -C $R fetch -q https://github.com/elliotglazer/diophantine-z-q main refs/pull/168/head
git -C $R cat-file -e $UP && git -C $R cat-file -e $PR168 && git -C $R cat-file -e 44b001cfe353d80318b945c283fbada8285a85c1
FORK=$(git -C $R rev-parse origin/main); echo $FORK > $C/fork-main.txt
MT=$(git -C $R merge-tree --write-tree $UP $PR168 | head -1)
M=$(GIT_AUTHOR_NAME="Jack McCarthy" GIT_AUTHOR_EMAIL="Deicyde@users.noreply.github.com" GIT_COMMITTER_NAME="Jack McCarthy" GIT_COMMITTER_EMAIL="Deicyde@users.noreply.github.com" git -C $R commit-tree $MT -p $UP -p $PR168 -m "Merge upstream #168 (dbaa4736f) into main 964d7dd71 for the re-cut")
echo "M $M tree $MT (Mac M tree c0: see M-tree.txt)"; cat $C/M-tree.txt
cd $C
echo "start $(date) fork main $FORK"; uptime
ROUTE168=1 python3 -I target.py $R $M $FORK $T $TAU moved.txt target-h.json > target-h.log 2>&1; tail -12 target-h.log
ROUTE168=1 python3 -I batches.py $R target-h.json $T $TAU 44b001cf 600 outh > batches-h.log 2>&1
echo "UNRESOLVED: $(grep -c UNRESOLVED batches-h.log || true)"; tail -22 batches-h.log | cut -c1-200
python3 -I restack.py $R outh/batches.json target-h.json $UP $PR168 restack-h.json 2>&1 | tail -22
python3 -I -c "import json; j=json.load(open('restack-h.json')); json.dump({'batches':j['stack']}, open('restack-batches-h.json','w'), indent=1)"
[ -d wt ] || git -C $R worktree add -q --detach $C/wt $UP
python3 -I run_checks.py wt checker-964d.py restack-batches-h.json checks-h.json 2>&1 | cut -c1-240
echo "done $(date)"
