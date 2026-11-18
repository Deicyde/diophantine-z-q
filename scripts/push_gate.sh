#!/usr/bin/env bash
# Run before pushing a branch meant for main (agents and people alike).
# 1. Fetch main and merge it with HEAD in memory (git merge-tree): stop on conflicts.
# 2. Check the merged tree for board rows that main has and the merge would drop, and for rows that main does not have
#    and the merge would add, such as rows a fold removed that a branch built on an older main brings back
#    (scripts/guard/check_pr.py rows). List intended removals in REMOVES_ROWS="a, b" and intended additions (a new
#    hypothesis) in ADDS_ROWS="c, d", and on "Removes-rows:" and "Adds-rows:" lines of the pull request body.
set -euo pipefail
git fetch -q origin main
base=$(git rev-parse origin/main)
if ! out=$(git merge-tree --write-tree "$base" HEAD); then
  echo "push gate: HEAD conflicts with origin/main ($base). Merge main first:"
  echo "$out" | sed -n '2,40p'
  exit 1
fi
tree=$(echo "$out" | head -1)
python3 scripts/guard/check_pr.py rows --base "$base" --tree "$tree" \
  --removes "${REMOVES_ROWS:-}" --adds "${ADDS_ROWS:-}"
echo "push gate: ok against origin/main $base"
