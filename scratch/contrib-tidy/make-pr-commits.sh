#!/usr/bin/env bash
# Build the two proof-only PR commits on top of upstream main (a5937595, the merge of PR #36)
# with git plumbing, without touching the working tree or creating refs (pass a branch name as
# the second argument of `mk` to create one). Each commit adds only `.lean` files under
# ZInQKernel/Contrib/, which is what check_kernel_contract.py routes to proof-only review.
# Usage: scratch/contrib-tidy/make-pr-commits.sh [SOURCE_COMMIT] [BRANCH1 BRANCH2]
set -euo pipefail
SRC=${1:-HEAD}
BASE=a5937595cde3e3db00975b81e5171cdef92c801a
export GIT_AUTHOR_NAME="Jack McCarthy"
export GIT_AUTHOR_EMAIL="Deicyde@users.noreply.github.com"
export GIT_COMMITTER_NAME="$GIT_AUTHOR_NAME"
export GIT_COMMITTER_EMAIL="$GIT_AUTHOR_EMAIL"
export GIT_AUTHOR_DATE="2026-11-13T00:00:00-0800"
export GIT_COMMITTER_DATE="$GIT_AUTHOR_DATE"
mk() {  # mk MESSAGE BRANCH PATHSPEC...
  local msg=$1 br=$2; shift 2
  local idx; idx=$(mktemp); rm -f "$idx"
  GIT_INDEX_FILE=$idx git read-tree "$BASE"
  git ls-tree -r "$SRC" -- "$@" | while read -r mode type obj path; do
    GIT_INDEX_FILE=$idx git update-index --add --cacheinfo "$mode,$obj,$path"
  done
  local tree; tree=$(GIT_INDEX_FILE=$idx git write-tree); rm -f "$idx"
  local c; c=$(echo "$msg" | git commit-tree "$tree" -p "$BASE")
  [ -n "$br" ] && git branch -f "$br" "$c" >/dev/null
  echo "$c"
}
mk "Contrib: prove HeckeContinuation and FunctionalEquation5 (Gauss's point count, Hecke theta)" \
  "${2:-}" ZInQKernel/Contrib/HeckeFE ZInQKernel/Contrib/GaussFE ZInQKernel/Contrib/HeckeAll
mk "Contrib: coefficients, Hasse bound and convergence of L(C_d, s); TYZInputs iff reading A" \
  "${3:-}" ZInQKernel/Contrib/PSide
