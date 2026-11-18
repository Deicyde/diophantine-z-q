#!/usr/bin/env bash
# Handoff from the existing devserver login for the #14 de Rham fold.
set -euo pipefail

repo=https://github.com/Deicyde/diophantine-z-q.git
branch=codex/derham-height-fold
patch=0eb82537d60c6e4d77606a84d7c7d531c94296a2
runner=a2d16081b9fb65266e732e8d8a78f9e844b61424
anchor=be73b91c5d005f166deadd2b4a7d70b1a0d53ad5
paths=(ZInQKernel ZInQKernel.lean lean ThirdParty lakefile.toml lake-manifest.json lean-toolchain)
export PATH="$HOME/.elan/bin:$PATH"

if [[ $(hostname -s) != devvm19145 ]]; then
  echo "Run this from Devserver corral 7 (devvm19145)." >&2
  exit 1
fi
if [[ $# -gt 1 ]]; then
  echo "Usage: bash $0 [warm-checkout]" >&2
  exit 2
fi
uptime
free -h
df -h "$HOME"
check_resources() {
  if ! awk '
    FNR == NR { load = $1 + 0; next }
    $1 == "MemAvailable:" { available = $2 }
    $1 == "SwapTotal:" { total = $2 }
    $1 == "SwapFree:" { free = $2 }
    END { exit !(load <= 40 && available >= 24 * 1024 * 1024 && total - free <= 8 * 1024 * 1024) }
  ' /proc/loadavg /proc/meminfo; then
    echo "Holding: load > 40, over 8 GiB of swap, or under 24 GiB of available memory." >&2
    return 1
  fi
  if ps -u "$(id -u)" -o stat=,comm= | awk '$1 !~ /^Z/ && $2 ~ /^(lean|lake)$/ { seen = 1 } END { exit !seen }'; then
    echo "Holding: another Lean or Lake process is active on this account." >&2
    return 1
  fi
  if ! df -Pk "$HOME" | awk 'NR == 2 { exit !($4 >= 2 * 1024 * 1024) }'; then
    echo "Holding: under 2 GiB available for the isolated checkout." >&2
    return 1
  fi
}
check_resources

is_warm() {
  local candidate=$1
  test -s "$candidate/.lake/build/lib/lean/ZInQKernel/OneProof/H/TailZ87.olean" &&
    test -s "$candidate/.lake/build/lib/lean/ZInQKernel/OneProof/Discharges.olean" &&
    git -C "$candidate" diff --quiet "$anchor" HEAD -- "${paths[@]}" &&
    git -C "$candidate" diff --quiet HEAD -- "${paths[@]}"
}
warm=
if [[ $# -eq 1 ]]; then
  if is_warm "$1"; then warm=$(cd "$1" && pwd); fi
else
  while IFS= read -r candidate; do
    if is_warm "$candidate"; then warm=$(cd "$candidate" && pwd); break; fi
  done < <(
    git -C "$HOME/dzq" worktree list --porcelain 2>/dev/null | sed -n 's/^worktree //p' || true
    printf '%s\n' "$HOME"/dzq-check* "$HOME"/dzq-wt/* "$HOME"/dzq-work/* "$HOME"/dzq
  )
fi
if [[ -z $warm ]]; then
  echo "No clean warm checkout matches the C8 baseline $anchor. Pass a matching checkout as the argument." >&2
  exit 1
fi
printf 'Warm imports: %s (%s)\n' "$warm" "$(git -C "$warm" rev-parse --short HEAD)"

task=$(mktemp -d "$HOME/dzq-derham-check.XXXXXX")
printf 'Isolated checkout and evidence: %s\n' "$task"
git clone -q --shared --no-checkout -- "$warm" "$task"
cd "$task"
git remote set-url origin "$repo"
git fetch -q --no-tags origin "$patch" "$runner"
git checkout -q --detach "$patch"
git show "$runner:scratch/fold-derham-vp/check.sh" > .git/verify-fold.sh

check_resources
export ZQ_FOLD_EVIDENCE="$task/.git/evidence"
mkdir -p "$ZQ_FOLD_EVIDENCE"
nice -n 10 bash .git/verify-fold.sh "$warm" 2>&1 | tee "$ZQ_FOLD_EVIDENCE/run.txt"

report=scratch/fold-derham-vp/axioms.txt
mkdir -p "$(dirname "$report")"
{
  printf 'Lean source commit: %s\n' "$patch"
  cat "$ZQ_FOLD_EVIDENCE/axioms.txt"
} > "$report"
git add -- "$report" docs/one-proof/{open-statements.json,kinds.tsv,OPEN.md,pages-wanted.md} \
  docs/one-proof/CONTRIBUTING.md STATUS.md scratch/contrib-kit/DischargesTest-output.txt
git diff --cached --check
git diff --exit-code
git -c user.name=Deicyde -c user.email=37917934+Deicyde@users.noreply.github.com \
  commit -m 'Verify the de Rham fold and refresh the open hypothesis catalog'
REMOVES_ROWS=deRhamVpAbVarDirect bash scripts/push_gate.sh

# Update only the contribution's branch. A concurrent update fails normally.
if command -v gh >/dev/null && gh auth status --hostname github.com >/dev/null 2>&1; then
  git -c credential.helper= -c 'credential.https://github.com.helper=!gh auth git-credential' \
    push origin "HEAD:refs/heads/$branch"
else
  git push origin "HEAD:refs/heads/$branch"
fi
printf 'Verified and pushed %s; evidence in %s\n' "$(git rev-parse HEAD)" "$ZQ_FOLD_EVIDENCE"
