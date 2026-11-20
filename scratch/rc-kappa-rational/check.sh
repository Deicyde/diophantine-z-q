#!/usr/bin/env bash
set -euo pipefail
root="$PWD"
out="$(mktemp -d)"
trap 'rmdir "$out"' EXIT
# Use the compiled dependencies from the base and the checked branch model.
export LEAN_PATH="${RC_BASE_OBJECTS:?}:${RC_BRANCH_OBJECTS:?}:${RC_CLASSIFY_OBJECTS:?}:$root/.lake/build/lib/lean"
for pkg in "$root"/.lake/packages/*; do
  LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
done
export ELAN_TOOLCHAIN="$(cat lean-toolchain)"
for file in "$@"; do
  up="$(uptime)"
  mem="$(free -g)"
  printf '%s\n%s\n' "$up" "$mem"
  awk -v up="$up" '/^Mem:/{i=split(up,a,"load average: "); split(a[i],l,",");
    if (l[1]+0>120 || $NF<20) exit 1; ok=1} END {if (!ok) exit 1}' <<< "$mem" ||
    { echo "Blocked by resource limit"; exit 1; }
  (cd "$out" && lake env lean -j1 --root="$root" -DautoImplicit=false "$root/$file")
done
