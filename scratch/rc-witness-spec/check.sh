#!/usr/bin/env bash
# Check one file at a time against compiled imports from the stage construction.
set -euo pipefail
: "${RC_WITNESS_STAGE_LIB:?Set this to the compiled stage dependency directory}"
up=$(uptime)
mem=$(free -g)
printf '%s\n%s\n' "$up" "$mem"
load=$(awk -F'load average: ' '{print $2+0}' <<<"$up")
available=$(awk '/^Mem:/ {print $NF}' <<<"$mem")
if awk -v work_load="$load" -v available="$available" 'BEGIN {exit !(work_load > 120 || available < 20)}'; then
  echo 'Lean held by the load/memory limit' >&2
  exit 1
fi
lake env bash -c 'export LEAN_PATH="$RC_WITNESS_STAGE_LIB:$LEAN_PATH"; exec lean -j1 "$@"' lean "$@"
