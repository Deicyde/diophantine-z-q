#!/usr/bin/env bash
# Run one Lean command after checking the devserver limits.
set -euo pipefail
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime
free -g
load=$(cut -d' ' -f1 /proc/loadavg)
available=$(free -g | awk '$1 == "Mem:" { print $7 }')
if awk -v hostload="$load" -v mem="$available" 'BEGIN { exit !(hostload > 150 || mem < 20) }'; then
  echo 'Lean held: host load or memory threshold exceeded' >&2
  exit 75
fi
exec lake env lean "$@"
