#!/bin/bash
# usage: net.sh CMD...  — (in the caller's cwd) run a git network command in a fresh tmux window (where github is reachable), wait, print output.
export PATH="$HOME/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
W=$(pwd); f=$(mktemp /tmp/lead6-net.XXXXXX); q=$(printf '%q ' "$@")
tmux new-window -d -n lead-net "bash -c 'cd $W && { $q; } > $f 2>&1; echo NET-EXIT=\$? >> $f'"
timeout ${NET_TIMEOUT:-300} bash -c "until grep -q '^NET-EXIT=' $f 2>/dev/null; do sleep 2; done"
cat $f; e=$(sed -n 's/^NET-EXIT=//p' $f); rm -f $f; exit ${e:-124}
