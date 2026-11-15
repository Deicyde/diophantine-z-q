#!/bin/bash
# usage: scratch/rayclass-cft/chk.sh File.lean [olean-out]   (one Lean process; LEAN_PATH + /tmp/rc-olean)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
LP=$(lake env printenv LEAN_PATH)
if [ -n "$2" ]; then OUT="-o /tmp/rc-olean/$2.olean"; else OUT=""; fi
LEAN_PATH="$LP:/tmp/rc-olean" timeout 3000 lean $OUT "scratch/rayclass-cft/$1"
