#!/bin/bash
# Compile one file with the prebuilt oleans of ~/dzq-check2 (same commit 5da857b0 for ZInQKernel/)
# plus private oleans in ~/rs-olean (TailY, compiled out of tree). Usage: chk.sh FILE [-o OUT.olean]
P=${CHECKOUT:-$HOME/dzq-check2}/.lake/packages
LP=$P/Cli/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/aesop/.lake/build/lib/lean:$P/proofwidgets/.lake/build/lib/lean:$P/importGraph/.lake/build/lib/lean:$P/LeanSearchClient/.lake/build/lib/lean:$P/plausible/.lake/build/lib/lean:$P/mathlib/.lake/build/lib/lean:${CHECKOUT:-$HOME/dzq-check2}/lean/.lake/build/lib/lean:${RS_LIB:-$HOME/rs-lib}
uptime; free -g | sed -n 2p
LEAN_PATH=$LP /usr/bin/time -f "%e s %M KB" $HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean "$@"
