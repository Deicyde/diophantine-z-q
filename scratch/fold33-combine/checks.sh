#!/bin/bash
# fold33-combine: the per-field checks, one Lean process at a time. Usage: scratch/fold33-combine/checks.sh TAG
set -u
cd "$(git rev-parse --show-toplevel)"
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
T=$1; O=scratch/fold33-combine
DUMP_OUT=$O/hashes_$T.txt lake env lean $O/DumpCompact.lean > $O/dump_$T.out 2>&1; echo "dump $?"
lake env lean $O/ClosureCheck.lean > $O/closure_$T.txt 2>&1; echo "closure $?"
lake env lean scripts/one_proof/OpenStatements.lean > $O/openstatements_$T.out 2>&1; echo "openstatements $?"
lake env lean scratch/contrib-kit/DischargesTest.lean > scratch/contrib-kit/DischargesTest-output.txt 2>&1; echo "dischargestest $?"
echo DONE
