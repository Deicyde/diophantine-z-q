#!/bin/bash
# h21-combine: build and Lean checks, one Lean process at a time. Usage: scratch/h21-combine/checks.sh TAG
set -u
cd "$(git rev-parse --show-toplevel)"
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
T=$1; O=scratch/h21-combine
lake build ZInQKernel.Contrib.OneProof.TYZThm21GChar ZInQKernel.Contrib.OneProof.H21Lcal ZInQKernel.Contrib.OneProof.TYZThm21GP +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges > $O/build_$T.txt 2>&1; echo "build $?"
DUMP_OUT=$O/hashes_$T.txt lake env lean $O/DumpCompact.lean > $O/dump_$T.out 2>&1; echo "dump $?"
lake env lean $O/ClosureCheck.lean > $O/closure_$T.txt 2>&1; echo "closure $?"
lake env lean scripts/one_proof/OpenStatements.lean > $O/openstatements_$T.out 2>&1; echo "openstatements $?"
lake env lean scratch/contrib-kit/DischargesTest.lean > scratch/contrib-kit/DischargesTest-output.txt 2>&1; echo "dischargestest $?"
echo DONE
