#!/bin/bash
# Check a work file that does `import PGBase` (run from the repository root after build_base.sh).
D=scratch/period-glue
LEAN_PATH=$(lake env printenv LEAN_PATH):$D/olean lean "$@"
