#!/usr/bin/env bash
# Compile the glue-descent drafts one file at a time (run from the worktree root).
# Oleans go to scratch/glue-descent/.lake/out (gitignored) so that later files can import them.
set -euo pipefail
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=scratch/glue-descent
OUT=$D/.lake/out
mkdir -p $OUT/GlueDescent
for f in ProjRep B1Quat Cochain Constants Chi B2Glue B2Assembly B3Assembly; do
  echo "== $f"
  lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean -o $OUT/GlueDescent/$f.olean $D/$f.lean" 2>&1 \
    | grep -E "error|sorry|depends on axioms" || true
done
