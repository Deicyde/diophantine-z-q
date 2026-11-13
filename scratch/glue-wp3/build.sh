#!/usr/bin/env bash
# Compile glue-wp3 one file at a time (run from the worktree root).
# Cochain..B3Assembly are verbatim copies of scratch/glue-descent/ (glue-descent's B2-B3);
# WP3.lean is new. Oleans go to scratch/glue-wp3/.lake/out (gitignored).
set -euo pipefail
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=scratch/glue-wp3
OUT=$D/.lake/out
mkdir -p $OUT/GlueDescent
for f in ${@:-Cochain Constants Chi B2Glue B2Assembly B3Assembly WP3}; do
  echo "== $f"
  if [ "$f" = WP3 ]; then
    lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean $D/$f.lean" 2>&1 | grep -v "^warning\|linter\|^Note\|^$" || true
  else
    lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean -o $OUT/GlueDescent/$f.olean $D/$f.lean" 2>&1 \
      | grep -E "error|sorry|depends on axioms" || true
  fi
done
