#!/bin/bash
# Assemble scratch/g8-local/G8Local.lean (one environment for the whole check):
#  1. g8-object's environment, produced by running scratch/g8-object/build.sh's own commands
#     (verbatim copies of g0-mod-field, g14-trace, g15-ram, g0-mod-galois, g0-assemble,
#     linked-tate, and g8-object's part_obj/part_ltcopy/part_link/part_split), with the output
#     redirected to base.lean here (g8-object's files are not touched);
#  2. the imports of this task's closed lemmas, ZInQKernel.Contrib.G8Local.* (built by lake);
#  3. part_local.lean (this task) and part_link2.lean (this task).
# Check: lake env lean scratch/g8-local/G8Local.lean
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$HERE/../g8-object"
# Step 1: g8-object's build.sh, output redirected.
( cd "$SRC" && sed -e 's#^} > G8Object.lean$#} > "'"$HERE"'/base.lean"#' -e 's#^cd "$(dirname "$0")"$##' build.sh | bash )
# Step 2-3.
{
  awk '/^import /{print; next} {exit}' "$HERE/base.lean"
  echo "import ZInQKernel.Contrib.G8Local.WildLocal"
  echo "import ZInQKernel.Contrib.G8Local.TateFix"
  echo "import ZInQKernel.Contrib.G8Local.LocalFieldF"
  awk 'BEGIN{body=0} !body && /^import /{next} {body=1; print}' "$HERE/base.lean"
  echo
  cat "$HERE/part_local.lean"
  if [ -f "$HERE/part_link2.lean" ]; then echo; cat "$HERE/part_link2.lean"; fi
} > "$HERE/G8Local.lean"
rm -f "$HERE/base.lean"
echo "wrote $HERE/G8Local.lean ($(wc -l < "$HERE/G8Local.lean") lines)"
