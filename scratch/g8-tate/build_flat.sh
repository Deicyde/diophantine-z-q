#!/bin/bash
# G8Tate.lean: the flat check file = Prefix.lean + Prefix2.lean (without `import Prefix`) +
# Tail.lean (without its imports); all imports first. Run build_prefix.sh, build_prefix2.sh,
# assemble.sh first. Check: lake env lean scratch/g8-tate/G8Tate.lean
cd "$(dirname "$0")"
{
  grep "^import" Prefix.lean
  grep "^import Mathlib" Tail.lean
  echo
  grep -v "^import" Prefix.lean
  echo
  grep -v "^import" Prefix2.lean
  echo
  grep -v "^import" Tail.lean
} > G8Tate.lean
wc -l G8Tate.lean
