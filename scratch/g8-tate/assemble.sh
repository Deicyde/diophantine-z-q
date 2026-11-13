#!/bin/bash
# Tail.lean = import Prefix2 (+ Mathlib imports of part_tools) + parts 1-5 (iteration file)
cd "$(dirname "$0")"
{
  echo "import Prefix2"
  grep "^import Mathlib" part_tools.lean
  echo
  grep -v "^import" part_tools.lean
  for f in part_local part_link part_onl part_tb; do echo; cat $f.lean; done
} > Tail.lean
