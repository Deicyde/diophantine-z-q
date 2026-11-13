#!/bin/bash
# dim_block.lean: verbatim scratch/g0-dim/Dim.lean l.107-305 (namespace G0Dim: field base change
# preserves the Krull dimension of a scheme locally of finite type, Stacks 00P4 globalized) and
# l.339-343 (`G0Dim.pkgI3_dim_baseChange`), inside a section opening `Order TensorProduct` (l.23).
# Dim.lean imports all of Mathlib; the 12 modules it needs are in dim_imports.txt (put first by build.sh).
cd "$(dirname "$0")"
SRC=../g0-dim/Dim.lean
{
  echo "section DimBlock"
  echo
  sed -n 23p $SRC
  echo
  sed -n 107,305p $SRC
  echo
  sed -n 339,343p $SRC
  echo
  echo "end DimBlock"
} > dim_block.lean
