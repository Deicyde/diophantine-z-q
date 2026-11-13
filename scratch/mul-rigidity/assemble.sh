#!/bin/bash
# Assemble MulRigidity.lean = imports + Rigidity.lean body + Mul.lean body + fs_tail.lean.part
cd "$(dirname "$0")"
{ echo "import Mathlib"; echo "import ZInQKernel.HDecomp.Objects"; echo;
  grep -v "^import " Rigidity.lean; echo; grep -v "^import " Mul.lean; cat fs_tail.lean.part; } > MulRigidity.lean
wc -l MulRigidity.lean
