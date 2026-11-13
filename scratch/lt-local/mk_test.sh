#!/bin/bash
# T3.lean = import Base + parts 1-4 + #print axioms (dev file)
cd "$(dirname "$0")"
{ printf 'import Base\nimport Mathlib.Analysis.Complex.Cardinality\nimport Mathlib.Topology.Algebra.Module.Cardinality\nimport Mathlib.FieldTheory.IsAlgClosed.Classification\n\n'
  for f in part_tools part_g7 part_copy part_main; do cat $f.lean; echo; done
  cat part_axioms.lean; } > T3.lean
