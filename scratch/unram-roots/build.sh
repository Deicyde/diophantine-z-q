#!/bin/bash
# UnramRoots.lean = imports (LadicCond + Tau Ceti) + Reduction.lean + Metric.lean + TCPart.lean
# (bodies, import lines dropped) + part_procyclic.lean + part_final.lean.
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.Conductor.LadicCond"
  grep "^import ZInQKernel.Contrib" TCPart.lean
  grep -v "^import" Reduction.lean
  grep -v "^import" Metric.lean
  grep -v "^import" TCPart.lean
  cat part_procyclic.lean
  cat part_final.lean
} > UnramRoots.lean
