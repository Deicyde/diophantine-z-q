#!/bin/bash
# DevProc.lean (TC-free dev check) = Reduction + Metric bodies + FrobData def + part_procyclic
cd "$(dirname "$0")"
{
  echo "import ZInQKernel.HDecomp.Conductor.LadicCond"
  grep -v "^import" Reduction.lean
  grep -v "^import" Metric.lean
  echo "namespace UnramRootsTask"
  echo "open PkgI4 (GQp)"
  echo "open LadicCond"
  echo "variable {p : ℕ} [Fact p.Prime]"
  sed -n '/^def FrobData/,/^$/p' TCPart.lean
  echo "end UnramRootsTask"
  cat part_procyclic.lean
} > DevProc.lean
