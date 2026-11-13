#!/bin/bash
# parts/b07_infrastalks.lean and LF2Stalks.lean.src from scratch/infra-stalks/HeightBCGlue.lean (task infra-stalks)
cd "$(dirname "$0")"
{ echo "/-! ## leaf-fold2: infra-stalks (scratch/infra-stalks/HeightBCGlue.lean lines 2955-3301, its Part 3, verbatim except"; echo "that the lines \`open PkgI3 (AbVar)\` are deleted, as g0-assemble2 did for part a20, and its two \`#print\` lines; Part 1 is module LF2Stalks) -/"; sed -n 2955,3301p ../infra-stalks/HeightBCGlue.lean | grep -v "^open PkgI3 (AbVar)$" | grep -v "^#print"; } > parts/b07_infrastalks.lean
{ echo "import Mathlib"; echo; echo "/-! leaf-fold2: scratch/infra-stalks/HeightBCGlue.lean lines 3-850 (its Part 1: general stalk lemmas), verbatim; root namespace. -/"; sed -n 3,850p ../infra-stalks/HeightBCGlue.lean; } > LF2Stalks.lean.src
