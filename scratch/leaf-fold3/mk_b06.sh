#!/bin/bash
# parts/b06_x6kummer.lean: scratch/x6-kummer parts B, C, D, E (task x6-kummer), verbatim. Its part0 (fs5-nocm §A:
# R1fpPropsFull ... X6KummerFibre) is part a60's text, and its partR (mul-rigidity's Rigidity.lean) is part a15's:
# both omitted (every declaration name checked present).
cd "$(dirname "$0")"
{ echo "/-! ## leaf-fold2: x6-kummer (scratch/x6-kummer/part{B,C,D,E}.lean, verbatim; see mk_b06.sh) -/"; echo "noncomputable section"; echo
  for p in partB partC partD partE; do grep -v '^#print' ../x6-kummer/$p.lean; echo; done; echo "end"; } > parts/b06_x6kummer.lean
