#!/bin/bash
# leaf-fold6: the chain module after leaf-fold5's TailN, and the flat file.
#   olean/TailO.lean = import TailN + parts/f10_leafq.lean (mk_f10.py: leafq-check's Fold.lean, renamed bundles)
#                      + parts/f20_fold6.lean (hand-written: bundles and sixContactMin_of_open6)
#   Leaves6.lean     = scratch/leaf-fold5/Leaves5.lean + the two parts (not committed: 6.5 MB, made by this script;
#                      md5 in flat.md5)
cd "$(dirname "$0")"
python3 mk_f10.py
{ echo "import TailN"; echo; cat parts/f10_leafq.lean; echo; cat parts/f20_fold6.lean; } > olean/TailO.lean
{ cat ../leaf-fold5/Leaves5.lean; echo;
  echo "/-! ## leaf-fold6: the parts after leaf-fold5 (module TailO of the olean chain) -/"; echo;
  cat parts/f10_leafq.lean; echo; cat parts/f20_fold6.lean; } > Leaves6.lean
md5sum Leaves6.lean | cut -c1-32 > flat.md5
wc -l olean/TailO.lean Leaves6.lean
