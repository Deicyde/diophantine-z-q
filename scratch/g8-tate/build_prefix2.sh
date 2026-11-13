#!/bin/bash
# Prefix2.lean = import Prefix + unram-tate's Tate-functor construction + linked-tate's linked data:
#  scratch/linked-tate/parts/96_unramtate.lean (= scratch/unram-tate/TateBridge.lean L1038-1825
#    verbatim, with ModField's file-level opens) lines 1-597 and 726-end, i.e. without its
#    copy of BCPoints.lean (the section BC/Tr declarations sK, bcPt, trPt, ...: local-glue's
#    bc_block.lean, already in Prefix, is the same text in the same namespace UnramTate); the
#    section header is kept;
#  scratch/linked-tate/parts/97_linkeddata.lean lines 1-445 (through `end UnramTate`; without the
#    two Leaves-layer composites linkedTateData_of_frobRam, afterG7_of_final), closing its section.
cd "$(dirname "$0")"
U=../linked-tate/parts/96_unramtate.lean
W=../linked-tate/parts/97_linkeddata.lean
{
  echo "import Prefix"
  echo
  echo "noncomputable section"
  sed -n '1,598p' $U
  echo "open scoped CategoryTheory.Obj"
  echo
  sed -n '726,$p' $U
  echo "end"
  echo
  sed -n '1,445p' $W
  echo
  echo "end"
  echo
  echo "end LinkedDataSec"
} > Prefix2.lean
