#!/bin/bash
# Assembles, from verbatim copies (nothing below is edited except the two deletions noted):
#   olean/LTail.lean  = "import LPrefix" + scratch/linked-tate/parts/*.lean  (= linked-tate's olean/Tail.lean)
#   olean/Mine.lean   = "import LTail" + AFR block + parts/*.lean            (iteration file)
#   LinkedFrob.lean   = LPrefix (linked-tate's Leaves.lean + imports_extra.txt) + linked-tate's parts
#                       + AFR block + parts/*.lean                            (the single-file check)
# AFR block = the two file-level `open` lines of g0-mod-field's ModField.lean (active in frob-trace's
#   FrobTrace.lean, whose prefix ModField.lean + unram-tate's section is linked-tate's parts 75 and 96), then
#   scratch/frob-trace/part_bridge_src.lean, scratch/frob-trace/part_frob.lean     (frob-trace)
#   scratch/mul-rigidity/Rigidity.lean minus its 4 imports and minus its copy of `def RigidityHom`
#     (already in linked-tate's part 40, same text)                                 (mul-rigidity)
#   scratch/alg-frob-red/part_red.lean                                              (alg-frob-red)
#   scratch/afr-absfrob/AbsFrobDef.lean minus its import and its copy of `def AbsFrob` (afr-absfrob's
#     own build.sh does the same), scratch/afr-absfrob/part_fext.lean               (afr-absfrob)
#   scratch/frob-pieces/part_{good,neron,final,full}.lean                           (frob-pieces)
# This is the order of frob-pieces' FrobPiecesFull.lean (alg-frob-red's AlgFrobRed.lean + afr-absfrob + frob-pieces).
cd "$(dirname "$0")"
R=../..
LT=$R/scratch/linked-tate
{
  echo "open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj"
  echo "open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q"
  echo
  cat $R/scratch/frob-trace/part_bridge_src.lean
  cat $R/scratch/frob-trace/part_frob.lean
  tail -n +5 $R/scratch/mul-rigidity/Rigidity.lean | sed '/^\/-- \*\*Textbook leaf (rigidity;/,/η\[A.X\] ≫ h = η\[B.X\] → IsMonHom h$/d'
  cat $R/scratch/alg-frob-red/part_red.lean
  tail -n +2 $R/scratch/afr-absfrob/AbsFrobDef.lean | sed '/^\/-- \*\*`AbsFrob` (GLUE/,/≫ g = g ≫ Fr$/d'
  cat $R/scratch/afr-absfrob/part_fext.lean
  for f in good neron final full; do cat $R/scratch/frob-pieces/part_$f.lean; echo; done
} > afr_block.tmp
{ echo "import LPrefix"; echo; for p in $LT/parts/*.lean; do cat $p; echo; done; } > olean/LTail.lean
{ echo "import LTail"; echo; cat afr_block.tmp; for p in parts/*.lean; do cat $p; echo; done; } > olean/Mine.lean
{ sed -n 1,3p $LT/Leaves.lean; cat imports_extra.txt; sed -n '4,$p' $LT/Leaves.lean; echo;
  for p in $LT/parts/*.lean; do cat $p; echo; done; cat afr_block.tmp; for p in parts/*.lean; do cat $p; echo; done; } > LinkedFrob.lean
rm afr_block.tmp
cmp <(tail -n +2 olean/LTail.lean) <(tail -n +2 $LT/olean/Tail.lean) && echo "LTail = linked-tate's Tail (after the import line)"
wc -l olean/LTail.lean olean/Mine.lean LinkedFrob.lean
