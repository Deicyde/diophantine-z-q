#!/bin/bash
# Assemble AlgDepProof.lean (IC + AD) from parts (run from repo root).
D=scratch/image-plane
{ sed 's/part 1: (IC) `ImageClosed` is a theorem/parts 1-2: (IC) `ImageClosed` and (AD) `AlgDep`/' $D/IC_head.lean.part
  cat $D/ICbase.lean.part $D/ADbase.lean.part $D/IC.lean.part $D/AD.lean.part
  printf '\nend Pin\n\nend AV\n\nend LeafQM\n\nend\n\n#print axioms LeafQM.AV.Pin.imageClosed\n#print axioms LeafQM.AV.Pin.algDep_of\n'
} > $D/AlgDepProof.lean
