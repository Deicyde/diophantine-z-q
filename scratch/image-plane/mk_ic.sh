#!/bin/bash
# Assemble ImageClosed.lean from its parts (run from repo root).
D=scratch/image-plane
{ cat $D/IC_head.lean.part $D/ICbase.lean.part $D/IC.lean.part
  printf '\nend Pin\n\nend AV\n\nend LeafQM\n\nend\n\n#print axioms LeafQM.AV.Pin.imageClosed\n'
} > $D/ImageClosed.lean
