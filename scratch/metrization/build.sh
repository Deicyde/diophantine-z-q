#!/bin/bash
# Assemble Metrization.lean = Base.lean (verbatim copy of scratch/g0-heightadd/HeightAdd.lean)
# + ExtLine.lean body + part files.
cd "$(dirname "$0")"
{ cat Base.lean; sed -e '/^import Mathlib/d' -e '/^#print axioms/d' ExtLine.lean; cat part_dim.lean; for f in part_g0dim.lean part_exists.lean part_prodgeo.lean part_prodlat.lean part_final.lean part_produnif.lean part_jacdet.lean part_prodsplit.lean part_jacgerm.lean part_jacscalar.lean; do [ -f $f ] && cat $f; done; } > Metrization.lean
