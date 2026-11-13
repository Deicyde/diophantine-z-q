#!/bin/bash
# Assemble Split.lean = Leaves.lean (up to TextbookLeaves) + glue-ssbc + part_split.lean
cd "$(dirname "$0")"
L=../h-decomposition/Leaves.lean
{ sed -n 1,18786p $L; echo "section GlueSSBCSec"; echo "/-! ### Copied from \`scratch/glue-ssbc/SSBC.lean\` (compiled there; imports covered by Mathlib). -/"; sed -n 27,235p ../glue-ssbc/SSBC.lean; echo "end"; echo "end GlueSSBCSec"; echo; sed -n 18787,19196p $L; cat part_split.lean; } > Split.lean
