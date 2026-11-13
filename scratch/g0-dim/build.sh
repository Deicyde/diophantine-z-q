#!/bin/bash
# Assemble SplitDim.lean = scratch/g0-split/Split.lean + part_dim.lean (the g0-dim proofs, appended).
# part_dim.lean is generated from Dim.lean §1-§2; regenerate Dim.lean edits by hand there.
cd "$(dirname "$0")"
{ cat ../g0-split/Split.lean; cat part_dim.lean; } > SplitDim.lean
