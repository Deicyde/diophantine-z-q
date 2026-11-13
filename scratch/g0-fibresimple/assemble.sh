#!/bin/bash
# Assemble FibreSimple.lean = scratch/g0-split/Split.lean (verbatim) + olean/Tail.lean (minus its import line)
cd "$(dirname "$0")"
{ cat ../g0-split/Split.lean; echo; echo; tail -n +2 olean/Tail.lean; } > FibreSimple.lean
wc -l FibreSimple.lean
