#!/bin/bash
# Assemble HeightAdd.lean = Split.lean l.16667-18603 (verbatim def-faltings copy) + part_heightadd.lean
cd "$(dirname "$0")"
{ echo "import Mathlib"; echo; sed -n 16667,18603p ../g0-split/Split.lean; } > Prefix.lean
cat Prefix.lean part_heightadd.lean part_zero.lean > HeightAdd.lean
