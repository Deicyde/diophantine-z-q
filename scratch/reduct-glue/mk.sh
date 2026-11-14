#!/bin/bash
# Assemble ReductGlue.lean = Base.lean (verbatim copy of reduct-split's Reduction.lean, with two extra
# imports added to its header) + Body.lean (minus its import lines)
cd "$(dirname "$0")"
{ grep '^import' Base.lean; grep '^import' Body.lean | grep -v ReductSplitBase; grep -v '^import' Base.lean; echo; grep -v '^import' Body.lean; } > ReductGlue.lean
