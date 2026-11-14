#!/bin/bash
# Assemble ReductGlue.lean = Base.lean (verbatim copy of reduct-split's Reduction.lean) + Body.lean (minus its import line)
cd "$(dirname "$0")"
{ cat Base.lean; echo; tail -n +2 Body.lean; } > ReductGlue.lean
