#!/bin/bash
# Weight.lean = g0-split's Split.lean (without its #print lines) + part_weight.lean (+ later parts)
cd "$(dirname "$0")"
S=../g0-split/Split.lean
{ grep -v '^#print' $S; cat part_weight.lean; [ -f part_twist.lean ] && cat part_twist.lean; } > Weight.lean
