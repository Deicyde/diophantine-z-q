#!/bin/bash
# Weight.lean = g0-split's Split.lean (without its #print lines) + part_weight.lean + part_twist.lean
#   + part_htconj.lean + part_final.lean
# HTFast.lean = Split.lean L1-4727 (through `end PkgI4Sec`) + part_htdefs.lean + part_htconj.lean
cd "$(dirname "$0")"
S=../g0-split/Split.lean
{ grep -v '^#print' $S; cat part_weight.lean part_twist.lean part_htconj.lean part_htextend.lean part_final.lean; } > Weight.lean
{ sed -n 1,4727p $S; cat part_htdefs.lean part_htconj.lean part_htextend.lean; } > HTFast.lean
