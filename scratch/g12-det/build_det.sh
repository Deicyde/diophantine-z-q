#!/bin/bash
# DetLeaves.lean = part_wp.lean (weil-pairing §1-§9) + DetTate.lean without its imports and
# #print lines + part_leaves.lean
cd "$(dirname "$0")"
{ cat part_wp.lean; sed -n '/^import ZInQKernel.HDecomp.Objects$/,$p' DetTate.lean | tail -n +2 | grep -v '^#print'; cat part_leaves.lean; } > DetLeaves.lean
