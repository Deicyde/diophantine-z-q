#!/bin/bash
# GoodRed.lean (flat file) = lines 1-14993 of scratch/linked-tate/Leaves.lean + closers + parts/*.lean
cd "$(dirname "$0")"
{ sed -n 1,14993p ../linked-tate/Leaves.lean; printf '\nend AV\n\nend LeafQM\n\nend\n\nend LeafQMSec\n'; echo; for p in parts/*.lean; do cat $p; echo; done; } > GoodRed.lean
wc -l GoodRed.lean
