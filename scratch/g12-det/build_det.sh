#!/bin/bash
# DetLeaves.lean = part_wp.lean (weil-pairing §1-§9) + DetTate.lean body (no #print) + part_leaves.lean
cd "$(dirname "$0")"
grep -v "^#print" part_dt.lean > /tmp/g12det_pdt.lean
cat part_wp.lean /tmp/g12det_pdt.lean part_leaves.lean > DetLeaves.lean
