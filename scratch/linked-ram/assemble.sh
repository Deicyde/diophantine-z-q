#!/bin/bash
# Flat file LinkedRam.lean = g0-assemble3's flat G0Assemble3.lean (committed, md5 b5a4fb97…) + lt-goodred's
# integ/99d_proofs.lean (verbatim) + this task's olean/Tail.lean minus its import line. Not committed (90k+ lines).
cd "$(dirname "$0")/../.."
D=scratch/linked-ram
OUT=$D/LinkedRam.lean
cp scratch/g0-assemble3/G0Assemble3.lean $OUT
printf '\n\n-- ===== lt-goodred integ/99d_proofs.lean (verbatim) =====\n\n' >> $OUT
cat scratch/lt-goodred/integ/99d_proofs.lean >> $OUT
printf '\n\n-- ===== linked-ram olean/Tail.lean (minus import) =====\n\n' >> $OUT
tail -n +2 $D/olean/Tail.lean >> $OUT
wc -l $OUT; md5sum $OUT
