#!/bin/bash
# av-b2: build the single-file check AVB2Flat.lean = leaf-fold3's flat Leaves3.lean (verbatim) +
# `import ZInQKernel.Contrib.AVB2.SerreLemma` + the body of olean/AVB2Main.lean (its import lines dropped).
# Check (one Lean process): lake env lean scratch/av-b2/AVB2Flat.lean   (build ZInQKernel.Contrib.AVB2.SerreLemma first)
cd "$(dirname "$0")"
SRC=../leaf-fold3/Leaves3.lean
OUT=AVB2Flat.lean
n=$(grep -n '^import' $SRC | tail -1 | cut -d: -f1)
head -$n $SRC > $OUT
echo 'import ZInQKernel.Contrib.AVB2.SerreLemma' >> $OUT
tail -n +$((n+1)) $SRC >> $OUT
echo "" >> $OUT
echo "-- ===== av-b2: scratch/av-b2/olean/AVB2Main.lean (its import lines dropped)" >> $OUT
grep -v '^import' olean/AVB2Main.lean >> $OUT
md5sum $OUT; wc -l $OUT
