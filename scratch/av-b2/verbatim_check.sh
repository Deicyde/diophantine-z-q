#!/bin/bash
# av-b2: check that AVB2Flat.lean is leaf-fold3's Leaves3.lean verbatim plus one import line and the appended
# body of olean/AVB2Main.lean (so every Prop it proves is leaf-fold3's own text).
cd "$(dirname "$0")"
SRC=../leaf-fold3/Leaves3.lean
n=$(wc -l < $SRC); i=$(grep -n '^import' $SRC | tail -1 | cut -d: -f1)
diff <(head -$i AVB2Flat.lean; sed -n "$((i+2)),$((n+1))p" AVB2Flat.lean) $SRC > /dev/null && echo "prefix: verbatim ($n lines)" || echo "prefix: DIFFERS"
diff <(tail -n +$((n+4)) AVB2Flat.lean) <(grep -v '^import' olean/AVB2Main.lean) > /dev/null && echo "tail: = AVB2Main body" || echo "tail: DIFFERS"
