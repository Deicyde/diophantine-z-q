#!/bin/bash
# Dev2.lean = TSSN.lean through `specNonMeeting_of_specialize` + abstract criterion + concrete part
cd "$(dirname "$0")"
head -2947 TSSN.lean > Dev2.lean
echo 'open NumberField' >> Dev2.lean
sed -n '/^theorem atPrime_congr/,/^end TSSN/p' Abstract.lean | grep -v '^end TSSN' >> Dev2.lean
cat Concrete.part >> Dev2.lean
echo "end PropTSGlue" >> Dev2.lean
