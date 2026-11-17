#!/bin/sh
# Regenerates H21Lcal.lean (development) and FoldCheck.lean (development + Main fold check) from src/.
cd "$(dirname "$0")/.."
AX='#print axioms ZInQ.Contrib.H21Lcal.functionalEquationPlus_proof
#print axioms ZInQ.Contrib.H21Lcal.analyticOrderAt_ne_one
#print axioms ZInQ.Contrib.H21Lcal.lcalSqPrinted_eq
#print axioms ZInQ.Contrib.H21Lcal.lcalSqPrinted_one
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21PairsPrinted_of_C
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21Span_of_printed
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21SpanPrinted_of_span'
{ printf 'import ZInQKernel.Contrib.HeckeAll.Provider\nimport ZInQKernel.Contrib.OneProof.TYZThm21Span\nimport ZInQKernel.Contrib.OneProof.TYZLcalOne\n'
  cat src/part1.lean src/part2.lean src/part3.lean; echo; echo "$AX"; } > H21Lcal.lean
{ printf 'import ZInQKernel.OneProof.Main\nimport ZInQKernel.Contrib.HeckeAll.Provider\nimport ZInQKernel.Contrib.OneProof.TYZThm21Span\nimport ZInQKernel.Contrib.OneProof.TYZLcalOne\n'
  cat src/part1.lean src/part2.lean src/part3.lean src/fold.lean; } > FoldCheck.lean
