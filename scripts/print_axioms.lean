import ZInQKernel

/-!
Prints the axioms of the main theorems, their variants, and the theorems that replace former
hypotheses. From the repository root, after `lake build ZInQKernel`:

    lake env lean scripts/print_axioms.lean

Each declaration should depend on `[propext, Classical.choice, Quot.sound]` only.
-/

-- The main theorems: two hypotheses (`MainGreenTao.lean`) and three hypotheses (`Main.lean`).
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of

-- Variants.
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b

-- Theorems that replace former hypotheses, and the vendored Green–Tao theorem.
#print axioms ZInQ.greenTaoDense
#print axioms ZInQ.Density.goodPrimeDensity
#print axioms ZInQ.greenTao_primes
#print axioms Submission.green_tao
#print axioms ZInQ.RouteK.Selmer.certifiedRank_of_certifiedRankSel
#print axioms ZInQ.RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b
#print axioms ZInQ.poleCompleteness_of_certifiedRank
#print axioms ZInQ.mordellWeilE
#print axioms ZInQ.catalogueBound8
