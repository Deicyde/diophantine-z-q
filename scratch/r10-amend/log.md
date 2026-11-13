# r10-amend results log

## Step 1 (statement, 2026-11-13 06:45)
- Definitions read (VERIFIED, read): `PkgI4.DeRhamComparison` (Contrib/G9/I4Layer.lean L1306 = Leaves.lean L4538),
  `htSpaceOver` (G_F-equivariant ℚ_p-maps V → ℂ_p(i)), `htMultOver w = finrank htSpaceOver(−w) / [F:ℚ_p]`,
  `G9Bridge.R10Weights` (Contrib/G9/Reduction.lean L61), 3c's `DeRhamComparisonWeights` (G9Weights.lean).
- Sign check: htMultOver w = dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}; V_p(A)^∨ = H¹_et; HT decomposition
  ℂ_p ⊗ H¹ ≅ ℂ_p^g ⊕ ℂ_p(−1)^g ⇒ mult g at w=0 and w=−1, 0 elsewhere (with Tate ℂ_p(j)^{G_F}=0, j≠0). Matches leaf.
- Sources on host: none (only the manuscript diophantine_zq.tex). Manuscript L11003 cites
  "[Faltings 1988, Chapter III, Theorem 4.1]" for the Hodge–Tate comparison (VERIFIED: the citation is in the tex;
  content of Faltings UNVERIFIED). locators.md R10 row reports Scholze Cor 1.8 read (other task, network).
- Amended leaf `ZInQ.Contrib.R10.DeRhamComparisonHT` in ZInQKernel/Contrib/R10/Amend.lean: per (p,F,A),
  (∀ g, dim = g → old R10 conclusion) ∧ (∀ w ≠ 0, −1, htMultOver w = 0). Weight clause has no dim hypothesis.
- Compiled (VERIFIED, lake build ZInQKernel.Contrib.R10.Amend, 104 s): deRhamComparison_of_HT, r10Weights_of_HT,
  deRhamComparisonWeights_of_HT, deRhamComparisonHT_iff (↔ DeRhamComparison ∧ R10Weights), htMultOver_eq_of_HT;
  all axioms [propext, Classical.choice, Quot.sound].
