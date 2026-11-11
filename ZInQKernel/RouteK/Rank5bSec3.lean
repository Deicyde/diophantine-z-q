import ZInQKernel.MainGreenTao
import ZInQKernel.RouteK.Rank5b
import ZInQKernel.RouteK.Rank5b.Sec3.Defs
import ZInQKernel.RouteK.Rank5b.Sec3.Perm
import ZInQKernel.RouteK.Rank5b.Sec3.Forest
import ZInQKernel.RouteK.Rank5b.Sec3.Redei
import ZInQKernel.RouteK.Rank5b.Sec3.DetAlg
import ZInQKernel.RouteK.Rank5b.Sec3.DetForest
import ZInQKernel.RouteK.Rank5b.Sec3.M5bForest
import ZInQKernel.RouteK.Rank5b.Sec3.Glue
import ZInQKernel.RouteK.Rank5b.Sec3.Count
import ZInQKernel.RouteK.Rank5b.Sec3.Genus
import ZInQKernel.RouteK.Rank5b.Sec3.Thm36
import ZInQKernel.RouteK.Rank5b.Sec3.TYZ
import ZInQKernel.RouteK.Rank5b.Sec3.Props
import ZInQKernel.RouteK.Rank5b.Sec3.Prop34
import ZInQKernel.RouteK.Rank5b.Sec3.Check
import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.RouteK.Redei.FourRank

/-!
# Route K, row 5b, §§2–3 of tyz-5b (root module)

Sections 2 and 3 of `docs/research/tyz-5b.md` in Lean, so that CR₃ can be stated in the terms of
Tian–Yuan–Zhang:

* `Sec3.Defs`: Rédei's `g` as a function of the bits (`Sec3.redeiG`, `gBit`; tyz-5b Proposition 2.3,
  the `κ` forms), the genus sum of row 5b (`Sec3.genusSum5b` over `Finpartition`s, `T5b`);
* `Sec3.Perm`, `Sec3.Forest`: permanent minors over `𝔽₂` and the forest lemma (Lemma 2.1,
  `Sec3.pmin_lapl_eq_forests`);
* `Sec3.Redei`: `κ` as a forest count, Lemma 2.2 (`Sec3.kappa_add_kappa`, `Sec3.kappa_eq_kappa`), (2.1),
  (2.2);
* `Sec3.DetAlg`, `Sec3.DetForest`, `Sec3.M5bForest`: Propositions 3.3–3.4 in forest form
  (`Sec3.det_M1G`, `Sec3.det_Pmat`, `Sec3.det_M5bG_forest`);
* `Sec3.Glue`, `Sec3.Count`, `Sec3.Genus`, `Sec3.Thm36`: the genus sum as a forest sum
  (`Sec3.genusSum5b_eq_forest`) and Theorem 3.6 for bits (`Sec3.det_M5bG_eq_genusSum5b`);
* `Sec3.TYZ`: Theorem 3.6 (`det_M5b_eq_T5b`), the hypothesis `CertifiedRankTYZ` and
  `certifiedRank5b_of_certifiedRankTYZ`;
* `Sec3.RedeiStatement`: CR₃ with TYZ's class numbers `#2Cl(ℚ(√−d_B))` (`CertifiedRankTYZCl`), Rédei's
  formula as a Prop (`RedeiFormula`) and `certifiedRankTYZ_iff_of_redeiFormula`; `RedeiFormula` is
  proved in `RouteK/Redei/FourRank.lean` (`RouteK.Redei.redeiFormula`).
-/

namespace ZInQ

/-- **Theorem 1.1** from 6C_min and CR₃^5b (`RouteK.Rank5b.CertifiedRank5b`), without 22P: CR₃^5b
implies CR₃^Sel by Corollary 4.4 (`RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`), and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel` applies.
The variant `exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b` also takes
22P. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b
    (hH : SixContactMin) (hCR : RouteK.Rank5b.CertifiedRank5b) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel hH
    (RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^TYZ (`RouteK.Rank5b.CertifiedRankTYZ`: for squarefree
`d ≡ 5 (mod 8)` with `#Sel₂(C_d) = 8` and odd genus sum `T_5b(d)`, every 2-Selmer class of `C_d` comes
from a rational point — a consequence of Tian–Yuan–Zhang (Proposition N of
`docs/research/nt-tyz.md`), Rédei's formula, proved in Lean as `RouteK.Redei.redeiFormula`, and
Gross–Zagier).

CR₃^TYZ implies CR₃^5b by Theorem 3.6 (`RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ`), which
implies CR₃^Sel by Corollary 4.4 (`RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ
    (hH : SixContactMin) (hCR : RouteK.Rank5b.CertifiedRankTYZ) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel hH
    (RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b
      (RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ hCR))

/-- **Theorem 1.1** from 6C_min and CR₃ in Tian–Yuan–Zhang's own terms
(`RouteK.Rank5b.CertifiedRankTYZCl`, with `g(d_B) = #2Cl(ℚ(√−d_B))`).

Rédei's formula (`RouteK.Rank5b.RedeiFormula`, tyz-5b Proposition 2.3), proved in Lean as
`RouteK.Redei.redeiFormula` (`RouteK/Redei/FourRank.lean`), turns CR₃ in class-number form into
CR₃^TYZ (`RouteK.Rank5b.certifiedRankTYZ_iff_of_redeiFormula`), and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ` applies. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl
    (hH : SixContactMin) (hCR : RouteK.Rank5b.CertifiedRankTYZCl) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ hH
    ((RouteK.Rank5b.certifiedRankTYZ_iff_of_redeiFormula RouteK.Redei.redeiFormula).1 hCR)

end ZInQ
