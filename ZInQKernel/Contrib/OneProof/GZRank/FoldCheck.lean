import ZInQKernel.OneProof.H.TailZ106
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.GZRank.Glue

/-!
# The fold check: `frozenTarget` with `hRank` replaced by single-print rows

`frozenTarget_with_GZ` is the body of `ZInQ.OneProof.frozenTarget` (`OneProof/Main.lean` at
`9f98d294`) with the root argument `hRank` (Silverman, Appendix C, Evidence 16.5.5, the rank-one
line) replaced by three printed rows:

* `hGZ : GZRank.GZThm73NonTorsion`, Gross–Zagier, Invent. Math. 84 (1986), Theorem (7.3)(1);
* `hB : BCDTPrint.BCDTThmAPrinted`, Breuil–Conrad–Diamond–Taylor, J. Amer. Math. Soc. 14 (2001),
  Theorem A with condition (2), the row this proof carried as `hB` before the forward-rank fold;
* `hC : GZRank.CarayolCor08`, Carayol, Ann. Sci. École Norm. Sup. (4) 19 (1986), Cor. 0.8.

The H bundles, Theorem 5.3 (`hRC`) and the Cassels–Tate pairing (`hCT`) are unchanged. Pole
completeness goes through the copied consumer `GZRank.poleCompleteness_of_nonTorsion`, which needs
only a point of infinite order at analytic rank one (`GZRank.nonTorsion_of_prints`). The file
imports what `Main.lean` imports, and not `Main.lean` itself.
-/

namespace ZInQ.OneProof.GZRank

/-- **Theorem 1.1, with `hRank` replaced by Gross–Zagier (7.3)(1), BCDT Theorem A and Carayol's
Corollaire 0.8**: the frozen target from the open H bundles, Theorem 5.3 over its genuine Selmer
condition, the Cassels–Tate pairing on the curves `E_ℓ`, and the three printed rows. -/
theorem frozenTarget_with_GZ
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : HDec.HSyn.OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hGZ : ZInQ.Manuscript.PoleS12.GZRank.GZThm73NonTorsion)
    (hB : ZInQ.Contrib.RC53Assist.BCDTPrint.BCDTThmAPrinted)
    (hC : ZInQ.Manuscript.PoleS12.GZRank.CarayolCor08) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open99 r t l)
    (ZInQ.Manuscript.PoleS12.GZRank.poleCompleteness_of_nonTorsion hRC hCT
      (ZInQ.Manuscript.PoleS12.GZRank.nonTorsion_of_prints hGZ hB hC))

end ZInQ.OneProof.GZRank

#print axioms ZInQ.OneProof.GZRank.frozenTarget_with_GZ
