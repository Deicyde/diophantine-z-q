import ZInQKernel.Contrib.OneProof.SerreRigidityZ30.ThreeAdic
import ZInQKernel.Contrib.OneProof.SerreRigidityZ30.Rigidity
import ZInQKernel.Contrib.OneProof.SerreRigidityZ30.Chain

set_option autoImplicit false
noncomputable section
namespace Y3Buzzard

/-!
# Rigidity at level three from Buzzard's Lemma 2.2 and Milne's Theorem 12.5

`SerreRigidityLevel3'` went through Buzzard's principal polarization, which is printed only with a
sketched proof in positive characteristic. Here its use in the level-three moduli argument is
replaced by `SerreRigidityFibreZ30`, proved from two printed statements:

* Buzzard's Lemma 2.2 at `N = 5` (`BuzzardLemma22Full5`) makes an `O`-linear automorphism of
  finite order on each geometric fibre: some power fixes a generator of the 5-torsion;
* an automorphism of finite order that is trivial on the 3-torsion is trivial on all 3-power
  torsion (`ThreeAdic.fixes_threePow`, using the counts of Milne's Remark 8.4);
* Milne's Theorem 12.5 (`MilneThm125Pts`) then makes it the identity.
-/

/-- The group-theoretic step, in the form the rigidity proof takes it. -/
theorem threeAdicStmt_holds : ThreeAdicStmt := by
  intro G _ φ m hm hφm h1 r hcard
  exact ThreeAdic.fixes_threePow φ m hm hφm h1 r hcard

/-- Rigidity at level three on geometric fibres over `Z[1/30]`, from printed statements. -/
theorem serreRigidityFibreZ30_of_printed (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hR : MilneRem84) (hZ : ZeroPreservingIsHomLN) : SerreRigidityFibreZ30 :=
  serreRigidityFibreZ30_of_leaves threeAdicStmt_holds hBz hMl hR hZ

/-- `Y3RouteA.Y3FullThreeRepZ30` from eight printed inputs: Buzzard's Lemma 2.2 and Milne's
Theorem 12.5 in place of `SerreRigidityLevel3'`. -/
theorem y3FullThreeRepZ30_of_printed_buzzard22 (hB1 : BuzzardThm21Cor23V15')
    (hM3 : MilneProp207 3) (hR : MilneRem84) (hBz : BuzzardLemma22Full5) (hMl : MilneThm125Pts)
    (hB4 : ZeroPreservingIsHomLN) (hB6 : ProjectiveFEC) (hM5 : MilneProp207 5) :
    Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30_of_printed_rem84_z30 hB1 hM3 hR (serreRigidityFibreZ30_of_printed hBz hMl hR hB4)
    hB4 hB6 hM5

end Y3Buzzard
