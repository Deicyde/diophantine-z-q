import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueHOneForwardV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace RC53.EllAdic

universe u

local instance stacks099VProEtSheafification (S : Scheme.{u}) : HasSheafify (Scheme.ProEt.topology S) Ab.{u+1} :=
  ProEtale.hasSheafify_proetale.{u, 0} S

local instance stacks099VEtaleSheafification (S : Scheme.{u}) : HasSheafify S.smallEtaleTopology Ab.{u+1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, 0} S

local instance stacks099VProEtGrothendieck (S : Scheme.{u}) : IsGrothendieckAbelian.{u+1}
    (Sheaf (Scheme.ProEt.topology S) Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (Scheme.ProEt.topology S) Ab.{u+1}

local instance stacks099VEtaleGrothendieck (S : Scheme.{u}) : IsGrothendieckAbelian.{u+1}
    (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

/-- The direct image in Stacks Tag 099V is restriction along the same
inclusion of small sites, at the same coefficient universe. -/
theorem smallEtaleAbPushforward_eq_stacks099V (S : Scheme.{u}) :
    smallEtaleAbPushforward S = ProEtale.epsilonDirectImage.{u, 0} S := rfl

local instance stacks099VPushforwardAdditive (S : Scheme.{u}) : (smallEtaleAbPushforward S).Additive := by
  change (ProEtale.epsilonDirectImage.{u, 0} S).Additive
  exact (ProEtale.epsilonAdjunction.{u, 0} S).right_adjoint_additive

/-- Transport degree-one vanishing along uniqueness of the left adjoint
 to the same direct image. -/
theorem smallEtale_rightDerived_one_from_099V (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology Ab.{u+1}) :
    IsZero (((smallEtaleAbPushforward S).rightDerived 1).obj ((smallEtaleAbPullback S).obj F)) := by
  let G := ProEtale.epsilonDirectImage.{u, 0} S
  let a : smallEtaleAbPullback S ⊣ G := smallEtaleAbAdjunction S
  let c := ProEtale.epsilonAdjunction.{u, 0} S
  let e := Adjunction.leftAdjointUniq a c
  have hz := (ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage.{0, u} S F).2 1
    (Nat.zero_lt_succ 0)
  exact hz.of_iso ((G.rightDerived 1).mapIso (e.app F))

/-- The literal small étale-to-pro-étale map in degree one is bijective.
Only the image of the chosen injective cokernel is shown to be epi. -/
theorem smallEtaleResidueHOneForward_bijective (S : Scheme.{u}) (p n : ℕ) :
    Function.Bijective (smallEtaleResidueHOneForward S p n) := by
  let L := smallEtaleAbPullback S
  let G := smallEtaleAbPushforward S
  let F := etaleConstantResidue S p n
  let i := Injective.ι (L.obj F)
  let q := cokernel.π i
  let w : i ≫ q = 0 := cokernel.condition i
  let T := ShortComplex.mk i q w
  have c : IsColimit (CokernelCofork.ofπ q w) := cokernelIsCokernel i
  have hT : T.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel T c) (inferInstance : Mono i) (inferInstance : Epi q)
  let : PreservesLimits G := (smallEtaleAbAdjunction S).rightAdjoint_preservesLimits
  let : Epi (G.map q) :=
    Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one hT G
      (smallEtale_rightDerived_one_from_099V S F)
  exact smallEtaleResidueHOneForward_bijective_of_specific_epi S p n i q w c

end RC53.EllAdic
