import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Sites.Pullback
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleToProEtSiteV1
import ZInQKernel.Contrib.OneProof.EllAdic.LanMixedEvaluationV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- The literal direct image on abelian sheaves is restriction along the
small étale-to-pro-étale inclusion. -/
noncomputable abbrev smallEtaleAbPushforward (S : Scheme.{u}) :=
  (smallEtaleToProEt S).sheafPushforwardContinuous Ab.{u+1}
    S.smallEtaleTopology (Scheme.ProEt.topology S)

/-- The inverse image of the same morphism of sites. -/
noncomputable abbrev smallEtaleAbPullback (S : Scheme.{u}) :=
  (smallEtaleToProEt S).sheafPullback Ab.{u+1}
    S.smallEtaleTopology (Scheme.ProEt.topology S)

/-- The specified site adjunction. -/
noncomputable def smallEtaleAbAdjunction (S : Scheme.{u}) :
    smallEtaleAbPullback S ⊣ smallEtaleAbPushforward S :=
  (smallEtaleToProEt S).sheafAdjunctionContinuous Ab.{u+1}
    S.smallEtaleTopology (Scheme.ProEt.topology S)

private theorem smallEtaleAbLan_preservesFiniteLimits (S : Scheme.{u}) :
    PreservesFiniteLimits
      ((smallEtaleToProEt S).op.lan : (S.Etaleᵒᵖ ⥤ Ab.{u+1}) ⥤ S.ProEtᵒᵖ ⥤ Ab.{u+1}) := by
  let i := smallEtaleToProEt S
  let F : (S.Etaleᵒᵖ ⥤ Ab.{u+1}) ⥤ S.ProEtᵒᵖ ⥤ Ab.{u+1} := i.op.lan
  change PreservesFiniteLimits F
  let : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  let : PreservesFilteredColimitsOfSize.{u,u+1} (forget Ab.{u+1}) :=
    preservesFilteredColimitsOfSize_shrink.{u+1,u+1,u,u+1} (forget Ab.{u+1})
  let : ReflectsLimits (forget Ab.{u+1}) := reflectsLimits_of_reflectsIsomorphisms
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u} F
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation F J
  intro U
  let : IsFiltered (CostructuredArrow i.op U) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence i (unop U))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationMixedIso Ab.{u+1} i.op U).symm

/-- Inverse image on the actual pair of abelian-sheaf sites preserves finite limits. -/
instance smallEtaleAbPullback_preservesFiniteLimits (S : Scheme.{u}) :
    PreservesFiniteLimits (smallEtaleAbPullback S) := by
  let := smallEtaleAbLan_preservesFiniteLimits S
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

instance smallEtaleAbPullback_preservesColimits (S : Scheme.{u}) :
    PreservesColimits (smallEtaleAbPullback S) := (smallEtaleAbAdjunction S).leftAdjoint_preservesColimits

instance smallEtaleAbPullback_additive (S : Scheme.{u}) : (smallEtaleAbPullback S).Additive := by
  let : (smallEtaleAbPullback S).IsLeftAdjoint := (smallEtaleAbAdjunction S).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

end RC53.EllAdic
