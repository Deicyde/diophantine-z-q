/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
-- Source-local namespace open deferred until its declaration.

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.ofUnitSection Scheme.Modules.coeff Scheme.Modules.sectionDual Scheme.Modules.dual Scheme.Modules.ihomSectionsEquiv Scheme.Modules.restrictUnitIso')
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Γ Modules Opens evaluation Modules.ofUnitSection Modules.coeff Modules.sectionDual Modules.dual Modules.ihomSectionsEquiv Modules.restrictUnitIso')
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (presheaf ofUnitSection restrictSection coeff sectionDual dual ihomEval map_ihomEval ihomEval_pre_app unitIsoSelf_hom_app ihomSectionsEquiv ihomSectionsEquiv_app_apply restrictUnitIso' restrictUnitIso_ι_hom_app_apply unitSection map_unitSection)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry

namespace SectionDualFormula

variable {X : Scheme.{u}} {M : X.Modules}

abbrev sVal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M, U) := s.app U (unitSection U)

lemma map_sVal (s : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op (sVal s U) = sVal s V := by
  have h := (NatTrans.naturality_apply s.mapPresheaf i.op (unitSection U)).symm
  rw [map_unitSection] at h
  exact h

lemma sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (sectionDual s).app U t = ihomEval M (𝟙_ X.Modules) U (sVal s U) t := by
  change (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom.app U
      (((MonoidalClosed.pre s).app (𝟙_ X.Modules)).app U t) = _
  rw [unitIsoSelf_hom_app, ihomEval_pre_app]

theorem ofUnitSection_sectionDual_app' (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    ofUnitSection U ((sectionDual s).app U t) =
      coeff s U (ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫ (restrictUnitIso' U.ι).hom) := by
  rw [sectionDual_app]
  have e1 := ihomSectionsEquiv_app_apply U t ⊤ (restrictSection s U)
  have e2 := restrictUnitIso_ι_hom_app_apply U ⊤
    ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  change _ = X.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((restrictUnitIso' U.ι).hom.app ⊤
        ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U)))
  rw [e2]
  change ihomEval M (𝟙_ X.Modules) U (sVal s U) t =
    (𝟙_ X.Modules).presheaf.map (eqToHom U.ι_image_top.symm).op
      ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  rw [e1, map_ihomEval]
  congr 1
  · exact (map_sVal s _).symm
  · change t = ((Scheme.Modules.dual M).presheaf.map _ ≫ (Scheme.Modules.dual M).presheaf.map _) t
    rw [← Functor.map_comp, ← op_comp,
      show (eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) : U ⟶ U) = 𝟙 U from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
    rfl

end SectionDualFormula

end AlgebraicGeometry.Scheme.Modules

end

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    Scheme.Modules.ofUnitSection U ((Scheme.Modules.sectionDual s).app U t) =
      Scheme.Modules.coeff s U
        (Scheme.Modules.ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫
          (Scheme.Modules.restrictUnitIso' U.ι).hom) :=
  AlgebraicGeometry.Scheme.Modules.SectionDualFormula.ofUnitSection_sectionDual_app' s U t
