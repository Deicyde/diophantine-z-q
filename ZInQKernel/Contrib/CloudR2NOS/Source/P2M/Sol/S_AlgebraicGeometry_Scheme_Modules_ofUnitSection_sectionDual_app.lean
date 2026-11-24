/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app.lean
  Source sha256  : 8865a55be93bd4725c66a4af5688761904e312d527ba01874882466c500eb145
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
r2nos_namespace_dual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.ofUnitSection Scheme.Modules.coeff Scheme.Modules.sectionDual Scheme.Modules.dual Scheme.Modules.ihomSectionsEquiv Scheme.Modules.restrictUnitIso'"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Γ Modules Opens evaluation Modules.ofUnitSection Modules.coeff Modules.sectionDual Modules.dual Modules.ihomSectionsEquiv Modules.restrictUnitIso'"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf ofUnitSection restrictSection coeff sectionDual dual ihomEval map_ihomEval ihomEval_pre_app unitIsoSelf_hom_app ihomSectionsEquiv ihomSectionsEquiv_app_apply restrictUnitIso' restrictUnitIso_ι_hom_app_apply unitSection map_unitSection"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace SectionDualFormula
r2nos_namespace_dual

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
end S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
