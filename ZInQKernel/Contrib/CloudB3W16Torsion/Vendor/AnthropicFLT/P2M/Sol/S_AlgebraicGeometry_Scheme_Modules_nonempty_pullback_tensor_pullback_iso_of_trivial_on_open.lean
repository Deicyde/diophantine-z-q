/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_PullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme in

theorem solution
    {Y T : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) (L : Y.Modules) (N : T.Modules)
    (eN : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : AlgebraicGeometry.Scheme.{u}).Modules)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj
        (L ⊗ (AlgebraicGeometry.Scheme.Modules.pullback q).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj L) := by
  have hfact : (q ⁻¹ᵁ V).ι ≫ q = (q ∣_ V) ≫ V.ι := (morphismRestrict_ι q V).symm
  refine ⟨Scheme.Modules.pullbackTensorObjIsoFLT (q ⁻¹ᵁ V).ι L _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp (q ⁻¹ᵁ V).ι q).app N ≪≫
    (Scheme.Modules.pullbackCongr hfact).app N ≪≫
    ((Scheme.Modules.pullbackComp (q ∣_ V) V.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (q ∣_ V)).mapIso eN ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (q ∣_ V)
