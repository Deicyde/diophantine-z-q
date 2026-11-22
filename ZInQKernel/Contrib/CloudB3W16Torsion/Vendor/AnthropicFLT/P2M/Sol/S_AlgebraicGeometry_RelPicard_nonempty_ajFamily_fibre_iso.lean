/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_ajFamily_fibre_iso

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t)).obj (ajFamily (a := a) ε) ≅
      pointSubBasepointModule (a := a) t ε) :=
  by
  rw [baseChangeSnd_eq_mapOnProdOver]

  have hΔ : (diagDiv (a := a)).pullbackAlong t.1 t.2 = RelEffCartierDiv.ofPoint a t.1 t.2 :=
    (RelEffCartierDiv.pullbackAlong_ofPoint a (𝟙 A) (Category.id_comp a) t.1 t.2).trans
      (RelEffCartierDiv.ofPoint_congr a (Category.comp_id _) _ _)
  have hE : (constDiv (a := a) ε).pullbackAlong t.1 t.2 = RelEffCartierDiv.ofPoint a ε.1 ε.2 :=
    (RelEffCartierDiv.pullbackAlong_ofPoint a (a ≫ ε.1) (comp_point_comp ε) t.1 t.2).trans
      (RelEffCartierDiv.ofPoint_congr a (by rw [← Category.assoc, t.2, Category.id_comp]) _ _)

  have hΔ' : (diagDiv (a := a)).I.comap (mapOnProdOver a t.1 t.2) = (RelEffCartierDiv.ofPoint a t.1 t.2).I :=
    congrArg RelEffCartierDiv.I hΔ
  have hE' : (constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2) = (RelEffCartierDiv.ofPoint a ε.1 ε.2).I :=
    congrArg RelEffCartierDiv.I hE
  have hcΔ : ((diagDiv (a := a)).I.comap (mapOnProdOver a t.1 t.2)).IsCartierFLT :=
    RelEffCartierDiv.isInvertible_I ((diagDiv (a := a)).pullbackAlong t.1 t.2)
  have hcE : ((constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2)).IsCartierFLT :=
    RelEffCartierDiv.isInvertible_I ((constDiv (a := a) ε).pullbackAlong t.1 t.2)

  obtain ⟨iΔ⟩ := Scheme.IdealSheafData.IsCartierFLT.nonempty_pullback_invModule_iso (mapOnProdOver a t.1 t.2)
    (RelEffCartierDiv.isInvertible_I (diagDiv (a := a))) hcΔ
  let iE : (Scheme.Modules.pullback (mapOnProdOver a t.1 t.2)).obj (constDiv (a := a) ε).I.module ≅
      ((constDiv (a := a) ε).I.comap (mapOnProdOver a t.1 t.2)).module :=
    @asIso _ _ _ _ ((constDiv (a := a) ε).I.pullbackModuleComparison (mapOnProdOver a t.1 t.2))
      (Scheme.IdealSheafData.IsCartierFLT.isIso_pullbackModuleComparison (mapOnProdOver a t.1 t.2)
        (RelEffCartierDiv.isInvertible_I (constDiv (a := a) ε)) hcE)
  refine ⟨Scheme.Modules.pullbackTensorObjIsoFLT _ _ _ ≪≫ (?_ ⊗ᵢ ?_)⟩
  · exact iΔ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hΔ')
  · exact iE ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module hE')
