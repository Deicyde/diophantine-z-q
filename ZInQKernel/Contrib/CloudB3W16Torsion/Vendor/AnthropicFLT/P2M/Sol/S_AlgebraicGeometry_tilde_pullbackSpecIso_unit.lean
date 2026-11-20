/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem solution {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
  exact h2

#print axioms solution
