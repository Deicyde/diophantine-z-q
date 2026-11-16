/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) [IsSeparated q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (d m : ℕ)
    (σ : ∀ k : ℕ, Fin m → ↥(((F k).tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι)))
    (hσ : ∀ (k : ℕ) (l : Fin m),
      (OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id (ProjSpace.twist q ι d))).H0Map
        (ProjSpace.stdCoverPullback ι) (σ (k + 1) l) = σ k l)
    (hgen : ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
      Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
          (Set.range fun l : Fin m =>
            (σ 0 l : ((F 0).tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤) :
    ∃ (E : OModulePresheaf q) (θ : ∀ k, OModulePresheaf.AffHom E (F k)),
      E.IsCoherent ∧ E.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.solution
