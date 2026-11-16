/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mGrVanishAsm

theorem exists_fin_span_eq {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (s : ℕ) (g : Fin s → A), Ideal.span (Set.range g) = I :=
  Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)

end P2mGrVanishAsm

open _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKc : ∀ k, (K k).IsCoherent) (hKq : ∀ k, (K k).IsQuasicoherent)
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : P.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (k i : ℕ),
      Subsingleton (((K k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by

  obtain ⟨s, g, hg⟩ := P2mGrVanishAsm.exists_fin_span_eq I
  obtain ⟨θ, -, hcomm, hgen⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
      I g hg F φ hφs hφk K j hji hjr

  obtain ⟨D, hD, h, hinj, hsat⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule
      ι hιq K hKc hKq θ hcomm hgen

  obtain ⟨d₀, hd₀⟩ :=
    ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
      (familyFramesGradedModule ι K θ hcomm) D hD h hinj hsat
  refine ⟨d₀.toNat, fun d hd k i => ?_⟩

  have hv : Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift (familyFramesGradedModule ι K θ hcomm) (d : ℤ)) (i + 1)) :=
    hd₀ (d : ℤ) (by omega) (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
  exact AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
    ι K hKq θ hcomm d k i hv
