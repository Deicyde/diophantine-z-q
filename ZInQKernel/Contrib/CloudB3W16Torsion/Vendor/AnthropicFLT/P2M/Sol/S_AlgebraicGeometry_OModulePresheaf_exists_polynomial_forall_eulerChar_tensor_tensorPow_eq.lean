/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TensorProduct
open Opposite

noncomputable section

namespace P2mChiSheaf
open AlgebraicGeometry.OModulePresheaf hiding zero

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isInvertible_tensorPow (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) (n : ℕ) :
    Scheme.Modules.IsInvertible (L.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit V
  | succ n ih => exact ih.tensor ⟨hL⟩

section Compare

variable (M N : V.Modules)

abbrev cmp (U : V.Opens) : Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) →ₗ[Γ(V, U)] Γ(M ⊗ N, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)

theorem cmp_tmul (U : V.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    cmp M N U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [cmp]

def resTw {U U' : V.Opens} (h : U ≤ U') :
    Γ(M, U') ⊗[Γ(V, U')] Γ(N, U') →ₛₗ[(V.presheaf.map (homOfLE h).op).hom] Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) :=
  (ofModules π M).tensorResₛₗ (ofModules π N) h

theorem resTw_tmul {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) (y : Γ(N, U')) :
    resTw π M N h (x ⊗ₜ y) = M.presheaf.map (homOfLE h).op x ⊗ₜ N.presheaf.map (homOfLE h).op y := rfl

theorem cmp_resTw {U U' : V.Opens} (h : U ≤ U') (t : Γ(M, U') ⊗[Γ(V, U')] Γ(N, U')) :
    cmp M N U (resTw π M N h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [resTw_tmul, cmp_tmul, cmp_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cmp_res {U U' : V.Opens} (h : U ≤ U') (t : ((ofModules π M).twist N).obj U') :
    cmp M N U (((ofModules π M).twist N).res h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) :=
  cmp_resTw π M N h t

def cmpHom : AffHom ((ofModules π M).twist N) (ofModules π (M ⊗ N)) where
  app U :=
    { toFun := cmp M N U.1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r t => map_smul (cmp M N U.1)
        ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t }
  app_smul U a t := map_smul (cmp M N U.1) a t
  naturality h := LinearMap.ext fun t => cmp_res π M N h t

theorem cmpHom_app (U : V.affineOpens) (t : ((ofModules π M).twist N).obj U.1) :
    (cmpHom π M N).app U t = cmp M N U.1 t := rfl

theorem cmpHom_bijective (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent)
    (U : V.affineOpens) : Function.Bijective ((cmpHom π M N).app U) :=
  Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent π hM hN U

end Compare

theorem eulerChar_eq_of_bijective [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}
    (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) :
    F.eulerChar K = G.eulerChar K := by
  obtain ⟨⟨e0⟩, hS⟩ := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective φ hφ K
  have h : ∀ i, F.cechFinrank K i = G.cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_tensor_eq [IsSeparated π] (K : V.OrderedAffineCover) (M N : V.Modules)
    (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent) :
    (ofModules π (M ⊗ N)).eulerChar K = ((ofModules π M).twist N).eulerChar K :=
  (eulerChar_eq_of_bijective π K (cmpHom π M N) (cmpHom_bijective π M N hM hN)).symm

theorem main {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨p, hp, hpn⟩ :=
    OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq π K (ofModules π M) hc hq Y hY d hd L hL
  refine ⟨p, hp, fun n => ?_⟩
  have hqn : (ofModules π (L.tensorPow n)).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial π (L.tensorPow n) (isInvertible_tensorPow L hL n).1
  rw [eulerChar_ofModules_tensor_eq π K M (L.tensorPow n) hq hqn]
  exact hpn n

end P2mChiSheaf

end

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) :=
  P2mChiSheaf.main π K M hc hq Y hY d hd L hL
