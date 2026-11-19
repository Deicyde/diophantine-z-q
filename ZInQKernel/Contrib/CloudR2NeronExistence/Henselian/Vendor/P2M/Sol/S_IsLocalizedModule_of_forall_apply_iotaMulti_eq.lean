import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_IsLocalizedModule_of_forall_apply_iotaMulti_eq.lean
Original Git blob: 1b919334643e4909897f204524db735a4800404f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_exteriorPower_exists_linearEquiv_baseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped _root_.TensorProduct



theorem solution
    {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (F : ⋀[R]^n M →ₗ[R] ⋀[A]^n N)
    (hF : ∀ m : Fin n → M, F (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti A n (fun i => f (m i))) :
    IsLocalizedModule S F := by
  classical
  have hf : IsBaseChange A f := (isLocalizedModule_iff_isBaseChange S A f).mp inferInstance
  rw [isLocalizedModule_iff_isBaseChange S A]

  obtain ⟨e₁, he₁⟩ := exteriorPower.exists_linearEquiv_baseChange R A M n

  let g : A ⊗[R] M ≃ₗ[A] N := hf.equiv
  let e₂ : ⋀[A]^n (A ⊗[R] M) ≃ₗ[A] ⋀[A]^n N :=
    LinearEquiv.ofLinear (exteriorPower.map n g.toLinearMap) (exteriorPower.map n g.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp]; simp)
      (by rw [← exteriorPower.map_comp]; simp)
  refine IsBaseChange.of_equiv (e₁.trans e₂) fun x => ?_

  have key : ∀ x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))),
      (e₁.trans e₂) ((1 : A) ⊗ₜ[R] x) = F x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [LinearEquiv.trans_apply, he₁, one_smul, hF]
      show exteriorPower.map n g.toLinearMap (exteriorPower.ιMulti A n fun i => (1 : A) ⊗ₜ[R] m i) = _
      rw [exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      show hf.equiv ((1 : A) ⊗ₜ[R] m i) = f (m i)
      rw [IsBaseChange.equiv_tmul, one_smul]
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [map_smul, ← hy, TensorProduct.tmul_smul, ← algebraMap_smul A r ((1 : A) ⊗ₜ[R] y), map_smul,
        algebraMap_smul]
  exact key x (by rw [exteriorPower.ιMulti_span]; trivial)


end P2MW.S_IsLocalizedModule_of_forall_apply_iotaMulti_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
