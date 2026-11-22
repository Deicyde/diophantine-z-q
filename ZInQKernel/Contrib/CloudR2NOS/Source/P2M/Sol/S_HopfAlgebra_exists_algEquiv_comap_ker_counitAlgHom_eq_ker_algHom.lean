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
  Source file    : P2M/Sol/S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean
  Source sha256  : d13de92a5a410c0706f68f809e4d680876c887e9b719726d37fe46eb0abbf52c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
r2nos_namespace_dual

w03_open "Bialgebra Coalgebra TensorProduct Bialgebra.TensorProduct Coalgebra.TensorProduct"

noncomputable section

namespace HopfRightTranslate
r2nos_namespace_dual

universe u v

variable (K : Type u) [Field K] (A : Type v) [CommRing A] [HopfAlgebra K A]

def rightTranslate (χ : A →ₐ[K] K) : A →ₐ[K] A :=
  (Algebra.TensorProduct.rid K K A).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id K A) χ).comp (comulAlgHom K A))

def antipodeAlgHom : A →ₐ[K] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode K) HopfAlgebra.antipode_one
    (fun a b => (HopfAlgebra.antipode_mul a b).trans (mul_comm _ _))

variable {K A}

theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom K A a = HopfAlgebra.antipode K a := rfl

theorem rightTranslate_apply_repr (χ : A →ₐ[K] K) (a : A) {ιrepr : Type*} (repr : Coalgebra.Repr K a ιrepr) :
    rightTranslate K A χ a = ∑ i ∈ repr.index, χ (repr.right i) • repr.left i := by
  show (Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A a)) = _
  have hcomul : comulAlgHom K A a = Coalgebra.comul (R := K) a := rfl
  rw [hcomul, ← repr.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul]

theorem sum_counit_right_smul {a : A} {ιrepr : Type*} (repr : Coalgebra.Repr K a ιrepr) :
    ∑ i ∈ repr.index, Coalgebra.counit (R := K) (repr.right i) • repr.left i = a := by
  have h := Coalgebra.sum_tmul_counit_eq (R := K) repr
  have h2 := congrArg (TensorProduct.rid K A) h
  simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h2
  exact h2

theorem counitAlgHom_comp_rightTranslate (χ : A →ₐ[K] K) :
    (counitAlgHom K A).comp (rightTranslate K A χ) = χ := by
  ext x
  show (counitAlgHom K A) ((Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A x))) = χ x
  have hcomul : comulAlgHom K A x = Coalgebra.comul (R := K) x := rfl
  rw [hcomul]
  have hmap : ((counitAlgHom K A).toLinearMap.comp
        (Algebra.TensorProduct.rid K K A).toLinearMap).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) χ).toLinearMap
      = (TensorProduct.lid K K).toLinearMap.comp
          (χ.toLinearMap.lTensor K |>.comp ((Coalgebra.counit (R := K)).rTensor A)) := by
    ext a b
    simp [Algebra.TensorProduct.rid_tmul, TensorProduct.lid_tmul, Algebra.smul_def, mul_comm]
  have h2 := congrArg (· (Coalgebra.comul (R := K) x)) (congrArg DFunLike.coe hmap)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_toLinearMap, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul,
    TensorProduct.lid_tmul, one_smul] at h2
  exact h2

theorem rightTranslate_leftInverse (χ : A →ₐ[K] K) :
    Function.LeftInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr χ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A ψ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        ψ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr ψ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp ψ.toLinearMap).compl₂ χ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (ψ y * χ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ (R0.right i) * ψ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ ((a₁ i).right j) * χ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_antipode_mul_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

theorem rightTranslate_rightInverse (χ : A →ₐ[K] K) :
    Function.RightInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr ψ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A χ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        χ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr χ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp χ.toLinearMap).compl₂ ψ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (χ y * ψ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ (R0.right i) * χ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ ((a₁ i).right j) * ψ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_mul_antipode_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

def rightTranslateEquiv (χ : A →ₐ[K] K) : A ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (rightTranslate K A χ)
    (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
    (AlgHom.ext (rightTranslate_rightInverse χ))
    (AlgHom.ext (rightTranslate_leftInverse χ))

theorem rightTranslateEquiv_apply (χ : A →ₐ[K] K) (a : A) :
    rightTranslateEquiv χ a = rightTranslate K A χ a := rfl

theorem comap_ker_counitAlgHom_rightTranslate (χ : A →ₐ[K] K) :
    (RingHom.ker (counitAlgHom K A).toRingHom).comap (rightTranslate K A χ).toRingHom
      = RingHom.ker χ.toRingHom := by
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := DFunLike.congr_fun (counitAlgHom_comp_rightTranslate χ) a
  simp only [AlgHom.comp_apply] at this
  rw [this]

end HopfRightTranslate

end

theorem solution
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom := by
  refine ⟨HopfRightTranslate.rightTranslateEquiv χ, ?_⟩
  show (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap
      (HopfRightTranslate.rightTranslate K A χ).toRingHom = RingHom.ker χ.toRingHom
  exact HopfRightTranslate.comap_ker_counitAlgHom_rightTranslate χ
end S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
