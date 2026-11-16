/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_HopfAlgebra_canMap_surjective_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_HopfAlgebra_canMap_surjective_of_surjective

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped TensorProduct
open HopfAlgebra

namespace P2mS17CS

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
variable {B : Type w} [CommRing B] [Bialgebra R B]
variable (π : A →ₐc[R] B)

theorem canAlgHom_tmul_one (a : A) : canAlgHom π (a ⊗ₜ[R] 1) = a ⊗ₜ[R] 1 := by
  rw [canAlgHom_tmul, map_one, mul_one]

theorem canAlgHom_antipode_comul (a' : A) :
    canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a')) = (1 : A) ⊗ₜ[R] π a' := by

  set Φ : (A ⊗[R] A) ⊗[R] A →ₗ[R] A ⊗[R] B :=
    (π : A →ₐ[R] B).toLinearMap.lTensor A ∘ₗ
      (LinearMap.mul' R A).rTensor A ∘ₗ
      ((HopfAlgebra.antipode R (A := A)).rTensor A).rTensor A with hΦ

  have step1 : (canAlgHom π : A ⊗[R] A →ₐ[R] A ⊗[R] B).toLinearMap
        ∘ₗ (HopfAlgebra.antipode R (A := A)).rTensor A
      = Φ ∘ₗ (TensorProduct.assoc R A A A).symm.toLinearMap
          ∘ₗ (Coalgebra.comul (R := R) (A := A)).lTensor A :=
    TensorProduct.ext' fun u v => by
      have inner : ∀ z : A ⊗[R] A,
          ((HopfAlgebra.antipode R u : A) ⊗ₜ[R] (1 : B)) *
              (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)) z
            = Φ ((TensorProduct.assoc R A A A).symm (u ⊗ₜ[R] z)) := fun z => by
        induction z with
        -- [port] tensor-product induction has no `zero` case in Mathlib 56a0; upstream `zero` alternative removed
        | add x y hx hy =>
            simp only [map_add, mul_add, TensorProduct.tmul_add] at *; rw [hx, hy]
        | tmul x y =>
            simp only [hΦ, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
              Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.assoc_symm_tmul,
              LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
              LinearMap.lTensor_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
        canAlgHom_tmul, HopfAlgebra.coaction, AlgHom.comp_apply]
      exact inner _

  have step2 : canAlgHom π ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a'))
      = Φ ((Coalgebra.comul (R := R) (A := A)).rTensor A (Coalgebra.comul a')) := by
    have h := LinearMap.congr_fun step1 (Coalgebra.comul (R := R) a')
    have hco := LinearMap.congr_fun (Coalgebra.coassoc (R := R) (A := A)) a'
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearEquiv.coe_coe] at h hco
    rw [h, ← hco, LinearEquiv.symm_apply_apply]

  rw [step2, hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
    ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := A),
    LinearMap.rTensor_comp_apply, Coalgebra.rTensor_counit_comul,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  simp

theorem canAlgHom_surjective (hπ : Function.Surjective π) : Function.Surjective (canAlgHom π) := fun z => by
  induction z with
  -- [port] tensor-product induction has no `zero` case in Mathlib 56a0; upstream `zero` alternative removed
  | tmul a c =>
      obtain ⟨a', ha'⟩ := hπ c
      exact ⟨(a ⊗ₜ[R] (1 : A)) *
          ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a')), by
        rw [_root_.map_mul, canAlgHom_tmul_one, canAlgHom_antipode_comul, ha',
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩
  | add y z hy hz =>
      obtain ⟨py, hy⟩ := hy; obtain ⟨pz, hz⟩ := hz
      exact ⟨py + pz, by rw [map_add, hy, hz]⟩

end P2mS17CS

open P2mS17CS in
theorem solution {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) :=
  canAlgHom_surjective π hπ
