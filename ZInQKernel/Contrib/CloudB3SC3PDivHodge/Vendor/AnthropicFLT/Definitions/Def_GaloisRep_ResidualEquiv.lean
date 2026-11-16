/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_GaloisRep_ResidualEquiv
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped TensorProduct

namespace ResidualGaloisRep

variable {k : Type} [Field k]

structure Equiv (ρ₁ ρ₂ : ResidualGaloisRep k) where

  toLinearEquiv : ρ₁.V ≃ₗ[k] ρ₂.V

  map_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ρ₁.V),
    toLinearEquiv (ρ₁.ρ σ x) = ρ₂.ρ σ (toLinearEquiv x)

def IsEquiv (ρ₁ ρ₂ : ResidualGaloisRep k) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

def refl (ρ : ResidualGaloisRep k) : Equiv ρ ρ where
  toLinearEquiv := LinearEquiv.refl k ρ.V
  map_apply _ _ := rfl

def symm {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) : Equiv ρ₂ ρ₁ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_apply σ x := by
    apply e.toLinearEquiv.injective
    rw [e.map_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def trans {ρ₁ ρ₂ ρ₃ : ResidualGaloisRep k} (e₁₂ : Equiv ρ₁ ρ₂) (e₂₃ : Equiv ρ₂ ρ₃) :
    Equiv ρ₁ ρ₃ where
  toLinearEquiv := e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv
  map_apply σ x := by
    rw [LinearEquiv.trans_apply, e₁₂.map_apply, e₂₃.map_apply, LinearEquiv.trans_apply]

noncomputable def baseChangeAlong {k' : Type} [Field k'] (ψ : k →+* k')
    {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChangeAlong ψ) (ρ₂.baseChangeAlong ψ) :=
  letI : Algebra k k' := ψ.toAlgebra
  { toLinearEquiv := e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange k' x) =
        (ρ₂.ρ σ).baseChange k' (e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

end Equiv

end ResidualGaloisRep
