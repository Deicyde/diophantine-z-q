/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_CompletionBridge
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CharacterDifferential
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PadicAlgCl_RingOfIntegers
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped TensorProduct in

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
    (p : ℕ) [inst_t1 : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n)
    (b : Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule) :
    ∃ dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]),
      (∀ (j : Fin n) (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (a • y) = (a : ℚ_[p]) • dα j y) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ x : PadicAlgCl p, τ x = σ x) →
          ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (G'.tateModuleRep (PadicAlgCl p) τ y) = σ • dα j y) ∧
      (∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ)
          (ψ : G'.Point (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v),
          G'.pointsMkAdd (PadicAlgCl p) v
              (Additive.ofMul (G'.pointMap
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).val v ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) v →
          ∀ z : integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)
              ⊗[PadicAlgCl.ringOfIntegers p K] G.cotangentModule,
            (G.cotangentModuleProj v).lTensor
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z =
              D.charDiff (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v ψ →
            ‖dα j y - ((TensorProduct.rid (PadicAlgCl.ringOfIntegers p K)
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p))
                ((b.coord j).lTensor
                  (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z) :
                  PadicAlgCl p) : ℂ_[p])‖ ≤
              (p : ℝ) ^ (-(v : ℤ))) :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers.solution p inst_t1 K inst_t2 h G G' D n hn b
