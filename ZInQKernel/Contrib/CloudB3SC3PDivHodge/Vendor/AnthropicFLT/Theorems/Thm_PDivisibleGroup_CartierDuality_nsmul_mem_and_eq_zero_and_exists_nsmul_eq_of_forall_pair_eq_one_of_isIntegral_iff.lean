/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CartierDuality
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CompletedPoints
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule
attribute [-simp] PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
    (p : ℕ) [inst_t1 : Fact p.Prime] {R : Type} [inst_t2 : CommRing R] [inst_t3 : Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (Ker G₁ Inv : Set (G.CPoints (integralClosure R (PadicAlgCl p))))
    (hKer : ∀ Y, Y ∈ Ker ↔
      ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
            Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) i Y →
        ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
          G'.pointsMkAdd (PadicAlgCl p) w
              (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) w →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
              (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1)
    (hG₁ : ∀ X, X ∈ G₁ ↔
      ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (hInv : ∀ X, X ∈ Inv ↔
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
        (σ' : integralClosure R (PadicAlgCl p) ≃ₐ[R] integralClosure R (PadicAlgCl p)),
        (∀ a : integralClosure R (PadicAlgCl p),
            ((σ' a : integralClosure R (PadicAlgCl p)) : PadicAlgCl p) = σ a) →
        σ' • X = X) :
    (∀ Y ∈ Ker, ∀ n : ℕ, n • Y ∈ Ker) ∧
    (∀ Y ∈ Ker, ∀ k : ℕ, p ^ k • Y = 0 → Y = 0) ∧
    (∀ X ∈ Ker, X ∈ G₁ → X ∈ Inv → ∃ X₁ ∈ Ker, X₁ ∈ G₁ ∧ X₁ ∈ Inv ∧ p • X₁ = X) :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff.solution p inst_t1 R inst_t2 inst_t3 hO h G G' D Ker G₁ Inv hKer hG₁ hInv
