/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CompletedPoints
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

theorem PDivisibleGroup.exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
    (p : ℕ) [inst_t1 : Fact p.Prime] {R : Type} [inst_t2 : CommRing R] [inst_t3 : Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h)
    (X : G.CPoints (integralClosure R (PadicAlgCl p)))
    (hX : ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
        Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
      ∀ a : G.level w,
        IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a))) :
    ∃ X' : G.CPoints (integralClosure R (PadicAlgCl p)),
      (∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X' →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a))) ∧
      p • X' = X :=
  @_root_.P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff.solution p inst_t1 R inst_t2 inst_t3 hO h G X hX
