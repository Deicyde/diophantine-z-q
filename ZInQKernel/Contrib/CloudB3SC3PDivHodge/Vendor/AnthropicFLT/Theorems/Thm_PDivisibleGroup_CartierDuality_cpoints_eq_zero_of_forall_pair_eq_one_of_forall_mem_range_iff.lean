/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
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
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule PadicComplex.smulCommClass_gal_padic PadicComplex.smulCommClass_padic_gal PadicComplex.uniformContinuousConstSMul_gal PadicComplex.mulSemiringAction
attribute [-simp] PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul PadicComplex.galAlgHom_apply PadicComplex.smul_algebraMap PadicComplex.norm_smul_eq PadicComplex.nnnorm_smul_eq PadicComplex.smul_coe

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
    (p : ℕ) [inst_t1 : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] K]
    {R : Type} [inst_t3 : CommRing R] [inst_t4 : Algebra R (PadicAlgCl p)]
    (hR : ∀ x : PadicAlgCl p, x ∈ Set.range (algebraMap R (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1)
    (hinj : Function.Injective (algebraMap R (PadicAlgCl p)))
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (g : G.CPoints R)
    (hg : ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
      ∀ (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) =
          G.cpointsProj (integralClosure R (PadicAlgCl p)) i
            (G.cpointsMap (Algebra.ofId R (integralClosure R (PadicAlgCl p))) g) →
      ∀ (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w),
        G'.pointsMkAdd (PadicAlgCl p) w
            (Additive.ofMul (G'.pointMap (integralClosure R (PadicAlgCl p)).val w ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) w →
        D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
            (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1) :
    g = 0 :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff.solution p inst_t1 K inst_t2 R inst_t3 inst_t4 hR hinj h G G' D g hg
