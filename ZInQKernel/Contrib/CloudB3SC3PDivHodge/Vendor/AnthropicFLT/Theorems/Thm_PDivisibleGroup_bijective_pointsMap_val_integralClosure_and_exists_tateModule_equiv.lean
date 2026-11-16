/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Points
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} [inst_t2 : Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [inst_t3 : CommRing L] [inst_t4 : Algebra R L] :
    Function.Bijective (G.pointsMap (integralClosure R L).val) ∧
    (∀ σ : L ≃ₐ[R] L, ∃ σ' : integralClosure R L ≃ₐ[R] integralClosure R L,
        ∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) ∧
    (∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ z : G.Points (integralClosure R L),
          G.pointsMap (integralClosure R L).val (σ' • z) = σ • G.pointsMap (integralClosure R L).val z) ∧
    ∃ e : TateModule p (G.Points (integralClosure R L)) ≃ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (G.Points (integralClosure R L))) (n : ℕ),
          ((e x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
            G.pointsMap (integralClosure R L).val ((x : ℕ → G.Points (integralClosure R L)) n)) ∧
      ∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ x : TateModule p (G.Points (integralClosure R L)),
          e (G.tateModuleRep (integralClosure R L) σ' x) = G.tateModuleRep L σ (e x) :=
  @_root_.P2MW.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv.solution R inst_t1 p h inst_t2 G L inst_t3 inst_t4
