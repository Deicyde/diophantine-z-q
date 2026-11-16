/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CharacterDifferential
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} [inst_t2 : Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (S : Type) [inst_t3 : CommRing S] [inst_t4 : Algebra R S] :
    ∃ HT : TateModule p (G'.Points S) →+ ((v : ℕ) → TensorProduct R S (G.Cotangent v)),
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ) (ψ : G'.Point S v),
          G'.pointsMkAdd S v (Additive.ofMul ψ) = (y : ℕ → G'.Points S) v →
            HT y v = D.charDiff S v ψ) ∧
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ),
          (G.cotangentMap v).lTensor S (HT y (v + 1)) = HT y v) ∧
      (∀ (a : ℤ_[p]) (y : TateModule p (G'.Points S)) (v : ℕ), HT (a • y) v = a.appr v • HT y v) ∧
      (∀ (σ : S ≃ₐ[R] S) (y : TateModule p (G'.Points S)) (v : ℕ),
          HT (G'.tateModuleRep S σ y) v =
            TensorProduct.map (σ : S →ₐ[R] S).toLinearMap LinearMap.id (HT y v)) :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff.solution R inst_t1 p h inst_t2 G G' D S inst_t3 inst_t4
