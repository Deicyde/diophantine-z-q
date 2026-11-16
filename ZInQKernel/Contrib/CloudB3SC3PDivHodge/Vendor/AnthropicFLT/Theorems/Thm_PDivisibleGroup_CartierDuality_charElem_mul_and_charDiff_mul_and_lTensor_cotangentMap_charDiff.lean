/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CharacterDifferential
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (S : Type) [inst_t2 : CommRing S] [inst_t3 : Algebra R S] (v : ℕ) :
    (∀ (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)),
        TensorProduct.rid R S (φ.lTensor S (D.charElem S v ψ)) =
          Point.toAlgHom ψ ((D.toDualEquiv v).symm φ)) ∧
    (∀ (f : G.Point S v) (ψ : G'.Point S v),
        Algebra.TensorProduct.lift (AlgHom.id R S) (Point.toAlgHom f) (fun _ _ => .all _ _)
          (D.charElem S v ψ) = D.pair S v f ψ) ∧
    (∀ ψ ψ' : G'.Point S v, D.charElem S v (ψ * ψ') = D.charElem S v ψ * D.charElem S v ψ') ∧
    D.charElem S v 1 = 1 ∧
    (∀ ψ ψ' : G'.Point S v, D.charDiff S v (ψ * ψ') = D.charDiff S v ψ + D.charDiff S v ψ') ∧
    D.charDiff S v 1 = 0 ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        Algebra.TensorProduct.map σ (AlgHom.id R (G.level v)) (D.charElem S v ψ) =
          D.charElem S' v (G'.pointMap σ v ψ)) ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        TensorProduct.map σ.toLinearMap LinearMap.id (D.charDiff S v ψ) =
          D.charDiff S' v (G'.pointMap σ v ψ)) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.transitionAlgHom v).toLinearMap.lTensor S (D.charElem S (v + 1) ψ₁) = D.charElem S v ψ) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.cotangentMap v).lTensor S (D.charDiff S (v + 1) ψ₁) = D.charDiff S v ψ) :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff.solution R inst_t1 p h G G' D S inst_t2 inst_t3 v
