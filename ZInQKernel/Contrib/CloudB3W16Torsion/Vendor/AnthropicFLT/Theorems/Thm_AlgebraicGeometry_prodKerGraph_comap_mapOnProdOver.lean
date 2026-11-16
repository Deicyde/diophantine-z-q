/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g') (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.solution
