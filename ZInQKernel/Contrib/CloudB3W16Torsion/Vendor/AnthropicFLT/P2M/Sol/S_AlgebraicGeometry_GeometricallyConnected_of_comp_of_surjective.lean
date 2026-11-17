/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩

  have hX : ConnectedSpace ↥(pullback (f ≫ g) k) :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K k

  let φ : pullback (f ≫ g) k ⟶ pullback g k :=
    pullback.map (f ≫ g) k g k f (𝟙 _) (𝟙 Z) (Category.comp_id _) (by simp)
  have hφ : Surjective φ :=
    MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective f› inferInstance rfl
      (Category.id_comp _).symm
  rw [connectedSpace_iff_univ, ← hφ.surj.range_eq]
  exact isConnected_range φ.continuous
