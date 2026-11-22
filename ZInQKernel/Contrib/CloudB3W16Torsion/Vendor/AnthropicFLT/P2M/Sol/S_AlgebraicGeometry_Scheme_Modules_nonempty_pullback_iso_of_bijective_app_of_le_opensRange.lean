/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_of_bijective_app_of_le_opensRange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : Y.Modules) (L : X.Modules)
    (π : L ⟶ (Scheme.Modules.pushforward f).obj M)
    (hπ : ∀ U : X.Opens, U ≤ f.opensRange → Function.Bijective (π.app U)) :
    Nonempty ((Scheme.Modules.pullback f).obj L ≅ M) := by
  have happ : ∀ U : Y.Opens, ((restrictFunctor f).map π).app U = π.app (f ''ᵁ U) := fun U => rfl
  haveI : IsIso ((restrictFunctor f).map π) := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    rw [happ, ConcreteCategory.isIso_iff_bijective]
    exact hπ _ (f.image_le_opensRange U)
  exact ⟨((restrictFunctorIsoPullback f).app L).symm ≪≫ asIso ((restrictFunctor f).map π) ≪≫
    (restrictFunctorAdjCounitIso f).app M⟩
