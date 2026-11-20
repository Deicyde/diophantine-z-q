/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by
  have : ReflectsColimit (FGSubalgebra.diagram R A) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · rintro (x : A)
    exact ⟨⟨Algebra.adjoin R {x}, {x}, by rw [Finset.coe_singleton]⟩,
      (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : Algebra.adjoin R {x}), rfl⟩
  · rintro A₀ A₁ (x₀ : A₀.1) (x₁ : A₁.1) (h : (x₀ : A) = x₁)
    refine ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩, homOfLE (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1),
      homOfLE (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1), ?_⟩
    change (Subalgebra.inclusion (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1) x₀ : ↥(A₀.1 ⊔ A₁.1)) =
      Subalgebra.inclusion (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1) x₁
    exact Subtype.ext h
