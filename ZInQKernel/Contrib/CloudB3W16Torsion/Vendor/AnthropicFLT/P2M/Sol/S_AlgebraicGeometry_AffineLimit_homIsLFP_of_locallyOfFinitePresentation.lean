/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AffineLimit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_FGSubalgebra_nonempty_isLimit_specCone
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ξ] : AffineLimit.HomIsLFP ξ := by
  refine ⟨fun A _ _ φ hφ ↦ ?_, fun A _ _ A₀ hA₀ φ₀ φ₀' h₀ h₀' hφ ↦ ?_⟩
  · obtain ⟨⟨A₀, hA₀⟩, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some φ
      (by rw [FGSubalgebra.specCone_π_comp_specOver]; exact congrArg _ hφ.symm)
    exact ⟨A₀, hA₀, g, hg', hg⟩
  · obtain ⟨⟨A₁, hA₁⟩, ⟨⟨⟨h⟩⟩⟩, H⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (FGSubalgebra.specDiagram R A) (FGSubalgebra.specOver R A) ξ (FGSubalgebra.specCone R A)
      (FGSubalgebra.nonempty_isLimit_specCone R A).some (i := Opposite.op ⟨A₀, hA₀⟩) φ₀ φ₀'
      h₀.symm h₀'.symm hφ
    exact ⟨A₁, hA₁, h, H⟩
