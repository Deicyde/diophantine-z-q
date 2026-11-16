/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field
    (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A), ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field.solution
