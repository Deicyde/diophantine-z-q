/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.free_and_finrank_quotient_span_of_generates_ker_pow
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow.solution
