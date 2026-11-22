/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IntermediateField

universe u

namespace AlgebraicCurve.CurveModel

theorem isProper_smooth_places_affineCover_glued (K : Type u) [Field K] [Infinite K]
    [PerfectField K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L] [Algebra.IsSeparable ↥K⟮t⟯ L] :
    IsProper (gluedToBase K t) ∧
    SmoothOfRelativeDimension 1 (gluedToBase K t) ∧
    (∃ P : closedPoints (glued K t) → Place K L, Function.Bijective P ∧
      ∀ x : closedPoints (glued K t),
        (((gluedFunctionFieldEquiv K t).symm : (glued K t).functionField ≃+* L).toRingHom.comp
            (algebraMap ((glued K t).presheaf.stalk x.1) (glued K t).functionField)).range =
          (P x).toValuationSubring.toSubring) ∧
    (∀ F : Finset (glued K t), ∃ U : (glued K t).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution
