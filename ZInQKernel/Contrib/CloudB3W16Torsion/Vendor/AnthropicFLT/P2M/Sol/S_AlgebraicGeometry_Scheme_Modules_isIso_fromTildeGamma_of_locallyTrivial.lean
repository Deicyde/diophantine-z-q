/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (htriv : ∀ x : Spec (.of R), ∃ (V : (Spec (.of R)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    IsIso M.fromTildeΓ :=
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen M fun g =>
    AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ g
