/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0
(Copyright 2026 Anthropic, PBC; see NOTICE.upstream and LICENSE in this directory).
Upstream file: Theorems/Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.lean
Modification notice (2026-11-15, cloud batch-2 worker W12): import paths relocated (modules
already published under ZInQKernel/Contrib/CloudW02Connectedness/Vendor/AnthropicFLT, including
P2M.Util, are reused); two `backward.isDefEq` options added for Lean 4.35; further Lean 4.35 /
Mathlib 56a00585 API adaptations, if any, are listed in ../PORT_CHANGES.md. Declarations keep
their upstream names; mathematical statements are unchanged.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W13Shared.FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime

-- Lean 4.35 port: retain the source's permissive backward elaboration behavior.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
theorem Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.solution
