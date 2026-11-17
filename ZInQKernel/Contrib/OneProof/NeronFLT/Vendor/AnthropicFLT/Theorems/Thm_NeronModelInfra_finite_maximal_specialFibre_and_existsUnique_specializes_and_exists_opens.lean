/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens.solution
