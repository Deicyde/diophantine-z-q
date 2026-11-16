/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution {U S : Scheme.{u}} (f : U ⟶ S) [Smooth f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by

  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := y) (U := ⊤) trivial

  have hle : W ≤ f ⁻¹ᵁ ⊤ := by simp
  letI : Algebra Γ(S, ⊤) Γ(U, W) := (f.appLE ⊤ W hle).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, ⊤) Γ(U, W) := Smooth.smooth_appLE f (isAffineOpen_top S) hW hle

  letI : Algebra Γ(U, W) (U.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  haveI : IsLocalization.AtPrime (U.presheaf.stalk y) (hW.primeIdealOf ⟨y, hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hyW⟩
  exact Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime Γ(S, ⊤) Γ(U, W)
    (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y)
