/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem isIntegrallyClosed_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {_} _ => ⟨0, Subsingleton.elim _ _⟩

theorem solution {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by
  by_cases hne : Nonempty U
  ·
    haveI := hne
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : U, hU.primeIdealOf x = y :=
      ⟨⟨hU.fromSpec.base y, hy⟩, hU.fromSpec.injective (by rw [hU.fromSpec_primeIdealOf])⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := by
      have := hU.isLocalization_stalk x
      rw [hx] at this
      exact this
    haveI := h x.1
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv
  ·
    have hU0 : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    subst hU0
    exact isIntegrallyClosed_of_subsingleton _
