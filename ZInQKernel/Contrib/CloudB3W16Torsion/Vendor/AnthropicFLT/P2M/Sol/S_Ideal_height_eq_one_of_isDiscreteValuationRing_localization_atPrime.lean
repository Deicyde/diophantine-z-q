/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by
  haveI := h
  have hnf : ¬ IsField (Localization.AtPrime p) := fun hF =>
    IsDiscreteValuationRing.not_a_field (R := Localization.AtPrime p)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have hd1 : ringKrullDim (Localization.AtPrime p) = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one (Localization.AtPrime p) hnf
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at hd1
  exact_mod_cast hd1
