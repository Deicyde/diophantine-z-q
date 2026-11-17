/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one (git blob a8a543a3924c33964afaaeea50757eb965a791ab, sha256 3932afe3fd6e257db41ae43cda9f979aadaf2571a7a951c2a2d1ff71884e22f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one

open IsLocalRing

namespace RankOneNilSol

theorem exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end RankOneNilSol

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n :=
  RankOneNilSol.exists_dvd_pow hb hc
