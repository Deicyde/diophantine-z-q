/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem (git blob b0b52a5c14ee145d51d0be50c5312bc7087a82a1, sha256 ecec19f38c19f56140bfb0ddf6bfa476d11e80513c6d0fa4601ce31eeb1fa8f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem

set_option autoImplicit false

theorem solution {K : Type*} [CommRing K] (R : Subring K)
    (P U : PowerSeries K) (m₀ L : ℕ)
    (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
    (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
    (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
    (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
    (n : ℕ) (hn : n + m₀ < L) :
    PowerSeries.coeff n P ∈ R := by
  obtain ⟨v, hv, hvu⟩ := hU₁
  induction n using Nat.strong_induction_on with
  | _ n ih =>

    have hsum := PowerSeries.coeff_mul (n + m₀) P U

    have hmem : (n, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n + m₀) := by simp
    rw [← Finset.add_sum_erase _ _ hmem] at hsum

    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U ∈ R := by
      refine Subring.sum_mem _ fun x hx => ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rcases lt_trichotomy x.1 n with hlt | heq | hgt
      · exact Subring.mul_mem _ (ih x.1 hlt (by omega)) (hU x.2)
      · exfalso; apply hne
        have : x.2 = m₀ := by omega
        exact Prod.ext heq this
      · have : x.2 < m₀ := by omega
        rw [hU₀ x.2 this, mul_zero]
        exact Subring.zero_mem _

    have hkey : PowerSeries.coeff n P = v * (PowerSeries.coeff (n + m₀) (P * U) -
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U) := by
      rw [hsum, add_sub_cancel_right, mul_comm v, mul_assoc, mul_comm _ v, hvu, mul_one]
    rw [hkey]
    exact Subring.mul_mem _ hv (Subring.sub_mem _ (hPU _ hn) hrest)
