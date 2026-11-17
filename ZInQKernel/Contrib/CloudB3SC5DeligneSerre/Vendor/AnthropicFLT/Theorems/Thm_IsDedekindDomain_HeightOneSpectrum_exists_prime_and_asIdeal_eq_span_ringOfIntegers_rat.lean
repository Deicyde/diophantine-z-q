/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat (git blob 14bccc6ad67463e63f1348c4bed1151900cc868d, sha256 518e15709c654d3186e439dbc57fa69d50444e08ba62e43ca1c780b4a2874cd3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsDedekindDomain NumberField
theorem IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  revert v
  exact @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.solution
