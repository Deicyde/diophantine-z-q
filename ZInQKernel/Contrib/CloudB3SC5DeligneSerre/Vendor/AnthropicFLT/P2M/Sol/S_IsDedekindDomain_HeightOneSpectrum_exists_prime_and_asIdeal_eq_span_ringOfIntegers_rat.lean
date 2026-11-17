/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat (git blob d56d99d0006fec93476a95bf1c3b360df7b13155, sha256 e577cecd18ddf6d8cfa707cf92b4b3cc4fa27575cbfa2c8fb13cea12daceb1d7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_⟩
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have h : Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
    (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v).symm
  have h3 : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) (Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal) = v.asIdeal :=
    Ideal.map_of_equiv e
  rw [← h3, h, Ideal.map_span, Set.image_singleton]
  congr 2
  simp
