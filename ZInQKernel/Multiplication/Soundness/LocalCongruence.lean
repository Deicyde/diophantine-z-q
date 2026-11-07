import ZInQKernel.Multiplication.Soundness.TestsToCongruence

/-!
# The congruence at an odd contact prime

Blueprint: `multiplication/soundness/local-congruence.md`.

If `t` satisfies `Slope(t, ℓ; c₀, c₀n₁, c₀n₂, c₀n₃)` and `p` is an odd contact prime of `t` with
`p > 324`, `p ∤ c₀` and `v_p(ℓ) = 0`, then `n₁n₂ ≡ n₃ (mod p²⁵)` (`local_congruence_of`). In the
certificate `ℓ = ℓ₀`, `c₀ = c_*`, and the three conditions on `p` are the properties of the
primes outside `S_mul`.
-/

namespace ZInQ.Mult



variable {p : ℕ} [hp : Fact p.Prime]

/-- **The congruence at an odd contact prime**, for an arbitrary normalization `ℓ` and shift
`c₀`: the properties of `p` used are `p > 324`, `p ∤ c₀` and `v_p(ℓ) = 0`. -/
theorem local_congruence_of (hp324 : 324 < p) {t ℓ : ℚ} {c₀ : ℤ} (n : Fin 3 → ℤ)
    (hc₀ : ¬ (p : ℤ) ∣ c₀) (hℓ : padicValRat p ℓ = 0)
    (hs : SlopePred t ℓ ![c₀, c₀ * n 0, c₀ * n 1, c₀ * n 2]) {c : ℚ} (hc : c ∈ contactSet)
    (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
    (p : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 := by
  obtain ⟨ht, ht1, hℓ0, η, q, h, z, hη, ha, hhc, hW, hΘ, hΦ⟩ := hs
  obtain ⟨g, π, hπ, hπp, hv⟩ := common_group_of hp324 ht ht1 hη hℓ0 hℓ ha
    (fun g => testValues (h g) (z g) ![c₀, c₀ * n 0, c₀ * n 1, c₀ * n 2]) hW hΘ hΦ hc hk hodd
  exact tests_to_congruence hp324 hπ hπp hc₀ n (z g) (hhc g).1 (hhc g).2 hv

/-- **The congruence at an odd contact prime.** If `t`
satisfies `Slope(t, ℓ₀; c_*, c_*n₁, c_*n₂, c_*n₃)` and `p ∉ S_mul` is an odd contact prime of
`t`, then `n₁n₂ ≡ n₃ (mod p²⁵)`. -/
theorem local_congruence (n : Fin 3 → ℤ) {t : ℚ}
    (hs : SlopePred t (Syntax.ell : ℚ) (certShifts n)) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S_mul)
    (hcontact : IsOddContactPrime t p) : (p : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h324, hc, -, -⟩ := not_mem_S_mul hp hpS
  obtain ⟨-, c, hcC, hk, hodd⟩ := hcontact
  exact local_congruence_of h324 n (by exact_mod_cast hc)
    (padicValRat_ell_of_not_mem fun hb => hpS (S_b_subset_S_mul hb)) hs hcC hk hodd

end ZInQ.Mult
