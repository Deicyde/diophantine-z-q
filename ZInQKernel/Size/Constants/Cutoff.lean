import ZInQKernel.Size.Constants.T

/-!
# The literal cutoff (Proposition 12.1)

Blueprint: `size/cutoff.md`.

Under the catalogue bound: `R = D`; `T = (48 A_ht)^13 = (96·10^13)^13 · D^(2210 G₀² D³)` with
`A_ht = 2·10^13 · max(1, C_cm, Q^17) = 2·10^13 · Q^17` and `Q = R^(R E₀) = D^(10 G₀² D³)`; and
`T < 2^(2^(2^9013))`. Moreover the least formal multiple search succeeds: `N_s ≥ 1`,
`1 ≤ M₀ ≤ N_s^10`, and the normalized representation `(a, b, c)` of `ξ([M₀]P₀)` has
`N_s⁴ ∣ a`, `N_s⁴ ∣ b` and `gcd(c, N_s) = 1`. This part does not need the catalogue bound
(`formal_multiple_succeeds`): `N_s ≥ 1` follows from Dirichlet's theorem.
-/

namespace ZInQ.Size

open Syntax AmbientPow

/-- The least formal multiple search succeeds for `N_s`. -/
theorem formal_multiple_succeeds :
    1 ≤ Ns ∧ 1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧
      (Ns : ℤ) ^ 4 ∣ (normalizedRep (xi (M0 • genP0))).1 ∧
      (Ns : ℤ) ^ 4 ∣ (normalizedRep (xi (M0 • genP0))).2.1 ∧
      Nat.Coprime (normalizedRep (xi (M0 • genP0))).2.2 Ns :=
  ⟨Ns_pos, (M0_bounds Ns_pos).1, (M0_bounds Ns_pos).2.1, (M0_bounds Ns_pos).2.2⟩

/-- **Proposition 12.1** (the literal cutoff). -/
theorem literal_cutoff (hCAT : CatalogueBound8) :
    R = D ∧
    (T = (48 * Aht) ^ 13 ∧ T = (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G0 ^ 2 * D ^ 3) ∧
      Aht = 2 * 10 ^ 13 * max (max 1 Ccm) (Q ^ 17) ∧ Aht = 2 * 10 ^ 13 * Q ^ 17 ∧
      Q = R ^ (R * E0) ∧ Q = D ^ (10 * G0 ^ 2 * D ^ 3)) ∧
    T < 2 ^ 2 ^ 2 ^ 9013 ∧
    (1 ≤ Ns ∧ 1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧
      (Ns : ℤ) ^ 4 ∣ (normalizedRep (xi (M0 • genP0))).1 ∧
      (Ns : ℤ) ^ 4 ∣ (normalizedRep (xi (M0 • genP0))).2.1 ∧
      Nat.Coprime (normalizedRep (xi (M0 • genP0))).2.2 Ns) :=
  ⟨R_eq_D hCAT,
    ⟨T_eq, T_eq_closed hCAT, Aht_eq, (Aht_eq_closed hCAT).1, Q_eq, Q_eq_closed hCAT⟩,
    T_lt hCAT, formal_multiple_succeeds⟩

end ZInQ.Size
