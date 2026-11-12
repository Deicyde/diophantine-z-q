# glue-sqrt-local results log

## CycloPadic.lean
- `cyclotomic_prime_pow_comp_isEisensteinAt_padicInt`: Φ_{p^{n+1}}(X+1) ∈ ℤ_p[X] is Eisenstein at (p). VERIFIED (compiled).
- `cyclotomic_prime_pow_irreducible_padic`: Irreducible (cyclotomic (p^(n+1)) ℚ_[p]), every prime p. VERIFIED (compiled, axioms propext, Classical.choice, Quot.sound).

## SqrtFinite.lean (compiled; axioms propext, Classical.choice, Quot.sound)
- `exists_half_iff`: copied verbatim from glue-I6-rest SqrtChar.lean.
- `dvd_sub_or_add_of_dvd_sq_sub_one_odd`: p odd prime, p^k ∣ x²-1 → p^k ∣ x-1 ∨ p^k ∣ x+1. VERIFIED.
- `dvd_sub_or_add_of_dvd_sq_sub_one`: any prime p, p^{k+1} ∣ x²-1 → p^k ∣ x∓1 (p=2 handled). VERIFIED.
- `units_sq_eq_one_odd`: p odd, u ∈ (ZMod p^k)ˣ, u²=1 → u=±1. VERIFIED.
- `redU_sq_eq_one`: any p, u ∈ (ZMod p^{k+1})ˣ, u²=1 → reduction to (ZMod p^k)ˣ is ±1. VERIFIED.
- `cast_eq_zero_of_two_nsmul`: 2a=0 in ZMod 2f → a ↦ 0 in ZMod f. VERIFIED.
- `proj_two_torsion`, `sqrt_criterion_finite`: for χ : Additive (ZMod p^k)ˣ × ZMod f →+ ℚ/ℤ, χ∘proj (proj : (ZMod p^{k+1})ˣ × ZMod 2f → (ZMod p^k)ˣ × ZMod f) is twice a character iff χ(-1,0)=0. Every prime p, every k, f. VERIFIED.
