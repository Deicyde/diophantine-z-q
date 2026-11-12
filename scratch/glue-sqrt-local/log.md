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

## SqrtLocal.lean (combined file: CycloPadic + SqrtFinite + Gal section; compiled, axioms propext, Classical.choice, Quot.sound)
- `galEquivUnits p n L : Gal(L/ℚ_[p]) ≃* (ZMod (p^(n+1)))ˣ` for any L with IsCyclotomicExtension {p^(n+1)} ℚ_[p] L (Mathlib autEquivPow + our irreducibility). VERIFIED.
- `finrank_eq_totient`: finrank ℚ_[p] L = φ(p^(n+1)). VERIFIED.
- `tauNeg := galEquivUnits.symm (-1)`; `tauNeg_mul_self`: τ x · x = 1 for every x with x^(p^(n+1)) = 1; `tauNeg_sq`. VERIFIED.
- `gal_sqrt_criterion` (p odd): χ : Additive Gal(L/ℚ_[p]) →+ AddCircle (1:ℚ) is 2ψ for some ψ iff χ(τ₋₁) = 0. VERIFIED.

## Frob.lean (compiled; axioms propext, Classical.choice, Quot.sound)
- `card_quotient_maximalIdeal`: Nat.card (ℤ_[p] ⧸ maximalIdeal) = p. VERIFIED.
- `exists_frobenius`: L/ℚ_p finite Galois (with [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]) → ∃ σ ∈ Gal(L/ℚ_p), ∀ m, ¬p∣m → ∀ ζ, ζ^m = 1 → σ ζ = ζ^p. VERIFIED.
  Proof: S = integralClosure ℤ_[p] L; IsGaloisGroup.of_isFractionRing; IsIntegralClosure.finite; Q maximal over (p) (exists_maximal_ideal_liesOver_of_isIntegral); S/Q finite; IsArithFrobAt.exists_of_isInvariant; IsArithFrobAt.apply_of_pow_eq_one.
- `eq_of_pow_eq_one_of_sub_mem`: in a domain, m-th roots of unity x, y with x - y ∈ Q, (m:R) ∉ Q are equal. VERIFIED.
- `pow_frobenius_of_isLocalRing`: if IsLocalRing (integralClosure ℤ_[p] L), every τ ∈ Gal(L/ℚ_p) has n with τ ζ = ζ^(p^n) for all prime-to-p roots of unity ζ. VERIFIED (compiled; the locality of the integral closure is a hypothesis, STANDARD, not proved).
  Proof: τ stabilizes the maximal ideal; stabilizerHom τ ∈ Gal((S/Q)/𝔽_p) = ⟨Frob⟩ (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow); roots of unity separate mod Q.
- `autToPow_eq_of_apply`: σ ζ = ζ^k (ζ primitive m-th root) → autToPow σ = k in ZMod m. VERIFIED.
- `range_autToPow_eq_zpowers`: p ∤ m, ζ primitive m-th root in L (L/ℚ_p finite Galois), IsLocalRing (integralClosure ℤ_[p] L) → range (autToPow : Gal(L/ℚ_p) → (ZMod m)ˣ) = zpowers (p mod m). VERIFIED (locality hypothesis).

## Local.lean / Unramified.lean (compiled; axioms propext, Classical.choice, Quot.sound)
- `isIntegral_iff_spectralNorm_le_one`: y ∈ L (L/ℚ_p finite) integral over ℤ_p ↔ spectralNorm ℚ_[p] L y ≤ 1. VERIFIED.
- `isLocalRing_integralClosure`: IsLocalRing (integralClosure ℤ_[p] L). VERIFIED. (units = norm 1; nonunits = norm < 1, closed under + by isNonarchimedean_spectralNorm; multiplicativity from spectralMulAlgNorm, ℚ_p complete.)
- Unramified.lean = Frob.lean + Local.lean merged; adds unconditional `pow_frobenius` and `range_autToPow_eq_zpowers'`: for p ∤ m, ζ primitive m-th root in finite Galois L/ℚ_p, range(autToPow) = zpowers (p mod m). VERIFIED.
- `finrank_eq_orderOf`: p ∤ m, IsCyclotomicExtension {m} ℚ_[p] L → finrank ℚ_[p] L = orderOf (p : (ZMod m)ˣ). VERIFIED.
- `isCyclic_gal`: same hypotheses → IsCyclic Gal(L/ℚ_[p]). VERIFIED.
- Note: Unramified.lean's ambient variables include [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]; for a cyclotomic L the last two are Mathlib instances/theorems and the first two come from Algebra.compHom.
