# redei-fp log

## Step 1: Redei/Field.lean — DONE (compiles with `lake env lean`)
- card_gal, omega_sq, isIntegral_omega, omegaO (+ simp lemmas), omegaO_sq, theta_eq, isIntegral_theta,
  thetaO, two_mul_thetaO, conj_omega, conj_apply (σ = star), conj_unique, conj_conj, conj_mul_self,
  eq_one_or_eq_conj, exists_conj_ne_one, algebraMap_smul, conj_omegaO, algNorm_eq, norm_eq_mul_conj,
  norm_nonneg, algNorm_coe, normZ_nonneg, normZ_eq_mul_conj, finrank_int, normZ_intCast, normZ_natCast,
  normZ_omega, exists_int_of_coe_eq_algebraMap (O ∩ ℚ = ℤ), intCast_injective, intCast_dvd_intCast_iff,
  isUnit_intCast_iff, rat_unit_eq, natCast_dvd_natCast_iff, span_natCast_eq_span_natCast_iff.
- Fixes: `ext` on 𝓞 K descends into re/im → use `apply RingOfIntegers.ext`; `AlgEquiv.ext fun x => _`;
  map_smul for AlgEquiv failed (MulActionHomClass) → Algebra.smul_def + AlgEquiv.commutes;
  re_one/im_one are scoped simp lemmas → pass explicitly.

## Step 2: Redei/Primes.lean — DONE (515 lines; plan estimate 500)
- prime_trichotomy proved WITHOUT ramification indices: P ∣ pO (N(pO) = p²), so N P ∈ {p, p²};
  N P = p² ⇒ P = pO; N P = p ⇒ pO = P·M with N M = p, M prime over p, M = τ•P (Galois transitivity
  `Ideal.exists_smul_eq_of_isGaloisGroup`), τ ∈ {1, σ}.
- dvd_of_ramified: residue field O/P ≅ ZMod p (charP_of_card_eq_prime + castHom bijective), x − σx ∈ P,
  x = ω and x = θ.
- ramified_of_dvd / ramified_two via mem_span_of_mul_self_mem (split: P ⊓ σP = PσP) + norms.
- ramSet (no NeZero), ramIdeal (chosen maximal ideal over p, ⊤ if p not prime), ramIdeal_spec,
  ramIdeal_mem, eq_ramIdeal_of_liesOver, smul_ramIdeal, span_omega, mul_conj_prime, mul_conj_ideal,
  absNorm_smul.
- Fixes: `rw [hc]` with hc : n = p*c breaks motive (O depends on n) → cast equation (n:O) = p*c;
  `rcases ... with rfl` on τ = σ eliminated σ → use h and rw; span_omega statement's anonymous
  constructor ≠ omegaO syntactically → `change`.
- #print axioms: propext, Classical.choice, Quot.sound only.
