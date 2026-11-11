# redei-fp report: steps 1 and 2 of docs/research/redei-plan.md §3.2

Status: **done**. Both modules have no `sorry`. `lake build ZInQKernel` passes.
`#print axioms` on the main results lists only propext, Classical.choice and Quot.sound.

Files (namespace `ZInQ.RouteK.Redei`):
- `ZInQKernel/RouteK/Redei/Field.lean` (300 lines; plan estimate 250)
- `ZInQKernel/RouteK/Redei/Primes.lean` (515 lines; plan estimate 500)
- `ZInQKernel/RouteK/Redei.lean`: root module, imports both. `ZInQKernel.lean` imports it.
  The sibling task redei-kernel should add `import ZInQKernel.RouteK.Redei.Kernel` to this root
  module. If both branches create the file, the merge conflict is trivial (two import lines).

`QNeg`, the `Fact`/`NumberField` instances and `gCl` are reused from
`Rank5b/Sec3/RedeiStatement.lean`; nothing is redefined.

## Proved: step 1 (Field.lean)
The probe statements keep their exact form, with `n` explicit:
- `card_gal`, `isIntegral_omega`, `isIntegral_theta` (n ≡ 3 mod 4), `algNorm_eq`,
  `norm_eq_mul_conj`, `norm_nonneg`.

Elements:
- `omegaO n : O` (abbrev for `⟨ω, isIntegral_omega n⟩`), `omegaO_sq : ω·ω = −n`.
- `thetaO n h3`, `two_mul_thetaO : 2θ = 1 + ω`, `theta_eq`.

The automorphism. All of these take `σ` with `hσ : σ ≠ 1`, as the plan does:
- `conj_omega : σ ω = −ω`, `conj_omegaO`, `conj_apply : σ x = star x`, `conj_unique`,
  `conj_conj`, `conj_mul_self`, `eq_one_or_eq_conj` (every τ is 1 or σ), `exists_conj_ne_one`.
- `algebraMap_smul` (simp, rfl): the coercion of `σ • x` for `x : O`.

Norms of integral elements:
- `algNorm_coe` (the norm is an integer), `normZ_nonneg`, `normZ_eq_mul_conj : (N x : O) = x · σ•x`.
- `finrank_int`, `normZ_intCast`, `normZ_natCast`, `normZ_omega : N ω = n`,
  `normZ_one_add_omega : N(1+ω) = 1+n`.

O ∩ ℚ = ℤ and the rational units:
- `exists_int_of_coe_eq_algebraMap` (O ∩ ℚ = ℤ), `intCast_injective`, `intCast_dvd_intCast_iff`.
- `isUnit_intCast_iff` (m = ±1), `rat_unit_eq` (the rational units of O are ±1).
- `natCast_dvd_natCast_iff`, `span_natCast_eq_span_natCast_iff : (a) = (b) ↔ a = b` (for ℕ). This
  is the form step 3, Hilbert 90, will use.

## Proved: step 2 (Primes.lean)
The plan's statements, in the probe's form:
- `prime_trichotomy n σ hσ hp P`, `dvd_of_ramified n hp P hram`.
- `ramSet n` (no `NeZero` argument), `ramIdeal n p`, `ramIdeal_spec n hn hsq hp`, `ramIdeal_mem n p`.
- `span_omega n hn hsq`, `mul_conj_ideal n σ hσ I`.

Extra lemmas for later steps:
- `ramified_of_dvd` (p ∣ n, n squarefree ⇒ every P over p has P² = pO).
- `ramified_two` (n ≡ 1 mod 4).
- `eq_ramIdeal_of_liesOver`: for p ∈ ramSet, 𝔭_p is the only prime over p.
- `smul_ramIdeal`: σ𝔭_p = 𝔭_p.
- `ramIdeal_isMaximal`, `ramIdeal_liesOver`, `ramIdeal_ne_bot`, `prime_of_mem_ramSet`,
  `mem_ramSet_of_mem_primeFactors`, `omegaO_mem_ramIdeal`.
- `mul_conj_prime`, and `absNorm_smul : N(σI) = N I` (corollary of `mul_conj_ideal`; the plan's §3.4
  lists this as a risk).
- `mem_span_of_mul_self_mem`: if p is split or inert, then x² ∈ pO ⇒ x ∈ pO.
- `exists_int_sub_mem_of_absNorm`: N P = p ⇒ ℤ → O/P is onto.
- `sub_conj_mem`: σP = P and N P = p ⇒ x − σx ∈ P.
- `conj_thetaO`: σθ = 1 − θ.

General ideal facts:
- `absNorm_span_natCast_eq` (N(mO) = m²), `natCast_mem_of_liesOver`, `span_le_of_liesOver`,
  `intCast_mem_iff_of_liesOver`.
- `liesOver_of_natCast_mem`, `exists_prime_liesOver` (every nonzero prime lies over some prime p,
  via Mathlib's `Nat.absNorm_under_prime`), `ne_bot_of_liesOver`.
- `smul_natCast_O`, `smul_intCast_O`, `smul_span_natCast`, `span_le_smul_of_liesOver`, `smul_ne_bot`,
  `smul_isMaximal`, `smul_eq_of_pow_le`.
- `eq_of_dvd_of_absNorm_eq` (I ∣ J with equal nonzero norms ⇒ I = J).

## The first leaf (§3.5): re-estimate
`prime_trichotomy` and `dvd_of_ramified` went through at the estimated size: about 60 and 50 lines,
plus about 100 lines of shared helpers. All of step 2 is 515 lines against an estimate of 500. Per
§3.5, the plan does not need re-costing. Steps 3–6 can build on this API.

A shortcut that kept this small. The trichotomy does not use ramification indices or
`map_algebraMap_eq_finsetProd_pow`. The proof:
1. pO ≤ P, so P ∣ pO, and N(pO) = p², so N P ∈ {p, p²}.
2. If N P = p², then P = pO.
3. If N P = p, write pO = P·M. Then N M = p, so M is prime (`isPrime_of_irreducible_absNorm`) and
   lies over p.
4. Galois transitivity (`Ideal.exists_smul_eq_of_isGaloisGroup`) gives M = τP with τ ∈ {1, σ}.

The residue-field argument works through `ZMod.castHom`, which is bijective because the cardinalities
match.

## Pitfalls (for steps 3–6)
- `ext` on `𝓞 (QNeg n)` descends into `re`/`im`. Use `apply RingOfIntegers.ext`.
- For automorphisms use `AlgEquiv.ext fun x => _`.
- `map_smul` on `σ : K ≃ₐ[ℚ] K` fails to find `MulActionHomClass`. Use `Algebra.smul_def` and
  `AlgEquiv.commutes`.
- `QuadraticAlgebra.re_one`, `im_one` are scoped simp lemmas: pass them explicitly.
- Never `rw`/`subst` an equation `n = p * c`: the type `𝓞 (QNeg n)` depends on `n`, and the motive
  breaks. Use the cast equation `(n : O) = p * c` (from `congrArg Nat.cast` and `simpa`).
- `rcases eq_one_or_eq_conj σ hσ τ with rfl | rfl` eliminates `σ` in the second branch. Use `h`
  and `rw`.
- The statement of `span_omega` has the anonymous constructor `⟨ω, isIntegral_omega n⟩`, which is not
  syntactically `omegaO n`. Start proofs with `change Ideal.span {omegaO n} = _`.

## Left / suggestions
- Nothing is left for steps 1–2.
- For step 3 (Ambiguous): use `mul_conj_ideal`, `span_natCast_eq_span_natCast_iff`, `normZ_nonneg`,
  `normZ_eq_mul_conj`, `eq_ramIdeal_of_liesOver` and `smul_ramIdeal`.
- For step 4 (Genus):
  - `sub_conj_mem` gives "σ acts trivially on O/𝔭_q" directly (σ𝔭_q = 𝔭_q by `smul_ramIdeal`,
    N𝔭_q = q by `ramIdeal_spec`).
  - So N(α) = α·σα ≡ α² (mod 𝔭_q) follows from `normZ_eq_mul_conj`.
- For step 5 (`exists_absNorm_eq_of_isSquare`): the "not inert" argument fits the pattern of
  `ramified_two` (`mem_span_of_mul_self_mem` plus norms).
- I did not touch `scripts/print_axioms.lean`: this task names no lines in it.
