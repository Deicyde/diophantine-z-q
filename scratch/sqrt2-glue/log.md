# sqrt2-glue results log

Target: `SqrtTwoNotInHHprime` (verbatim from scratch/tyz-318/Lemma318.lean): for squarefree `n ≡ 5 (mod 8)`,
`∀ s ∈ HHprime n, s ^ 2 ≠ 2`. tyz-318 proved `SigmaLift → SqrtTwoNotInHHprime` (copied here).

## Setup
- 2026-11-14 00:12: merged origin/wip/tyz-318; copied tyz-318's .lake/build (reflink); `lake build` of
  RingClassTwo, RingClassBridge, Tau Ceti TorsionReduction OK (6 changed Tau Ceti modules rebuilt).
- [VERIFIED, compiled] scratch/tyz-318/Lemma318.lean compiles in this worktree (23 s), axioms standard.

## Plan (Route A, factorization form; no Chebotarev over L_n(i))
SigmaLift ⇐ FrobNormLaw (Frobenius over F = L_n(i) at a prime P acts on H_{d₀,4} as Art([N_{F/K}P]))
          + NormSigma (an α ∈ 𝓞_F, coprime to 2, with [N_{F/K_{d₀}}(α)] = σ_{d₀} in Pic(ℤ+4𝓞_K) for all d₀).
Product of Frobenius lifts over the prime factorization of α𝓞_F.

## Step 1: reduction (compiled)
- [VERIFIED, compiled 00:35] scratch/sqrt2-glue/Sqrt2Glue.lean §0–§4: verbatim copies `SqrtTwoNotInHHprime`, `SigmaLift`,
  tyz-318's `sqrtTwoNotInHHprime_of_sigmaLift`; defs `kEmb`, `iotaK`, `relNormK` (Mathlib `Ideal.relNorm` for
  K_d → F via embed d), `classOf` (Pic class; `sigmaClass d = classOf (span {3+2√−d})` by rfl);
  Props `FrobNormLaw` (GLUE: Frobenius over F at P ∤ 2 acts on H̄_{d,4} as artin4 (classOf (N_{F/K_d} P))),
  `NormSigma` (GLUE: α ∈ 𝓞_{L_n(i)} coprime to 2 with classOf(N(α𝓞)) = σ_{d₀} ∀ d₀);
  `sigmaLift_of : FrobNormLaw → NormSigma → SigmaLift` (induction over normalizedFactors (α𝓞_F)),
  `sqrtTwoNotInHHprime_of`. Helpers: odd absNorm ⟺ coprime to 2 (Cauchy), relNorm preserves it,
  `mem_primeTo_of_isCoprime_two`, `classOf_mul`, `kEmb_mem_Lni`, `finiteDimensional_Lni`.
- [VERIFIED, compiled 00:30] §5 `eq_pow_of_congr`: in a finite L/K of number fields, at an unramified prime Q,
  an automorphism acting as x ↦ x^{(N𝔭)^f} mod Q equals φ^f for an arithmetic Frobenius φ (reduced to Tau Ceti
  `isArithFrobAt_eq_of_isUnramifiedAt` via ρ = τ⁻¹φ^f ≡ 1, φρ Frobenius).
- [VERIFIED, compiled 00:38] §6 `psi4`/`tauQ4`/`tau4` (transport H_{d,4} ≅ H̄_{d,4}) and **`frob_on_H4`**: h ∈ Gal(ℚ̄/F)
  acting as x ↦ x^{N P} mod 𝔔 on 𝓞_M (F ⊂ M ⊃ H̄_{d,4}) acts on H̄_{d,4} as artin4(classOf(N_{F/K_d} P)).
  Uses Mathlib `relNorm_eq_pow_of_isMaximal`, `cardQuot_pow_inertiaDeg`, Tau Ceti `isArithFrobAt_ringClassArtinEquiv_picClass`,
  `isUnramifiedAt_ringClassField`.
- Pitfall [VERIFIED]: `artin4 d c = ringClassArtinEquiv (O4 d) c := rfl` hits max recursion (instance paths);
  `artin4 d = ringClassArtinEquiv (O4 d) := rfl` is fine — rewrite with it.
- [VERIFIED, compiled 00:42] §7 **`frobNormLaw : FrobNormLaw`** (no hypotheses): M = F ⊔ ⨆_{d∈D} H̄_{d,4}, Mathlib Frobenius
  `IsArithFrobAt.exists_of_isInvariant` over 𝓞_F in Gal(M/F) at a prime 𝔔 over P, lifted by `liftNormal`, then
  `frob_on_H4`. **`sqrtTwoNotInHHprime_of_normSigma : NormSigma → SqrtTwoNotInHHprime`**. Axioms standard.
- [VERIFIED, compiled 00:47] §8 `classOf_span_congr` (class of 1 + 2ε√−d + 4γ is σ_{1+2ϖ}), `NormCongr` (GLUE Prop),
  `normSigma_of : NormCongr → NormSigma`.
- [VERIFIED, compiled ~00:55] §9–§11 arithmetic (`pstar`, `prod_pstar_primeFactors`, `not_sq_of_mul`), `trace_eq_zero_of_sq`
  (Tr x = 0 if x² ∈ K, x ∉ K), `finrank_adjoin_sq_le` ([ℚ(T):ℚ] ≤ 2^#T), `prod_one_add_two`, `norm_one_add_two_mul`
  (N(1+2β) = 1 + 2Tr β + 4γ, γ integral; via embeddings into an algebraic closure), `trace_sum_sq`.
- [VERIFIED, compiled ~01:00] §12 `sQ`, `xS`, `betaQ` (= i∏(1+√p*)/2), integrality, `kEmb_ne_xS` (x_S ∉ K_{d₀} unless
  S = primes of d₀; rational-square arguments), `finrank_Lni_le` ([L_n(i):ℚ] ≤ 2^{ω(n)+1}), **`normCongr_at`**
  (Tr β = (N/2^r)ε√−d₀ with N = [L_n(i):K_{d₀}] ≤ 2^r; integrality of the trace forces N = 2^r; then the norm congruence).
- [VERIFIED, compiled ~01:05] §13 **`normCongr : NormCongr`, `normSigma`, `sigmaLift : SigmaLift`,
  `sqrtTwoNotInHHprime : SqrtTwoNotInHHprime`** — no hypotheses; `#print axioms` = [propext, Classical.choice, Quot.sound];
  no `sorry` in the file.
