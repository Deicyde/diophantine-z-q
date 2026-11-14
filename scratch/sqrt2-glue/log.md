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
