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
