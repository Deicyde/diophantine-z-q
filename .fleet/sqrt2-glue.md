# sqrt2-glue — fleet report (2026-11-14)

**Verdict: PROVED.** `SqrtTwoNotInHHprime` (√2 ∉ ℍ'_n for all squarefree n ≡ 5 mod 8), the glue Prop tyz-318
left under TYZ Lemma 3.18, is a Lean theorem with no hypotheses and no leaves:
`ZInQ.Contrib.TYZGenus.Sqrt2Glue.sqrtTwoNotInHHprime` (also `sigmaLift : SigmaLift`, tyz-318's stronger form).
Combined with tyz-318's file, `lemma318Literal_HHprime : Lemma318Literal HHprime` and
`package_lemma318Literal_HHprime : Package.Lemma318Literal HHprime` hold outright, so cm-bridge's `h318` is
discharged (`tyzThm35ReadingA_of_cmLeaves_ringClassD_no318`).

**What compiles** (`lake env lean`, 0 errors, no `sorry`/`axiom`, `#print axioms` = [propext, Classical.choice, Quot.sound]):
- `scratch/sqrt2-glue/Sqrt2Glue.lean` (1573 lines, ~40 s): verbatim copies of `SqrtTwoNotInHHprime`, `SigmaLift`
  (byte-identical to tyz-318), and the proof.
- `scratch/sqrt2-glue/Combined.lean` (~37 s): tyz-318's Lemma318.lean followed by Sqrt2Glue.lean, ending with the
  unconditional Lemma 3.18.

**Proof** (Route A of tyz-318 §3.2, factorization form; no Chebotarev, no class field of L_n(i)):
α = 1 + 2i∏_{q|n}(1+√q*)/2 ∈ 𝓞_{L_n(i)}; h = product of Frobenius elements over L_n(i) at the prime factors of α𝓞.
- `FrobNormLaw` PROVED (`frobNormLaw`): Frobenius over F at P ∤ 2 acts on H̄_{d,4} as Art(N_{F/K_d}P), from Tau Ceti's
  ring-class reciprocity at primes + unramifiedness and Mathlib relNorm/Frobenius API.
- `NormSigma`/`NormCongr` PROVED: N(1+2β) ≡ 1 + 2Tr β (mod 4), Tr_{F/K_{d₀}} β = ±√−d₀ ([F:K_{d₀}] = 2^{ω(n)} from an upper
  bound plus integrality of the trace), and the Pic class of 1 ± 2√−d₀ + 4γ is σ_{1+2ϖ}.

**What remains:** nothing for this glue. Integration: Sqrt2Glue.lean (or Combined.lean) can become a Contrib module.
Report: docs/research/sqrt2-glue.md; log: scratch/sqrt2-glue/log.md.
