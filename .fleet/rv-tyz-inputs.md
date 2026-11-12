# rv-tyz-inputs: adversarial review of the TYZ inputs of Proposition N

**Verdict: Proposition N's dependence on Tian–Yuan–Zhang is sound, with one residual doubt of exposition.**
Every input I1–I7 holds. Their printed proofs are complete and correct as far as checked, except for one
computation that TYZ do not print (T1 below). Neither the false `d₁ = 1` convention of Theorem 1.2 nor the
sketched Proposition 3.4 enters the proof of any input. Full note: `docs/research/rv-tyz-inputs.md`. Scripts:
`scratch/rv-tyz-inputs/`.

**Per input.** I1 (recursion, `ε`-classes): holds as printed; Lemma 3.9 re-derived. I2 (Lemma 2.8,
Prop 2.3): holds once quoted modulo 2 (missing `w_K`; also new: Theorem 2.1 is false for ordered pairs at
`n ≡ 3`, which does not affect Lemma 2.8). I3 (Thm 3.5 first assertion): holds given Theorem 3.3, whose
exact constant is "computations similar to Theorem 2.1" and is not printed (**T1**). Proposition N needs only
that the constant is uniform in `χ` up to a 2-adic unit: factors depending on `d₀` alone drop out (VERIFIED);
the uniformity itself is structural but SPECULATIVE until written out. I4 (Lemmas 3.16, 3.18), I6
(Prop 3.2(1)): hold, proofs re-derived. I5 (Lemma 3.21(1), (4)): holds; its "checked easily by Theorem 3.6"
step was re-derived. I7: STANDARD.

**Computations (all VERIFIED, PARI/sympy, at most 30 inputs per check):**
- I2: on 30 values of `m ≡ 1, 3 (mod 8)` (`ω ≤ 6`), every `𝓛(d)` from `L(E_d, 1)` (about 200 values) is an
  integer, and Lemma 2.8 mod 2 and Lemma N1 hold on all 30.
- I4/I6: `A(ℍ′_n)_tors = ℤ/4 × ℤ/2` and `√2 ∉ ℍ′_n` on 8 fields built as TYZ define them (degree up to 64,
  including two cases with two divisors `d₀ ≡ 5`). Control: `(ℤ/4)²` over `H_{d,4}`.
- I5: every 2-adic matrix decomposition, cusp class and normaliser claim of Props 3.7–3.9 verified exactly
  (one sign misprint, harmless). TYZ's external cusp dictionary for `X₀(32)` (from Tian 2014) was verified
  with exact modular symbols.
- I7 consequence: 30 small `n` with `T_5a` or `T_5b` odd: all have analytic rank 1. On the 25 with a
  generator, `𝓛(n)` is an integer and `v₂(𝓛) ≤ ρ`. Plus 11 pure-5b `n` with `ω = 6, 7`: all have analytic rank 1.

**Misprints found (all harmless):** the sign in `w₀ϖε` (Prop 3.8); `(4P)^c = 4P` for `−4P` (Lemma 3.9,
`d₁ = 1`); `w_K` (Lemma 2.8); "ring class field" for ray class field (Lemma 3.16).

**Earlier reviews.** rv-nt-tyz checked the quotations but not the proofs (its B4). rv-prop-n took I1, I3 and
I5 as quoted. This is the first re-derivation of the input proofs.

**Next:** write out the constant of Theorem 3.3 from TYZ's Theorem A.9, or read the journal version
(Asian J. Math. 21 (2017), not read here) to remove T1.
