# pn-design results log

## Step 1 (inputs I1–I7 read in Period7.tex)

- Read: L318–345 (def. of 𝓛, root number), L363 (g), L499 (§2 hyp. n ≡ 1,2,3 sqfree), L580–586
  (Prop 2.3), L1062–1082 (Lemma 2.8, 𝓛(1) = 1), L1167 (§3 hyp.), L1253–1374 (Prop 3.2, ℙ(n), Thm 3.3,
  Z(n), ℍ'_n, recursion, Thm 3.5), L1384–1402 (τ), L2170–2232 (Lemmas 3.16, 3.18), L2480–2590
  (β₁, Lemma 3.21, proof of 3.5(2)).
- `n2_check.py` (seed 1): unwound recursion coefficients c_n(e) for n ≡ 5, with ARBITRARY integer 𝓛
  (no Lemma 2.8) and ε = ±1 off (5,3), ±i at (5,3): 190 trials (1–7 primes), 0 mismatches with
  c_n(e) ≡ 𝓛(n/e) (mod 2ℤ[i]). Same with ε at (5,3) a random unit (mixed classes): 154 mismatches.
  ⇒ N2 in the 𝓛-form needs no I2/N1; it needs the ε-classes of Thm 3.3 including uniformity at (5,3).
