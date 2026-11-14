# tyz-318 results log

Target: `Lemma318Literal HHprime` (verbatim copy of `Package.Lemma318Literal`, from scratch/cm-bridge/Bridge.lean §0),
TYZ Lemma `torsion2` (Lemma 3.18): torsion of `A(ℍ'_n)` is killed by `2(1+[i])`.

## Route (no ramification at odd primes, no Lubin–Tate)
1. Odd torsion: reduction at a prime `p ≡ 3 (mod 8)`, `p ≡ 1 (mod q)` for all odd `q ∣ nℓ` (Dirichlet, in Mathlib);
   such `p` is inert in every `K_{d₀}` (`d₀ ∣ n`, `d₀ ≡ 5 (8)`), so (GLUE) every prime of `ℍ'_n` over `p` has
   residue field inside `F_{p²}`; `A` is supersingular at `p` and (LEAF) `Ã(F_{p²})` is killed by `p+1`;
   Tau Ceti `eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero` (Silverman VII.3.1(b), proved, vendored) gives
   `A(ℍ'_n)[ℓ] ↪ Ã(k)`, and `ℓ ∤ p+1`.
2. 2-primary torsion: a 2-power torsion point outside `A[(1+i)³]` has a multiple `S ∈ A(K)` with `4S = 0`,
   `2(1+i)S ≠ 0`; then `x(S)` satisfies `x² − 2ex + 4 = 0`, `e = x(2S)`, `e² = −4`, so `(i(x−e)/2)² = 2` and
   `√2 ∈ K`. (GLUE, TYZ's Step 3) `√2 ∉ ℍ'_n`.

## Findings
- [VERIFIED, computed, scratch/tyz-318/ss_check.py, pure Python] leaf sanity: for p ∈ {3,7,11,19,23,31,43,47},
  `y² = x³ + 4x` has `(p+1)²` points over `F_{p²}`, `p+1` over `F_p`, and every `F_{p²}`-point is killed by `p+1`.
