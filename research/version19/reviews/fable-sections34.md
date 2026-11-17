# Fable review: V19 draft on the 250, effective-sum and reflected-height sections as typeset

Reviewed 16 November 2026.

File: `C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\version19-250-draft-20261116\quartic_v19.tex`, SHA-256 `388eb3e8…`.
Scope: Section `v19:effective-sums` (lines 280–350), Section `v19:reflected-height` (lines 352–405), the factor table `v19:contact-factors` (lines 1061–1120), and how `v19:250-soundness` consumes the two results.
Method: every line read and each step re-derived by hand. Finite claims recomputed with my own scripts (`chk34.py`, `chk34b.py` in the session scratch folder; integers and fractions only). Compared with Jose's `effective_elliptic_sums_20261108_v10.tex` and `quartic262_20261110_v21.tex` lines 84–158 at cd474ee, and with released V18 (lines 9826–9952, 20806–20816, 21150–21201). No code of Astra, Jose or Carbon was run.

## Verdict

No error found. Four small exposition gaps, each closed below by a short argument; none changes a statement or a constant.

## Errors

None.

## What was checked and holds

### Lemma `v19:sum-height` and its application

- Height weight `f_v log p / 2` for a finite place with value group Z: correct for [K:Q] = 2, including the ramified place above 2. It agrees with V18's convention: with it, h(x(P_*)) = log 41 for x(P_*) = (57 − 28√2)/8.
- Parameter t = −x/y gives t²x² − x − Dt² = 0, so x = (1 + √(1+4Dt⁴))/(2t²) = t⁻² + Dt² − D²t⁶ + …; the tail has integer (Catalan) coefficients times powers of D.
- dx/(2y) = dt/√(1+4Dt⁴), re-derived by differentiation; hence the printed logarithm series.
- Above 2 the denominators 4k+1 are units. At odd p, v_p(4k+1) ≤ log₃(4k+1) ≤ 4k−2 for k ≥ 1, so each term with k ≥ 1 has valuation at least (4k+1)a − (4k−2) ≥ 3a for integer a ≥ 1. Hence v(ℓ(t) − t) ≥ 3a, v(ℓ(t)) = a, and x(t) − ℓ(t)⁻² is integral.
- L_v is independent of m and nonzero; ℓ([n]P) = nL_v whenever [n]P is formal.
- Local loss: with J the formal indices at v, Z = (n_i L_v)⁻² C_J / ∏_{j∈J∖i} n_j² + integral, so the local loss against x_i is at most v(C_J). Where x_i is integral there is nothing to lose.
- Summation: Σ_v (f_v log p / 2) v(C_J) = log C_J for a positive integer C_J. With C_J ≤ kB^{2(k−1)} and C(3, k−1) subsets of size k: log B coefficient 3·2 + 3·4 + 1·6 = 24; constant 3 log 2 + 3 log 3 + log 4 = log 864.
- Real places: positivity gives σ(Z) ≥ σ(x_i) > 0, no loss.
- Application: D = 11 − 6√2 ∈ Z[√2]; P_* has infinite order; x of a nonzero double is (x₀² + D)²/(4y₀²), positive at both real embeddings since σ(D) > 0. V18 `eq:o8-indexheight` reads h(x(nP_*)) ≥ n² − 6 for n ≠ 0, on the normalized curve of `sec:degree8-original`, as the draft says.
- Constant 80: max of 24 log B − B²/2 is 12 log 24 − 12 ≈ 26.14 < 27; the total subtracted is at most 2·27 + 12 + 2 log 864 < 79.6 < 80.
- The typeset lemma is Jose's Theorem 1 at r = 4 with the same proof; the corollary is his Corollary 4.

### Section `v19:reflected-height`

- V18 H₀ defines M_S(a) for every finite rational a = u/v in lowest terms, v > 0, a ∉ {0, 1, 2401, −343/32}, counting primes outside S = {2,3,5,7,11,13,17,37,41,2399} with positive odd valuation on v, u, u−v, u−2401v, 32u+343v. V18 states the bound for every such a. (H4.2): h(a) < C₂ M² E(M) [1 + log M / log B_S], C₂ < 2^{7557/32}.
- M_S ≤ B_* M₅: a prime counted by M_S is either at most 76176, so divides B_*, or is counted by M₅.
- B_* < 2^{109445}: recomputed. There are 7499 primes up to 76176, the largest is 76163, and their product has bit length 109445. This matches V18 line 20814.
- B_S = 1857890364330, log B_S ≈ 28.25 > 28. 7557/32 ≈ 236.2 < 237.
- E(m) ≤ Σ_{j≤m} 1/j ≤ 1 + log m. 1 + log B_* ≈ 75862 < 2¹⁸. 1 + log B_* / log B_S < 2711 < 2¹³.
- Exponent 237 + 2·109445 + 18 + 13 = 219158 < 221231.
- Factorization claim: recomputed for all ten contacts. The prime support of the denominators, the 45 differences and the ten numbers 1 − θ is exactly {2,3,5,7,11,13,37,41,47,67,109,179,257,439,2099,2399,2029147}. Only 2029147 exceeds 76176; it is prime; it occurs only in θ₄ − θ₁₀ and θ₅ − θ₉.
- Typeset table `v19:contact-factors`: all 55 rows parsed and compared with my values (value, numerator factors, denominator factors, every listed factor prime). All correct.
- Reflection: u = 2 + 1/t sends ∞, 0, 1, 2401, −343/32 to t = 0, −1/2, −1, 1/2399, −32/407. t = 1/(u−2) has row sums 1 and 3; t = (2u′−5)/(u′−2) has row sums 7 and 3. So h(t) ≤ h(u) + log 3 and h(t) ≤ h(u′) + log 7.
- Product step, square root, and the arithmetic–geometric mean step are correct.
- E₂ = 2029147 < 2²¹; 1 + log E₂ ≈ 15.52 < 22; C E₂² < 2^{221273}; log 7 < 2 ≤ 2^{221273}·22², so doubling absorbs it. K₂ = 2^{221274}.

### Consumption in `v19:250-soundness` and `v19:250-local`

- Soundness uses B² ≤ 2h(𝒮) + 80 with 𝒮 the sum of the abscissas of Q_i = [n_i]P, four nonzero integer labels, B their maximum, P = P_*: exactly the lemma's setting.
- Soundness uses h(t_j) ≤ K₂ M_j (22 + ½ log M_j)² with M_j = M(t_j). `v19:250-local` defines M(u) for u ∉ Θ₂ with the same Σ (primes ≤ 76176 and 2029147) and the same criterion as M₂°(t) here. The construction section proves t_j ∉ Θ₂.
- The local section's claim that at a prime outside Σ exactly one contact has positive valuation and u − 1 is a unit follows from the factor table, which includes the numbers 1 − θ.

## Gaps (exposition only), with the argument that closes each

1. **"Each original radical is at most E₂M_±" is asserted, not derived** (lines 389–391). Closure: write t = a/b in lowest terms. Then u = (2a+b)/a is in lowest terms, and its five forms are a, 2a+b, a+b, b−2399a, 407a+32b, the numerators of t − θ for θ ∈ Θ. For p > 76176 dividing one of them, p ∤ b (otherwise p | a), so v_p(form) = v_p(t − θ). So M₅(u) is M₊ times possibly E₂. The same holds for t′ = 2 − t = (2b−a)/b and the block 2 − Θ. Two sentences would do.
2. **Domain of the five-contact inequality not stated** (line 387). It needs 2 + 1/t and 2 + 1/(2−t) finite and outside {0, 1, 2401, −343/32}. That is exactly t ∉ Θ₂ (t = 0 and t = 2 are contacts). One clause.
3. **M₅(u) is not defined in this section**; it is introduced only as "the same five forms outside the cutoff 76176". A reader needs: u = r/s reduced, s > 0, primes p > 76176 with positive odd valuation on s, r, r−s, r−2401s, 32r+343s. Jose's paper has this sentence.
4. **The substitution M_S ≤ B_*M₅ into (H4.2)** silently uses monotonicity after replacing E(M_S) by 1 + log M_S, and the inequalities 1 + x + y ≤ (1+x)(1+y) and 1 + (x+y)/L ≤ (1 + x/L)(1 + y) for L ≥ 1. All hold; a half-line would make the exponent count checkable.

## Wording notes

- Lemma proof: "formal" is used for a point with v(x) < 0. Since t = −x/y also has positive valuation at points reducing to (0,0), say once that formal means v(x) < 0.
- "Where x_i is integral there is no positive local loss" could add "and otherwise [n_i]P is formal".
- Line 372: "it is prime by trial division" is fine; the table section could repeat it.
- The derived bound is strict (<); Jose's display has ≤. Harmless.

## Not checked

- V18's own proof of (H4.2) (sections H₀–H₄) and of `eq:o8-indexheight`; taken as released. I only confirmed their statements, domains and constants.
- That ℓ is a homomorphism on the whole formal group at the place above 2 beyond the standard theory.
- Anything outside these sections: the coordinate maps, the 222-row and 175-row tables, the 195 material.
- Astra's `check_interfaces.py` and other scripts.
