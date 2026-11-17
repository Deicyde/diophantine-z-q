# mcheck-22p: manuscript check of `prop:fixed-prime-pattern` (tex L1267–1704) and the L954 step

**Verdict: no error found.** The proof of the fixed twenty-two-prime pattern is correct, step by step, as far as
reading and computation can tell. The citations of Green–Tao, Green–Tao and Green–Tao–Ziegler could not be checked
against the papers (no network). Two steps are compressed in the text, and I filled them in (marked *gap filled*).
The non-congruence conditions `gcd(d₁,d₂) = 4` and `p ∤ d₁d₂` are secured correctly: by congruences for the
2-part and for odd primes `ℓ ≤ L`, and by a Selberg-sieve upper bound for the odd primes `ℓ > L`, where congruences
cannot work. A numerical counterexample below shows that the sieve step is genuinely needed. The tail step at tex L954,
`h(u) ≤ h(j) + log(2·4000⁶) < h(j) + 74`, is correct and is proved in Lean (`scratch/mcheck-22p/L954.lean`).

Line numbers are those of `diophantine_zq.tex` at the base commit 4a063a7f2. Marks: **VERIFIED** (read, computed or
compiled), **STANDARD** (published, with a reference), **UNVERIFIED** (a locator recalled from memory; no network).
All files are under `scratch/mcheck-22p/`. The Lean files import Mathlib only and compile with
`lake env lean`. Every script was run with `python3` (no sympy on this host; helpers in `nt.py`) and its output is
committed next to it as `<name>.out`.

## Manuscript check

| # | tex lines | step | verdict | reason | evidence |
|---|---|---|---|---|---|
| 1 | 1267–1297 | statement (with 𝓗 from L238–239) | OK | stated as a Prop; compiles; agrees with the kernel's `ZInQ.FixedPrimePattern` (read) | `Statement.lean` |
| 2 | 1299–1313 | coefficient vectors; each form has a coefficient ±1; every pair independent over ℚ and over 𝔽_q for q > 324, for every A | OK | every pair has an A-free nonzero 2×2 minor of size ≤ 61 | `Finite.lean` (`unit_coeff`, `pairwise_minor`, `contact_diffs`, by `decide`) |
| 3 | 1314–1319 | box Ω avoiding the zero planes; signs ε_ν | OK | the planes pass through 0; a small box away from them works for every A | reading |
| 4 | 1320–1329 | residue mod q⁵ avoiding F_ν ≡ 0, lifted mod q⁸; valuations e_{ν,q} ≤ 4; d_ν | OK | proportion ≤ 22/q⁵ ≤ 22/32; mod q⁸ fixes F/q^e mod q^{8−e} ⊇ mod 8 at q = 2 | `Finite.lean` (`ineqs`), `local_densities.out` (c) |
| 5 | 1329–1342 | residues c₂ = 1 (8), c₇ = 3 (7), c_q = 1; pick distinct h_ν ∈ 𝓗 in the right class mod W | OK | the class is a unit class mod W = 8·∏_{odd q≤324} q; Dirichlet gives 22 primes in each class; ≤ 22 demands per class | `Finite.lean` (`class_infinite`, `prime_coprime_W`) |
| 6 | 1343–1355 | at h = h_ν: point on F_ν = 0 avoiding 42 lines; lift mod h² with Ψ_ν ≢ 0, −1 | OK | restrictions are nonconstant (row 2); 42h < h²; a ±1 coefficient makes the lift surjective | `Finite.lean` (`ineqs`), reading |
| 7 | 1356–1368 | CRT residue r₀ mod W₀; Ψ_ν integral, ≠ 0 at p ∣ W₀, ≠ −1 at odd p ∣ W₀; coefficients divisible by every p ∣ W₀ | OK | v_q(F_ν) = e ≤ 4 < 8 and v_h(F_ν) = 1 are fixed on the progression; distinct h_ν make k_μ a unit at h_ν | reading |
| 8 | 1369–1380 | Q_*, constants α_A < β_A with Ψ_ν ≍ X on XΩ | OK | homogeneity, and the closure of Ω avoids the planes | reading |
| 9 | 1382–1404 | 44 planes at q ≤ L, q ∤ W₀; density ≥ c_A (log L)^{−44} | OK | every q ≤ 324 divides W₀, so q > 324 > 44; Mertens | `Finite.lean` (`ineqs`), reading |
| 10 | 1405–1419 | Green–Tao Main Theorem with GI(20) and MN(20); singleton classes give complexity ≤ 20 | OK (locators UNVERIFIED) | 22 forms with pairwise non-proportional linear parts: for each form, 21 singleton classes = s+1 with s = 20; coefficients and moduli fixed before X → ∞; values in [1, βX] | `Finite.lean` (`pairwise_minor`), reading; see Known issues 1–2 |
| 11 | 1420–1436 | local factors: (1−1/q)^{−22} at q ∣ W_L; 1 − 22/q ≤ P ≤ 1 − 22/q + 231/q²; log β_q ≥ −484/q²; uniform lower bound for the singular product | gap filled | the text gives −484/q² without derivation. Series: q²·(log(1−22/q) − 22 log(1−1/q)) = −Σ_{k≥2}(22^k−22)/(k q^{k−2}) ≥ −(231 + (22³/3q)/(1−22/q)) ≥ −242.72 for q ≥ 325 | `local_densities.out` (a), (d): exact counts at q ∈ {331, 337}, six values of A each |
| 12 | 1437–1453 | errors < half the main terms for finitely many r; weighted → unweighted; proper prime powers O(X^{5/2}(log X)^{23}); eq. (prime-lower) with a_A independent of L | OK | c_A, the singular lower bound and vol Ω do not depend on L | reading |
| 13 | 1455–1503 | Selberg upper sieve: A_d = N²g(d) + R_d with \|R_d\| ≪ Nd + d²; the weights; the quadratic form = 1/G(Z); S ≪ N²/G + NZ⁶ + Z⁸ | OK | standard. The bound \|λ_d\| ≤ d is correct but weak (in fact \|λ_d\| ≤ 1) | reading |
| 14 | 1504–1533 | truncated denominator G(Z) ≥ ½ H(Z^{1/100}) | OK | E log d = Σ g(q) log q ≤ 0.42 log Z; Markov | reading |
| 15 | 1534–1553 | G(Z) ≫ log Z (q ≡ 1 mod 4, one prime omitted); G(Z) ≫ (log Z)^{21} | OK | Mertens in progressions; g(q) ≥ 21/q − 210/q² | reading |
| 16 | 1554–1562 | p ≡ 1 (8), p ≡ 3 (7) ⇒ p splits, (7/p) = −1; N(d) = 7, so the reductions of d lie in opposite square classes; opposite twists of y² = x³ − x; good reduction | OK | | `Finite.lean` (`norm_d`, `seven_nonsq_of_three_mod7`, `two_sq_of_one_mod8`); `orders_small.out` |
| 17 | 1563–1587 | ι commutes with Frobenius; centralizer argument ⇒ Frobenius = a + bi ∈ ℤ[i]; d₁ = p+1−2a, d₂ = p+1+2a | OK (one locator doubtful) | the argument is correct. The Silverman locator for "Frobenius integral over ℤ" is doubtful (Known issue 3) | `orders_small.out` (60 primes), `orders_large.out` (33 primes of ~450–910 bits) |
| 18 | 1588–1594 | 2-part of gcd(d₁,d₂) is exactly 4; 0 < d_i < 2p, 4 ∣ d_i ⇒ p ∤ d₁d₂ | OK | full rational 2-torsion; d₁+d₂ = 2(p+1) ≡ 4 (mod 16); Hasse | `orders_small.out`, `orders_large.out` (`two_part_4`, `p_ndiv`, `hasse`) |
| 19 | 1595–1599 | odd ℓ ∣ gcd ⇒ ℓ ∣ a, ℓ ∣ p+1, b² ≡ −1 (ℓ); "the progression conditions already rule out every odd ℓ ≤ L" | gap filled | the text does not list the cases: (i) odd q ≤ 324: p ≡ c_q ∈ {1, 3 mod 7}, never −1; (ii) q = h_μ: Ψ_μ ≢ −1 by row 6, and Ψ_ν ≢ −1 (ν ≠ μ) by the excluded plane ε_νF_ν = −k_ν mod h_μ; (iii) other q ≤ L: the 44 planes of row 9 | reading; `orders_small.out` confirms gcd(d₁,d₂) = 4·oddpart(gcd(a, p+1)) |
| 20 | 1600–1643 | bad prime values ≪ X/(L log X) + X^{7/8} + √X log X, uniformly in L | OK | sieve on (U,V) with ρ(q) = 2q−1 (q ≡ 1 mod 4); absorption exponents correct; for ℓ > X^{1/8}, a ≠ 0 removes the additive constant | reading |
| 21 | 1644–1681 | fibre F_ν = c: 21 distinct zero lines, union in [21q − 210, 21q]; ≪ X²/(log X)^{21}, uniform in p | OK | the constant comparison μc = 0 argument is right | `local_densities.out` (b) (q = 331, four fibres) |
| 22 | 1682–1704 | order of choices: L first, then X; a pattern survives; v ≠ 0 | OK | b_A and a_A do not depend on L; (log L)^{44}/L → 0 | reading |
| 23 | 949–954 | J(u) = j = a/b ⇒ h(u) ≤ h(j) + log(2·4000⁶) < h(j) + 74 | OK | the numerator divides −a·3600⁶ (F(0) = 0); the denominator divides the top nonzero coefficient; ℓ¹ norm 3.571·10²¹ ≤ 2·4000⁶ = 8.192·10²¹; log(2·4000⁶) = 50.46 | `L954.lean` (`height_bound`, `log_height_bound`, `log_const_lt`; standard axioms only), `l954_polys.out` |

### Step 2 in detail: how the proof secures gcd(d₁, d₂) = 4 and p ∤ d₁d₂ (VERIFIED)

1. **Congruence part (tex L1330–1333, L1554–1594).** Every counted prime value satisfies p ≡ 1 (mod 8) and
   p ≡ 3 (mod 7). Then the reductions δ₁, δ₂ of d = 75 − 53√2 satisfy δ₁δ₂ = 7, which is a nonsquare mod p, so the
   two reduced curves are quadratic twists of each other by a nonsquare. Hence d₁ = p+1−2a and d₂ = p+1+2a with
   a² + b² = p (CM by ℤ[i]). Consequences:
   - the 2-part of the gcd is exactly 4;
   - p ∤ d₁d₂ (Hasse);
   - an odd ℓ divides gcd(d₁,d₂) iff ℓ ∣ gcd(a, p+1).

   Numerical check, `orders_small.py`: 30 primes p > 324 with p ≡ 1 (8), p ≡ 3 (7), counted directly. Every row
   satisfies d₁ + d₂ = 2(p+1), gcd = 4·oddpart(gcd(a, p+1)), and p ∤ d₁d₂. The contrast sample with (7/p) = +1 gives
   d₁ = d₂, so the condition p ≡ 3 (mod 7) is essential.
2. **Small odd ℓ by congruences (tex L1596–1597, rows 7, 9, 19).** The progression forces Ψ_ν ≢ −1 (mod ℓ), that is
   ℓ ∤ p+1, for every odd ℓ ≤ L. The text does not spell out this step; row 19 fills it in. For example, p = 1249 has
   gcd = 20 and p = 3769 has gcd = 52. Such primes are excluded by c₅ = c₁₃ = 1.
3. **Large ℓ by a sieve (tex L1600–1643).** This is not, and cannot be, a congruence or Chebotarev argument.
   `orders_large.py` part B builds three primes (~910 bits) that satisfy **every** residue prescription of
   tex L1330–1333, yet have 337 ∣ gcd(a, p+1), so gcd(d₁,d₂) = 1348 = 4·337. The proof handles such ℓ > L by
   counting representations p = a² + b² with ℓ ∣ a and b² ≡ −1 (mod ℓ). This shows that bad primes make up a
   proportion O(1/L) of the prime values. L is then chosen so large that this beats the (log L)^{−44} loss of the
   lower bound. I checked the exponents and the uniformity in L (rows 20–22).

   Part A: 30 random primes (~450 bits) in the full residue pattern. Their orders were computed from the Cornacchia
   candidates p+1 ± 2a, p+1 ± 2b, confirmed by [N]P = O on four random points, with exactly one surviving candidate
   each time. All 30 have gcd = 4 and pass every structural check.

### Hypotheses of the cited Green–Tao and Green–Tao–Ziegler theorems (row 10)

- **Finite complexity.** After the substitution T = r + W_L n, the 22 forms n ↦ ε_νF_ν(r+W_Ln)/k_ν have linear parts
  that are nonzero rational multiples of the homogeneous F_ν. These are pairwise non-proportional (`pairwise_minor`),
  so no two forms are affinely dependent. The complexity is ≤ 20, using singleton classes in GT Definition 1.5.
  VERIFIED (computation) for the forms; STANDARD for the definition (Green–Tao, Ann. of Math. 171 (2010), Def. 1.5,
  UNVERIFIED locator).
- **Non-degeneracy / local admissibility.** No prime q makes every pattern vanish:
  - for q ∣ W_L the forms are constant and nonzero mod q;
  - for q > L, the 22 planes miss a proportion ≥ 1 − 22/q > 0.

  The local factors are positive and their product is bounded below uniformly in L and r (row 11). VERIFIED.
- **Size conditions.** Coefficients, constants and moduli are fixed before X → ∞. The convex body K = (XΩ − r)/W_L
  lies in [−N, N]³ with N ≍ X, and the values lie in [1, βX]. VERIFIED (reading).
- **Inputs.** GI(20) is Green–Tao–Ziegler, Ann. of Math. 176 (2012), Theorem 1.3. MN(20) is Green–Tao, Ann. of
  Math. 175 (2012), Theorem 1.1. Both are STANDARD, with UNVERIFIED locators. The manuscript cites GTZ as
  "arXiv v5, 2026 corrected version" with an erratum (Known issue 2).

## Known issues

1. **tex L1406, locator.** "Main Theorem, p. 1763" of Green–Tao, *Linear equations in primes*: the page number is
   UNVERIFIED. The theorem exists. It is conditional on GI(s) and MN(s), as the text says.
2. **tex L1408, L1416–1418, bibliography L11107–11110: the GTZ citation.** The manuscript relies on "arXiv:1009.3998v5,
   2026 corrected version" together with an author erratum ("Proposition 3.1 and modified deduction of
   Proposition 7.3"). I could not check offline whether this version or erratum exists, or whether it leaves Theorem 1.3
   as published (UNVERIFIED). Theorem 1.3 of the published version, Ann. of Math. 176 (2012) 1231–1372, gives GI(s)
   for every s (STANDARD, locator UNVERIFIED). Someone with network access should confirm that the erratum does not
   change the statement used here.
3. **tex L1577–1578, locator.** "[V.2.3.1(b), p. 142] silverman" is cited for "the Frobenius endomorphism is integral over ℤ".
   From memory (UNVERIFIED), Silverman's Theorem V.2.3.1 is the Weil-conjecture theorem for E/𝔽_q, and its part (b)
   is not about integrality. The fact itself is standard: φ² − tφ + p = 0 in End(E), by III.8.6 and the
   Cayley–Hamilton argument used in V.2. This is a locator problem, not a mathematical one.
4. **tex L1595–1599, compressed step.** "The progression conditions already rule out every odd ℓ ≤ L" requires the
   three-case check in row 19 (q ≤ 324, the catalogue primes h_μ, and the other q ≤ L). The text does not write it out,
   but every case follows from conditions the proof imposes. Gap filled.
5. **tex L1430–1431, compressed step.** log β_q ≥ −484/q² is stated without derivation. It holds with room to spare: the
   true constant is ≈ 242 for q ≥ 325 (row 11). Gap filled.
6. **tex L1484, remark.** |λ_d| ≤ d is correct but weak; the same two facts give |λ_d| ≤ 1. Harmless.
7. **tex L1671–1672, wording.** "The second denominator estimate in (prime-truncated-denominator)": that display is a single
   estimate. "Second" refers to the second *application* (L1544–1550), i.e. G(Z) ≫ (log Z)^{21}. Harmless.

## Deliverables and leaves

- `Statement.lean`: `MCheck22P.FixedPrimePattern`, compiles.
- `Finite.lean`: the finite facts, compiles.
- `L954.lean`: the L954 inequality, compiles with axioms propext, Classical.choice and Quot.sound.
- Scripts and their outputs:
  - `orders_small.py`, `orders_large.py` (step 2);
  - `local_densities.py` (step 3);
  - `l954_polys.py` (step 4).
- `log.md`: the results log.

This was a check task, so there was no fold, no change to `ZInQKernel/`, and no new leaf. If the prop were ever
formalized along the manuscript's route, the literature leaves would be:
- the Green–Tao Main Theorem (Ann. 171), conditional form;
- MN(s) (Ann. 175, Thm 1.1);
- GI(s) (GTZ, Ann. 176, Thm 1.3).

All three are printed theorems over genuine definitions (von Mangoldt sums over convex bodies), so their Lean
statements could be printed forms. Everything else in the proof (the Selberg sieve, Mertens, CM by ℤ[i], Hasse) is
textbook glue. The kernel avoids all of this through route AP.
