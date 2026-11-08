# Pole completeness by Route K: an audit of the deep inputs

This note audits the external theorems on which Route K would rest. Route K
(`docs/research/rs-pole.md` §4.1, checked in `docs/research/rv-route-k.md`) proves pole
completeness PC for a modified pole polynomial whose two curves are congruent number curves

```
C_d : y² = x³ − d²x = x(x − d)(x + d),
```

and replaces the manuscript's restricted converse RC (Theorem 5.3, line 1005; about 8,000 lines
in Sections 7–9 and Appendices E–G) by a published or preprinted 2-converse for the family
`C_d`. The candidates are

- Kriz, arXiv:2002.04767, Theorem 10.13 (with Theorems 1.1, 9.23 and 10.17(2)); and
- Tian–Yuan–Zhang, Asian J. Math. 21 (2017) 721–774, Theorem 1.2, in the determinant form of
  Smith, arXiv:1603.08479, Theorem 2.2, followed by Gross–Zagier.

Every claim carries one of three marks.

- **VERIFIED**: checked against the source text (the manuscript, the Lean files, or the arXiv
  LaTeX sources and PDFs of the cited papers), or by an exact computation. Scripts are in
  `scratch/pc-audit/`, outputs in `scratch/pc-audit/out_*.txt`.
- **STANDARD**: a well-known published theorem, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.

Notation follows `rv-route-k.md`. For an admissible input `B` and a signed divisor `m` of 2730,
`β = sqf(mB)` and `θ = sqf(m(m − B))`, where `sqf` is the signed squarefree part; `θ > 0`,
`θ ≡ 1 (mod 8)` and `gcd(θ, 2730) = 1` (VERIFIED, `rv-route-k.md` §4.2–4.4). The Kummer map of
`C_d` is `P ↦ (x, x − d) ∈ (ℚ*/ℚ*²)²` with the usual values at 2-torsion points; the *first
coordinate* of a class is the class of the abscissa. A curve `C_d` is *Selmer-minimal* if
`dim_{𝔽₂} Sel₂(C_d/ℚ) = 3`. For an odd integer `u > 0`, `χ₋₁(u) = 1` if `u ≡ 3 (mod 4)` and `0`
otherwise, and `χ₂(u) = 1` if `u ≡ ±3 (mod 8)` and `0` otherwise.

## Summary of verdicts

| Record | Input | Needed by | Verdict |
| --- | --- | --- | --- |
| RK1 | Kriz, Theorem 10.13 (rank-one 2-converse, CM by `ℤ[i]`) | K-Kriz | **usable with a stated extra hypothesis**: it is an unrefereed preprint (v5, 2022). It covers every converse curve of Route K without congruence conditions. The LMFDB small cases are never needed. One step of its proof cites an example curve that violates the proof's own hypothesis `f₀ ≥ 4`; the step is repaired by `C_5` (VERIFIED). |
| RK2 | Kriz, Theorem 9.23 (rank zero) | nothing | not needed |
| RK3 | Cassels–Tate pairing alternating (Cassels; Poonen–Stoll, A019) | K-Kriz only | usable as is |
| RK4 | Tian–Yuan–Zhang, Theorem 1.2 | K-TYZ | **usable with a stated extra hypothesis**: published and refereed, but it certifies only part of the Selmer-minimal curves, so the descent must also enforce its criterion. The arXiv text was read; the journal text was not available and must be compared. |
| RK5 | Smith, Theorem 2.2 (TYZ's sums as bordered determinants) | K-TYZ | **usable**: unrefereed, but an elementary 𝔽₂ identity. VERIFIED with 0 mismatches on all 12,159 squarefree `n < 20000` and 450 random `n` with 4–9 odd primes. Only two rows are needed in the recommended variant. |
| RK6 | TYZ's criterion is a linear condition on the Selmer class (this note) | K-TYZ | VERIFIED by computation (900 Selmer-minimal curves) and by a proved bordered-determinant lemma; a written proof of the rules is SPECULATIVE but routine |
| RK7 | Gross–Zagier forward theorem, only "analytic rank one ⟹ rank ≥ 1" (part of A020) | K-TYZ | usable as is; modularity of `C_d` is classical (CM), so BCDT is not needed, and Kolyvagin is not needed |
| RK8 | Complete 2-descent and Monsky's matrices for `C_d` | both | usable as is (STANDARD, elementary) |
| RK9 | Rank ≥ 1 plus Selmer-minimality gives a point with prescribed first coordinate | both | VERIFIED (counting argument; no pairing needed) |

**Recommendation.** Cite Tian–Yuan–Zhang (RK4) with Gross–Zagier (RK7) as the deep input, with
the descent strengthened by a purely 2-adic condition (§4.2, variant K-TYZ-β). Do not rely on
Kriz alone while it is unrefereed; record it as an alternative that needs no 2-adic refinement.
Details in §5.

## 1. The statement and every use

### 1.1 The hypothesis (VERIFIED)

Manuscript Theorem 5.2 (`hyp:PC`, lines 1001–1003): for rational `B` with square reduced
denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}`, the pole polynomial
`Q_pole` (lines 975–987) has a rational zero `Φ(B)`. Lean: `ZInQ.PoleCompleteness` in
`ZInQKernel/Hypotheses/Pole.lean`, stated for `ZInQ.PoleSoluble`, the solubility of
`ZInQ.polePoly`.

### 1.2 Uses (VERIFIED by `grep -rn "hPC" ZInQKernel`)

PC is applied in exactly two places. Every other occurrence (`completeness_core`,
`multiply_complete`, `multiplication_exact`, `value_relation_iff_of`, `Pstar_spec`, `assembly`,
and the four main theorems of `ZInQKernel/Main.lean`) only passes it on.

| Lean site | Manuscript | Input |
| --- | --- | --- |
| `ZInQ.Mult.slope_complete`, `Multiplication/Completeness/SlopeCompleteness.lean:187` | line 1751 | `B = slopeR ℓ a R₀ / Θ²` |
| `ZInQ.Assembly.test_complete`, `Assembly/Local/TestCompleteness.lean:104` | Lemma 11.2, line 6233 | `B = testR / poleTheta²` |

The soundness direction never uses PC; it uses the one-sided obstruction (Lemma 5.1, line 988),
proved in Lean (`ZInQ.Assembly.poleSoluble_no_negative_odd`, `ZInQ.Mult.pole_obstruction`).
Lemma 1.2 lists PC among the inputs (line 101).

### 1.3 What Route K changes

Route K replaces `x + 3ℓ` by `x + ℓ` in `T₁, T₂`, so the curves become `C_e` and `C_{eH}`.
Soundness transfers, with the factor 3 no longer needed at `p = 3` (`rv-route-k.md` §4.1,
VERIFIED there). The hypothesis would become `PoleCompleteness_C`, with the same quantifiers.
This audit concerns only the deep input of its proof.

## 2. The weakest form the proof needs

### 2.1 What PC needs per input (VERIFIED, from `rv-route-k.md` §2 and §4.2)

`Φ_C(B)` holds once, for one multiplier `m`, there is a squarefree `n` with `β | n` such that
each of `C_n` and `C_{nθ}` has a rational point whose abscissa lies in `βℚ*²`. If `θ = 1`,
2-torsion points give the witnesses; if `n = ±β`, the point `(β, 0)` serves on `C_n`. Each call
site needs one such `B` per instance.

### 2.2 What the deep input must supply

The descent (the gap of `rv-route-k.md` §4.4, still unproved) is meant to produce, for each
admissible `B`, a multiplier `m` and an `n` such that every curve `C_d`, `d ∈ {n, nθ}`, that does
not carry the torsion point is Selmer-minimal and has a Selmer class `σ_d` of first coordinate
`β`. From there the deep input must give, for **at most two curves per input**:

> **(R≥1)** `rank C_d(ℚ) ≥ 1`.

Nothing more is needed (VERIFIED, record RK9): rank ≥ 1 together with
`dim Sel₂ = 3 = 2 + rank` forces `C_d(ℚ)/2C_d(ℚ) = Sel₂(C_d)`, so `σ_d` is the image of a
rational point, which may be taken non-torsion, with abscissa in `βℚ*²`.

This is much weaker than either theorem as stated:

- **Rank exactly one, finiteness of Ш, and the analytic rank are never used.**
- **The curves are chosen, not given.** The descent selects them from an infinite family
  (64 multipliers and infinitely many auxiliary primes), so a converse is needed only on a set
  of curves that the construction may restrict further. The quantitative question is how
  restrictive a published criterion is on Selmer-minimal curves:
  - Kriz: no restriction (every Selmer-minimal `C_d` qualifies).
  - TYZ: of 900 random Selmer-minimal `C_d` (half with `|d| < 10⁶`, half products of 3–7
    primes below 1,224, 40% of them doubled), TYZ certifies 240 of 273 with `|d| ≡ 5`, 218 of
    365 with `|d| ≡ 6` and 244 of 262 with `|d| ≡ 7 (mod 8)` (`out_tyz_beta_rule.txt`).
    Smith's asymptotic densities, as the number of prime factors grows, are 3/4, 1/2 and 3/4
    (Theorem 1.4).
  - More precisely (RK6): whether TYZ applies to `C_d` depends only on `|d| mod 8` and on the
    2-adic and sign data of the class `σ_d`. Row 5b (for `|d| ≡ 5`) and row 6 (for `|d| ≡ 6`)
    depend only on the first coordinate `β`. Since `θ ≡ 1 (mod 8)`, both curves `C_n` and
    `C_{nθ}` then satisfy the same condition.
  - Cost of the restriction (VERIFIED, counting):
    - the `β`-rule of row 5b (`β` odd, `|β| ≡ 3 (mod 4)`) holds for 16 of the 64 multipliers;
    - the rule of row 6 holds for 32 of the 64. Each 2-adic class of `β` with each sign comes
      from exactly four multipliers, because `β ≡ mB` and the signed divisors of 2730 cover
      `{±1} × ℚ₂*/ℚ₂*²` evenly.
    - In addition `n' = n/β` must lie in one class modulo 4 or 8, a congruence on the auxiliary
      primes.
- **The `f₀ ≤ 3` cases do not occur** (RK1): the converse curves can be taken with odd part of
  `|d|` at least 11.

The net requirement on the deep input is therefore: *(R≥1) for Selmer-minimal `C_d` whose
non-torsion Selmer class satisfies a prescribed 2-adic condition.* TYZ plus Gross–Zagier gives
exactly this.

## 3. The manuscript's proof and the trust leaves of Route K

### 3.1 The manuscript (VERIFIED, lines 1019–1121; summarized from `rs-pole.md` §3)

PC is deduced from RC by a Rédei-matrix construction of `n ≡ 11 (mod 12)` (lines 1019–1070),
the corank lemma (line 1072, A019), RC applied to `E_n` and `E_{nθ}`, the forward lemma
(line 1086; A020, A066, A082) and rescaling. RC itself is a new, unrefereed 2-converse for the
non-CM curves `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` and carries 39 audit records that occur only in its
proof (A022–A045, A049–A054, A067–A070, A073–A075, A080, A081; `rv-route-k.md` §3).

### 3.2 Route K's trust leaves

Route K deletes RC and its 39 records. Depending on the variant, it imports:

- **K-Kriz**: RK1 (Kriz 10.13), RK3 (Cassels–Tate, already A019), RK8, RK9.
- **K-TYZ**: RK4 (TYZ 1.2), RK5 (Smith 2.2, or a direct proof of the rows used), RK7
  (Gross–Zagier, the rank part of A020), RK8, RK9. Neither Cassels–Tate, Kolyvagin nor BCDT is
  needed.

Dirichlet (A057), reciprocity and CRT are used by the descent in both variants, as in the
manuscript.

The records follow.

---

### RK1: Kriz, rank-one 2-converse for curves with CM by `ℤ[i]`

**Source.** D. Kriz, *Supersingular main conjectures, Sylvester's conjecture and Goldfeld's
conjecture*, arXiv:2002.04767v5. Read in the v5 LaTeX source and the v5 PDF (215 pages):
Theorem 1.1 (p. 4), Assumption 5.1 (p. 104), Assumption 5.6 and Example 5.7 (p. 106),
Assumption 7.20 (p. 147), §9.2 (p. 179), Theorem 9.23 (p. 188), Definition 10.1 (pp. 189–190),
Proposition 10.5 and Theorem 10.8 (pp. 192–194), Theorem 10.13 (p. 198), Theorem 10.17
(p. 199). Page numbers are those of the PDF.

**Version and status (VERIFIED, 2026-11-08).** Five arXiv versions: v1 12 Feb 2020, v2 26 Jul
2021, v3 14 Sep 2021, v4 22 Jun 2022, v5 19 Oct 2022. The arXiv record has no journal reference,
and a Crossref query finds no journal article with this title. The author's monograph
*Supersingular p-adic L-functions, Maass–Shimura operators and Waldspurger formulas* (Annals of
Math. Studies, Princeton, 2021) is a different work. Status: **unrefereed preprint**.

**Exact statement.** Theorem 10.13 (Rank 1 p-Converse Theorem): *Let `E/ℚ` be an elliptic curve
with CM by `O_K` and suppose `p` is ramified in `K`. Then*
`r_p(E/ℚ) := corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 1 ⟹ r_an(E/ℚ) = r_alg(E/ℚ) = 1` *and*
`#Ш(E/ℚ) < ∞`. Theorem 1.1 cites Theorems 9.23 and 10.13 and states only `r_p = r ⟹ r_an = r`
for `r = 0, 1`. Theorem 10.17(2): for `E^d : y² = x³ − d²x`, `r₂(E^d/ℚ) ≤ 1` implies
`r_an = r_alg = r₂` and `#Ш < ∞`; its proof reads "immediately follows from Theorems 9.23 and
10.13 with `p = 2` and `K = ℚ(i)`".

**Conventions (VERIFIED).**
- "`E/ℚ` has CM by `O_K`" means that the base change `E/K` has `End(E/K) ≅ O_K` (Theorem 1.1).
  Then `K` has class number one and `p` is the unique ramified prime (Assumption 5.1).
- `Sel_{p^∞}(E/ℚ)` is the usual Selmer group, the kernel of
  `H¹(ℚ, E[p^∞]) → Π_ℓ H¹(ℚ_ℓ, E)` (Definition 10.1).
- `f₀` is the positive generator of the prime-to-`p` part of the conductor of the Hecke
  character of `E`; `f₀²` is the prime-to-`p` part of the conductor of `E` (§9.2, citing
  Bertolini–Darmon–Prasanna, Proposition 3.13).

**Hypotheses, as used in the proof (VERIFIED).**
1. The construction assumes `f₀ ≥ 4` (Assumption 5.6(1), Example 5.7, Assumption 7.20).
   For `f₀ ≤ 3`, the proofs of 9.23 and 10.13 appeal to the LMFDB: "for `p = 2` all elliptic
   curves with CM by `ℤ[i]` or `ℤ[√−2]` of conductor `≤ 3²·2⁸ = 2304`" (proof of 9.23,
   p. 188; the proof of 10.13 refers back to it). The proof of 10.13 says "Recall that `N²` is
   the prime-to-`p` part of the conductor", a typo for `f₀²`.
2. Root number `−1` is imported from the `p`-parity theorem (Nekovář, Kim,
   Dokchitser–Dokchitser) in Proposition 10.5.
3. Further imports inside the proof: Rubin's main conjecture machinery, the equivariant main
   conjecture of Johnson-Leung–Kings (appendix), Rohrlich's nonvanishing theorem (choice of
   `χ₀`), and Yuan–Zhang–Zhang's Gross–Zagier formula on Shimura curves (Theorem 10.8).
4. **A finding.** Theorem 10.8 (on which 10.13 rests) argues by contradiction. It shows that
   otherwise no `E'` with CM by `O_K`, `f₀' ≥ 4` ("assume `f₀' ≥ 4`", p. 193) and
   `r_p(E') = 1` could have analytic rank one, and it refutes this with an example from the
   LMFDB. For `K = ℚ(i)`, `p = 2` the example is `256b1 : y² = x³ − 2x`. That curve has
   conductor `256 = 2⁸`, so `f₀' = 1`, which violates the stated assumption (VERIFIED, PARI,
   `out_kriz_examples.txt`). The step is repaired by `E' = C_5 : y² = x³ − 25x`:
   - conductor `800 = 2⁵·5²`, so `f₀' = 5`;
   - rank 1 with generator `(−4, 6)` and `dim Sel₂ = 3`, so `r₂ = 1`;
   - analytic rank 1: root number `−1` and `L'(C_5, 1) ≈ 2.2274`.

   (VERIFIED numerically, PARI.) The same slip occurs for `K = ℚ(√−2)` (example `256a1`). It
   does not threaten the theorem, but it shows that the proof has not been refereed.

**Translation to Route K (VERIFIED unless marked).**
- Curves: `E = C_d`, `d` squarefree and nonzero, `K = ℚ(i)`, `p = 2`. `C_d` has CM by `ℤ[i]`
  over `ℚ(i)` via `[i](x, y) = (−x, iy)` (STANDARD). The sign of `d` is immaterial
  (`C_d = C_{−d}`), and so is squarefreeness (`C_d ≅ C_{dλ²}`).
- `f₀` is the odd part of `|d|`. PARI gives conductors `32d²` for odd `d` and `64(d/2)²` for even
  `d` (`d = 1, 2, 3, 5, 6, 7, 10, 11, 13`, `out_kriz_examples.txt`); the general formula is
  STANDARD.
- Hypothesis check: Route K applies the converse only to Selmer-minimal `C_d`, with
  `d = nθ` (`θ > 1`) or `d = n ≠ ±β`. The case `θ = 1` uses 2-torsion and `n = ±β` uses the
  point `(β, 0)`. If `θ > 1`, then `θ` has a prime factor `≥ 11`, because `gcd(θ, 2730) = 1`.
  If the auxiliary primes of `n` are taken `≥ 11` (Dirichlet allows this), every converse
  curve has `f₀ ≥ 11`. In any case `f₀ ≤ 3` means `|d| ∈ {1, 2, 3, 6}`:
  - `C_1`, `C_2`, `C_3` have `dim Sel₂ = 2`, so they are never converse curves;
  - `C_6` is Selmer-minimal with the explicit generator `(−3, 9)`.

  **The LMFDB step is never needed.**
- Concluded: Selmer-minimal gives `r₂ = 1` by RK3, then Kriz gives `rank C_d(ℚ) = 1`, then RK9
  gives the point. Theorem 10.17(2) sits under header hypotheses (full rational 2-torsion, no
  cyclic 4-isogeny) that belong to its part (1); cite Theorem 10.13 directly.

**Verdict.** Usable with the stated extra hypothesis that an unrefereed 215-page preprint is
accepted as a citation, together with the repair of Theorem 10.8 above. Mathematically it is the
best fit: no congruence conditions, no extra condition on the Selmer class.

### RK2: Kriz, rank-zero converse (Theorem 9.23)

*Statement:* for `E/ℚ` with CM by `O_K` and `p` ramified in `K`,
`r_p(E/ℚ) = 0 ⟺ r_an(E/ℚ) = 0`. Route K never needs to prove rank zero. **Not needed.**

### RK3: The Cassels–Tate pairing is alternating

**Source.** Manuscript Lemma 5.4 (`lem:corank`, line 1072) and record A019 (Poonen–Stoll,
Corollaries 4 and 7, Theorem 8(3)). For elliptic curves, Cassels, J. reine angew. Math. 211
(1962), already gives an alternating nondegenerate pairing on `Ш/Ш_div` (STANDARD).

**Use in Route K (VERIFIED, logic).** `C_d(ℚ)_tors = (ℤ/2)²` (STANDARD; e.g. Koblitz,
*Introduction to elliptic curves and modular forms*, Ch. I, §9). The exact sequence
`0 → C_d(ℚ)[2^∞]/2 → Sel₂ → Sel_{2^∞}[2] → 0` gives `dim Sel_{2^∞}[2] = 1` for a Selmer-minimal
curve. Write `Sel_{2^∞} ≅ (ℚ₂/ℤ₂)^{r₂} ⊕ F` with `F` finite; then `F ≅ Ш[2^∞]/div`. If
`r₂ = 0`, then `F = Ш[2^∞]` is finite, cyclic and nonzero. That is impossible, because a
nondegenerate alternating pairing on a finite abelian group forces it to have the form `G × G`.
So `r₂ = 1`, which is Kriz's hypothesis.

**Verdict.** Usable as is; needed only in K-Kriz.

### RK4: Tian–Yuan–Zhang, analytic rank one from genus class numbers

**Source.** Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number
problem*, Asian J. Math. 21 (2017), no. 4, 721–774, DOI 10.4310/AJM.2017.v21.n4.a5 (pages per
Crossref). Read in arXiv:1411.4728v1 (18 Nov 2014), the only arXiv version, LaTeX source and
PDF: Theorems 1.1 and 1.2 (§1), Proposition 3.4, Theorem 3.5 and its proof (end of §3).

**Version and status.** Published in a refereed journal. **The journal text could not be
retrieved here**, so the statement and its numbering in the journal must be checked against the
arXiv text quoted below. Smith (RK5) also worked from arXiv v1.

**Exact statement (arXiv v1, Theorem 1.2).** *Let `n ≡ 5, 6, 7 (mod 8)` be a positive and
square-free integer. Then `𝓛(n)` is an integer. If `n ≡ 5, 7 (mod 8)`, then `2^{−ρ(n)}𝓛(n)`
is even only if*

```
Σ_{n = d₀⋯d_ℓ, d_i ≡ 1 (8), i > 0} Π_i g(d_i)  ≡  Σ_{n = d₀⋯d_ℓ, d₀ ≡ 5,6,7, d₁ ≡ 1,2,3, d_i ≡ 1 (8), i > 1} Π_i g(d_i)  ≡ 0 (mod 2).
```

*If `n ≡ 6 (mod 8)`, then `2^{−ρ(n)}𝓛(n)` is even only if the second sum is `≡ 0 (mod 2)`.
All decompositions are non-ordered with `d_i > 1`.* The notation:

- `g(d) = #2Cl(ℚ(√−d))`, which is odd exactly when the class group has no element of order 4;
- `E_n : ny² = x³ − x`, with root number `−1` for `n ≡ 5, 6, 7` (Birch–Stephens);
- `𝓛(n) = [L'(E_n, 1)/(2^{2k(n)−2−a(n)} Ω_{n,∞} R_n)]^{1/2}` if `ord_{s=1} = 1` (similarly
  with `L(E_n, 1)` if the order is 0), and `𝓛(n) = 0` if `ord_{s=1} L(E_n, s) > 1`;
- `2^{ρ(n)} = [E_n(ℚ) : φ_n(A_n(ℚ)) + E_n[2]]` for the 2-isogeny `φ_n : A_n → E_n`.

**Consequence used.** If one of the sums is odd, then `𝓛(n) ≠ 0`, so `ord_{s=1} ≤ 1`, and the
root number gives `ord_{s=1} L(E_n, s) = 1`. This is the form quoted by Smith (Theorem 2.1).

**A convention to fix (VERIFIED by reading).** The statement in §1 does not say whether `d₁` may
be `1`, nor how a factor `d₁ ≡ 1 (mod 8)` is counted against the factors `d_i`, `i > 1`. The
proof settles it. In Proposition 3.4 the decomposition allows `d₁ = 1`: the term `Z(n)` is
`d₀ = n, d₁ = 1`. The proof of Theorem 3.5(2), the last paragraphs of §3, extracts these parity
conditions:

- for `n ≡ 5, 7`, the coefficients of `τ((1−i)/2)` and `τ(1/2)` must be even:
  `Σ_{d₀ ≡ 5, d₁ ≡ 1,3, d_i ≡ 1} Π g` and `Σ_{d₀ ≡ 7, d₁ ≡ 1,3, d_i ≡ 1} Π g`;
- for `n ≡ 6`, the coefficients of `τ(i/2)` and `τ(1/2)` must have the same parity:
  `Σ_{d₀ ≡ 6, d_i ≡ 1} Π g + Σ_{d₀ ≡ 7, d₁ ≡ 2, d_i ≡ 1} Π g ≡ 0`.

With multiset decompositions and `d₁ = 1` allowed, these are exactly Smith's `𝓛_{5a}, 𝓛_{5b}`,
`𝓛_{7a}, 𝓛_{7b}` and `𝓛_6`, and the conditions of Theorem 1.2 are equivalent to Smith's. If
`d₁ > 1` were forced, the second sum would change by `g(n)`, and the proof does not support that
reading. The journal version should be checked for a clarified statement.

**Translation to Route K (VERIFIED unless marked).**
- `E_n ≅ C_n` over `ℚ` via `(x, y) ↦ (nx, n²y)`. For a Route K curve `C_d` (`d` squarefree, any
  sign) apply the theorem to `n = |d|`; `C_d = C_{|d|}`, and the first Kummer coordinates agree.
- **Which `d`.** TYZ applies only to `|d| ≡ 5, 6, 7 (mod 8)`. For Selmer-minimal `C_d` this is
  automatic: `dim Sel₂ − 2` is odd exactly for `n ≡ 5, 6, 7`. This is VERIFIED for all 3,000
  squarefree `n < 5000` (`out_parity_check.txt`), and it is a theorem (STANDARD: 2-Selmer
  parity, Monsky; root numbers, Birch–Stephens).
- **But not every Selmer-minimal `d` is certified.** In the samples 60% (`|d| ≡ 6`) to 93%
  (`|d| ≡ 7`) are (§2.2); asymptotically 1/2 to 3/4.
  So the descent must also realize TYZ's condition on each converse curve. RK6 shows that this
  is a linear condition on the Selmer class, and a 2-adic condition on `β` when
  `|d| ≡ 5, 6 (mod 8)`.
- Concluded: `ord_{s=1} L(C_d, s) = 1`, then RK7 gives `rank ≥ 1`, then RK9 gives the point.
- Imports of TYZ's own proof: Waldspurger's formula, the Gross–Zagier formula of
  Yuan–Zhang–Zhang, and Tian's induction. For their remark on rank, they cite Coates–Wiles,
  Rubin, Gross–Zagier and Kolyvagin.

**Verdict.** Usable, published and refereed, with the stated extra hypothesis that each converse
curve satisfies the criterion. The descent can arrange this (§4.2). Compare with the journal
statement before citing.

### RK5: Smith, TYZ's sums as bordered Monsky determinants

**Source.** A. Smith, *The congruent numbers have positive natural density*,
arXiv:1603.08479v2 (29 Mar 2016). Read in the LaTeX source and PDF: Theorems 1.4, 2.1, 2.2,
Table 1 (Rédei determinants for `g`), Table 2, Propositions 2.4–2.5, and the proofs of all eight
rows (§2.1–2.2).

**Version and status.** Two arXiv versions, both from March 2016; no journal version found
(Crossref). **Unrefereed preprint.** It is not Smith's later work on `2^∞`-Selmer groups
(arXiv:1702.02325), which Kriz cites.

**Exact statement.** Theorem 2.2: *With `A`, `y` and `z` defined from `n` as above, the second
and third columns of Table 2 are equal in the rows corresponding to `n mod 8`.* The data:

- `n > 0` squarefree, with odd part `p₁⋯p_r`;
- `(d/p)₊ = (1 − (d/p))/2 ∈ 𝔽₂`, `y_i = (−1/p_i)₊`, `z_i = (2/p_i)₊`;
- `A_{ij} = (p_j/p_i)₊` for `i ≠ j`, and `A_{ii} = Σ_{j≠i} A_{ij}`.

The rows needed here:

| Row | Second column (TYZ sum) | Third column |
| --- | --- | --- |
| 5a | `Σ_{d ≡ 5 (8)} g(d)𝓛(n/d)` | `|A+Aᵀ, Aᵀ, y+z; A, D_z, 0; (y+z)ᵀ, 0, 0|` |
| 5b | `Σ_{d₀ ≡ 7, d₁ ≡ 3} g(d₀)g(d₁)𝓛(n/d₀d₁)` | `|A+Aᵀ, Aᵀ, 0; A, D_z, y; 0, yᵀ, 0|` |
| 6 | `Σ_{d₀ ≡ 7n (16), d₁ ≡ 7} g g 𝓛 + Σ_{d ≡ n (16)} g(d)𝓛(n/d)` | `|A+Aᵀ+D_{y+z}, Aᵀ, y; A, D_z, y; yᵀ, yᵀ, 0|` |
| 7a | `Σ_{d ≡ 7} g(d)𝓛(n/d)` | `|A+Aᵀ, Aᵀ, y+z, 0; A, D_z, 0, y; (y+z)ᵀ, 0, 0, 0; 0, yᵀ, 0, 0|` |
| 7b | `Σ_{d₀ ≡ 5, d₁ ≡ 3} g g 𝓛` | `|A+Aᵀ, Aᵀ, y+z, y; A, D_z, 0, 0; (y+z)ᵀ, 0, 0, 0; yᵀ, 0, 0, 0|` |

Here `𝓛(1) = 1`, and `𝓛(m)` for `m ≡ 1 (8)` is the parity of the sum over unordered
factorizations of `m` into factors `≡ 1 (8)` of `Π g` (Smith's recursion); otherwise `𝓛(m) = 0`.

**Proof status (VERIFIED by reading).**
- Row 1 (Propositions 2.4–2.5) is a complete but terse expansion of the determinant over
  involutions.
- The seven other rows reduce to the same closure argument, with short case analyses; several
  steps say only "the normal argument". Rows 5b and 6, the only rows used by the recommended
  variant, take about half a page each.
- **A slip:** after Table 1 the text says `g(n)` "is nonzero if and only if `ℚ(√−n)` has an
  element in its class group of exact order four". Table 1 and TYZ's definition give the
  opposite: the computation below confirms that the Table 1 determinant is 1 exactly when there
  is no element of order 4. The slip is in the prose only.

**Independent verification (VERIFIED, `smith22_check.py`).** The check:

- implements Table 2 from Legendre symbols;
- implements TYZ's sums with `g(d)` computed from PARI class groups, which is independent of
  Rédei theory;
- implements Table 1;
- compares them.

Results:

- All 12,159 squarefree `n < 20000`, about 2,070 per row: **0 mismatches** in all eight rows
  and in Table 1 (`out_smith22_n20000.txt`).
- 300 random `n` with 4–9 odd primes below 60, and 150 random `n` with 4–9 odd primes below 541
  (40% of them even): **0 mismatches** (`out_smith22_large.txt`).

**Translation to Route K.** It converts TYZ's condition into 𝔽₂-linear algebra on the same
Legendre-symbol data that governs the descent, which is what the descent proof needs. In the
recommended variant only rows 5b and 6 are used (RK6).

**Verdict.** Usable as an elementary identity: verified on more than 12,000 inputs, with a
complete if terse proof. Since it is unrefereed, a written proof of rows 5b and 6 should
accompany the citation. That is a short exercise following Smith §2.2.

### RK6: TYZ's criterion is a linear condition on the non-torsion Selmer class

This record is not an external theorem. It explains why the extra condition of RK4 is cheap for
Route K.

**Lemma (proved; VERIFIED on 3,000 random matrices, `bordered_lemma.py`).** Let `M` be a
symmetric matrix over a field with corank one and kernel spanned by `k`. Then
`det [[M, v], [vᵀ, 0]] = −c (vᵀk)²` with `c ≠ 0`; over `𝔽₂`,
`det [[M, v], [vᵀ, 0]] = vᵀk`.

*Proof.* `M·adj(M) = det(M)·I = 0`, so the columns of `adj(M)` lie in `ker M = ⟨k⟩`. Since
`adj(M)` is symmetric, `adj(M) = c kkᵀ`, and `c ≠ 0` because `adj(M)` has rank one when the
corank is one. Laplace expansion along the last row and column gives
`det [[M, v], [vᵀ, 0]] = −vᵀ adj(M) v`. ∎

**Corank (VERIFIED, `out_bordered_lemma.txt`, 600 random `n < 10⁶`).** Let
`M₁ = [[A+Aᵀ, Aᵀ], [A, D_z]]` and `M₂ = [[A+Aᵀ+D_{y+z}, Aᵀ], [A, D_z]]`. Then:

- for `n ≡ 5 (mod 8)`: `corank M₁ = dim Sel₂ − 2`;
- for `n ≡ 6`: `corank M₂ = dim Sel₂ − 2`;
- for `n ≡ 7`: `corank M₁ = dim Sel₂ − 1`, which is why rows 7a and 7b carry two borders.

This agrees with Monsky's description of `Sel₂(C_n)` (STANDARD, RK8) and with Smith's remark in
§1 ("this condition on Selmer groups is equivalent to a certain singular Monsky matrix `M`
having corank one").

**Consequence.** For a Selmer-minimal `C_n` with `n ≡ 5` or `6`, the TYZ determinant of each row
is a linear functional evaluated at the kernel vector, which represents the non-torsion Selmer
class. **The TYZ certificate is therefore a property of the Selmer class `σ`.**

**The rules (VERIFIED by computation, `tyz_class_link.py`, `tyz_beta_rule.py`, 900 random
Selmer-minimal `n`, `out_tyz_class_link.txt`, `out_tyz_beta_rule.txt`).** Let `(a, b)` be any
of the four representatives of the coset `σ + torsion` in coordinates `(x, x − n)`, written as
signed squarefree integers. Every rule below takes the same value on all four representatives,
and agrees with Smith's determinant on every sample.

| `n mod 8` | Row | TYZ row nonzero exactly when |
| --- | --- | --- |
| 5 | 5b | `χ₋₁(|a|_odd) = 1`, i.e. the odd part of `|a|` is `≡ 3 (mod 4)` |
| 5 | 5a | `[b < 0] + χ₋₁(|b|_odd) + χ₂(|b|_odd) = 1` |
| 6 | 6 | `[a even] + χ₋₁(|a|_odd) = 1` |
| 7 | 7a | `χ₋₁(|a|_odd) + [b even] = 1` |
| 7 | 7b | `χ₂(|b|_odd) = 1` |

Two control tests:

- No rule in `a` alone predicts rows 5a, 7a or 7b; `tyz_beta_rule.py` finds conflicts for those
  rows when `b` is ignored.
- With the 2-adic and sign data of both `a` and `b`, the full TYZ certificate is determined
  without conflict (60 keys, 0 conflicts).

**Where the rules come from (VERIFIED by computation, `kernel_ident.py`, `out_kernel_ident.txt`,
300 Selmer-minimal `n` in each class).** For an integer `c`, write `S(c) ∈ 𝔽₂^r` for the
indicator vector of the odd primes of `n` that divide `c`. Then the kernel of Smith's block is
spanned by

- `n ≡ 5 (mod 8)`: `k = (S(ab), S(a))` for exactly one representative `(a, b)`, and that
  representative has `a` odd (300 of 300);
- `n ≡ 6 (mod 8)`: `k = (S(ab), S(b))` for exactly one representative, and it has `a` odd
  (300 of 300).

Here `a`, `b` and `ab` are the classes of `x`, `x − n` and `x + n`. With the bordered lemma this
gives the rows directly:

- row 5b: `(0, y)ᵀk = Σ_{p | a} (−1/p)₊ = χ₋₁(|a|_odd)`;
- row 5a: `(y + z, 0)ᵀk = Σ_{p | ab} (−2/p)₊`, which by the local relations equals the form in
  the table;
- row 6: `(y, y)ᵀk = yᵀ(S(ab) + S(b)) = yᵀS(a) = χ₋₁(|a|_odd)` with `a` odd, which is the
  coset-invariant rule `[a even] + χ₋₁(|a|_odd)`. Multiplying `a` by `n` changes its parity and
  multiplies its odd part by `n/2 ≡ 3 (mod 4)`, so the rule is invariant.

What remains unwritten is a proof of the two kernel identifications from the local conditions
of RK8, i.e. a change of basis between Monsky's matrix and Smith's symmetrized one. It is
SPECULATIVE only in the sense of not yet written; it is routine linear algebra over `𝔽₂`.

**Application to Route K.** Take `σ_d` with first coordinate `β` on both converse curves
`C_n, C_{nθ}`. Since `θ ≡ 1 (mod 8)`, `|nθ| ≡ |n| (mod 8)`, so:

- if `|n| ≡ 5 (mod 8)`, `β` is odd (the 2-adic image of an odd `d ≡ 5` has only odd first
  coordinates, `rv-route-k.md` §4.4) and `|β| ≡ 3 (mod 4)`, then **both curves are certified**
  by row 5b;
- if `|n| ≡ 6 (mod 8)` and `[β even] ≠ [|β|_odd ≡ 3 (mod 4)]`, then **both curves are certified**
  by row 6.

These are conditions on `m` (which fixes the 2-adic class of `β`; all eight classes of
`ℚ₂*/ℚ₂*²` and both signs are reachable, `rs-pole.md` §4.1) and on `n' = n/β` modulo 8. For
example, `|β| ≡ 3 (mod 4)` odd needs `n' ≡ 3 (mod 4)`. The choice `n = ±β` is never compatible
with these two rules, so this variant always uses auxiliary primes and the converse on both
curves.

**Test in the Route K setting (VERIFIED, `ktyz_rule_test.py`, `out_ktyz_rule_random.txt`).**
The test draws 30 admissible inputs from the `random` generator of `rv-route-k`. For every
multiplier it searches `n' ∈ {1, θ}`, single auxiliary primes below 200 and products of two,
and keeps the solutions found by the Kriz-form descent. For each converse curve of each
solution (up to 40 solutions per input) it compares Smith's determinant with the prediction of
the two `β`-rules.

- 1,348 rule checks, **0 violations**.
- **30 of 30 inputs** have a solution in which every converse curve is certified by the
  `β`-rule alone.

**The K-TYZ-β descent itself (VERIFIED, `ktyz_beta_search.py`, `out_ktyz_beta_*.txt`).** The
search is restricted from the start to multipliers whose `β` satisfies a rule and to `n'` in the
required class mod 8. It uses 1–4 random auxiliary primes `≥ 11` from the first 400 such primes,
prefiltered by the necessary local conditions. It asks that `C_n` and `C_{nθ}` both be
Selmer-minimal with class `β`, and then re-checks Smith's determinant (row 5b or 6) on both
curves.

| Family (`rv-route-k` generators) | Solved | Solutions failing the TYZ re-check |
| --- | --- | --- |
| `random` | 30 of 30 (median 1 auxiliary prime, at most 195 evaluations) | 0 |
| `manybeta` (`ω(β)` up to 14) | 9 of 10 at the first budget; the 10th solved on retry (below) | 0 |
| `edgeS0` (minimal `S₀` valuations, small `β`) | 10 of 10 | 0 |
| `extremeB` (`B` near `1/2` or tiny) | 10 of 10 | 0 |
SMOOTH_ROW

The unsolved `manybeta` input was replayed and retried with a pool of 2,000 primes, 1–6
auxiliary primes and 3,000 evaluations per pair (`ktyz_retry.py`, `out_ktyz_retry_manybeta2.txt`).
- 23 of the 48 (multiplier, rule) pairs then succeed. For example `m = −2730` with rule 5 succeeds
  after 34 evaluations with the single prime `n' = 8719`, which lies outside the first pool.
- All 23 solutions pass the TYZ re-check.
- The other 25 pairs fail within 3,000 evaluations. This is the fixed-multiplier difficulty that
  `rv-route-k.md` §4.4 already met in the Kriz form. It concerns the descent, not the deep input.


### RK7: Gross–Zagier, analytic rank one gives a point of infinite order

**Source.** Record A020 (Gross–Zagier; Kolyvagin MPI/90-69, Theorem 1; Kato, Corollary 14.3;
BCDT, Theorem A), used in Lemma 5.5 (line 1086).

**What K-TYZ needs (STANDARD).** Only `ord_{s=1} L(C_d, s) = 1 ⟹ rank C_d(ℚ) ≥ 1`. This
follows from the Gross–Zagier formula, applied with an auxiliary imaginary quadratic field `K`
satisfying the Heegner hypothesis and `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein,
Murty–Murty, Waldspurger). The input is the same auxiliary Heegner data that A020 already
records. Modularity of `C_d` is classical (CM: Deuring, Shimura; `L(C_d, s)` is a Hecke
L-function), so BCDT (A066) is unnecessary. Kolyvagin's finiteness of Ш is unnecessary (RK9).

**Verdict.** Usable as is; a strict sub-application of A020.

### RK8: Complete 2-descent for `C_d`; Monsky's matrices

**Source.** STANDARD:
- Silverman, *The Arithmetic of Elliptic Curves*, X §1, Proposition 1.4 (complete 2-descent
  with full 2-torsion);
- Heath-Brown, *Invent. Math.* 118 (1994), Appendix by Monsky (Selmer rank of `C_n` as
  `2 + corank` of an explicit `𝔽₂` matrix);
- the local images used in `rv-route-k.md` §4.4.

**Use.** The descent lemma (all variants) and RK6. The computations rely on
`scratch/rv-route-k/sel2cong.py`. Its output was cross-checked there against PARI's `ell2cover`
(30 curves) and against actual generators. Here it was used again on the 3,000 curves of
`out_parity_check.txt` and the 900 curves of RK6, consistently with Smith's corank formulas for
`n ≡ 1, 2` (`rv-route-k.md` §4.3) and with the corank table of RK6.

**Verdict.** Usable as is.

### RK9: Rank ≥ 1 and Selmer-minimality give a point with prescribed first coordinate

**Statement (VERIFIED, logic).** Let `C_d` have `dim Sel₂ = 3` and `rank C_d(ℚ) ≥ 1`. Then every
class `σ ∈ Sel₂(C_d)` is the image of a non-torsion rational point. In particular, if some class
has first coordinate `β`, then `C_d` has a rational point with abscissa in `βℚ*²`.

*Proof.* `C_d(ℚ)/2C_d(ℚ)` injects into `Sel₂` and has dimension `2 + rank ≥ 3`, hence it equals
`Sel₂` (and the rank is one). If `P` maps to `σ`, so does `P + 2Q` for a non-torsion `Q`, and it
is non-torsion. For a non-torsion point, `x ∉ {0, ±d}`, so the first Kummer coordinate is the
class of `x`. ∎

So no pairing argument (Cassels–Tate or Poonen–Stoll) is needed at this step, and neither is
finiteness of Ш. Cassels–Tate enters only in K-Kriz, to turn `dim Sel₂ = 3` into corank one
(RK3). Without Selmer-minimality, rank one would not suffice: the class `σ` could then lie in the
part of `Sel₂` that maps onto `Ш[2]`. That is why the descent must produce Selmer-minimal
curves, as the manuscript's descent does for `E_ℓ` (lines 1035–1070).

---

## 4. Candidate cheaper routes

All routes below presuppose Route K's change of curve and its descent lemma
(`rv-route-k.md` §4.4), which is the remaining elementary gap. They differ in the deep input.

### 4.1 K-Kriz

- **Idea.** Selmer-minimal gives corank one (RK3), then Kriz 10.13 gives rank one, then RK9.
- **What it replaces.** RC (Theorem 5.3) and its 39 records, by RK1 and RK3.
- **Why it might work.** Kriz's theorem covers every converse curve. The descent needs no
  condition beyond Selmer-minimality and the class `β`. The `f₀ ≤ 3` cases do not occur.
- **Main obstacle.** Status: an unrefereed 215-page preprint, in which this audit found one
  (repairable) error in the proof of Theorem 10.8.
- **First test.** Check whether the author or the literature records a published version or an
  erratum. Success criterion: a journal reference, or an expert's written confirmation of the
  repaired Theorem 10.8.

### 4.2 K-TYZ-β (recommended)

- **Idea.** Use TYZ (RK4) with Gross–Zagier (RK7). Strengthen the descent so that `β` and `n`
  satisfy one of the two 2-adic rules of RK6:
  - `|n| ≡ 5 (mod 8)`, `β` odd, `|β| ≡ 3 (mod 4)`; or
  - `|n| ≡ 6 (mod 8)` and `[β even] ≠ [|β|_odd ≡ 3 (mod 4)]`.

  Both converse curves are then certified by rows 5b or 6, and only those two rows of Smith's
  identity are needed.
- **What it replaces.** RC and its 39 records, by TYZ (published), two rows of Smith (reprovable
  in a page), and the rank part of A020. Poonen–Stoll (A019), Kolyvagin and BCDT also drop out.
- **Why it might work.**
  - The extra conditions are on `m` (a finite choice that covers every 2-adic class of `β`) and
    on `n'` modulo 8 (a congruence on the auxiliary primes, chosen by Dirichlet anyway).
  - In the experiment of RK6 every input admitted a solution certified by the `β`-rule alone.
  - The `rv-route-k` TYZ experiments solved 60 of 60 inputs with unrestricted TYZ certificates.
- **Main obstacle.**
  - The descent lemma must be proved with `n'` in a prescribed class mod 8 and `m` restricted to
    the multipliers whose `β` satisfies the rule. The congruence of `n'` interacts with the
    2-adic Selmer conditions and with the symbols `(−1/q), (2/q)` of the auxiliary primes.
  - The rules of RK6 need a written proof (matching Smith's kernel with Monsky's parametrization).
  - TYZ's journal statement must be compared with arXiv v1.
- **First test.** Fix the rule `|n| ≡ 5`, `|β| ≡ 3 (mod 4)` and extend the descent search to
  insist on it, on the hard families of `rv-route-k` (`manybeta`, `smooththeta`). Success
  criterion: every input of 30 per family is solved with both curves certified by row 5b or 6.
  Then write the descent proof with the extra 2-adic slot.

### 4.3 K-TYZ (unrestricted)

- **Idea.** As in 4.2, but accept any row of Table 2.
- **Gain.** More freedom (`n = ±β` allowed for `|β| ≡ 5, 7`).
- **Cost.** Rows 5a, 7a and 7b depend on the second Kummer coordinate `b`, which the descent
  does not control directly. Their rules involve `b`'s sign, parity and residue mod 8, which
  are fixed by the local conditions at 2 and `∞` only up to a choice.
- **Assessment.** Useful as a fallback in the search; worse than 4.2 for a proof.

### 4.4 K-L: a narrow Lean hypothesis

- **Idea.** Instead of `PoleCompleteness_C`, state in Lean the deep input in the form consumed:

  > for squarefree `d` with `|d| ≡ 5 (mod 8)` (resp. `6`) and the explicit Monsky matrix of
  > corank one, whose non-torsion Selmer class has first coordinate `a` with
  > `|a|_odd ≡ 3 (mod 4)` (resp. the row-6 rule), `C_d` has a rational point of infinite order.

  Then prove the descent and RK9 in Lean.
- **Gain.** The Lean hypothesis becomes a direct consequence of a published theorem (TYZ with
  Gross–Zagier), with the bookkeeping proved.
- **Obstacle.** Formalizing the descent (Legendre symbols, CRT, Dirichlet) is substantial but
  elementary.
- **First test.** State it and check that `test_complete` and `slope_complete` close from it
  and the descent lemma (as `sorry`). SPECULATIVE effort estimate: weeks.

### 4.5 Routes that are not usable

- **Heegner, Birch–Stephens and Monsky criteria for one or two odd primes.** Not usable: every
  prime of `β` divides `n` (`rs-pole.md` §2.3), and `ω(β)` is unbounded.
- **Tian's earlier criterion** (Cambridge J. Math. 2014: all prime factors `≡ 1 (mod 8)`, no
  4-torsion) and **TYZ's Corollary 1.4** (single genus class number, conditions on the primes
  `≡ 3 (mod 4)` or `≡ ±3 (mod 8)` of `n`). Not usable: they restrict the primes of `n`, hence of
  `β`, which are dictated by the input.
- **Keeping `E_ℓ` and citing a published converse.** None exists for non-CM curves at `p = 2`
  with full rational 2-torsion (`rs-pole.md` §4.2).

## 5. Ranking and recommendation

| Rank | Route | Deep inputs | Chance |
| --- | --- | --- | --- |
| 1 | **K-TYZ-β** (§4.2) | TYZ 1.2 (published), Smith rows 5b and 6 (elementary), Gross–Zagier | medium |
| 2 | K-Kriz (§4.1) | Kriz 10.13 (unrefereed), Cassels | medium–high mathematically, but the citation is weaker |
| 3 | K-L (§4.4), after 1 or 2 | the same, as a narrow Lean hypothesis | medium, given 1 or 2 |
| 4 | K-TYZ unrestricted (§4.3) | TYZ, Smith all rows, Gross–Zagier | medium for the search, low for a proof |

**The single most promising next step.** Prove the Route K descent lemma in the K-TYZ-β form:

> For every admissible `B` there are a multiplier `m` and a squarefree `n = βn'` such that
> - `|n| ≡ 5 (mod 8)` with `β` odd and `|β| ≡ 3 (mod 4)`, or `|n| ≡ 6 (mod 8)` with
>   `[β even] ≠ [|β|_odd ≡ 3 (mod 4)]`; and
> - `C_n` and `C_{nθ}` are both Selmer-minimal with a class of first coordinate `β`.

Then PC for the modified polynomial follows from TYZ 1.2, Smith's rows 5b or 6, Gross–Zagier,
and RK9.

- **Success criterion.** A written proof of the lemma, validated by running the algorithm it
  defines on 30 inputs from each generator of `scratch/rv-route-k/descent_search.py`. Each
  output must be checked with `sel2cong.py` (Selmer-minimality and class `β`) and with Smith's
  determinant (row 5b or 6 nonzero).
- **Chance: medium.**
  - In favour:
    - the deep input is published;
    - the extra conditions are 2-adic and sit inside the descent's free parameters;
    - every test input admitted a `β`-rule solution.
  - Against: the descent lemma itself is unproved even in the Kriz form, and prescribing
    `n' mod 8` removes one degree of freedom that the unrestricted search used. If the
    restricted lemma resists, K-Kriz needs only the unrestricted lemma, at the price of an
    unrefereed citation.

**Which to cite.** TYZ (Asian J. Math. 2017), after confirming the journal statement against
arXiv v1, with Gross–Zagier. Prove rows 5b and 6 of Smith's identity in the text, or cite Smith
with the verification above. Mention Kriz's Theorem 10.13, with the repair of Theorem 10.8, as
an alternative that would make the 2-adic refinement unnecessary once it is refereed.

## Scripts (`scratch/pc-audit/`)

| Script | Purpose | Output |
| --- | --- | --- |
| `smith22_check.py` | Smith's Table 1 and Table 2 against TYZ's genus sums with class groups from PARI | `out_smith22_n20000.txt`, `out_smith22_large.txt` |
| `tyz_class_link.py` | linear rules for TYZ rows in terms of the Selmer class | `out_tyz_class_link.txt` |
| `tyz_beta_rule.py` | which rows are determined by the first coordinate alone | `out_tyz_beta_rule.txt` |
| `bordered_lemma.py` | bordered-determinant lemma; coranks of Smith's blocks against `dim Sel₂` | `out_bordered_lemma.txt` |
| `parity_check.py` | `dim Sel₂ − 2` odd exactly for `n ≡ 5, 6, 7 (mod 8)`, all squarefree `n < 5000` | `out_parity_check.txt` |
| `kriz_examples.py` | conductors, `f₀`, ranks and Selmer dimensions of `256b1` and small `C_d` | `out_kriz_examples.txt` |
| `kernel_ident.py` | kernel of Smith's block in terms of the Selmer class | `out_kernel_ident.txt` |
| `ktyz_rule_test.py` | Route K descent with TYZ certificates predicted by the `β`-rules | `out_ktyz_rule_*.txt` |

Sources were downloaded from arXiv into a separate directory and read as LaTeX and PDF text.
They are not committed.
