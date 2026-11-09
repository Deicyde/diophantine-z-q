# The Tian–Yuan–Zhang citation behind CR₃

This note settles which statement of Tian–Yuan–Zhang (TYZ) the hypothesis CR₃
(`ZInQ.CertifiedRank`, `ZInQKernel/Hypotheses/CertifiedRank.lean`) can rest on. It checks the
form used in `docs/research/tyz-5b.md` (Proposition 1.1 there) against the source, and gives a
proof of that form whose inputs are all unambiguous statements of the paper.

## Verdict

1. **Versions.** arXiv:1411.4728 has exactly one version, v1 (18 Nov 2014). The journal version
   (Asian J. Math. 21 (2017), no. 4, 721–774, DOI 10.4310/ajm.2017.v21.n4.a5) could not be read.
   Crossref registers no erratum or update for it. No readable version states the form used
   (`T_5b(n)` odd ⟹ `𝓛(n) ≠ 0`) directly.
2. **The literal statement of Theorem 1.2 is false.** Theorem 1.2 ends with "all decompositions
   … are non-ordered with all `d_i > 1`". Read that way, the second sum for `n ≡ 5 (mod 8)` is
   `T_5a(n) + g(n) + T_5b(n)` (§1.4). For `n = 26565 = 3·5·7·11·23` and `n = 33117 = 3·7·19·83`
   this sum is odd while `rank C_n(ℚ) = 3`, so `𝓛(n) = 0` (VERIFIED, exact computation). The same
   two values refute the other literal reading, where `d₁ > 1` is a distinguished factor. The
   only true reading admits the trivial factor `d₁ = 1` (reading A). Under that reading the two
   sums are `T_5a` and `T_5a + T_5b`, and the theorem gives exactly the form used.
   Theorem 3.5(2), the "enhanced version", omits the sentence `d_i > 1`, and the proof of
   Proposition 3.4 uses `d₁ = 1` explicitly. So reading A is the authors' intended statement
   too.
3. **The proof in §3.3.** The proof of Theorem 3.5(2) for `n ≡ 5` establishes the `(7, 3)`
   bracket separately. Its last step is independent of the `(5, 1)` bracket (VERIFIED, §2.3).
   The step before it does depend on the rest: the coefficients of the genus point come from
   Proposition 3.4. That proposition is proved by a joint induction over all classes of
   divisors, its proof is a sketch, and its statement has the same `d₁ = 1` ambiguity. The two
   facts tyz-5b supplies are correct. Four more implicit facts are needed, all true (§2.2).
4. **Other published statements.** None found. Smith (arXiv:1603.08479, Theorem 2.1; unrefereed)
   states reading A with the rows `5a` and `5b` separated. Tian's two expository articles
   (ICCM Notices 5 (2017) 51–61; Proc. ICM 2022, 1990–2010) could not be read (UNCHECKED). Six
   other papers that cite TYZ, and three related papers that do not, never restate the theorem
   (§3).
5. **What to cite.** Proposition N below, with the proof of §4. That proof bypasses
   Proposition 3.4 entirely: it computes the coefficients of the genus point modulo 2 directly
   from the recursion that defines it (Lemma N2). Its inputs are Theorem 3.5 (first assertion),
   Lemmas 3.16, 3.18 and 3.21(1), (4), the recursion of §3.1, the `ε`-classification of
   Theorem 3.3, and Lemma 2.8 with Proposition 2.3. All of these are unambiguous. The same
   argument proves reading A of Theorem 3.5(2) for `n ≡ 5` in full. Along the way it settles
   tyz-5b's remark on the `(5, 1)` bracket, which tyz-5b left partly SPECULATIVE.
6. **Kriz.** CR₃ follows from TYZ, Gross–Zagier–Kolyvagin and the elementary parts of tyz-5b for
   *every* `d` it covers, not only the slot curves. Kriz is not needed anywhere in CR₃ (§5.1).
7. **Unrefereed sources** remain in CR₃'s justification (§5.2). The one that matters is the
   manuscript's citation of Kolyvagin through the MPIM preprint MPI/90-69 (Lemma 5.5,
   `lem:forward-rank`; audit record A020). TYZ themselves cite the published papers
   (Izvestiya 1989; Grothendieck Festschrift 1990). The other entries are Smith's preprint (no
   longer used), Kriz (an alternative only), the project's own notes, and the fact that TYZ was
   read in its arXiv form only.

**Proposition N** (the statement to cite). *Let `n ≡ 5 (mod 8)` be positive and squarefree. If*
`T_5b(n) = Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` *is odd, then `𝓛(n) ≠ 0`. Hence
`ord_{s=1} L(E_n, s) = 1`.* Here `𝓛₁(m)` is the sum of `Π g(B)` over the set partitions of the
primes of `m` into blocks `B ≡ 1 (mod 8)`. (Proof in §4; reference: TYZ, Theorem 3.5 and the
argument of its proof of part (2), §3.3, with the coefficient lemma of §4.3 below in place of
Proposition 3.4.)

Every claim carries one of four marks.

- **VERIFIED**: checked against the source text (the arXiv LaTeX source `Period7.tex` of
  1411.4728v1, 3357 lines, e-print sha256 `b295b160…fed2`), proved here, or established by an
  exact computation (scripts in `scratch/nt-tyz/`).
- **STANDARD**: a published theorem whose statement applies as used, with a reference.
- **SPECULATIVE**: an idea, not proved.
- **UNCHECKED**: a source that could not be read here.

Line numbers `Lnnnn` refer to `Period7.tex`. TYZ number theorems, lemmas and propositions on one
counter per section (`\newtheorem{thm}{Theorem}[section]`, L244–247). With that counter, §2 contains
Theorem 2.1, Theorem 2.2 (`LQ`), Proposition 2.3 (`odd`), Theorem 2.4, Lemma 2.5, Theorem 2.6
(label `thm2.3`), Lemma 2.7 (`lem2.6`) and Lemma 2.8 (unlabelled, L1062). §3 contains
Proposition 3.1, Proposition 3.2 (`CM point1`), Theorem 3.3 (`GZ`), Proposition 3.4
(`congruence`), Theorem 3.5 (`m3`), Theorem 3.6 (`CM point2`), …, Lemma 3.16 (`torsion1`),
Lemma 3.17 (`torsion3`), Lemma 3.18 (`torsion2`), Lemma 3.19 (`multiples2`), Lemma 3.20 and
Lemma 3.21 (`betaaction`). (VERIFIED)

## Notation

- `E_n : ny² = x³ − x` (isomorphic to `C_n : y² = x³ − n²x`), `A : 2y² = x³ + x`, `F = ℚ(i)`,
  `A(ℂ) = ℂ/(1+i)ℤ[i]` via `τ`, and `K_n = ℚ(√−n)`, all as in TYZ §3.1.
- `g(d) = #2Cl(ℚ(√−d)) mod 2` (TYZ §1, L363).
- For odd squarefree `m > 0`, a *partition* of `m` is a set partition of its prime factors, and
  its blocks are identified with their products. `w(π) = Π_{B∈π} g(B)`. Write
  `𝓛₁(m) = Σ w(π)` over the partitions with all blocks `≡ 1 (mod 8)`, with `𝓛₁(1) = 1`.
- For `n ≡ 5 (mod 8)`:
  `T_5a(n) = Σ_{d ≡ 5} g(d) 𝓛₁(n/d)`, the partitions with one block of class 5 and all others
  of class 1;
  `T_5b(n) = Σ_{d₀ ≡ 7, d₁ ≡ 3} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)`, one block of class 7, one of class 3, the
  others of class 1.
  These are Smith's `𝓛_5a`, `𝓛_5b` (arXiv:1603.08479, Table 2) and tyz-5b's `T_5b`.
- All parities are in `𝔽₂`. For Gaussian integers, `≡` means modulo `2ℤ[i]`; there `±1 ≡ 1` and
  `±i ≡ i`.

## 1. Sources and exact statements

### 1.1 Versions (VERIFIED where stated)

- **arXiv:1411.4728.** The arXiv API and abs page list a single version, v1 (submitted 18 Nov 2014),
  with no journal reference. The e-print is one LaTeX file, `Period7.tex`. All quotations below are
  from it.
- **Journal.** Crossref gives *Genus periods, genus points and congruent number problem*, Asian J.
  Math. 21 (2017), no. 4, 721–774, DOI 10.4310/ajm.2017.v21.n4.a5. Crossref registers no update,
  correction or erratum for this DOI. The journal text was not accessible (UNCHECKED). In
  particular it is not known whether the journal version changed the statement of Theorem 1.2.
- **Dependencies.** The steps used in §4 rest only on results proved inside TYZ. Their external
  inputs are Waldspurger's formula and the Gross–Zagier formula of Yuan–Zhang–Zhang (Annals of Math.
  Studies 184; TYZ appendix, Theorems A.3, A.8 and A.9 `EGZ`), Gross–Zagier and Kolyvagin (TYZ cite Kolyvagin, Math.
  USSR Izv. 32 (1989), and *Euler systems*, Grothendieck Festschrift II (1990), L3297–3304), and
  Rédei. These are refereed publications, not on arXiv. Tian's *Congruent numbers and Heegner
  points* (arXiv:1210.8231, one version, v1; Cambridge J. Math. 2 (2014)) supplies the induction
  method but is not quoted in the steps used.

### 1.2 The statements (VERIFIED against the source)

**Theorem 1.1** (L371–380). *Let `n ≡ 1, 2, 3 (mod 8)` be positive and squarefree. Then `𝓛(n)` is an
integer, and `𝓛(n) ≡ Σ_{n = d₀d₁⋯d_ℓ, d_i ≡ 1 (8), i > 0} Π_i g(d_i) (mod 2)`. Here all decompositions
`n = d₀⋯d_ℓ` are non-ordered with `d_i > 1` for all `i ≥ 0`. The right-hand side is considered to be 1
if `n = 1`.*

**Theorem 1.2** (L389–409). *Let `n ≡ 5, 6, 7 (mod 8)` be positive and squarefree. Then `𝓛(n)` is an
integer. If `n ≡ 5, 7 (mod 8)`, then `2^{−ρ(n)}𝓛(n)` is even only if*

```
Σ_{n = d₀⋯d_ℓ;  d_i ≡ 1 (8), i>0}  Π_i g(d_i)
   ≡  Σ_{n = d₀⋯d_ℓ;  d₀ ≡ 5,6,7;  d₁ ≡ 1,2,3;  d_i ≡ 1 (8), i>1}  Π_i g(d_i)  ≡  0   (mod 2).
```

*If `n ≡ 6`, [the second sum alone] `≡ 0`. Here all decompositions `n = d₀⋯d_ℓ` are non-ordered with
all `d_i > 1`.*

**Recursion** (§3.1, L1320–1327). `P(n) ∈ A(ℍ'_n)` is defined inductively by

```
P(n) := Z(n) − Σ_{n = d₀d₁;  d₀ ≡ 5,6,7;  d₁ ≡ 1,2,3 (8);  d₁ > 1}  ε(d₀, d₁) 𝓛(d₁) P(d₀),
```

where `Z(n) = Σ_{t∈Φ₀} f_n(P_n)^t` is the genus point and `ε(d₀, d₁) ∈ μ₄` is as in Theorem 3.3. Here
`d₁ > 1` is written explicitly. "`𝓛(d₁) ∈ ℤ` by Theorem 1.1."

**Theorem 3.3** (L1299–1311, the `ε`-part). *`P_χ` is non-torsion only if `χ = χ_{d₀,d₁}` with
`n = d₀d₁`, `d₀ ≡ 5, 6, 7`, `d₁ ≡ 1, 2, 3 (8)`. In that case `P_χ = ε(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in
`A(H'_n(i)) ⊗ ℚ`, where `ε(d₀, d₁) = ±i` if `(d₀, d₁) ≡ (5, 3) (mod 8)` and `ε(d₀, d₁) = ±1`
otherwise.*

**Proposition 3.4** (L1332–1348). *In `A(ℍ'_n)`,*

```
P(n) ≡ Σ_{n = d₀d₁⋯d_ℓ;  d₀ ≡ 5,6,7;  d₁ ≡ 1,2,3;  d_i ≡ 1, i>1}  ε(d₀, d₁) (Π_{i≥1} g(d_i)) Z(d₀)
       + i Σ_{(d₀, d₁, d₂) ≡ (5, 3, 2);  d_i ≡ 1, i>2}  (Π_{i≥1} g(d_i)) Z(d₀)      mod 2A(ℍ'_n).
```

The statement says nothing about ordering or about `d₁ = 1`. Its proof (L2024–2163) needs
`d₁ = 1`: "the contribution by `d₀ = d₀'' = n`, `d₁ = 1` is the single term `Z(n)`" (L2077).

**Theorem 3.5** (L1353–1374). *The vector `𝒫(n) = 2^{−1−ρ(n)}𝓛(n)α_n ∈ A(K_n)^− ⊗ ℚ` is represented by
`P(n)`, in the sense that they are equal in `A(ℍ'_n) ⊗ ℚ`. Moreover (1) `𝓛(n)` is integral; (2) assume
that `P(n) ∈ A(K_n)^− + A[4]`, i.e. `2^{−ρ(n)}𝓛(n)` is even. If `n ≡ 5, 7 (mod 8)`, then [the two sums
of Theorem 1.2] `≡ 0 (mod 2)`; if `n ≡ 6`, [the second sum] `≡ 0`.* Theorem 3.5 does **not** repeat
the sentence "all decompositions are non-ordered with all `d_i > 1`".

**Lemma 2.8** (L1062–1066). *`Σ_{n = d₁d₂} ε(d₁, d₂) 𝓛(d₁) 𝓛(d₂) = Q(n)`, where `ε(d₁, d₂) = ±1` and the
sum is over non-ordered decompositions `n = d₁d₂` with `d₁, d₂ > 0` and `d₂ ≡ 1 (mod 8)`.* (Here
`n ≡ 1, 2, 3`, the setting of §2.)

**Proposition 2.3** (L580–586). *`f_n((B̂^×)²) ⊂ 1 + 2ℤ`; therefore `Q(n) ≡ g(n) (mod 2)`.*

**Lemma 3.16** (L2182–2185). *`ℚ(A[4]) = ℚ(√2, i)` and `A(ℚ(i)) = A[(1+i)³]`.*

**Lemma 3.18** (L2230–2232). *`A(ℍ'_n)_tors = A[(1+i)³]` if `n` is odd.*

**Lemma 3.21** (L2504–2525). With `β₁ = r_∞(−1)r₂(−2)`, `β₂ = r_∞(−1)r₂(6)` and any liftings `β'_j`:
*(1) for `n ≡ 5 (mod 8)`, `Z(n)^{β'₁+1} = Z(n)^{β'₂+1} ∈ g(n)τ((1−i)/2) + ℤτ(1)`; … (4) for `n ≡ 7
(mod 8)`, `Z(n)^{β'₁+1} = Z(n)^{β'₂+1} = g(n)τ(1/2)`.*

**Corollary 1.4** (L427–466) uses only the first sum, with the value `g(n)`. The reading issue below
does not affect it.

### 1.3 The readings of the second sum for `n ≡ 5 (mod 8)` (VERIFIED)

For odd `n ≡ 5`, the classes allowed in the second sum leave two types of term: `(d₀, d₁) ≡ (5, 1)`
and `(d₀, d₁) ≡ (7, 3)`.

- *`(7, 3)` terms.* Here `d₀` and `d₁` are the unique factors of classes 7 and 3, so `d₁ > 1`
  automatically, and the non-ordered factors `d_i ≡ 1`, `i > 1`, form a partition. The product
  `Π_i g(d_i)` runs over all `i ≥ 0`. These terms add up to `T_5b(n)` under every reading.
- *`(5, 1)` terms.* Three readings are possible.
  - **A** (`d₁ = 1` admitted): the factors other than `d₀` form an arbitrary, possibly empty,
    partition into class-1 blocks. The sum is `T_5a(n)`, which equals the first sum.
  - **B** (all `d_i > 1`, non-ordered; `d₁` is just one of the class-1 factors): the partitions
    with one class-5 block and at least one class-1 block. The sum is `T_5a(n) + g(n)`, because the
    only excluded partition is `{n}`.
  - **C** (`d₁ > 1` distinguished among the class-1 factors): `Σ_π k(π) w(π)`, where `k(π)` is the
    number of class-1 blocks.

So the second sum is `T_5a + T_5b` (A), `T_5a + g(n) + T_5b` (B), or `Σ k w + T_5b` (C). Under
reading A, Theorem 1.2 for `n ≡ 5` says: *if `2^{−ρ(n)}𝓛(n)` is even, then `T_5a(n)` and `T_5b(n)`
are both even.* That contains the form used (tyz-5b Proposition 1.1, here Proposition N). The final
sentence of Theorem 1.2 ("all `d_i > 1`") selects B or C. Theorem 3.5(2) has no such sentence and
so permits A. The proof of Proposition 3.4 requires A (L2077).

### 1.4 Readings B and C are false (VERIFIED, exact computation)

Take `n = 26565 = 3·5·7·11·23` and `n = 33117 = 3·7·19·83`. Both are `≡ 5 (mod 8)`.

- *Rank.* PARI's `ellrank` gives rank bounds `3..3` and three points on `C_n`, for example
  `(−18515, 2592100)`, `(−13860, 2668050)`, `(31740, 3094650)` for `n = 26565`. The height
  determinants are `39.40` and `269.70`. Independently of heights, the Kummer images of the 2-torsion
  together with the three points span a 5-dimensional subspace of `(ℚ*/ℚ*²)²`. So
  `dim C_n(ℚ)/2C_n(ℚ) ≥ 5` and `rank C_n(ℚ) ≥ 3` (`scratch/nt-tyz/kummer_independence.py`).
- *Analytic rank.* If `ord_{s=1} L(C_n, s) ≤ 1`, then `rank = ord ≤ 1` by Gross–Zagier–Kolyvagin
  (manuscript Lemma 5.5; STANDARD). So `ord ≥ 2`, and `𝓛(n) = 0` by TYZ's definition (L338–344).
  Hence `2^{−ρ}𝓛(n) = 0` is even and the hypothesis of Theorem 1.2 holds.
- *Genus sums.* With `g` from PARI class groups, certified by `bnfcertify` and checked against
  Rédei's formula on every divisor: `g(n) = 1`, `T_5a = T_5b = 0`, the reading-B `(5,1)` sum `= 1`
  and the reading-C `(5,1)` sum `= 1`. So the second sum is `0` under A and `1` under B and C
  (`certify_counterexamples.py`, `out_certify.txt`).

Theorem 1.2 read as B or C is therefore false, and so is Theorem 3.5(2) read the same way. A scan
of all 32 squarefree `n ≡ 5 (mod 8)` below `52000` with at most 7 prime factors and analytic rank 3
(`literal_reading.py`; the numerical rank is used only to select candidates) finds reading A
consistent on all 32. Readings B and C fail exactly on the two values above, the only ones in the
scan with `g(n) = 1`. This matches the identity of §1.3: when `𝓛(n) = 0` and `T_5a ≡ T_5b ≡ 0`,
reading B's sum is `g(n)`. In the other direction, 30 random samples of squarefree `n ≡ 5`, `n < 3·10⁵`
(28 distinct values), were tested: every sample with `T_5a` or `T_5b` odd has analytic rank 1.
There were 24 such samples (22 distinct `n`), three of them with only `T_5b` odd
(`reading_a_check.py`).

**Consequence.** The project cannot cite the *literal* Theorem 1.2: its text is false. It can cite
reading A, which is the statement TYZ's proof gives (§4 proves it for `n ≡ 5`). Smith also read the
theorem this way (§3).

## 2. The proof of Theorem 3.5(2) for `n ≡ 5` (L2560–2600), step by step

### 2.1 The argument as written (VERIFIED by reading)

- S1. Assume `P(n) = P + t` with `P ∈ A(K_n)^−` and `t ∈ A[4]`.
- S2. `β = r_∞(−1)r₂(−2)` acts on `K_n` by `√−n ↦ −√−n` ("explicit calculation"), so
  `P(n)^β + P(n) = t^β + t`.
- S3. `t ∈ A(ℍ'_n)[4] = A(ℚ(i))` (Lemma 3.18), and `β` acts trivially on `ℚ(i)`. So
  `P(n)^β + P(n) = 2t ∈ ℤτ(1)`.
- S4. Apply `β' + 1` to Proposition 3.4 and use Lemma 3.21. This gives
  `c₁ τ((1−i)/2) + c₂ τ(1/2) ∈ 2A(ℍ'_n)^{β'+1} + ℤτ(1)`, where
  `c₁ = i^{(n−1)/2} Σ_{d₀≡5, d₁≡1,3, d_i≡1} Π_i g(d_i)` and `c₂ = Σ_{d₀≡7, d₁≡1,3, d_i≡1} Π_i g(d_i)`.
- S5. The contribution of `2A(ℍ'_n)^{β'+1}` is torsion, so it lies in `2A(ℍ'_n)_tors = 2A(ℚ(i)) =
  ℤτ(1)`.
- S6. "Thus the coefficients in both of the brackets must be even."

### 2.2 The facts the proof leaves implicit

The two facts tyz-5b names (its §1.2) are correct:

- **F1. The second bracket is `T_5b(n)`** (VERIFIED). Every class-7 term has `d₁ ≡ 3` (§1.3). The
  factor `g(d₀)` comes from Lemma 3.21(4), `Z(d₀)^{β'+1} = g(d₀)τ(1/2)`, and `ε(d₀, d₁) = ±1` for
  `(7, 3)`. This presupposes the non-ordered reading of the factors `d_i`, `i > 1`, in
  Proposition 3.4, which that statement does not say (see §2.3).
- **F2. The brackets are separately even** (VERIFIED, sharpened in §2.3).

Four more facts are used without comment:

- **F3. `β` fixes `ℚ(i)` and negates `√−n`** (VERIFIED). Let `χ` be the idele class character of a
  quadratic field. It is trivial on the principal idele `−2`, and it is unramified with
  `χ_p(−2) = 1` at the primes not dividing the discriminant. For `ℚ(i)`: `χ_∞(−1) = −1`, so
  `χ₂(−2) = −1`, and `χ(β) = χ_∞(−1)χ₂(−2) = 1`. For `K_n`, `n ≡ 5, 7 (mod 8)`: `χ₂(−2) =
  −Π_{p|n} (−2/p) = −(−2/n) = 1`, so `χ(β) = −1`.
- **F4. `[i]` commutes with `β'`** (VERIFIED). `[i]` is defined over `ℚ(i)`, which `β'` fixes (F3).
  So `β' + 1` may be applied term by term to the `ℤ[i]`-combinations of Proposition 3.4 (the
  coefficients `ε = ±i` and the factor `i^{(n−1)/2}`).
- **F5. `ℍ'_n` is Galois over `ℚ`** (VERIFIED from Proposition 3.2(1)). S5 needs
  `x^{β'} + x ∈ A(ℍ'_n)` for `x ∈ A(ℍ'_n)`, so that Lemma 3.18 applies. Here
  `ℍ'_n = L_n(i)·Π_{d₀≡5} H'_{d₀}`. `L_n(i)` is abelian over `ℚ`. By Proposition 3.2(1), `H'_d` is the
  fixed field in the ring class field `H_{d,4}` of conductor 4 of the order-2 subgroup
  `⟨σ_{1+2ϖ}⟩`. `Gal(H_{d,4}/ℚ)` is generalized dihedral: complex conjugation inverts
  `Gal(H_{d,4}/K_d)` (STANDARD; Cox, *Primes of the form x² + ny²*, Lemma 9.3). So every subgroup of
  `Gal(H_{d,4}/K_d)` is normal in `Gal(H_{d,4}/ℚ)`, `H'_d` is Galois over `ℚ`, and so is the
  compositum.
- **F6. The "i.e." of Theorem 3.5(2)** ("`P(n) ∈ A(K_n)^− + A[4]`, i.e. `2^{−ρ(n)}𝓛(n)` is even") is
  asserted without proof. It is **not needed** for the form used, which only needs `𝓛(n) ≠ 0`. If
  `𝓛(n) = 0`, then `P(n)` represents `𝒫(n) = 0` (first assertion of Theorem 3.5), so `P(n)` is
  torsion and lies in `A[(1+i)³] ⊂ A[4]` (Lemma 3.18). That is the hypothesis of S1 with `P = 0`.

### 2.3 Is the `(7, 3)` bracket established on its own?

**The last step: yes** (VERIFIED). Write the class-5 bracket as a Gaussian integer
`C₁ = a + bi`, and let `C₂ ∈ ℤ` be the class-7 bracket (F1). With `τ(x) = 0` iff `x ∈ (1+i)ℤ[i]`, S4–S5 say
`C₁(1−i)/2 + C₂/2 ∈ ℤ + (1+i)ℤ[i] = ℤ[i]`, that is,

```
((a + b + C₂) + (b − a) i) / 2 ∈ ℤ[i]   ⟺   a ≡ b  and  C₂ ≡ 0   (mod 2).
```

So `C₂` is even whatever `C₁` is, and nothing about the `(5, 1)` bracket enters. (This is F2 in a
sharper form: tyz-5b checked the cases where `C₁` is a unit times an integer.)

**The coefficients: not as written.** `C₁` and `C₂` are read off Proposition 3.4. That
proposition is used for all classes at once, and three things about it fall short.

1. *Statement.* It does not say whether the factors are ordered, or whether `d₁ = 1` is allowed. Its
   proof needs `d₁ = 1` (L2077). With ordered factors `d_i`, `i > 1`, the class-7 coefficient would
   change (a partition with `k` class-1 blocks would be counted `k!` times).
2. *Proof structure.* It is proved by induction on `n` for all classes together (L2041–2047: "it
   suffices to prove that the above formula (applied to every `P(d₀)` below) …"). The class-7
   coefficient of `P(n)` is assembled from the coefficients of `P(d₀)` for all `d₀ ≡ 5, 7`, including
   the class-5 coefficients, which are exactly the ambiguous `(5, 1)` part.
3. *Proof detail.* The cancellation of the multiplicities (L2063–2071: "if this set is non-empty,
   the number of such partitions is even") is a one-line sketch covering both classes of `d₀`. The
   pairing of the `(5, 3)` terms (L2079–2096) is correct as stated. Both sides of
   `ε(d₀''d₁'', d₁)ε(d₀'', d₁'') = ±ε(d₀''d₁, d₁'')ε(d₀'', d₁)` contain exactly one factor of type
   `(5, 3)`, whichever class `d₀''` has (VERIFIED).

None of this shows that Proposition 3.4 is wrong. §4.3 proves its correct form for `n ≡ 5`:
`P(n) ≡ Σ_e 𝓛(n/e) Z(e)`, over `e | n` with `e ≡ 5, 7`. That form agrees with reading A. But a
citation of the `(7, 3)` bracket that goes through Proposition 3.4 inherits the ambiguity of its
statement. The proof in §4 avoids Proposition 3.4 entirely.

## 3. Published statements elsewhere

- **Smith, arXiv:1603.08479** (v1 28 Mar 2016, v2 29 Mar 2016; the two versions differ only in the
  abstract and acknowledgements; no journal reference). Theorem 2.1 (label `thm:TYZ`, cited as
  "[Theorem 1.1, 1.2]" of TYZ) reads: *"if `n` is 5, 6, or 7 mod 8, and if the row `x` agrees with `n`
  mod 8, then the analytic rank of `E^{(n)}` is exactly one if `𝓛_x(n)` is nonzero"*. Table 2 lists
  `𝓛_5a = Σ_{d≡5} g(d)𝓛(n/d)` and `𝓛_5b = Σ_{d₀≡7, d₁≡3} g(d₀)g(d₁)𝓛(n/d₀d₁)` as separate rows, and
  the introduction says "either `𝓛_5a(n)` or `𝓛_5b(n)` is nonzero". Smith's `𝓛` is defined by a
  recursion that picks the block of a fixed prime, so it is the set-partition sum `𝓛₁`. This is
  exactly reading A, with the form used stated as one row (VERIFIED, LaTeX source `cnc.tex`,
  `intro.tex`). The paper is unrefereed.
- **Tian, expository.** Y. Tian, *Congruent number problem*, Notices of the ICCM 5 (2017), no. 1,
  51–61 (DOI 10.4310/iccm.2017.v5.n1.a3), which Dalawat (arXiv:2201.11071v2, in a commented-out
  passage) calls "an expository account" of TYZ. Y. Tian, *The congruent number problem and elliptic
  curves*, Proc. ICM 2022, Vol. 3, 1990–2010 (DOI 10.4171/icm2022/85). Neither text was accessible,
  and Crossref holds no abstract for either (UNCHECKED). These are the most likely places for an
  authoritative restatement.
- **Papers citing TYZ, read in their arXiv sources.** None restates Theorem 1.2:
  Burungale–Tian, arXiv:2104.06732v2 (cites TYZ only for "more than 50% of `n ≡ 5, 6, 7` are
  congruent, cf. [TYZ, Sm1]"); Dalawat, arXiv:2201.11071v2 (only in commented-out text);
  Feng–Liu–Pan–Tian, arXiv:2405.11132 (method only); Zhang, arXiv:2111.11618 (cites "[TYZ, Theorem 1.1, Corollary 1.3]",
  journal version, for the case `s₂(n) = 0`, `n ≡ 1, 2, 3`); Guo–Ye–Yin, arXiv:2505.13133 (general citation);
  Sun, arXiv:2610.31631 (the method of TYZ §§3.1, 3.3).
- **Related papers that do not cite TYZ.** Smith, arXiv:1702.02325v2 (only an acknowledgement of
  Tian); Kriz, arXiv:2002.04767v5 (cites Yuan–Zhang–Zhang and Burungale–Tian, not TYZ); Chen,
  arXiv:2411.14188.

So the only accessible statement of the form used is Smith's unrefereed one. It agrees with
reading A.

*A warning on numbering.* Zhang cites the journal version for a statement that is Theorem 1.1 with
Corollary 1.4 in arXiv v1, but calls it "Corollary 1.3". In arXiv v1, Remark 1.3 shares the counter.
If Zhang's number is right, the journal numbering differs from arXiv v1 at least in §1 (UNCHECKED).
A citation should therefore give the arXiv version together with the label, for example "Theorem
3.5 (`m3`) of arXiv:1411.4728v1", or name the result in words.

## 4. What to cite, and a self-contained proof

### 4.1 The statement

**Proposition N.** *Let `n ≡ 5 (mod 8)` be positive and squarefree. If `𝓛(n) = 0`, then `T_5a(n)` and
`T_5b(n)` are both even. In particular, if `T_5b(n)` is odd, then `𝓛(n) ≠ 0` and
`ord_{s=1} L(E_n, s) = 1`.*

The first sentence is reading A of Theorem 3.5(2) for `n ≡ 5`, with `P(n) ∈ A[4]` in place of the
hypothesis "`P(n) ∈ A(K_n)^− + A[4]`". Only the last sentence is used for CR₃.

### 4.2 Inputs (all from TYZ, all unambiguous)

- **I1** (recursion, §3.1, L1320–1327, with the `ε`-classification of Theorem 3.3). `P(n)` is
  defined by the displayed recursion. `𝓛(d₁) ∈ ℤ`, and `ε(d₀, d₁) ≡ i (mod 2ℤ[i])` if
  `(d₀, d₁) ≡ (5, 3)` and `≡ 1` otherwise. Here `d₁ > 1` is explicit. For `d₀ | n`, `ℍ'_{d₀} ⊂ ℍ'_n`,
  so all `P(d₀)` and `Z(d₀)` lie in the `ℤ[i]`-module `A(ℍ'_n)`.
- **I2** (Lemma 2.8 and Proposition 2.3). For odd squarefree `m ≡ 1, 3 (mod 8)`:
  `Σ ε 𝓛(d₁)𝓛(d₂) = Q(m) ≡ g(m)`, over non-ordered `m = d₁d₂` with `d₂ ≡ 1`; and `𝓛(1) = 1` (L1082).
  For `m ≡ 3` the factor `d₁ ≡ 3` is distinguished by its class. For `m ≡ 1` the pairs are
  unordered (L1068–1077: the symmetry `P(d₁, d₂) = P(d₂, d₁)` of Lemma 2.7 is used to halve the sum).
- **I3** (Theorem 3.5, first assertion; proof L2343–2380). `P(n)` and `𝒫(n)` are equal in
  `A(ℍ'_n) ⊗ ℚ`, and `𝒫(n) = 0` if `𝓛(n) = 0` (L1295).
- **I4** (Lemmas 3.16, 3.18). `A(ℍ'_n)_tors = A[(1+i)³] = A(ℚ(i))` for odd `n`.
- **I5** (Lemma 3.21(1), (4)), with `β' = β'₁`.
- **I6** (Proposition 3.2(1)), for F5.
- **I7** (§1, L318–345). The definition of `𝓛(n)`, which is `0` exactly when `ord_{s=1} > 1`, and the
  root number `−1` for `n ≡ 5, 6, 7` (Birch–Stephens, quoted by TYZ; STANDARD).

### 4.3 Two lemmas (VERIFIED, proved here)

For odd squarefree `m ≡ 1` or `3 (mod 8)`, let `Λ(m) = Σ w(π)` over the partitions `π` of `m` whose
blocks all have class 1, except for exactly one block of class 3 when `m ≡ 3`. So `Λ(m) = 𝓛₁(m)` for
`m ≡ 1`, `Λ(m) = Σ_{d≡3} g(d)𝓛₁(m/d)` for `m ≡ 3`, and `Λ(1) = 1`.

**Lemma N1** (Theorem 1.1, set-partition reading). *For odd squarefree `m ≡ 1, 3 (mod 8)`,
`𝓛(m) ≡ Λ(m) (mod 2)`.*

*Proof.* Induction on `m`, using I2 modulo 2 (`ε = ±1`). The case `m = 1` is `𝓛(1) = 1`.

- *Case `m ≡ 1`.* I2 reads `𝓛(m) + Σ Λ(d₁)Λ(d₂) ≡ g(m)`, over unordered pairs `{d₁, d₂}` with
  `d₁d₂ = m` and both `> 1`. Both factors are `≡ 1`, and `Λ` is multiplicative on them in the sense
  that `Λ(d₁)Λ(d₂)` is the sum of `w(π)` over the partitions of `m` that refine `{d₁, d₂}`. A
  partition `π` with `b` blocks arises from exactly `2^{b−1} − 1` unordered pairs: the unordered
  splittings of its blocks into two nonempty groups. That number is `0` for `b = 1` and odd for
  `b ≥ 2`. So `𝓛(m) ≡ g(m) + Σ_{π, b≥2} w(π) = Λ(m)`, since the one-block partition has weight `g(m)`.
- *Case `m ≡ 3`.* The pairs are `(d₁, d₂)` with `d₁ ≡ 3` and `d₂ ≡ 1`, `d₂ > 1`. A partition `π`
  with one class-3 block and a set `S` of class-1 blocks arises `2^{|S|} − 1` times: choose a
  nonempty subset of `S` for `d₂`. Hence `𝓛(m) ≡ g(m) + Σ_{|S|≥1} w(π) = Λ(m)`. ∎

So "non-ordered" in Theorem 1.1 means set partitions, also for `m ≡ 1`, where every factor has the
same class. A reading with `d₀` distinguished would give `Σ b(π)w(π)`, and this violates I2 already
for partitions with two blocks.

**Lemma N2** (coefficients of the genus point). *Let `n ≡ 5 (mod 8)` be squarefree. Then
`P(n) = Σ_e c_n(e) Z(e)` over the divisors `e | n` with `e ≡ 5, 7 (mod 8)`, with `c_n(e) ∈ ℤ[i]` and*

```
c_n(e) ≡ Λ(n/e) ≡ 𝓛(n/e)   (mod 2ℤ[i]).
```

*Proof.* Unwinding the recursion I1 gives `P(n) = Σ_e c_n(e) Z(e)` with

```
c_n(e) = Σ_{chains}  Π_{j=0}^{k−1} ( −ε(D_{j+1}, q_j) 𝓛(q_j) ),
```

summed over the chains `n = D₀ > D₁ > ⋯ > D_k = e` (`k ≥ 0`) of divisors with every `D_j ≡ 5, 7`,
where `q_j = D_j/D_{j+1} > 1`. Since `D_j/D_{j+1} = q_j` and the classes `D_j` lie in `{5, 7}`, the
quotients have class `q_j ≡ 1, 3`, and every ordered factorization `n/e = q₀q₁⋯q_{k−1}` into factors
`> 1` of classes 1 and 3 is a chain. A class-3 factor switches the class of `D` between 5 and 7, and a
class-1 factor keeps it. By I1, a step has `ε ≡ i` exactly when it goes from class 7 to class 5.
Starting from `D₀ ≡ 5`, these are the 2nd, 4th, … class-3 factors. So, modulo 2,

```
c_n(e) ≡ Σ_{(q₀, …, q_{k−1})}  i^{⌊s/2⌋} Π_j 𝓛(q_j),     s = number of class-3 factors q_j.
```

Now replace each `𝓛(q_j)` by `Λ(q_j)` (Lemma N1) and expand. A term of the expansion is an ordered
factorization together with a partition of each `q_j` (one class-3 block if `q_j ≡ 3`, none if
`q_j ≡ 1`). Equivalently, it is a partition `π` of `n/e` into blocks of classes 1 and 3, together with
an ordered set partition `(G₀, …, G_{k−1})` of the blocks of `π` into nonempty groups, each group
containing at most one class-3 block. Its weight is `i^{⌊s/2⌋} w(π)`, where `s` is the number of
class-3 blocks of `π`. This depends only on `π`. So

```
c_n(e) ≡ Σ_π  i^{⌊s(π)/2⌋} w(π) N(π),    N(π) = number of admissible ordered groupings.
```

- If `s(π) ≥ 2`, exchange the groups of the two class-3 blocks with the smallest labels. They lie in
  different groups, so this is a fixed-point-free involution on the admissible groupings, and
  `N(π)` is even.
- If `s(π) ≤ 1`, every ordered set partition of the `b` blocks is admissible, so `N(π) = a(b)`, the
  Fubini number (`a(0) = 1`). All Fubini numbers are odd: `a(b) = Σ_{j=1}^{b} C(b, j) a(b − j) ≡
  Σ_{j=1}^{b} C(b, j) = 2^b − 1` for `b ≥ 1`, by induction.

The parity of `s(π)` is fixed by the class of `n/e`. For `e ≡ 7` we have `n/e ≡ 3`, so `s` is odd and
only `s = 1` survives. For `e ≡ 5` we have `n/e ≡ 1`, so `s` is even and only `s = 0` survives. In
both cases the surviving `π` are exactly those counted by `Λ(n/e)`, and the factor `i^{⌊s/2⌋}` is 1.
Hence `c_n(e) ≡ Λ(n/e)`. (For `e = n` the only chain is the empty one, and `c_n(n) = 1 = Λ(1)`.) ∎

In particular the coefficient of `Z(e)` is real modulo 2 for both classes. TYZ's factor
`i^{(n−1)/2}` equals `±1` for `n ≡ 5`, and tyz-5b's remark that the terms with an even number of
extra class-3 factors cancel is proved here.

*Check.* `coeff_check.py` computes `c_n(e)` in `ℤ[i]/2` directly from the recursion, on abstract data
(random classes and a random function `g` on subsets, `r = 2, …, 9` primes, 400 trials). It finds
`c_n(e) = Λ(n/e)` for every `e ≡ 7` and every `e ≡ 5`, with no value outside `{0, 1}`. It also finds
`C₂ = T_5b` and `C₁ = T_5a` in all 400 trials (`out_coeff_check.txt`).
