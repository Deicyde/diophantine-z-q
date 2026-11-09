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
5. **What to cite.** Proposition A below, with the proof of §4. That proof bypasses
   Proposition 3.4 entirely: it computes the coefficients of the genus point modulo 2 directly
   from the recursion that defines it (Lemma C). Its inputs are Theorem 3.5 (first assertion),
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

**Proposition A** (the statement to cite). *Let `n ≡ 5 (mod 8)` be positive and squarefree. If*
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
