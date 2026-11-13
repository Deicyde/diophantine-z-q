# rv-prop-n: second review of Proposition N (nt-tyz §4) and of F1, F2 (nt-tyz §2.2)

Scope: `docs/research/nt-tyz.md` §4 (statement 4.1, inputs I1–I7 as quoted in 4.2, Lemmas N1 and N2 in
4.3, proof 4.4) and the implicit facts F1, F2 of §2.2, against the Lean forms `CertifiedRankTYZRk` and
`CertifiedRankTYZClRk` (`ZInQKernel/RouteK/Rank/Statements.lean`). This review was written before reading
`docs/research/rv-nt-tyz.md`; §7 compares the two. Scripts and outputs: `scratch/rv-prop-n/`; log:
`scratch/rv-prop-n/log.md`.

Marks: **VERIFIED** (exact derivation here, or exact/PARI computation with a script), **STANDARD**
(published theorem, with reference), **SPECULATIVE**. A claim marked *quoted* rests on nt-tyz's
quotation of the TYZ source `Period7.tex`, which is not available on this host; this review could not
compare it with the source.

> **Locator correction (2026-11-12, loc-adopt).** The convolution lemma of input I2 (TYZ L1062–1066),
> called "Lemma 2.8" when this review was written, is printed as **Lemma 2.9**; Lemma 2.8 is the
> symmetry lemma (`lem2.6`). VERIFIED for arXiv v1 by recounting the shared §2 counter of
> `Period7.tex` (nt-tyz's count skipped Definition 2.7, L842); the journal has the same numbers per
> the locator audit `docs/research/locators.md` (AI agents, 2026-11-12). Numbers are corrected in
> place. The same audit read the journal text: arXiv Theorem 1.2 is journal **Theorem 1.4**, and it
> keeps "all `d_i > 1`", so the values refuting reading B refute journal Theorem 1.4 too. No
> mathematical content of this review changed.

## Verdict

**Proposition N holds as stated, relative to the inputs I1–I7 as quoted.** Every inference of §§4.3–4.4
follows from those inputs (VERIFIED by hand and by an independent abstract computation). No repair of
the mathematics is needed. Three presentational corrections are listed in §6 (F4 is not used in §4.4;
the single lifting `β'` should be said to serve all divisors at once; I1's inclusion `ℍ'_{d₀} ⊂ ℍ'_n`
is part of the quotation, not proved). The conclusion "`T_5b(n)` odd ⟹ `ord_{s=1} L(C_n, s) = 1`" is
exactly the analytic input that `CertifiedRankTYZClRk` and, via Rédei's formula (proved in Lean),
`CertifiedRankTYZRk` need; their remaining step "analytic rank one ⟹ a point of infinite order" is
Gross–Zagier and lies outside Proposition N.

Numerically, 51 inputs (two runs of ≤ 30) found no counterexample: 22 values of analytic rank 3 (with up
to 7 prime factors, most with primes of classes 3 and 7) all have `T_5a = T_5b = 0`, and all 15 values
with `T_5b` odd and all 4 with only `T_5a` odd have analytic rank 1 (VERIFIED, PARI; §5).

**Most serious residual issue.** Not a gap in the argument but its basis: the whole proof is only as good
as the quotations of I1, I3 and I5 (the recursion of §3.1 with its coefficient `𝓛(d₁)` and its
`ε`-classes; Theorem 3.5's first assertion; Lemma 3.21(1), (4)). These were compared with the TYZ source
once (rv-nt-tyz), and not by this review. The numerical data give indirect support for the two features
of I1 the proof is sensitive to (§4.3, §5.3).

## 1. The statement used, and what Lean asks for

- Proposition N (nt-tyz §4.1): for squarefree `n ≡ 5 (mod 8)`, `𝓛(n) = 0 ⟹ T_5a(n) ≡ T_5b(n) ≡ 0`;
  hence `T_5b(n)` odd ⟹ `𝓛(n) ≠ 0` ⟹ `ord_{s=1} L(E_n, s) = 1`.
- `E_n : ny² = x³ − x` is ℚ-isomorphic to `C_n : y² = x³ − n²x` by `(x, y) ↦ (nx, n²y)`, so the
  `L`-functions agree (VERIFIED). Lean's curve is `shortCurve (−d²)`, i.e. `C_d`.
- `CertifiedRankTYZClRk`: `d % 8 = 5`, `Squarefree d`, `T5bCl d = 1` ⟹ `C_d(ℚ)` has a point of infinite
  order. `T5bCl d` is the sum over set partitions of the primes of `d` with exactly one block `≡ 7`,
  exactly one block `≡ 3` and all other blocks `≡ 1 (mod 8)` of `Π_B #(Cl(𝓞_{ℚ(√−d_B)})²)` mod 2
  (`Admissible5bNat`, `gCl`). This is Proposition N's `T_5b(d) = Σ_{d₀≡7, d₁≡3} g(d₀)g(d₁)𝓛₁(d/d₀d₁)`
  with TYZ's `g(m) = #2Cl(ℚ(√−m))` (the subgroup of squares of the class group of the maximal order):
  the blocks `d₀, d₁` are the unique blocks of classes 7 and 3, and `𝓛₁` is the sum over the set
  partitions of the rest into class-1 blocks (VERIFIED by reading the definitions). The parity of
  `#Cl²` is 1 iff the 2-part of `Cl` is elementary abelian, which is what `tyzlib.gCl` computes.
- `CertifiedRankTYZRk` is the same with Rédei's bits `gBit` in place of `gCl`; `RedeiFormula` (proved in
  Lean) identifies them on exactly the blocks read by `T5b`. The two `g`'s agreed on every block of all
  51 samples (VERIFIED, `tyzlib.redei_g` reimplements `Sec3.redeiG`).
- So Proposition N's last sentence plus "analytic rank one ⟹ rank ≥ 1" (Gross–Zagier; pc-audit RK7;
  STANDARD, outside this review) is exactly the content of both Lean hypotheses. The Lean forms ask for
  less than Proposition N gives (no `T_5a`, no `rank = 1`).

## 2. The inputs I1–I7 (internal consistency and what the proof uses)

- **I1** (recursion with `ε`-classes). Used in N2 only modulo `2ℤ[i]`. The `ε`-information actually
  used is: `ε(d₀, d₁) ≡ 1` for `(d₀, d₁) ≡ (5, 1), (7, 1), (7, 3)`. The value at `(5, 3)` is irrelevant
  (§4.3). Consistency with Theorem 3.3: Theorem 3.3 writes `P_χ = ε 2^{h₂(n)} 𝓛(d₁)𝒫(d₀)`, the
  recursion `ε 𝓛(d₁) P(d₀)` without `2^{h₂}`. This is consistent if `Z(n)`, a sum over the
  representatives `Φ₀` of `2Cl` rather than of `Cl`, is `2^{−h₂(n)}Σ_χ P_χ`; then the recursion is the
  inductive form of Theorem 3.5's first assertion. *Quoted*; consistent (SPECULATIVE as to TYZ's exact
  normalization, which this review cannot read).
- **I2** (Lemma 2.9 with Proposition 2.3). Used **only modulo 2**, in N1: the signs `ε = ±1`, the
  equality `Σ = Q(m)` and `Q(m) ≡ g(m)` enter only through their reduction mod 2. The abstract check
  (§3) models I2 as a congruence only (random signs and random even errors in both `Q(m)` and `𝓛(m)`)
  and N1 still holds in every trial. So a failure of Lemma 2.9 as an equality (for example at `m = 3`)
  does not affect Proposition N, provided the congruence holds (VERIFIED, as a statement about the
  proof). What N1 does need is that the decompositions in Lemma 2.9 for `m ≡ 1` are **unordered**: with
  ordered pairs, `𝓛(m)𝓛(1)` would appear twice and the induction would give no information on
  `𝓛(m)`. That is part of the quotation (L1068–1077).
- **I3** (Theorem 3.5, first assertion): `𝓛(n) = 0 ⟹ P(n)` torsion. Used once. *Quoted.*
- **I4** (Lemmas 3.16, 3.18). PARI: `A : 2y² = x³ + x ≅ Y² = X³ + 4X` (conductor 32) has `A(ℚ) ≅ ℤ/4`,
  `A(ℚ(i)) ≅ ℤ/4 × ℤ/2` (order 8 `= #ℤ[i]/(1+i)³`), `A(ℚ(√2)) = A(ℚ(√−2)) ≅ ℤ/4` and
  `A(ℚ(ζ₈)) ≅ (ℤ/4)²` (VERIFIED, `torsion_A.py`). This confirms Lemma 3.16. Lemma 3.18 (`A(ℍ'_n)_tors =
  A[(1+i)³]`) is *quoted*; it requires `√2 ∉ ℍ'_n`, which is why TYZ pass from the ring class field
  `H_{d,4}` (whose genus field contains `ℚ(i, √2)`) to its subfield `H'_d`.
- **I5** (Lemma 3.21(1), (4)). Used with integer coefficients `ℓ_e ∈ {0, 1}` only. `τ((1−i)/2)` has order
  2 and is not in `ℤτ(1)`; `τ(1/2)` has order 4 with `2τ(1/2) = τ(1)` (VERIFIED by hand from
  `A(ℂ) = ℂ/(1+i)ℤ[i]`). So the relation is sensitive to `a mod 2` and to `N mod 2` separately, as the
  proof requires; whether `g(e)` in I5 means the bit or the integer `#2Cl` does not matter.
- **I6** (Proposition 3.2(1)), for F5. F5's argument is correct: `Gal(H_{d,4}/ℚ) ≅ Pic(𝒪₄) ⋊ ⟨c⟩` with
  `c` acting by inversion (STANDARD; Cox, *Primes of the form x² + ny²*, Lemma 9.3), so every subgroup of
  `Pic(𝒪₄)` is normal, `H'_d/ℚ` is Galois, and so is the compositum `ℍ'_n` (VERIFIED, given I6).
- **I7.** Root number of `C_n` is `−1` for `n ≡ 5, 6, 7 (mod 8)` (STANDARD; Birch–Stephens 1966). The
  property "`𝓛(n) ≠ 0 ⟹ ord_{s=1} ≤ 1`" of TYZ's definition is *quoted*. With the root number it gives
  `ord = 1`.

F3 (β fixes `ℚ(i)`, negates `√−n`): re-derived from the product formula for the quadratic characters:
`χ(β) = χ_∞(−1)χ₂(−2) = Π_{p | D odd} (−2/p)` (the unramified places contribute 1). For `ℚ(i)` the
product is empty, so `χ(β) = 1`; for `K_n`, it is the Jacobi symbol `(−2/n) = −1` for `n ≡ 5` (and
`n ≡ 7`) mod 8 (VERIFIED).

## 3. Lemma N1 (VERIFIED)

Re-derived by hand. For `m ≡ 1`: the I2-sum is `𝓛(m)𝓛(1)` plus the unordered pairs `{d₁, d₂}`,
`d₁d₂ = m`, both `> 1` (both automatically `≡ 1`). A set partition with `b ≥ 2` class-1 blocks refines
exactly `2^{b−1} − 1` such pairs (odd); the one-block partition refines none and has weight `g(m)`.
So `𝓛(m) ≡ g(m) + Σ_{b≥2} w(π) = Λ(m)`. For `m ≡ 3`: `d₁ ≡ 3` is the class-3 factor, `d₂ ≡ 1`; a partition
with one class-3 block and a set `S` of class-1 blocks arises `2^{|S|} − 1` times. Correct. Partitions of
`m ≡ 3` with three or more class-3 blocks are correctly excluded from `Λ` (they never occur as
`Λ(d₁)Λ(d₂)`). The m = 1 base case uses `𝓛(1) = 1` (*quoted*, L1082) and `g(1) = 1`
(`ℚ(i)` has class number 1).

Independent check (`abstract_check.py`, own code, not nt-tyz's): abstract primes with random classes,
random `g` on subsets, `𝓛` defined from I2 used only mod 2 (random signs, random even errors). 453 trials
with 1 to 9 primes: `𝓛 ≡ Λ` on every divisor of class 1 or 3. The distinguished-`d₀` reading
`Σ b(π)w(π)` differs from `Λ` in 184 of the trials, so the test discriminates.

## 4. Lemma N2 and the proof of §4.4

### 4.1 Lemma N2 (VERIFIED)

Re-derived by hand.

- Unwinding: a chain `n = D₀ > ⋯ > D_k = e` with `D_j ≡ 5, 7` has quotients `q_j ≡ 1, 3` (a quotient of
  class 5 or 7 would give `D_{j+1} ≡ 1, 3`, excluded by the recursion), and conversely every ordered
  factorization of `n/e` into factors `> 1` of classes 1, 3 is a chain, since `D_{j+1} ≡ D_j q_j` and
  `{5, 7}` is stable under multiplication by `{1, 3}` mod 8. The step from class 7 to class 5 is the
  pair `(d₀, d₁) = (D_{j+1}, q_j) ≡ (5, 3)`; from class 5 to 7 it is `(7, 3)`. Starting at class 5,
  the class-3 steps alternate, so `⌊s/2⌋` of them are `(5, 3)`-steps.
- Expansion: replacing `𝓛(q_j)` by `Λ(q_j)` gives pairs (partition `π` of `n/e` into blocks of classes 1
  and 3; ordered grouping of its blocks with at most one class-3 block per group). Groups with two or
  more class-3 blocks are correctly excluded (they are not counted by `Λ(q_j)`). The weight
  `i^{⌊s/2⌋}w(π)` depends only on `π`. **This uses that every class-1 step and every `(7, 3)` step has
  `ε ≡ 1`**: otherwise the weight would depend on the order of the groups.
- `s ≥ 2`: exchanging the groups of the two lowest class-3 blocks is a fixed-point-free involution, so
  `N(π)` is even whatever the weight. `s ≤ 1`: `N(π)` is the Fubini number `a(b)`, odd by the stated
  induction (`a(b) ≡ 2^b − 1` for `b ≥ 1`).
- Class of `n/e` fixes the parity of `s`, so the survivors are exactly the partitions counted by
  `Λ(n/e)`, with weight 1.

Independent check (same script): `c_n(e)` computed exactly in `ℤ[i]` from the recursion with random
units `ε` (±i at `(5, 3)`, ±1 elsewhere) and random integer lifts of `𝓛(q)`. In 453 trials (1–9 primes):
`c_n(e) ≡ Λ(n/e)` with imaginary part `≡ 0` for every `e ≡ 5, 7`, and `a ≡ T_5a`, `N ≡ T_5b` with
`T_5a, T_5b` computed directly as set-partition sums.

### 4.2 The proof of §4.4 (VERIFIED, given I1–I7)

Each step checked:

1. `𝓛(n) = 0` ⟹ `P(n)` torsion (I3) ⟹ `P(n) ∈ A[(1+i)³] = A(ℚ(i))` (I4) ⟹ `P(n)^{β'} = P(n)` (F3, and `A`
   is defined over ℚ) ⟹ `P(n)^{β'} + P(n) = 2P(n) ∈ 2A[(1+i)³] = A[1+i] = ℤτ(1)` (the module is cyclic,
   `ℤ[i]/(1+i)³`).
2. `P(n) = Σ ℓ_e Z(e) + 2X` with `X ∈ A(ℍ'_n)`: needs `(c_n(e) − ℓ_e)/2 ∈ ℤ[i]` (N2) and `[i]` defined
   over `ℚ(i) ⊂ ℍ'_n`.
3. `P(n)^{β'} + P(n) = Σ ℓ_e Z(e)^{β'+1} + 2(X^{β'} + X)`: uses only that `β'` acts additively. Since
   `ℓ_e ∈ ℤ`, **F4 is not needed here**; the `ℤ[i]`-coefficients are inside `X`.
4. I5 for each `e` (including `e = n`, `ℓ_n = 1`): one `β' ∈ Gal(ℍ'_n/ℚ)` restricts on each `ℍ'_e` to a
   lifting of `β₁`, and Lemma 3.21 holds for any lifting. nt-tyz does not say this; it should.
5. `X^{β'} + X` is torsion and lies in `A(ℍ'_n)` (F5), hence in `A[(1+i)³]` (I4); so
   `2(X^{β'} + X) ∈ ℤτ(1)`.
6. `a(1−i)/2 + N/2 ∈ ℤ + (1+i)ℤ[i] = ℤ[i]` ⟹ `a` and `N` even. The parities: `a ≡ Σ_{e≡5} g(e)Λ(n/e) =
   T_5a(n)`, `N ≡ Σ_{e≡7} g(e)Λ(n/e) = Σ_{e≡7, d≡3} g(e)g(d)𝓛₁(n/ed) = T_5b(n)` (VERIFIED).
7. Contrapositive and I7 give `ord = 1`.

The proof uses neither Proposition 3.4 nor Theorem 1.2 nor the "i.e." of Theorem 3.5(2).

### 4.3 Sensitivity to the `ε`-classes (VERIFIED, `abstract_eps_variants.py`)

Replacing the set of class pairs where `ε ≡ i`: `{(5,3)}` (TYZ) and `∅` give 0 mismatches in 420 trials;
`{(7,3)}`, `{(5,3), (7,3)}`, `{(5,1)}`, `{(7,1)}` give 1929, 1929, 3007, 1100 mismatched coefficients.
So the argument depends on Theorem 3.3's "`ε = ±1` otherwise" and not at all on its "`ε = ±i` at
`(5, 3)`". This narrows what a future comparison with the source has to confirm.

## 5. Numerical tests (VERIFIED, PARI; ≤ 30 inputs per run, sequential)

### 5.1 Method

`g(d)` from `quadclassunit` on the field discriminant (`−d` or `−4d`): `g = 1` iff every cyclic factor of
`Cl` has 2-adic valuation ≤ 1. Class groups are GRH-conditional in PARI, but every value was matched by
Rédei's formula (`tyzlib.redei_g`, the Lean `redeiG`), which is unconditional. `T_5a, T_5b` as
set-partition sums. Analytic rank by `ellanalyticrank` on `y² = x³ − n²x` (numerical; the odd parity is
forced by the root number). Samples were selected without looking at the genus sums where the point was
to test the contrapositive (selection by PARI's 2-descent bound `ellrank ≥ 3`), and by genus sums where
the point was to test the forward direction.

### 5.2 Results

| run | inputs | analytic rank 3 | with `T_5b` odd | with only `T_5a` odd | violations |
|---|---|---|---|---|---|
| 1 (`out_run1.txt`) | 30 | 7, all `T_5a = T_5b = 0` | 12, all rank 1 | 3, all rank 1 | 0 |
| 2 (`out_run2.txt`) | 21 | 15, all `T_5a = T_5b = 0` | 3, all rank 1 | 1, rank 1 | 0 |

Stress cases: rank 3 with 6–7 primes and primes of both classes 3 and 7 (`1582581 = 3·7·11·13·17·31`,
`1915485`, `2225685`, `2379405`, `2422245`, `13498485 = 3·5·7·11·13·29·31`; `2817661 = 7·11·23·37·43`,
`134805 = 3·5·11·19·43` with four class-3 primes); `T_5b` odd with 7 primes (`4849845 = 3·5·7·11·13·17·19`,
`12777765`, `10975965`), all analytic rank 1. Two values with 2-Selmer bound 3 but analytic rank 1
(`1101565`, `1564437`) have `T_5a = T_5b = 0`, as they must.

### 5.3 What the numbers say about the inputs

Of the 22 rank-3 values, 7 have `g(n) = 1` (`134805, 26565, 141141, 887565, 2379405, 2422245, 13498485`;
`out_alt.txt`). This (a) refutes reading B of Theorem 1.2 on six values beyond nt-tyz's two, and (b)
refutes any variant of I1 in which the coefficient of `P(d₀)` is an even multiple of `𝓛(d₁)`: such a
recursion would give `c_n(e) ≡ 0` for `e ≠ n` and the analogue of Proposition N would read
"rank ≥ 2 ⟹ `g(n)` even". This is indirect support for the quoted coefficient `𝓛(d₁)` (SPECULATIVE as a
statement about the source; VERIFIED as a computation).

## 6. F1, F2 and the list of corrections

- **F1** (the class-7 bracket is `T_5b`). Correct for the reading of Proposition 3.4 that nt-tyz states
  (non-ordered `d_i`, `i > 1`; `ε = ±1` at `(7, 3)`; `Z(d₀)^{β'+1} = g(d₀)τ(1/2)`). In the §4 proof it is
  replaced by the computation `N ≡ T_5b` of §4.2 item 6, which needs no reading of Proposition 3.4
  (VERIFIED).
- **F2** (the brackets are separately even). The `ℤ[i]` computation of nt-tyz §2.3 is correct:
  `((a + b + C₂) + (b − a)i)/2 ∈ ℤ[i] ⟺ a ≡ b, C₂ ≡ 0 (mod 2)` (VERIFIED). In §4.4 the class-5
  coefficient is an integer `a`, and the same computation gives `a ≡ N ≡ 0`.

Corrections to nt-tyz §4 (none changes the verdict):

1. §4.4 says `β' + 1` "commutes with `[i]` (F4)". F4 is not used: the coefficients applied to the
   `Z(e)` are the integers `ℓ_e`. (F4 is true, but it belongs to TYZ's own S4, not to §4.4.)
2. §4.4 should state that one `β' ∈ Gal(ℍ'_n/ℚ)` restricts to a lifting of `β₁` on each `ℍ'_e`, `e | n`,
   so that Lemma 3.21 applies to all `Z(e)` with the same `β'`.
3. I1's "for `d₀ | n`, `ℍ'_{d₀} ⊂ ℍ'_n`" is part of the quoted definition of `ℍ'_n`, not a proved
   statement; it should be marked as quoted.
4. (Clarity.) State in §4.2 which `ε`-information is used: only `ε ≡ ±1` at `(5,1), (7,1), (7,3)`.

## 7. Comparison with rv-nt-tyz (read after §§1–6 were written and committed)

**Agreement.** rv-nt-tyz reaches the same verdict on Proposition N ("proved after one minor repair")
and the same assessment of every step of §§4.3–4.4. Point by point:

| Point | rv-nt-tyz | this review |
|---|---|---|
| N1, N2, proof §4.4 | CORRECT (hand + 360 abstract configurations) | VERIFIED (hand + 453 abstract configurations, own code) |
| I2 only mod 2 | B1: at `m = 3`, Lemma 2.9 and Theorem 2.1 differ by the odd factor `w_K = 3`; repair: quote I2 as a congruence | §2: I2 enters only mod 2; the abstract model perturbs `Q(m)` and `𝓛(m)` by even errors (a factor 3 is such an error), N1 unaffected. Same conclusion; the `w_K` diagnosis is rv-nt-tyz's (it needs the source) |
| F4 unused | B2 | correction 1 |
| `ε` at `(5, 3)` irrelevant | B3, mutation at `(5,1)`, `(7,3)` | §4.3, mutation at `(5,1)`, `(7,1)`, `(7,3)`, and at all-`ε ≡ 1` |
| single `β'` for all `e` | I5 row: TYZ's `β'₁` is any lift to `Gal(ℚ̄/ℚ)` (L2495–2500) | correction 2: should be said in nt-tyz; rv-nt-tyz's source check settles it |
| `ℍ'_{d₀} ⊂ ℍ'_n` | I1 row: `ℍ'_n = L_n(i)·Π_{d₀ \| n, d₀ ≡ 5,6} H'_{d₀}` (L1320) | correction 3: marked quoted; rv-nt-tyz's quotation settles it |
| F5 | CORRECT (same argument) | VERIFIED given I6 |
| second half of F3 | not needed for Prop N | not used in §4.2 (also re-derived) |
| numerics | 30 `n < 2·10⁵`: 24 with an odd sum, all rank 1; **one** of rank 3 | 51 `n` up to `1.4·10⁷`: 19 with an odd sum, all rank 1; **22** of rank 3 (up to 7 primes), all `T_5a = T_5b = 0` |
| Lean forms | not examined | §1: `T5bCl` is Proposition N's `T_5b` with TYZ's `g`; `T5b` agrees through `RedeiFormula` and on all 51 samples |

**What this review adds.** (1) The contrapositive is now tested on 22 curves of analytic rank 3 rather than
one (in rv-nt-tyz) or nt-tyz's 32 below 52000, including many with 6–7 primes of mixed classes. (2) Six new
values refuting reading B (`134805, 141141, 887565, 2379405, 2422245, 13498485`), and the observation that
the same data refute any even-coefficient variant of the recursion (§5.3). (3) The match between Proposition
N's conclusion and the Lean statements `CertifiedRankTYZClRk`/`CertifiedRankTYZRk` (§1). (4) The `(7, 1)`
mutation, completing the list of `ε`-classes the proof depends on.

**What rv-nt-tyz has that this review cannot.** The comparison of I1–I7 with `Period7.tex` (B1 rests on
it), and the findings A1 (state reading A as a set-partition convention) and A2 (the "i.e." direction needed
for the full reading A is immediate). Neither affects Proposition N.

**Disagreements.** None.

## 8. Consequence for CR₃'s trust statement

Proposition N may be cited as CR₃'s analytic input in the form already used in `Statements.lean`
("Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as completed in nt-tyz §4,
Proposition N"). Suggested additions for the trust statement (task cr3-trust):

1. Proposition N and its Lemmas N1, N2 are repository arguments with **two independent model reviews**
   (rv-nt-tyz, rv-prop-n) and no human review.
2. Its TYZ inputs are: the recursion of §3.1, used only modulo 2 and only through "`ε = ±1` except at
   `(5, 3)`"; Lemma 2.9 with Proposition 2.3, used only modulo 2 (Lemma 2.9 is misprinted or inconsistent
   with Theorem 2.1 at `m = 3` by an odd factor, rv-nt-tyz B1); Theorem 3.5 (first assertion); Lemmas 3.16,
   3.18, 3.21(1), (4); Proposition 3.2(1). Proposition 3.4 and Theorem 1.2 are not used, and Theorem 1.2
   (journal Theorem 1.4) in its literal form is false (now eight values: 26565, 33117 and the six of §5.3).
3. The quotations were checked against the arXiv source once (rv-nt-tyz), not against the journal text.
   (2026-11-12: the AI locator audit `locators.md` compared the journal numbering and restriction, not
   the inputs' quotations.)
4. The step "analytic rank one ⟹ point of infinite order" (Gross–Zagier) is separate from Proposition N.

## 9. Next step

A human referee (or a source-holding reviewer) confirms the three sensitive quotations against TYZ:
the recursion's coefficient `ε(d₀, d₁)𝓛(d₁)` with `ε = ±1` at `(5,1), (7,1), (7,3)`; Lemma 3.21(1), (4);
Theorem 3.5's first assertion. Everything else in Proposition N is elementary and has been checked twice.
