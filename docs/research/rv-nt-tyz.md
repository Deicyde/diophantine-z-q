# Referee report on nt-tyz: the Tian–Yuan–Zhang citation behind CR₃

This report examines the three claims of `docs/research/nt-tyz.md`:

- (a) Theorem 1.2 of Tian–Yuan–Zhang (TYZ, arXiv:1411.4728v1; journal Theorem 1.4), read literally (all `d_i > 1`), is
  false, with counterexamples `n = 26565` and `n = 33117`;
- (b) Proposition N (if `n ≡ 5 (mod 8)` is squarefree and `T_5b(n)` is odd, then `𝓛(n) ≠ 0` and
  `ord_{s=1} L(E_n, s) = 1`) follows from the inputs I1–I7, without TYZ's Proposition 3.4;
- (c) Kriz's preprint is not needed for any `d` covered by CR₃.

Everything below was checked against the TeX source of arXiv:1411.4728v1 (`Period7.tex`, 3357 lines;
the e-print was downloaded again and has the SHA-256 checksum recorded in nt-tyz), re-derived by hand,
or recomputed with code written for this review. Line numbers `Lnnnn` refer to `Period7.tex`. The
notation is that of nt-tyz: `g(d) = #2Cl(ℚ(√−d)) mod 2`, `w(π) = Π_{B∈π} g(B)` for a set partition
`π` of the primes of an odd squarefree number, `𝓛₁`, `Λ`, `T_5a`, `T_5b` as defined there.

Each step examined is marked **CORRECT** (checked here), **GAP** (missing or wrong, with a repair), or
**UNCHECKED** (not examined here).

> **Locator correction (2026-11-12, loc-adopt).** The convolution lemma of input I2 (L1062–1077),
> called "Lemma 2.8" when this report was written, is printed as **Lemma 2.9**; the symmetry lemma
> (`lem2.6`, L1009), called "Lemma 2.7", is **Lemma 2.8**. VERIFIED for arXiv v1 by recounting the
> shared §2 counter of `Period7.tex` (nt-tyz's count skipped Definition 2.7, L842); the journal has
> the same numbers per the locator audit `docs/research/locators.md` (AI agents, 2026-11-12).
> Numbers are corrected in place. The same audit read the author-hosted typeset journal text
> (Asian J. Math. 21 (2017)): arXiv Theorem 1.2 is journal **Theorem 1.4**, which keeps "all
> `d_i > 1`", so claim (a) applies to the journal statement too (per the audit; not re-read here).
> Line numbers are unchanged; no finding of this report changed.

## Verdict

- **(a) Proved.** Both counterexamples are correct. The factorizations, the 46 class-group
  parities, the genus sums under each reading, and an exact lower bound `rank C_n(ℚ) ≥ 3` were all
  recomputed independently. With the root number `−1` and Gross–Zagier–Kolyvagin this forces
  `𝓛(n) = 0`. Readings B and C of the second sum of Theorem 1.2 then give `1`, so Theorem 1.2 is
  false under both. One clarification is needed (finding A1): "reading A" must be stated as a
  set-partition convention. Admitting `d₁ = 1` alone does not single out a true statement: the
  reading that admits `d₁ = 1` *and* counts `d₁` as a distinguished factor is refuted by the same two
  values.
- **(b) Proved after one minor repair.** Lemmas N1 and N2, the facts F3–F5, and the proof of
  Proposition N are correct. Each of the inputs I1–I7 is quoted correctly from the source, with one
  exception. At `m = 3`, TYZ's Lemma 2.9 (input I2) is inconsistent with their own Theorem 2.1 by
  the factor `w_K = 3` (finding B1). Lemma N1 uses I2 only modulo 2, and the odd factor does not
  matter there. So the repair is to quote I2 as a congruence. Two
  of the facts listed, F4 and the second half of F3, are not needed for Proposition N. The `ε`-class
  of the `(5, 3)` steps does not enter Lemma N2 at all (findings B2, B3). The deep inputs (TYZ
  Theorem 3.3, Theorem 3.5 first assertion, Lemmas 3.18 and 3.21) are taken as citations; their
  proofs were not re-verified (finding B4).
- **(c) Proved, relative to the elementary results of tyz-5b.** The deduction in nt-tyz §5.1 is
  valid and uses no step from Kriz, the Cassels–Tate pairing or Smith. It rests on Proposition 0
  (descent-alt §4.1) and on tyz-5b's Lemma 4.1, Theorem 4.3 and Theorem 3.6. Those were not re-proved
  in this review (UNCHECKED here; finding C1). But their combined conclusion, `T_5b(d) = 1` for every
  CR₃-admissible `d`, was confirmed on 50 actual curves with a 2-Selmer group computed independently.

No finding invalidates any of the three claims.

## Findings

| # | Severity | Where | Finding |
|---|----------|-------|---------|
| A1 | minor | nt-tyz Verdict 2, §1.3 | "The only true reading admits the trivial factor `d₁ = 1`" is imprecise. A fourth literal reading D (admit `d₁ = 1`, and count `d₁` as a distinguished factor) gives the second sum `T_5a + Σ_π k(π)w(π) + T_5b`, which is also `1` for both counterexamples. The surviving reading is the set-partition reading: each set partition of the primes of `n` is counted once. |
| A2 | minor | nt-tyz §1.3, §2.2 F6 | nt-tyz calls the "i.e." of Theorem 3.5(2) unproved (F6). The direction that Theorem 1.2 needs (`2^{−ρ(n)}𝓛(n)` even ⟹ `P(n) ∈ A(K_n)^− + A[4]`) is immediate from Theorem 3.5 (first assertion) and Lemma 3.18 (§4.5 below). So reading A of Theorem 1.2 for `n ≡ 5` is *fully* proved by the argument of nt-tyz §4.4, not only Proposition N. For `n ≡ 7`, only the coefficient lemma was checked (§3.4). For `n ≡ 6`, nothing was checked. |
| B1 | minor | nt-tyz §4.2, I2 | At `m = 3`, where `w_K = 3`, TYZ's Lemma 2.9 (`Σ ε𝓛(d₁)𝓛(d₂) = Q(m)`) is inconsistent with their Theorem 2.1. Theorem 2.1 and the character formula give `Q(3) = P(3, 1) = ±3𝓛(3)`, Lemma 2.9 gives `Q(3) = ±𝓛(3)`, and `𝓛(3) = ±1`. If Theorem 2.1 is right, the correct identity is `w_K Σ ε𝓛𝓛 = Q(m)`. Either way the discrepancy is an odd factor, so the congruence modulo 2, which is all Lemma N1 needs, holds. |
| B2 | remark | nt-tyz §4.4, §2.2 F3, F4 | F4 (`[i]` commutes with `β'`) is not used by the proof of Proposition N: the coefficients `ℓ_e` are integers, and `X` enters only through `X^{β'} + X ∈ A(ℍ'_n)` (F5). The second half of F3 (`β` negates `√−n`) is not used either. It is needed only for the full Theorem 3.5(2) (finding A2). |
| B3 | remark | nt-tyz §4.3, I1 | The value of `ε` on `(5, 3)` steps does not enter Lemma N2: such steps occur only in chains with at least two class-3 factors, and these cancel in pairs. Mutation tests confirm this (§3.3). So I1 is needed only for the pairs `(5, 1)`, `(7, 1)`, `(7, 3)`, where `ε ≡ 1`. |
| B4 | scope | inputs I3–I6 | TYZ's Theorem 3.3 (generalized Gross–Zagier), the first assertion of Theorem 3.5, Lemma 3.18 (notably its Step 3, `√2 ∉ ℍ'_n`) and Lemma 3.21 (via Theorem 3.6) are used as citations. Their statements are unambiguous and are quoted correctly. Their proofs were read but not re-verified. |
| B5 | cosmetic | nt-tyz §1.2, §2.3 | The quotation "the contribution by `d₀ = d₀'' = n`, `d₁ = 1` is the single term `Z(n)`" is at L2076, not L2077. |
| C1 | scope | nt-tyz §5.1 | The chain uses Proposition 0 (descent-alt §4.1) and tyz-5b's Lemma 4.1, Theorem 4.3 and Theorem 3.6. These were not re-proved here. Their combined conclusion was tested on 50 actual curves with no failure (§6). |

## 1. The inputs I1–I7 against the source

| Input | Source | Check |
|-------|--------|-------|
| I1, recursion | L1320–1327 | CORRECT. `P(n) := Z(n) − Σ ε(d₀, d₁)𝓛(d₁)P(d₀)` over `n = d₀d₁`, `d₀ ≡ 5, 6, 7`, `d₁ ≡ 1, 2, 3 (8)`, `d₁ > 1` (written explicitly), with `ε` "as in Theorem GZ". `ℍ'_n = L_n(i)·Π_{d₀|n, d₀≡5,6} H'_{d₀}` (L1320), so `ℍ'_{d₀} ⊂ ℍ'_n` for `d₀ | n`, and `i ∈ ℍ'_n`. |
| I1, `ε`-classes | Thm 3.3, L1299–1311 | CORRECT. `ε(d₀, d₁) = ±i` if `(d₀, d₁) ≡ (5, 3)`, `±1` otherwise. Modulo `2ℤ[i]`, `±1 ≡ 1` and `±i ≡ i`. |
| I2 | Lemma 2.9, L1062–1077; L1082; Prop 2.3, L580–586 | CORRECT as a congruence, but see B1. For `m ≡ 1`, the pairs `{d₁, d₂}` are unordered (L1068–1077, using the symmetry of Lemma 2.8); for `m ≡ 3`, `d₁ ≡ 3` is fixed by its class. `𝓛(1) = 1` (L1082; also confirmed numerically). `Q(m) ≡ g(m)` because `f_m` takes odd values on squares. |
| I3 | Thm 3.5, L1353–1356; proof L2343–2380; L1295 | CORRECT. `P(n)` and `𝒫(n)` are equal in `A(ℍ'_n) ⊗ ℚ`; `𝒫(n) = 0` if `𝓛(n) = 0` (L1295). Since `K_n ⊂ L_n(i) ⊂ ℍ'_n`, both sides live in `A(ℍ'_n) ⊗ ℚ`. |
| I4 | Lemma 3.16, L2182–2185; Lemma 3.18, L2230–2232 | CORRECT. `A(ℚ(i)) = A[(1+i)³]`, and `A(ℍ'_n)_tors = A[(1+i)³]` for odd `n`. With `A(ℂ) = ℂ/(1+i)ℤ[i]` (L1386), `A[(1+i)³] = τ(½ℤ[i])` (L1399), `A[1+i] = ℤτ(1)`, and `2A[(1+i)³] = A[1+i]`. |
| I5 | Lemma 3.21, L2504–2525 | CORRECT. `β₁ = r_∞(−1)r₂(−2)` and `β'₁` is *any* lift to `Gal(ℚ̄/ℚ)` (L2495–2500). For `e ≡ 5`: `Z(e)^{β'+1} ∈ g(e)τ((1−i)/2) + ℤτ(1)`. For `e ≡ 7`: `Z(e)^{β'+1} = g(e)τ(1/2)`. Since `β'` is fixed independently of `e`, the lemma may be applied with one `β'` to every `Z(e)`, `e | n`. |
| I6 | Prop 3.2(1), L1253–1258 | CORRECT. For `d ≡ 5`, `H'_d(√2)` is the ring class field of conductor 4 of `K_d`, and `H'_d` is its fixed field under `σ_{1+2ϖ}`. |
| I7 | L318–345 | CORRECT. Root number `−1` for `n ≡ 5, 6, 7` (Birch–Stephens, quoted at L318–327), and `𝓛(n) = 0` exactly when `ord_{s=1} L(E_n, s) > 1` (L338–345). |

**On B1.** TYZ's Theorem 2.1 (L554–560) states `P(d₁, d₂) = ±2^{k−a}w_K 𝓛(d₁)𝓛(d₂)`. The character
formula (L997–1003, with L1068–1077) gives `Σ' P(d₁, d₂) = 2^{h₂(m)−δ}Q(m)` over non-ordered decompositions with
`d₂ ≡ 1`, where `δ = [m ≡ 1 (8)]`. For `m ≡ 3`, `h₂(m) = k − 1` and `a = 1`; for `m ≡ 1`, `h₂(m) = k` and
`δ = 1`. In both cases the powers of 2 cancel and `w_K Σ ε𝓛(d₁)𝓛(d₂) = Q(m)`. Here `w_K = 1`, except for
`m = 3`, where `ℚ(√−3)` has six roots of unity and `w_K = 3`. For `m = 3`, the only genus character is
trivial, so `Q(3) = P(3, 1) = ±3𝓛(3)𝓛(1)`. Numerically `𝓛(3)² = 1` and `𝓛(1)² = 1` (from the
definition at L338, with `L(E_n, 1)` and `Ω_{n,∞}` computed to 10 digits). So Theorem 2.1 gives
`Q(3) = ±3`, while Lemma 2.9 as printed gives `Q(3) = ±1`. The value `Q(3) = f_3(1)` was not computed
independently here, so it is not decided which of the two statements is misprinted. Since they differ
by an odd factor, the congruence `Σ ε𝓛𝓛 ≡ g(m) (mod 2)`, which is all that Lemma N1 uses, holds for
every `m ≡ 1, 3` in either case.

## 2. Lemma N1 (CORRECT)

The statement: for odd squarefree `m ≡ 1, 3 (mod 8)`, `𝓛(m) ≡ Λ(m) (mod 2)`. Re-derived as follows.
The proof is by induction on `m`, from I2 modulo 2 (where `ε ≡ 1`).

*Case `m ≡ 1`.* In I2, the pair `{1, m}` contributes `𝓛(m)`. For the pairs with both factors `> 1`
(both `≡ 1`), the induction hypothesis turns `𝓛(d₁)𝓛(d₂)` into `Λ(d₁)Λ(d₂)`. That product is the sum
of `w(π)` over the partitions `π` of `m` into class-1 blocks, each block lying inside `d₁` or inside
`d₂`. A partition with `b` blocks arises from exactly `2^{b−1} − 1` unordered pairs, one for each
splitting of its blocks into two nonempty groups. This number is `0` for `b = 1` and odd for
`b ≥ 2`. Hence `𝓛(m) ≡ g(m) + Σ_{b(π)≥2} w(π) = Λ(m)`. CORRECT.

*Case `m ≡ 3`.* The pairs are `(d₁, d₂)` with `d₁ ≡ 3` and `d₂ ≡ 1`. The pair with `d₂ = 1`
contributes `𝓛(m)`. A partition with one class-3 block and a set `S` of class-1 blocks arises
`2^{|S|} − 1` times, once for each nonempty subset of `S` whose union is `d₂`. This number is odd
exactly when `|S| ≥ 1`. Hence `𝓛(m) ≡ g(m) + Σ_{|S|≥1} w(π) = Λ(m)`. CORRECT.

The remark after the lemma is also correct: the reading of Theorem 1.1 with a distinguished `d₀`
gives `Σ b(π)w(π)`, which fails the recursion as soon as some two-block partition has
`g(d₁)g(d₂) = 1`. Lemma N1 was also confirmed numerically on every proper divisor class in the 360
configurations of §3.3: there `𝓛` is computed from the recursion of I2, not from `Λ`.

## 3. Lemma N2: the coefficients of the genus point

### 3.1 Re-derivation (CORRECT)

Let `n ≡ 5 (mod 8)` be squarefree. Unwinding I1 gives `P(n) = Σ_e c_n(e)Z(e)` over the divisors
`e ≡ 5, 7`, with `c_n(e) = Σ Π_{j<k} (−ε(D_{j+1}, q_j)𝓛(q_j))`. The sum runs over the chains
`n = D₀ > D₁ > ⋯ > D_k = e` with every `D_j ≡ 5, 7`, and `q_j = D_j/D_{j+1} > 1`. The following points
were checked one by one.

1. *Chains and ordered factorizations.* `5q` and `7q` lie in `{5, 7} (mod 8)` exactly when `q ≡ 1, 3`.
   So the chains are exactly the ordered factorizations `n/e = q₀⋯q_{k−1}` into factors `> 1` of
   classes 1 and 3. A class-3 factor switches the class of `D` between 5 and 7; a class-1 factor
   keeps it.
2. *Where `i` occurs.* The step from `D_j` to `D_{j+1}` uses `ε(D_{j+1}, q_j)`, which is `≡ i` iff
   `(D_{j+1}, q_j) ≡ (5, 3)`, that is, iff the step goes from class 7 to class 5. Starting from
   `D₀ ≡ 5`, these are the 2nd, 4th, … class-3 steps. So the unit factor is `i^{⌊s/2⌋}`, where `s` is the
   number of class-3 factors. The sign `(−1)^k` is `≡ 1`.
3. *Expansion.* Replace `𝓛(q_j)` by `Λ(q_j)` (Lemma N1; both are integers, so this is legitimate
   modulo `2ℤ[i]`) and expand. The terms correspond bijectively to pairs (a partition `π` of `n/e`
   into blocks of classes 1 and 3; an ordered set partition of the blocks of `π` into nonempty groups,
   each with at most one class-3 block). A group with one class-3 block has product `≡ 3`, a group
   without has product `≡ 1`, and `Λ(q)` enumerates exactly the partitions of `q` with that many
   class-3 blocks. The weight `i^{⌊s(π)/2⌋}w(π)` depends only on `π`.
4. *Cancellation.* If `s(π) ≥ 2`, exchanging the groups of the two class-3 blocks with the smallest
   labels is a fixed-point-free involution on the admissible groupings. The two blocks lie in
   different groups, every group still has at most one class-3 block, and the involution preserves
   the weight. So the multiplicity `N(π)` is even. If `s(π) ≤ 1`, every ordered set partition is
   admissible, and `N(π)` is the Fubini number `a(b)`, which is odd: `a(0) = 1`, and
   `a(b) = Σ_{j≥1} C(b, j)a(b − j) ≡ 2^b − 1` by induction.
5. *Parity of `s`.* The product of the blocks is `≡ 3^{s}`. So `s` is even iff `n/e ≡ 1`, iff `e ≡ 5`;
   then only `s = 0` survives. And `s` is odd iff `e ≡ 7`; then only `s = 1` survives. In both cases
   the survivors are exactly the partitions counted by `Λ(n/e)`, with unit factor `i⁰ = 1`.

Hence `c_n(e) ≡ Λ(n/e) ≡ 𝓛(n/e) (mod 2ℤ[i])`. This is real for both classes of `e`.

### 3.2 A remark (B3)

Steps of type `(5, 3)` occur only in chains with `s ≥ 2`, and all such terms cancel in point 4.
Therefore Lemma N2 holds whatever the `ε`-class of a `(5, 3)` step is. Of the `ε`-classification in
I1, only `ε ≡ 1` on `(5, 1)`, `(7, 1)` and `(7, 3)` is used. In particular, the factor `i^{(n−1)/2}` in
TYZ's display (L2586) plays no role for `n ≡ 5`.

### 3.3 Independent recomputation

`c_n(e)` was computed in `ℤ[i]/2 = 𝔽₂[i]` directly from the recursion I1, on abstract
configurations: `r` labelled primes with random classes in `{1, 3, 5, 7}` whose product is `5`, and a
random function `g` from nonempty subsets to `𝔽₂`. The values `𝓛(q)` were computed from the
recursion of I2 modulo 2, not from `Λ`, so the test covers Lemma N1 as well. They were compared with
`Λ(n/e)`, computed by direct enumeration of set partitions.

- 360 configurations, 40 for each `r = 1, …, 9`: 20 440 coefficients `c_n(e)`, no mismatch with
  `Λ(n/e)`, and no coefficient with a nonzero `i`-part. No mismatch between the recursion's `𝓛(q)`
  and `Λ(q)`. The two brackets `C₁ = Σ_{e≡5} c_n(e)g(e)` and `C₂ = Σ_{e≡7} c_n(e)g(e)` equal `T_5a` and
  `T_5b` in all 360 configurations. `T_5b` is odd in 136 of them.
- 30 actual integers `n ≡ 5 (mod 8)` below `3·10⁶` with 3 to 7 prime factors, with `g` from
  class-group computations: 152 coefficients, no mismatch.
- Mutation tests (90 configurations each). Giving `ε` the class 1 instead of `i` on `(5, 3)` steps
  still gives no mismatch, as §3.2 predicts. Giving `ε` the class `i` on `(5, 1)` steps, or on
  `(7, 3)` steps, gives 2181 and 1261 mismatches. So the test does detect errors in the parts of I1
  that matter.
- *Proposition 3.4 under a distinguished `d₁`.* If `d₁ = 1` is admitted and `d₁` is distinguished
  among the class-1 factors, the predicted coefficient of `Z(e)` for `e ≡ 5` is
  `Σ_π (1 + k(π))w(π)`. For `e ≡ 7` the prediction is `Λ(n/e)`, since there `d₁` is the class-3
  block. This disagrees with the recursion on 4876 of the coefficients above, in 265 of the 360
  configurations. Proposition 3.4 is true only with
  the set-partition convention, under which its coefficient of `Z(e)` is `Λ(n/e)`. This agrees with
  nt-tyz §2.3.

### 3.4 The case `n ≡ 7`

nt-tyz states without proof that for `n ≡ 7`, `c_n(e) ≡ iΛ(n/e)` for `e ≡ 5` and `Λ(n/e)` for `e ≡ 7`.
The same argument gives this, now starting at `D₀ ≡ 7`. The first class-3 step goes from 7 to 5 and
carries `i`. The survivors have `s = 1` for `e ≡ 5` and `s = 0` for `e ≡ 7`. The recomputation on 120
configurations with `n ≡ 7` (3825 coefficients) found no mismatch. CORRECT for the coefficient lemma.
The rest of the `n ≡ 7` case was not examined.

## 4. The facts F3–F6 and the proof of Proposition N

### 4.1 F3 (CORRECT)

Let `χ` be the idele class character of a quadratic field, and `β = r_∞(−1)r₂(−2)`. Then `β` acts on
the field by `χ(β) = χ_∞(−1)χ₂(−2)`. The normalization of the Artin map does not matter for quadratic
characters. By the product formula for the principal idele `−2`, and since `χ_p(−2) = 1` at the
unramified odd `p`, `χ₂(−2) = (χ_∞(−2)Π_{p ramified, odd} χ_p(−2))^{−1}`.

- For `ℚ(i)`: `χ_∞(−2) = −1`, so `χ₂(−2) = −1` and `χ(β) = (−1)(−1) = 1`. So `β` fixes `i`.
- For `K_n`, `n ≡ 5 (mod 8)`: at `p | n`, `χ_p(−2) = (−2/p)`, so `χ₂(−2) = −(−2/n)`. Here
  `(−1/n) = 1` and `(2/n) = −1`, so `(−2/n) = −1`, `χ₂(−2) = 1` and `χ(β) = −1`. So `β` negates `√−n`.

Proposition N uses only the first item. The second is needed for the full Theorem 3.5(2) (§4.5).

### 4.2 F4 (CORRECT, not needed)

`[i]` is defined over `ℚ(i)`, and `β'` fixes `ℚ(i)`, so `([i]x)^{β'} = [i]x^{β'}`. The proof of
Proposition N applies `β' + 1` only to `Σ ℓ_e Z(e)` with integers `ℓ_e`, and to `2X`, where it needs
only that `X^{β'} + X` lies in `A(ℍ'_n)`. So F4 is never used (B2).

### 4.3 F5 (CORRECT)

By I6, for `d ≡ 5`, `K_d ⊂ H'_d ⊂ H_{d,4}`, the ring class field of conductor 4. `Gal(H_{d,4}/ℚ)` is
the semidirect product of the abelian group `Gal(H_{d,4}/K_d)` by complex conjugation, which acts by
inversion (Cox, *Primes of the form x² + ny²*, Lemma 9.3). Every subgroup `U` of the abelian part
satisfies `cUc^{−1} = U^{−1} = U`, so it is normal. Hence `H'_d` is Galois over `ℚ`. `L_n(i)` is abelian
over `ℚ`, and a compositum of Galois extensions is Galois. So `ℍ'_n` is Galois over `ℚ`, and every lift
`β'` maps `A(ℍ'_n)` to itself. This is what the last step needs: `X ∈ A(ℍ'_n)` implies
`X^{β'} + X ∈ A(ℍ'_n)`. TYZ use the same fact without comment at L2594 ("the contribution from
`2A(ℍ'_n)^{β'+1}` is torsion, contained in `2A(ℍ'_n)_tors`").

### 4.4 Proof of Proposition N (CORRECT)

Each step was checked.

1. `𝓛(n) = 0` ⟹ `𝒫(n) = 0` ⟹ `P(n)` maps to `0` in `A(ℍ'_n) ⊗ ℚ` (I3). So `P(n)` is torsion, and
   `P(n) ∈ A[(1+i)³] = A(ℚ(i))` (I4).
2. `β'` fixes `ℚ(i)` (F3, first item), so `P(n)^{β'} + P(n) = 2P(n) ∈ 2A[(1+i)³] = A[1+i] = ℤτ(1)`.
3. By Lemma N2, `c_n(e) − ℓ_e ∈ 2ℤ[i]` with `ℓ_e ∈ {0, 1}`, `ℓ_e ≡ Λ(n/e)`. So
   `P(n) = Σ ℓ_e Z(e) + 2X` with `X ∈ A(ℍ'_n)`. This uses I1: `Z(e) ∈ A(ℍ'_n)`, a `ℤ[i]`-module.
4. Apply `β' + 1`. By I5, `Σ ℓ_e Z(e)^{β'+1} ≡ aτ((1−i)/2) + Nτ(1/2)` modulo `ℤτ(1)`, with
   `a = Σ_{e≡5} ℓ_e g(e) ≡ Σ_{e≡5} g(e)𝓛₁(n/e) = T_5a(n)` and
   `N = Σ_{e≡7} ℓ_e g(e) ≡ Σ_{e≡7} g(e)Σ_{d≡3} g(d)𝓛₁(n/ed) = T_5b(n)`.
5. Every other term is torsion, so `2(X^{β'} + X)` is torsion. Then `X^{β'} + X` is a torsion point of
   `A(ℍ'_n)` (F5), so it lies in `A[(1+i)³]` (I4), and `2(X^{β'} + X) ∈ ℤτ(1)`.
6. So `τ(a(1−i)/2 + N/2) ∈ ℤτ(1)`, that is, `a(1−i)/2 + N/2 ∈ ℤ + (1+i)ℤ[i] = ℤ[i]`. This gives
   `a ≡ 0` and `a + N ≡ 0`, hence `T_5a(n) ≡ T_5b(n) ≡ 0`.
7. Contrapositive and I7: if `T_5b(n)` is odd, then `𝓛(n) ≠ 0`, so `ord_{s=1} ≤ 1`, and the root number
   `−1` makes the order equal to 1.

The proof uses neither Proposition 3.4 nor Theorem 1.2, and no ordering convention beyond Lemma N1.
The claim of nt-tyz §4.4 ("What the proof does not use") is CORRECT.

*Differential test.* For 30 random squarefree `n ≡ 5 (mod 8)` below `2·10⁵` with at least 3 prime
factors, `T_5a(n)` and `T_5b(n)` were computed from Rédei matrices and compared with the analytic rank
of `C_n`, computed numerically. In 24 cases `T_5a` or `T_5b` is odd (in 4 of them only `T_5b`), and
all 24 have analytic rank 1. One case has analytic rank 3, with `T_5a ≡ T_5b ≡ 0`. No contradiction.

### 4.5 F6, and the full reading A for `n ≡ 5` (finding A2)

nt-tyz marks the "i.e." of Theorem 3.5(2) as unproved and avoids it. The direction that Theorem 1.2
needs is immediate. Suppose `2^{−ρ(n)}𝓛(n) = 2m` with `m ∈ ℤ`. Then `𝒫(n) = mα_n ∈ A(K_n)^−`, and
`P(n) − mα_n` is torsion in `A(ℍ'_n)` (I3), hence lies in `A[(1+i)³] ⊂ A[4]` (I4). So
`P(n) ∈ A(K_n)^− + A[4]`.

Under this hypothesis, write `P(n) = P + t`. Then `P^{β'} = −P` by F3 (second item), and
`t ∈ A(ℍ'_n)[4] = A(ℚ(i))` is fixed by `β'`, so `P(n)^{β'} + P(n) = 2t ∈ ℤτ(1)`. Steps 3–6 above then
give `T_5a ≡ T_5b ≡ 0`. So reading A of Theorem 1.2 (and of Theorem 3.5(2)) for `n ≡ 5` is fully
proved by nt-tyz's argument, not only Proposition N. The converse direction of the "i.e." is not
needed anywhere.

## 5. The counterexamples of nt-tyz §1.4 (CORRECT)

**Readings.** For `n ≡ 5`, the `(7, 3)` terms of the second sum give `T_5b(n)` under every reading,
because `d₀` and `d₁` are the unique blocks of classes 7 and 3. The `(5, 1)` terms give:

- A (set partitions, `d₁ = 1` admitted, each set partition counted once): `T_5a(n)`;
- B (all `d_i > 1`; `d₁` is one of the class-1 blocks, counted once): `Σ_{k(π)≥1} w(π) = T_5a + g(n)`;
- C (all `d_i > 1`; `d₁` distinguished among the class-1 blocks): `Σ_π k(π)w(π)`;
- D (`d₁ = 1` admitted *and* `d₁` distinguished; added here): `Σ_π (1 + k(π))w(π) = T_5a + Σ_π k(π)w(π)`.

Here `π` runs over the partitions with one class-5 block and `k(π)` class-1 blocks.

**Factorizations.** `26565 = 3·5·7·11·23` and `33117 = 3·7·19·83`, both `≡ 5 (mod 8)`. CORRECT.

**Class-group parities.** `g(d)` was computed for all 31 resp. 15 divisors `d > 1` by three methods,
which agree on every divisor. (i) `g(d) = h(D)/#Cl(D)[2]`, by enumerating the reduced forms of
discriminant `D = disc ℚ(√−d)` and the reduced ambiguous forms (`b = 0`, `b = a` or `a = c`). This is
exact and unconditional. (ii) Rédei's formula: `g(d)` is odd iff the 4-rank `t − 1 − rank_{𝔽₂} R` is `0`,
where `R` is the Rédei matrix. (iii) PARI's `quadclassunit`. Both `n` have `g(n) = 1`. CORRECT.

**Genus sums.** For both `n`: `T_5a = T_5b = 0`. Hence the second sum is `0` under A and `1` under B, C
and D. CORRECT (and reading D is refuted as well).

**Rank.** Three points on each curve `C_n : y² = x³ − n²x` were found by a search (PARI's `ellrank`,
used only to find them; they differ from those listed in nt-tyz):

- `n = 26565`: `(−8349, 2304324)`, `(−644, 673946)`, `(148764, 56455938)`;
- `n = 33117`: `(53067, 9552060)`, `(−1120791/100, 3299122323/1000)`, `(917301/25, 378261576/125)`.

Each was checked exactly to lie on the curve. The Kummer map `x ↦ (x, x − n) ∈ (ℚ*/ℚ*²)²`, corrected
at the 2-torsion points as usual, is injective on `C_n(ℚ)/2C_n(ℚ)`. The images of `(0, 0)`, `(n, 0)`
and the three points span a 5-dimensional `𝔽₂`-space; the squarefree parts were computed by exact
factorization. Since `C_n(ℚ)[2] = (ℤ/2)²`, `dim C_n(ℚ)/2C_n(ℚ) = 2 + rank`, so `rank C_n(ℚ) ≥ 3`
(exact). As a numerical cross-check, the regulators of these triples are `39.4026` and `269.7036`,
equal to those reported in nt-tyz for different points. The root number is `−1`.

**Conclusion.** If `ord_{s=1} L(C_n, s) ≤ 1`, Gross–Zagier–Kolyvagin would give rank `= ord ≤ 1`. So
`ord ≥ 2`, and in fact `ord ≥ 3` because the order is odd. By TYZ's definition (L338–345), `𝓛(n) = 0`,
so the hypothesis "`2^{−ρ(n)}𝓛(n)` is even" of Theorem 1.2 holds. Its conclusion fails under readings
B, C and D. Theorem 1.2 read literally is false. Claim (a) is proved. A rank lower bound of 2 would
already suffice.

**Finding A1.** nt-tyz says the only true reading "admits the trivial factor `d₁ = 1`". Reading D also
admits `d₁ = 1` and is false. The correct description is the set-partition convention: decompositions
are set partitions of the primes of `n`, each counted once, and `d₁` is the block of class 2 or 3 if
there is one, and `1` otherwise. With this convention, the coefficient lemma (§3) shows that
Proposition 3.4 holds, and §4.5 shows that Theorem 1.2 holds for `n ≡ 5`.

## 6. Section 5.1 of nt-tyz: Kriz is not needed

**The deduction (CORRECT).** CR₃ (`ZInQ.CertifiedRank`) assumes that `d > 0` is squarefree with
`d ≡ 5 (mod 8)`, that `a | d` is squarefree with `|a| ≡ 7 (mod 8)`, that the system `Σ(𝒞_d)` has 8
solutions, and that one solution has first coordinate the class of `a`. By Proposition 0
(descent-alt §4.1), this says `dim Sel₂(C_d) = 3` and `a ∈ π₁(Sel₂(C_d))`. Since `|a|` is odd and
`≡ 3 (mod 4)`, tyz-5b's Corollary 4.4 applies to every such `d`. Its proof goes through Theorem 4.3
(via Lemma 4.1 and the bordered-determinant Lemma 4.2), which gives `det M_5b = 1`. Theorem 3.6 then
gives `T_5b(d) = 1`. Corollary 1.2 (Proposition N, then "analytic rank one ⟹ rank ≥ 1", then pc-audit
RK9) gives the point. A class with first coordinate `a` is not torsion, since the torsion classes have
odd parts `1` and `d`, both `≡ 1 (mod 4)`. No step uses Kriz, the Cassels–Tate pairing or Smith's
preprint.

Only rank `≥ 1` is needed: `rank ≤ dim Sel₂ − 2 = 1` holds for free. So Gross–Zagier, with an
auxiliary non-vanishing twist, would suffice in place of Kolyvagin. nt-tyz §5.2 makes the same point.

**What was not re-proved (C1).** Proposition 0, Lemma 4.1, Theorem 4.3 and Theorem 3.6 of tyz-5b
are elementary but long. They are outside the scope of this review. Their combined conclusion was
tested instead.

**Test on actual curves.** The 2-Selmer group was computed by a full 2-descent written for this
review. The local images `W_v ⊂ (ℚ_v*/ℚ_v*²)²` of `C_d(ℚ_v)/2C_d(ℚ_v)`, for `v ∈ {∞, 2, p | d}`, are
generated by local points until they reach their known dimensions (1, 3 and 2). Then
`Sel₂ = {(b₁, b₂) : loc_v ∈ W_v for all v}`. This agreed with `2^{2+rank}` on nine test curves,
including both counterexamples (32 elements each).

- 30 random CR₃-admissible pairs `(d, a)` with `d < 2·10⁶` (2 to 5 primes): `T_5b(d) = 1` in all 30.
  For two of them (`d = 226733` and `d = 265341`), a generator `P` was found, and one of `P + T`,
  `T ∈ C_d[2]`, has `x/a` a square. This is the conclusion of CR₃, checked end to end.
- A separate sample of 20 admissible `d` with 4 or 5 primes: `T_5b(d) = 1` in all 20.

Claim (c) is proved as a deduction, relative to the elementary results of tyz-5b and Proposition 0,
and the tests found no exception.

## 7. Repairs

1. **(B1) Quote I2 as a congruence.** Replace "`Σ ε𝓛(d₁)𝓛(d₂) = Q(m) ≡ g(m)`" by
   "`Σ ε𝓛(d₁)𝓛(d₂) ≡ Q(m) ≡ g(m) (mod 2)` (Lemma 2.9 with Proposition 2.3; at `m = 3`, Lemma 2.9 and
   Theorem 2.1 differ by the odd factor `w_K = 3`, and the congruence holds under either)". Lemma N1 uses
   nothing more, and its proof is unchanged.
2. **(A1) State reading A as a convention on set partitions.** "Decompositions are set partitions of
   the primes of `n`, each counted once; `d₀` is the block of class 5, 6 or 7, `d₁` the block of class
   2 or 3 if there is one and `1` otherwise, and `d_i`, `i > 1`, the class-1 blocks." Also record that
   the reading with `d₁ = 1` admitted but `d₁` distinguished (reading D) is refuted by the same two
   values.
3. **(B2, B3) Optional simplifications.** In §4.4 of nt-tyz, drop the appeal to F4, and note that
   only the first half of F3 is used. In I1, note that only `ε ≡ 1` on `(5, 1)`, `(7, 1)` and `(7, 3)`
   is used. These changes shrink the list of facts a human referee must check. They change nothing
   in the logic.
4. **(A2) Optional strengthening.** Add the two-line argument of §4.5. With it, nt-tyz proves reading
   A of Theorems 1.2 and 3.5(2) for `n ≡ 5` in full, with the hypothesis "`2^{−ρ(n)}𝓛(n)` is even".
   This supports the recommendation that a correct published form exists, which Proposition N
   instantiates.
5. **(B5)** Line reference L2077 → L2076.

None of these repairs touches the citation recommended in nt-tyz §4.5 or the conclusion for CR₃.

## Computations

All computations are exact unless marked numerical. PARI/GP 2.17 was used only for factorizations,
for a third class-group cross-check, for finding points, and for the numerical items. The code is in
`scratch/rv-nt-tyz/`.

| Computation | Method | Result |
|-------------|--------|--------|
| `g(d)`, genus sums for 26565, 33117 (`counterexamples.py`, `genus.py`) | reduced forms; Rédei matrix; PARI | three methods agree on 46 divisors; `T_5a = T_5b = 0`; A = 0, B = C = D = 1 |
| rank ≥ 3 (`rank_lower.py`) | exact Kummer images of `T₁, T₂, P₁, P₂, P₃` | span of dimension 5 for both `n` |
| Lemmas N1, N2 (`coeff_recompute.py`) | recursions I1, I2 in `𝔽₂[i]` vs set-partition enumeration | 360 configurations, 20 440 coefficients, 0 mismatches; brackets = `(T_5a, T_5b)` |
| mutation tests | altered `ε`-rule | `(5, 3)` class irrelevant; `(5, 1)` / `(7, 3)` errors detected |
| N1, N2 on actual `n` (`coeff_real.py`) | `g` from reduced forms | 30 `n`, 152 coefficients, 0 mismatches |
| `n ≡ 7` coefficients (`coeff_n7.py`) | as above | 120 configurations, 3825 coefficients, 0 mismatches |
| `𝓛(1)`, `𝓛(3)` (`calL_small.py`) | numerical `L(E_n, 1)/Ω` | `𝓛(1)² = 𝓛(3)² = 1` to 10 digits |
| Proposition N vs analytic rank (`propN_diff.py`) | Rédei parities; numerical analytic rank | 30 `n`, 24 with an odd sum, all of analytic rank 1 |
| §5.1 on actual curves (`cr3_sample.py`) | own full 2-descent; Rédei parities | 30 + 20 admissible `d`, `T_5b = 1` in all; 2 end-to-end points |
