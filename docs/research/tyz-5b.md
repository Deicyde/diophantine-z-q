# Route K on published theorems: Tian–Yuan–Zhang, row 5b, for the slot curves

This note decides whether the deep input of Route K (`docs/research/rs-pole.md` §4.1,
`docs/research/rv-route-k.md`, `docs/research/pc-audit.md`) can be taken from published theorems for
the curves that the slot construction of `docs/research/slot-k.md` produces.

## Verdict

**Yes.** For every admissible input, both curves `C_n` and `C_{nθ}` of the slot construction have a
rational point of infinite order whose abscissa lies in `βℚ*²`, by the following chain:

1. slot-k §2.5: `|n| ≡ |nθ| ≡ 5 (mod 8)`, both curves are Selmer-minimal (`dim Sel₂ = 3`), and `β`, with
   `|β| ≡ 7 (mod 8)`, is a first coordinate of both Selmer groups;
2. §4 below (elementary): for such a curve the determinant of row 5b of Smith's Table 2 equals 1;
3. §3 below (elementary): that determinant equals Tian–Yuan–Zhang's genus sum
   `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀)g(d₁)𝓛(n/d₀d₁)`, so this sum is odd;
4. Tian–Yuan–Zhang (Asian J. Math. 21 (2017); arXiv:1411.4728, Theorem 3.5(2) and its proof, §3.3):
   then `𝓛(n) ≠ 0`, so `L(C_n, s)` has a simple zero at `s = 1`;
5. Gross–Zagier and Kolyvagin (manuscript Lemma 5.5, `lem:forward-rank`, line 1086; audit record
   A020): `rank C_n(ℚ) = 1`;
6. pc-audit RK9: rank one and `dim Sel₂ = 3` give `C_n(ℚ)/2C_n(ℚ) = Sel₂(C_n)`, so the class `β` comes
   from a point of infinite order.

So Route K needs nothing from Kriz (arXiv:2002.04767) for these curves, and none of Smith's
unrefereed preprint (arXiv:1603.08479) either: row 5b of Smith's Theorem 2.2 is reproved here (§3)
by a different and shorter argument, and pc-audit's rule RK6 for row 5b is proved (§4). Row 6 is
never needed, because the construction always has `|n| ≡ 5 (mod 8)`.

Two reservations, neither of them mathematical gaps in this note:

- **Which statement of TYZ.** The form used is "for `n ≡ 5 (mod 8)`: if the `(7, 3)` sum is odd then
  `2^{−ρ(n)}𝓛(n)` is odd". The proof of TYZ Theorem 3.5(2) establishes exactly this (§1.2). The
  *statement* of Theorems 1.2 and 3.5(2) groups the `(7, 3)` sum with the `(5, 1)` sum; it implies
  the form used under the reading that the second sum includes `d₁ = 1` (the reading that the proof
  requires, pc-audit RK4), but not under the literal reading `d₁ > 1`. The journal version could not
  be retrieved; its statement should be compared before citing (UNCHECKED).
- **Status of the inputs from the other notes.** The chain uses slot-k's theorem (under independent
  review) and Proposition 0 of descent-alt §4.1 for `c = 5` (rechecked in slot-k §2.1).

Every claim carries one of four marks.

- **VERIFIED**: proved in this note, checked against the source text (arXiv LaTeX sources of TYZ and
  Smith), or established by an exact computation. Scripts are in `scratch/tyz-5b/`.
- **STANDARD**: a published theorem whose statement applies as used, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.
- **UNCHECKED**: a source that could not be read here.

## Notation

- `C_d : y² = x³ − d²x`, Kummer map `P ↦ (x, x − d)` into `(ℚ*/ℚ*²)²` (as in slot-k). `C_d = C_{−d}`
  and the first coordinate does not depend on the sign of `d`.
- `n > 0` odd squarefree, `n = p₁⋯p_r`, `V = {1, …, r}`. For `S ⊆ V`, `d_S = Π_{i∈S} p_i`.
- `(a/p)₊ ∈ 𝔽₂` is `0` if `a` is a nonzero square mod `p` and `1` otherwise. `a_{ij} = (p_j/p_i)₊`
  for `i ≠ j`; `y_i = (−1/p_i)₊ = [p_i ≡ 3 (mod 4)]`; `z_i = (2/p_i)₊ = [p_i ≡ ±3 (mod 8)]`. In slot-k's
  notation `a_{ij} = [p_j/p_i]`, `y = λ`, `z = μ`.
- Quadratic reciprocity (STANDARD): `a_{ij} + a_{ji} = y_iy_j` for `i ≠ j`.
- `L` (Smith's `A`) is the `r × r` matrix with `L_{ij} = a_{ij}` (`i ≠ j`) and `L_{ii} = Σ_{j≠i} a_{ij}`,
  so its rows sum to zero. For `B ⊆ V`, `L_B` is the same matrix built from the primes of `B` only (Smith's
  `A_Rows[B, B]`); `L_V = L`.
- For `S ⊆ V`: `y(S) = Σ_{i∈S} y_i`, `z(S) = Σ_{i∈S} z_i`. The class of `d_S` mod 8 is `1, 5, 7, 3` for
  `(y(S), z(S)) = (0,0), (0,1), (1,0), (1,1)`. "`S` has class `c`" means `d_S ≡ c (mod 8)`.
- `g(d) = #2Cl(ℚ(√−d)) mod 2`, so `g(d) = 1` iff the class group has no element of order 4 (TYZ §1).
  `g(S) = g(d_S)`.
- A **partition** of `S` is a set of nonempty disjoint blocks with union `S`. Since `n` is squarefree,
  an unordered factorization of `d_S` into factors `> 1` is the same as a partition of `S`.
- Smith's matrices (2r × 2r and (2r+1) × (2r+1)), over `𝔽₂`:

  ```
  M₁ = | L + Lᵀ   Lᵀ  |          M_5b = | L + Lᵀ   Lᵀ    0 |
       | L        D_z |                 | L        D_z   y |
                                        | 0        yᵀ    0 |
  ```

  where `D_z` is diagonal with entries `z_i`. By reciprocity `(L + Lᵀ)_{ij} = y_iy_j` for `i ≠ j`, and the
  diagonal of `L + Lᵀ` is 0.
- The genus sum of row 5b (Smith, Table 2; TYZ's coefficient of `τ(1/2)`, §1.2):

  ```
  T_5b(n) = Σ_π Π_{B∈π} g(B),   π over partitions of V with one block of class 7,
                                 one block of class 3, and all other blocks of class 1.
  ```

  In Smith's notation `T_5b(n) = Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀)g(d₁)𝓛(n/d₀d₁)`, where `𝓛(m)` is the sum of
  `Π g` over the partitions of the primes of `m` into blocks of class 1 (Smith's recursive definition of `𝓛` (§2, before Theorem 2.1)
  chooses the block containing a fixed prime, so it enumerates exactly these partitions; VERIFIED by
  reading Smith §2).

## 1. The theorem used

### 1.1 Tian–Yuan–Zhang (VERIFIED by reading arXiv:1411.4728v1)

**Source.** Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number
problem*, Asian J. Math. 21 (2017), no. 4, 721–774. Read in arXiv:1411.4728v1 (18 Nov 2014, the only
arXiv version), LaTeX source. Theorems are numbered by section, with remarks, lemmas and propositions
on the same counter. The journal text could not be retrieved (UNCHECKED); pc-audit RK4 records the
same limitation.

**Setting (§1).** For squarefree `n > 0`, `E_n : ny² = x³ − x`, isomorphic to `C_n` over `ℚ` by
`(x, y) ↦ (nx, n²y)`. By Birch–Stephens the root number of `E_n` is `−1` for `n ≡ 5, 6, 7 (mod 8)`
(quoted in TYZ §1; STANDARD). The invariant `𝓛(n)` is defined from `L(E_n, 1)` if `ord_{s=1} = 0`,
from `L'(E_n, 1)/R_n` if `ord_{s=1} = 1`, and is `0` if `ord_{s=1} > 1`. The integer `ρ(n) ≥ 0` is defined
by `2^{ρ(n)} = [E_n(ℚ) : φ_n(A_n(ℚ)) + E_n[2]]` for a 2-isogeny `φ_n : A_n → E_n`.

**Theorem 1.2** (= Theorem 3.5(2), which is stated as "an enhanced version of Theorem 1.2"). *Let
`n ≡ 5, 6, 7 (mod 8)` be positive and squarefree. Then `𝓛(n)` is an integer. If `n ≡ 5, 7 (mod 8)`,
then `2^{−ρ(n)}𝓛(n)` is even only if*

```
Σ_{n = d₀⋯d_ℓ, d_i ≡ 1 (8), i>0} Π_i g(d_i)  ≡  Σ_{n = d₀⋯d_ℓ, d₀ ≡ 5,6,7, d₁ ≡ 1,2,3, d_i ≡ 1 (8), i>1} Π_i g(d_i)  ≡  0 (mod 2).
```

*All decompositions are non-ordered with all `d_i > 1`.* (The case `n ≡ 6` is not used here.)

**Hypotheses.** Only `n > 0`, squarefree, `n ≡ 5, 6, 7 (mod 8)`. There is no condition on the number of
prime factors, on their residues, or on the Selmer group.

**Imports of TYZ's proof.** Waldspurger's formula, the Gross–Zagier formula of Yuan–Zhang–Zhang (their
Theorem 3.3, "Gross–Zagier formula", for the quadratic points `P_χ`) and Tian's induction. For the
remark that the rank part of BSD holds when `ord_{s=1} ≤ 1`, they cite Coates–Wiles, Rubin,
Gross–Zagier and Kolyvagin (§1).

### 1.2 The form used, and where TYZ prove it (VERIFIED by reading the proof)

**Proposition 1.1.** *Let `n ≡ 5 (mod 8)` be positive and squarefree. If `T_5b(n)` is odd, then
`2^{−ρ(n)}𝓛(n)` is odd; in particular `𝓛(n) ≠ 0` and `ord_{s=1} L(E_n, s) = 1`.*

*Where it is proved.* TYZ §3.3, last subsubsection ("Proof of Theorem 3.5: part (2)"). Assume
`P(n) ∈ A(K_n)^− + A[4]`, which TYZ identify with "`2^{−ρ(n)}𝓛(n)` is even" in the statement of
Theorem 3.5(2). Here `P(n)` is the genus point, an explicit combination of CM points on a modular
curve, and `A : 2y² = x³ + x`. TYZ apply `β' + 1` to the congruence of Proposition 3.4 and use
Lemma 3.21 and Lemma 3.18 (`A(ℍ'_n)_tors ⊂ A[4]`). They obtain, for `n ≡ 5 (mod 8)`,

```
c₁ τ((1−i)/2) + c₂ τ(1/2) ∈ ℤ τ(1),
c₁ = i^{(n−1)/2} Σ_{d₀ ≡ 5, d₁ ≡ 1,3, d_i ≡ 1 (i>1)} Π_i g(d_i),    c₂ = Σ_{d₀ ≡ 7, d₁ ≡ 1,3, d_i ≡ 1 (i>1)} Π_i g(d_i),
```

and conclude "the coefficients in both of the brackets must be even". The facts behind each step:

- *The second bracket is `T_5b(n)`.* If `d₀ ≡ 7` and the `d_i`, `i > 1`, are `≡ 1`, then `d₁ ≡ 5 · 7 ≡ 3`, so
  `d₁ ≡ 1` does not occur. `d₀` and `d₁` are the unique factors of classes 7 and 3, so `d₁ > 1`
  automatically, and the non-ordered factors `d_i ≡ 1`, `i > 1`, form a partition. The product
  `Π_i g(d_i)` includes `i = 0`, because Lemma 3.21(4) gives `Z(d₀)^{β'+1} = g(d₀)τ(1/2)` for `d₀ ≡ 7`. The
  unit `ε(d₀, d₁) = ±1` of Theorem 3.3 for `(d₀, d₁) ≡ (7, 3)` does not matter, since
  `−τ(1/2) = τ(1/2) − τ(1)`.
- *Both coefficients must be even.* Here `τ : ℂ/(1+i)ℤ[i] → A(ℂ)` and `ℤτ(1) = {0, τ(1)}`. If
  `a·u(1−i)/2 + b/2 ∈ ℤ + (1+i)ℤ[i] = ℤ[i]` with `u ∈ {±1, ±i}` and `a, b ∈ ℤ`, then `a` and `b` are even:
  for `a, b` not both even, the left side is `u(1−i)/2`, `1/2` or `(u(1−i) + 1)/2`, and none of these lies
  in `ℤ[i]` for any of the four units (checked case by case).

So the contrapositive is Proposition 1.1: `T_5b(n)` odd implies `P(n) ∉ A(K_n)^− + A[4]`, that is,
`2^{−ρ(n)}𝓛(n)` is odd. Directly: if `𝓛(n) = 0`, the first assertion of Theorem 3.5 (`P(n)` represents
`2^{−1−ρ(n)}𝓛(n)α_n` in `A(ℍ'_n) ⊗ ℚ`) makes `P(n)` torsion, hence in `A[4]` by Lemma 3.18, a
contradiction. Finally `𝓛(n) ≠ 0` gives `ord_{s=1} ≤ 1` by the definition of `𝓛`, and the root number `−1`
gives `ord_{s=1} = 1`.

*Relation with the statement of Theorem 1.2.* For `n ≡ 5` the first sum is Smith's
`T_5a = Σ_{d ≡ 5} g(d)𝓛(n/d)` (here `d₀ ≡ 5` is the unique factor not `≡ 1`). The second sum consists of
the `(5, 1)` terms and the `(7, 3)` terms. If `d₁ = 1` is admitted in the second sum, as Proposition 3.4
requires (its term `Z(n)` is `d₀ = n`, `d₁ = 1`; pc-audit RK4), the `(5, 1)` terms give `T_5a` again (see
the remark below) and the statement reads `T_5a ≡ T_5a + T_5b ≡ 0`, which is equivalent to the two
conditions of the proof; then Proposition 1.1 follows from the statement itself. Under the literal
reading `d₁ > 1`, the second sum becomes `T_5a + g(n) + T_5b`, and Proposition 1.1 needs the proof. This is
the citation issue of the verdict.

*Remark (the `(5, 1)` bracket; not used, partly SPECULATIVE).* Unwinding the recursion
`P(n) = Z(n) − Σ ε(d₀, d₁)𝓛(d₁)P(d₀)` that defines `P(n)`, the coefficient of `Z(d₀)` for `d₀ ≡ 5` is a sum
over ordered factorizations of `n/d₀` into factors `≡ 1`. After expanding each `𝓛` (Theorem 1.1) into
partitions, each partition into `k` blocks is counted once for every ordered set partition of its blocks,
that is, by the Fubini number `a(k)`. All Fubini numbers are odd (`a(k) = Σ_j C(k, j) a(k − j)` over
`j ≥ 1`, and induction), so the coefficient is `𝓛(n/d₀)` mod 2 and the first bracket is `T_5a`. The terms
with an even number of extra factors `≡ 3` carry a factor `±i` per pair of class changes and cancel in
pairs mod 2; this part was not written out (SPECULATIVE). Only the second bracket is used.

### 1.3 What Gross–Zagier and Kolyvagin add, and what the conclusion gives

- **Rank one.** Proposition 1.1 gives `ord_{s=1} L(C_n, s) = 1`. The manuscript's Lemma 5.5
  (`lem:forward-rank`, line 1086; audit record A020: Gross–Zagier, Kolyvagin MPI/90-69 Theorem 1,
  STANDARD) then gives `rank C_n(ℚ) = 1` and `Ш(C_n/ℚ)` finite. Modularity of `C_n` is classical (CM by
  `ℤ[i]`; Deuring, Shimura), so the BCDT citation inside Lemma 5.5 is not needed for these curves
  (pc-audit RK7). Only "analytic rank one implies rank at least one" is used below.
- **A Heegner-type point.** TYZ's Theorem 3.5 says more: the genus point `P(n)`, an explicit sum of
  CM points `f_n(P_n)^t` over a set of representatives of `2Cl'_n` corrected by lower genus points,
  represents `2^{−1−ρ(n)}𝓛(n)α_n`, where `α_n` generates `A(K_n)^−` modulo torsion. When `𝓛(n) ≠ 0` this
  point has infinite order in `A(K_n)^− ≅ A^{(−n)}(ℚ)`, a curve 2-isogenous to `E_n`. TYZ do not compute
  its 2-adic Kummer class.
- **No prescribed class.** Neither TYZ nor Gross–Zagier says which class of `C_n(ℚ)/2C_n(ℚ)` the point
  occupies. The class `β` comes from Selmer-minimality, as follows (pc-audit RK9, VERIFIED there and
  rechecked here): `C_n(ℚ)[2] = (ℤ/2)²` (STANDARD), so `dim C_n(ℚ)/2C_n(ℚ) = 2 + rank = 3 = dim Sel₂(C_n)`.
  The Kummer map is injective on `C_n(ℚ)/2C_n(ℚ)`, so it is onto `Sel₂(C_n)`. If `σ ∈ Sel₂` has first
  coordinate `β`, some `P ∈ C_n(ℚ)` maps to `σ`, and so does `P + 2Q` for `Q` of infinite order, which has
  infinite order. A point of infinite order has `x ∉ {0, ±n}`, so its first coordinate is the class of
  `x`: the abscissa lies in `βℚ*²`. Neither the Cassels–Tate pairing nor finiteness of `Ш` is used.

**Corollary 1.2.** *Let `d` be squarefree with `|d| ≡ 5 (mod 8)`, `dim Sel₂(C_d) = 3`, and `β` a first
coordinate of `Sel₂(C_d)`. If `T_5b(|d|)` is odd, then `C_d` has a rational point of infinite order with
abscissa in `βℚ*²`.* (Proposition 1.1 for `n = |d|`, Lemma 5.5, and the argument above.)

The rest of the note shows that `T_5b(|d|)` is odd for the curves of slot-k: §2–3 express `T_5b` as a
determinant, §4 evaluates the determinant on a Selmer-minimal curve, §5 applies this to slot-k.

## 2. Forests and Rédei's formulas

### 2.1 The forest lemma (VERIFIED, proved here)

Let `U` be a finite set with bits `a_{ij}` (`i ≠ j`), and let `L` be its Laplacian: `L_{ij} = a_{ij}`,
`L_{ii} = Σ_{j≠i} a_{ij}`. For `R ⊆ U`, a **forest rooted at `R`** is a map `f : U ∖ R → U` with `f(i) ≠ i`
and no cycles (iterating `f` from any `i` reaches `R`). Its **trees** are the fibres of the map
"iterate `f` until `R`"; each tree contains exactly one root, and `f` maps each tree into itself. The
weight is `wt(f) = Π_i a_{i f(i)}`. All determinants are over `𝔽₂`, where they equal permanents.

**Lemma 2.1 (forest lemma).** *For `F, W ⊆ U` with `|F| = |W|`,*

```
det L[U ∖ F, U ∖ W] = Σ wt(f),   f over forests rooted at F in which every tree contains exactly one element of W.
```

*Here `L[I, J]` is the submatrix with rows `I` and columns `J`.*

This is the `𝔽₂` case of the all-minors matrix-tree theorem (Chaiken, SIAM J. Alg. Disc. Meth. 3
(1982); STANDARD). A self-contained proof:

*Proof.* Expand `det L[U∖F, U∖W] = Σ_σ Π_i L_{iσ(i)}` over bijections `σ : U∖F → U∖W`, and expand each
diagonal entry `L_{ii} = Σ_{j≠i} a_{ij}`. The terms correspond to pairs `(f, D)`: `f : U∖F → U` with
`f(i) ≠ i`, and `D = {i : σ(i) = i}`, where `σ(i) = i` on `D` and `σ(i) = f(i)` off `D` must be a bijection
onto `U ∖ W`. The term has weight `wt(f)`.

*Cycles cancel.* Let `Z` be a cycle of `f`. If some `i ∈ Z` is not in `D`, then `σ(i) = f(i)`; if `f(i)`
were in `D`, then `σ(f(i)) = f(i) = σ(i)`, contradicting injectivity. Going around `Z`, either `Z ⊆ D` or
`Z ∩ D = ∅`. In the second case `σ` permutes `Z`, so `Z ⊆ U ∖ W`, and `Z` may be moved into `D` without
changing the image of `σ`. Toggling the cycle of `f` containing the smallest cyclic element is therefore
a weight-preserving involution without fixed points on the pairs where `f` has a cycle, and these
terms cancel mod 2.

*Acyclic `f`.* Then `f` is a forest rooted at `F`, and `σ` moves elements only within trees. Let `T` be a
tree with root `ρ`. Its domain elements `T ∖ {ρ}` are sent by `σ` injectively into `T ∖ W`, onto all of it,
so `|T| − 1 = |T ∖ W|`: each tree contains exactly one element `w` of `W`. Conversely, if this holds,
`σ` is unique: `w ∉ D` (as `w ∉ U∖W`), so `σ(w) = f(w)`; then `f(w)` is not hit by itself, so it is not in
`D`, and so on up to the root, which receives `σ` of its child on the path. Every vertex off the path
from `w` to `ρ` must be hit by itself (by induction from the leaves: its children are in `D`), so it lies
in `D`. Hence each such forest contributes exactly once. ∎

**Consequences.** For `B ⊆ V` and `ρ ∈ B` put `κ_ρ(B) = det L_B[B∖ρ, B∖ρ]`. By Lemma 2.1 with `U = B`,
`F = W = {ρ}`, it is the number mod 2 of spanning arborescences of `B` rooted at `ρ` (every vertex of
`B ∖ ρ` has one arrow inside `B`, `i → f(i)` of weight `a_{i f(i)}`, and all paths lead to `ρ`).

**Lemma 2.2 (column sums).** *The column sums of `L_B` are `c_j = y_j (1 + y(B))`. Hence:*
1. *if `y(B) = 1`, all cofactors of `L_B` are equal, and `κ_ρ(B) =: κ(B)` does not depend on `ρ`;*
2. *for all `B`, `det L_B[B∖j, B∖i] = κ_j(B)` for all `i, j ∈ B`;*
3. *(`κ`-difference) for `i ≠ j` in `B`, `κ_i(B) + κ_j(B) = Σ c(T_i)` over the forests of `B` rooted at
   `{i, j}`, where `T_i` is the tree of `i` and `c(T) = Σ_{v∈T} c_v`.*

*Proof.* Column `j`: `Σ_{i≠j} a_{ij} + L_{jj} = Σ_{i≠j} (a_{ij} + a_{ji}) = y_j (y(B) − y_j) = y_j(1 + y(B))`
mod 2. (2) The rows of `L_B[B∖j, B]` sum to zero, so the column `i` of this matrix is the sum of the
others, and deleting column `i` or column `j` gives the same determinant mod 2. (1) If `y(B) = 1` the
columns also sum to zero, so by the transposed argument the cofactor does not depend on the deleted row
either. (3) In `L_B[B∖j, B∖j]`, add all other rows to row `i`: the new row `i` is
`(c − L_{j,·})` restricted to `B ∖ j`. The determinant splits as `det(row i ← c) + det(row i ← L_{j,·})`.
The second matrix is `L_B[B∖i, B∖j]` with rows permuted, of determinant `κ_i(B)` by (2). Expanding the
first along the row `c`: `Σ_{v ∈ B∖j} c_v det L_B[B∖{i,j}, B∖{j,v}]`, and by Lemma 2.1 (roots `{i, j}`,
`W = {j, v}`) the minor counts the 2-forests rooted at `{i, j}` with `v` in the tree of `i` (for `v = i`, all
2-forests). Summing over `v` gives `Σ c(T_i)`. ∎
