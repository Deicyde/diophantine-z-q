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
