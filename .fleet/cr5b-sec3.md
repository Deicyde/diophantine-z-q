# cr5b-sec3 report: tyz-5b §§2–3 in Lean, and CR₃ in the terms of Tian–Yuan–Zhang

All of the task is done, with no `sorry`. `lake build ZInQKernel` succeeds,
`python3 scripts/check_target.py` reports that `FrozenTarget` matches, and `#print axioms` on
`ZInQ.RouteK.Rank5b.det_M5b_eq_T5b` (Theorem 3.6), `ZInQ.RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ`
and `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ` lists
only `propext`, `Classical.choice` and `Quot.sound`.

The files are under `ZInQKernel/RouteK/Rank5b/Sec3/`, about 4,150 lines. The root module is
`ZInQKernel/RouteK/Rank5bSec3.lean`, and `ZInQKernel.lean` imports it with one line. No other existing file
was edited. Generic lemmas are in the namespace `ZInQ.RouteK.Rank5b.Sec3` (written `Sec3.` below). They
are stated for any finite index type `ι` with bits `a : ι → ι → 𝔽₂` and `y z : ι → 𝔽₂`, under reciprocity
`Sec3.Recip a y` (`a_ij + a_ji = y_i y_j` for `i ≠ j`). The statements about `d` are in
`ZInQ.RouteK.Rank5b`.

## Lean names for tyz-5b §§2–3

| tyz-5b item | Lean name | status |
| --- | --- | --- |
| Notation: `L_B` (Laplacian on `B`) | `Sec3.lapl a B` (`Lmat d` is `lapl (aBit d) univ` by `rfl`) | definition |
| Notation: genus sum `T_5b` | `Sec3.genusSum5b` (bits, sum over `Finpartition univ`), `T5b d` (residues of `d_B` mod 8), `T5b_eq_genusSum5b` | definitions; equality proved |
| §2.1 Lemma 2.1 (forest lemma) | `Sec3.pmin_lapl_eq_forests` (with `Sec3.det_submatrix_eq_pmin`, `Sec3.det_eq_pmin_univ`: over `𝔽₂` a determinant is the permanent `pmin`) | proved |
| §2.1 Consequences (`κ_ρ(B)` counts arborescences) | `Sec3.kappa` (definition, `det L_B[B∖ρ, B∖ρ]`), `Sec3.kappa_eq_forests` | proved |
| Lemma 2.2, column sums `c_j = y_j(1 + y(B))` | `Sec3.colSum_lapl` | proved |
| Lemma 2.2(1) | `Sec3.kappa_eq_kappa` | proved |
| Lemma 2.2(2) | `Sec3.pmin_lapl_offdiag` | proved |
| Lemma 2.2(3) (`κ`-difference) | `Sec3.kappa_add_kappa` | proved |
| §2.2 Proposition 2.3 (Rédei) | `Sec3.redeiG` (definition of `g` from the `κ` forms), `gBit d B`; `Sec3.redeiG_eq_kappa` (case 1 as stated) | used as the definition; the class-number identity is part of the trust statement |
| (2.1) | `Sec3.sum_y_kappa`, `Sec3.sum_z_kappa` | proved |
| (2.2) | `Sec3.sum_z_kappa_of_y_zero` | proved |
| Lemma 3.1, Lemma 3.2 | not formalized as stated; replaced by `Sec3.det_M1G`, `Sec3.det_M5bG`, `Sec3.det_Pmat` (see the notes) | replaced |
| Proposition 3.3 | `Sec3.det_M1G_eq_class3` (`y(V) = 0`), `Sec3.det_M1G_eq_zero` (`y(V) = 1`); forest form `Sec3.det_Pmat` with `Sec3.det_M1G` | proved |
| Proposition 3.4 | `Sec3.det_M5bG_eq_class73` (partition form), `Sec3.det_M5bG_forest` (forest form) | proved |
| Proposition 3.5 | `Sec3.sum_class1_eq_sum_class3` | proved |
| Theorem 3.6 | `Sec3.det_M5bG_eq_genusSum5b` (bits: reciprocity and `y(V) = 0`); `det_M5b_eq_T5b` (squarefree `d ≡ 5 (mod 8)`) | proved |
| CR₃^TYZ | `CertifiedRankTYZ`, `certifiedRank5b_of_certifiedRankTYZ` | definition; proved |
| Main theorem variant | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ` (root module) | proved |
| §6 cross-checks | `T5b_21`, `T5b_5`, `T5b_5_direct` (`Sec3/Check.lean`) | proved |

`M5b d = Sec3.M5bG (aBit d) (yBit d) (zBit d)` holds by `rfl` (`Sec3.M5b_eq_M5bG`).

## Definitions of `g` and `T_5b`

- **`g`** (`Sec3.redeiG a y z B`). Let `κ_ρ(B) = det L_B[B∖ρ, B∖ρ]` (`Sec3.kappa`, a Mathlib `det` on the
  subtype `B.erase ρ`). Then `g(B) = Σ_{ρ∈B} y_ρ κ_ρ(B)` if `y(B) = 1` and `g(B) = Σ_{ρ∈B} z_ρ κ_ρ(B)`
  if `y(B) = 0`. These are Rédei's formulas of tyz-5b Proposition 2.3. For `y(B) = 1` the proposition
  says `g(B) = κ(B)`, the common value of the `κ_ρ(B)`. The definition uses `Σ_ρ y_ρ κ_ρ(B)` instead,
  so that no `ρ` has to be chosen. The two agree by Lemma 2.2(1), because `Σ_ρ y_ρ = 1`
  (`Sec3.redeiG_eq_kappa`). For `d`, `gBit d B = redeiG (aBit d) (yBit d) (zBit d) B`, a function of
  the bits only.
- **`T_5b`**. `T5b d` is the sum of `Π_{B∈π} gBit d B` over `π : Finpartition (univ : Finset
  d.primeFactors)` satisfying `Admissible5bNat`: exactly one block with `d_B ≡ 7`, exactly one with
  `d_B ≡ 3`, and every block `≡ 7, 3` or `1 (mod 8)`, where `d_B = Π_{p∈B} p` (`dProd`). The generic
  `Sec3.genusSum5b` reads the classes off the bits, `(y(B), z(B)) = (1,0), (1,1), (0,0)`.
  `T5b_eq_genusSum5b` proves that the two agree for odd `d`, using `lam8_prod`, `mu8_prod`, and the fact
  that an odd class mod 8 is determined by `(λ, μ)`.

## Trust statement of `CertifiedRankTYZ`

`CertifiedRankTYZ := ∀ d, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5b d = 1 → ∀ ab ∈ Sel2 d,
Loc ℚ d ab.1 ab.2`. Its docstring states the inputs it rests on:

- **Tian–Yuan–Zhang**, Asian J. Math. 21 (2017), arXiv:1411.4728, in the form proved in the proof of
  their Theorem 3.5(2) (§3.3). For squarefree `n ≡ 5 (mod 8)`: if the `(7, 3)` genus sum is odd, then
  `2^{−ρ(n)}𝓛(n)` is odd, so `ord_{s=1} L(C_n, s) = 1`. See tyz-5b §1, Proposition 1.1, and its caveat
  about how to read the statement of Theorems 1.2 and 3.5(2); see also `docs/research/nt-tyz.md`.
- **Rédei's formula** (tyz-5b Proposition 2.3, genus theory): the `κ` forms in `gBit` equal
  `#2Cl(ℚ(√−d)) mod 2`, so `T5b d` is TYZ's genus sum. This is not formalized.
- **Gross–Zagier and Kolyvagin** (manuscript Lemma 5.5): `rank C_d(ℚ) = 1`. Then
  `dim C_d(ℚ)/2C_d(ℚ) = 3 = dim Sel₂`, so every Selmer class comes from a rational point.

`certifiedRank5b_of_certifiedRankTYZ` uses only Theorem 3.6. The chain to the main theorem is
CR₃^TYZ → CR₃^5b (Theorem 3.6) → CR₃^Sel (cr5b-lean's Corollary 4.4) →
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel`.

## Differences from tyz-5b (no mathematical error found)

1. **Lemmas 3.1 and 3.2 are replaced by rank-one algebra.** By reciprocity, `L + Lᵀ = D_y + y yᵀ`.
   Hence `M₁ = P + w wᵀ` with `P = [[D_y, Lᵀ], [L, D_z]]` (`Sec3.Pmat a z y`) and `w = (y, 0)`. Since the
   rows of `L` sum to zero, `P (𝟏, 0) = w`. The matrix determinant lemma, which I proved without the
   invertibility hypothesis Mathlib needs (`Sec3.det_add_col_mul_row`, `Sec3.det_add_col_mul_row_of_mulVec`),
   then gives `det M₁ = (1 + y(V)) det P` (`Sec3.det_M1G`). Over `𝔽₂`,
   `det [[A, v], [vᵀ, 0]] = det(A + v vᵀ) + det A` (`Sec3.det_border_zmod2`). With the symmetric
   quadratic form of `adj P` (`Sec3.quad_symm_zmod2`), this gives
   `det M_5b = (1 + y(V)) Σ_k y_k (det P(z[k↦1]) + det P(z[k↦0]))` (`Sec3.det_M5bG`). Finally
   `det P(c, d) = Σ_F c^F Σ_{f rooted at F} wt(f) Π_ρ d(T_ρ)` (`Sec3.det_Pmat`), by a principal-minor
   expansion, the anti-diagonal block structure and a transversal sum.
   The case `y(V) = 1` of Proposition 3.3 then follows from the factor `1 + y(V)`, without the parity
   argument of the paper.
2. **The proof of Theorem 3.6 differs.** It avoids splitting a partition into `(B₇, B₃, partition of
   S)`. Both sides become sums over the forests `f` of `V` of
   `(Σ_{k root} y_k z^{R∖k}) wt(f) Π_ρ y(T_ρ)` (`Sec3.det_M5bG_forest`, `Sec3.genusSum5b_eq_forest`).
   On the `T_5b` side:
   - each block weight is written as a forest sum (`Sec3.w7_eq`, `w3_eq`, `w1_eq`; the last uses
     Lemma 2.2(3) as in the proof of Proposition 3.5);
   - the forests are glued along the partition (`Sec3.prod_sum_allF`);
   - for a fixed forest, the compatible marked partitions correspond to pairings of the remaining roots
     (`Sec3.card_setA`);
   - the number of pairings is odd iff the set has even size (`Sec3.card_fpfi`, by conjugation with a
     transposition). This is the paper's "`(2k−1)!!` is odd".

   Propositions 3.3–3.5 are also proved in their partition forms, by the same machinery.
3. **Proposition 3.5** is stated for the whole index type: partitions of `V` with `y(V) = 0`. For a subset
   `S`, apply it to the subtype `S` with the restricted bits.
4. **Generic Theorem 3.6** needs only reciprocity and `y(V) = 0`, i.e. `n ≡ 1 (mod 4)`; `z(V) = 1` is not
   needed. For `d`, squarefreeness is used only to get `y(V) = 0` from `d ≡ 5 (mod 8)`
   (`sum_yBit_univ`). The statement keeps tyz-5b's hypotheses.
5. **Forest lemma.** It is stated for a fixed `W`, with the condition "every tree contains exactly one
   element of `W`" (`Sec3.IsTransv`). The cycle cancellation fixes one cycle of `f` and toggles `σ` on
   it, instead of using the smallest cyclic element. In the acyclic case the compatible bijection is
   given explicitly (`Sec3.sigmaW`).

## Lemmas added beyond the leaves (all in `Sec3`)

- **Permanent minors**: `pmin`, `bijFun`, `pmin_expand_row`, `pmin_updateRow_sum`, `pmin_eq_zero_of_row_eq`,
  `pmin_add_diagonal`, `pmin_fromBlocks_anti`, `pmin_transpose`.
- **Forests**: `mapsOn`, `root`, `IsAcyc`, `forests`, `allF`, `compat`, `card_compat_even`, `eq_sigmaW`,
  `sigmaW_mem_iff`, `sum_transv`.
- **Determinants**: `det_add_col_mul_row`, `det_add_col_mul_row_of_mulVec`, `det_border_zmod2`,
  `quad_symm_zmod2`, `adjugate_Pmat_inr`.
- **Set partitions**: `ofPartFun`, `part_ofPartFun`, `finpartition_ext_part`, `prod_parts_inter`, `Resp`,
  `prod_sum_allF`, `fpfi`, `card_fpfi`, `setA`, `card_setA`, `setAgen`, `card_setAgen`, `sum_prod_uniform`.

Top-level names in `ZInQ.RouteK.Rank5b` are `recip_bits`, `yBit_eq_lam8`, `zBit_eq_mu8`,
`dProd_class_iff`, `admissible5bNat_iff`, `sum_yBit_univ` and `natMod8_eq_iff_cast`. A grep of
`ZInQKernel/` found no clashes.

## Cross-check (step 4)

`T5b n` cannot be evaluated by the kernel. The bits are defined through `IsSquare` in `ZMod p` (`legBit`),
so they are noncomputable, and `decide` does not apply. Instead:

- `T5b_21 : T5b 21 = 1` and `T5b_5 : T5b 5 = 0` combine Theorem 3.6 with cr5b-lean's kernel checks of
  `det M_5b`. They are not independent of Theorem 3.6.
- `T5b_5_direct` gets `T5b 5 = 0` from the definition alone: the only block is `{5}`, of class 5.

An independent check of `n = 21` from the definition would have to enumerate the two set partitions of
`{3, 7}` and evaluate small `κ` determinants by hand. It was not done.

## Build times

- Each `Sec3` file takes 5–10 s with `lake env lean`, including about 4–5 s of imports (measured
  5.2–9.4 s; the slowest are Genus, Thm36 and TYZ).
- `lake build ZInQKernel.RouteK.Rank5bSec3` takes about 15 s incrementally.
- A full `lake build ZInQKernel` with everything else already built takes a few seconds; the initial
  build of the tree from a partial cache took about 6 min.

## What remains

- Rédei's formula, tyz-5b Proposition 2.3 (the class-number parity), is not formalized. It is part of
  the trust statement, as the task specified.
- The journal statement of TYZ Theorems 1.2 and 3.5(2) is still UNCHECKED (tyz-5b §1.2), as is the
  reading `d₁ = 1`.
- **Suggestion.** If an independent kernel check of `T5b` is wanted, give a computable bit table for one
  small `n` (as `Rank5b/Check.lean` does with `primeCfg`) and evaluate `Sec3.genusSum5b` on `Fin r`
  through a computable enumeration of partitions. The current `Finpartition` instance is probably too
  slow for `decide`.
