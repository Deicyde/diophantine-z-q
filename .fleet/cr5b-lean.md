# cr5b-lean report: tyz-5b §4 (the elementary half of the TYZ route for CR₃^Sel) in Lean

All new code is in `ZInQKernel/RouteK/Rank5b/` (namespace `ZInQ.RouteK.Rank5b`), with root module
`ZInQKernel/RouteK/Rank5b.lean`, imported from `ZInQKernel.lean` (one line). No `sorry`, no axioms,
no `native_decide`. No existing file was edited apart from that one import line.

## Results

| tyz-5b item | Lean name | file | status |
| --- | --- | --- | --- |
| Notation: `a_ij = (p_j/p_i)₊`, `y_i`, `z_i` | `aBit`, `yBit`, `zBit` | Matrices.lean | defined |
| agreement with the Lean system (`a_ij = bit p_j p_i`, `y = λ`, `z = μ`) | `natConfig_bit_eq_aBit`, `natConfig_lam_eq_yBit`, `natConfig_mu_eq_zBit` | Matrices.lean | proved |
| `L`, `M₁` (on `P ⊕ P`), `M_5b` (on `(P ⊕ P) ⊕ Unit`) | `Lmat`, `M1`, `M5b` (configuration level: `Config.Lc`, `Config.M1c`, `Config.M5bc`; `M1_eq_M1c`, `M5b_eq_M5bc`) | Matrices.lean | defined |
| `M₁` symmetric | `M1_transpose`, `Config.M1c_transpose` | Matrices.lean | proved |
| reciprocity `a_ij + a_ji = y_iy_j`; `(L + Lᵀ)_ij = y_iy_j` off the diagonal, `0` on it | `aBit_add_aBit`, `Lmat_add_transpose_apply` | Matrices.lean | proved |
| (E1),(E2),(R),(D) = the Lean system for `c = 5` | `Config.D_iff_of_five` (and the definitions, see below) | Kernel.lean | proved |
| Lemma 4.1: `Sel₂ = 𝒯 ⊕ H` | `Config.solEquivTorsH : {σ // IsSol σ} ≃ (ZMod 2 × ZMod 2) × {σ // IsH σ}` | Kernel.lean | proved |
| Lemma 4.1: `H ≅ ker M₁`, `(a,b) ↦ (u+v, u)` | `Config.hEquivKer`; for `Sel₂(C_n)`: `sel2HEquivKer` (+ `sel2HEquivKer_apply`) | Kernel.lean, Row5b.lean | proved |
| Lemma 4.1: `#Sel₂(C_n) = 4 · #ker M₁` | `Config.card_sols_eq`; `sel2_ncard_eq_four_mul` (via `prop0`, `sel2_subset_range_selPair`, `selPair_injective`; also `sel2_eq_image`, `sel2_ncard_eq_card_sols`) | Kernel.lean, Row5b.lean | proved |
| Lemma 4.2 (bordered determinant) | `det_border_eq_dotProduct` (with `border M v = fromBlocks M (replicateCol v) (replicateRow v) 0`) | Bordered.lean | proved |
| Theorem 4.3 | `det_M5b_eq_dot` (configuration level: `Config.det_M5bc_eq`) | Row5b.lean | proved |
| Corollary 4.4, first sentence | `det_M5b_eq_one` | Row5b.lean | proved |
| CR₃^5b | `CertifiedRank5b` (docstring = trust statement) | Row5b.lean | defined |
| derivation | `certifiedRankSel_of_certifiedRank5b : CertifiedRank5b → Selmer.CertifiedRankSel` | Row5b.lean | proved |
| main-theorem variant | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b (hH : SixContactMin) (hCR5 : RouteK.Rank5b.CertifiedRank5b) (h22 : FixedPrimePattern) : FrozenTarget` | Rank5b.lean (root) | proved |
| kernel cross-checks (step 6) | `det_M5b_21 : (M5b 21).det = 1`, `det_M5b_5 : (M5b 5).det = 0` | Check.lean | proved |

`CertifiedRank5b` is exactly the requested
`∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → (M5b d).det = 1 → ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2`;
`M5b d` takes only `d` (the data use `legBit`, which needs no oddness proof).

`#print axioms` on `certifiedRankSel_of_certifiedRank5b`, `det_M5b_eq_dot`, `det_M5b_eq_one`,
`det_border_eq_dotProduct`, `sel2_ncard_eq_four_mul`, `sel2HEquivKer` and the variant:
`[propext, Classical.choice, Quot.sound]`. `python3 scripts/check_target.py`: "FrozenTarget matches".

## Statements: how the Lean forms read, and the differences from tyz-5b §4

1. **The equations of §4.1 are the Lean system literally**, no change of convention:
   `Config.monsky u x = Σ_{y≠x} bit y x (u_y + u_x)` with `bit y x = [y/x] = a_xy`; `E1`, `E2`, `(R)`
   are `Config.E1`, `Config.E2`, `a0 = b0`; `(D)` for `c = 5` is `twoAdicRows 5 = (a₁ = 0 ∧ b₁ = μ·u ∧
   λ·v = λ·u)` (`Config.D_iff_of_five`); `λ = y`, `μ = z`. For `natConfig n`, `prodClass = n mod 8 = 5`
   (`natConfig_prodClass`).
2. **Torsion.** `𝒯 = {(−1,−n)^e (n,2)^f}` is written on the unknowns as `tors e f = (a₀, a₁, b₀, b₁, u, v)
   = (e, 0, e, f, f·𝟏, e·𝟏)`; the splitting map is `σ ↦ ((a₀ + λ·u, b₁), σ + tors(a₀ + λ·u, b₁))`, exactly
   the "change of `(b₁, a₀ + λ·u)`" argument of §4.1. "Non-torsion" in Theorem 4.3 is formalized as
   `∀ e f, σ ≠ tors e f` for the unknowns `σ` with `selPair n σ = (a, b)` (equivalent to `(a, b) ∉ 𝒯`
   by `selPair_injective`). The conclusion `det M_5b = y·u` is `dot (yBit n) σ.u = Σ_{p | a} y_p`.
   The "same value on all four representatives" remark is not stated separately (it is immediate
   from the theorem applied to each non-torsion representative).
3. **Corank one.** Lemma 4.2 is stated for a symmetric `M` over `ZMod 2` with a vector `k ≠ 0`,
   `M k = 0`, and `∀ w, M w = 0 → w = 0 ∨ w = k` (kernel `= {0, k}`, i.e. corank one over `𝔽₂`), any
   `Fintype` index. **The proof differs from tyz-5b's**: no adjugate. If `v·k = 0`, `(k, 0)` is a
   nonzero kernel vector of the bordered matrix; if `v·k = 1`, pairing the first block of
   `N(w, t) = 0` with `k` (using `kᵀM = (Mk)ᵀ = 0`) gives `t = 0`, then `w ∈ {0, k}` and `v·w = 0`
   give `w = 0`, so `det N ≠ 0`, i.e. `det N = 1` (Mathlib `Matrix.exists_mulVec_eq_zero_iff`).
   This avoids the step "adj(M) is nonzero when the corank is one", which Mathlib does not have.
4. **`M₁` is symmetric by its block shape** (`[[X, Lᵀ], [L, D]]` with `X = L + Lᵀ`), for any bits; reciprocity
   is not needed for the symmetry. Reciprocity (from `legBit_reciprocity`, i.e. Mathlib's
   `legendreSym.quadratic_reciprocity`) is used for `X_ij = y_iy_j` (`Lmat_add_transpose_apply`) and,
   at configuration level, inside the computation `(Lᵀt)_i = (Kt)_i + y_i(y·t + t_i)` (`Config.LcT_mulVec`).
5. **Corollary 4.4** is formalized with the hypothesis requested (`|a| ≡ 7 (mod 8)` for some
   `(a, b) ∈ Sel₂`), which is what `CertifiedRankSel` uses. tyz-5b's weaker hypothesis
   `|a|_odd ≡ 3 (mod 4)` also follows from `det_M5b_eq_dot` (`a` is odd since `a₁ = 0`), but is not
   stated as a separate theorem. The non-torsion step uses `|a| = Π_{p|a} p ∈ {1, n}` for torsion
   classes (`natAbs_classInt_zero`, `Nat.prod_primeFactors_of_squarefree`), and `y·u = λ(|a| mod 8)`
   (`lam8_prod_pow`).
6. No mathematical error was found in tyz-5b §4.

## Lemmas added beyond the leaves (all in `ZInQ.RouteK.Rank5b`; names checked for clashes)

Bordered.lean: `border`, `zmod2_eq_zero_or_one'`, `border_mulVec_inl`, `border_mulVec_inr`.
Kernel.lean: `zmod2_mul_self`, `Config.sum_lam`, `Config.sum_mu`, `Config.bit_eq_bit_add`,
`Config.Lc_mulVec` (`(L s)_x = (K s)_x`), `Config.LcT_mulVec`, `Config.M1c_mulVec_inl`,
`Config.M1c_mulVec_inr` (the (top)/(bottom) equations of §4.1), `Config.lam_sum_of_five`,
`Config.mu_sum_of_five`, `Config.monsky_add`, `Config.monsky_const`, `Config.dot_add_right`,
`Config.dot_const`, `Config.sum_monsky` (`Σ_x (Kw)_x = λ·w` when `y(V) = 0`), `uadd`, `tors`,
`uadd_tors_tors`, `Config.isSol_uadd_tors`, `Config.IsH`, `Config.kvec`, `Config.ofKer`,
`Config.M1c_mulVec_kvec`, `Config.isH_ofKer`, `Config.kvec_ofKer`, `Config.ofKer_kvec`,
`Config.torsCoord`, `Config.isH_uadd_torsCoord`.
Row5b.lean: `Config.ofKer_zero`, `Config.uadd_tors_zero_zero`, `natAbs_classInt_zero`, `lam8_prod_pow`.
Check.lean: `Config.M5bc_of_iso`, `Config.det_M5bc_of_iso` (invariance of `M_5b` under isomorphism
of configurations), `primeFactors_21`, `primeFactors_5`, `legBit_3_7`, `legBit_7_3`, `enum21`,
`equiv21`, `idx5`, `M5bc_primeCfg_21`.

(The namespace `ZInQ.RouteK.Rank5b.Config` holds the configuration-level facts; inside it, write
`RouteK.Config.E1` etc. for the system's own declarations, and `IsH 𝒞 σ` rather than `𝒞.IsH σ`.)

## Cross-checks (kernel only)

`n = 21 = 3·7`: `det M_5b = 1` (tyz-5b §5–6: `#Sel₂ = 8`, `7` a first coordinate). `n = 5`:
`det M_5b = 0` (`y_5 = 0`, the border row vanishes). The `n = 21` check transports `M5b 21` to the
configuration `primeCfg ![3, 7]` (`det_M5bc_of_iso`), evaluates the entries from `legBit 3 7 = 0`,
`legBit 7 3 = 1`, and expands the explicit `5 × 5` determinant (`det_succ_row_zero`, `decide`);
about 8 s. Python on the same definitions also gives `det M_5b = 1` for `3·23`, `7·11`, `7·19`, and `0`
for `13`, `3·7·17` (not checked in Lean).

## Build

* Full `lake build ZInQKernel` in this worktree (Mathlib cache present, project oleans partly
  missing): 5 min 11 s wall. Incremental after the Rank5b changes: 26 s.
* Each Rank5b module elaborates in 4–8 s.

## What §3 (det M_5b = T_5b, the forest lemma, Rédei's formulas) would need in Lean

The goal would be `CertifiedRank5b` from a hypothesis in TYZ's own form ("`T_5b(n)` odd ⇒ every Selmer
class is a point"), i.e. Theorem 3.6 `T_5b(n) = det M_5b` for `n ≡ 5 (mod 8)`.

1. **Genus data.** Define `g(d) = #Cl(ℚ(√−d))[2^∞]`-parity in Lean — not available in Mathlib in a usable
   form (class groups of imaginary quadratic fields exist abstractly as `ClassGroup (𝓞 K)`, but the
   4-rank/genus theory is absent). Practical route: *define* `g` by Rédei's formulas (Prop. 2.3,
   `g(B) = κ(B)` or `Σ_ρ z_ρ κ_ρ(B)`) as a function of the bits, prove Theorem 3.6 for that `g` purely
   combinatorially, and put "Rédei's `g` equals the class-number parity" (G1–G3, genus theory) into the
   trust statement, next to TYZ. Then all of §3 is linear algebra over `𝔽₂` on bits with reciprocity.
2. **Forest lemma (Lemma 2.1)**, all-minors matrix-tree theorem over `𝔽₂`: not in Mathlib (Mathlib has
   no matrix-tree theorem). Needs functional graphs `f : U∖F → U`, acyclicity, trees as fibres, and the
   cycle-toggling sign-reversing involution; this is the largest piece (estimate: 1–2k lines). Over
   `𝔽₂` determinant = permanent, which removes signs but the bijection `(f, D) ↔ σ` remains.
3. **Lemma 2.2** (column sums, cofactor independence, κ-difference): standard determinant manipulations
   (`Matrix.det_updateRow_add`, Laplace expansion `det_succ_row` on `Fin`-indexed submatrices); needs
   a good API for submatrices indexed by finsets (`Matrix.submatrix` with `Finset` subtypes).
4. **Lemmas 3.1–3.2**: `det (J − I)` over `𝔽₂` and a generalized Laplace expansion along a block of rows
   (Mathlib has only single-row Laplace; the block version — or the involution expansion of a symmetric
   determinant used in Prop. 3.4 — must be written).
5. **Props. 3.3–3.5 and Theorem 3.6**: sums over set partitions (Mathlib's `Finpartition`), grouping of
   forests by their tree partition, multilinear-polynomial coefficient comparison in `z`, and
   `(2k−1)!!` odd. Combinatorially heavy but elementary.
6. Since `det M_5b` is now a Lean object with Theorem 4.3 proved, the cleanest finishing statement would
   be `T5b n = (M5b n).det` with `T5b` defined from Rédei's `g`; the kernel can cross-check small `n`
   (as `det_M5b_21`) once `T5b` is computable on concrete bits.

## Problems

None blocking. `legBit` is defined with classical decidability, so `M5b n` cannot be evaluated by
`decide` directly; concrete values need the transport lemma `det_M5bc_of_iso` and explicit Legendre
bits (as in Check.lean).

## Suggestions for the next agent

* To use `CertifiedRank5b` downstream, `certifiedRankSel_of_certifiedRank5b` composes with
  `Selmer.certifiedRank_of_certifiedRankSel`; the main-theorem variant is already in the root module.
* For more kernel checks, copy the `n = 21` pattern: enumerate primes as `Fin r → ℕ`, prove the
  `legBit` values (`⟨r, by decide⟩` for squares, `fin_cases` for non-squares), give an explicit
  `Fin (2r+1) ≃ (Fin r ⊕ Fin r) ⊕ Unit`, and expand. `r = 3` (7 × 7) should still be cheap.
* If Lemma 4.1 is needed for other classes `c`, the configuration-level file is generic except
  `D_iff_of_five`, `lam_sum_of_five`, `mu_sum_of_five` (the torsion generators change with `c`).
