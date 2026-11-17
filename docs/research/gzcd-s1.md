# gzcd-s1: `hGZ` in printed form; the three queue12 steps (S1, G4(b), S2) are Lean proofs

Status: research note (task gzcd-s1, 2026-11-17). Branch `wip/gzcd-s1`, base `wip/leaf-fold33b` (08ca9c44, with
`origin/main` an ancestor), and `origin/wip/h33-d1` (4b12a442) merged. h33-d1 already contains
`origin/wip/eps-splitting` (5e3d65de) and hgz-steps. The merge added 42 files and modified none, with no conflicts.

New Lean files (nothing else under `ZInQKernel/` edited):
- `ZInQKernel/Contrib/OneProof/GrossZagierCdPrinted/Discr.lean`: the discriminant bridge.
- `ZInQKernel/Contrib/OneProof/GrossZagierCdPrinted.lean`: the printed leaf, the equivalence with `hGZ`'s current
  type, and the bridge.

Scratch, checks and log are in `scratch/gzcd-s1/`.

Marks:
- **VERIFIED**: compiled, computed, or read in a source named here.
- **STANDARD**: published, with an exact reference.
- **SPECULATIVE**: an assessment.
- **UNVERIFIED**: a theorem number from memory. This host has no copy of Gross–Zagier.

---

## 0. Main result

**The current type of the binder `hGZ`, hgz-steps' `ZInQ.GZSch.GrossZagierCurveCd`, is equivalent in Lean to a
printed-form leaf, `ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted`.** None of the three steps in the queue12 verdict
is left (VERIFIED: compiled, no `sorry`, standard axioms):

```lean
theorem ZInQ.GZCdPrinted.grossZagierCurveCd_iff_printed :
    ZInQ.GZSch.GrossZagierCurveCd ↔ ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted
theorem ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed :
    GrossZagierCurveCdPrinted → ZInQ.GZSch.GrossZagierCurveCd          -- discharges hGZ
```

| queue12 step | content | Lean |
| --- | --- | --- |
| **S1** | the leaf ranges over every normal proper model `(X, ι)` of `X₀(N)` | model uniqueness, both directions of valuative extension: `CurveModel.exists_iso_of_functionField` and `GZUnique.model_transfer` (h33-d1; reused, not duplicated). The printed leaf asks for **one** model. |
| **G4(b)** | `V₊(Z) ∩ ESch E = {O}` | `H33D1.not_mem_chartZ_iff` (h33-d1). The printed leaf now states `π(∞) = O` literally (`π p = H33D1.ptO E`, with `O = [0 : 1 : 0]` = `ker χ_O` on the chart `D₊(Y)`). |
| **S2** | `ε_D` vs. the splitting character of `K` | eps-splitting: `EpsSplit.quadChar_eq_epsD` and `epsD_eq_one_iff_isSplitIn`. **New here: the discriminant bridge** `GZDiscr.discr_eq_of_sq` and `GZDiscr.exists_sq_eq_discr`. The printed leaf takes `K` by its discriminant (`NumberField.discr K = D`), with any embedding `K → ℂ`. |

`#discharges` (VERIFIED, `scratch/gzcd-s1/Discharges-output.txt`, 0 `sorry`):

```
DISCHARGES [hGZ] by ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed
  still assumes: [ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 39 open hypotheses, 13888 theorems checked, 30 discharge one
```

**Rating.** `GZCdPrinted.GrossZagierCurveCdPrinted` is **LEAF, printed form (direct instance)** (§3). Since
`GZSch.GrossZagierCurveCd` is equivalent to it in Lean, the current binder can be rated LEAF by that equivalence,
with no edit to `Main.lean`. The other option is the manual fold of §4. Either way the count is **`hGZ` GLUE →
LEAF, GLUE −1, no new glue**. The only items left are readings, not Lean steps (§3):
- the canonical model;
- the point `τ`;
- G10, the normalization of `ĥ`.

## 1. The discriminant bridge (`GrossZagierCdPrinted/Discr.lean`, namespace `ZInQ.GZDiscr`)

```lean
theorem discr_basis_two [Algebra ℚ K] (c : Basis (Fin 2) ℚ K) (h0 : c 0 = 1) (A B : ℚ)
    (hw : c 1 * c 1 = A • c 1 + B • (1 : K)) : Algebra.discr ℚ c = A ^ 2 + 4 * B
theorem discr_eq_of_sq [NumberField K] (hD : Int.IsFundamentalDiscr D) (hneg : D < 0)
    (hK : finrank ℚ K = 2) (hδ : δ ^ 2 = (D : K)) : NumberField.discr K = D
theorem exists_sq_eq_discr [NumberField K] (hK : finrank ℚ K = 2) :
    ∃ δ : K, δ ^ 2 = (NumberField.discr K : K)
```

All three are VERIFIED (compiled, standard axioms).

- **`discr_basis_two`.**
  - `Tr 1 = 2` and `Tr w = A`, the latter from the matrix trace of `leftMulMatrix c w`.
  - `Tr w² = A² + 2B`.
  - The determinant of the trace matrix is `2(A² + 2B) − A² = A² + 4B`.
- **`discr_eq_of_sq`.**
  - `{1, θ}` with `θ = (D + δ)/2` is a `ℤ`-basis of `𝓞_K` (`thetaBasis`). It is spanning by eps-splitting's
    `exists_int_repr` and independent by `thetaK_ne`.
  - Mathlib's `NumberField.discr_eq_discr` and `Algebra.discr_localizationLocalization` reduce `discr K` to the
    `ℚ`-discriminant of `{1, θ}`.
  - From `θ² = Dθ − (D² − D)/4`, that discriminant is `D² − (D² − D) = D`.
- **`exists_sq_eq_discr`.**
  - Take `w ∉ ℚ` and the basis `c = {1, w}` with `w² = Aw + B`, so `disc(c) = A² + 4B`.
  - The integral basis, reindexed to `Fin 2`, is `c ᵥ* P` with `P = c.toMatrix b'`. Then
    `discr K = det(P)² (A² + 4B)` (`Algebra.discr_of_matrix_vecMul`).
  - Take `δ = det(P)(2w − A)`.

## 2. The printed leaf (`GrossZagierCdPrinted.lean`, namespace `ZInQ.GZCdPrinted`)

`GZPrintedBody E N f X sX ι` is h33-d1's `GZSplitBody` (eps-splitting's binders) with three changes:

| `GZSplitBody` (h33-d1 / eps-splitting) | `GZPrintedBody` (gzcd-s1) |
| --- | --- |
| `∀ p, IsCuspInfty N ι p → π p ∉ (chartZ E).opensRange` | `∀ p, IsCuspInfty N ι p → π p = H33D1.ptO E` (`π(∞) = O`) |
| `∀ K …, finrank ℚ K = 2 → ∀ δ : K, δ ^ 2 = D → …` | `∀ K …, finrank ℚ K = 2 → NumberField.discr K = D → …` |
| `∀ ιK : K →ₐ[ℚ] ℂ, ιK δ = I √(−D) → …` | `∀ ιK : K →ₐ[ℚ] ℂ, …` (any embedding) |

Everything else is verbatim:
- `π : X ⟶ ESch E` over `ℚ`, nonconstant;
- `D`, `β`, `IsOddImagFundDisc D`, `D < −4`;
- every `p ∣ N` with `IsSplitIn K p`, and `4N ∣ D − β²`;
- the Heegner points `IsHeegnerPointReps`, `IsPointAt`;
- `n ≠ 0` and `ιK(y) = n • Σ_r ptOf E (x_r ≫ π)`;
- the entire continuations `F` of `L(f, s)` and `G` of `L(f ⊗ quadChar K, s)`;
- the conclusion `∃ κ > 0, (FG)'(1) = κ ĥ(y)`.

`GrossZagierCurveAtPrinted E` asks for **some** model:
`∃ X, IsIntegral, sX, IsProper sX ∧ IsNormalScheme X ∧ dim X = 1 ∧ ∃ ι, GZPrintedBody …`.
`GrossZagierCurveCdPrinted` restricts `E'` to the short models in the isogeny class of `C_d`, as before.

Proofs (all VERIFIED):
- `exists_sqrt_embedding`: if `δ₀² = D < 0`, then any `ιK` sends `δ₀` or `−δ₀` to `i√|D|`.
- `gzPrintedBody_iff : GZPrintedBody ↔ GZSplitBody` on every model. It uses `discr_eq_of_sq` in one direction,
  `exists_sq_eq_discr` with `exists_sqrt_embedding` in the other, and `not_mem_chartZ_iff` for the cusp.
- `grossZagierCurveCdPrinted_iff : GrossZagierCurveCdPrinted ↔ GZSplitUnique.GrossZagierCurveCdSplitSome`.
- `grossZagierCurveCd_iff_printed`. It goes through h33-d1's `grossZagierCurveAtSplitSome_of_all` and
  `grossZagierCurveCdSplit_of_some` (model uniqueness), and eps-splitting's `grossZagierCurveCd_of_split` and
  `grossZagierCurveCdSplit_of_curveCd`.
- `grossZagierAlgOptCd_of_printed`: through hgz-steps' `grossZagierAlgOptCd_of_curve`.

## 3. Rating of `GZCdPrinted.GrossZagierCurveCdPrinted`

**LEAF, printed form (direct instance)** (SPECULATIVE until a statement check, since this host has no copy of GZ).

- **It is the print's statement.** Gross–Zagier I.6.3 / V §2 Thm 2.1 (UNVERIFIED locators; queue9 reading of V §2,
  p. 310), item by item:

  | print | leaf |
  | --- | --- |
  | `K` an imaginary quadratic field of discriminant `D` | Mathlib's `NumberField.discr` |
  | every prime dividing `N` splits in `K` | Mathlib's `primesOver` |
  | `ε` the quadratic character of `K` | `quadChar K` |
  | `π : X₀(N) → E` a modular parametrization with `π(∞) = 0` | a nonconstant morphism of `ℚ`-schemes with `π(∞) = O` literally |
  | the Heegner points | the `ℂ`-points `τ_r` |

  `X₀(N)` is a normal proper model of `ℚ(j, j_N)`.
- **It is not stronger than the print.**
  - It asks for one model (the canonical one) where the print has the canonical model. This is weaker.
  - "Any embedding `ιK`" is equivalent to the fixed one (`exists_sqrt_embedding`, Lean).
  - `∃ κ > 0` and `y = n y_K` weaken the print.
  - The whole leaf is equivalent in Lean to hgz-steps' `GrossZagierCurveCd`, which was rated not stronger. It is
    also equivalent to h33-d1's `GrossZagierCurveCdSplitSome`.
- **It is not vacuous.** hgz-steps' bridge constructs every hypothesis (model, `π`, cusp, points `τ_r`) from the
  older data. A field `K` with `discr K = D` exists, `ℚ(√D)` (`discr_eq_of_sq`).
- **Its definitions are genuine.** The scheme objects are `Proj`, Mathlib's `IsProper`, and Tau Ceti's L-series and
  canonical height. There is no structure invented for the purpose.

**Readings, not Lean steps:**
1. **The canonical model** `X₀(N)_ℚ` with `ι : K(X) ≃ ℚ(j, j_N)` (Shimura 1971 §6.7, UNVERIFIED). Every model is
   isomorphic to it compatibly with `ι` (Lean: model uniqueness).
2. **The point `τ`** (`IsPointAt`, the uniformization `ℍ → X₀(N)(ℂ)` read through `q`-expansions). It is unique
   on every model (`isPointAt_unique`, Lean).
3. **G10, the normalization of `ĥ`.** `y.canonicalHeight` is Tau Ceti's `lim h(x(2ⁿ y))/4ⁿ` over `K`
   (`Contrib/TauCeti/.../CanonicalHeight/Basic.lean`, VERIFIED read). Gross–Zagier's `ĥ` may differ by a fixed
   positive factor: 2 for `h(x)` against `½ h(x)`, or `[K : ℚ]` for relative against absolute heights
   (Silverman VIII.9, STANDARD). Any such factor is absorbed by `∃ κ > 0`. The statement is unaffected as long as
   Tau Ceti's height is a positive multiple of the Néron–Tate height, which is the definition (SPECULATIVE about
   GZ's exact convention; no copy here).

**Count.** `hGZ` goes GLUE → LEAF, **GLUE −1, no new glue**. Proposed kinds row: `scratch/gzcd-s1/kinds-row.tsv`.

## 4. Fold (manual: `hGZ` is a binder of `frozenTarget`, not a bundle field)

Two options:
- **(a) No edit.** Keep `(hGZ : ZInQ.GZSch.GrossZagierCurveCd)` and rate it LEAF by `grossZagierCurveCd_iff_printed`.
- **(b) Retype.** In `ZInQKernel/OneProof/Main.lean`:
  - add `import ZInQKernel.Contrib.OneProof.GrossZagierCdPrinted`;
  - replace `(hGZ : ZInQ.GZSch.GrossZagierCurveCd)` by `(hGZp : ZInQ.GZCdPrinted.GrossZagierCurveCdPrinted)`;
  - replace the use `hGZ` by `(ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed hGZp)`.

Option (b) is checked in `scratch/gzcd-s1/FoldCheck.lean`. `ZInQ.GZCdPrinted.frozenTarget_printed` is
`frozenTarget` on the current top (`sixContactMin_of_open63`, bundles `OpenResearchLeaves44`,
`OpenTextbookLeaves17`, `OpenAddedLeaves26`) with that binder. `frozenTarget_printed_eq` shows by `rfl` that it is
the old theorem applied to the bridge.

`#print axioms` (VERIFIED, `FoldCheck-output.txt`) gives `[propext, Classical.choice, Quot.sound]` for each of:
- `frozenTarget_printed` and `ZInQ.OneProof.frozenTarget`;
- `grossZagierCurveCd_iff_printed` and `grossZagierAlgOptCd_of_printed`;
- `GZDiscr.discr_eq_of_sq` and `GZDiscr.exists_sq_eq_discr`;
- `CurveModel.exists_iso_of_functionField`, `GZUnique.model_transfer` and `H33D1.not_mem_chartZ_iff`;
- `EpsSplit.quadChar_eq_epsD`.

The autofold spec is `scratch/gzcd-s1/autofold.json`: field `hGZ`, one published leaf with kind and flag. autofold.py
folds only `HDec.HSyn` bundle fields, so the spec's note gives the manual edit. It supersedes h33-d1's `hGZ` spec
(the leaves are equivalent).

## 5. Checks (VERIFIED)

- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.GrossZagierSplitUnique ZInQKernel.Contrib.OneProof.GrossZagierModelUnique`
  after the merge: no errors (`build1.txt`, 52 min, from a stale `.lake`).
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.GrossZagierCdPrinted`:
  "Build completed successfully (16091 jobs)" (`build3.txt`).
- Both new files also compile under `lake env lean` with no errors and no warnings.
- `FoldCheck.lean` and `Discharges.lean`: outputs as in §0 and §4.
- The new files contain no `sorry`, no `axiom`, and no `#eval`, `run_cmd`, notation or macros. Sizes are 9.7 KB and
  7.5 KB.
- The only files added under `ZInQKernel/` are the 8 merged from h33-d1 and the 2 new ones. No file was modified.

## 6. What remains

- The integrator's choice between options (a) and (b) in §4, and a statement check of the printed leaf against GZ
  (I.6.3, V §2 Thm 2.1), including G10.
- No Lean step is left in `hGZ`.
