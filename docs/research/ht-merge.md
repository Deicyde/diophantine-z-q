# ht-merge: one leaf `ScholzeH1AbVar` in place of `ScholzeDeRhamAlg` + `HodgeNumberH1AbVar`

Task ht-merge, 2026-11-17. Base `wip/ht-merge` = `origin/wip/ht-abvar` (8344578f6) with `origin/main` (d435851d2) merged
(no conflicts). Results log: `scratch/ht-merge/log.md`. This is model work; no person has reviewed it.

Labels: **VERIFIED** means compiled, computed, or read in a named file on this host. **STANDARD** means published, with
the reference given. **SPECULATIVE** means not checked. Locators given from memory are marked UNVERIFIED (no network).

## 0. Result

1. **The merge is allowed** (VERIFIED, §1). `DeRhamScholze.ScholzeDeRhamAlg` is applied in exactly one place,
   `DeRhamScholze.dual_deRham_of_scholze` (`DeRhamScholze.lean` L325, `hS p F A.X 1`: an abelian variety over a finite
   `F/ℚ_p`, degree 1). Every other user reaches it only through that theorem.
2. **One leaf, with Lean proofs of everything else** (VERIFIED, standard axioms, §3, §4):

   ```lean
   def DeRhamScholze.HTMerge.ScholzeH1AbVar : Prop :=
     ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
       (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
       IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
         finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g
   ```

   In words: for an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`, `H¹_ét(A_{F̄}, ℚ_p)` is de Rham, the Hodge
   filtration of its `D_dR` has its jumps in `[0, 1]`, and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p]·g`. These are the Lean objects
   of the two old leaves. From it and `T10_TateDuality` (unchanged), the four theorems that used the old pair are
   re-proved with the same conclusions, and the old pair implies the new leaf (`scholzeH1AbVar_of_old`).
3. **Abelian surfaces or general `g`** (§2). Every end consumer applies the leaf only to abelian surfaces: G9 applies R10
   at `A'` with `A'.dim = 2`. The intermediate statements are stated for every `g`, though: the H field
   `hodgeTateDecompAbVar` (`TailS.lean` L347), the amended R10 that it feeds, and the four theorems that part (3) of the
   task keeps unchanged. A `g = 2` leaf cannot prove them. So the leaf of the fold is stated for every `g` and labelled a
   **generalization (on-the-spot)**, as the task prescribes when a consumer needs general `g`. The consumer that needs
   it is the H field `hodgeTateDecompAbVar` as stated, and R10 above it. The manuscript-exact form `ScholzeH1AbSurf`
   (`g = 2`, `dim Fil¹ = 2[F:ℚ_p]`) is also stated. It follows from the general leaf, and it alone proves the H field
   for every abelian surface (`hodgeTateDecompAbSurf_of_scholzeH1AbSurf`). §2.3 lists what a `g = 2` fold would have to
   change.
4. **Net change** (VERIFIED with `scratch/ht-merge/count.py` on `kinds.tsv`): the H rows of the joint fold go from
   **5/27 on 32** (ht-abvar's spec) to **5/26 on 31**, one row and one GLUE fewer. Against the current top (5/24 on
   29), the joint fold is +2 GLUE instead of +3. Consumer (iii) now costs +1: `hodgeTateDecompOr` leaves, while
   `scholzeH1AbVar` and `t10TateDuality` enter. Frozen-target's `hPC` row (from main) is unchanged by both specs.

## 1. Part (1): who uses `ScholzeDeRhamAlg` (VERIFIED by grep over every `.lean` file in `ZInQKernel/` and `scratch/`)

| declaration | file | how it reaches `hS` |
|---|---|---|
| `dual_deRham_of_scholze` | `DeRhamScholze.lean` L317-330 | `obtain ⟨h1, h2⟩ := hS p F A.X 1` (L325), `A : PkgI4.I3.AbVar F`, with `IsProper`, `Smooth` from `A.proper`, `A.smooth` |
| `isDeRhamTensorOver_of_scholze`, `deRhamVpAbVarDirect_of_scholze`, `deRhamVpAbVarDirect_of_leaves`, `lemDeRhamDescent_tate` | `DeRhamScholze.lean` L332-417 | through `dual_deRham_of_scholze` |
| `hodgeTateDecompHom_of_scholze`, `hodgeTateDecompOr_of_scholze`, `hodgeTateDecompOr_of_leaves` | `DeRhamScholze.lean` L382-405 | through `dual_deRham_of_scholze` |
| `TT.hodgeTateDecompOr_of_scholzeMilne` | `DeRhamScholzeT.lean` L240 | through `hodgeTateDecompOr_of_leaves` |
| `HTAbVar.hodgeTateDecompAbVar_of_scholze` | `HTAbVarScholze.lean` L43 | through `dual_deRham_of_scholze` |
| the dry runs and specs of derham-scholze and ht-abvar | `scratch/derham-scholze/`, `scratch/ht-abvar/` | pass the field to the theorems above |

No consumer uses another `X` or another degree, so the merge goes ahead.

## 2. Part (2): which abelian varieties the consumers need

### 2.1 The route (VERIFIED by reading the files named)

* **`deRhamVpAbVarDirect`** is a LEAF row (Berger 2004 §II.5.1, `kinds.tsv` L8). derham-scholze's discharge of it is not
  on ht-abvar's dry-run route, so in the joint fold the new leaf feeds only `hodgeTateDecompAbVar`.
  `deRhamVpAbVarDirect_of_scholzeH1` is re-proved anyway (part 3), as an alternative supplier.
* **`hodgeTateDecompAbVar`** (`TailS.lean` L347, every `g`) goes into `deRhamComparisonHT_of_leavesT` (`TailS.lean` L2059).
  That gives `r10 : ZInQ.Contrib.R10.DeRhamComparisonHT` (every `A`), at `scratch/ht-abvar/HTDryRun.lean` L626
  (`HTMergeDryRun.lean` L627; the line numbers in this list are HTDryRun's, one more in HTMergeDryRun). `r.r10` is read at:
  * L686, `g8_g12_hf_pz` (`PicZeroCharZeroCopy.lean` L815), which passes it to `g8_g11_hf`;
  * L720, `g8_g11_hf` (`HomFreeFiniteAlgClosedReroute/Consumers.lean` L553), which uses it only as `h9g hR10 K A ℓ r e hdim …`;
  * L688, `C8Conrad.g12DetPZ_of_inputs`, which leads to `g12DetPZ_of_twistFinite` (`C8Conrad.lean` L179); that uses it only as
    `h9 hdR K A 5 r e hdim hint`;
  * L784/L791, `g9Glue_of_deRhamComparisonHT` and `g9GlueNoT23_of_deRhamComparisonHT` (`TailE.lean` L6388-6395).
* **The end consumer is G9.** `G9Glue` and `G9GlueNoT23` (`TailA.lean` L2007, L2017) both carry the hypothesis
  `A.dim = 2`. Their proof `g9GlueNoT23_of_fieldEmb` (`TailC.lean` L14121) applies R10 as `hR10 ℓ F A' 2 (hdim')` and
  R10's weight clause as `hW ℓ F A' w`. Here `A'` is the base change of the abelian surface to a completion, with
  `A'.dim = 2` (`localModel_of_abVarBaseChange`, `TailC.lean` L14390).
* **Manuscript.** Step C3 (L728-737) applies `lem:de-rham-descent` to the QM abelian surface. The lemma (L10939-10941)
  is stated for an abelian surface `A/F`, and its Hodge numbers are "`2,2`" (L10996).

### 2.2 Conclusion

Every end consumer needs only abelian surfaces. Every intermediate statement between the leaf and G9 quantifies over
every `g`:
* the H field `hodgeTateDecompAbVar`;
* `deRhamComparisonHT_of_leavesT`;
* R10 and the bundle field `r10 : PkgI4.DeRhamComparisonHT` of `OpenResearchLeaves5EB` and its successors;
* the hypothesis `hR10 : PkgI4.DeRhamComparison` of `G9Glue`, `G9GlueNoT23`, `g8_g11_hf`, `g8_g12_hf_pz` and
  `g12DetPZ_of_*`.

The four theorems of part (3) also quantify over every `g`. A leaf for `g = 2` therefore cannot prove them with their
statements unchanged, and it cannot fill the field at ht-abvar's swap point either. The leaf of the fold is stated for
every `g`, labelled a generalization (on-the-spot) in its docstring, its flag (`autofold.json`) and here (§6). The
consumer that needs general `g` is the H field `hodgeTateDecompAbVar` as stated, through R10.

### 2.3 What a `g = 2` fold would change (not done here)

To fold the manuscript-exact `ScholzeH1AbSurf` instead, every statement listed in §2.2 would have to be restricted to
dimension 2:
* the field type of `hodgeTateDecompAbVar` in `OpenResearchLeaves35EBCF` and its successors;
* the bundle field `r10`;
* the `hR10` binders of the G8-G12 copies.

That is a copy reroute of the generated body (c8-conrad2's generator), with consumer statements changed. It saves no
row: the leaf count is the same, and only its scope narrows. It is recorded as an option for the integrator. Its Lean
core is already here: `hodgeTateDecompAbSurf_of_scholzeH1AbSurf : ScholzeH1AbSurf → T10_TateDuality →
HodgeTateDecompAbSurf`, where `HodgeTateDecompAbSurf` is the H field with `g := 2`, verbatim otherwise.

## 3. The leaf

### 3.1 Statement and tags

`DeRhamScholze.HTMerge.ScholzeH1AbVar` (§0). The objects are derham-scholze's:
* `HQ`, `rhoH`: Mathlib's pro-étale `Scheme.EllAdicCohomology` of `A ×_F Spec F̄` in degree 1, tensored with `ℚ_p`,
  with `σ` acting by transport along `1 × Spec(σ⁻¹)` (t10-etale's `galH`, `galHX_abVar`);
* `IsDeRhamFam`: `D_dR = ddrFam`, with `dim_{ℚ_p} D_dR = [F:ℚ_p]·dim W`;
* `HodgeRange … 1`: `Fil⁰ D_dR = D_dR` and `Fil² D_dR = 0`;
* `filD`: `Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)`.

None of these objects was invented for the purpose.

| tag | content |
|---|---|
| (a) manuscript | `lem:de-rham-descent` (L10939-10951, abelian surface `A/F`). Scholze's comparison, applied in L10954-10965: "Apply \cite[Corollary 1.8]{scholze2013}, with the corrections in \cite{scholze-erratum}" (L10955-10956), with Thms 9.1 (filtered de Rham hypercohomology) and 9.3, and "Thus `H¹_ét(A_{F̄}, ℚ_ℓ)` is de Rham" (L10964-10965). Hodge numbers: "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`" (L10996, uncited). Citation of the comparison in step C3: L735-737. |
| (b) print | Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), e1, Cor. 1.8 with Thms 9.1, 9.3 (bibitem L11010-11014), and the corrigendum, Forum Math. Pi 4 (2016), e6 (bibitem L11015-11018). Locators as read by the locator audit (`locators.md` row R10); not re-read here. |
| kind | **consequence** (Mathlib has no `H_dR` and no rigid-analytic spaces) |
| class | CITED (Scholze, L736-737, L10954-10965) with ELLIOT (Hodge numbers, L10996, uncited) |
| generalization | on-the-spot in `g` (§2.2, §6) |

### 3.2 Rating: not printed form

* **(a) Rigid-analytic spaces.** Cor. 1.8 is a statement about proper smooth rigid-analytic varieties, which Mathlib
  lacks. The leaf is the algebraic form that the manuscript derives through Thms 9.1/9.3, plus derham-scholze's two
  on-the-spot dictionary steps (`F̄` vs `ℂ_p`; pro-étale vs étale; derham-scholze §3.1, steps 3-4).
* **(b) No `H¹_dR` in Mathlib.** The Hodge numbers are therefore stated on the étale side of the filtered comparison
  `D_dR(H¹_ét) ≅ H¹_dR(A/F)`. Both the jump clause and `dim Fil¹ = [F:ℚ_p]·g` are images of facts about `H¹_dR` under
  that isomorphism: `Fil¹ H¹_dR = H⁰(A, Ω¹)` has dimension `g`.
* **(c) The leaf merges a cited print with an uncited manuscript sentence (L10996).** The class field records both.
  This is the price of the merge, which ht-abvar §6(a) flagged.
* **(d) General `g`** (§2).

The leaf asserts nothing beyond the print, the manuscript's Hodge-number sentence (with `h^{1,0} = g` for general `g`),
and these dictionary steps. It is not a disguised form of the conclusion: the steps from it to the Hodge–Tate
decomposition are proved in Lean (§4) by derham-scholze's and ht-abvar's glue:
* Milne transport;
* Fontaine's `gr D_dR ≅ D_HT` with dimensions (`hodgeTate01_dims`);
* Tate–Sen;
* `dim V_p A = 2g`.

### 3.3 Nothing lost

* `scholzeH1AbVar_of_old : ScholzeDeRhamAlg → HodgeNumberH1AbVar → ScholzeH1AbVar`: the first two clauses are
  `ScholzeDeRhamAlg` at `X = A.X`, `i = 1`, and the third is `HodgeNumberH1AbVar`.
* Conversely, `hodgeNumberH1AbVar_of_scholzeH1` gives ht-abvar's leaf back.
* The only content of `ScholzeDeRhamAlg` that the new leaf drops is other `X` and other degrees `i`, and no consumer
  uses either (§1).
* `hodgeTateDecompAbVar_of_old` recovers ht-abvar's theorem through the new leaf.

## 4. Part (3): the theorems re-proved (file `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean`)

The file imports `ZInQKernel.Contrib.OneProof.HTAbVarScholze`, and through it `DeRhamScholzeT`, `DeRhamScholze` and
`HTAbVarScholzeDims`. It does not import `ZInQKernel.OneProof.Main`, and it has no `sorry`.

| old theorem (leaves) | new theorem (leaves) | conclusion (unchanged) |
|---|---|---|
| `DeRhamScholze.deRhamVpAbVarDirect_of_scholze (hS) (hT) (hM)` | `HTMerge.deRhamVpAbVarDirect_of_scholzeH1 (hN) (hT) (hM)` | `DeRhamPrint.Direct.DeRhamVpAbVarDirect` |
| `DeRhamScholze.deRhamVpAbVarDirect_of_leaves (hS) (hT)` | `HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne (hN) (hT)` | same |
| `DeRhamScholze.hodgeTateDecompHom_of_scholze (hS) (hT) (hM) (hW)` | `HTMerge.hodgeTateDecompHom_of_scholzeH1 (hN) (hT) (hM) (hW)` | `HodgeTateOr.HodgeTateDecompHom` |
| `DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne (hS) (hT)` | `HTMerge.hodgeTateDecompOr_of_scholzeH1Milne (hN) (hT)` | `HodgeTateOr.HodgeTateDecompOr` |
| `DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze (hS) (hT) (hH)` | `HTMerge.hodgeTateDecompAbVar_of_scholzeH1 (hN) (hT)` | `HodgeSplit.HodgeTateDecompAbVar` |

Helpers:
* `dual_of_H1`: transport of the three clauses to `V_p(A)^∨` along `milneE`, for one `A`;
* `isDeRhamTensorOver_of_H1`;
* `htDecomp_of_H1`: ht-abvar's proof, pointwise in `A`;
* `dual_deRham_of_scholzeH1`: the conclusion of `dual_deRham_of_scholze`.

The `g = 2` forms are `ScholzeH1AbSurf`, `scholzeH1AbSurf_of_abVar`, `HodgeTateDecompAbSurf`,
`hodgeTateDecompAbSurf_of_abVar` and `hodgeTateDecompAbSurf_of_scholzeH1AbSurf`. The type checks are in
`scratch/ht-merge/Axioms.lean`: each old and new theorem is shown to have the same conclusion, and the H field is copied
verbatim and checked `Iff.rfl` against `TailS.lean` L347.

## 5. Part (4): compile log, `#discharges`, dry run, count

All on 11-17, with Lean 4.35.0 and Mathlib v4.35.0, over the merged base (main d435851d).

| check | outcome |
|---|---|
| `lake build ZInQKernel.Contrib.OneProof.ScholzeH1AbVar` | built (12341 jobs); `lake env lean` on the scratch copy reports no errors and no warnings |
| `scratch/ht-merge/Axioms.lean` (output `axioms-output.txt`) | the verbatim copy of `HodgeTateDecompAbVar` is `Iff.rfl` with TailS's; each old/new theorem pair has the same conclusion type (`example`s); all ten new theorems use `[propext, Classical.choice, Quot.sound]` |
| `scratch/ht-merge/Discharges.lean` (output `discharges_out.txt`) | `#discharges: 30 open hypotheses, 11762 theorems checked, 25 discharge one`; the new lines are below |
| `scratch/ht-merge/HTMergeDryRun.lean` (output `dryrun_out.txt`) | compiles with no errors; `ZInQ.OneProof.frozenTarget_hm`, `HDec.HSyn.sixContactMin_of_open73HM` and `sixContactMin_of_open72_hm` use `[propext, Classical.choice, Quot.sound]` |
| `scratch/ht-merge/count.py` | H rows: current 5/24 on 29; ht-abvar spec 5/27 on 32; **ht-merge spec 5/26 on 31** |
| `render_open.kinds_row_problems` on the new row | no problems (flag_class `pending-review,unverified-locator`) |

```
DISCHARGES [OpenResearchLeaves53.deRhamVpAbVarDirect] by DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne
  still assumes: [DeRhamScholze.HTMerge.ScholzeH1AbVar, T10Etale.T10_TateDuality]
DISCHARGES [OpenResearchLeaves53.hodgeTateDecompOr] by DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne
  still assumes: [DeRhamScholze.HTMerge.ScholzeH1AbVar, T10Etale.T10_TateDuality]
```

The 30 open hypotheses are the 29 H rows and main's `hPC`. `hodgeTateDecompAbVar` is not an open field, so its
theorem does not appear in `#discharges`. It is used at the hand-fold swap point instead.

**Dry run.** The body is ht-abvar's: c8-conrad2's generated copy, verbatim. The handwritten top is ht-abvar's with
three changes:
* the swap `hodgeTateDecompAbVar := DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1 hN hT`;
* the added bundle `OpenAddedLeaves28HM = {conradAppBQp, tateTwistInvariantsInertia, scholzeH1AbVar, t10TateDuality}`,
  which has four fields where ht-abvar's `OpenAddedLeaves28HT` had five;
* `frozenTarget_hm`, rewritten for main's new `Main.lean` (`(r t l) (hPC)` →
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`).

The field taint is unchanged from ht-abvar (`scratch/ht-abvar/dryrun_taint_out.txt`), because the swap points and the
removed rows are the same.

**Hand-fold spec.** `scratch/ht-merge/autofold.json` supersedes ht-abvar's spec. It has the same `handfold` swap,
`new_leaves` with `scholzeH1AbVar` (kind `consequence`, class CITED + ELLIOT, flag "pending review: … generalization
(on-the-spot) in g …") in place of `scholzeDeRhamAlg` and `hodgeNumberH1AbVar`, and the count noted above.

| | rows | LEAF/GLUE |
|---|---|---|
| current top (H rows) | 29 | 5/24 |
| ht-abvar's joint fold | 32 | 5/27 |
| **ht-merge's joint fold** | **31** | **5/26** |
| change against ht-abvar | −1 | −0/−1 |

## 6. On-the-spot steps

* **Generalization in `g`** (the only new one). The manuscript states the Hodge numbers `2,2` for the abelian surface
  (L10996). The leaf states `dim_F Fil¹ D_dR(H¹_ét) = g` for an abelian variety of dimension `g`. Sketch:
  * Scholze's filtered comparison (Cor. 1.8 with Thm 9.1, as the manuscript applies it for any proper smooth variety,
    L10954-10960) identifies `D_dR(H¹_ét)` with `H¹_dR(A/F)` as filtered `F`-spaces.
  * The Hodge filtration of `H¹_dR(A/F)` has `Fil⁰ = H¹_dR`, `Fil² = 0`, and `Fil¹ = H⁰(A, Ω¹_A)`, by Hodge–de Rham
    degeneration, which is STANDARD for abelian varieties in characteristic 0.
  * `Ω¹_A ≅ 𝒪_A ⊗ ω_A` is free of rank `g` and `H⁰(A, 𝒪_A) = F`, so `dim_F H⁰(A, Ω¹) = g` (Mumford, *Abelian varieties*,
    §4; locator UNVERIFIED).
  * For `g = 2` this is the manuscript's sentence.
* Inherited, unchanged: derham-scholze's dictionary steps (`F̄` vs `ℂ_p`; pro-étale vs étale). Also ht-abvar's proved
  glue: Fontaine's `gr D_dR ≅ D_HT` with dimensions, the transport of `Fil¹` along Milne, and Hom form → tensor form.
  All of it is in Lean.

## 7. Known issues

1. **The manuscript's lemma is for abelian surfaces; the route's statements are for every `g`** (§2). The end
   consumers (G9) use only `g = 2`, but the H field `hodgeTateDecompAbVar`, R10 and the theorems that the task keeps
   unchanged quantify over `g`. So the fold leaf is a generalization (on-the-spot) of the manuscript's sentence L10996.
   This is no gap in the manuscript: it is a mismatch between the manuscript's scope and the generality of the
   project's intermediate statements. A `g = 2` fold is possible only by restricting those statements (§2.3).
2. **The merged leaf mixes a cited print with an uncited manuscript fact** (ht-abvar §6(a)). Scholze's Cor. 1.8 is
   cited at L736-737 and L10955. The Hodge numbers (L10996) carry no citation. Before the merge each had its own row
   with its own class; now one row carries the class "CITED with ELLIOT". A reader must check both parts before the row
   can count LEAF, and as a consequence leaf it counts GLUE under autofold's rule whatever the reading.
3. Inherited from derham-scholze and ht-abvar, unchanged:
   * no rigid-analytic spaces and no `H_dR` in Mathlib, so the leaf is a consequence and not printed form;
   * Mathlib's `ℓ`-adic cohomology is pro-étale;
   * `t10TateDuality` (Milne) is unread;
   * `h^{1,0} = g` has no verified locator.
4. No known issue with Scholze Cor. 1.8 / Thms 9.1, 9.3 as the manuscript uses them (not re-read here; locators as in
   `locators.md` R10).

## 8. What remains

* The fold itself (integrator): c8-conrad3's handfold plus the (iii) swap of `scratch/ht-merge/autofold.json`, which
  supersedes `scratch/ht-abvar/autofold.json`. It needs `--allow-rise` or a ruling (net +2 GLUE on the H rows instead of
  +3).
* Readings: Milne Thm 12.1(a) (for `t10TateDuality`) and a locator for `h^{1,0}(A) = g`.
* Optional: the `g = 2` reroute (§2.3), if the integrator prefers the manuscript's scope to unchanged consumer
  statements. It saves no row.
