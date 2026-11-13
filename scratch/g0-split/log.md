# g0-split results log

Files: `part_split.lean` (the new section, edited by hand); `build.sh` assembles `Split.lean` =
`scratch/h-decomposition/Leaves.lean` lines 1-18786 (everything before `HSyn`) + the body of
`scratch/glue-ssbc/SSBC.lean` (section `GlueSSBCSec`) + `Leaves.lean` lines 18787-19196 (HSyn §0-§3
through `TextbookLeaves`) + `part_split.lean` (replaces the old `glueOutputs_of_leaves` with its
`sorry`, and the three theorems after it). Check: `lake env lean scratch/g0-split/Split.lean`
(needs `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` first).

## Compile outcomes (VERIFIED)

- Setup: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`: OK (14 s).
- run1-run3 (first design, 9 pieces incl. `DescentToNumberField`): token `ι` reserved (renamed `emb`);
  `set` broke a dependent `φ` (replaced by explicit terms); then 0 errors, standard axioms.
- Soundness fix (not a compile error): the first `ModularConstituent` quantified over every
  number-field model `A/K` of the fibre and asked for `L ⊇ K` with `[L:ℚ] ≤ QM`. False for models over
  fields of degree `> QM` (base-change any model), so the reduction would have been vacuous. Fixed:
  the piece now *produces* the field `L'` and the model `A/L'` together (Glazer's `L'` contains the
  fibre field). `DescentToNumberField` dropped; `fibre_descent` replaced by `model_dim`.
- run4: 0 errors, no `sorry`; `glueOutputs_of_leaves` with 8 explicit hypotheses.
- run5: `javanpeykarJ1` (from leaf-push2's R18 transported + `X1BelyiOnModel` + T34): compiled first try.
- run6-run8: R22 block copied from leaf-push2 (`AbVar` ambiguous between `PkgI3` and `DefFaltings`:
  qualified); `PazukiOutput` is the hardened `x + 3` form, so R22 is applied at `X = max(1, x+3)` with
  `log π ≤ 3` (leaf-push2's `R22_plus3` argument). 0 errors.
- run9 (final, 19983 lines, 4m13s wall): 0 errors, no `declaration uses sorry`. `#print axioms`, all
  `[propext, Classical.choice, Quot.sound]`: `HSyn.glueOutputs_of_leaves`, `HSyn.sixContactMin_of_leaves`,
  `HSyn.G0Split.transfer_core`, `HSyn.G0Split.javanpeykarJ1`, `HSyn.G0Split.thetaPazuki`,
  `HSyn.G0Split.semisimpleBaseChange`.

## Main statement (VERIFIED, compiled)

```
theorem HSyn.glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves)
    (hR18 : R18_JavanpeykarConcrete) (hR22 : R22_PazukiConcrete)
    (hDim : DimBaseChange) (hBelyi : X1BelyiOnModel) (hSimp : FibreSimple)
    (hAdd : HeightAdditivity) (hBC : StableHeightBaseChange) (hProd : IsogenousProduct)
    (hThetaPt : ThetaPointOfFibre) (hMod : ModularConstituent) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul
theorem HSyn.sixContactMin_of_leaves (r) (t) (hR18) (hR22) (m : G0Split.MissingPieces) : ZInQ.SixContactMin
```

## Proved pieces applied (VERIFIED, compiled here)

| piece | from | glue step |
|---|---|---|
| `LeafQM.AV.exists_fibre_object` (existing) | R1-R2 (`r.r1r2`) | A4 |
| `G0Split.model_dim` (new) | `DimBaseChange`, `Scheme.homeoOfIso`, `IsHomeomorph.topologicalKrullDim_eq` | A dimension 2 |
| `ZInQ.DefFaltings.faltingsHeight_coe` (existing) | H5 (`r.h5.1`) | heights real |
| `G0Split.thetaPazuki` (new) | concrete R22 + `ThetaPointOfFibre` | G19 (F1 + F3) |
| `G0Split.hom_of_common` (new wrapper) | `PkgI3.E1_exists_hom_ne_zero`, R9a, R9b, T26, glue-ssbc | G17 (E1) |
| T8 `PkgI3.PoincareReducibility` (leaf `t.t8`) | — | G17 |
| `LeafModCurves.dim_J1_le` (existing) | T34 | E2, `g ≤ N²` |
| `G0Split.javanpeykarJ1` (new) | concrete R18 + `X1BelyiOnModel` + T34 | G18/E2 |
| `G0Split.transfer_core` (new) | R19, R20, R21 + `log_grKappa`, `one_le_grKappa` | E3-E4 numerics |
| `G0Split.semisimpleBaseChange` (copied proof) | glue-ssbc | E1's hypothesis |

## GlueOutputs fields -> step -> status

| field | step | status |
|---|---|---|
| `K'`, `z`, `Φ(z) = J(u)` | G19 F1 | missing piece 7 `ThetaPointOfFibre` |
| `PazukiOutput h(z) h_A` | G19 F3 | proved from concrete R22 (`thetaPazuki`) + piece 7's height comparison |
| `h_A` | stable Faltings height of `A` | `faltingsHeight A`, real by H5 |
| `1 ≤ N ≤ QM²` | G13-G16 | missing piece 8 `ModularConstituent` |
| `h_F(J₁(N)) ≤ 1.3·10⁷N¹²` | G18/E2 (R18) | proved from concrete R18 + piece 2 + piece 5 (base change) |
| `2 ≤ g` | G17 (`dim J = 2 + dim Z`) | missing piece 6 `IsogenousProduct` (dimension clause) |
| `g ≤ N²` | E2 | proved (T34) + piece 1 |
| `1 ≤ d` | `finrank_pos` | proved |
| `d ≤ QM` | G7 (B3) | missing piece 8 |
| `L ≤ GR bound` | E3 (R19) on G17's isogeny | proved (`transfer_core`) given pieces 3, 6, 8 and E1, T8 |
| `h_A + h_Z ≤ h_F(J) + L/2` | E4 (R20 + additivity) | R20 proved in; additivity = missing piece 4; base change = piece 5 |
| `-(3/2) g ≤ h_Z` | E4 (R21) | proved (`transfer_core`) with `dim Z ≤ g` from piece 6 |
| CM disjunct | not used (G6 NoCM) | — |
