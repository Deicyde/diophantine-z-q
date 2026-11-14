
Notes on the table. The vacuity caution of leaf-fold6 §2.1 still applies to R19, R20, R22 and `h5fin`: they are
stated over `stableFaltingsHeight`. Every field not marked "folded by leaf-fold7" has leaf-fold6's type; the build
checks this, since `sixContactMin_of_open7` passes those fields unchanged to `sixContactMin_of_open6`.

**Flagged for a human check.** New in this fold:
- `igusaPsi4`, `igusaChi10`: Igusa defines `ψ₄` as an Eisenstein series and prints the theta expression as a
  theorem (qm-split).
- `shimuraFamily`: the reading "for every `π`" needs a GAGA-level composition step (qm-split). Lemma QP enters as
  for `r1r2`.
- `shimuraTaniyamaQbar`: the model is stated over `ℚ̄`, as in Milne's form; Shimura–Taniyama print a number field
  (qm-split).
- `yuThm11`: the simple/non-simple labels are dropped, which makes it weaker.
- `deRhamH1AbVarT`: `H¹_ét` is written as `Hom(V_p A, ℚ_p)`. `hodgeTateDecompAbVar` chooses bases.
  `dsThm965` extends coefficients along `ι_L ∘ ι_C⁻¹` (hodge-split §3).
- `uniformizationLeafAll`, `gagaMorphism`: these are "coordinate forms" of Mumford §1 and of GAGA (bp-analytic §4,
  homlattice §3). That they count as leaves is SPECULATIVE.
- `geomConnOfRationalPoint`, `groupSchemeEquidim`: specializations of Stacks 04KV and of SGA 3 VI_A 2.4, with
  locators UNVERIFIED.

Still open from leaf-fold6: `ShimuraGoodReduction` (level 3 at `3 ∣ D`, now in its guard-free form),
`ValenceFormulaGammaStar`, `R1R2fpRep`, `RaynaudCriterion` (the case `m = 3`).

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields; `?` marks a field that is not in published form (c or comp). The grouping is a
reading of the docstrings, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves and QM abelian surfaces** (Shimura 1967, 1971; Shimura–Taniyama; Deligne; Baba–Granath; González–Rotger; Yu; Kurihara; Elkies; Takeuchi; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard) | 14 (11) | `r1r2`?, `shimuraFamily`?, `r1rec`?, `r3`?, `r5`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `valenceFormulaGammaStar`?, `qmHauptmodulBase3`?, `shimuraGoodReductionNoGuard`? |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa; Shimura 1976; Mumford, Tata II) | 3 (1) | `igusaPsi4`, `igusaChi10`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** (Mumford; Milne; Birkenhake–Lange; Conrad; Serre GAGA) | 10 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t11bExists`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate; SGA 7; Raynaud) | 7 (3) | `r6`?, `r7a`, `r7b`?, `r8`?, `t3Surj`, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme` |
| **C′. Schemes and group schemes over a field** (EGA III₁ 4.3; EGA IV 8.8, 8.10, 17.7; Cartier; Stacks 04KV, 00TV; SGA 3 VI_A) | 8 (0) | `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_8_10_5_xii`, `egaIV_17_7_8_ii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 8 (5) | `r9a`, `r9b`, `r18`?, `r19`, `r20`?, `r21`?, `r22`?, `h5fin`? |
| **E. p-adic Hodge theory** (Tate 1967; Ax–Sen–Tate; Fontaine; Faltings; Scholze; Pan; Berger) | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** (Deligne; Deligne–Serre; Diamond–Shurman; Kato; Carayol; Shimura; Atkin–Li) | 7 (5) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r15`?, `r16`?, `r17`?, `t24`? |
| **G. Algebraic and modular curves** (Weil; Milne JV; Stacks; Shimura 1971; Igusa 1959) | 5 (2) | `t33`, `dimJacobianEqGenus`?, `genusX1Field`?, `normalModelOfFunctionFieldQ`, `igusaGL2` |
| total | **68 (30)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold6 §3:
- Group B gained the published Mumford and Milne statements and lost every consequence row except `t10` and `t09`.
- Groups C′ and E are now entirely in published form, apart from Pan–Berger.
- In group G only `dimJacobianEqGenus` and `genusX1Field` are composites; `curveBijIso` was proved and
  `normalCurveSmoothQ` replaced.
- Group A holds most of what remains: the moduli of the Shimura curve. It needs abelian schemes over a base or a
  coarse comparison (curve-split §3.6, qm-split §3).

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base build.** On the base, `lake build +ZInQKernel.OneProof.Main` rebuilt the chain LPrefix…TailO, about 15
  min, because some kernel modules it imports were out of date in this worktree.
- **Hashes before.** `DumpCompact` gave 8594 OneProof constants (`hashes_before.txt`) and the frozenTarget type
  (`frozenTarget_before.txt`).
- **New modules.** `lake build ZInQKernel.OneProof.H.TailP`, then Q, R, T (with S), U, W, V and X, compiled one at a
  time; each took 8–71 s. All the split tasks' files compiled unchanged in the new environment. The exceptions are
  the documented edits, checked by `verbatim_check7.py` (`verbatim_check7_out.txt`):
  - the mul-rigidity copy in TailQ, 166 lines, replaced by the kernel import of the same text;
  - the GENERATED banner line of av-glue's `Combined.lean`;
  - the imports of TailR, merged into one header.

  Apart from those, every source line appears unchanged and in order. The only added lines are banners,
  `section`/`end` wrappers, the reopened header of TailT, and the reopened namespace of TailW.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** `DumpCompact` gives 9953 constants. `cmp_hashes.py`: 0 removed, 1 changed (`frozenTarget`),
  1359 new, all in TailP–TailX.
- **Check7.lean.** The kernel conclusion, the closure (186 483 constants, no `sorryAx`), and the head constant and
  declaring module of all 69 fields (`check7_result.txt`).
- **Module sizes.** TailP 63 KB, TailQ 125 KB, TailR 85 KB, TailS 110 KB, TailT 103 KB, TailU 114 KB, TailV 8 KB,
  TailW 48 KB, TailX 18 KB. Each is under 150 KB.

**No statement of a leaf, row or glue Prop was changed.** Every field that was not folded keeps its type. Every
folded field is filled by a compiled theorem whose conclusion is the old field's constant, either directly or after
the transports of §1.1.

## 5. Not folded, and why

Decision rule. A fold is taken only if neither the strict GLUE count nor the lenient GLUE count rises, and if it
does one of the following: lowers the strict GLUE count; replaces a consequence or composite by published-form
leaves; or replaces a GLUE field by a strictly smaller statement of the same form, with no new field. The third
case covers `quotientP1Coordinate`, `eigenformHTNew` and `shimuraGoodReductionNoGuard`.

- **height-split, all rows** (H-14 `r18`, H-15 `r19`, H-16 `r20`, H-17 `r21`, H-18 `r22`, H-19 `h5fin`, H-3
  `r5count`).
  - Every route goes through the identification `IsStableFaltingsHeight ↔ stableFaltingsHeight`, which needs SS1
    and SS2. height-split itself calls these consequence-level forms: the global form of SGA 7 IX 3.6 and the
    open-subgroup form of IX 3.3.
  - Example: `r22` (c) would become `PazukiCor13Upper` (published) plus SS1 (c) and SS2 (c). N1 follows from the
    existing `neronSchemeExtensionExists`. The strict GLUE count rises.
  - Folding `r20` and `r22` together leaves the strict GLUE count at 2: SS1 and SS2 replace them, and the field
    count rises by 4.
  - `r18`, `r21` and `h5fin` also need the four glue Props of `HeightGlue`. `r19` is already in published form.
  - `r5count` would need the glue `QMPairEmbeddingCorrespondence` beside the Eichler leaf.
- **mcr-glue's full split.** It is six leaves (L1–L6, three of them composites) plus the glue A, B, C1, C2, so the
  glue goes from 1 to 4. Only the step to `QuotientP1Coordinate` was taken.
- **qm-split, not taken:**
  - H-44 `thetaRatiosAlgebraic`: replaced by a published leaf plus a smaller composite. One more field, no GLUE
    count lowered.
  - H-87 `valenceFormulaGammaStar` and H-88 `qmHauptmodulBase3`: need the project glue `GammaStarFromO1` and the
    number `ThetaQuotientValue24`, so the lenient GLUE count rises.
  - H-1 `r1r2`, H-43 `x6ConicModel`, H-59 `y3Connected`: the per-witness glue props would replace one composite
    by a leaf plus glue.
- **curve-split, H-79 `genusX1Field`.** Only `dim J₁(N) ≤ N²` is used, but that use lives in existing modules: E2
  in `TailD` and `javanpeykarJ1` in `LPrefix` consume `OpenTextbookLeaves4.t34 : DimJ1Genus`, an equality. A bound
  cannot fill that field, so the fold would mean restating the chain above E2. Besides, curve-split's replacement
  `RiemannHurwitzQj` is itself a composite, so the count is neutral.
- **curve-split, H-83:** cannot be stated in published form today; only its guard clause was dropped.
- **av-split H-53 `t09SymmIsogenyExists` and H-78 `dimJacobianEqGenus`:** not splittable over Mathlib (no dual
  abelian variety, no `H¹(X, 𝒪_X)`).
- **hodge-split H-9 `r11r12`:** Pan's and Berger's theorems need `B_st`, which Mathlib does not have.
- **Duplicated definitions that remain.** The new fields are declared in OneProof modules. The av-split, av-glue
  and curve-split pieces are kernel-only, so a PR could move them to `ZInQKernel/Contrib/` unchanged. The copies
  `AVGlue.WeilPairing.IsogenyQuasiInverse`, root `WeilPairing.IsogenyQuasiInverse`, root `ModelGlue.CurveBijIso`
  and hodge-split's G9 rows are verbatim copies of chain rows; `TailX` and `TailV` identify each with the chain's
  row, by unfolding or by the transports. No FaithCheck was needed, since no HDec copy was deleted.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.** Removed: `r : OpenResearchLeaves5`, `t : OpenTextbookLeaves6`, `l : OpenAddedLeaves6`,
`g : OpenGlue6`. Added: `r : OpenResearchLeaves7`, `t : OpenTextbookLeaves7`, `l : OpenAddedLeaves7`,
`g : OpenGlue7`. The six TYZ and GZ hypotheses are unchanged.

**Fields removed (26):**
- research: `r1b`, `r4`, `r10`, `r13`, `r14`;
- textbook: `t4`, `t5`, `t8`, `homLatticeCorr`, `t23`, `t27`, `t35`, `normalCurveSmoothQ`,
  `geomConnectedOfConstantFieldQ`, `x0Transitive`;
- added: `cmOptimalEmbedding`, `qmClassNumberOne`, `senTwist`, `finiteImageHT`, `isogenyQuasiInverse`,
  `qmAutCard`, `alFixedPoints`, `stQM`, `shimuraGoodReduction`, `curveBijIso`;
- glue: `modelCoordinateResidue`.

**Fields added (27):**
- research: `shimuraFamily`, `igusaPsi4`, `igusaChi10`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`,
  `eigenformHTNew`, `dsThm965`, `dsThm966`;
- textbook: `mulEtaleAbelianScheme`, `mumfordTorsionAlgClosed`, `poincareComplement`, `cartierSmooth`,
  `geomConnOfRationalPoint`, `groupSchemeEquidim`, `uniformizationLeafAll`, `gagaMorphism`, `bdRInvariants`,
  `yuThm11`, `regularSmoothPerfect`, `igusaGL2`;
- added: `qmCentralizerCMC`, `tateTwistInvariants`, `axSenTate`, `milneIsogenyQuasiInverse`,
  `shimuraTaniyamaQbar`, `shimuraGoodReductionNoGuard`;
- glue: `quotientP1Coordinate`.

Three removed fields are proved outright, with no replacement: `curveBijIso`, `qmClassNumberOne`,
`geomConnectedOfConstantFieldQ`. The last follows from the existing field `zariskiConnectedness`.
