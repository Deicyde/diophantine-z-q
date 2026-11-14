
Notes on the table.
- `r1r2` is now the only carrier of R1(d) and R5 in the bundles. Its docstring already lists both (Deligne 1971
  Cor. 5.7; González–Rotger 2006 Thm 5.12), so its form, a composite, does not change.
- `r5count` (González–Rotger Prop. 5.6, a count of classes) does not follow from `r1r2`: no clause of the witness
  counts points.

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields. `?` marks a field that is not in published form (c or comp). The grouping is
leaf-fold8's, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** | 12 (7) | `r1r2`?, `shimuraFamily`?, `r3`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** | 9 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** | 11 (4) | `r6`?, `r7a`, `serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `neronSchemeModelExistsDVR`, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableReductionThm`?, `semistableNeronBaseChange`?, `semistablePersists`? |
| **C′. Schemes and group schemes over a field** | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** | 5 (3) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** | 3 (2) | `dimJacobianEqGenus`?, `genusX1Field`?, `igusaGL2` |
| total | **62 (21)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold8 §3:
- **Group A** lost R1(d) and R5 in field-of-moduli form, as consequences: they are now theorems of `r1r2`.
- **Group F** lost `r15` (Deligne–Serre's consequences), now a theorem of Deligne–Serre's printed theorem
  (modular-split).
- **Group C** traded two consequences (`r7b`, `r8`) for four published-form leaves, the local printed theorems of
  Serre–Tate, SGA 7 IX and BLR (reduct-split).
- **Group G** lost the Jacobian's existence and the normal model, both published and both proved by cloud worker
  W07.
