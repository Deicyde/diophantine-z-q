Notes on the table.
- Every field not marked "folded by leaf-fold8" has leaf-fold7's type. The build checks this, since
  `sixContactMin_of_open8` passes those fields unchanged to `sixContactMin_of_open7`.
- The vacuity caution of leaf-fold7 §2 (R19, R20, R22, `h5fin` over `stableFaltingsHeight`) is gone: those fields
  are theorems now.
- The new height leaves are stated over height-split's definitions `IsSemistable` and `IsStableFaltingsHeight`.
  Their non-vacuity is machine-checked only at the zero abelian variety (height-split §7); the torus and abelian
  parts are not exercised. SPECULATIVE: these are faithful renderings of Faltings' definition (Faltings 1983 §1;
  Deligne, Sém. Bourbaki 616), and height-split's independent review found no defect.

**Flagged for a human check.** New in this fold:
- `pazukiCor13Upper`: if Pazuki's level-2 coordinates are `θ[a;0](0, 2Ω)` rather than the classical
  `θ[a;b](0, Ω)`, the leaf (and the kernel row `R22_Pazuki` itself) overstates the print by about `log 4`
  (height-split §8, RISK 1). Unchanged from the row it replaces.
- `bostLowerBound`: the display is unread. The leaf is in Deligne's normalization, the weaker reading.
- `faltingsLemma5BC`: the operative source is Raynaud, Astérisque 127 VII Cor. 2.1.3 (UNVERIFIED).
- `igusaCMValue24`: one number, read off Lin–Yang's eqs. (2), (14) at the Baba–Granath CM value. Equivalent to
  the old glue; the manuscript cites exactly this.
- `valenceFormulaCocompactEq`: stated with Mathlib's invariant measure on `ℍ` and a genuine fundamental-domain
  predicate. Shimura and Rankin state it for `vol(Γ\ℍ)`.

Still open from leaf-fold7: `ShimuraGoodReduction` (guard-free form), `R1R2fpRep`, `RaynaudCriterion` (the case
`m = 3`), and the composites of §3.

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields; `?` marks a field that is not in published form (c or comp). The grouping is a
reading of the docstrings, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** (Shimura 1967, 1971; Shimura–Taniyama; Shimizu; Deligne; Baba–Granath; González–Rotger; Yu; Kurihara; Elkies; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard) | 14 (9) | `r1r2`?, `shimuraFamily`?, `r1rec`?, `r3`?, `r5`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa; Shimura 1976; Mumford, Tata II; Lin–Yang's Igusa vector) | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** (Mumford; Milne; Birkenhake–Lange; Serre GAGA) | 9 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** (BLR; Serre–Tate; SGA 7 IX; Raynaud) | 9 (6) | `r6`?, `r7a`, `r7b`?, `r8`?, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableReductionThm`?, `semistableNeronBaseChange`?, `semistablePersists`? |
| **C′. Schemes and group schemes over a field** (EGA IV 8.10; Cartier; Stacks 04KV, 00TV; SGA 3 VI_A) | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** (Faltings; Bost; Javanpeykar; Pazuki; Gaudron–Rémond) | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** (Tate 1967; Ax–Sen–Tate; Fontaine; Faltings; Scholze; Pan; Berger) | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** (Deligne; Deligne–Serre; Diamond–Shurman; Kato; Carayol; Shimura) | 6 (4) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r15`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** (Weil; Milne JV; Stacks; Shimura 1971; Igusa 1959) | 5 (2) | `t33`, `dimJacobianEqGenus`?, `genusX1Field`?, `normalModelOfFunctionFieldQ`, `igusaGL2` |
| total | **65 (26)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold7 §3:
- **Group D** went from 5 of 8 not in published form to 1 of 7. Faltings' Lemma 5 is the one left.
- **Group C′** lost three EGA rows, which are proved now. **Group B** lost T11(b), also proved.
- **Group C** gained SGA 7 IX's three semistable-reduction statements, as consequences in global form.
- **Group A** lost the valence and Hauptmodul composites. In their place it has the valence formula and Shimizu's
  covolume, both in published form.
- Most of what remains is in groups A and C: the moduli of the Shimura curve, and Néron/monodromy.

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base build.** On the base, `lake build +ZInQKernel.OneProof.Main` took 19 min. It rebuilt the kernel modules
  and the whole chain LPrefix…TailX, which were out of date in this worktree.
- **Hashes before.** `DumpCompact` gave 9953 OneProof constants (`hashes_before.txt`) and the `frozenTarget` type
  (`frozenTarget_before.txt`).
- **New modules.** Each was built with `lake build ZInQKernel.OneProof.H.X`, one at a time:
  - TailY 14 s, TailZ 13 s, TailZ2 14 s, TailZ3 14 s, all at the first try;
  - the six Contrib modules 11 s–3 min 38 s;
  - TailZ4 9 s, after one fix (`r18_lf8`/`r22_lf8`, §1.1);
  - TYZSplit 31 s.

  `verbatim_check8.py` (`verbatim_check8_out.txt`) checks every copied slice: it appears unchanged, as one block,
  after the module's header, with only the `#print` lines dropped. It also checks that lines 37-2197 of
  `HauptGlue.lean` occur in `TailO.lean` in order. They form three contiguous blocks, matching Fold.lean's
  1-934/1326-2563 cut.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** `DumpCompact` gives 10831 constants. `cmp_hashes.py` reports 0 removed and 1 changed
  (`frozenTarget`). The 878 new constants are all in TailY–TailZ4 and TYZSplit.
- **Check8.lean** checks:
  - the kernel conclusion;
  - the closure: 193 116 constants, no `sorryAx`;
  - the head constant and declaring module of all 66 fields;
  - the axioms of the six Contrib proofs and of `tyzThm33Pinned_of_tyzThm33`.
- **Module sizes.** TailY 115 KB, TailZ 81 KB, TailZ2 80 KB, TailZ3 65 KB, TailZ4 15 KB, TYZSplit 29 KB. Each is
  under 150 KB.

**No statement of a leaf, row or glue Prop was changed.** Every field that was not folded keeps its type. Every
folded field is filled by a compiled theorem whose conclusion is the old field's constant, either directly or
through `r18_lf8`, `r22_lf8`, `t11bExists_lf8`. No HDec copy was deleted, so no FaithCheck was needed.

## 5. Not folded, and why

Decision rule (leaf-fold7 §5). A fold is taken only if neither the strict nor the lenient GLUE count rises, and if
it does one of the following:
- lowers the strict GLUE count;
- replaces a consequence or composite by published-form leaves.

- **H-3 `r5count` (height-glue `r5fpCount_of_t11b`).** The route is `R5fpCount` from
  `EichlerOptimalEmbeddingCount` (published), `T11b_Rigidity` (proved now, §1.1), `CMDescent` and
  `QMUniformizationC`. It does not qualify:
  - `QMUniformizationC`'s own docstring calls it "not one printed statement". It bundles Shimura's moduli
    statements for principally polarized surfaces, the algebraicity of QM tori, GAGA for homomorphisms, and the
    passage to the unpolarized `𝒪^×` form, so it is a composite.
  - `CMDescent` bundles Albert's classification with Shimura–Taniyama, so it is at best a consequence.
  - The fold would therefore replace one consequence by a published leaf, a consequence and a composite: strict
    GLUE +1, lenient GLUE +1.

  The proof compiles in height-glue's `QMFull.lean` and could be folded as soon as `QMUniformizationC` is split
  (height-glue §5 lists the pieces: T35, `T11a_RiemannEnd`, class number one, Riemann's algebraicity of QM tori,
  linear algebra of `M₂(ℝ)`).
- **qm-glue H-1 `r1r2`, H-43 `x6ConicModel` (`r1r2fpRep_of_canonical`, `x6ConicModel_of_canonical'`).**
  - In: the existential leaves `CanonicalModelY3` (a "qualified consequence", Lemma QP), `CanonicalCoarseX6`,
    `BabaGranathX6`, `GonzalezRotgerX6`, `ConicCanonical`.
  - Also in: the per-witness glue `ReciprocityOfFine` and the project glue `CoarseFactor`.
  - Out: one composite and one consequence.
  - The strict GLUE count would rise (−2 + 3), so this was not taken. Proving `ReciprocityOfFine` from an
    existential form through qm-split's `compare_iso`, and `CoarseFactor` (descent along a finite map, qm-glue
    §4.3), would make it pay.
- **qm-glue (c) H-44 `thetaRatiosAlgebraic`.** qm-glue found no further Lean reduction (it needs a polarization
  object in `PkgI3.AbVar`).
- **qm-split's final head (ead4b7dc).** Its `Haupt.lean` derives H-87/H-88 from the same leaves by an index
  argument (`…_of_O1`) instead of the proof of `GammaStarFromO1`. qm-glue's `HauptGlue.lean` was used, because it
  is the compiled file that also contains the `IgusaCMValue24` reduction. Both give the same three leaves.
- **TYZ T-5 `hS`.** Left as it is, as the task asked. tyz-split splits it into two GLUE Props, so no gain.
- **Duplicated definitions.**
  - `TailY` and `TailZ` contain height-glue's verbatim root-namespace copies of metrization2's kernel
    (`G0Dim`, `ZInQ.Metrization`, `ZInQ.Metrization2`) and of unif-dims' `JacDetDescends` chain. These are not in
    `ZInQKernel/HDecomp` or `Contrib`; the chain's copies are inside `HDec`, so nothing clashes.
  - `TailZ3` keeps qm-glue's copies of `Valence.lean`'s statements (`HDec.LeafQCheck.QMSplitVB`), which no other
    module has.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves7`, `t : OpenTextbookLeaves7`, `l : OpenAddedLeaves7`.
- Added: `r : OpenResearchLeaves8`, `t : OpenTextbookLeaves8`, `l : OpenAddedLeaves8`.
- `g : OpenGlue7` is unchanged.

**TYZ.**
- Removed: `h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ`.
- Added: `h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`.
- `h11`, `h29`, `hS`, `hL2`, `hL3` are unchanged.

**Fields removed (14):**
- research: `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin`;
- textbook: `t3Surj`, `t11bExists`, `t24`;
- added: `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii`, `valenceFormulaGammaStar`,
  `qmHauptmodulBase3`.

**Fields added (11):**
- research: `semistableReductionThm`, `semistableNeronBaseChange`, `semistablePersists`, `bostLowerBound`,
  `javanpeykarBound`, `faltingsLemma5BC`, `pazukiCor13Upper`, `gaudronRemondThm14`;
- added: `valenceFormulaCocompactEq`, `shimizuCovolumeO1`, `igusaCMValue24`.

Six removed fields are proved outright, with no replacement: `t3Surj`, `t11bExists`, `t24`,
`zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii` (cloud workers W03, W06, W08, W02, W01).
