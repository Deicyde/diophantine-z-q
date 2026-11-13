# H leaves inventory: `ResearchLeaves4` (24) and `TextbookLeaves` (35) in g0-assemble3's world

Agent h-leaves, 2026-11-13. Read-only. Repo `~/dzq-wt/frontier` (HEAD = b7cdba8e + 1 commit). Lean was not run.
Marks: **V** = VERIFIED (I read it in a Lean file, a report, or grep output at the commit named). **R** = REPORTED (a doc says so; I did not check the Lean).
Abbreviations:
- g0a3 = origin/wip/g0-assemble3 @357f5d9e: bundle `scratch/g0-assemble3/parts/z95_bundle4.lean` (last touched 7b21e1d6), flat `G0Assemble3.lean`, root-namespace `Leaves.lean`.
- LF = leaf-fold on HEAD: `scratch/h-decomposition/Leaves.lean`, `namespace HDec`, commit 54425895.
- LF2 = origin/wip/leaf-fold2 @b38ee0c4. AP = origin/wip/assemble-port @ff5537e3.
- K = `ZInQKernel/HDecomp/`. C = `ZInQKernel/Contrib/`.

## 0. Answer first

1. **Newer assembly on the HDec base (AP).** This answers the coordinator's question. AP's top theorem is (V, `scratch/assemble-port/parts/z99_bundle5.lean`, commit f5ba81ea):
   ```lean
   theorem HDec.HSyn.sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
       ZInQ.SixContactMin :=
     sixContactMin_of_leaves4 (researchLeaves4_of_open2 r) (textbookLeaves_of_open2 t) (gluePieces4_of_gluePieces5 r gp)
   ```
   - `OpenResearchLeaves2` (26 fields) and `OpenTextbookLeaves2` (18 fields) are LF2's bundles (AP part z98). `GluePieces5` has 41 fields.
   - Compile status (V, from `scratch/assemble-port/log.md`): olean chain TailD exit 0, standard axioms. A flat-file compile is not recorded.
   - The docstring count "14 LEAF, 3 LEAF?, 24 GLUE" is wrong. Counting the field docstrings gives **11 LEAF, 3 LEAF?, 27 GLUE** (V). The cited `docs/research/assemble-port.md` does not exist on the branch.
   - LF2's own top theorem (R, LF2 report §0/§5: flat compile exit 0) is `HDec.HSyn.sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (l : OpenAddedLeaves2) (g : OpenGlue2)`. Its base 6f296292 predates g0a3's reductions, so AP supersedes it.
   - Other branches the coordinator listed: dim-contrib, frob-contrib, rv-fast, notes-fix2 and spread-out prove no bundle field (V, diff stat and grep). spread-out has no own commit yet (head = frob-pieces 60340bed).
2. **The brief's claim "every textbook leaf T1-T32 is proved" is FALSE.**
   - Proved (12 fields): t2, t14a, t14b, t15, t16a, t17, t18, t20, t21, t25, t28, t31.
   - Open (18 fields): **t1, t3, t4, t5, t6, t7, t8, t9, t10, t11a, t11b, t16b, t23, t24, t26, t27, t29a, t29b**.
   - The specific list asked about:

     | asked | status |
     |---|---|
     | T1 | open; only reduced (t-purity2) |
     | T3 | open |
     | T4 | open |
     | T5 | open |
     | T6 | open |
     | T7 | open |
     | T8 | open |
     | T9 | open; reducible to two GluePieces4 LEAFs (see row t9) |
     | T10 | open |
     | T11a, T11b | open |
     | T23 | open |
     | T24 | open; atkin-li's `AtkinLiTwistNew` is a different Prop |
     | T26 | open |
     | T27 | open |
     | T29 | open; glue-vigneras proves only N5's order |
   - Evidence (V): grep of the 150 newest origin refs for a theorem whose conclusion is any of these Props, with or without hypotheses, finds none.
   - Not in T1-T32, but listed for completeness: T33, T34, T35, T38 and T41 are also open. T40 is reduced, not proved.
3. **HEAD's h-decomposition §2.2 is stale.**
   - It still marks T14, T28, T36 and T37 "open". All four are proved on HEAD: `C/T14/Main.lean`, `C/T28/Assemble.lean`, `C/RLeaf/` (V).
   - It still lists T39 as a leaf. T39 follows from T40 (`ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp`, V).
4. **Fields unused by `sixContactMin_of_leaves4`.** I grepped every projection `r.X` / `t.X` in g0a3's flat file (V). This finds more unused fields than g0a3 §6 lists:
   - **Research (not in g0a3 §6): r1rec, r3, r4, r5, r7b, r8.** They occur only in the structure literals `toR3`, `researchLeaves4_of` and `researchLeaves3_of`. h-decomposition §2.1 already says R8 "is needed by no step". LF2 and AP still carry all six.
   - **Textbook: t1, t3, t4, t16b, t20, t21, t28, t29a, t29b** (as g0a3 §6), **plus t10**. t10 is projected only by `HSyn.TextbookLeaves.t10_groupIso` (G0Assemble3.lean L33512), which nothing uses. LF2 and AP keep t10 as a hypothesis.
   - `t2` is used, by prop-ts-glue (`propTSAll_of_gp4`), and is proved anyway.
5. **What stays open in g0a3's world (strict list).**
   - **18 research fields:** r1r2, r5count, r6, r7a, r9a, r9b, r10, r11r12, r13, r14, r15, r16, r18, r19, r20, r21, r22, h5fin.
   - **16 textbook fields:** t5, t6, t7, t8, t9, t11a, t11b, t23, t24, t26, t27, t33, t34, t35, x1, t41. Inside x1 only T38 and T40 are open (T40 reduced).
   - Also open but outside my two tables: the research-type LEAFs that g0a3 put in `GluePieces4`: `r1bFamily` (R1(b)), `carayolR17` (R17), `r14Det` (R14 with the det clause). AP moves them into `OpenResearchLeaves2` as `r1b`, `r17`, `r14`.
   - Almost every research field is a "consequence / assembled / joint" Lean form (flag column below), so a strict list must flag them. The exceptions are r7a, r9a, r9b, r19 and r20 (marked E). r19 still says something only together with H5.

## 1. `ResearchLeaves4` (24 fields; g0a3 z95_bundle4.lean; types V)

Field types are defined in g0a3's `scratch/g0-assemble3/Leaves.lean` (root namespace), except r10 (`parts/d45_r10.lean`).

Column definitions:
- **LF name** is the field of LF's `HDec.HSyn.OpenResearchLeaves`. Every type there is the same name with the `HDec.` prefix unless the row says otherwise.
- **Docs status** comes from h-decomposition §2.1 on HEAD and locators.md: Y = YES, CONS = CONSEQUENCE, UNV = UNVERIFIED, NO = "NO — statement".
- **Flag**: C = the docs' E/C column says "C" (consequence); J = joint or assembled; P = premise Lemma P or H5.
- **Used** means projected on the `sixContactMin_of_leaves4` route (V, grep of the flat file).
- **Proofs**: none of the 24 is proved anywhere. Evidence (V): grep of the 150 newest refs for theorems concluding these Props finds only bridges `_iff` and reductions; tc-survey §0: "None of the 23 research-level leaves … is in Tau Ceti". The table therefore has no "proved" column.
- **Last touched** comes from LF2 §2.1 (R).
- **Running tasks**: none of the running tasks (tyz-cm, t40-tate, t40-igusa, twist-descent, linked-frob, hom-unify, mobius-contrib, infra-hodge, spread-out, heightbc-contrib) targets a research field (R/SPECULATIVE, judged from branch heads and reports).

| field | Prop (g0a3) | LF name / kernel K | leaf | citation (docs) | docs status | flag | used? | last touched |
|---|---|---|---|---|---|---|---|---|
| r1r2 | `LeafAdopt.R1R2fpRep` | same; K has only `R1R2fp` (K/QM/Leaves.lean:335) | R1(a,c,d) + π₀ + R2 + R5 on X₆ | Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7, Ex. 5.8, §§4.8-4.17; Kottwitz, JAMS 5 (1992), §5; Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1, §3.1 (p. 740); González–Rotger (R5) | R1: "UNVERIFIED as the full literal leaf, a qualified consequence"; R2: YES (polarized quotient), the indices claim was NO and is removed; Lemma P locators (Buzzard 1997 p. 592; Rotger 2003, 2004) UNV; pin clauses (Mumford GIT Ch. 6, Faltings–Chai I.2.7) UNV | **C, J, P** ("assembled from several statements"; the biconditionals are derived; the π₀ clause is proved by pi0-x6 from R5 clauses + 2 new Props) | yes | pin-apply (six-clause `R1fpProps`) |
| r1rec | `LeafQM.AV.R1rec` | same; K/QM/Leaves.lean | R1(d) reciprocity, object form | Deligne 1971 §1.8, §§3.7-3.13, Thm 4.19, Cor. 5.7/Ex. 5.8 | CONS with qualifications (reflex field) | C, P | **no** | leaf-adopt |
| r3 | `ZInQ.LeafPush2.R03_LinYang` | same; K/LeafPush2/R3.lean | R3 | Math. Z. 295 (2020), 775-819; arXiv:1807.00466v1 **Example 29** (pp. 20-21), eqs. (13)-(14) | "NO — claimed v1 locator" (Example 30), corrected to 29; journal numbering UNV; alternative supplier Baba–Granath Prop. 3.6 p. 742 (read) | **C, J, P** ("Consequence of Example 29 … with Weil's dichotomy (Weil 1957, UNVERIFIED) and Lemma P") | **no** | leaf-push2 |
| r4 | `PkgI1.ThetaModularity` | same; not in K | R4 | Amer. J. Math. 89 (1967), pp. 833-834, 848; Amer. J. Math. 84 (1962) | UNV (signs/exponents); numerically checked by pkg-I1 | C ("in the form stated") | **no** | pkg-I1 |
| r5 | `LeafQM.AV.R5fp` | same; K/QM/Leaves.lean | R5(ii) | J. Math. Soc. Japan 58 (2006), Prop. 5.6, Thm 5.12 (arXiv numbering VERIFIED by rv-h-cm; journal pp. 943, 946) | Thm 5.12: YES on X₀(D,N) | P (≡ `R5fpStrong`, a reformulation) | **no** | leaf-qm-fp |
| r5count | `LeafQM.AV.R5fpCount` | same; K/QM/Leaves.lean | R5(i) | same, Prop. 5.6 | locators NO for the old `#CM=h(R)`; restated (loc-fix) as `2^b h(R)`, the text the audit read | P | yes (`fibreComTrivial_of_gp4`) | leaf-qm-fp |
| r6 | `PkgI2.RaynaudCriterion.{0}` | same; K/Objects.lean:919 | R6 | SGA 7 I, Exp. IX, Prop. 4.7 with Prop. 3.5; Silverberg–Zarhin, AIF 45 (1995), Thm 3.5 | UNV at m = 3 | **C** (Galois consequence) | yes | pkg-I2 |
| r7a | `PkgI2.NeronOggShafarevich.{0}` | same; K/Objects.lean:861 | R7(a) | Ann. of Math. 88 (1968), Thms 1, 2 | UNV | E | yes | pkg-I2 |
| r7b | `PkgI2.SerreTatePotentialGood.{0}` | same; K/Objects.lean:882 | R7(b) | same | UNV | E | **no** | pkg-I2 |
| r8 | `PkgI2.GrothendieckMonodromy.{0}` | same; K/Objects.lean:902 | R8 | SGA 7 I, Exp. IX, Thm 3.6 (S–Z cite "Prop. 3.6") | UNV | **C** (monodromy "consequence form"; "needed by no step … can be dropped") | **no** | leaf-push |
| r9a | `PkgI3.FaltingsSemisimple` | same; K/Objects.lean:423 | R9(a) | Invent. Math. 73 (1983), Satz 3, Satz 4, Korollar 1, pp. 360-361; erratum 75 (1984) | UNV | E | yes | pkg-I3 |
| r9b | `PkgI3.FaltingsTate` | same; K/Objects.lean:430 | R9(b) | same | UNV | E | yes | pkg-I3 |
| r10 | `ZInQ.Contrib.R10.DeRhamComparisonHT` (part d45; = C/R10/Amend.lean) | LF: `HDec.PkgI4.DeRhamComparisonHT` (a separate copy; AP accepts it by unfolding, V z99) | R10 amended | Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; HT clause: Tate 1967, Faltings 1988 (RL4 docstring adds Fontaine 1982, Tate 1967 §3.3) | Y (filtered comparison), CONS (Tate weights); added clause UNV | **C** (Tate-module form "a consequence with T10"; amended = old + `R10Weights`) | yes | r10-amend, g9-derham, leaf-fold |
| r11r12 | `PkgI4.PanBerger` | same; also C/G9/I4Layer.lean | R11 + R12 | Berger, Invent. Math. 148 (2002), Thm 0.7, Cor. 5.22 (arXiv v3 Thm 0.6); Pan, JAMS 35 (2022), Thm 1.0.4 (arXiv v2) | R11 Y; R12 CONS of v2, JAMS number UNV | **J** ("joint consequence … not a merged leaf") | yes | pkg-I4 |
| r13 | `PkgI4.EigenformHT` | same; C/G9/I4Layer | R13 | Kato, Astérisque 295 (2004), §§9.2-9.4, (9.2.2), pp. 187-188 (+§§6.3, 8.3, 11.3-11.4, 14.10.2-3); Saito 1997 | CONS via Kato; Saito UNV | C | yes | pkg-I4 |
| r14 | `EigenformRepExists` (det-free) | LF: `HDec.G0Galois.R14Det` (stronger); in g0a3 the det clause is `GluePieces4.r14Det` | R14 | Shimura 1971, Thm 7.14; Deligne, Sém. Bourbaki 355 (1971); Deligne–Serre 1974 | CONS, chain partly UNV; Eisenstein caveat (WP13) | C | yes | g0-mod-galois, leaf-fold |
| r15 | `DeligneSerreConseq` | same; not in K | R15 | Ann. Sci. ÉNS 7 (1974), Thm 4.1 (with T25, T18, T19) | CONS (with Lemma 3.2) | C | yes | hdec-faithful |
| r16 | `LeafModCurves.R16_EichlerShimuraJ1'` | same; K/ModCurves/Leaves.lean:179 | R16 | Shimura 1971, Thm 7.9, §7; Shimura 1973, Thm 1 | CONS "with an incompletely sourced realization bridge"; suppliers (ii) and (iii) UNV | **C, J** (three suppliers) | yes | leaf-modcurves |
| r18 | `ZInQ.LeafPush2.R18_Javanpeykar` | same; K/LeafPush2/R18.lean | R18 | ANT 8 (2014), Thm 1.1.1 (p. 90) | CONS | C, P (H5; needs `HeightCopiesAgree`) | yes | leaf-push2 |
| r19 | `ZInQ.DefFaltings.R19_GaudronRemond` | same; K/Faltings/Leaves.lean | R19 | Duke Math. J. 163 (2014), Thm 1.4 (p. 2060) | Y | P (H5; normalization-sensitive) | yes | def-faltings |
| r20 | `ZInQ.DefFaltings.R20_FaltingsLemma5` | same; K/Faltings/Leaves.lean | R20 | Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII Cor. 2.1.3 | UNV | P | yes | def-faltings |
| r21 | `ZInQ.DefFaltings.R21_Bost` | same; K/Faltings/Leaves.lean | R21 | Bost, Sém. Bourbaki 795 (1996), via Gaudron–Rémond 2014 §9 | UNV from Bost | C (weaker constant), P | yes | def-faltings |
| r22 | `ZInQ.LeafPush2.R22_Pazuki` | same; K/LeafPush2/R22.lean | R22 | Bull. SMF 140 (2012), Cor. 1.3(2) | CONS "not the literal corollary"; Def. 2.6 identification UNV ("main risk") | **C** (hardened), P | yes | leaf-push2 |
| h5fin | `ZInQ.DefFaltings.StableHeightFinite` | LF: `h5 : HDec.LeafAdopt.H5` (= fin ∧ `NeronModelMinimal`, stronger); K/Faltings/Height.lean:282 | H5 (finiteness half) | Faltings 1983 §1; Deligne, Sém. Bourbaki 616 (1983); BLR (1990) 1.2/1, 1.4/3; SGA 7 I, Exp. IX, 3.3, 3.6 | all UNV; not in locators.md | **C, P** ("published theorem + correctness of the definition") | yes | h5-glue, g0-assemble2 |

Two LF fields have no RL4 counterpart: `r1an`, `r17`. Both are `opaque` placeholders in LF. g0a3 replaces them by `GluePieces4.r1bFamily` and `carayolR17` (V, z80 header).

## 2. `TextbookLeaves` (35 fields; same field list in g0a3 and LF, V by diff)

Column definitions:
- All types are defined in g0a3's `Leaves.lean`; LF's types are the same with the `HDec.` prefix.
- **Citation** is quoted from h-decomposition §2.2 on HEAD. The column header there reads "Reference (UNVERIFIED)", so every reference is UNV unless the row says otherwise. Only T27 was audited in locators.md.
- **Proof** is V unless marked R.
- **"verbatim"** means LF's `#hdec_same` check passed (leaf-fold §2, R from its compile log).

| field | Prop | K location | leaf | citation (docs) | E/C, flag | proof (name, file, branch@commit; same defs?) | used? | last touched / running |
|---|---|---|---|---|---|---|---|---|
| t1 | `PkgI2.PurityBranchLocus.{0}` | Objects.lean:767 | T1 (I2) | SGA 1 X 3.4; Stacks 0BMB | E | **open**. t-purity2 proves T1 ⇔ T1′ ⇔ T1″ (`TPurity2K.purityBranchLocus_of_local`, scratch/t-purity2/T1Kernel.lean, HEAD). tc-survey #14: WEAKER (dim 2, main only) | **no** | pkg-I2; t-purity2 |
| t2 | `PkgI2.AbhyankarDVR.{0}` | Objects.lean:1011 | T2 | SGA 1 X 3.6; Stichtenoth 3.9.1 | E | **proved**: `HDec.TBrauerPurity.abhyankarDVR` (copied into LF, 54425895; LF `t2_proved`, verbatim); kernel form `TBrauerPurityT2K.abhyankarDVR` (scratch/t-brauer-purity/T2Kernel.lean, HEAD 0fd756fb). In g0a3 still a field; AP fills it | yes (prop-ts-glue) | t-brauer-purity |
| t3 | `PkgI2.NeronMappingAbelianScheme.{0}` | Objects.lean:937 | T3 = **I2-NMP** | BLR §1.2 Prop. 8 | C | **open**. tc-survey: NOT FOUND. Off-route use: afr-absfrob `fExtendGen_of_nmp`, frob-pieces `algFrobRed_of_neron_nmp` (R) | **no** | pkg-I2 |
| t4 | `PkgI2.ReductionTorsionBijective.{0}` | Objects.lean:975 | T4 = **I2-Red** | Serre–Tate 1968 §1 | C | **open**. tc-survey: NOT FOUND (elliptic only). Off-route: frob-pieces `algFrobRed_of_neron_nmp` (R) | **no** | pkg-I2 |
| t5 | `PkgI2.TorsionStructure.{0}` | Objects.lean:993 | T5 = **I2-Tors** | Mumford §4, §6 | E | **open**. tc-survey #16: WEAKER (g = 1) | yes | pkg-I2; mobius-contrib uses it (`mobiusGlue_of_t5`) |
| t6 | `PkgI3.HomFreeFinite` | Objects.lean:445 | T6 = **I3.M1** | Mumford §19 Thm 3 | E | **open**. tc-survey: NOT FOUND | yes | pkg-I3 |
| t7 | `PkgI3.CharPolyIndepOfEll` | Objects.lean:454 | T7 = I3.M2 | Mumford §19 Thm 4 | E | **open**. NOT FOUND | yes | pkg-I3 |
| t8 | `PkgI3.PoincareReducibility` | Objects.lean:465 | T8 = I3.M3 | Milne, *Abelian varieties* (C–S 1986), Prop. 12.1 | C | **open**. NOT FOUND | yes | pkg-I3 |
| t9 | `LeafPush.T09_WeilPairing.{0}` | not in K | T9 | Mumford §§20, 23 | **C** ("consequence", polarization hidden) | **open**, but derivable from GluePieces4 LEAFs `t09SymmIsogenyExists` + `isogenyQuasiInverse` via `oldT9_of_symmIsogeny` (G0Assemble3.lean L48563, weil-pairing). It concludes the copy `OldT9.T09_WeilPairing`, whose text equals `LeafPush.T09_WeilPairing` except `Type u` → `Type` (V); the bridge has not been compiled. tc-survey #16: WEAKER | yes (g8_g12) | leaf-push; weil-pairing |
| t10 | `T10Etale.T10_TateDuality` | Textbook/T10Etale.lean:522 | T10 | Milne 1986, Thm 15.1(a); Bhatt–Scholze 2015 §5.6 | E | **open**. tc-survey: NOT FOUND | **no** (only in the unused `t10_groupIso`) | t10-etale, leaf-adopt3 |
| t11a | `ZInQ.LeafPush2.T11a_RiemannEnd` | LeafPush2/T.lean:45 | T11(a) | Mumford §§1-3; Birkenhake–Lange Prop. 1.2.1; Serre 1956; Conrad 2006 §3; Milne 1986 §20 | E | **open** (bp-analytic: half, as glue). tc-survey #18: WEAKER | yes | leaf-push2 |
| t11b | `ZInQ.LeafPush2.T11b_Rigidity` | LeafPush2/T.lean:56 | T11(b) | same | E | **open**. NOT FOUND | yes | leaf-push2 |
| t14a | `PkgI6.BrauerHasse2C` | Conductor/I6Base.lean:169 | T14(a′) | Milne ADT I; Tate in C–F VII §11 | C | **proved**: `ZInQ.Contrib.T14.brauerHasse2C`, C/T14/Main.lean, HEAD b9281f34 (kummer-index). Same Prop as LF's (verbatim via the BrauerT14T15 forms); LF2/AP `t14a_proved` by `exact` | yes | kummer-index |
| t14b | `PkgI6.BrauerReciprocity2C` | I6Base.lean:175 | T14(b′) | same | C | **proved**: `ZInQ.Contrib.T14.brauerReciprocity2C` (same file and commit) | yes | kummer-index |
| t15 | `PkgI6.LocalH2CardC` | I6Base.lean:191 | T15 | Serre, *Corps locaux* XIII §3, X §5 | E | **proved**: `ZInQ.Contrib.BrauerT14T15.localH2CardC`, C/BrauerT14T15/T15.lean, HEAD 0b00e684; LF `t15_proved`, verbatim | yes | t1415-tc |
| t16a | `∀ p, PkgI6.LocalKroneckerWeber p` | I6Base.lean:257 | T16(a) | Neukirch V (1.10); Serre XIII §4, XV §2 | E | **proved**: `ZInQ.Contrib.localKroneckerWeber`, C/LocalKW/LocalKW.lean, HEAD 804a20eb; LF verbatim | yes (via `leafSqrtCrit`) | lkw |
| t16b | `PkgI6.LocalReciprocityUpper` | I6Base.lean:426 | T16(b) | same | E | **open**. tc-survey #12: WEAKER | **no** | pkg-I6 |
| t17 | `TSkolemKW.KW.KroneckerWeberCyclic` | Textbook/KroneckerWeberUse.lean:112 | T17 (narrowed) | Washington Thm 14.1 | C (narrowed) | **proved**: `ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic`, C/KroneckerWeber/Leaves.lean, HEAD f41c037d; LF verbatim | yes | kw-new |
| t18 | `PkgI6.ChebotarevExists` | I6Base.lean:273 | T18 (narrowed) | Neukirch VII.13.4 | C | **proved**: `ZInQ.Contrib.chebotarevExists`, C/Chebotarev/Exists.lean, HEAD a3ae7f4f; LF verbatim | yes (via `frobeniusDense`) | cheb-bridge |
| t20 | `GlueConductor.HilbertDifferentFormula` | Conductor/Breaks.lean:341 | T20 (global) | Serre, *Corps locaux* IV §1 Prop. 4 | E | **proved**: `ZInQ.Contrib.Different.hilbertDifferentFormula`, C/Different, HEAD e597a8fd; LF verbatim | **no** | diff-bridge |
| t21 | `GlueConductor.SerreDifferentBound` | Breaks.lean:350 | T21 (global) | Serre III §6 | E | **proved**: `ZInQ.Contrib.Different.serreDifferentBound` (same commit); LF verbatim | **no** | diff-bridge |
| t23 | `∀ p, PkgI4.T23_FontaineClosure p` | not in K (copy in C/G9/I4Layer.lean:1488) | T23 | Astérisque 223, Thm 3.8 | E, but **flag**: "the Lean form, on V^∨, is a consequence of the published statement, not exact" | **open**. tc-survey: NOT FOUND | yes | leaf-push |
| t24 | `EigenformTwist` | ModCurves/C9.lean:373 | T24 | Shimura 1971 Prop. 3.64; Atkin–Li 1978 | C | **open**. atkin-li @6f77abb1 proves gz-theta's `AtkinLiTwistNew` (weight 2, trivial character, quadratic twist into `cuspFormsNew`), a different Prop with no bridge (V, report). tc-survey #11: WEAKER | yes | hdec-faithful |
| t25 | `PkgI4.NewformOfEigenform` | ModCurves/C9.lean:384 | T25 | Li 1975 Thm 5; Miyake 4.6.19 | C | **proved**: `T25.newformOfEigenform_leaf`, C/T25/NewformOfEigenform.lean, HEAD e84f8159. LF: defeq, `#hdec_same` shows one elaboration difference in `HasNebentypus` | yes | t25-newform |
| t26 | `PkgI3.TateModuleFree` | Objects.lean:437 | T26 = **I3.M0** | Mumford §§4, 18-19 | E | **open**. tc-survey #16: WEAKER | yes | pkg-I3 |
| t27 | `PkgI3.QMDichotomyYu` | Objects.lean:483 | T27 | Yu, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125) | locators: **CONSEQUENCE, refereed locator checked**; volume UNV. C | **open**. NOT FOUND | yes | pkg-I3, loc-fix |
| t28 | `PkgI1.IgusaClebschSeparation` | Textbook/Igusa/Forward.lean:371 | T28 | Igusa, Ann. of Math. 72 (1960) | E | **proved**: `T28.igusaClebschSeparation_proved`, C/T28/Assemble.lean, HEAD (file 2d7f26e2; merge 7506d714). AP z98 `t28_proved` | **no** | igusa-generic, igusa-special |
| t29a | `∀ p, LeafPush.T29a_DivisionNormalizer p` | not in K | T29(a) | Vignéras LNM 800 Ch. II | E | **open** (glue-vigneras / K/Vigneras prove only N5's order) | **no** | leaf-push |
| t29b | `∀ p, LeafPush.T29b_SplitNormalizer p` | not in K | T29(b) | same | E | **open** (same) | **no** | leaf-push |
| t31 | `GlueDescent.B2Q.LeafUnramified` | Descent/B2Glue.lean:318 | T31 | Serre, *Galois cohomology* I §3.2 | C | **proved**: `ZInQ.Contrib.T31.leafUnramified`, C/T31/Main.lean, HEAD 77f718ec; LF verbatim | yes | t31-unram |
| t33 | `LeafModCurves.JacobianExists ℚ` | ModCurves/Defs.lean:199 | T33 | Weil 1948; Milne, *Jacobian varieties*, Thm 1.1, Prop. 6.1 | E (specialized) | **open**. NOT FOUND | yes | leaf-modcurves |
| t34 | `LeafModCurves.DimJ1Genus` | ModCurves/Leaves.lean:203 | T34 | Shimura 1971 Prop. 1.40, §6.7; Milne 1986 | C (citation chain) | **open**. tc-survey #20: DIFFERENT | yes | leaf-modcurves |
| t35 | `ZInQ.LeafPush2.UniformizationExists` | LeafPush2/T.lean:33 | T35 | Mumford §1 with GAGA (Serre 1956) | E | **open**. tc-survey #18: WEAKER. GluePieces4 `analyticUniformizationOfDim` repeats its content over another `AbVar` | yes | leaf-push2 |
| x1 | `X1Belyi.X1Leaves` | ModCurves/X1Belyi.lean:358 | T36-T40 | T36 AEC III.6.4(b); T37 Serre–Tate 1968 Thm 1 / AEC VII.4.1; T38 Hartshorne I.6, II.6.7; T39 Igusa 1959, Shimura 1971 §6.2, Prop. 6.9; T40 Silverman, *Adv. topics* V.3.1; Ogg 1973 | T36 E, T37 C, T38 C, T39 E, T40 C | **T36 proved** `ZInQ.RLeaf.t36_torsionStructure` (C/RLeaf/T36Torsion.lean, cc7222f3). **T37 proved** `ZInQ.RLeaf.T37.t37_goodReductionUnramified` (b777563f). **T39 ⇐ T40** (`x1ConstantField_of_x1RationalCusp`, f6c38023). **T40 reduced**: on HEAD to `IgusaTransitive ∧ TateCuspLaurent`; `TateCuspLaurent` proved (`ZInQ.RLeaf.tateCuspLaurent`, t40-tate @6da675b5, not merged), giving `x1RationalCusp_of_igusaTransitive`; t40-igusa @5ee27509 proves `IgusaTransitive ↔ X0Transitive ∧ TateMuN` and `x1RationalCusp_of_x0_tateMuN` (C/RLeaf/T40.lean). **T38 open.** AP splits x1 into `t38`, `t40` (V z98) | yes | rleaf-elliptic; **running: t40-tate (TateMuN, @c87d3b9b), t40-igusa** |
| t41 | `ZInQ.H5Neron.NeronModelExists` | Faltings/H5Neron.lean:205 | T41 = N1 | BLR 1.2/1, 1.4/3 | E | **open**. Reduced (R): tau-n1n2 `n1_n2_of_leaves` (leaves N1-loc, N1-ab, N2-loc + glue `NeronLocalToGlobal`, `SemistableLocalToGlobal`); neron-lg reduces that glue to leaf NL + 5 glue. No row in tc-survey (row 15 covers only nonzero AbVar) | yes (`heightAdditivity_of_h5neron`) | h5-neron; spread-out (likely neron-lg's `AbVarSpreadsOut`; SPECULATIVE, no commits yet) |

**tc-survey rows (origin/wip/tc-survey @489f46bc §1) for the open fields:**

| leaf | tc-survey |
|---|---|
| T1 | #14 WEAKER |
| T5, T9, T26 | #16 WEAKER (g = 1) |
| T11a, T35 | #18 WEAKER |
| T16b | #12 WEAKER |
| T24 | #11 WEAKER |
| T34 | #20 DIFFERENT |
| T3, T4, T6, T7, T8, T10, T11b, T23, T27, T29a/b, T33 | NOT FOUND |
| T36-T41 | no row |
| research leaves | none in Tau Ceti; R7a/R7b #17 WEAKER (g = 1) |

## 3. Kernel nicknames → bundle field (V: K/Objects.lean docstrings, g8-tate §, lt-goodred, frob-pieces reports)

| nickname | Prop | field |
|---|---|---|
| I2-Tors | `PkgI2.TorsionStructure` (`ObjBridge.TorsionStructure`, `Iff.rfl`) | t5 (T5) |
| I2-NMP | `PkgI2.NeronMappingAbelianScheme` | t3 (T3; unused) |
| I2-Red | `PkgI2.ReductionTorsionBijective` | t4 (T4; unused) |
| I3.M0 | `PkgI3.TateModuleFree` (K/Objects.lean:435 docstring says "I3.M0 — structure of the Tate module") | t26 (T26) |
| I3.M1 | `PkgI3.HomFreeFinite` | t6 (T6) |
| I3.M2 / I3.M3 | `CharPolyIndepOfEll` / `PoincareReducibility` | t7 / t8 |
| R6 | `PkgI2.RaynaudCriterion` (`ObjBridge.RaynaudCriterion`, `Iff.rfl`) | r6 |
| R7a (NOS) | `PkgI2.NeronOggShafarevich` | r7a |
| N1 | `ZInQ.H5Neron.NeronModelExists` | t41 |
| N2 | `SemistableNeronIdentityComponent` | not a bundle field (inside the H5 reduction) |
| R17 / R1(b) / R14Det | `CarayolR17'` / `R1bFamily` / `R14Det` | GluePieces4 (g0a3); `OpenResearchLeaves2.r17 / r1b / r14` (LF2, AP) |

Related glue results today, outside my tables (R):
- lt-goodred @53ba766f proves GluePieces4's `GoodRedTorsion` (no hypotheses) and `QMEndRank` (from t6, t27). AP has not merged lt-goodred (V `merge-base`).
- g8-tate uses only R6, I2-Tors, T26, T7.
