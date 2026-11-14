# leaf-fold6: leafq-check's four reductions applied to leaf-fold5's bundles, T8 kept as a leaf, 68 fields, glue 1

Task leaf-fold6, 2026-11-14. Base d5d43efc (wip/w54: fork main a53d1c7d with tyz-chain, sqrt2-glue, frontier-r2,
leaf-fold5, leafq-check). Nothing was merged. Lean: `scratch/leaf-fold6/` (build order `BUILD.md`; part generator
`mk_f10.py`; `assemble.sh`, `chain.sh`, `ctail.sh`; checks `olean/Check6.lean`, `py/verbatim_check6.py`; results
log `log.md`). No file under `ZInQKernel/`, `blueprint/`, `scratch/h-decomposition/` or
`docs/research/h-decomposition.md`, and no other task's file, was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; the locators below are the source reports').

## 1. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6)
    (l : OpenAddedLeaves6) (g : OpenGlue6) : ZInQ.SixContactMin
```

**VERIFIED.** No `sorry`; `#print axioms HDec.HSyn.sixContactMin_of_open6` gives
`[propext, Classical.choice, Quot.sound]` (olean chain and flat file, §4). Its conclusion is the kernel's own
`ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): `olean/Check6.lean` compiles
`example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open6`.

The hypotheses are 68 named Props; none is an `opaque` placeholder.

| bundle | fields | content |
|---|---|---|
| `OpenResearchLeaves5` | 26 | leaf-fold5's research bundle, reused unchanged (nine fields on the kernel's Props) |
| `OpenTextbookLeaves6` | 21 | leaf-fold5's textbook bundle with `poincareComplement` replaced by T8 itself, on the kernel's Prop |
| `OpenAddedLeaves6` | 20 | leaf-fold5's added bundle with leafq-check's four reductions |
| `OpenGlue6` | 1 | `ModelCoordinateResidue` |

**Counts.** Kinds as in §2 (strict; the rule is in §2.0). The column "inherited" uses the kinds the earlier fold
reports gave the same fields (leaf-fold5 §2, leafq-check §1), for comparison.

| statement | research | textbook | added | glue | total | LEAF / LEAF? / GLUE, inherited | strict (this report) |
|---|---|---|---|---|---|---|---|
| leaf-fold4 (`sixContactMin_of_open4`) | 26 | 19 | 20 | 1 | 66 | 58 / 7 / 1 | |
| leaf-fold5 (`sixContactMin_of_open5`) | 26 | 21 | 21 | 2 | 70 | 55 / 13 / 2 | 51 / 17 / 2 |
| leafq-check (`sixContactMin_of_open10`, over leaf-fold4's bundles) | 26 | 19 | 19 | 1 | 65 | 60 / 4 / 1 | |
| **leaf-fold6 (`sixContactMin_of_open6`)** | 26 | 21 | 20 | **1** | **68** | 57 / 10 / 1 | **51 / 16 / 1** |
| leaf-fold6, T8 by Poincaré's complement (`sixContactMin_of_open6_poincare`) | 26 | 21 | 20 | 2 | 69 | 57 / 10 / 2 | 52 / 15 / 2 |

(leafq-check's own count 15 / 4 for its 19 added fields, with leaf-fold4's 26 + 19 research and textbook fields all
LEAF and one glue, gives 60 / 4 / 1. leaf-fold5's strict count is this report's rule applied to its 70 fields: the
four research fields `r1r2`, `r3`, `r11r12`, `r16` move to LEAF?; see §2.5.)

### 1.1 What changed (each item is a theorem in `scratch/leaf-fold6/parts/`)

**(a) leafq-check's four reductions, on leaf-fold5's bundles** (part f10 = leafq-check's `Fold.lean`, ported by
`mk_f10.py`; part f20).
- `gammaStarGen` is dropped: `LeafQCheck.gammaStarGen_proof` (a descent on the `Γ*`-orbit of `i + j`, from Mathlib
  alone).
- `valenceBoundGammaStar` → `valenceFormulaGammaStar`: `LeafQCheck.VB.valenceBound_of_formula` (`e_P ≤ 6` proved,
  `ellipticOrderLe6_proof`).
- `cmDescends` → `stQM`: `cmDescends_of6 r t l` = leafq-check's `PeriodMapH.LeafQCheck.cmDescends_of l.stQM t11b
  (torsionDescends_of_t5 t5) r.r1r2`, where leaf-fold5 had changed two of the inputs, so its versions are used and
  transported: `t11b := t11b_of_exists5 t.t11bExists` (leaf-fold5 weakened T11(b) to its existence half, av-b2),
  `t5 := torsionStructure_ofK5 t.t5` (leaf-fold5 restated T5 over the kernel's Prop). `r1r2` is unchanged.
- `qmHauptmodul` → `qmHauptmodulBase3`: `qmHauptmodul_of6 r l` = `qmHauptmodul_of_base2 (base2_of_base3 r.r4
  gammaStarGen_proof (valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)`.

None of these needed a change to leafq-check's proofs: `Fold.lean`'s body compiled after leaf-fold5's TailN unchanged
except for the renames below (§4).

**Renames.** leafq-check's `Fold.lean` names its intermediate bundles `OpenAddedLeaves5` … `OpenAddedLeaves10` and
theorems `sixContactMin_of_open5` … `open10`, which clash with leaf-fold5's. `mk_f10.py` renames leafq-check's (never
leaf-fold5's): `OpenAddedLeavesQ5` … `Q10`, `sixContactMin_of_openQ5` … `openQ10`, `openAddedLeaves4_of_Q5`,
`openAddedLeavesQ5_of_Q6` (52 occurrences; the script asserts that undoing the renames gives `Fold.lean` back). These
intermediate forms (over leaf-fold4's bundles) remain in the chain and compile.

**(b) T8: kept as a textbook leaf** (part f20). leaf-fold5 replaced T8 (`PkgI3.PoincareReducibility`) by
`PoincareComplement` (LEAF) and the glue `SimpleImageIsogeny`. Keeping T8 gives fewer glue fields:

| form of T8 | textbook | glue | total | Lean |
|---|---|---|---|---|
| **T8 as a leaf (chosen)** | 21 (`t8`) | **1** | **68** | `sixContactMin_of_open6` |
| `PoincareComplement` + `SimpleImageIsogeny` (leaf-fold5's) | 21 (`poincareComplement`) | 2 | 69 | `sixContactMin_of_open6_poincare` (compiled; T8 from the kernel's `poincareReducibility_of_simpleImage`) |

The field is the kernel's own constant `_root_.PkgI3.PoincareReducibility` (`ZInQKernel/HDecomp/Objects.lean`, the
same statement as pkg-I3's and as the chain's copy, §4), transported to the chain's copy by `t8_ofK6` (abelian
varieties through leaf-fold4's `toAbVarK4`/`ofAbVarK4`, as leaf-fold5's `t8_of_simpleImage5`). Price: T8 is a
composite (Poincaré's theorem plus images and kernels of homomorphisms, av-b1 §3.3), so it is LEAF?, where
`PoincareComplement` was LEAF; the strict LEAF? count is 16 against 15.

**(c) Kernel constants kept.** `OpenResearchLeaves5` is reused as it is, and every textbook and added field that
leaf-fold5 put on a kernel constant has the same type (an `Expr` check, §4). 32 of the 68 fields are kernel constants
(leaf-fold5: 33 of 70; the difference is `poincareComplement` and `simpleImageIsogeny` out, `t8` in).

### 1.2 Which constants the fields are (VERIFIED, `olean/Check6.lean`)

Kernel constants (32): research `r3`, `r6`, `r7a`, `r7b`, `r8`, `r9a`, `r9b`, `r16`, `r17`; textbook `t3Surj`, `t4`,
`t5`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `t8`, `t10`, `homLatticeCorr`, `t24`, `t27`, `t33`,
`dimJacobianEqGenus`, `genusX1Field`, `t35`, `normalModelOfFunctionFieldQ`, `normalCurveSmoothQ`,
`geomConnectedOfConstantFieldQ`, `x0Transitive`, `neronSchemeExtensionExists`; added `zariskiConnectedness` and the
three EGA IV fields. The other 36 are the chain's constants inside `namespace HDec`; the three new ones
(`STQM`, `ValenceFormulaGammaStar`, `QMHauptmodulBase3`) have no kernel namesake.

## 2. Every remaining hypothesis

### 2.0 Classification rule

- **form**: *published form* (the Lean Prop is the printed statement, possibly specialized or with clauses
  dropped); *consequence of one theorem* (follows from one printed theorem by a derivation that uses no other
  published theorem beyond definitions and standard conventions); *composite* (needs two or more printed theorems, or
  a printed theorem together with an argument of the project); *project glue*.
- **kind**: **LEAF** = published, refereed, stated over genuine definitions, form *published form* or *consequence of
  one theorem*, and no source report records that it may be stronger than the source. **LEAF?** = form *composite*,
  or a recorded open question about the exact printed form (flagged for a human check). **GLUE** = to be proved by
  the project.
- Against the earlier fold reports this moves six fields to LEAF? (their source reports call them composites):
  `r1r2`, `r3`, `r11r12`, `r16`, `valenceFormulaGammaStar`, `t8` (the last two are new fields here). Every LEAF? of
  leaf-fold5 that is still a field stays LEAF?.
- Lemma QP (the type-`μ` principal polarization of a QM pair exists and is unique in characteristic 0; rv-qm-polar,
  VERIFIED as an argument, published locators UNVERIFIED) is folded into several QM leaves. Where it is the only
  extra input (the field is otherwise a consequence of one theorem), the field is kept LEAF and the premise is noted
  ("QP"); `r1r2` and `r3` are composites on other grounds as well.

Locators are the source reports' (UNVERIFIED here unless the audit `locators.md` read them). "Last task" names the
last task that changed the field's statement or role. "K" = the field is a kernel constant. "QP" = rests on Lemma QP.

### 2.1 `OpenResearchLeaves5` (26: 22 LEAF, 4 LEAF?)

| field | kind | form | source | last task | K |
|---|---|---|---|---|---|
| `r1r2 : LeafAdopt.R1R2fpRep` | LEAF? | composite | R1(a,c,d), R1 at level one, R2, R5 on points of one `Y₃`, `X₆`: Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8; Baba–Granath 2008 Thm 2.1, Lemma 3.1; González–Rotger 2006 Prop. 5.6, Thm 5.12; with Lemma QP folded in. Audit: R1 "qualified consequence" (the specialization of Deligne's PEL model to this functor needs a human check); Shimura 1967 and Kottwitz unread (`locators.md` R1) | pin-apply | |
| `r1b` (`FibreQM.R1bFamily`) | LEAF | consequence of one theorem | R1(b): Shimura 1967 Main Thm I (holomorphic `ℍ → V(ℂ)`, moduli point `ℂ²/ι(𝒪)(τ,1)ᵀ`) composed with `π`; other triples by qm-pin's comparison (proved). QP (via `R1R2fpRep`) | fibre-qm-period, leaf-fold2 | |
| `r1rec : LeafQM.AV.R1rec` | LEAF | consequence of one theorem | R1(d), Shimura reciprocity on the canonical model (Shimura 1967 Main Thm II; Deligne 1971 §§3.7-3.13, Thm 4.19; audit: consequence with reflex-field qualifications, kept); weaker than reciprocity | leaf-adopt | |
| `r3 : ZInQ.LeafPush2.R03_LinYang` | LEAF? | composite | Lin–Yang 2020 (arXiv v1 Ex. 29, pp. 20-21) on `j ≠ 0, ∞`; Baba–Granath Thm 2.1 for `X₆/W`; Weil's dichotomy (Weil 1957) at `j ∈ {0, ∞}`; Lemma P for the polarization (kernel docstring `HDecomp/LeafPush2/R3.lean`) | leaf-push2; kernel Prop by leaf-fold5 | K |
| `r4 : PkgI1.ThetaModularity` | LEAF | consequence of one theorem | R4, Igusa 1962/1967 (`ψ₄`, `χ₁₀` in theta constants are modular of weight 4, 10); signs UNVERIFIED in print, checked numerically on five generators of `Sp₄(ℤ)` | pkg-I1 | |
| `r5 : LeafQM.AV.R5fp` | LEAF | consequence of one theorem | R5(ii), González–Rotger 2006 Thm 5.12 (with Thm 5.8), read by the audit (YES on `X₀(D,N)`); degree and containment of `k`; QP | leaf-qm-fp | |
| `r5count : LeafQM.AV.R5fpCount` | LEAF | consequence of one theorem | R5(i), González–Rotger Prop. 5.6 (corrected count `2^{b(R)}h(R)`, rv-loc-leaves (e)); QP | leaf-qm-fp | |
| `r6 : PkgI2.RaynaudCriterion` | LEAF | consequence of one theorem | R6, Raynaud, SGA 7 IX Prop. 4.7 (via Silverberg–Zarhin Thm 3.5). Open note: the audit could not read whether the printed bound includes `m = 3` (STANDARD that it is `m ≥ 3`; UNVERIFIED here) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r7a : PkgI2.NeronOggShafarevich` | LEAF | published form | R7(a), Serre–Tate 1968 Thm 1 (per `m`; rv-loc-leaves (b) FAITHFUL) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r7b : PkgI2.SerreTatePotentialGood` | LEAF | consequence of one theorem | R7(b), Serre–Tate 1968 Thm 2 / Cor. 2 (one `K'` for all `n`, FAITHFUL) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r8 : PkgI2.GrothendieckMonodromy` | LEAF | consequence of one theorem | R8, SGA 7 IX 3.6 (Silverberg–Zarhin call it Prop. 3.6; SGA unread) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r9a : PkgI3.FaltingsSemisimple` | LEAF | published form | R9(a), Faltings 1983 Satz 3 (original unread by the audit) | pkg-I3; kernel Prop by leaf-fold5 | K |
| `r9b : PkgI3.FaltingsTate` | LEAF | published form | R9(b), Faltings 1983 Satz 4, Kor. 1 (integral form) | pkg-I3; kernel Prop by leaf-fold5 | K |
| `r10 : PkgI4.DeRhamComparisonHT` | LEAF | consequence of one theorem | R10 amended: Scholze 2013 Thm 1.6, Cor. 1.8 (audit: YES for the filtered comparison, consequence for the weights; or Faltings 1988, Tate 1967) | r10-amend | |
| `r11r12 : PkgI4.PanBerger` | LEAF? | composite | Pan 2022 Thm 1.0.4 (arXiv v2 VERIFIED by the audit; `p ≥ 5`) with Berger 2002 Thm 0.7 (de Rham ⇒ pst) applied to its hypothesis; rv-loc-leaves (a) FAITHFUL. Two research theorems (R11, R12) in one Prop, because "potentially semistable" is not statable in Lean | pkg-I4 | |
| `r13 : PkgI4.EigenformHT` | LEAF | consequence of one theorem | R13, Kato 2004 §§9.2-9.4 (audit: consequence, cusp forms of every level), with the proved `NewformOfEigenform` and Brauer–Nesbitt for general eigenforms | pkg-I4 | |
| `r14 : G0Galois.R14Det` | LEAF | published form (by weight) | R14 with determinant: Shimura 1971 Thm 7.14 (`k = 2`), Deligne 1971 (`k ≥ 2`), Deligne–Serre 1974 (`k = 1`) | g0-mod-galois | |
| `r15 : DeligneSerreConseq` | LEAF | consequence of one theorem | R15, Deligne–Serre 1974 Thm 4.1 with Lemma 3.2 of the same paper (audit; `ρ.IsSemisimple` is a hypothesis, rv-loc-leaves (h)) | hdec-faithful | |
| `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | LEAF? | composite | R16: Shimura 1973 Thm 1 (unconditional clauses), the rank-2 realization over `K_f ⊗ ℚ_ℓ`, and the Eichler–Shimura relation (Shimura 1971 Thm 7.9, UNVERIFIED): three suppliers (rv-loc-leaves (j), `locators.md` R16) | leaf-modcurves; kernel Prop by leaf-fold5 | K |
| `r17 : LadicCond.CarayolR17'` | LEAF | consequence of one theorem | R17, Carayol 1986 Théorème (A) (audit: covers `p ∣ N` and `ℓ = 2`; rv-loc-leaves (f) FAITHFUL) | g0-mod-newform; kernel Prop by leaf-fold5 | K |
| `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | LEAF | consequence of one theorem | R18, Javanpeykar 2014 Thm 1.1.1 (read by the audit), with H5's identification of the height | leaf-push2 | |
| `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | LEAF | consequence of one theorem | R19, Gaudron–Rémond 2014 Thm 1.4 (read by the audit), with H5 | def-faltings | |
| `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | LEAF | published form | R20, Faltings 1983 Lemma 5 (unread by the audit, including the direction), with H5 | def-faltings | |
| `r21 : ZInQ.DefFaltings.R21_Bost` | LEAF | published form | R21, Bost 1996 in the form printed by Gaudron–Rémond §9 (p. 2098, read); Bost's display unreadable | def-faltings | |
| `r22 : ZInQ.LeafPush2.R22_Pazuki` | LEAF | consequence of one theorem | R22, Pazuki 2012 Cor. 1.3(2) (read by the audit), upper half with `h_D = h_F + log π`; rv-loc-leaves (c) FAITHFUL | leaf-push2 | |
| `h5fin : ZInQ.DefFaltings.StableHeightFinite` | LEAF | published form | H5, finiteness half (Faltings 1983 §1; Deligne, Bourbaki 616; locators UNVERIFIED) | h5-glue | |

Vacuity caution (not a verdict; h-decomposition.md, def-faltings): R19, R20, R22 and `h5fin` are stated over
`stableFaltingsHeight`, an infimum that is `⊤` on an empty index set; their non-vacuity rests on the uniformization
statements being satisfiable.

### 2.2 `OpenTextbookLeaves6` (21: 16 LEAF, 5 LEAF?)

| field | kind | form | source | last task | K |
|---|---|---|---|---|---|
| `t3Surj : ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` | LEAF | published form (half) | BLR §1.2 Prop. 8, surjective half (injective half proved) | neron-c; folded by leaf-fold5 | K |
| `t4 : PkgI2.ReductionTorsionBijective` | LEAF | published form | T4, Serre–Tate 1968 §1 Lemma 2 (rv-leaves-b FAITHFUL) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `t5 : PkgI2.TorsionStructure` | LEAF | consequence of one theorem | T5, `A[n] ≅ (ℤ/n)^{2g}`, Mumford §4 over `k̄` | pkg-I2; kernel Prop by leaf-fold5 | K |
| `homFreeFiniteAlgClosed : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | LEAF | published form | Mumford §19 Thm 3 over an algebraically closed field | av-b1; folded by leaf-fold5 | K |
| `charPolyIndepOfEllAlgClosed : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | LEAF | consequence of one theorem | Mumford §19 Thm 4 (degree clause dropped), algebraically closed field | av-b1; folded by leaf-fold5 | K |
| **`t8 : PkgI3.PoincareReducibility`** | LEAF? | composite | T8: Poincaré's complement theorem (Milne 1986 Prop. 12.1; Mumford §19 Thm 1) with images and kernels of homomorphisms (Mumford §§4-8, Milne §8; av-b1 §3.3); true as stated, not stronger (av-b1 §4) | pkg-I3; **leaf-fold6** (back from leaf-fold5's split; kernel Prop) | K |
| `t10 : T10Etale.T10_TateDuality` | LEAF | consequence of one theorem | T10, Tate duality (Milne 1986 Thm 15.1, number UNVERIFIED) | t10-etale; kernel Prop by leaf-fold5 | K |
| `homLatticeCorr : ZInQ.HomUnify.HomLatticeCorr` | LEAF | consequence of one theorem | analytic representation of homomorphisms: Mumford §1, §3 (`A ↦ A^an` fully faithful), Birkenhake–Lange Prop. 1.2.1 (tori), GAGA | hom-unify; kernel Prop by leaf-fold5 | K |
| `t11bExists : AVB2.T11bExists` | LEAF | published form (half) | T11(b) existence half: Conrad 2006 §3; Milne 1986 §20 | av-b2; folded by leaf-fold5 | |
| `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | LEAF | consequence of one theorem | T23, Fontaine, Astérisque 223 Exp. III §1.5, matrix form | pkg-I4 | |
| `t24 : PkgI4.EigenformTwist` | LEAF | published form | T24, Shimura 1971 Prop. 3.64; Atkin–Li 1978 Prop. 3.1 | hdec-faithful; kernel Prop by leaf-fold5 | K |
| `t27 : PkgI3.QMDichotomyYu` | LEAF | consequence of one theorem | T27, Yu 2013 Thm 1.1 (the "split by `ℚ(√d)`" clause dropped; repaired from a stronger form by loc-fix) | pkg-I3; kernel Prop by leaf-fold5 | K |
| `t33 : LeafModCurves.JacobianExists ℚ` | LEAF | published form | T33, Weil; Milne 1986 Thm 1.1, Prop. 6.1 | leaf-modcurves; kernel Prop by leaf-fold5 | K |
| `dimJacobianEqGenus : ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | LEAF? | composite | Milne 1986 Prop. 2.1 with Thm 1.1/Prop. 6.1; Serre duality, Hartshorne III.7.12, II.8 | curves-g; folded by leaf-fold5 | K |
| `genusX1Field : ZInQ.Contrib.CurvesG.GenusX1Field` | LEAF? | composite | Shimura 1971 §6.7, Prop. 6.9, Prop. 1.40 | curves-g; folded by leaf-fold5 | K |
| `t35 : ZInQ.LeafPush2.UniformizationExists` | LEAF | consequence of one theorem | T35, `A(ℂ) ≅ ℂ^g/Λ` (Mumford §1 with GAGA) | leaf-push2; kernel Prop by leaf-fold5 | K |
| `normalModelOfFunctionFieldQ : ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | LEAF | published form | (A): Stacks 0BXX; Hartshorne I.6.7-6.9, II.6.7 | curves-g; folded by leaf-fold5 | K |
| `normalCurveSmoothQ : ZInQ.Contrib.CurvesG.NormalCurveSmoothQ` | LEAF? | composite | (B): Atiyah–Macdonald 9.2 + Stacks 00TV/0B8X | curves-g; folded by leaf-fold5 | K |
| `geomConnectedOfConstantFieldQ : ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ` | LEAF? | composite | (C): Stacks 0FD1; EGA III 4.3 | curves-g; folded by leaf-fold5 | K |
| `x0Transitive : ZInQ.RLeaf.X0Transitive` | LEAF | published form | Lang, *Elliptic functions* Ch. 5 §2 Thm 3; Cox Thm 11.18 | t40-igusa, t40-clash | K |
| `neronSchemeExtensionExists : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | LEAF | published form (weakened) | BLR §1.4 Thm 3 with §1.2 Def. 1 (no group law, no uniqueness) | neron-c; folded by leaf-fold5 | K |

### 2.3 `OpenAddedLeaves6` (20: 13 LEAF, 7 LEAF?)

| field | kind | form | source | last task | K |
|---|---|---|---|---|---|
| `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | LEAF | consequence of one theorem | Shimura 1967 (CM points, `End_𝒪(A) ≅ φ_τ(k) ∩ 𝒪`); Jordan 1981 §3; González–Rotger §5 | fs5-nocm | |
| `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` | LEAF? | composite | Shimura, Duke 43 (1976) / Ann. Math. 102 (1975), or Weil 1957 + Thomae (*Tata II* IIIa §8); `NS(A_ℚ̄) = NS(A_ℂ)`; nonvanishing (Igusa) (leafq-check §2.5) | g0-thetapoint | |
| **`qmHauptmodulBase3 : LeafQCheck.HM.QMHauptmodulBase3`** | LEAF? | composite | the Hauptmodul property of `j_θ` on `Γ*` and its value `−16/27` at the order-2 point: Lin–Yang 2020 Ex. 29 with (13)-(14); Igusa's theta expressions; Hashimoto 1995; Elkies 1998 §3 (leafq-check §2.4) | leafq-check; folded by **leaf-fold6** | |
| `qmClassNumberOne : FibreQM.QMClassNumberOne` | LEAF | consequence of one theorem | Eichler's class number one (Vignéras Cor. III.5.7; Voight Cor. 28.5.17), lattice form | fibre-qm-period | |
| `senTwist : G0Galois.SenTwist` | LEAF | consequence of one theorem | Sen 1980 §2 Thm 4 and Cor. | g12-det | |
| `finiteImageHT : G0Galois.FiniteImageHT` | LEAF | consequence of one theorem | Sen 1980 Cor. of Thm 11 (Tate 1967, Ax–Sen–Tate) | g12-det | |
| `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | LEAF | consequence of one theorem | Mumford §§6, 8, 20, 23 (existential in the dual, never stronger); also gives T9 | weil-pairing | |
| `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | LEAF | consequence of one theorem | Mumford §7-8; Milne 1986 Prop. 7.1 | weil-pairing | |
| `x6ConicModel : X6Kummer.X6ConicModel` | LEAF? | composite | Kurihara 1979; Elkies 1998 §3; on one witness (leafq-check §2.6) | x6-kummer | |
| `y3Connected : TSHecke.Y3Connected` | LEAF? | composite | Deligne, PSPM 33 (1979) 2.1, 2.6.3 with the reciprocity action; witness form (leafq-check §2.7) | ts-hecke | |
| `qmAutCard : HeckeRest.QMAutCard` | LEAF | consequence of one theorem | Shimura 1963 / the classification of `End⁰(A) ⊇ B` (Rotger 2003 §2) | hecke-rest | |
| `alFixedPoints : HeckeRest.ALFixedPoints` | LEAF | consequence of one theorem | Ogg 1983; Rotger 2004 §§2-4 (with a finite embedding check) | hecke-rest | |
| `zariskiConnectedness : ZariskiConn.ZariskiConnectedness` | LEAF | published form | EGA III₁ 4.3.1, 4.3.4 | zariski-conn | K |
| **`stQM : PeriodMapH.LeafQCheck.STQM`** | LEAF | consequence of one theorem | Shimura–Taniyama 1961 §12.4; Shimura 1998 §12.4 Prop. 26: an abelian variety over `ℂ` of CM type is isomorphic to a base change from a number field (`End⁰ ⊇ ℚ(√2, φ)`, a quartic CM field). Flagged by leafq-check for a human check of the up-to-isomorphism form | leafq-check; folded by **leaf-fold6** | |
| **`valenceFormulaGammaStar : LeafQCheck.VB.ValenceFormulaGammaStar`** | LEAF? | composite | the valence formula (Shimura 1971 Prop. 2.16 / Thm 2.20; Rankin 1977 Thm 4.1.4) with the signature `(0;2,4,6)` of `Γ*/ℚ^×` (Takeuchi 1977; Elkies 1998 §3), on finite sets. Flagged by leafq-check for a human check of the normalization of `e_P` and the constant `m/12` | leafq-check; folded by **leaf-fold6** | |
| `egaIV_8_8_2_ii` | LEAF | published form | EGA IV₃ 8.8.2 (ii) (Stacks 01ZM) | spread-out | K |
| `egaIV_8_10_5_xii` | LEAF | published form | EGA IV₃ 8.10.5 (xii) (Stacks 081F) | spread-out | K |
| `egaIV_17_7_8_ii` | LEAF | published form | EGA IV₄ 17.7.8 (ii) (Stacks 07RP) | spread-out | K |
| `shimuraGoodReduction : VertWitness.ShimuraGoodReduction` | LEAF? | composite | Kottwitz 1992 §5; Buzzard 1997; Morita 1981; Carayol 1986; with Lemma P and Yoneda. Flagged: which source states full level 3 at `3 ∣ D` is UNVERIFIED (vert-witness §3) | vert-witness; folded by leaf-fold5 | |
| `curveBijIso : ModelGlue.CurveBijIso` | LEAF? | composite | EGA III 4.4.2; Hartshorne II.6.9, III.10.7, I.6.12 | model-glue; folded by leaf-fold5 | |

Dropped since leaf-fold5: `gammaStarGen` (proved), `valenceBoundGammaStar`, `cmDescends`, `qmHauptmodul` (theorems
from the new fields, §1.1).

### 2.4 `OpenGlue6` (1, GLUE)

| field | form | content | last task |
|---|---|---|---|
| `modelCoordinateResidue : ModelGlue.ModelCoordinateResidue` | project glue | on a model `(𝒴, 𝒜)` of `ShimuraGoodReduction` at `p > 324`, a coordinate `ρ : 𝒴 → P¹` over `ℤ_(p)` with R2fp's fibre relation on `ℚ̄`-points, defined at every point whose stalk is a DVR with maximal ideal `(p)`, with residue transcendental over the prime field. Content: the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` (SGA 1 Exp. V; `p ∤ |Γ'|`) and the CM sections staying disjoint mod `p`. Not proved: neither quotient schemes nor `P¹_{ℤ_(p)}` exist in Mathlib 4.35 (model-glue §2) | model-glue |

`SimpleImageIsogeny` (av-b1) is no longer a field (T8 kept, §1.1 (b)).

### 2.5 Changes of kind against the earlier reports

| field | earlier kind (report) | here | why |
|---|---|---|---|
| `r1r2` | LEAF (leaf-fold2-5) | LEAF? | four sources and Lemma QP; R1 a qualified consequence needing a human check (`locators.md` R1) |
| `r3` | LEAF (leaf-push2, leaf-fold2-5) | LEAF? | Lin–Yang + Baba–Granath + Weil's dichotomy + Lemma P (its own docstring) |
| `r11r12` | LEAF (pkg-I4, leaf-fold2-5) | LEAF? | Pan and Berger composed (its own docstring; two of the 23 research theorems) |
| `r16` | LEAF (leaf-modcurves, leaf-fold2-5) | LEAF? | three suppliers (rv-loc-leaves (j)) |
| `valenceFormulaGammaStar` | LEAF (leafq-check) | LEAF? | the valence formula and the signature of `Γ*` |
| `t8` | LEAF (leaf-fold4) | LEAF? | Poincaré plus images/kernels (av-b1 §3.3) |

No field was found stronger than its source; the six are true composites of published results (each
SPECULATIVE only as to the boundary between "consequence of one theorem" and "composite").

## 3. The remaining leaves by the theory they come from

The 67 leaves (26 + 21 + 20) fall into nine groups (counts are of bundle fields; LEAF? in parentheses).

| group (published theory) | # (LEAF?) | fields |
|---|---|---|
| **A. Shimura curves with quaternionic multiplication** (Shimura 1967, 1971; Shimura–Taniyama; Deligne; Baba–Granath; González–Rotger; Rotger; Ogg; Elkies; Kurihara; Takeuchi; Eichler; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard) | 16 (7) | `r1r2`?, `r1b`, `r1rec`, `r3`?, `r5`, `r5count`, `cmOptimalEmbedding`, `qmHauptmodulBase3`?, `qmClassNumberOne`, `x6ConicModel`?, `y3Connected`?, `qmAutCard`, `alFixedPoints`, `stQM`, `valenceFormulaGammaStar`?, `shimuraGoodReduction`? |
| **A′. Theta functions and Siegel modular forms of genus 2** | 2 (1) | `r4`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** (Mumford; Birkenhake–Lange; Milne; Conrad; Yu 2013) | 12 (1) | `t4`, `t5`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `t8`?, `t10`, `homLatticeCorr`, `t11bExists`, `t27`, `t35`, `t09SymmIsogenyExists`, `isogenyQuasiInverse` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate; SGA 7; Raynaud) | 6 (0) | `r6`, `r7a`, `r7b`, `r8`, `t3Surj`, `neronSchemeExtensionExists` |
| **C′. Scheme theory: limits and connectedness** (EGA III₁ 4.3; EGA IV 8.8, 8.10, 17.7) | 4 (0) | `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_8_10_5_xii`, `egaIV_17_7_8_ii` |
| **D. Faltings 1983 and Faltings heights** | 8 (0) | `r9a`, `r9b`, `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` |
| **E. p-adic Hodge theory** | 6 (1) | `r10`, `r11r12`?, `r13`, `t23`, `senTwist`, `finiteImageHT` |
| **F. Galois representations of modular forms** | 5 (1) | `r14`, `r15`, `r16`?, `r17`, `t24` |
| **G. Algebraic and modular curves** | 8 (5) | `t33`, `dimJacobianEqGenus`?, `genusX1Field`?, `normalModelOfFunctionFieldQ`, `normalCurveSmoothQ`?, `geomConnectedOfConstantFieldQ`?, `x0Transitive`, `curveBijIso`? |
| total | **67 (16)** | |

(`?` marks LEAF?.) Plus the glue Prop `ModelCoordinateResidue` (arithmetic geometry of the model of `Y₃`: tame
quotients). Against leaf-fold5: group A lost `gammaStarGen` and `cmDescends`/`valenceBoundGammaStar`/`qmHauptmodul`
became `stQM`/`valenceFormulaGammaStar`/`qmHauptmodulBase3` (17 → 16); group B has `t8` for `poincareComplement`. The
grouping is a reading of the docstrings (SPECULATIVE in its boundaries: `t4` could go under C, `curveBijIso` under C′,
`shimuraGoodReduction` under C).

**Flagged for a human check**: `ShimuraGoodReduction` (level 3 at `3 ∣ D`), `STQM` (the up-to-isomorphism form),
`ValenceFormulaGammaStar` (normalization of `e_P`, constant `m/12`), `R1R2fpRep` (R1's specialization; Lemma QP's
locators), `RaynaudCriterion` (the `m = 3` boundary in print).

## 4. Checks

**Kernel build.** `lake build $(cat scratch/leaf-fold5/kernel_targets.txt)` in this worktree: success (11006 jobs,
16 min). The kernel modules the chain imports are unchanged between leaf-fold5's base ee7582da and d5d43efc
(`git diff --stat ee7582da d5d43efc -- ZInQKernel` touches only `Contrib/TYZChain` and `AllContrib`).

**Olean chain** (`scratch/leaf-fold6/chain.sh`, one Lean process at a time; times in `log.md`): leaf-fold4's committed
sources LPrefix … TailK (LPrefix 535 s … TailK 13 s) and leaf-fold5's TailL, TailM (455 s), TailN, compiled unchanged,
then TailO (part f10 + part f20, 27 s): 0 errors, no `sorry` in any module. All 369 `#print axioms` reports of the
chain, joined over wrapped lines, read `[propext, Classical.choice, Quot.sound]`; TailO's 20 include
`sixContactMin_of_open6`, `sixContactMin_of_open6_poincare`, `t8_ofK6`, `cmDescends_of6`, `qmHauptmodul_of6`,
`gammaStarGen_proof`, `ellipticOrderLe6_proof`, `cmDescends_of`, `base2_of_base3`, `sixContactMin_of_openQ5` …
`openQ10` (VERIFIED).

**Kernel conclusion, closure, field heads, field types** (`olean/Check6.lean`, 46 s; output without host paths in
`check6_result.txt`, VERIFIED):
- `example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open6` compiles.
- The closure of `sixContactMin_of_open6` has 184 758 constants and does **not** contain `sorryAx`. It contains
  leafq-check's `gammaStarGen_proof`, `valenceBound_of_formula`, `ellipticOrderLe6_proof`, `cmDescends_of`,
  `torsionDescends_of_t5`, `base2_of_base3`, `qmHauptmodul_of_base2`, `orbit4`, `orbit3`, `orbit24`,
  `LQ20.s20WeightExact_of`, and leaf-fold5's `t11b_of_exists`, `torsionStructure_ofK5`, `heckeVertWitness_of_leaves5`,
  the kernel's `smoothFibreReduced`, `homFreeFinite_of_algClosed`, `curveOfFunctionFieldQ_of_split`,
  `neronModelExists_of_extension`; it does not contain `poincareReducibility_of_simpleImage` (the `_poincare` variant's
  closure, 184 795 constants, does).
- The head constant of every field type: 68 fields, 32 kernel constants (§1.2).
- **Field types as terms**: every field type of `OpenTextbookLeaves6`, `OpenAddedLeaves6`, `OpenGlue6` is `==` (as an
  `Expr`, universe levels included) the type of the same field of leaf-fold5's `OpenTextbookLeaves5`,
  `OpenAddedLeaves5`, `OpenGlue5` or of leafq-check's `OpenAddedLeaves10` (here `OpenAddedLeavesQ10`); `t8`'s type is
  the constant `PkgI3.PoincareReducibility`: ALL MATCH. `OpenResearchLeaves5` is leaf-fold5's structure itself.

**Flat file** FLAT-PLACEHOLDER

**Verbatim check** (`python3 py/verbatim_check6.py`, output `py/verbatim_check6_out.txt`: ALL OK, VERIFIED):
- (A) the 41 field lines of the new structures other than `t8` have, character for character, the text of the
  same field in leaf-fold5's part e90 (38) or in leafq-check's `Fold.lean` `OpenAddedLeaves10` (`qmHauptmodulBase3`,
  `stQM`, `valenceFormulaGammaStar`); the 26 research fields are leaf-fold5's structure.
- (B) every one of the 36 chain head constants has, in the flat file, a declaration identical to one in a source
  file outside the assemblies (leaf-fold*, h-decomposition, g0-assemble*, olean/ copies, flat files), e.g.
  `ModelCoordinateResidue`, `CurveBijIso`, `ShimuraGoodReduction` in model-glue's files, `STQM` in leafq-check's
  `CMDescendsGlue.lean`, `ValenceFormulaGammaStar` in `ValenceBound.lean`, `QMHauptmodulBase3` in
  `QMHauptmodulCM.lean`, `T11bExists` in av-b2's `AVB2Main.lean`. For `R1R2fpRep`, `R5fp`, `R5fpCount` the
  statement is identical and the docstring was repaired since (rv-loc-leaves). The 32 kernel head constants are
  found in `ZInQKernel/` (the field is the kernel's declaration, so its text is the kernel's).
- (C) the kernel's `PkgI3.PoincareReducibility` (`HDecomp/Objects.lean`) is identical, docstring included, to
  pkg-I3's `I3.lean`, and its statement is identical to the chain's copy (whose docstring carries rv-leaves-b's
  repair 2), which leaf-fold4's `t8` used.
- (D) `STQM`, `TorsionDescends`, `bcC`, `ValenceFormulaGammaStar`, `ellOrder`, `EllipticOrderLe6`,
  `QMHauptmodulBase`, `QMHauptmodulBase2`, `QMHauptmodulBase3`, `x3` have the same text in part f10, in leafq-check's
  `Fold.lean` and in leafq-check's standalone files.

**Changes to the copied texts** (each in a script, with its reason):

| script | change | reason |
|---|---|---|
| `mk_f10.py` | `import TailK` dropped; 52 renames (`OpenAddedLeaves5..10` → `Q5..Q10`, `sixContactMin_of_open5..10` → `openQ5..Q10`, `openAddedLeaves4_of_5`, `openAddedLeaves5_of_6`); reversibility asserted | name clash with leaf-fold5 |
| `parts/f20_fold6.lean` | hand-written transports and bundles | §1.1 |

**No statement of a leaf or glue Prop was changed.**

## 5. Not folded, and why

- **The other 36 fields as kernel Props** (goal (c) keeps leaf-fold5's 32 + `t8`; nothing new could move): the three
  new leafq-check Props have no kernel namesake; the rest are as in leaf-fold5 §5 (QM structures `QML3`/`QMPair` whose
  isomorphism notions enter `fieldOfModuli`; Faltings heights over the copied `GroupModel`; the p-adic layer whose only
  kernel versions are task-local copies; the period, Hecke and Galois-representation layers that live only in the
  chain). wip/one-proof moves the whole chain onto kernel objects.
- **T8 by Poincaré's complement** (`PoincareComplement` LEAF + `SimpleImageIsogeny` GLUE): one more glue Prop; compiled
  as `sixContactMin_of_open6_poincare` (69 fields), not canonical (goal (b)). av-b1's finer split
  (`ImageFactorization` + `SimpleSurjIsogeny`) would give glue 3.
- **leafq-check's intermediate forms** (`OpenAddedLeavesQ5` … `Q10` over leaf-fold4's bundles): kept in the chain
  under their new names, not used by `sixContactMin_of_open6`.
- **`ThetaRatiosAlgebraic`, `X6ConicModel`, `Y3Connected`**: unchanged (leafq-check §2.5-§2.7: true, consequences of
  published results, not splittable in Lean today).
- **`QMHauptmodulBase3`**: leafq-check proved the disc −4 and disc −3 clauses; the Hauptmodul property and the value
  `−16/27` remain (genuine arithmetic content).
- As in leaf-fold5 §5: curves-g's `DimJ1LeSq` proposal, neron-lg, homlattice's split of `HomLatticeCorr`, t5-torsion's
  options, kerwild-fix and frobchain-contrib.
