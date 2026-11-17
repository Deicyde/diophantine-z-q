# frontier: every open Prop on the path to `ZInQ.FrozenTarget`

Task frontier, 2026-11-13; refreshes r2 to r10, 2026-11-14 to 11-16 (text checks only, no Lean run). Base of r10: fork
main c0f3d085 (leaf-fold33, over leaf-fold32 6b7a4544, leaf-fold31 and leaf-fold30 over leaf-fold29, and r9 merged),
on wip/frontier-r10. Branch snapshot: the commits in `scratch/frontier/refs.txt` (r10 section: branch heads read 11-16
22:56 PST, main 11-16 22:56 PST). Lean: `scratch/frontier/TYZChain.lean`, `TopChain.lean` (compiled 11-13, unchanged
in r2). Mechanical check: `scratch/frontier/chain.py` (with `chainlib.py`), run from the repository root; output
`scratch/frontier/chain_out.txt`. Results log: `scratch/frontier/log.md`. Working notes from three read-only survey
agents (11-13): `scratch/frontier/agent-{h-glue,h-leaves,tyz}.md`. Only this report and `scratch/frontier/` were
edited. Model work; no human review.

**Counts.** This report's counts describe the snapshot named above. The public count of open statements is the count
line of `docs/one-proof/OPEN.md`, which the integrator regenerates from the Lean build at every fold.

Marks: **VERIFIED** (read in a named Lean file or report at a named commit, or compiled here), **REPORTED** (a task's
report or log says so; the Lean was not re-read), **UNVERIFIED** (a theorem number or locator taken from a report or
from memory; this host has no network and no copy of the papers).

**Classification (the integrator's rule, applied strictly).** **LEAF** = a published, refereed statement, and the
Lean Prop is that statement or a specialization of it (fewer cases, weaker constant read off the same display).
Textbook theorems (Mumford, Milne, BLR, …) count as published. Everything else is **GLUE**: the project's own
arguments, statements that are standard but not printed in that form, "consequences" whose derivation needs an
argument, readings of a printed statement, and composites of several published theorems. Where a GLUE Prop is a
consequence or composite of published theorems, the table says so ("lit-composite") and names the nearest sources;
it is still GLUE.

**Form and two counts (r3, the integrator's ruling of 2026-11-14).** Every row has a form: *published form* (the
printed statement, or a specialization read off the same display), *consequence of one theorem* (a short
derivation from one printed theorem), *composite* (several published results) or *project glue*. The **strict
count** (LEAF = published form only) leads: every GLUE row under it is a Lean argument the project still owes. The
**lenient count** follows, "if consequences of one theorem count as leaves". A consequence or composite row
becomes a strict LEAF once its derivation is compiled; the form column says where the derivation is written
(for leaf-fold3's fields, leaf-review-a and leaf-review-b).

## 0. Main result

**The list.** If every proof and reduction that the branches had compiled by the snapshot (11-16 22:56 PST) is folded
in (scenario F, §5), the open Props on the path to `ZInQ.FrozenTarget` are **35: 15 LEAF and 20 GLUE** in the strict
count. If consequences of one theorem count as leaves, they are 27 LEAF and 8 GLUE.

**The library theorem.** `ZInQ.OneProof.frozenTarget` on main (scenario A) has 35 hypotheses, leaf-fold33's 29 fields
in three bundles and the six TYZ and GZ Props, and its proof uses all of them (the folds' prune scans find no unused
field). Its fields and its six other hypotheses are classified in the integrator's table `docs/one-proof/kinds.tsv`
(rendered in `docs/one-proof/OPEN.md`), whose headline follows the integrator's strict convention: a leaf with a
flagged plausible weaker reading counts GLUE, a merely unread leaf stays LEAF, flagged. The table's strict and
strictest columns agree, and two published kinds are GLUE in both, pending a reading: the fields are **11 LEAF and 18
GLUE** in the strict count, as OPEN.md's count line says, and by kind 13 published and 16 other. With the top: 15 LEAF
and 20 GLUE strict, 27 and 8 lenient. Scenario F has as many rows: it also applies two splits that the folds leave out
on purpose (each replaces one field by a leaf plus smaller statements, leaf-fold9 §5; here one Prop for one:
modular-split's for `r17` and c-to-printed2's for `eigenformHTNew`, §4.1). Since leaf-fold33 the library theorem takes
the `C_d` form of the top's Gross–Zagier hypothesis, which scenario F took in r9 (Z7, Z11, §2.1).

| premise | open Props | strict LEAF | strict GLUE | lenient LEAF | lenient GLUE | table |
|---|---|---|---|---|---|---|
| GZ, `Literature.GrossZagier` | 2 | 1 | 1 | 1 | 1 | §2.2 |
| TYZ, `Literature.TYZThm35ReadingA` | 4 | 3 | 1 | 4 | 0 | §3.2 |
| H, `SixContactMin`: research-level fields of r3 | 3 | 2 | 1 | 2 | 1 | §4.2 |
| H: textbook fields of r3 | 0 | 0 | 0 | 0 | 0 | §4.3 |
| H: fields that were glue in C4 | 0 | 0 | 0 | 0 | 0 | §4.4 |
| H: Props introduced by reductions until r3 | 1 | 1 | 0 | 1 | 0 | §4.5 |
| H: fields of the H base introduced in r4 | 8 | 1 | 7 | 8 | 0 | §4.6 |
| H: Props open only in scenario F, introduced in r4 | 0 | 0 | 0 | 0 | 0 | §4.7 |
| H: fields of leaf-fold9 introduced in r5 | 0 | 0 | 0 | 0 | 0 | §4.8 |
| H: Props open only in scenario F, introduced in r5 | 1 | 0 | 1 | 1 | 0 | §4.9 |
| H: fields of leaf-fold10 and leaf-fold11 introduced in r6 | 0 | 0 | 0 | 0 | 0 | §4.10 |
| H: Props open only in scenario F, introduced in r6 | 1 | 0 | 1 | 1 | 0 | §4.11 |
| H: fields of leaf-fold13 introduced in r7 | 1 | 0 | 1 | 0 | 1 | §4.12 |
| H: Props open only in scenario F, introduced in r7 | 0 | 0 | 0 | 0 | 0 | §4.13 |
| H: fields of leaf-fold14 to leaf-fold19 introduced in r8 | 2 | 1 | 1 | 2 | 0 | §4.14 |
| H: fields of leaf-fold20 to leaf-fold26 introduced in r9 | 4 | 0 | 4 | 1 | 3 | §4.15 |
| H: fields of leaf-fold32 and leaf-fold33 introduced in r10 | 8 | 6 | 2 | 6 | 2 | §4.16 |
| **total** | **35** | **15** | **20** | **27** | **8** | |

By form: 15 published form, 12 consequences of one theorem, 8 composites, 0 project glue.

**Since r9 (11 new rows; 8 LEAF and 3 GLUE strict, 8 and 3 lenient).** 20 rows are proved (H-65, H-72, H-98, H-99,
H-100, H-103, H-104, H-118, H-120, H-121, H-201, H-202, H-203, H-205, T-18, T-19, T-20, T-22, T-23, Z-6), three pruned
(H-150, H-192, H-210), eleven replaced by new leaves (H-5, H-77, H-125, H-126, H-182, H-200, H-207, H-211, T-15, Z-3,
Z-5) and fourteen off the route (H-70, H-89, H-90, H-91, H-92, H-93, H-94, H-95, H-96, H-97, H-174, H-190, Z-4, Z-7).
The H base is leaf-fold33's `sixContactMin_of_open48` inside the library (C4'''''''''', §1). leaf-fold30: ds965-weak
restates `dsThm965` in its weakest printed reading; sgr-fold, with sgr-direct, proves the one consumer of
`shimuraIntegralModelRep` and of the glue field `quotientP1Coordinate` with no integral model and prunes both, for one
new glue field, `nvLocalInertia`; persists-dvr proves `semistablePersistsSHcp` from four kept fields; dcy3-fold prunes
`deligneComponentsY3PrintedAb`. leaf-fold31: pi0-fold prunes `deligneComponentsX6PrintedAb` and
`geomConnOfAlgClosure`, and fork PR #24 proves `regularSmoothPerfect`. leaf-fold32: abhyankar proves `nvLocalInertia`
(through nv-local's `TameBranchNormal`), so the glue bundle is empty and goes; theta-fold2 removes
`thetaRatiosAlgebraic`, whose use form theta-direct proves with no hypotheses; fork PRs #25, #29, #31, #34 and #35,
milne-compile and ega-limit prove eight fields; gt-sga3 narrows `sga3_VIB_3_10` to its neighbourhood form;
dict-models, dict-galois, coeff-fix and pic-fix restate eight fields by the printed statements they come from
(`sga7_IX_3_3_SH`, `raynaudSemistableSH`, `mumfordGroupLaw`, `neronBaseChangeStrictHenselization`, `r7a`,
`dsThm965Weak` with `dsThm966`, `phiAmpleIsogeny`); and on the top fork PRs #36 and #38 prove `hL3s` and `hJP`,
t21-proof proves `hT21`, and bfh-gamma0's `hBFH`, a published form, replaces `hFH`. The integrator's dictionary
rulings re-rate `picZeroAbVar`, `phiAmpleIsogeny` and `weilPairingMumford` (leaf-fold31) and `gagaMorphism`
(leaf-fold32) as consequences, and the dictionary pass (leaf-fold32) re-rates nine fields and the top's `h33`:
`bostLowerBound`, `gaudronRemondThm14`, `javanpeykarBound`, `pazukiCor13Upper`, `hodgeTateDecompAbVar`,
`deRhamH1AbVarT`, `gonzalezRotgerProp56X6`, `elkiesX6StarFunctionField` and `h33` become consequences and
`gonzalezRotgerX6Ab` a composite. leaf-fold33: neron-sh-proof proves `neronBaseChangeStrictHenselization` outright,
and with it dict-models' `blr_7_2_1`; poincare-proof proves `poincareComplement`, phi-ample pic-fix's first Mumford
leaf, and phisurj `weilPairingMumford` and `phiAmpleIsogeny`, so pic-fix's second leaf leaves the chain; piczero-char0
replaces `picZeroAbVar` by its characteristic-0 form from three printed leaves, two of which idcomp-lft and piclft
prove; homfree-noemb and sga3-nbhd reroute `homFreeFiniteAlgClosed` and gt-sga3's neighbourhood form away;
goodmodel-iso replaces `mumfordGroupLawConn` and `neronSchemeExtensionExists` by BLR's Néron existence theorem over a
Dedekind base; and on the top hfx-proof and hp23-proof prove `hfx` and `hP23`, hcm-dict retypes `hCM` to Shimura's
Theorem 5.4 as printed, and gzopt-dict, with heegner-32 and gz-conj, takes the `C_d` route into the library theorem:
`hGZ`, Gross–Zagier over the algebraic `X₀(N)`, replaces `hL3`, and gamma0-qexp and etaw32-proof prove the route's two
other leaves. The count of rows goes from 72 to 35: 48 go, 11 come.

**Not applied** (§4.1): the reports of the branches after main (below), which are not merged; as in r9, sh-route's
theorems and shimura-cft's leaf.

**Who works on what** (the integrator's `docs/one-proof/claims.tsv` with the crowd kit's columns): the cloud claims
mark 2 rows (2 by cloud batch 2), and the rows say which; the project's own claims are on 16 fields and hypotheses:
`charPolyIndepOfEllAlgClosed` (H-71: deg-det); `h11` (T-1: h11-reduce); `picRepresentableAbVar` (H-199: pic-repr);
`r17` (r17-bypass); `eigenformHTNew` (ht-bypass); `r11r12` (H-9: pb-bypass); `gaudronRemondThm14` (H-110:
gr14-narrow); `r9a` (H-6: faltings-cm); `r9b` (H-7: faltings-cm); `gonzalezRotgerProp56X6` (H-204: gr56-prove);
`r16CoreY` (H-212: r16-used); `hCM` (T-24: cm-primitive); `neronOggShafarevichSep` (H-219: nos-proof);
`sga7_IX_3_5_ForwardGeom` (H-208: sga7-35-proof); `raynaudSemistableSHOr` (H-217: raynaud-proof); `hL29` (T-21:
h29-proof). After main the fork's branches carry results on 23 rows, marked "after main" in the rows; their reports
are not merged, so this report does not use them:
- r16-used (dcf24ac6): `r16CoreY` replaced by one printed-form leaf.
- isj1-dict (37628525): the `IsJ1` step behind r16-used's leaf reduced as far as the kernel allows.
- x1-igusa (62d9b7c5): isj1-dict's Igusa-transitivity step proved from Igusa's theorem as Diamond–Shurman §7.5 prints
  it.
- weber-field (f2cf835b): x1-igusa's function-field comparison proved with no hypotheses.
- aftate-or (7378fd4e): `r16CoreY` from a printed-form leaf, x1-igusa's `IgusaGL2DS` and the field
  `mumfordTorsionAlgClosed`.
- sga1-fix (06be00c5): `uniformizationLeafAll` and `gagaMorphism` from printed leaves of SGA 1 XII.
- gaga-chart (5626f0b0): `gagaMorphism` from one printed leaf and `uniformizationLeafAll`.
- gr56-prove (90b817cb): `gonzalezRotgerProp56X6` from Eichler's optimal-embedding count.
- gr14-narrow (830ff58d): `gaudronRemondThm14` narrowed to its forward direction.
- sga7-cp (0c200c57): `sga7_IX_3_5_ForwardGeom` (and the old field `raynaudSemistableSH`) weakened to the instance
  used.
- composite-out (822da7b5): the three uses of `shimuraMainThmIDeligneY3AbU` proved, so the composite is not needed.
- shimura-split2 (838a7430): `rayClassCMAb` and `shimuraFamilyAb` from two new leaves, without
  `shimuraMainThmIDeligneY3AbU`.
- holfam (93220b34): shimura-split2's holomorphic family from one printed leaf on Deligne's PEL curve.
- pel-hodge (1d9922c7): holfam's leaf from its printed Hodge form and `uniformizationLeafAll`.
- pb-bypass (c1636db9): `r11r12` from Pan's and Berger's printed theorems over Fontaine's `B_st`.
- pb-fix (e479bc56): pb-bypass's two leaves restated in printed form.
- pb-fix2 (401a7523): `r11r12` from two printed-form leaves and the Diamond–Shurman fields of its base.
- ht-exists (7088f9ed): `eigenformHTNew` from Kato's existence form.
- r17-bypass (3e6e5017): `r17` from one new leaf, the existence form of Carayol's conductor theorem.
- faltings-cm (ce696e14): `r9b` from its surjectivity half and `homFreeFiniteAlgClosed`.
- height-fix (49e6d97d): `bostLowerBound` and `gaudronRemondThm14` from printed-height leaves, the measure defect
  fixed and the normalized-mass step proved; one glue Prop (descent of semi-abelian reduction) left.
- javanpeykar-fix (3d1ce928): `javanpeykarBound` from printed leaves, the Jacobian and Belyi dictionary steps proved.
- aftate-fix2 (c56922c0): `r16CoreY` from three printed-form leaves over genuine definitions, with `A_f` universal.
- charpoly-ell (0d75311f): `charPolyIndepOfEllAlgClosed` reduced to one statement, `DegEqDetTate`.
- deg-det (ecf7da39): charpoly-ell's `DegEqDetTate` from one printed leaf and two fields.
- coeff-field (5bb50efa): `eigenformCoeffFieldFinite` from the rational structure of `S_k(Γ₁(N))`.
- nos-proof (e9828e92): `r7a` from one leaf, the printed direction (c) ⇒ (a) over a separable closure.
- gr-dict (48db1227): both González–Rotger rows from printed leaves.
- h33-dict (d489fc13): `h33` from TYZ's printed Theorem 3.3 and `hCM`, the dictionary steps proved.
- gaga-serre (1d7687e7): `gagaMorphism` from Serre's GAGA, the projectivity of abelian varieties proved.
- dict-galois (81d1f67f): `hodgeTateDecompAbVar` and `deRhamH1AbVarT` restated as printed (its `r7a` part is folded).
- coeff-rational (e85590b8): `eigenformCoeffFieldFinite` from two printed-form leaves on `S_k(Γ₁(N))`, with no
  diamond-operator leaf.
- hodgetate-from-dr (7320b450): `hodgeTateDecompAbVar` proved with its exact type from printed forms, the field
  removed.
- derham-print (ccb19bd3): `deRhamH1AbVarT` from two printed-form leaves and `mumfordTorsionAlgClosed`.
- grx6ab-print (b047ce25): `gonzalezRotgerX6Ab` from González–Rotger's Theorem 5.12 as printed and printed moduli
  leaves.
- elkies-print (168bbb39): `elkiesX6StarFunctionField` from one new leaf in elkies-coord's function-field form and the
  moduli witness the bundle supplies.
- semiab-descend (6a6de248): height-fix's last glue Prop, `SemiAbelianDescendsPerfect`, proved from one new published
  leaf.
- javanpeykar-rebase (4cb6a008): `javanpeykarBound` over height-fix's printed stable height, from printed leaves.
- sga33-shpre (ffd056ea): `sga7_IX_3_3_SHpre` is used only in characteristic 0 with a perfect residue field (route
  (c)).
- y3abu-print (579a89bb): `shimuraMainThmIDeligneY3AbU` from two printed-form leaves.
- y3abu-strict (e0197d03): y3abu-print's moduli leaf split into the two printed statements, the glue proved.
- tyz-genus (01ad83f2): TYZ Lemma 2.8 proved, so `hL29` follows from TYZ Theorem 2.1 alone.
- gz-dict2 (4fd8ddd2): fold33-review's steps D1 and D2 for `hGZ` proved in Lean, D3 reduced to the uniqueness of the
  strong Weil parametrization.
- bst-construct (fe8b3066): `r11r12` from Berger's and Pan's printed theorems with Berger's period rings built in Lean
  inside Mathlib's `B_dR` (on the base before coeff-fix: it takes `dsThm965Weak` and `dsThm966`).
- eichler-bound (09896d1f): `gonzalezRotgerProp56X6` with no new leaf: the half the chain reads from three textbook
  fields, Eichler's optimal-embedding bound proved outright.
- r17-print (785e3f29): `r17` from Carayol's Théorème (A) as printed and `eigenformCoeffFieldFinite`, every dictionary
  step proved.

**The 35 names** (L = LEAF in both counts; c = consequence of one theorem, LEAF only in the lenient count; all others
GLUE; details in the tables):
- GZ: `ZInQ.BFHPrinted.BFHClauseIIGamma0` (L); `ZInQ.GZAlg.GrossZagierAlgOptCd`.
- TYZ: `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` (L); `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (c); `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3` (L); `ZInQ.Contrib.HCMDict.ShimuraThm54` (L).
- H: `PkgI3.FaltingsSemisimple` (L); `PkgI3.FaltingsTate` (L); `PkgI4.PanBerger`; `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` (L); `AvSplit.MumfordTorsionAlgClosed` (L); `ZInQ.HomLattice.GAGAMorphism` (c); `ZInQ.HeightSplit.JavanpeykarBound` (c); `ZInQ.HeightSplit.GaudronRemondThm14` (c); `ZInQ.HeightSplit.BostLowerBound` (c); `ZInQ.HeightSplit.PazukiCor13Upper` (c); `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (c); `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (c); `ModularSplit.R17.CarayolRealization` (c); `CToPrinted2.KatoRealizationCohSS` (c); `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab`; `T09Pic.PicRepresentableAbVar` (L); `GRCountX6.GonzalezRotgerProp56X6` (c); `UnipotentForward.SGA7_IX_3_5_ForwardGeom`; `RayClassCFT.ShimuraMainThmIDeligneY3AbU`; `R16Split.R16CoreY`; `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField` (c); `DSCoeffExt.DSThm965Printed` (L); `DSCoeffExt.EigenformCoeffFieldFinite`; `DSThm966EV.DSThm966Printed` (L); `DictModels.RaynaudOr.RaynaudSemistableSHOr` (L); `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`; `NOSSepDict.NeronOggShafarevichSep` (L); `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` (L); `PicFix.KleimanPicZeroProper` (L).

**How far this is checked.**
- **Scenario A is one compiled theorem.** `ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`, on
  leaf-fold33's bundles) derives `ZInQ.FrozenTarget` from leaf-fold33's three bundles (24 + 3 + 2 = 29 fields) and the
  six top Props `TYZThm11Integral`, `TYZLemma29PrintedNe3`, `ShimuraThm54`, `TYZThm33`, `BFHClauseIIGamma0` and
  `GrossZagierAlgOptCd`. OPEN.md states that the kernel checks it with no `sorry` and only the standard axioms
  (REPORTED; the folds regenerate the build's `open-statements.json`). `chain.py onep` reads the signature: its
  hypotheses are scenario A's (the three bundles and the six top Props); the bundles' fields are the 29 field rows of
  `kinds.tsv`, with the names and type heads of the build's `open-statements.json`, whose six other hypotheses have
  scenario A's heads.
- **Scenario F.** A plus the edges of §4.1 that the folds leave out, each compiled on its branch per its report and
  log. `chain.py` checks signatures (0 mismatches over 226 theorem edges, 21 of them followed on the route) and
  compares definitions where a proof lives in another Lean world (§5.2). F is not compiled as one file.

**Declarations proved by this task.** All compile with `lake env lean` (exit 0, no `sorry`), and `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each (VERIFIED; outputs `scratch/frontier/TYZChain_out.txt`,
`TopChain_out.txt`).

```lean
-- scratch/frontier/TYZChain.lean: tyz-cm's eleven Shimura modules and cm-bridge's Bridge.lean, both as on
-- cm-bridge ed50dc33 (which merges tyz-cm 0ad48a7d), verbatim minus imports (build_tyz.py), then:
theorem ZInQ.GZTheta.Frontier.newCM : ZInQ.GZTheta.NewCM     -- verbatim copy of atkin-li's proof
theorem ZInQ.GZTheta.Frontier.heckeThetaNewform : ZInQ.GZDecomp.HeckeThetaNewform
theorem ZInQ.Frontier.tyzThm35ReadingA_of_open (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hS : ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ ZInQ.Contrib.TYZGenus.CMBridge.tyzZ)
    (h5 : ZInQ.Contrib.TYZGenus.CMBridge.Lemma321Five) :
    ZInQ.Literature.TYZThm35ReadingA
theorem ZInQ.Frontier.frozenTarget_of_open (hH : ZInQ.SixContactMin) (h11 …) (h1 …) (h29 …) (hS …)
    (h318 …) (h35 …) (h5 …)                          -- the seven hypotheses above
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
-- scratch/frontier/TopChain.lean: the same over fork main's modules only
theorem ZInQ.Frontier.frozenTarget_of_open_main (hH : ZInQ.SixContactMin)
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```
`newCM`/`heckeThetaNewform` show that atkin-li's proof of the GZ leaf `HeckeThetaNewform` compiles verbatim over fork
main's modules; `TYZChain.lean` shows that tyz-cm's and cm-bridge's reductions compose.

**Findings in brief** (§7): since r9, 20 rows proved, three pruned, eleven replaced and fourteen off the route, and
the glue bundle is gone; scenario A is one library theorem with 35 hypotheses, all used, now with the `C_d` route of
the Gross–Zagier hypothesis; its 29 fields are 11 LEAF and 18 GLUE strict by the integrator's table (r9: 51 fields, 39
LEAF); no project-glue Prop is left.

## 1. The chain to `ZInQ.FrozenTarget`

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| C0 (r3) | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` with `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/GZTheta/NewCMFinal.lean` @ main; `Contrib/TYZChain/Main.lean` @ w54 | `SixContactMin`, the 4 TYZ Props of §3.2, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (r1-r2: this task's `frozenTarget_of_open` in `scratch/frontier/TYZChain.lean`, with cm-bridge's 7 TYZ Props) |
| C1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` | `Contrib/GZDecomp/Decomp.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` (via `GrossZagierCd`; `HeckeContinuation`, `FunctionalEquation5` discharged by the proved `ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) |
| C2 | `ZInQ.GZTheta.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner` | `Contrib/GZTheta/NewCMFinal.lean` @ wip/atkin-li 6f77abb1 | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishing`, `GrossZagierHeegner` → `FrozenTarget` |
| C3 | TYZ: §3.1 | | → `TYZThm35ReadingA` |
| C4'''''''''' (r10) | H: `HDec.HSyn.sixContactMin_of_open48 (r : OpenResearchLeaves31) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves25)` | `ZInQKernel/OneProof/H/TailZ55.lean` L30 @ main (leaf-fold33 c0f3d085, over leaf-fold32 6b7a4544, leaf-fold31 2880fef1 and leaf-fold30 a1dddf46: `TailZ38`, `TailZ39`, `TailZ41`-`TailZ55` over leaf-fold29's `TailZ37`, with dcy3-fold's, pi0-fold's and theta-fold2's prunes made in place, the empty glue bundle dropped by hand, the fields that fork PRs and milne-compile prove closed by one autofold, and leaf-fold33's reroutes made as copies in `OneProof/H` that leave the earlier declarations in place; `autofold.py`'s folds, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`; 24 + 3 + 2 fields (§4) |
| C4''''''''' (r9) | H: `HDec.HSyn.sixContactMin_of_open31 (r : OpenResearchLeaves24) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ37.lean` L104 @ main (leaf-fold29 0e70c94e, over leaf-fold28b 8961bb09, which merges leaf-fold-hx 862bd440 into leaf-fold27 f3f288d8, over leaf-fold26 86755ad8, leaf-fold25 bc90deac (which merges leaf-fold23 aa9763a1 and leaf-fold24 b2ae6c53), leaf-fold22b 9a100aa7, leaf-fold21 47bba295 and leaf-fold20 24f97774: `TailZ33`-`TailZ37` and rigid-prune's `TailZ40` over leaf-fold19's `TailZ32`; `autofold.py`'s folds, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`, 26 + 11 + 13 + 1 fields; superseded: leaf-fold30 to leaf-fold33 fold the reports of §4.1 into the next generations |
| C4'''''''' (r8) | H: `HDec.HSyn.sixContactMin_of_open26 (r : OpenResearchLeaves19) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves16) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ32.lean` L47 @ main (leaf-fold19 c2ad4181, folding fork PR #19, over leaf-fold18 3782dac8, leaf-fold17 be8511f3, leaf-fold16 a454ad64, leaf-fold15 63205204 (gt-ega's `TailZ25`), sem-prune 2b486d04 and leaf-fold14 97579a97: `TailZ23`-`TailZ32` over leaf-fold13's `TailZ22`; leaf-fold14 reports `lake build +ZInQKernel.OneProof.Main` passing with standard axioms, and the later folds are `autofold.py`'s, with the build's `open-statements.json` regenerated, REPORTED) | → `ZInQ.SixContactMin`, 30 + 13 + 14 + 1 fields; superseded: leaf-fold20 to leaf-fold29 fold the reports of §4.1 into the next generations |
| C4''''''' (r7) | H: `HDec.HSyn.sixContactMin_of_open16 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ22.lean` L335 @ main (leaf-fold13 29885092, merged in w66: x6-fold e33b690a, which adds `TailZ20`-`TailZ22` over leaf-fold11 b73da969: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, no existing constant changed, REPORTED by x6-fold §1) | → `ZInQ.SixContactMin`, 35 + 15 + 14 + 1 fields; superseded: leaf-fold14's bundles map to leaf-fold9's directly, so `open12` to `open16` are compiled but off the path (leaf-fold14 §1) |
| C4'''''' (r6) | H: `HDec.HSyn.sixContactMin_of_open15 (r : OpenResearchLeaves12) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves11) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ19.lean` L1895 @ main (leaf-fold11 b73da969, merged in w63, with leaf-fold12's `TailZ18`, `TailZ19`; over leaf-fold10 a5df68fe, merged in w61, and the prune 0218a662, merged in w62: `lake build +ZInQKernel.OneProof.Main` passes, standard axioms, no unused field, REPORTED by leaf-fold11 §4) | → `ZInQ.SixContactMin`, 32 + 15 + 13 + 1 fields; superseded: leaf-fold13 fills its bundles inside OneProof |
| C4''''' (r5) | H: `HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ9.lean` L161 @ main (leaf-fold9 cf6914e1, merged in w60; over leaf-fold8's `sixContactMin_of_open8` in `TailZ4.lean`: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open9` without `sorryAx`; REPORTED by its report §1, §4) | → `ZInQ.SixContactMin`, 30 + 18 + 14 + 1 fields; superseded: leaf-fold10 and leaf-fold11 fill its bundles inside OneProof |
| C4'''' (r4) | H: `HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8) (g : OpenGlue7)` | `ZInQKernel/OneProof/H/TailZ4.lean` L265 @ main (leaf-fold8 b0f2f6da, merged in w59; over leaf-fold7's `sixContactMin_of_open7` in `TailX.lean`, w58: `lake build +ZInQKernel.OneProof.Main` exit 0, standard axioms, the closure of `sixContactMin_of_open8` without `sorryAx`; REPORTED by its report §1) | → `ZInQ.SixContactMin`, 31 + 20 + 14 + 1 fields; superseded: leaf-fold9 fills its bundles (`researchLeaves8_of_open9`, `textbookLeaves8_of_open9`) inside OneProof |
| C4''' | H: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6` | `scratch/leaf-fold6/parts/f20_fold6.lean` @ main (leaf-fold6 733d8013, in w55; flat file compiled, REPORTED) | superseded: leaf-fold7 fills its bundles (`researchLeaves5_of_open7`, `glue6_of_open7`, …) inside OneProof |
| C4'' (r3) | H: `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5) (l : OpenAddedLeaves5) (g : OpenGlue5)` | `scratch/leaf-fold5/Leaves5.lean` L121755 @ wip/leaf-fold5 5a7e03d1 (in w54; flat file of the final text, 121 783 lines, md5 5999e1db: `lake env lean` exit 0 in 1570 s, 0 errors, no `sorry`, 349 axiom reports all standard; olean chain and `Check5.lean` compiled; REPORTED by its log) | → `ZInQ.SixContactMin`; 26 + 21 + 21 + 2 fields (§4) |
| C4' (r2) | H: `HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4) (l : OpenAddedLeaves4) (g : OpenGlue4)` | `scratch/leaf-fold4/Leaves4.lean` L118447 @ wip/leaf-fold4 9dcf1ca8 (final; flat file, 118 478 lines, md5 6bbeb639: `lake env lean` exit 0 in 1048 s, 0 errors, no `sorry`, 326 axiom reports all standard; olean chain and `Check4.lean`, the kernel conclusion, compiled; REPORTED by its report and log); on fork main since w49 | → `ZInQ.SixContactMin`; 26 + 19 + 20 + 1 fields (§4) |
| C5 | assemble-port's `HDec.HSyn.sixContactMin_of_leaves5` (C4 of the 17:35 report; 26 + 17 + 27 fields) | `scratch/assemble-port/AssemblePort.lean` L116751 @ 92a27877 | C4' is its successor through leaf-fold2-4: the 17:35 scenario-F edges folded, `chartProper`, `chartQuasiFinite`, `hauptmodulUnique` proved, `periodMapGlue`, `abVarSpreadsOut` reduced to leaves, `DivisiblePoints` removed (leaf-fold4 §1.1); g0-assemble3's 46-glue-field `sixContactMin_of_leaves4` before it |
| C6 | H, per field: §4 | | each open field, or the Props it was reduced to |
| **C0 ∘ C4'''''''''' in the library (r10)** | `ZInQ.OneProof.frozenTarget (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves16) (l : HDec.HSyn.OpenAddedLeaves25) (h11 …) (hL29 …) (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54) (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33) (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0) (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) : ZInQ.FrozenTarget` | `ZInQKernel/OneProof/Main.lean` @ main (OneProof since w56; B9 since leaf-fold-hx; B10 since leaf-fold29; Z10 and B11 since leaf-fold32; Z7, Z11, B12 and B13 since leaf-fold33; leaf-fold33's bundles, with no glue bundle) | scenario A of this report: C4'''''''''' with theta-wp8's B9, h29-ne3's B10, the fork PRs' and t21-proof's B11, hfx-proof's and hp23-proof's B12 and hcm-dict's B13 (§3.1), the `C_d` form Z7 with bfh-gamma0's Z10 and the `C_d` route Z11 (§2.1) and the kernel's C1 |

The fork's registered headline (`ZInQKernel/MainLiterature.lean`) has five hypotheses; two are proved
(`ZInQ.Contrib.heckeContinuation`, `functionalEquation5`) and C1 already uses them. C4' concludes the kernel's
`ZInQ.SixContactMin` (the flat file imports the kernel's definition; `Leaves.lean` is wrapped in `namespace HDec`), so
C0 and C4'''''''''' compose by modus ponens. Earlier compiled H assemblies (cpts-transport's 44-field and linked-ram's
45-field `GluePieces5` in the W0 world, lt-goodred's and linked-frob's variants, leaf-fold2's
`sixContactMin_of_open2`) are superseded by C4, C4', C4'', C4''', C4'''', C4''''', C4'''''', C4''''''', C4'''''''' and
C4'''''''''.

## 2. GZ: `ZInQ.Literature.GrossZagier`

Only `C_d`, `d ≡ 5 (mod 8)` squarefree, is used (gz-decomp §0.3): the chain goes through `ZInQ.GZDecomp.GrossZagierCd`,
which `Literature.GrossZagier` implies (`grossZagierCd_of_grossZagier`).

### 2.1 Chain (VERIFIED: signatures read; Z5 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| Z1 | `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd` | `Contrib/GZDecomp/Scope.lean` @ main | `SixContactMin`, `TYZThm35ReadingA`, `GrossZagierCd` → `FrozenTarget` |
| Z2 | `ZInQ.GZDecomp.grossZagierCd_of_leaves'` | `Contrib/GZDecomp/Decomp.lean` @ main | `HeckeThetaNewform`, `FHNonvanishing`, `GrossZagierHeegner` → `GrossZagierCd` (glue G1-G6 proved) |
| Z3 | `ZInQ.GZTheta.heckeThetaNewform : HeckeThetaNewform` | `Contrib/GZTheta/NewCMFinal.lean` @ atkin-li 6f77abb1 | no hypotheses (also `AtkinLiTwistNew`, `NewformUniqueAcrossLevels` proved there) |
| Z5 | `ZInQ.GZTheta.Frontier.heckeThetaNewform` | `scratch/frontier/TYZChain.lean`, `TopChain.lean` | verbatim copy of Z3, compiled over fork main, standard axioms |
| Z6 (r9) | `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE` | `ZInQKernel/Contrib/OneProof/FHNonvanishing.lean` L25 @ main (gz-fh 75a3c0bd, in the library since leaf-fold24) | `FriedbergHoffsteinB_FE` → `FHNonvanishing` (the twisted functional equation `TwistFunctionalEquation` proved); both scenarios used it in r9 (r10: off the route, Z10) |
| Z7 (r9, F) | `ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd` with `ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing` | `ZInQKernel/Contrib/GZStatements/Weak.lean` L138, L94 @ main (gz-statements 0b742fc5, on main since 11-13) | `SixContactMin`, `TYZThm35ReadingA`, `FHNonvanishingCd`, `GrossZagierHeegnerCd` → `FrozenTarget`, and `FHNonvanishing` → `FHNonvanishingCd` (the headline applies `hL2` and `hL3` only at the curves `C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)` squarefree; scenario F's top in place of C2 since r9, and since leaf-fold33 the library theorem's too; both scenarios use it) |
| Z8 (r9, F) | `ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean` L675 @ main (jacobi-lambda b6fc38e9, over gz-weil's first commits, merged by leaf-fold-hx) | `WeierstrassUniformization`, `HeegnerPointRationalCd`, `GrossZagierFormulaCd`, `GrossConjugationCd` → `GrossZagierHeegnerCd` (gz-hl3's split at the curves `C_d`, the Heegner point built from Mathlib's Weierstrass `℘` and the Eichler integral of the newform; its parametrization leaf `ShimuraCMParamCd` proved by gz-weil's twist and uniformization steps from Jacobi's derivative formula `dλ/dt = πiλθ₄⁴`, which jacobi-lambda proves; r10: off the route, Z11's heegner-32 edge proves `GrossZagierHeegnerCd` first) |
| Z9 (r9, F) | `ZInQ.GZHeegner.heegnerPointRationalCd_of_printed` | `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean` L18 @ main (gz-heegner 58a780e4, merged, not folded) | `ShimuraMainCM`, `X0ModuliGaloisMero` → `HeegnerPointRationalCd` (Shimura reciprocity at the Heegner points and the canonical model of `X₀(N)` for functions with poles in `ℍ`; r10: off the route, with Z8) |
| Z10 (r10) | `ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0` | `ZInQKernel/Contrib/OneProof/BFHGamma0.lean` L176 @ main (bfh-gamma0 96a4acb9, over bfh-leaf and bfh-kronecker, folded by leaf-fold32) | `BFHClauseIIGamma0` → `FHNonvanishing` (Bump–Friedberg–Hoffstein's clause (ii) for the classical `Γ₀(N)` newform with the Kronecker symbol; the library theorem takes `hBFH` in place of `hFH`); both scenarios use it |
| Z11 (r10) | `ZInQ.Heegner32.grossZagierHeegnerCd_of_printed`, `ZInQ.GZAlg.grossZagierFormulaCd_of_alg`, `ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof`, `ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof`, `ZInQ.GZConj.grossConjugationCd` | `ZInQKernel/Contrib/OneProof/HeegnerPointRationalCd.lean` L33, `ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean` L681, `ZInQKernel/Contrib/OneProof/Gamma0QExpansion.lean` L52, `ZInQKernel/Contrib/OneProof/EtaW32Character.lean` L461, `ZInQKernel/Contrib/OneProof/GrossConjugationCd.lean` L795 @ main (heegner-32 718d8d4c, gzopt-dict 92b6cd1e over period-odd, cd-optimal and gz-optimal, gamma0-qexp 8d1223be, etaw32-proof 21a80bfa and gz-conj 2c7ce521, folded by leaf-fold33) | `ShimuraMainCM`, `GrossZagierFormulaCd`, `GrossConjugationCd` → `GrossZagierHeegnerCd`; `GrossZagierAlgOptCd`, `Gamma0QExpansion`, `EtaW32Character` → `GrossZagierFormulaCd`; no hypotheses → `Gamma0QExpansion`, `EtaW32Character`, `GrossConjugationCd` (the Heegner point from `hCM` and the two Gross–Zagier statements at the curves `C_d`, with no Weierstrass uniformization and no canonical model of `X₀(N)`; the formula at `C_d` from Gross–Zagier over the algebraic `X₀(N)`, the `q`-expansion principle on `Γ₀(N)` and the eta-quotient law at level 32; the library theorem takes `hGZ` in place of `hL3`); both scenarios use it |

Off the route since r9: gz-hl3's general split `ZInQ.GZHL3.grossZagierHeegner_of_leaves` (six leaves, among them the
composites `StrongWeilCurve` and `IsogenyLattice`: Eichler–Shimura and Faltings' isogeny theorem for every elliptic
curve over `ℚ`) and gz-heegner's `ZInQ.GZHeegner.heegnerPointRational_of_printed`. Until leaf-fold33 the library
theorem's `hL3` was that general form, so `#discharges` could not show the `C_d` route as a discharge of it (gz-weil
§0); leaf-fold33 folds the route into `Main.lean` by hand (gzopt-dict).

### 2.2 Open Props (2: 1 LEAF, 1 GLUE in the strict count; 1 LEAF, 1 GLUE in the lenient count)

| # | Lean name | defined in | class | nearest published sources (all numbers UNVERIFIED) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| Z-8 | `ZInQ.BFHPrinted.BFHClauseIIGamma0` | `ZInQKernel/Contrib/OneProof/BFHGamma0.lean` L85 @ main | **LEAF**: Bump–Friedberg–Hoffstein's clause (ii) for weight-2 newforms on `Γ₀(N)`: for the sign `ε` of the functional equation and every finite set `S` of primes containing those dividing `N`, some fundamental discriminant `D ≠ 1` with `εD > 0` and every `p ∈ S` split in `ℚ(√D)` has `L(1, F, χ_D) ≠ 0`, with `χ_D` the Kronecker symbol; bfh-gamma0 proves `FHNonvanishing` from it (Z10) (replaces Z-3) | Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), opening theorem, clause (ii) (locator UNVERIFIED) | bfh-gamma0, over bfh-leaf and bfh-kronecker; hypothesis `hBFH` of the library theorem since leaf-fold32 | no | published form: Bump–Friedberg–Hoffstein 1990, clause (ii), for the classical `Γ₀(N)` newform with the Kronecker symbol as printed (bfh-gamma0); kinds.tsv flag: definition-level readings (the Petersson coset sum as the fundamental-domain integral, the Atkin–Lehner newform, `ε` over `completedL`, `L(1)` as the value of every continuation); under Diamond–Shurman's Def. 5.8.1 the `U_p`-eigen property for the `Γ₀` action is not proved; a cloud read matched it clause by clause; unread by a human |
| Z-9 | `ZInQ.GZAlg.GrossZagierAlgOptCd` | `ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean` L138 @ main | GLUE (composite): the Gross–Zagier formula over the algebraic curve `X₀(N)`, for every short model `E'` in the isogeny class of a curve `C_d`, `d ≡ 5 (mod 8)` squarefree: for a weight-2 newform `f` on `Γ₀(N)` with `L(f) = L(E')`, a `ℚ`-embedding `φ^* : ℚ(E') → ℚ(X₀(N))` read through `q`-expansions as an optimal parametrization, and a Heegner discriminant `D < −4`, a point `y` with `ι(y) = n Σ φ(τ_r)` has `(L(f) L(f ⊗ χ_D))'(1) = κ ĥ(y)` for some `κ > 0`; gzopt-dict proves `GrossZagierFormulaCd` from it with the `q`-expansion principle on `Γ₀(N)` and the eta-quotient law at level 32 (`grossZagierFormulaCd_of_alg`; gamma0-qexp and etaw32-proof prove those two) (replaces Z-5) | Gross–Zagier, Invent. Math. 84 (1986) 225–320, Thm I.6.3 and Ch. V Thm 2.1, strong Weil case (locators UNVERIFIED) | gzopt-dict, over period-odd, cd-optimal and gz-optimal; hypothesis `hGZ` of the library theorem since leaf-fold33 | after main: gz-dict2 (`GrossZagierAlgOptCd`) | composite: Gross–Zagier 1986 Thm I.6.3 and Ch. V Thm 2.1 with the constant forgotten (gzopt-dict rates it printed); kinds.tsv: published kind, GLUE (pending reading: fold33-review finds three steps between the print's morphism `φ : X₀(N) → E` and the Lean pull-back not proved in Lean: D1, `ℚ`-embeddings of function fields are morphisms of the curves; D2, `φ` at Heegner points read through `q`-expansions; D3, `IsOptimalParam` is the strong Weil parametrization), so a composite by the integrator's convention |

Retired rows: r9: Z-1 `FHNonvanishing` (replaced by Z-3, gz-fh, Z6); Z-2 `GrossZagierHeegner` (split in scenario F
through its `C_d` form, Z7 to Z9; it stayed the hypothesis `hL3` of the library theorem until leaf-fold33 replaced it
by the `C_d` route, Z7 with Z11); r10: Z-3 `FriedbergHoffsteinB_FE` (replaced by Z-8: bfh-gamma0, Z10); Z-4
`WeierstrassUniformization` and Z-7 `X0ModuliGaloisMero` (off the route: Z11); Z-5 `GrossZagierFormulaCd` (replaced by
Z-9: gzopt-dict, Z11); Z-6 `GrossConjugationCd` (proved: gz-conj, Z11).

Already on record, not applied (gz-decomp §0.3): replace the premise `Literature.GrossZagier` by `GZDecomp.GrossZagierCd`.

## 3. TYZ: `ZInQ.Literature.TYZThm35ReadingA`

Caveats attached to every row (tyz-decomp §0): reading A is printed in no refereed text (only in Smith,
arXiv:1603.08479, Thm 2.1, unrefereed); TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 = Asian J. Math. 21 (2017) 721–774,
read by AI agents in the arXiv version only; `Lnnnn` are lines of its source `Period7.tex` as quoted by the reports
(not on this host); Proposition N and the encoding were reviewed by AI models only.

### 3.1 Chain (VERIFIED: signatures read by `chain.py`; T0 compiled here)

| step | theorem | file @ commit | hypotheses → conclusion |
|---|---|---|---|
| A1 | `ZInQ.Contrib.TYZDecomp.tyzThm35ReadingA_of_leaves` | `Contrib/TYZDecomp/Leaves.lean:380` @ main | `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`, `TYZGenusPackage` |
| A2 | `ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_cmLeaves` | `Contrib/TYZGenus/Package.lean:948` @ main | h11, h1, h29, `CMFieldOfDefinitionTYZ`, `IInH4`, `TYZSigmaFixesZn`, `HprimeNormal`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` |
| A3 (finest in a kernel module on main) | `ZInQ.Contrib.TYZGenus.RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` | `Contrib/TYZGenus/RingClassBridge.lean:55` @ main | h11, h1, h29, `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaFixesZn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → GenusPointLeafCM ℓ` (`IInH4`, `HprimeNormal` proved: `iInH4`, `hprimeNormal`); used by `TopChain.lean` |
| B1 (cm-bridge, scratch) | `ZInQ.Contrib.TYZGenus.CMBridge.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five` | `scratch/cm-bridge/Bridge.lean` L3201 @ cm-bridge ed50dc33 (final; merges tyz-cm 0ad48a7d) | h11, h1, h29, `Shimura.ShimuraReciprocityModFn`, `Lemma318Literal HHprime`, `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ`, `Lemma321Five` |
| inside B1 | cm-bridge: `GenusFieldLeLni`, `IInHprime`, `BetaOnGenus7`, `tyzThm36Seven_of` (TYZ Thm 3.6(3) from `ShimuraReciprocityPic`, `EtaModelFricke`, `CMAlgebraic`); tyz-cm: `etaModelInvariant`, `etaModelEquation`, `etaModelFricke`, `etaCuspGrowth`, `xQExpRational`, `yQExpRational`, `cmValueRingClass_of_modFn`, `shimuraReciprocityPic_of_shimuraModFn`, `cmFieldOfDefinition_of_cmValueRingClass` (proved) | `ZInQKernel/Contrib/TYZGenus/Shimura*.lean` (11 modules) and `Bridge.lean` @ ed50dc33 | |
| **T0** (this task, compiled) | `ZInQ.Frontier.tyzThm35ReadingA_of_open` (= B1) | `scratch/frontier/TYZChain.lean` (B1 with the 11 tyz-cm modules, verbatim) | the 7 Props of the 17:35 list → `TYZThm35ReadingA`; with B2-B4, the 5 Props of §3.2 |
| B2 (r2) | `ZInQ.Contrib.TYZLcal.tyzLcalOne_of_leaves` | `scratch/tyz-lcal/TYZLcal.lean` L900 @ tyz-lcal 61d0b14e (on main since w52) | `TYZThm11Integral`, `TYZLemma29Mod2` → `TYZLcalOne` (Theorem 1.1 at `m = 1`, Lemma 2.9 mod 2 at `m = 3`, and an analytic bound `‖L(C₁,1)‖ ≤ 3.35` from the fork's Hecke continuation) |
| B3 (r2) | `ZInQ.Contrib.TYZGenus.T321.lemma321Five_of_shimuraModFn'` | `scratch/tyz-321/L321.lean` L5460 @ tyz-321 521eacc0 | `Shimura.ShimuraReciprocityModFn` → `Lemma321Five` (ring class field theory, the kernel's genus theory, cm-bridge's genus characters; no TYZ text) |
| B4 (r2) | `ZInQ.Contrib.TYZGenus.TYZ35.thm35First_of_lcal_thm33` | `scratch/tyz-35/Thm35.lean` L1363 @ tyz-35 a8101726 (on main since w52) | `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `∀ ℓ, IsTYZLcal ℓ → Thm35First ℓ tyzZ` |
| B5 (r3) | `T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn` with `Sqrt2Glue.sqrtTwoNotInHHprime` | `Contrib/TYZChain/Lemma318.lean`, `Sqrt2Glue.lean` @ w54 (tyz-318 94b05c87, sqrt2-glue 84107b66) | → `Lemma318Literal HHprime`, no hypotheses (ss-exponent proved the supersingular exponent tyz-318 used) |
| **T0 (r3, kernel)** | `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` | `Contrib/TYZChain/Main.lean` @ w54 (tyz-chain; B1 with B2-B5 as kernel modules) | `TYZThm11Integral`, `TYZLemma29Mod2`, `Shimura.ShimuraReciprocityModFn`, `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ` → `TYZThm35ReadingA`; both scenarios used it until r8 (r9: off the route, B9) |
| T0' (r4) | `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33` | `ZInQKernel/OneProof/TYZSplit.lean` @ main (tyz-split 99e582b5, compiled into OneProof by leaf-fold8) | `TYZThm33` → T0's hypothesis `∀ ℓ, IsTYZLcal ℓ → TYZThm33Pinned ℓ`, so T-11 follows from the printed Theorem 3.3; both scenarios used it until r8 (r9: B9 takes `TYZThm33` itself) |
| B6 (r4) | `ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` | `scratch/tyz-split/T5.lean` @ main | `CMModuli`, `X0RatStructure` → `Shimura.ShimuraReciprocityModFn`; scenario F used it until r7 (r8: off the route, B8) |
| B7 (r6) | `T5Glue.cmModuli_of_t5'`, `T5Glue.x0RatStructure_of_leaf` | `scratch/t5-glue/T5Glue.lean` @ main (t5-glue 39bb3cd2, merged in w66; r6 read it at the earlier head 405763f6, the same file; the later commits add the report and its second review, which finds `RingClassLattice` true) | `ShimuraMainCM`, `RingClassLattice` → `CMModuli` (the absolute Artin map's surjectivity and `InvertibleColon` proved over Tau Ceti); `X0ModuliGalois` → `X0RatStructure`; scenario F used them under B6 until r7 (r8: off the route, B8) |
| B8 (r8) | `T5Glue.shimuraReciprocityModFn_of_printed` | `ZInQKernel/Contrib/OneProof/RingClassLattice.lean` L3353 @ main (gt-ringclass 06f03bd4, folded by leaf-fold17: t5-glue's development verbatim, with `RingClassLattice` proved as `T5Glue.ringClassLattice`) | `ShimuraMainCM`, `X0ModuliGalois` → `Shimura.ShimuraReciprocityModFn`; the library theorem took T-15 and T-16 in place of `hS`, so both scenarios used it in r8 (r9: off the route, B9) |
| B9 (r9) | `ThetaWP8.tyzThm35ReadingA_noHX` | `ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean` L890 @ main (theta-wp8 04afc477, with hx-used's eta route, folded by leaf-fold-hx) | `TYZThm11Integral`, `TYZLemma29Mod2`, `ShimuraMainCM`, `TYZThm33` → `TYZThm35ReadingA`: Shimura reciprocity for modular functions at level 32 from `ShimuraMainCM` alone, with `ThetaWeierstrass8` proved; the library theorem drops `hX`, so both scenarios use it |
| B10 (r9) | `ZInQ.Contrib.TYZDecomp.H29Split.tyzLemma29Mod2_of_sixLeaves` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L864 @ main (h29-ne3 a03caff2, over h29-split and h29-fix, folded by leaf-fold29) | `LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZTestVectorExists`, `TYZLemma29PrintedNe3`, `TYZThm21At31`, `TYZProp23Printed` → `TYZLemma29Mod2`: the mod-2 reading of Lemma 2.9 from TYZ's printed statements over genuine definitions (the quaternion algebra's test vectors and genus periods), with Lemma 2.9 at `n = 3` replaced by Theorem 2.1's instance; the library theorem takes the six in place of `h29`, so both scenarios use it |
| B11 (r10) | `ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof`, `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof`, `ZInQ.Contrib.T21Proof.tyzThm21At31` | `ZInQKernel/Contrib/OneProof/LegendreThreeSquares.lean` L22, `ZInQKernel/Contrib/OneProof/JonesPall.lean` L20, `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean` L104 @ main (fork PRs #36 47ca4df2 and #38 a9bc2e35 and t21-proof f597c34c, folded by leaf-fold32) | no hypotheses → `LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZThm21At31`: three of B10's six leaves proved (`TYZThm21At31` from the Brandt value at 3 and rigorous bounds for two `L`-values by kernel computation), so the library theorem takes three; both scenarios use it |
| B12 (r10) | `ZInQ.Contrib.HfxProof.tyzTestVectorExists`, `ZInQ.Contrib.HP23Proof.tyzProp23Printed` | `ZInQKernel/Contrib/OneProof/TYZTestVectorExists.lean` L26, `ZInQKernel/Contrib/OneProof/TYZProp23Printed.lean` L27 @ main (hfx-proof 779d0d7d and hp23-proof ca83418a, folded by leaf-fold33) | no hypotheses → `TYZTestVectorExists`, `TYZProp23Printed`: two more of B10's six leaves proved, so five are theorems and the library theorem takes one, `hL29`; both scenarios use it |
| B13 (r10) | `ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed` | `ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean` L442 @ main (hcm-dict d1ae76f6, folded by leaf-fold33) | `ShimuraThm54` → `ShimuraMainCM` (Shimura's Theorem 5.4 as printed, over short Weierstrass models; the print's analytic isomorphisms matched to `IsAnalyticUnif` in Lean); the library theorem takes `hCM` of that type; both scenarios use it |

### 3.2 Open Props (4: 3 LEAF, 1 GLUE in the strict count; 4 LEAF, 0 GLUE in the lenient count)

| # | Lean name | defined in | class | citation (UNVERIFIED unless marked) | last task; newest commit | running now | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| T-1 | `ZInQ.Contrib.TYZDecomp.TYZThm11Integral` | `Contrib/TYZDecomp/Leaves.lean` @ main | **LEAF** (specialization: odd `m` only) | TYZ Thm 1.1, first assertion, L371–380 (read by nt-tyz) | tyz-decomp; main (tyz-lcal audit 11-13: faithful, not stronger) | no | published form: specialization of TYZ Thm 1.1 to odd `m` (tyz-lcal audit: faithful, not stronger) |
| T-12 | `ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` | `ZInQKernel/OneProof/TYZSplit.lean` L157 @ main | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count) | TYZ Theorem 3.3 over the kernel's definitions, for `n ≡ 5, 7 (mod 8)`, `𝒫(d)` existential | tyz-split | after main: h33-dict (`TYZThm33`) | consequence of one theorem: TYZ Thm 3.3, Period7.tex L1299-1311, specialized (tyz-split §1), carried along the kernel's eta model of `X₀(32)` by the q-expansion principle (`IsRatModFn 32`), which already sits behind `hS`; a clause-by-clause statement review found the leaf Thm 3.3 or weaker (tyz-split §1 and the docstring, wip/w61 3c241950); the `[i]` sign of the base point is printed (`α = −i` in the Hecke-action proof, about L1564-1566), and h33-sign pins it in Lean by TYZ Thm 3.6(1) (kinds.tsv's flag since leaf-fold22b); re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): `PchiG` uses the eta-quotient map `φ_C` where TYZ use the algebraic `ℚ`-isomorphism `i₀` (the analytic uniformization of `X₀(32)`), and choosing `ε` before `φ` needs TYZ Prop. 3.2(4) (kinds.tsv) |
| T-21 | `ZInQ.Contrib.TYZDecomp.H29Split.TYZLemma29PrintedNe3` | `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` L455 @ main | **LEAF**: TYZ Lemma 2.9 as printed, for squarefree `1 < n ≡ 1, 3 (mod 8)` with `n ≠ 3`: `Q(n) = Σ ε 𝓛(d₁)𝓛(d₂)` over the decompositions `n = d₁d₂` (at `n = 3` the print is false: `Q(3) = ±3` while `𝓛(3)² = 1`) (replaces T-3) | TYZ Lemma 2.9, L1062–1066 | h29-ne3, over h29-split and h29-fix; hypothesis `hL29` of the library theorem since leaf-fold29 | after main: tyz-genus (`TYZLemma29PrintedNe3`) | published form: TYZ Lemma 2.9, restricted to odd classes, `n > 1`, `n ≠ 3` (h29-ne3) |
| T-24 | `ZInQ.Contrib.HCMDict.ShimuraThm54` | `ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean` L426 @ main | **LEAF**: Shimura's Theorem 5.4 as printed: for `K = ℚ(√−m)`, `σ ∈ Aut(ℂ)` and an idele `s` with `σ = [s, K]` on `K^ab`, a lattice `𝔞` in `K` and an analytic isomorphism `ξ : ℂ/𝔞 → E(ℂ)` onto a short Weierstrass curve, some analytic isomorphism `ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` has `ξ(u)^σ = ξ'(s⁻¹u)` for `u ∈ K/𝔞` (uniqueness of `ξ'` dropped; "analytic isomorphism" is `IsAnalyticUnif`, matched to the print in Lean by `isAnalyticUnif_iff`); hcm-dict proves `ShimuraMainCM` from it (`HCMDict.shimuraMainCM_of_printed`) (replaces T-15) | Shimura 1971 (Introduction to the arithmetic theory of automorphic functions), Thm 5.4; Lang, Elliptic functions, Ch. 10 Thm 3 (numbers UNVERIFIED) | hcm-dict; hypothesis `hCM` of the library theorem since leaf-fold33 | no | published form: Shimura 1971 Thm 5.4 as printed, over short Weierstrass models, uniqueness dropped (hcm-dict); kinds.tsv: unread, a new printed leaf |

Retired rows: T-2 `TYZLcalOne` (proved, B2), T-4 `Lemma318Literal` (proved, B5), T-6 `Thm35First` (reduced to T-11,
B4), T-7 `Lemma321Five` (proved, B3); r4: T-5 (split by tyz-split into `CMModuli` and `X0RatStructure`), T-11 (from
the printed TYZ Thm 3.3 (`TYZThm33`, tyz-split)); r6: T-13 `CMModuli` and T-14 `X0RatStructure` (split by t5-glue,
B7); r8: T-17 `RingClassLattice` (proved by gt-ringclass, B8); r9: T-16 `X0ModuliGalois` (off the route, B9:
leaf-fold-hx removes `hX`), T-3 `TYZLemma29Mod2` (replaced by T-18 to T-23, B10: leaf-fold29 takes h29-ne3's six
leaves). T-15 is a hypothesis of the library theorem since r8, defined in gt-ringclass's verbatim copy of t5-glue's
file; leaf-fold-hx re-rates it a consequence. r10: T-18 `LegendreThreeSquares`, T-19 `JonesPallX2Y2Z16` and T-22
`TYZThm21At31` (proved by fork PRs #36 and #38 and t21-proof, B11); T-20 `TYZTestVectorExists` and T-23
`TYZProp23Printed` (proved by hfx-proof and hp23-proof, B12); T-15 `ShimuraMainCM` (replaced by T-24: hcm-dict, B13);
T-12 is re-rated a consequence (the dictionary pass).

## 4. H: `ZInQ.SixContactMin`

Base (r10): leaf-fold33's compiled C4'''''''''' (c0f3d085), inside OneProof: leaf-fold30 (a1dddf46; ds965-weak,
sgr-fold with sgr-direct, persists-dvr, dcy3-fold), leaf-fold31 (2880fef1; pi0-fold, fork PR #24, the Pic dictionary
ruling), leaf-fold32 (6b7a4544; abhyankar with nv-local, the empty glue bundle dropped, theta-fold2 with theta-direct,
fork PRs #25, #29, #31, #34 to #36 and #38, milne-compile, gt-sga3, bfh-gamma0, t21-proof, ega-limit, dict-models,
dict-galois's `r7a` part, coeff-fix with coeff-ext, pic-fix with pic-dict, the dictionary pass's re-rating) and
leaf-fold33 (neron-sh-proof, poincare-proof, gzopt-dict over period-odd, cd-optimal and gz-optimal with heegner-32 and
gz-conj, phi-ample, homfree-noemb, etaw32-proof, hfx-proof, gamma0-qexp, hp23-proof, fold33-copy with sga3-nbhd and
goodmodel-iso, hcm-dict, fold33-review's flag on `hGZ`, fold33-pic with phisurj and piczero-char0, idcomp-lft,
piclft), over r9's base 0e70c94e (leaf-fold29) and the folds before it. Bundles: `OpenResearchLeaves31` (24),
`OpenTextbookLeaves16` (3) and `OpenAddedLeaves25` (2); the glue bundle is gone, its last field proved. The fields'
forms are the integrator's `kinds.tsv`: 13 published, 11 consequences, 5 composites, 0 project glue by kind. Its
strict and strictest columns agree; two published kinds are GLUE in both, pending a reading (`sga7_IX_3_3_SHpre`,
`sga7_IX_3_5_ForwardGeom`), and so is the top's `hGZ`; this report records them as composites, the integrator's
convention. Its six rows with bundle `frozenTarget` give the forms of the top (§2.2, §3.2). `chain.py` reads the
bundles from `ZInQKernel/OneProof/H/TailZ50.lean`, `ZInQKernel/OneProof/H/TailZ55.lean` at main. Row numbers are kept,
retired rows listed, new rows from H-214 (§4.16), Z-8 (§2.2) and T-24 (§3.2).

### 4.1 What changed since r9 (signatures VERIFIED by `chain.py`)

Compiled into C4'''''''''' (scenario A), fold by fold. leaf-fold30: ds965-weak restates `dsThm965` (H-125) as
`dsThm965Weak`, its weakest printed reading (`ρ(Frob_𝔭)` has the Hecke polynomial as characteristic polynomial or
satisfies it), and proves the old field from it with the kernel's Chebotarev density; sgr-direct proves
`HeckeVertWitness`, the one consumer of both `shimuraIntegralModelRep` (H-210) and the glue field
`quotientP1Coordinate`, from bundle fields and one new glue Prop, `NVLocalInertia`, with no integral model, and
sgr-fold prunes both fields and takes `nvLocalInertia` as a glue field; persists-dvr proves `semistablePersistsSHcp`
(H-203) from the fields `sga3_VIB_3_10` (H-174), `sga7_IX_3_3_SH` (H-207), `neronBaseChangeStrictHenselization`
(H-205) and `geomConnOfRationalPoint` (H-99); and dcy3-fold prunes `deligneComponentsY3PrintedAb`, threading
`Y3Connected` from `mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU` (dcy3-used's replacement, which scenario F took
in r9). leaf-fold31: pi0-fold prunes `geomConnOfAlgClosure` (H-150) and `deligneComponentsX6PrintedAb` (H-192), which
fed only `R1pi0Props`, the last conjunct of `R1R2fpRep`, read by no live constant; fork PR #24 proves
`regularSmoothPerfect` (H-118) from the vendored theorem that a regular local ring is formally smooth over a perfect
field; and the integrator's Pic dictionary ruling re-rates `picZeroAbVar` (H-200), `phiAmpleIsogeny` (H-201) and
`weilPairingMumford` (H-202) as consequences. leaf-fold32: abhyankar proves nv-local's `TameBranchNormal` with no
hypotheses, so `nvLocalInertia` is proved and the glue bundle goes; the dictionary pass re-rates `gagaMorphism`
(H-105) as a consequence and keeps `picRepresentableAbVar` (H-199) a leaf; theta-fold2 removes `thetaRatiosAlgebraic`,
whose one reader uses only theta-split's use form `ThetaRatiosAtQM`, which theta-direct proves with no hypotheses;
fork PR #25 proves `geomConnOfRationalPoint` (H-99), fork PR #29 `tateTwistInvariants` (H-120) and `axSenTate`
(H-121), fork PR #31 `groupSchemeEquidim` (H-100), fork PR #34 `cartierSmooth` (H-98), fork PR #35
`uniformizationLeafAll` (H-103), and milne-compile compiles fork PR #23's proof of `milneIsogenyQuasiInverse` (H-104),
seven fields closed by one autofold in `TailZ44`; gt-sga3 narrows `sga3_VIB_3_10` (H-174) to its neighbourhood form
`sga3_VIB_3_10_Nbhd` and proves the old field from it and `geomConnOfRationalPoint`. A second autofold (`TailZ45`)
takes the dictionary pass's printed restatements: ega-limit proves `egaIV_8_10_5_xii` (H-65) from vendored Stacks
material (Chow's lemma over an affine noetherian base, Stacks 081F); dict-models proves `sga7_IX_3_3_SH` (H-207),
`raynaudSemistableSH` (H-182), `mumfordGroupLaw` (H-211) and `neronBaseChangeStrictHenselization` (H-205) from H-218,
H-217, `mumfordGroupLawConn` and `blr_7_2_1`, each the print or the print with a reading made explicit; dict-galois
proves `r7a` (H-5) from its form over a separable closure, H-219; coeff-ext and coeff-fix prove `dsThm965Weak` from
Diamond–Shurman 9.6.5 as printed, H-214, with H-215, and `dsThm966` (H-126) from Deligne–Serre's Theorem 4.1 as
printed, H-216; pic-fix proves `phiAmpleIsogeny` (H-201) from `mumfordKLFiniteSectionAC` and `mumfordPhiSurjectiveAC`,
two printed Mumford leaves; and the dictionary pass re-rates nine fields (§0). On the top, fork PRs #36 and #38 prove
`hL3s` (T-18) and `hJP` (T-19), t21-proof proves `hT21` (T-22; B11, §3.1), the top's `h33` (T-12) is re-rated a
consequence, and bfh-gamma0 proves `FHNonvanishing` from Z-8, Bump–Friedberg–Hoffstein's clause (ii) on `Γ₀(N)`, so
`hBFH` replaces `hFH` (Z-3; Z10, §2.1).

leaf-fold33 (one step at a time, each checked: `docs/research/leaf-fold33.md`): neron-sh-proof proves
`neronBaseChangeStrictHenselization` (H-205) outright, and with it the BLR §7.2 Thm 1 form `blr_7_2_1`; poincare-proof
proves `poincareComplement` (H-72) from five open fields; phi-ample proves `mumfordKLFiniteSectionAC` from
`picRepresentableAbVar` and `picZeroAbVar`; homfree-noemb reroutes Theorem 6, the one reader of
`homFreeFiniteAlgClosed` (H-70), through fields with a ring homomorphism to `ℂ`; sga3-nbhd removes
`sga3_VIB_3_10_Nbhd` (H-174) with no new leaf; goodmodel-iso, over group-law-dvr, proves GIT Thm 6.14 over a DVR from
BLR §1.4 Thm 3 over a Dedekind base, H-220, which replaces `mumfordGroupLawConn` (H-211) and
`neronSchemeExtensionExists` (H-77), its case `D = 𝓞_L`; phisurj proves `weilPairingMumford` (H-202) and
`phiAmpleIsogeny` from `picRepresentableAbVar`, `picZeroAbVar` and `mumfordTorsionAlgClosed`, with a Lean proof of
Mumford §20's nondegeneracy, so `mumfordPhiSurjectiveAC` is rerouted away; and piczero-char0 finds every use of
`picZeroAbVar` (H-200) in characteristic 0 and proves that form from three printed leaves, of which idcomp-lft and
piclft prove `identityComponentLFT` and `picLocFinType` outright, leaving H-221. The reroutes are copies: new modules
in `ZInQKernel/OneProof/H/` carry the rerouted chain, and the earlier declarations stay. On the top, hfx-proof and
hp23-proof prove `hfx` (T-20) and `hP23` (T-23; B12, §3.1); hcm-dict proves `ShimuraMainCM` from T-24, Shimura's
Theorem 5.4 as printed, and `hCM` takes that type (T-15; B13); and gzopt-dict, with heegner-32 and gz-conj, takes the
`C_d` route into the library theorem (Z7, Z11, §2.1): `hL3` goes and `hGZ`, Z-9, Gross–Zagier over the algebraic
`X₀(N)`, comes, with the `q`-expansion principle on `Γ₀(N)` and the eta-quotient law at level 32 proved by gamma0-qexp
and etaw32-proof (Z-5, Z-6; Z-4 and Z-7 are off the route). fold33-review then flags `hGZ` pending a reading, so it
counts GLUE (§4.18). r9's changes are in the r9 report (`git show 8342c2eb:docs/research/frontier.md`, §4.1).

Applied on top by scenario F:

| field of C4'''''''''' (rows) | now | theorems · task · file |
|---|---|---|
| `r17` (H-21) | ⇐ `CarayolRealization` (H-157); the transport to every attached representation is proved (as in r6 to r9) | `ModularSplit.R17.carayolR17'_of_realization` · modular-split · `scratch/modular-split/R17.lean` |
| `eigenformHTNew` (H-127) | ⇐ `KatoRealizationCohSS` (H-181) and `TateTwistInvariants`, `AxSenTate` (as in r6 to r9; since leaf-fold32 both are theorems, fork PR #29) | `CToPrinted2.eigenformHTNew_of_printedSS` · c-to-printed2 · `scratch/c-to-printed2/CToPrinted2.lean` |

On the TYZ side both scenarios use B9 (§3.1): the CM hypothesis rests on `ShimuraMainCM` alone, since leaf-fold33 from
Shimura's printed Theorem 5.4 (B13), and B8, T0 and T0' are off the route. Since leaf-fold22 no row is a leaf on
`R1fpProps` (H-154 is off the route), and the chain's conversions between the two moduli problems take rigid-prune's
`QMFamilyGroupLaw`, proved from `mumfordGroupLaw`, since leaf-fold33 in its DVR form from the field
`neronSchemeExtensionDedekind` (H-220). On the GZ side both scenarios take the `C_d` form of the top since leaf-fold33
(Z7): the headline uses `hL2` and `hL3` only at the curves `C_d`, and Z11 reduces that form to `hGZ` and `hCM`. Since
leaf-fold32 scenario F replaces no consumer: the two fields whose consumers it replaced in r9, `thetaRatiosAlgebraic`
and `deligneComponentsY3PrintedAb`, are gone from the bundles, so `chain.py`'s consumer replacements (`BYPASS`) are
empty.

Off the route since r10 (the edges stay in `chain.py`): mcr-glue's `HDec.MCRGlue.quotientP1Coordinate_of_leaves` with
`MCRGlue.coordinateNormalization_of`, and mcr-quot's `MCRQuot.fibreAutTame_of''`, `MCRQuot.genericQuotientP1_of''`,
`MCRQuot.cMSectionsDisjoint_of''` and `MCRQuot.coordinateFromSections_of''`, with their rows (H-89 to H-97), since
leaf-fold30 prunes the glue field `quotientP1Coordinate` (sgr-fold); theta-glue's
`HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare` and igusa-alg's
`HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.qmThetaSymmetricCurve_of_linYang` (H-190), since leaf-fold32 removes
`thetaRatiosAlgebraic` (theta-fold2); gz-fh's `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE` (Z6), which
bfh-gamma0's Z10 replaces; jacobi-lambda's `ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves4` (Z8) and gz-heegner's
`ZInQ.GZHeegner.heegnerPointRationalCd_of_printed` (Z9), since heegner-32's edge (Z11) proves `GrossZagierHeegnerCd`
first; since r9: unipotent-b's `UnipotentB.semistableUnipotent_of_printedGen` with fork PR #19's
`ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof`, since leaf-fold20 proves `semistableUnipotent`;
shimura-split's `HDec.QMSplit.Moduli.shimuraFamily_of_hol` with route A's `LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab`
and `LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core`, since leaf-fold22 proves `shimuraFamilyAb`; the top's
`ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` (T0), `T5Glue.shimuraReciprocityModFn_of_printed` (B8) and
`ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33` (T0'), which B9 replaces; since r8: reduct-b's
`ReductB.raynaudSemistable_of_SH_pair`, `ReductB.semistablePersistsDVR_of_SH_pair` and
`ReductB.semistableReductionDVR_of_raynaud`, whose fields leaf-fold14 replaces by their strictly henselian forms;
t09-pic's `T09Pic.t09SymmIsogenyExists_of_four`, which leaf-fold14 compiles; tyz-split's
`ZInQ.Contrib.TYZGenus.TYZSplitT5.shimuraReciprocityModFn_of_split` (B6) with t5-glue's `T5Glue.cmModuli_of_t5'` and
`T5Glue.x0RatStructure_of_leaf` (B7), which B8 replaces; since r7: x6-glue's `HDec.QMSplit.Moduli.r1r2_of_published`
and `HDec.QMSplit.Moduli.x6ConicModel_of_published` with route A's `LeafQM.AV.R1UnivRigid.r1R2fpRep_iff_ab`, whose
conclusions x6-fold proves in C4'''''''; reduct-glue's `ReductGlue.raynaudSemistable_of_SH'` and the modus-ponens
steps through `ReductionFromSH`, `PersistsFromSH` and `UnipotentFromSH`, which reduct-b's and unipotent-b's theorems
replace; theta-glue's `HDec.HSyn.G0Split.ThetaPt.ThetaGlue.qmThetaSymmetricCurve_of_alg59`, which igusa-alg's theorem
replaces; since r6: `HDec.QMSplit.Moduli.y3Connected_of_deligne` (shimura-split) and
`ModularSplit.DimJac.dimJacobianEqGenus_of_glue` (modular-split), whose fields leaf-fold10 compiles; reduct-split's
`ReductSplit.raynaudCriterion_final'`, `ReductSplit.semistableReductionThm_final`,
`ReductSplit.semistablePersists_final`, `ReductSplit.semistableNeronBaseChange_of_leaves` and
`ReductSplit.faltingsLemma5BC_final`, whose conclusions are no longer fields; shimura-split's
`HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5` and `HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5` with shimura-glue's
edges, which x6-glue's theorems replace; modular-split's `ModularSplit.EigenHT.eigenformHTNew_of_coh`; qm-split's
`HDec.HSyn.G0Split.ThetaPt.QMSplitTheta.thetaRatiosAlgebraic_of`, whose field theta-split bypasses; cm24-value's
`CM24.igusaCMValue24_field`, now inside C4''''''; since r5: coarse-factor's `r1r2fpRep_of_canonical''`, which
shimura-split's theorem extends; qm-glue's and coarse-factor's `x6ConicModel` theorems with `ConicCanonical`, which is
`X6Kummer.X6ConicModel` verbatim (shimura-split, `Iff.rfl`); height-glue's `r5fpCount_of_t11b`; the cloud-w07 proofs,
now inside C4'''''. The r2-r4 edges compiled inside C4'''' are off the route as well. Retired rows (r2, r3): H-23,
H-26, H-27, H-28, H-29, H-31, H-37, H-39, H-40, H-45, H-47, H-48, H-50, H-55, H-58, H-62; r4: H-1, H-2, H-3, H-8,
H-10, H-14..H-20, H-22, H-24, H-25, H-32, H-33, H-35, H-36, H-38, H-41..H-44, H-46, H-51, H-52, H-54, H-61, H-63,
H-64, H-66, H-67, H-69, H-73..H-76, H-80..H-88, T-5, T-11; r5: H-4, H-12, H-21, H-59, H-78, H-106, H-107, H-108,
H-111, H-114, H-115, H-116, H-127, H-137, H-138, H-139, H-140, H-141, H-143; r6: H-79, H-133, H-134, H-144, H-145,
H-146, H-147, H-149, H-151, H-152, H-153, H-155, H-156, H-158, H-159, H-160, H-161, H-162, H-163, H-164, H-165, H-166,
H-167, T-13, T-14; r7: H-53, H-142, H-177, H-178, H-179, H-180, H-183, H-184, H-186, H-189, H-191; r8: H-101, H-124,
H-129, H-131, H-132, H-135, H-136, H-168, H-171, H-173, H-176, H-185, H-187, H-195, T-17; r9: H-13, H-117, H-119,
H-128, H-130, H-148, H-154, H-169, H-170, H-172, H-175, H-188, H-193, H-196, H-197, H-198, H-206, T-3, T-16, Z-1, Z-2;
r10: H-5, H-65, H-70, H-72, H-77, H-89, H-90, H-91, H-92, H-93, H-94, H-95, H-96, H-97, H-98, H-99, H-100, H-103,
H-104, H-118, H-120, H-121, H-125, H-126, H-150, H-174, H-182, H-190, H-192, H-200, H-201, H-202, H-203, H-205, H-207,
H-210, H-211, T-15, T-18, T-19, T-20, T-22, T-23, Z-3, Z-4, Z-5, Z-6, Z-7. Not applied: the variants each report keeps
aside (r10: the reports of the branches after main (§0); r9: the reports of the branches after r9's main; r8: the
reports of the branches after r8's main; gt-qm's reroute of `yuThm11`'s four live uses (H-128; r9: yu-prune folds it);
unipotent-b's split, which leaf-fold14 left out; r7: sh-route's `strictHenselizationNeron0_final`,
`strictHenselizationPair0_final`, `strictHenselizationInside0_final` and `route_final` from `NeronBaseChangeSH`, whose
statements add `[CharZero K]` and a perfect residue field; reduct-b's Route B-cp, `ss1_ss3_of_cp`, over the restricted
leaf `SemistablePersistsSHcp`, which leaf-fold14 compiles; unipotent-b's `semistableUnipotent0_of_printed`, which
concludes the field with two instances added; t09-pic's split of `WeilPairingMumford` into one printed property per
leaf (L4a-L4f, `t09SymmIsogenyExists_of_split`) and its weaker variants; shimura-cft's `shimuraFamilyAb_of_mainThmI`,
whose leaf implies H-154; gap-triage's `modelYIrreducible_of_open9`, over leaf-fold9's bundle; r6: c-to-printed's
`shimuraFamily_of_mainThmI`, whose leaf `ShimuraMainThmIY3` implies H-154 and is still a consequence; c-to-printed2's
`eigenformHTNew_of_realization` with the leaf `KatoRealization`; theta-split's route 2, `thetaRatiosAtQM_of_cm`
through Shimura's theorem on theta-nulls at CM points; reduct-glue's `strictHenselizationNeron_of` from the pair
`StrictHenselizationDVR`, `NeronBaseChangeUnramifiedDVR`, whose second member may exceed the print; reduct-glue's
`SerreTateFromComplete`, whose field `serreTateThm2` the prune removed; r4: height-split's `r20_of_leaves` with
`IsogenySemistableBaseChange`; curve-split's `x0Transitive_of_igusaSL2X`; qm-split's `qmHauptmodulBase3_of_shimizu`
and `y3Connected_of`; hodge-split's `panBerger_of_templates`; r5: shimura-split's `r1r2fpRep_of_split6`, which keeps
`r1rec` and `r5` as inputs; modular-split's weaker `KatoRealization` leaf; reduct-split's `raynaudCriterion_final`,
which `raynaudCriterion_final'` supersedes by proving the perfect case of its glue).

### 4.2 Research-level fields of r3 still open (3: 2 LEAF, 1 GLUE strict; 2 LEAF, 1 GLUE lenient)

| # | field : Lean name | leaf | class | citation | flags | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|---|
| H-6 | `r9a : PkgI3.FaltingsSemisimple` | R9(a) | **LEAF** | Faltings, Invent. Math. 73 (1983), Satz 3 (erratum 75 (1984)) | UNVERIFIED | pkg-I3 | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-7 | `r9b : PkgI3.FaltingsTate` | R9(b) | **LEAF** | Faltings 1983, Satz 4, Kor. 1 | UNVERIFIED | pkg-I3; after main: faltings-cm (`r9b`) | published form: Faltings 1983 (leaf-review-b §2.3) |
| H-9 | `r11r12 : PkgI4.PanBerger` | R11 + R12 | GLUE (joint consequence of two theorems) | Berger, Invent. Math. 148 (2002), Thm 0.7; Pan, JAMS 35 (2022), Thm 1.0.4 | JAMS numbering UNVERIFIED | pkg-I4; after main: pb-bypass (`r11r12`); pb-fix (`r11r12`); pb-fix2 (`r11r12`); bst-construct (`r11r12`) | composite: Pan and Berger (leaf-review-b §2.4) |

### 4.3 Textbook fields of r3 still open (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

None left: each is proved or split (§4.1).

T6, T7, T8, T9, T11(b), T3, T41, T34 and T38 are proved or reduced (r2); their replacements are rows of §4.5.
T4, T5, T23, T24, T27, T33, T35, T40 and the normal model of a function field are proved or split in r4 (§4.1).

### 4.4 Fields that were glue in C4, still open (in C4'''''''''' they are `OpenAddedLeaves25` fields) (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

| # | field : Lean name | def part | content; nearest published sources (UNVERIFIED) | report's label | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.5 Props introduced by reductions until r3, still open (1: 1 LEAF, 0 GLUE strict; 1 LEAF, 0 GLUE lenient)

| # | Lean name | def file @ commit | from field | class; content; sources (UNVERIFIED) | last task; running | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-71 | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | `Contrib/AVB1/AlgClosed.lean` L51 @ main | t7 (H-27) | **LEAF** (specialization: T7 over algebraically closed fields, without `deg P = 2g` and `P(n) = deg(n − φ)`; Mumford §19 Thm 4) | av-b1; after main: charpoly-ell (`charPolyIndepOfEllAlgClosed`); deg-det (`charPolyIndepOfEllAlgClosed`) | published form: specialization of Mumford §19 Thm 4 (av-b1 §3.2) |

Proved and gone from the tables: r10, `RegularSmoothPerfect` (fork PR #24), `SemistablePersistsSHcp` (persists-dvr),
`GeomConnOfRationalPoint` (fork PR #25), `TateTwistInvariants` and `AxSenTate` (fork PR #29), `GroupSchemeEquidim`
(fork PR #31), `CartierSmooth` (fork PR #34), `UniformizationLeafAll` (fork PR #35), `MilneIsogenyQuasiInverse`
(milne-compile, fork PR #23's proof), `EGAIV_8_10_5_xii` (ega-limit), `LegendreThreeSquares` (fork PR #36),
`JonesPallX2Y2Z16` (fork PR #38), `TYZThm21At31` (t21-proof), `NeronBaseChangeStrictHenselization` with `BLR_7_2_1`
(neron-sh-proof), `PoincareComplement` (poincare-proof), `WeilPairingMumford` and `PhiAmpleIsogeny` (phisurj),
`TYZTestVectorExists` (hfx-proof), `TYZProp23Printed` (hp23-proof) and `GrossConjugationCd` (gz-conj), and from new
leaves `DSThm965` and `DSThm965Weak` (ds965-weak, coeff-ext), `DSThm966` (coeff-fix), the dict-models fields
`SGA7_IX_3_3_SH` and `RaynaudSemistableSH`, `MumfordGroupLaw` and `NeronSchemeExtensionExists` (goodmodel-iso),
`NeronOggShafarevich` (dict-galois), `PicZeroAbVar` (piczero-char0), `ShimuraMainCM` (hcm-dict) and
`GrossZagierFormulaCd` (gzopt-dict); r9, `X0Transitive` (flt-cqj2; the field `igusaGL2` deleted),
`StrictHenselizationInside` (gt-unip), `ThetaWeierstrass8` (theta-wp8; `hX` dropped), and from new leaves
`SGA7_IX_3_3`, `SemistableUnipotent`, `RayClassCMAb`, `ShimuraFamilyAb`, `ShimuraGoodReductionNoGuard`,
`ElkiesX6StarPrinted`, `R16_EichlerShimuraJ1'`, `FHNonvanishing` and `TYZLemma29Mod2`, and with leaf-fold29
`BabaGranathRationalAb` (bg-explicit), `STQM` (st-qbar) and the lower half of Faltings' Lemma 5 (faltings5-lower); r8,
`RingClassLattice` (gt-ringclass), `MulEtaleAbelianScheme` (fork PR #19), `QMCentralizerCMC` (gt-qm),
`ValenceFormulaCocompactEq` (gt-valence), `IgusaPsi4`, `IgusaChi10` (gt-theta), `ShimizuCovolumeO1` (gt-gamma),
`BLR_1_2_4` (gt-blr), `EGAIV_8_10_5_openImm` (gt-ega), and from new leaves `GonzalezRotgerCountX6Ab`,
`StrictHenselizationPair` and `ElkiesEquationsX6Ab`; r7, `IgusaAlg` (igusa-alg); r6, `IgusaCMValue24` (cm24-value),
`HTDual` (c-to-printed2), `FixedTorsionRationalImperfect`, `SemistableAlmostAll`, `SemistableLocalGlobal` and
`SemistableNeronBaseChangeLocalGlobal` (reduct-glue, the last two through c-to-printed's printed fields); r5,
`DeligneSerreConseq` (modular-split); r4, `EigenformTwist`, the two EGA IV descents, `ZariskiConnectedness`,
`T11bExists`, `NeronMappingAbelianSchemeSurj` (PRs #6-#10), `JacobianExists ℚ`, `NormalModelOfFunctionFieldQ`
(cloud-w07), `QMClassNumberOne` (qm-split), `CurveBijIso` (curve-split); r3, `GammaStarGen`; r2, `SerreRigidity3`,
`T09_WeilPairing` (av-b2), and in the chain below `HeckeVertWitness`: `SmoothFibreReduced` (smooth-fibre),
`SpecialFibreMaxIdeal`, `SpecialFibreUniformizer`, `SpecialFibreDVR` (vert-witness), `ModelGenericFibre`,
`GermOfQbarValues`, `ModelIntegral`, `ModelFunctionField` (model-glue). Props that r4's own tasks introduced and
proved were never rows: height-split's glue (`AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`UniformizationDim`, `MetrizationOfUniformization`, `NeronMetrizable`, proved from T35 by height-glue), qm-split's
`GammaStarFromO1` (qm-glue), qm-glue's `CoarseFactor` (coarse-factor), mcr-glue's four glue Props (mcr-quot, from
three others). Proved before 17:35: see the 17:35 report (`git show d8c95123:docs/research/frontier.md`). Props that
r5's tasks introduced and proved were never rows: reduct-split's `TorsionFieldOfDefinition`, `DVRFiniteExtension`,
`DVRComapFinite` and `IsogenyBaseChangeDeg`; shimura-split's `PairsLift` (from T5). Props that r6's tasks introduced
and proved or reduced were never rows: shimura-glue's `MobiusCompose` (proved); reduct-glue's `UnipotentFromSH` and
`PersistsFromSH` (from the strict-henselization leaves); x6-glue's `ConicModelT` (from its charts); t5-glue's
`AbsArtinSurjectiveQNeg` and `InvertibleColon` (proved over Tau Ceti); theta-glue's `ThetaEightSquare`,
`IgusaThetaSymmetric` (from `IgusaAlg`) and `IgusaAlg 3`, `IgusaAlg 4` (proved); genus-route's `DimJ1Le5` (proved);
route A's `MumfordRigidity` (from `mumfordRigidityCore`). Props that r7's tasks introduced and proved were never rows:
t09-pic's `veryAmpleIsAmple` (formerly a leaf, EGA II 4.5.10) and its genuine definitions; igusa-alg's `IgusaAlg 3` to
`IgusaAlg 9` and its two theta-route theorems; sh-route's commutative algebra (`SHExists0`, `SHInside0`, `SHPair0`);
unipotent-b's two `K^s` versus `K̄` Props. Props that r8's tasks introduced and proved were never rows: sem-prune's
`G9GlueNoT23` and `FaltingsLemma5BCLower`; gt-shpair's commutative algebra (`IsSHSep` pins the strict henselization in
every characteristic); gt-elkies's Atkin–Lehner group, a definition, and its moduli step `orbit_iff_twist`;
gt-grcount's passage from `R5fpCount`. Props that r9's tasks introduced and proved were never rows: gz-fh's
`TwistFunctionalEquation`; gz-hl3's glue (Heegner representatives, the point on `E`, the embedding of `ℚ(√D)`, the Ch.
V corollaries) and its composite leaves `HeegnerPointRational` and `HeegnerPointRationalCd` (gz-heegner) and
`ShimuraCMParamCd` (gz-weil, from `JacobiLambdaDeriv`); theta-wp8's `ThetaWeierstrass8` and hx-used's eta route;
flt-cqj2's `ModularEquationGeneric` and `CyclicQuotientJBijOn`; elkies-coord's step from the fibres of `t` to the
`W`-orbits; r16-split's rank-two clause; sgr-split's `SmoothGeomConnIntegral` and `AbVarEndTorsionFree`; gt-rayclass's
`ClassNumberOneB`; yu-prune's `YuB6Alg`; gz-weil's `JacobiLambdaDeriv` (jacobi-lambda), with x0-32's
`EtaModelDifferential` and `ModularParamC1`; `TYZTauExists` (h29-split's alternative leaf, from the three-square
theorems) and h29-ne3's `TYZLemma29Printed`; neron-dvr's number-field Néron theorem; dcy3-used's `Y3ConnectedAb`.
Props that r10's tasks introduced and proved were never rows: sgr-direct's `NVLocalInertia` (a glue field in
leaf-fold30 and leaf-fold31) and nv-local's `TameBranchNormal`, both proved by abhyankar; theta-direct proves
theta-split's use form `ThetaRatiosAtQM`, never a row either; the dictionary tasks' bridges (dict-models' four,
dict-galois' passage from a separable to an algebraic closure through `MulEtaleAbelianScheme`, coeff-ext's
coefficient-field steps, pic-dict's and pic-fix's descent from `K̄`) are proved, never rows; so are leaf-fold33's
`NeronGoodModelIso` (goodmodel-iso), `Gamma0QExpansion` and `EtaW32Character` (gamma0-qexp, etaw32-proof), and
piczero-char0's `IdentityComponentLFT` and `PicLocFinType`, fields for one step, proved by idcomp-lft and piclft.

### 4.6 Fields of the H base introduced in r4 (8: 1 LEAF, 7 GLUE strict; 8 LEAF, 0 GLUE lenient)

Each row is a field of C4'''''''''' (its name is in the 'last task' column; leaf-fold9 to leaf-fold32 keep
leaf-fold8's fields, less those proved, pruned or replaced since) and the hypothesis of a compiled theorem in the
task's file. Its form is the kind in the integrator's `kinds.tsv`, which keeps leaf-fold8's; where this report's
reading differs the pointer says so. Theorem numbers are the reports' and UNVERIFIED unless a report read the source.
r10: fork PR #24 proves `regularSmoothPerfect` (H-118; leaf-fold31), ds965-weak replaces `dsThm965` (H-125) by
`dsThm965Weak` (leaf-fold30) and coeff-fix that by H-214 and H-215 (§4.16), coeff-fix replaces `dsThm966` (H-126) by
H-216, the dictionary pass re-rates `gagaMorphism` (H-105) and the four height fields (H-109, H-110, H-112, H-113) and
the two Hodge fields (H-122, H-123) as consequences, and the fork PRs and milne-compile prove H-98, H-99, H-100,
H-103, H-104, H-120 and H-121 (leaf-fold32); leaf-fold33: poincare-proof proves `poincareComplement` (H-72),
homfree-noemb reroutes `homFreeFiniteAlgClosed` (H-70) away, and goodmodel-iso replaces `neronSchemeExtensionExists`
(H-77) by H-220.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-102 | `AvSplit.MumfordTorsionAlgClosed` | `scratch/av-split/AvSplitAll.lean` L1411 @ main | H-25, H-38 | **LEAF**; over `k = k̄`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` | av-split; field `mumfordTorsionAlgClosed` of leaf-fold33; cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | published form: Mumford AV §6 Application 2 (iv) (the integrator's correction of av-split's §4; UNVERIFIED) |
| H-105 | `ZInQ.HomLattice.GAGAMorphism` | `scratch/av-split/AvSplitAll.lean` L1029 @ main | H-69 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); GAGA for homomorphisms of complex abelian varieties | av-split; field `gagaMorphism` of leaf-fold33; after main: sga1-fix (`gagaMorphism`); gaga-chart (`gagaMorphism`); gaga-serre (`gagaMorphism`); cloud batch 2: claimed on the issue 2026-11-15 02:14Z, in progress (claims.tsv) | consequence of one theorem: Serre, GAGA, in the form of homlattice §3.2 (av-split §1); re-rated 11-16 under the dictionary ruling (leaf-fold32): GAGA's hypothesis, a holomorphic map, is reached from the uniformization only through the holomorphic inverse function theorem, and the print for proper `X` is SGA 1 XII 4.4 (kinds.tsv) |
| H-109 | `ZInQ.HeightSplit.JavanpeykarBound` | `scratch/height-split/HeightSplit.lean` L508 @ main | H-14 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Javanpeykar's bound over the published stable height | height-split; field `javanpeykarBound` of leaf-fold33; after main: javanpeykar-fix (`javanpeykarBound`); javanpeykar-rebase (`javanpeykarBound`) | consequence of one theorem: specialization of Javanpeykar 2014 Thm 1.1.1; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): the Jacobian and Albanese model dictionary (Milne, Jacobian varieties 6.1 with base change), `dim J` the genus, and `IsBelyiFunction` to a Belyi map of `X_ℚ̄` are theorem steps (kinds.tsv) to `K` with a `K`-rational Belyi function (height-split §4; leaf-fold8 §2; height-split §7 notes that a stricter reader may call it a consequence) |
| H-110 | `ZInQ.HeightSplit.GaudronRemondThm14` | `scratch/height-split/HeightSplit.lean` L773 @ main | H-15 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Gaudron–Rémond's bound over the published stable height | height-split; field `gaudronRemondThm14` of leaf-fold33; after main: gr14-narrow (`gaudronRemondThm14`); height-fix (`gaudronRemondThm14`); semiab-descend (`gaudronRemondThm14`) | consequence of one theorem: Gaudron–Rémond 2014 Thm 1.4; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): the kernel's coordinate-form height equals the printed stable height only through the analytic uniformization, as for `bostLowerBound` (kinds.tsv) (height-split table) |
| H-112 | `ZInQ.HeightSplit.BostLowerBound` | `scratch/height-split/HeightSplit.lean` L429 @ main | H-17 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); `h_D ≥ −(g/2) log 2π` (Deligne's normalization) | height-split; field `bostLowerBound` of leaf-fold33; after main: height-fix (`bostLowerBound`); semiab-descend (`bostLowerBound`) | consequence of one theorem: Bost, Sém. Bourbaki 795; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): the kernel's coordinate-form `GroupModel.height` equals Bost's `h` only through the analytic uniformization, the torus integral and `ω = e*Ω¹` (EGA IV 17.2.5) (kinds.tsv) (display unread; height-split §2) |
| H-113 | `ZInQ.HeightSplit.PazukiCor13Upper` | `scratch/height-split/HeightSplit.lean` L717 @ main | H-18 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the upper side of Pazuki's comparison of theta and Faltings heights | height-split; field `pazukiCor13Upper` of leaf-fold33 | consequence of one theorem: Pazuki 2012 Cor. 1.3(2); re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): analytic principal polarizations of `ℂ²/Λ` are read as algebraic `(A, L)` through Appell–Humbert and Lefschetz with GAGA (kinds.tsv), read off the same display (height-split §3) |
| H-122 | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | `scratch/hodge-split/HodgeSplit.lean` L343 @ main | H-8 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); the Hodge–Tate decomposition of `ℂ_p ⊗ V_p(A)` | hodge-split; field `hodgeTateDecompAbVar` of leaf-fold33; after main: dict-galois (`hodgeTateDecompAbVar`); hodgetate-from-dr (`hodgeTateDecompAbVar`) | consequence of one theorem: Fontaine 1982; Faltings 1988; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): the coordinate form `ℂ_p(1)^g ⊕ ℂ_p^g` needs the dual abelian variety's dimension `g` (Mumford §8, §13), unless Fontaine prints the coordinate form (kinds.tsv) (hodge-split §1) |
| H-123 | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | `scratch/hodge-split/HodgeSplit.lean` L1988 @ main | H-8 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); `Hom(V_p A, ℚ_p)` is de Rham | hodge-split; field `deRhamH1AbVarT` of leaf-fold33; after main: dict-galois (`deRhamH1AbVarT`); derham-print (`deRhamH1AbVarT`) | consequence of one theorem: Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, Hom form; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): `Hom(V_p A, ℚ_p) = H¹_et(A_F̄, ℚ_p)` is Milne 1986 Thm 15.1(a), and Scholze's Cor. 1.8 also needs the rigid comparison (kinds.tsv) (hodge-split §1) |

### 4.7 Props open only in scenario F, introduced in r4 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

r4's rows here were mcr-glue's and mcr-quot's split of the glue field `quotientP1Coordinate`, hypotheses of compiled
theorems that scenario F applied on top of the H base; r10: all nine are off the route (H-89 to H-97), since
leaf-fold30 prunes the field (sgr-fold, §4.1).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.8 Fields of leaf-fold9 introduced in r5 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

r5's rows here are all gone: H-145 is restated on abelian schemes (route-a-fold), H-146 and H-147 are fields that
scenario F replaces by their strictly henselian forms (§4.1), and r9: H-148, the field `neronSchemeModelExistsDVR`
that leaf-fold9 introduced from reduct-split's `Reduction.lean`, is pruned (r6-nf with neron-dvr, leaf-fold29).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.9 Props open only in scenario F, introduced in r5 (1: 0 LEAF, 1 GLUE strict; 1 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4''''''''''. Its form is the task
report's label, or my reading where the report's own text names more than one source or gives no label; the pointer
says which. Its H-150 is a field since leaf-fold13 and moved to §4.12. r9: H-154 is off the route (§4.1).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-157 | `ModularSplit.R17.CarayolRealization` | `scratch/modular-split/R17.lean` L127 @ main | H-21 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform has conductor exponent `v_p(N)` at every `p ≠ ℓ`; the transport to every attached `ρ` is proved | modular-split; after main: r17-bypass (`r17`); r17-print (`r17`) | consequence of one theorem: Carayol 1986 Thm (A) at his realization (audit), with Casselman's `a(π_p) = v_p(N)` and Ribet's irreducibility (modular-split §2: still a consequence) |

### 4.10 Fields of leaf-fold10 and leaf-fold11 introduced in r6 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

r6's rows here were fields that leaf-fold10 or leaf-fold11 introduced, each the hypothesis of a compiled theorem in
its file (`TailZ16`, `TailZ17`: route-a-fold; `TailZ19`: c-to-printed's printed leaves), and all are gone: r8:
`gonzalezRotgerCountX6Ab` is replaced (gt-grcount), `blr_1_2_4` and `egaIV_8_10_5_openImm` are proved and
`raynaudKernelBound` is pruned; r9: `mumfordRigidityCore` (H-170) becomes `mumfordGroupLaw`, `sga7_IX_3_3` (H-175) is
proved from its strictly henselian form (§4.15), faltings5-lower proves `faltingsLemma5Printed` (H-172; leaf-fold29),
and scenario F replaced the consumer of `deligneComponentsY3PrintedAb` (H-169; dcy3-used), which dcy3-fold prunes
(leaf-fold30); r10: gt-sga3 narrows `sga3_VIB_3_10` (H-174), the last, to its neighbourhood form (leaf-fold32), which
sga3-nbhd removes from the chain (leaf-fold33). leaf-fold10's other new fields are not rows: `neronLocalizesDVR` is
proved since leaf-fold11, and leaf-fold14 replaces the DVR fields.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.11 Props open only in scenario F, introduced in r6 (1: 0 LEAF, 1 GLUE strict; 1 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''''' (§4.1). Its form is the
task report's label, or my reading where the report gives none or names more than one source (the pointer says
"reading"). r8: H-182 is a field since leaf-fold14 (§4.14), and H-185 and H-187 are replaced; r9: H-188 is proved
(gt-unip, leaf-fold20); r10: H-190 is off the route, since leaf-fold32 removes `thetaRatiosAlgebraic` (theta-fold2,
§4.1). r6's branch heads are merged (w66), so the rows point at main; r6's rows for x6-glue's leaves are replaced by
fields (§4.12).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-181 | `CToPrinted2.KatoRealizationCohSS` | `scratch/c-to-printed2/CToPrinted2.lean` L618 @ main | H-158 (from H-127) | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); some semisimple `ρ` attached to the newform, with Kato's Hodge–Tate weights; with `TateTwistInvariants` and `AxSenTate`, theorems since leaf-fold32 (fork PR #29), it gives `eigenformHTNew`, and is equivalent to it over the bundle | c-to-printed2; after main: ht-exists (`eigenformHTNew`) | consequence of one theorem: Kato, Astérisque 295 (2004) §8.3 and §§9.2-9.4 at his `V_{F_λ}(f)`, quantified existentially (c-to-printed2 §2.1; locators read by locators.md row R13): the report's label, a consequence |

### 4.12 Fields of leaf-fold13 introduced in r7 (1: 0 LEAF, 1 GLUE strict; 0 LEAF, 1 GLUE lenient)

Each row is a field of C4'''''''''' that leaf-fold13 introduced (x6-fold), and the hypothesis of a compiled theorem in
`TailZ20`-`TailZ22`: x6-glue's leaves restated on abelian schemes (r6's rows H-142, H-177, H-178, H-179); H-150 kept
its row from r5 (until r6 open only in scenario F). Forms: kinds.tsv's. r8: H-195 is replaced by gt-elkies's leaf; r9:
H-196 is proved from H-209 (gt-rayclass, §4.15), and bg-explicit proves `babaGranathRationalAb` (H-193; leaf-fold29);
r10: pi0-fold prunes `geomConnOfAlgClosure` (H-150) and `deligneComponentsX6PrintedAb` (H-192; leaf-fold31).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-194 | `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` | `ZInQKernel/OneProof/H/TailZ22.lean` L69 @ main | H-142 | GLUE (composite); some coarse witness, on abelian schemes, has the residue fields of CM points (`R5ptProps`) | x6-fold; field `gonzalezRotgerX6Ab` of leaf-fold33; after main: gr-dict (`gonzalezRotgerX6Ab`); grx6ab-print (`gonzalezRotgerX6Ab`) | composite: González–Rotger 2006 Thm 5.12 (qm-glue §4.2; UNVERIFIED); x6-fold restates it on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem; `gonzalezRotgerX6_iff_ab` with the field `mumfordRigidityCore`, H-170; the chain now converts by `gonzalezRotgerX6_iff_ab_gl`, with rigid-prune's `QMFamilyGroupLaw`, proved from `mumfordGroupLaw`, since leaf-fold33 in its DVR form `MumfordGroupLawDVR`, from the field H-220 by goodmodel-iso's copy reroute); re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): it asserts the witness `R1fpPropsAb` with `X6Props`, which no print states (kinds.tsv) |

### 4.13 Props open only in scenario F, introduced in r7 (0: 0 LEAF, 0 GLUE strict; 0 LEAF, 0 GLUE lenient)

Each row is a hypothesis of a compiled theorem that scenario F applies on top of C4'''''''''' (§4.1). r7's rows here
were unipotent-b's printed SGA 7 IX 3.5 and its glue; r9: both are off the route (H-197, H-198), since leaf-fold20
proves `semistableUnipotent` from gt-unip's leaf. r8: t09-pic's four leaves are fields since leaf-fold14 (§4.14).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|

### 4.14 Fields of leaf-fold14 to leaf-fold19 introduced in r8 (2: 1 LEAF, 1 GLUE strict; 2 LEAF, 0 GLUE lenient)

Each row is a field of C4'''''''''' that leaf-fold14 to leaf-fold19 introduced, and the hypothesis of a compiled
theorem in its file: leaf-fold14's fold 1, reduct-b's Route B-cp (H-182, H-203; the third, `strictHenselizationPair`,
is replaced by gt-shpair's H-205 in leaf-fold18), and fold 2, t09-pic's four leaves (H-199 to H-202); gt-grcount's
H-204 (leaf-fold17). Forms: kinds.tsv's. r9: H-206 is replaced by elkies-coord's H-213 (§4.15). r10: persists-dvr
proves `semistablePersistsSHcp` (H-203; leaf-fold30), and the Pic dictionary ruling re-rates t09-pic's `picZeroAbVar`
(H-200), `phiAmpleIsogeny` and `weilPairingMumford` (H-202) as consequences (leaf-fold31); leaf-fold32 replaces
`phiAmpleIsogeny` (H-201) by two printed Mumford leaves (pic-fix), `raynaudSemistableSH` (H-182) and
`neronBaseChangeStrictHenselization` (H-205) by their printed forms (dict-models), and the dictionary pass re-rates
H-204 a consequence; leaf-fold33 proves `phiAmpleIsogeny` and `weilPairingMumford` (phisurj) and
`neronBaseChangeStrictHenselization` (neron-sh-proof), and replaces `picZeroAbVar` by Kleiman's Theorem 9.5.4, H-221
(piczero-char0, idcomp-lft, piclft; §4.16).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-199 | `T09Pic.PicRepresentableAbVar` | `ZInQKernel/OneProof/H/TailZ24.lean` L289 @ main | H-53 | **LEAF**; the relative Picard fppf sheaf of an abelian variety is representable | t09-pic; field `picRepresentableAbVar` of leaf-fold33 (since leaf-fold14) | published form: Murre (1964), Oort (1962); FGA Exp. 232 Thm 3.1; Kleiman, The Picard scheme, Thm 9.4.8 with Thm 9.2.5 (t09-pic §3; UNVERIFIED) |
| H-204 | `GRCountX6.GonzalezRotgerProp56X6` | `ZInQKernel/Contrib/OneProof/GRCountX6.lean` L72 @ main | H-168 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); González–Rotger's count on every witness of the moduli description of `X₀(6,1)`, with no existence claim: the CM points by an order `R` that occurs as some `End_𝒪(A)` number `2^{inertCount6 k}·#Pic(R)`; with the field `gonzalezRotgerX6Ab` it gives `gonzalezRotgerCountX6Ab` | gt-grcount; field `gonzalezRotgerProp56X6` of leaf-fold33 (since leaf-fold17); after main: gr56-prove (`gonzalezRotgerProp56X6`); gr-dict (`gonzalezRotgerProp56X6`); eichler-bound (`gonzalezRotgerProp56X6`) | consequence of one theorem: González–Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): González–Rotger's `CM(R)` (optimal embeddings modulo `𝒪¹`) is read as polarization-free `ℚ̄` pairs with `End = R` only through Shimura 1967 and the descent of CM pairs (kinds.tsv), p. 943 (read by the locator audit), at `(D, N) = (6, 1)` (gt-grcount; statement review 11-14, two lenses: faithful); kinds.tsv flags that `D(R)`, the product of the `p ∣ D` with `(R/p) = −1`, is to be confirmed against the paper |

### 4.15 Fields of leaf-fold20 to leaf-fold26 introduced in r9 (4: 0 LEAF, 4 GLUE strict; 1 LEAF, 3 GLUE lenient)

Each row is a field of C4'''''''''' that leaf-fold20 to leaf-fold26 introduced, and the hypothesis of a compiled
theorem in its contribution file: gt-sga7's H-207 and gt-unip's H-208 (leaf-fold20); gt-rayclass's H-209 and
sgr-split's H-210 (leaf-fold22); gt-rigidity's H-211 (leaf-fold23); r16-split's H-212 (leaf-fold25); elkies-coord's
H-213 (leaf-fold26). Forms: kinds.tsv's. leaf-fold27 to leaf-fold29 introduce no field; leaf-fold29's six new
hypotheses of the top are TYZ rows (T-18 to T-23, §3.2). r10: sgr-fold prunes `shimuraIntegralModelRep` (H-210;
leaf-fold30); leaf-fold32 replaces `sga7_IX_3_3_SH` (H-207) and `mumfordGroupLaw` (H-211) by their printed forms
(dict-models, §4.16), leaf-fold33 replaces the latter by H-220 (goodmodel-iso), the dictionary pass re-rates H-213 a
consequence, and kinds.tsv's columns count H-208 GLUE, pending a reading, so it is recorded as a composite.

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-208 | `UnipotentForward.SGA7_IX_3_5_ForwardGeom` | `ZInQKernel/Contrib/OneProof/UnipotentForward.lean` L420 @ main | the field `semistableUnipotent` (r8: H-197, H-198 in scenario F) | GLUE (composite); SGA 7 IX 3.5, forward direction at `σ = τ`, over a strictly henselian DVR with `Ω = K^s` and `ℓ` invertible: if `A` has semistable reduction (read on the geometric special fibre), every `σ` in inertia satisfies `(σ − 1)² = 0` on `T_ℓ(A)`; gt-unip proves the field `semistableUnipotent` from it, with `StrictHenselizationInside` proved from a Néron leaf of the chain | gt-unip; field `sga7_IX_3_5_ForwardGeom` of leaf-fold33 (since leaf-fold20); after main: sga7-cp (`sga7_IX_3_5_ForwardGeom`) | composite: SGA 7 I Exp. IX Prop. 3.5, forward direction at `σ = τ` (gt-unip; number UNVERIFIED); kinds.tsv: if Prop. 3.5 reads semistability on the `k(s)` fibre, a consequence through `SemiAbelianDescendsSepClosed`, and if its display lacks the echelon clause the square-zero bound comes from IX 2.4; statement review 11-15 (two lenses, AI, no print): yes, a consequence under the alternative readings; kinds.tsv (leaf-fold32): published kind, GLUE in its strict and strictest columns (pending reading: two recorded readings make it a consequence), so a composite by the integrator's convention |
| H-209 | `RayClassCFT.ShimuraMainThmIDeligneY3AbU` | `ZInQKernel/Contrib/OneProof/RayClassShimura.lean` L1152 @ main | H-196 and the field `shimuraFamilyAb` (r8: H-154 in scenario F) | GLUE (composite); Shimura's Main Theorem I in Deligne's adelic form on the fine witness `Y₃`, on abelian schemes, with the moduli clause at every `u ∈ 𝒪̂^×` (`ModuliAtUnits`): the QM pair at `[τ, g]` and reciprocity at CM points; gt-rayclass proves `rayClassCMAb` (without rigidity) and `shimuraFamilyAb` from it, with `ClassNumberOneB` proved | gt-rayclass; field `shimuraMainThmIDeligneY3AbU` of leaf-fold33 (since leaf-fold22); after main: composite-out (`shimuraMainThmIDeligneY3AbU`); shimura-split2 (`shimuraMainThmIDeligneY3AbU`); holfam (`shimuraMainThmIDeligneY3AbU`); pel-hodge (`shimuraMainThmIDeligneY3AbU`); y3abu-print (`shimuraMainThmIDeligneY3AbU`); y3abu-strict (`shimuraMainThmIDeligneY3AbU`) | composite: Shimura, Ann. of Math. 85 (1967) Main Theorem I; Deligne, Sém. Bourbaki 389 (1971) §§4.9-4.21 and §5 (the PEL model is Cor. 5.7 / Ex. 5.8); Milne, Introduction to Shimura varieties §§12-14 (gt-rayclass; locators UNVERIFIED); the docstring's label: a consequence (the moduli clause only for `g ∈ 𝒪̂^×`); kinds.tsv: a composite, pending review |
| H-212 | `R16Split.R16CoreY` | `ZInQKernel/Contrib/OneProof/R16Split.lean` L534 @ main | H-13 | GLUE (composite); R16 without its rank-two clause (Eichler–Shimura on `J₁(N)`, existential form): for a newform `f`, an abelian variety `A/ℚ`, a surjection `J₁(N) → A` and `θ : K_f → End⁰(A)` with `dim A = [K_f:ℚ]`, Frobenius at `p ∤ Nℓ` acting on each `ι`-component of `V_ℓ(A)` with trace `ι(a_p(f))` and determinant `ι(χ(p))p`; r16-split proves `r16` from it (the rank-two clause from `dim A = [K_f:ℚ]` and Mumford §19 Thm 4) | r16-split; field `r16CoreY` of leaf-fold33 (since leaf-fold25); after main: r16-used (`r16CoreY`); isj1-dict (`r16CoreY`); x1-igusa (`r16CoreY`); weber-field (`r16CoreY`); aftate-or (`r16CoreY`); aftate-fix2 (`r16CoreY`) | composite: Shimura 1973 Thm 1, unconditional clauses; Shimura 1971 Thm 3.52 and Thm 7.11 (from the congruence relation, Thm 7.9); Diamond–Shurman Thm 9.5.4 (r16-split; locators UNVERIFIED); a composite, like `r16` |
| H-213 | `HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField` | `ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean` L814 @ main | H-206 | GLUE in the strict count (consequence of one theorem; LEAF in the lenient count); Elkies' coordinate in function-field form on one witness of the moduli clause: `ℚ(X₆)^W = ℚ(t)` (under the integrality that the charts give), the CM values `t = 0, 1, ∞` at discriminants −24, −4, −3, and the two charts of `X₆` over the `t`-line; elkies-coord proves `elkiesX6StarPrinted` (the fibres of `t` are the `W`-orbits) from it | elkies-coord; field `elkiesX6StarFunctionField` of leaf-fold33 (since leaf-fold26); after main: elkies-print (`elkiesX6StarFunctionField`) | consequence of one theorem: Elkies, ANTS-III (1998) §3; re-rated 11-16 under the dictionary ruling (dictionary pass, rater and skeptic, leaf-fold32): it carries the same `R1` moduli witness that is rated a composite elsewhere (kinds.tsv): `X*(6) = X₆/W` with coordinate `t` (elkies-coord; section, display and the `0/∞` orientation UNVERIFIED); the printed coordinate statement in function-field form, never stronger (the docstring); kinds.tsv: published, pending review |

### 4.16 Fields of leaf-fold32 and leaf-fold33 introduced in r10 (8: 6 LEAF, 2 GLUE strict; 6 LEAF, 2 GLUE lenient)

Each row is a field of C4'''''''''' that leaf-fold32 or leaf-fold33 introduced, and the hypothesis of a compiled
theorem in its contribution file: coeff-fix's H-214, H-215 and H-216, dict-models' H-217 and H-218 and dict-galois'
H-219 (leaf-fold32), goodmodel-iso's H-220 and piczero-char0's H-221 (leaf-fold33). Forms: kinds.tsv's;
`sga7_IX_3_3_SHpre` is a published kind that its columns count GLUE, pending a reading, so it is recorded as a
composite. Fields that came and went within r10 are not rows: ds965-weak's `dsThm965Weak` and sgr-fold's glue field
`nvLocalInertia` (leaf-fold30 to leaf-fold32), and leaf-fold32's `sga3_VIB_3_10_Nbhd` (gt-sga3), `mumfordGroupLawConn`
and `blr_7_2_1` (dict-models) and `mumfordKLFiniteSectionAC` and `mumfordPhiSurjectiveAC` (pic-fix), with
piczero-char0's `identityComponentLFT` and `picLocFinType`, which leaf-fold33 proves, replaces or reroutes away
(§4.1); leaf-fold31 introduces no field. The top's new hypotheses are GZ rows (Z-8, Z-9, §2.2) and a TYZ row (T-24,
§3.2).

| # | Lean name | def file @ commit | replaces | class; content | last task | form (strict LEAF = published form) |
|---|---|---|---|---|---|---|
| H-214 | `DSCoeffExt.DSThm965Printed` | `ZInQKernel/Contrib/OneProof/DSCoeffExt.lean` L434 @ main | H-125 | **LEAF**; Diamond–Shurman's Theorem 9.6.5 as printed, over `K_{f,λ}`: for a normalized eigenform `f ∈ S_k(N, χ)` (DS Def. 5.8.1, `k ≥ 2`) with number field `K_f` and `λ` over `ℓ`, a continuous `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified outside `ℓN`, with `ρ_{f,λ}(Frob_𝔭)` having characteristic polynomial (or satisfying) `x² − a_p x + χ(p)p^{k−1}`; with `eigenformCoeffFieldFinite` coeff-ext proves the earlier restatement `dsThm965Weak` (`DSCoeffExt.dsThm965Weak_of_printed`), from which ds965-weak proves the old field | coeff-fix; field `dsThm965Printed` of leaf-fold33 (since leaf-fold32) | published form: Diamond–Shurman Thm 9.6.5 over `K_{f,λ}` as printed (Deligne 1971; Shimura 1971 Thm 7.14 for `k = 2`), either wording by or-introduction (coeff-ext, coeff-fix; number UNVERIFIED); kinds.tsv: unread, a new printed leaf |
| H-215 | `DSCoeffExt.EigenformCoeffFieldFinite` | `ZInQKernel/Contrib/OneProof/DSCoeffExt.lean` L460 @ main | H-125 | GLUE (composite); for a normalized eigenform `f ∈ S_k(N, χ)` (DS Def. 5.8.1), `k ≥ 2`, the field `K_f = ℚ(a_n(f) : n)` is finite over `ℚ`, the presupposition of Diamond–Shurman 9.6.5 | coeff-fix; field `eigenformCoeffFieldFinite` of leaf-fold33 (since leaf-fold32); after main: coeff-field (`eigenformCoeffFieldFinite`); coeff-rational (`eigenformCoeffFieldFinite`) | composite: Diamond–Shurman Thm 6.5.1 (`k = 2`) and Shimura 1971 Thm 3.52 with the Hecke stability of the rational structure (§3.5) for every `k` (coeff-fix; numbers UNVERIFIED); kinds.tsv: composite, pending reading |
| H-216 | `DSThm966EV.DSThm966Printed` | `ZInQKernel/Contrib/OneProof/DSThm966EV.lean` L48 @ main | H-126 | **LEAF**; Deligne–Serre's Theorem 4.1 as printed: a nonzero weight-1 cusp form of type `(1, ε)`, `ε(−1) = −1`, that is a `T_p`-eigenvector for `p ∤ N` with eigenvalues `a_p` has a continuous `ρ : G_ℚ → GL₂(ℂ)` unramified outside `N` with `tr ρ(Frob_p) = a_p` and `det ρ(Frob_p) = ε(p)`; coeff-fix proves the old field `dsThm966` from it (`DSThm966EV.dsThm966_of_printed`) | coeff-fix; field `dsThm966Printed` of leaf-fold33 (since leaf-fold32) | published form: Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1 with (4.1.1), p. 514 (coeff-fix; AI-read only: W24, cloud checks) |
| H-217 | `DictModels.RaynaudOr.RaynaudSemistableSHOr` | `ZInQKernel/Contrib/OneProof/RaynaudSemistableOr.lean` L295 @ main | H-182 | **LEAF**; Raynaud's criterion over a strictly henselian DVR with the conclusion weakened to the disjunction of the two readings of "semistable reduction" (over `k(s)` for every Néron model, or on the geometric special fibre); dict-models proves the old field `raynaudSemistableSH` from it and `geomConnOfRationalPoint` (`DictModels.RaynaudOr.raynaudSemistableSH_of_or`) | dict-models; field `raynaudSemistableSHOr` of leaf-fold33 (since leaf-fold32) | published form: SGA 7 I Exp. IX Prop. 4.7 over a strictly henselian DVR, either reading by or-introduction (dict-models; number UNVERIFIED); kinds.tsv: the print may assume an algebraically closed residue field or require `m > 3` |
| H-218 | `DictModels.SGA7Pre.SGA7_IX_3_3_SHpre` | `ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean` L43 @ main | H-207 | GLUE (composite); SGA 7 IX 3.3, second assertion, over strictly henselian traits with the print's open `N⁰ ×_S S'` (the preimage of `N⁰` under `N ×_O O' → N`) in place of the identity component of `N ×_O O'`; dict-models proves the old field `sga7_IX_3_3_SH` from it and `sga3_VIB_3_10_Nbhd` (`DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre`) | dict-models; field `sga7_IX_3_3_SHpre` of leaf-fold33 (since leaf-fold32); after main: sga33-shpre (`sga7_IX_3_3_SHpre`) | composite: SGA 7 I Exp. IX Prop. 3.3, second assertion, over strictly henselian traits (dict-models; number UNVERIFIED); kinds.tsv: published kind, GLUE in its strict and strictest columns (pending reading: the print may assume an algebraically closed residue field), so a composite by the integrator's convention |
| H-219 | `NOSSepDict.NeronOggShafarevichSep` | `ZInQKernel/Contrib/OneProof/NeronOggShafarevichSep.lean` L36 @ main | H-5 | **LEAF**; the criterion of Néron–Ogg–Shafarevich over a separable closure: as the old field `r7a` with `AlgebraicClosure K` replaced by any `Ks` with `IsSepClosure K Ks`; dict-galois proves the old field from it (`NOSSepDict.neronOggShafarevich_of_sep`, through `MulEtaleAbelianScheme`) | dict-galois; field `neronOggShafarevichSep` of leaf-fold33 (since leaf-fold32); after main: nos-proof (`neronOggShafarevichSep`) | published form: Serre–Tate, Ann. of Math. 88 (1968), §1 Thm 1, over a separable closure as printed (dict-galois; numbering UNVERIFIED); kinds.tsv: unread, a new printed leaf |
| H-220 | `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` | `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean` L56 @ main | H-77 | **LEAF**; BLR's existence theorem for Néron models over a Dedekind base: for a Dedekind domain `D` with fraction field `L` and an abelian variety `A` over `L`, a smooth, separated, quasi-compact `Spec D`-scheme `N` with `N_L ≅ A` to which every morphism from the generic fibre of a smooth `Spec D`-scheme extends (no group structure asked for); the old field `neronSchemeExtensionExists` is its case `D = 𝓞_L` (`neronSchemeExtensionExists_of_dedekind`), and goodmodel-iso proves GIT Thm 6.14 over a DVR from it (`GoodModelIso.mumfordGroupLawDVR_of_dedekind`), so it also replaces dict-models' restatement of `mumfordGroupLaw` | goodmodel-iso; field `neronSchemeExtensionDedekind` of leaf-fold33 | published form: Bosch–Lütkebohmert–Raynaud, Néron models (1990), §1.4 Thm 3 with §1.2 Def. 1, existence half, affine Dedekind base (group-law-dvr, goodmodel-iso; numbers UNVERIFIED) |
| H-221 | `PicFix.KleimanPicZeroProper` | `ZInQKernel/Contrib/OneProof/PicZeroAbVar.lean` L25 @ main | H-200 | **LEAF**; Kleiman's Theorem 9.5.4: for `X` proper and geometrically normal over a field `K`, the identity component `Pic⁰_{X/K}` is proper, for every scheme representing the fppf Picard sheaf and every open whose underlying set is the identity component; with two other printed leaves, which idcomp-lft and piclft prove outright, piczero-char0 proves the characteristic-0 form of the old field `picZeroAbVar` (`PicZeroChar0.picZeroAbVar0_of_leaves`), the only form the chain reads | piczero-char0; field `kleimanPicZeroProper` of leaf-fold33 | published form: Kleiman, The Picard scheme (FGA Explained, Ch. 9), Thm 9.5.4 (piczero-char0; numbering UNVERIFIED); kinds.tsv: unread, a new printed leaf |

### 4.17 Bundle fields never projected, and the prune (not on the list)

r10: sgr-fold (`docs/research/sgr-fold.md`) prunes `shimuraIntegralModelRep` (H-210) and the glue field
`quotientP1Coordinate` once sgr-direct proves their one consumer; its scan finds 0 unused of the 55 fields left.
dcy3-fold prunes `deligneComponentsY3PrintedAb`, whose one use, `Y3Connected`, two fields give. pi0-fold
(`docs/research/pi0-fold.md`) prunes `geomConnOfAlgClosure` (H-150) and `deligneComponentsX6PrintedAb` (H-192), which
fed only `R1pi0Props`, read by no live constant; its scan finds 0 unused of 46. theta-fold2
(`docs/research/theta-fold2.md`) removes `thetaRatiosAlgebraic` once theta-direct's proof of its use form is threaded
to the one reader; its scan finds 0 unused of 44. leaf-fold33's removals are proofs and copy reroutes, each followed
by a closure check of the removed Props (`docs/research/leaf-fold33.md`). `chain.py`'s `UNUSED` is empty.

Until r9:
r9: yu-prune (`docs/research/yu-prune.md`) removes `yuThm11` (H-128) from every bundle generation: its consumers take
`YuB6Alg`, proved from three textbook fields; its scan finds 0 unused of 57 fields after the prune. flt-cqj2's fold
deletes `igusaGL2` (H-117) from generations 7 to 11, since its one consumer takes the proved `X0Transitive`. r6-nf
(`docs/research/r6-nf.md`, with neron-dvr) removes `neronSchemeModelExistsDVR` (H-148; BLR 1.4/3 over every DVR): of
its three uses, `r8` was only copied between bundles and is pruned from every generation, and `r6` and SS1/SS3 are
applied only at number fields, where neron-dvr's theorem gives them from the textbook field N1
(`neronSchemeExtensionExists`, H-77); its scan finds 0 unused fields among the rest. `chain.py`'s `UNUSED` is empty.

Until r8:
r8: sem-prune (`docs/research/sem-prune.md`) removes the two fields that gap-triage found used only syntactically,
`bdRInvariants` (H-124) and `raynaudKernelBound` (H-173), from every bundle generation, after re-proving their
consumers without them (`G0Galois.G9GlueNoT23`; `HeightSplit.FaltingsLemma5BCLower` from the field
`faltingsLemma5Printed`). Its PruneScan finds no unused field before and after, and `chain.py`'s `UNUSED` is empty.

Until r7:
r7: none. x6-fold's scan (`scratch/x6-fold/PruneScan.lean`, genus-fold's scan) finds no unused field at w66, and
`chain.py`'s `UNUSED` is empty. gap-triage finds two fields used only syntactically, which a scan of projections
cannot see: `bdRInvariants` (passed on by `g8_g11`, `g8_g12`, whose only proofs ignore it) and `raynaudKernelBound`
(`faltingsLemma5_of_printed` needs only the half that `faltingsLemma5Printed` gives); its attack list ranks removing
both first (gap-triage §1, A1).

Until r6:
r6: none. The integrator's prune (0218a662, merged in w62) removed `r3 : ZInQ.LeafPush2.R03_LinYang`, `serreTateThm2`
and `t10 : T10Etale.T10_TateDuality` from every bundle generation: the three fields that its fixed Lean scan
(wip/prune-scan e3045e7d) found unused at w61 (the prune's diff only removes lines: 63, with one structure-literal
line rewrapped). genus-fold (w63) removed `genusX1Field` and `t34` the same way, with their dead readers, after
genus-route made them unnecessary (H-79). The other three of r5's never-projected fields (`semistableReductionDVR`,
`semistableUnipotent`, `neronSchemeModelExistsDVR`) are used since leaf-fold10, whose proofs of `r6`,
`semistableReductionThm` and `semistablePersists` take them. leaf-fold11's scan finds no unused field at w63, and
`chain.py`'s `UNUSED` is empty.

Until r5:
r5: `r3 : ZInQ.LeafPush2.R03_LinYang`, `t10 : T10Etale.T10_TateDuality` and reduct-split's four leaves
`serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `neronSchemeModelExistsDVR`. In OneProof/H the four
are used only in `TailZ9`'s `researchLeaves8_of_open9`, as arguments of `serreTatePotentialGood_final` and
`grothendieckMonodromy_final'`, which fill leaf-fold8's never-projected `r7b` and `r8`; in `TailZ5`-`TailZ9`, `r3` and
`t10` occur only as `r3 := r.r3` and `t10 := t.t10` (VERIFIED, grep at main), and below `TailZ5` as in r4. Scenario F
uses three of the four (§4.8; `chain.py F` recomputes the set). The integrator has approved removing all six after
leaf-fold10. `r1rec` and `r5` left the list of unused fields: leaf-fold9 proves them from `r1r2`.

Until r4 the six were `r1rec`, `r3`, `r5`, `r7b`, `r8` and `t10`:
`r1rec : LeafQM.AV.R1rec`, `r3 : ZInQ.LeafPush2.R03_LinYang`, `r5 : LeafQM.AV.R5fp`, `r7b : PkgI2.SerreTatePotentialGood`,
`r8 : PkgI2.GrothendieckMonodromy`, `t10 : T10Etale.T10_TateDuality`. VERIFIED (agent-h-leaves and my grep) for
g0-assemble3's flat file: they occur only in the structure literals that convert the bundles (and `t10` only in the
unused `HSyn.TextbookLeaves.t10_groupIso`); C4 converts its bundles to g0-assemble3's and uses the same consumers
(REPORTED by assemble-port's report; not re-grepped, its flat file has more conversions). assemble-port already deleted
the unused textbook fields T1, T3, T4 (as textbook fields), T16(b), T20, T21, T28, T29.
r2-r4: in leaf-fold4's and leaf-fold5's flat files `r1rec`, `r7b`, `r8` occur only as `f := r.f` in three structure literals, and `t10` only
there and in `T10_groupIso_of_tateDuality` (VERIFIED, grep of `Leaves4.lean` @ 9dcf1ca8 and `Leaves5.lean` @ 5a7e03d1); `r3` and `r5` were not
re-grepped (their names collide with local variables).
r4: leaf-fold8 keeps the six (`r1rec`, `r3`, `r5`, `r7b`, `r8` in `OpenResearchLeaves8`, `t10` in `OpenTextbookLeaves8`). In
OneProof/H they occur only as `f := r.f` or `f := t.f`, or a transport `_ofK5` of it, in the bundle conversions of
`TailD`, `TailE`, `TailI`, `TailK`, `TailN`, `TailO` and `TailX`, and `t10` in LPrefix's `T10_groupIso_of_tateDuality`
(VERIFIED, grep at main); leaf-fold7 and leaf-fold8 left the chain from LPrefix to TailO unchanged.

### 4.18 Statement reviews of the leaves (leaf-review-a, leaf-review-b, leafq-check, the r4 to r10 tasks)

leaf-review-a (groups A, A′, F: 21 fields) and leaf-review-b (groups B, C, D, E, G: 41 fields) read every leaf-fold3
field with the definitions it uses: 8 PUBLISHED-FORM (`t11b`, `serreRigidity3`, `r7a`, `t41`, `r9a`, `r9b`, `r19`, `t33`),
54 CONSEQUENCE, none STRONGER-THAN-SOURCE or NOT-A-PUBLISHED-STATEMENT; no statement repair proposed. Since r3 the
form column carries their verdicts: a CONSEQUENCE is a consequence of one theorem or a composite, with the review's
derivation named, and is GLUE in the strict count until that derivation is compiled. leafq-check (r3) checked
leaf-fold4's seven LEAF? fields: `GammaStarGen` proved, three replaced by smaller statements (H-86..H-88), and
`ThetaRatiosAlgebraic`, `X6ConicModel`, `Y3Connected` unchanged (true, each a consequence of published results, not
splittable in Lean today). Premises the reviews flag across rows: Lemma QP (its existence half may be glue), the
specialization of Deligne's PEL model to `R1fpProps` (an open human check, inherited by `r1r2`, `r1b`, `y3Connected`,
`x6ConicModel`), and the definition of `stableFaltingsHeight` (group D).

The r4 split tasks each checked their rows against the sources they could read, and none found a row false, vacuous
or stronger than its sources. height-split, mcr-glue and height-glue add an independent model review of their new
statements (no defect; height-glue's RISKs: `QMUniformizationC` bundles the algebraicity of QM tori, GAGA and the
unpolarized form with the published moduli statements, and `CMDescent` bundles the classification of endomorphism
algebras). tyz-split read TYZ's source and settled tyz-35's three HUMAN CHECK items; the `[i]` sign of the base point,
the one input it left unprinted, was found printed later (`α = −i` in the proof of the Hecke action, about
Period7.tex L1564-1566). Flags kept in the form column: `PazukiCor13Upper` is half of Pazuki's corollary, and the
comparison of normalizations is in height-split §3; `EichlerOptimalEmbeddingCount` may be printed modulo `𝒪¹`; Igusa
prints `ψ₄`, `χ₁₀` as identities of Eisenstein series; `CanonicalModelY3`, `ShimuraFamily` and `CanonicalCoarseX6`
keep the Lemma QP caveat.

The r5 split tasks checked their rows against the sources they could read (reduct-split could read none of its
sources, so its locators are UNVERIFIED); none reports a row false or vacuous. shimura-split's independent review
found `GonzalezRotgerCountX6` OK, and Eichler's count gives 2, 2, 2 points at discriminants −4, −3, −24, matching the
conic model's fibres (REPORTED, leaf-fold9 §1.1); the open check is that the kernel's `inertCount6 k` (`p·𝒪_k` prime
for `p = 2, 3`) is González–Rotger's `b(k)`. reduct-split's reading risks: SGA 7 IX 4.7 may be printed over a strictly
henselian base (`RaynaudSemistable`), and Serre–Tate Thm 2 for a complete `K` (`SerreTateThm2`, never projected); its
leaves count as published forms pending the integrator's review of the printed base ring. modular-split's two
realization leaves are consequences: Carayol's and Kato's objects cannot be defined in Mathlib. tyz-split's T-12
passed a clause-by-clause statement review: TYZ Theorem 3.3 or weaker, carried along the kernel's eta model (§3.2).
Every leaf stated on a witness of the moduli clause lists carries `R1fpProps`, whose clause `R1univProps` classifies
families without a group law, while the published moduli theorem classifies abelian schemes; r5 put the open check on
the step between them (rigidity, extension of the polarization) in those rows. Since r6 it rests on one field,
`mumfordRigidityCore` (H-170): with it r1univ-rigid compiles, for 18 leaves, that the leaf on `R1fpProps` is
equivalent to the same leaf on abelian schemes, and route-a-fold restates four fields that way. The row that still
carries `R1fpProps` says so (H-154); since r7, x6-fold states x6-glue's leaves on abelian schemes (§4.12),
`RayClassCMAb` included.

The r6 tasks checked their rows against the sources they could read; none reports a row false or vacuous.
reduct-glue's base review, first version, with the integrator's rulings (11-14): `NeronSchemeModelExistsDVR` (H-148)
and `MumfordTorsionAlgClosed` (H-102) stay published forms, the latter with Mumford's locator corrected to §6
Application 2 (iv); the four SGA 7 IX DVR fields count as consequences (a plausible weaker reading: a strictly
henselian base) until a human reads SGA 7 IX (its head, the openings of §2-§4, the displays of 4.7 and 3.5) and
Serre–Tate §1-§2; of their strictly henselian forms, `RaynaudSemistableSH` and `SemistableReductionSH` are published
forms and the other two consequences, tagged "review v1, v2 pending"; the three strict-henselization leaves are
consequences. c-to-printed's reading risks: BLR 1.2 Prop. 4 may be printed with strict henselizations (so `blr_1_2_4`
counts as a consequence, as does `sga7_IX_3_3`), the numbers of SGA 3 VI_B 3.10 and of Raynaud's bound are
unconfirmed, and Faltings' Lemma 5 was not read (those stay LEAF, flagged). reduct-glue's "no project glue is left"
for reduct-split's seven rows holds for `r7b` and `r8` only over perfect fields (`K^s → K̄` needs
`MulEtaleAbelianScheme`); neither is a hypothesis of the library theorem. x6-glue's independent review found no false,
vacuous or too-strong statement; the fibre clause of `ElkiesEquationsX6` is a composite of Elkies' statement and the
moduli meaning of `W`, and the CM assignment in `BabaGranathRational` is an UNVERIFIED reading of Baba–Granath's
table. c-to-printed2's review found no mathematical error, and its two realization leaves stay consequences: the
printed objects are quantified existentially. t5-glue's `ShimuraMainCM` is Shimura's Theorem 5.4 in Lang's idelic form
(numbers UNVERIFIED). theta-glue's `LinYangThetaCurve` is numerically VERIFIED (80 digits at 12 points) and `IgusaAlg`
by exact expansion, neither proved.

The r7 tasks checked their rows against the sources they could read; none reports a row false or vacuous, and none had
network access, so every locator is UNVERIFIED. reduct-b changes no statement: its three theorems prove the DVR fields
from the strictly henselian leaves already on the list. unipotent-b's `SemistableUnipotentPrintedGen` is 3.5 over the
printed strictly henselian base, with the echelon clause as recalled; its glue is needed only when the residue field
is imperfect. t09-pic states its four leaves over genuine definitions (Picard sheaf, `Pic⁰`, ample and very ample
bundles, Mumford's `ē_n` as `weilScalar`) and argues that `WeilPairingMumford` is a consequence of the print, not
stronger: each clause is one printed property and holds under either sign convention. shimura-cft's leaf (not used
here) is a consequence by its report, a composite by its review. kinds.tsv flags `deligneComponentsY3PrintedAb`
(depends on one display, Deligne 389 §5 and Milne 2005 §14) and `elkiesEquationsX6Ab` (its fibre clause), both GLUE by
the integrator's convention, and keeps the reading of Baba–Granath's table flagged on `babaGranathRationalAb`, LEAF.
igusa-alg's proofs replace theta-glue's exact expansions by Lean theorems with standard axioms; `LinYangThetaCurve`
stays a composite, numerically VERIFIED.

The r8 tasks and folds checked their new leaves with an AI statement review (two lenses, from memory, 11-14; recorded
in kinds.tsv's `rated_by`); none had network access, so every locator is UNVERIFIED. `GonzalezRotgerProp56X6` is
faithful, with `D(R)` to be confirmed against the paper; `NeronBaseChangeStrictHenselization` is a published form;
`ElkiesX6StarPrinted` is a consequence (the `ℚ̄`-point form of Elkies' coordinate statement), GLUE by the integrator's
ruling. Of the top's two new hypotheses, `X0ModuliGalois` is a consequence, and `ShimuraMainCM` cites the Artin-map
lemmas that fix its normalization. leaf-fold14's next-fold review rates `raynaudSemistableSH` and
`semistablePersistsSHcp` (a): kinds.tsv calls the first's reading risk (the print may assume an algebraically closed
residue field) low and the second a specialization of every reading of the print. t09-pic's four leaves are pending a
review (one model review, no errors), and kinds.tsv counts `weilPairingMumford` a composite in its strictest reading.
gt-valence's proof of the valence formula settles its statement: the volume is Mathlib's invariant measure, so it is
the genuine formula, neither vacuous nor stronger than its source.

The r9 tasks and folds checked their new leaves with AI statement reviews (two lenses, no print, 11-15; recorded in
kinds.tsv's `rated_by`); none had network access, so every locator is UNVERIFIED. leaf-fold20's two SGA 7 IX leaves
pass (`SGA7_IX_3_5_ForwardGeom` is a consequence under the alternative readings); `hFH` is a consequence of
Friedberg–Hoffstein's Theorem B, pending a reading of three clauses; `shimuraIntegralModelRep` is pending a reading of
the PEL functor and the level comparison. The integrator's dictionary ruling (11-15) re-rates `hCM` and
`uniformizationLeafAll` as consequences (each reached from its print through analytification), and `open-leaf-def`
restates OPEN.md's LEAF as the printed form or a direct instance of it. h33-sign verifies the `[i]` sign of `TYZThm33`
from the paper and pins it in Lean. gz-hl3 finds that Heegner rationality with a complex constant `c` is false for CM
curves, so its leaves take `c ∈ ℚ^×`; gz-heegner finds that the former `hX` covers only functions regular on `ℍ`, so
the Heegner point needs `X0ModuliGaloisMero`. After main, leaf-audit finds theta-fold's `LinYangEx29All` false and the
other 15 leaves of 11-15 sound. h29-fix finds TYZ's Lemma 2.9 false as printed at `n = 3` (`Q(3) = ±3` while `𝓛(3)² =
1`, by computation), so h29-ne3 restricts it to `n ≠ 3` and takes Theorem 2.1's instance at `(3, 1)`; kinds.tsv rates
the six leaves published, each restricted from the print, unread, or both. The integrator's statement review (11-15)
rates gz-hl3's two Gross–Zagier statements at the curves `C_d` as consequences (claims.tsv), where gz-hl3 rated them
printed; this report follows the review (Z-5, Z-6).

r10: ds965-weak's leaf `DSThm965Weak` holds under both printed wordings of Diamond–Shurman 9.6.5 ("characteristic
polynomial" and "satisfies") by or-introduction, which the integrator's ruling (11-16) counts as a direct instance;
the review then rated it GLUE through the coefficient extension, and coeff-ext and coeff-fix replace it by the print
over `K_{f,λ}` and the finiteness of `K_f`, the latter a composite (Diamond–Shurman prints only `k = 2`). The
dictionary pass (rater and skeptic, 11-16) re-rates nine fields and `h33` (§0) and restates four fields in printed
form (dict-models: each new leaf is the print, or the print with the reading made explicit by a disjunction or an
added hypothesis); kinds.tsv keeps `blr_7_2_1`, `sga7_IX_3_3_SHpre` and `sga7_IX_3_5_ForwardGeom` GLUE pending a
reading. t21-proof proves `hT21` outright, which TYZ's printed Theorem 2.1 at `(3, 1)` needed no reading for. The
integrator's dictionary rulings of 11-16 re-rate `picZeroAbVar`, `phiAmpleIsogeny` and `weilPairingMumford` as
consequences (Mumford's displays are over an algebraically closed field, and identifying his dual with the identity
component of the Lean's fppf `Pic_{A/K}`, then descending to `K`, are theorem steps), and `gagaMorphism` too (GAGA's
holomorphic map is reached from the uniformization only through the holomorphic inverse function theorem, and the
print for proper `X` is SGA 1 XII 4.4); `picRepresentableAbVar` stays a leaf, with Murre–Oort cited first. nv-local
finds `NVLocalInertia` true as stated and reduces it to `TameBranchNormal`, a statement of general commutative
algebra, which abhyankar proves. bfh-gamma0's `hBFH` is rated published, flagged: its definitions take readings (the
Petersson coset sum as the fundamental-domain integral, the Atkin–Lehner newform), under Diamond–Shurman's newform
convention one eigen property for the `Γ₀` action is not proved, and a cloud read matched it clause by clause, unread
by a human; bfh-gamma0 proves it equivalent to bfh-kronecker's leaf. gt-sga3's neighbourhood leaf left the chain
unread (sga3-nbhd, leaf-fold33). leaf-fold33: hcm-dict's `ShimuraThm54` is unread, a new printed leaf, and its
dictionary (the print's analytic isomorphism as `IsAnalyticUnif`) is proved in Lean; fold33-review flags `hGZ` pending
a reading, since three steps between Gross–Zagier's morphism `φ : X₀(N) → E` and the Lean pull-back are not proved
(D1, `ℚ`-embeddings of function fields are morphisms of the curves; D2, `φ` at Heegner points read through
`q`-expansions; D3, `IsOptimalParam` is the strong Weil parametrization); goodmodel-iso's and piczero-char0's leaves
are unread printed leaves.

## 5. Completeness check

### 5.1 Scenario A (compiled composite)

`python3 scratch/frontier/chain.py A` (from the repository root): 0 signature mismatches; 35 open nodes = the 24 + 3 +
2 = 29 fields of the three bundles of C4'''''''''' (each expanded from the structure as read at main) plus the 6 TYZ
and GZ hypotheses of the top: the hypothesis list of the composite of Z7 with Z10 and Z11, B9 with B10 to B13, and
C4'''''''''', all of them used (§4.17). With kinds.tsv's forms (its strict and strictest columns agree, and its
`frozenTarget` rows give the top): 15 LEAF and 20 GLUE strict, 27 and 8 lenient. `chain.py onep`: its hypotheses are
scenario A's (the three bundles and the six top Props); the bundles' fields are the 29 field rows of `kinds.tsv`, with
the names and type heads of the build's `open-statements.json`, whose six other hypotheses have scenario A's heads.

### 5.2 Scenario F (frontier)

`python3 scratch/frontier/chain.py F`: 0 signature mismatches over 226 theorem edges in the file (21 followed on the
route; no consumer replacement, no modus-ponens step and no transfer along an equivalence is followed); 35 open nodes
= the 35 of §0 (no never-projected field is left). Where a followed edge's file is not the H base, the check compares
the Prop it proves with the one the route uses (`defcheck`); in r10 no followed edge carries its own copy of the Prop
it proves, so it has nothing to compare (r9 compared nine, all identical or the kernel's own constant).
The F-only edges outside OneProof/H (fork PR #29 in library files, modular-split and c-to-printed2 in scratch files;
since leaf-fold33 the `C_d` edges are edges of both scenarios) prove library constants: each file imports ZInQKernel
modules and has no definition of the Prop it proves (or only a copy for an `rfl` check), and imports the module that
defines it, which `OneProof/Main.lean` imports too or the file of the edge that takes it; or the file is the library
module that defines the Prop, and the edge that takes it is in that module (`worldcheck`):
- `CarayolR17'` (`scratch/modular-split/R17.lean`): defined in `ZInQKernel/HDecomp/Conductor/LadicCond.lean`.
- `EigenformHTNew` (`scratch/c-to-printed2/CToPrinted2.lean`, which has only a `Verbatim` copy for an `rfl` check): defined in `ZInQKernel/OneProof/H/TailS.lean`.
- `AxSenTate` (`ZInQKernel/Contrib/OneProof/AxSenTate.lean`): defined in `ZInQKernel/OneProof/H/TailS.lean`.
- `TateTwistInvariants` (`ZInQKernel/Contrib/OneProof/TateTwistInvariants.lean`): defined in `ZInQKernel/OneProof/H/TailS.lean`.
No followed edge concludes a kernel constant written with `_root_` in the bundles, so `rootcheck` has nothing to
check; no followed edge's file is over leaf-fold4's chain, so `chaincheck` has nothing to compare; and `BYPASS` is
empty, so `bypass_check` has no consumer replacement to compare (r9 had theta-split's and dcy3-used's).
No followed edge that takes an F-only row has its own copy of the row's definition: the 0 that take one import it.
The pairwise checks of r2 still pass. The eight kernel leaf copies that the flat files carried are gone: OneProof/H
imports `ZInQKernel/HDecomp/Objects.lean` itself. mcr-quot's and shimura-split's T5 is the kernel's
`ObjBridge.TorsionStructure` or `PkgI2.TorsionStructure.{0}`, which `Objects.lean` proves equal by `Iff.rfl`
(`torsionStructure_iff`).

`python3 scratch/frontier/chain.py doc` compares the rows `Z-n`, `T-n`, `H-n` with the scenario-F open set: 35 rows
with 35 distinct heads, equal to the open set.

What the script does not check: that the edges compose in one Lean environment; argument instantiation (for example
`heckeVertWitness_of_leaves5` takes `R1R2fp`, extracted from `r1r2` by `Classical.choice`); section variables that a
theorem takes through `include` (none on the route since qm-glue replaced qm-split's `qmHauptmodulBase3_of_O1`); and
the defs that a Prop's def mentions (only the top-level def text is compared).

## 6. Integration state

### 6.1 Composites that exist
- **`ZInQ.OneProof.frozenTarget`** (main; leaf-fold33's bundles, with no glue bundle; B9 since leaf-fold-hx, B10 since
  leaf-fold29, Z10 and B11 since leaf-fold32, Z7, Z11, B12 and B13 since leaf-fold33): scenario A as one library
  theorem (§1).
- **C4'''''''''', leaf-fold33** (c0f3d085, over leaf-fold32, leaf-fold31 and leaf-fold30): 24 + 3 + 2 fields inside
  OneProof (`TailZ38`, `TailZ39`, `TailZ41`-`TailZ55` over leaf-fold29's `TailZ33`-`TailZ37` and `TailZ40`,
  leaf-fold19's `TailZ23`-`TailZ32`, leaf-fold13's `TailZ20`-`TailZ22`, leaf-fold11's `TailZ16`-`TailZ19` and
  `OneProof/Genus/*`, leaf-fold10's `TailZ10`-`TailZ15`, leaf-fold9's `TailZ5`-`TailZ9`, leaf-fold8's `TailY`-`TailZ4`
  and leaf-fold7's `TailP`-`TailX`); the contributions it folds are in `ZInQKernel/Contrib/OneProof/`, and
  leaf-fold33's copy reroutes in `ZInQKernel/OneProof/H/`; lake build and axioms REPORTED.
- **The top in the kernel**: C2 (atkin-li) with bfh-gamma0's Z10 in `Contrib/OneProof/BFHGamma0.lean`, theta-wp8's B9
  in `Contrib/OneProof/ThetaWeierstrass8.lean`, h29-ne3's B10 in `Contrib/OneProof/TYZLemma29Mod2.lean` and the fork
  PRs' and t21-proof's B11 in `Contrib/OneProof/LegendreThreeSquares.lean`, `JonesPall.lean` and `TYZThm21At31.lean`,
  hfx-proof's and hp23-proof's B12 in `TYZTestVectorExists.lean` and `TYZProp23Printed.lean`, hcm-dict's B13 in
  `ShimuraMainCM.lean`; gz-statements' `C_d` form of C2 (Z7) in `Contrib/GZStatements/Weak.lean`, with the `C_d` route
  Z11 in `Contrib/OneProof/HeegnerPointRationalCd.lean`, `GrossZagierAlgebraic.lean`, `Gamma0QExpansion.lean`,
  `EtaW32Character.lean` and `GrossConjugationCd.lean`.
- **The contributor and crowd kits** (contrib-kit 46afc732, w66; crowd kit 1c791eb1): `docs/one-proof/OPEN.md` and
  `pages-wanted.md`, generated from the build's `open-statements.json`, `kinds.tsv`, `claims.tsv`, `reviews.tsv`,
  `credits.tsv` and `issues.json`; `ZInQKernel/OneProof/Discharges.lean`, whose `#discharges` names the hypotheses of
  `frozenTarget` that a contribution proves; `scripts/one_proof/autofold.py`, which writes the fold that removes them
  and refuses a rise of either GLUE count; and `scripts/one_proof/frontier_crosswalk.py`, which maps this report's row
  IDs to the hypotheses.
- Superseded: C4''''''''' (leaf-fold29), C4'''''''' (leaf-fold19), C4''''''' (leaf-fold13), C4'''''' (leaf-fold11),
  C4''''' (leaf-fold9), C4'''' (leaf-fold8), C4''' (leaf-fold6), C4'' (leaf-fold5), C4' (leaf-fold4), C4
  (assemble-port) and the variants listed in r2.

### 6.2 What folding scenario F into C4'''''''''' needs
leaf-fold7 to leaf-fold33 take a fold only if neither GLUE count rises and the fold lowers the strict GLUE count or
replaces a consequence or composite by published-form leaves (leaf-fold9 §5; `autofold.py` refuses a rise). With this
report's forms (SPECULATIVE until compiled):
- modular-split (`r17` → `CarayolRealization`) and c-to-printed2 (`eigenformHTNew` → `KatoRealizationCohSS`): neutral
  (consequences both);
- after main on the other rows: the branches listed in §0, marked in the rows.

### 6.3 The library theorem
`ZInQ.OneProof.frozenTarget` has exactly the hypotheses of scenario A, and its proof uses all of them. Since
leaf-fold-hx `hX` is gone (B9); since leaf-fold29 h29-ne3's six published leaves replace `h29` (B10), three of them
theorems since leaf-fold32 (B11) and two more since leaf-fold33 (B12), so its TYZ hypotheses are `h11`, `hL29`, `hCM`
(since leaf-fold33 of the type of Shimura's printed Theorem 5.4, B13) and `h33`; since leaf-fold32 `hBFH` replaces
`hFH` (Z10), which had replaced `hL2` in leaf-fold24 (Z6), and since leaf-fold33 `hGZ` replaces `hL3` through the
`C_d` route (Z7, Z11); it takes no glue bundle. Each F edge removes or replaces a hypothesis once folded.

## 7. Findings

**Refresh r10 (2026-11-16).**

1. **20 rows proved, three pruned, eleven replaced and fourteen off the route** (§0, §4.1). The 11 new rows are 8
   published forms, 3 composites. The total goes from 72 to 35, the strict count from 49/23 to 15/20 and the lenient
   count from 60/12 to 27/8.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold33: 35 hypotheses,
   all used. Its 29 fields are 11 LEAF and 18 GLUE strict by the integrator's table, as OPEN.md's count line says;
   with the top, 15 LEAF and 20 GLUE strict, 27 and 8 lenient. `chain.py onep` reads its hypotheses from `Main.lean`
   and finds scenario A's, and the bundles and the top agree with `kinds.tsv` and the build's `open-statements.json`.
3. **The fields go from 51 to 29, the glue bundle is gone, and the printed restatements stay** (§4.1). sgr-direct
   takes the integral model of the Shimura curve out of the proof: `HeckeVertWitness`, the one consumer of
   `shimuraIntegralModelRep` and of the glue field `quotientP1Coordinate`, follows from bundle fields and one glue
   Prop of tame commutative algebra, which abhyankar proves through nv-local's `TameBranchNormal`; so mcr-glue's and
   mcr-quot's nine rows, three of them project glue, leave the frontier with the field they split. persists-dvr and
   fork PR #24 prove `semistablePersistsSHcp` and `regularSmoothPerfect`; dcy3-fold, pi0-fold and theta-fold2 prune
   `deligneComponentsY3PrintedAb`, `deligneComponentsX6PrintedAb` with `geomConnOfAlgClosure`, and
   `thetaRatiosAlgebraic`, whose use form theta-direct proves with no hypotheses; fork PRs #25, #29, #31, #34 and #35
   and milne-compile prove seven textbook and added fields, and ega-limit `egaIV_8_10_5_xii`; coeff-ext and coeff-fix
   replace `dsThm965` (through ds965-weak's `dsThm965Weak`) and `dsThm966` by Diamond–Shurman 9.6.5 and Deligne–Serre
   4.1 as printed, and dict-models, dict-galois, gt-sga3 and pic-fix restate seven more fields (leaf-fold32).
   leaf-fold33 then proves `neronBaseChangeStrictHenselization`, `poincareComplement`, `weilPairingMumford` and
   `phiAmpleIsogeny` with no new leaf, reroutes `homFreeFiniteAlgClosed` and gt-sga3's neighbourhood form away, and
   replaces `picZeroAbVar` by Kleiman's Theorem 9.5.4 and `mumfordGroupLawConn` with `neronSchemeExtensionExists` by
   BLR's Néron existence theorem over a Dedekind base: of leaf-fold32's eleven printed leaves six stay, and
   leaf-fold33 adds two.
4. **The top has six hypotheses**: fork PRs #36 and #38 prove `hL3s` and `hJP` (Legendre's three-square theorem and
   the Jones–Pall form), t21-proof proves `hT21` (TYZ's Theorem 2.1 at `(3, 1)`, with rigorous `L`-value bounds by
   kernel computation), and hfx-proof and hp23-proof prove `hfx` and `hP23`, so five of h29-ne3's six leaves are
   theorems; bfh-gamma0's `hBFH`, a published form, replaces the consequence `hFH`; hcm-dict retypes `hCM` to
   Shimura's printed Theorem 5.4 (a consequence before, a leaf now); gzopt-dict's `hGZ` replaces the composite `hL3`
   (finding 7); and the dictionary pass re-rates `h33` a consequence: 4 LEAF and 2 GLUE strict.
5. **The strict and strictest columns of `kinds.tsv` agree**; two published kinds are GLUE in both, pending a reading
   (`sga7_IX_3_3_SHpre`, `sga7_IX_3_5_ForwardGeom`), and so is the top's `hGZ`; this report records them as
   composites.
6. **The dictionary rulings raise the GLUE count**: `picZeroAbVar`, `phiAmpleIsogeny`, `weilPairingMumford`
   (leaf-fold31) and `gagaMorphism` become consequences, and the dictionary pass (leaf-fold32) makes the four height
   fields, the two Hodge fields, `gonzalezRotgerProp56X6`, `elkiesX6StarFunctionField` and the top's `h33`
   consequences and `gonzalezRotgerX6Ab` a composite: each needs a theorem step between the print and the Lean
   statement (§4.18). The printed restatements (finding 3), leaf-fold33's proofs of `phiAmpleIsogeny` and
   `weilPairingMumford` and its reduction of `picZeroAbVar` to Kleiman's printed theorem, and the tasks after main
   (§0) answer part of it.
7. **The `C_d` route is in the library theorem** (leaf-fold33, Z7 and Z11): heegner-32 builds the Heegner point from
   `hCM` and the two Gross–Zagier statements at the curves `C_d`, gz-conj proves the conjugation relation, and
   gzopt-dict reduces the formula to `hGZ`, Gross–Zagier over the algebraic `X₀(N)`, with its two other leaves proved
   (gamma0-qexp, etaw32-proof). The composite `hL3` is replaced by one printed statement, which counts GLUE until the
   steps D1 to D3 between the print and the Lean form are proved or read away (fold33-review, §4.18).
8. **After main** 46 branches report results on 23 rows (§0); this report does not use them until they are merged.
9. **Project glue**: no row is project glue.
10. **chain.py**: the H base is leaf-fold33 (`sixContactMin_of_open48` in `TailZ55.lean`; bundles in `TailZ50.lean`,
   `TailZ55.lean`); B11 to B13 and Z10 are edges of both scenarios, and so are Z7 and Z11 since leaf-fold33; Z6, Z8
   and Z9 are off the route; `BYPASS` is empty; scenario F differs from A only by modular-split's and c-to-printed2's
   splits.

**Refresh r9** (unchanged):

1. **Five rows proved, two pruned, eight replaced, five off the route, one split** (§0, §4.1). The 18 new rows are 11
   published forms, 5 consequences of one theorem and 2 composites. The total goes from 75 to 72, the strict count
   from 49/26 to 49/23 and the lenient count from 59/16 to 60/12. Main moved on to leaf-fold30 after the snapshot;
   this report describes leaf-fold29.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold29: 62 hypotheses,
   all used. Its 51 fields are 39 LEAF and 12 GLUE strict by the integrator's table (41 and 10 with
   `weilPairingMumford` and `dsThm965` published); with the top, 47 LEAF and 15 GLUE strict, 53 and 9 lenient.
   `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles and the top agree
   with `kinds.tsv` and the build's `open-statements.json`.
3. **The top has eleven hypotheses**: `hX` is gone (theta-wp8's B9 takes Shimura reciprocity at level 32 from
   `ShimuraMainCM` alone), `hFH`, a single leaf, replaces the composite `hL2` (gz-fh), and h29-ne3's six published
   leaves replace the composite `h29` (B10). TYZ's Lemma 2.9 is false as printed at `n = 3`, so that case is Theorem
   2.1's instance. Two of the eleven are consequences since the dictionary ruling (`hCM`, `hFH`).
4. **leaf-fold29 removes four fields with no new leaf**: bg-explicit, st-qbar and faltings5-lower prove
   `babaGranathRationalAb`, `shimuraTaniyamaQbar`'s one use and the lower half of Faltings' Lemma 5, and r6-nf with
   neron-dvr applies `r6` only at number fields, so BLR's existence theorem is needed only there (from the field N1).
   dcy3-used, merged by the same fold but not folded, shows that `deligneComponentsY3PrintedAb` is used only as
   `Y3Connected`, which two fields give; scenario F replaces its consumer.
5. **The SGA 7 IX fields are strictly henselian now**: leaf-fold20 proves `sga7_IX_3_3` and `semistableUnipotent` from
   the strictly henselian forms, so unipotent-b's split and its glue `SemiAbelianDescendsSepClosed` are off the route;
   every SGA 7 IX field of the library theorem is stated over a strictly henselian base.
6. **On the curves `C_d` the split of `hL3` has no composite.** gz-hl3 makes the Heegner point a Lean object; on
   gz-statements' `C_d` form of the top, gz-weil's parametrization of `C_d`, with Jacobi's derivative formula proved
   by jacobi-lambda (both on main through leaf-fold-hx), removes its composites `StrongWeilCurve` and
   `IsogenyLattice`, and gz-heegner proves the Heegner point's rationality from `hCM` and a printed consequence.
   Scenario F takes that form (Z7 to Z9): `hL3` rests on one published form and three consequences (the integrator's
   ratings). A fold needs the library theorem to take `GrossZagierHeegnerCd`; strict GLUE +2, lenient −1, so the fold
   is held.
7. **After the snapshot the `C_d` route of `hL3` shrinks to one leaf** (not used here; the branches were pushed after
   the branch heads were read): heegner-32 (718d8d4c) proves `GrossZagierHeegnerCd` from `hCM`, `GrossZagierFormulaCd`
   and `GrossConjugationCd`, with no canonical model of `X₀(N)` and no `WeierstrassUniformization`; gz-conj (2c7ce521)
   proves `GrossConjugationCd` outright; gz-moduli (85111fc7) proves `GrossZagierFormulaCd` from the single leaf
   `GrossZagierModuliCd`, the Gross–Zagier formula in its printed moduli form. Folded, `hL3` would be replaced by
   `GrossZagierModuliCd` alone: strict GLUE −1 if it rates printed. The integrator records this as pending that
   rating, expected −1.
8. **The re-ratings**: the dictionary ruling makes `hCM` and `uniformizationLeafAll` consequences, and `dsThm965`
   carries a strictest-reading flag (Diamond–Shurman may print only that Frobenius satisfies the polynomial), so this
   report records it as a composite, as it does `weilPairingMumford` and `deligneComponentsY3PrintedAb`.
9. **After main** 21 branches report results on 24 rows (§0); this report does not use them until they are merged.
   leaf-audit finds one of theta-fold's two leaves (`LinYangEx29All`) false.
10. **Project glue** is 3 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`.
11. **chain.py**: the H base is leaf-fold29 (bundles in `TailZ37`, `TailZ32`, `TailZ34`, `TailX`); B9, B10 and Z6 are
   edges of both scenarios; dcy3-used's consumer replacement joins theta-split's; scenario F's top is gz-statements'
   `C_d` form of C2, with jacobi-lambda's and gz-heegner's `C_d` theorems, and gz-hl3's general split stays in the
   file off the route; `worldcheck` accepts a constant defined in the module of the F edge that takes it, or in the
   edge's own library module.

**Refresh r8** (unchanged):

1. **Nine rows proved, two pruned, four replaced** (§0, §4.1). The 4 new rows are 3 published forms and 1 consequence
   of one theorem, and five rows that were open only in scenario F are fields now. The total goes from 86 to 75, the
   strict count from 54/32 to 49/26 and the lenient count from 68/18 to 59/16.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold19: 65 hypotheses,
   all used. Its 58 fields are 44 LEAF and 14 GLUE strict by the integrator's table, as OPEN.md's count line says (45
   and 13 with `weilPairingMumford` published); with the top, 47 LEAF and 18 GLUE strict, 55 and 10 lenient. `chain.py
   onep` reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles and the top agree with
   `kinds.tsv` and the build's `open-statements.json`.
3. **The CM hypothesis rests on two printed leaves**: gt-ringclass proves `RingClassLattice`, so the library theorem
   takes `ShimuraMainCM` and `X0ModuliGalois` (T-15, T-16) in place of `hS`, and tyz-split's and t5-glue's splits are
   off the route.
4. **Three of the four SGA 7 IX DVR fields are gone from the library theorem**: leaf-fold14 folds reduct-b's Route
   B-cp, so the strictly henselian `raynaudSemistableSH` and the restricted `semistablePersistsSHcp` are fields in
   their place, and gt-shpair proves the strict-henselization pair from BLR §1.2 Prop. 2 in every characteristic; the
   fourth, `semistableUnipotent`, stays a field.
5. **Contributions fold mechanically**: since gt-ega, the integrator's `autofold.py` writes each fold (the next bundle
   generation, its conversion, the top, `kinds.tsv`, `claims.tsv`), and refuses a rise of either GLUE count. sem-prune
   removes the two fields that gap-triage found used only syntactically.
6. **One field table for the whole theorem**: kinds.tsv's rows with bundle `frozenTarget` give the forms of the seven
   TYZ and GZ hypotheses, and they agree with this report's rows (§2.2, §3.2).
7. **claims.tsv** (crowd kit): the cloud claims are batch and round labels with public holders; it still lists
   unipotent-b and igusa-alg as in progress, merged in w66 and not folded.
8. **Nine branches after main** (gt-rayclass, gt-rigidity, gt-sga3, gt-sga7, gt-unip, gt-x6facts, rayclass-cft,
   linyang-printed, sh-printed2) report reductions of fields on the list (§0); this report does not use them until
   they are merged.
9. **Project glue** is 4 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `SemiAbelianDescendsSepClosed`.
10. **chain.py**: the H base is leaf-fold19 (bundles in `TailZ29`, `TailZ32`, `TailZ31`, `TailX`); B8 is an edge of
   both scenarios; fork PR #19's proof of `mulEtaleAbelianScheme` is an F edge, since unipotent-b's split still takes
   it; `onep` compares the top with kinds.tsv's `frozenTarget` rows through the build's JSON.

**Refresh r7** (unchanged):

1. **One row proved, two split, three off the route, five replaced** (§0, §4.1). The 11 new rows are 6 published
   forms, 3 consequences of one theorem, 1 composite and 1 project glue. The total (86) and the strict count (54/32)
   are r6's; the lenient count goes from 69/17 to 68/18.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold13: 71 hypotheses,
   all used. Its 65 fields are 46 LEAF and 19 GLUE strict by the integrator's table (47 and 18 with
   `gonzalezRotgerCountX6Ab` published); with the top, 48 LEAF and 23 GLUE strict, 59 and 12 lenient. `chain.py onep`
   reads its hypotheses from `Main.lean` and finds scenario A's, and the bundles agree with `kinds.tsv` and the
   build's `open-statements.json`.
3. **One field table.** The forms of the fields come from the integrator's `kinds.tsv`; r6's own `fields11.tsv` is
   gone. The table's strictest column is this report's strict count, and its strict column the alternative.
4. **x6-glue's leaves are on abelian schemes now**, so the rows that carry `R1fpProps` shrink to H-154; their open
   check rests on `mumfordRigidityCore` (H-170).
5. **The SGA 7 IX rows**: reduct-b takes `SemistableReductionSH`, `ReductionFromSH` and `StrictHenselizationNeron` off
   the route, and unipotent-b replaces `SemistableUnipotentSH` by the printed 3.5; the base reading of the DVR fields
   (a human reading of SGA 7 IX) still decides whether they count as consequences.
6. **The theta route rests on one leaf**: igusa-alg proves `IgusaAlg 5` to `9` in Lean, so `QMThetaSymmetricCurve`
   follows from `LinYangThetaCurve` alone.
7. **claims.tsv lags w66**: it lists reduct-b, unipotent-b, t09-pic and igusa-alg as in progress, but their reports
   are merged and scenario F uses them.
8. **Project glue** is 5 Props: `CMStabObj`, `CoverModelOfHeckeN`, `P1SchemeQ`, `RingClassLattice`,
   `SemiAbelianDescendsSepClosed`.
9. **chain.py**: the H base is leaf-fold13 (bundles in `TailZ22`, `TailZ11`, `TailX`); the field table is `kinds.tsv`,
   and `onep` also compares the bundles with `open-statements.json`; r6's branch heads are read at main; `worldcheck`
   accepts a copy for an `rfl` check in a `section Verbatim` and at main.

**Refresh r6** (unchanged):

1. **6 rows proved, 10 split, 6 off the route, 3 replaced** (§0, §4.1). The 27 new rows are 12 published forms, 10
   consequences of one theorem, 2 composites and 3 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold11: 67 hypotheses,
   all used. Its 61 fields are 43 LEAF and 18 GLUE strict by the integrator's convention (44 and 17 with
   `gonzalezRotgerCountX6Ab` published; leaf-fold11's own count 50 and 11); with the top, 45 LEAF and 22 GLUE strict,
   56 and 11 lenient. `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's.
3. **The strict convention changes counts, not rows.** A leaf with a flagged plausible weaker reading counts GLUE (the
   four SGA 7 IX DVR fields, `blr_1_2_4`, `sga7_IX_3_3`); a merely unread leaf stays LEAF, flagged
   (`faltingsLemma5Printed`, `raynaudKernelBound`, `sga3_VIB_3_10`). The strictly henselian rows (H-182, H-183, H-184,
   H-185) keep the first version of the base review.
4. **The moduli-witness rows rest on one field.** r5's open check on the rows stated on `R1fpProps` (rigidity,
   extension of the polarization) now rests on the field `mumfordRigidityCore` (H-170), which route-a-fold added;
   scenario F reaches `r1r2Ab` and `shimuraFamilyAb` from the old forms through route A's transfers. `RayClassCM` is
   not among the 18 transfers r1univ-rigid compiled.
5. **`thetaRatiosAlgebraic` leaves by replacing its consumer**, and its curve part is now a composite leaf plus closed
   polynomial identities: theta-glue proves `ThetaEightSquare` and `IgusaAlg 3`, `IgusaAlg 4`; `IgusaAlg 5` to `9` are
   VERIFIED by exact expansion and not yet in Lean.
6. **Project glue** is 6 Props: `CMStabObj`, `CoverModelOfHeckeN`, `IgusaAlg`, `P1SchemeQ`, `ReductionFromSH`,
   `RingClassLattice`.
7. **chain.py**: the H base is leaf-fold11 (bundles in `TailZ19`, `TailZ11`, `TailZ18`, `TailX`); leaf-fold11 has no
   field table, so this report keeps `fields11.tsv`; edges along an equivalence (`iff`) are checked on both sides of
   the `↔`; the w62 draft's genus-route bypass and rigidity form leaf are gone with the fields; `UNUSED` and
   `USED_IN_F` are empty.

**Refresh r5** (unchanged):

1. **1 row proved, 14 split, 3 off the route, 1 dropped** (§0, §4.1). The 23 new rows are 7 published forms, 9
   consequences of one theorem, 1 composite and 6 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, now over leaf-fold9: 69 hypotheses,
   63 used by its proof (39 LEAF and 24 GLUE strict, 49 and 14 lenient). `chain.py onep` reads its hypotheses from
   `Main.lean` and finds scenario A's.
3. **H-43 had not been reduced in r4.** qm-glue's `ConicCanonical` is `X6Kummer.X6ConicModel` verbatim (shimura-split,
   `Iff.rfl`), so r4's F route for H-43 was a renaming; scenario F now takes H-43 from shimura-split's smaller leaf
   `ElkiesConicX6`, with `r1r2` and T5.
4. **Forms.** `GonzalezRotgerCountX6` (the new field under `r5count`) counts as a composite, by the integrator's ruling
   and my reading of its existential witness (leaf-fold9 lists it as a published form); open check: `inertCount6` is
   González–Rotger's `b`. reduct-split's three leaves on the list are published forms pending the review of the
   printed base ring (§0 gives the count without them). modular-split's `HTDual`, which the report calls a named glue,
   counts as project glue.
5. **Project glue** is 9 Props: the coordinate's three, reduct-split's four (local-to-global steps, and
   `FixedTorsionRationalImperfect`, which only imperfect fields need), and modular-split's `H0DifferentialsEqHolo`
   (the last step of `dimJacobianEqGenus`, no literature left) and `HTDual`.
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-79 (no
   `Γ₁(N)\ℍ*` in Lean), H-13 (`r16`, modular-split §4.1), `ShimuraGoodReductionNoGuard` (abelian schemes over a base),
   `T10_TateDuality` (never projected; reduct-split §4).
7. **chain.py**: the H base is leaf-fold9 (bundles in `TailZ9`, `TailZ4`, `TailX`); a declaration can be picked by
   occurrence (`nth`); `USED_IN_F` is recomputed; `worldcheck` checks that the library files of shimura-split and
   modular-split prove the library's own constants.

**Refresh r4** (unchanged):

1. **10 rows proved, 39 split** (§0, §4.1). The new rows are 35 published forms, 13 consequences of one theorem,
   8 composites and 3 project glue.
2. **Scenario A is one compiled theorem** on main, `ZInQ.OneProof.frozenTarget`, with 66 used hypotheses: 41 LEAF and
   25 GLUE strict, 52 and 14 lenient. `chain.py onep` reads its hypotheses from `Main.lean` and finds scenario A's.
3. **T-11 is a published form and compiled**: TYZ Theorem 3.3 as printed (Period7.tex read by tyz-split), restricted
   to `n ≡ 5, 7 (mod 8)`; leaf-fold8 put tyz-split's derivation of the pinned form into OneProof. T-5 stays GLUE: no
   printed form of Shimura reciprocity can be stated over Lean's definitions today, and the split gives a CM part (a
   consequence of Shimura Thm 5.4) and a modular-curve part.
4. **Forms.** A field of C4'''' has leaf-fold8's form (its §2): SS1, SS2, SS3 and `FaltingsLemma5BC` are
   consequences (height-split's own caveats and review), `JavanpeykarBound` and `IgusaCMValue24` published forms, and
   Igusa's `ψ₄`, `χ₁₀` published forms with qm-split's flag. Four F-only leaves of height-glue and qm-glue whose own
   docstrings or reviews name more than one source are counted by my reading, not as published forms: `CMDescent` and
   `ConicCanonical` (consequences), `QMUniformizationC` and `CanonicalCoarseX6` (composites).
5. **The project glue left is under the coordinate**: `QuotientP1Coordinate` in scenario A; in scenario F,
   `P1SchemeQ`,
   `CMStabObj` and the decomposition's `CoverModelOfHeckeN` (§4.1: counted open, since the chain derives it only
   downstream of the coordinate).
6. **Not splittable today** (rows kept): H-9 (Pan and Berger need `B_st`), H-53 (the dual abelian variety), H-78
   (`H¹(X, 𝒪_X)` on schemes), H-79 (no `Γ₁(N)\ℍ*` in Lean; its consumers could use Riemann–Hurwitz instead, curve-split
   §3.5), `ShimuraGoodReductionNoGuard` (abelian schemes over a base), `EigenformHTNew` (Kato's objects), H-59
   (`Y3Connected`: qm-glue reads it as the existential statement about the canonical model itself).
7. **chain.py**: the H base is read from OneProof/H at main; the def check tells the kernel's own constants (which
   OneProof/H imports) from copies and compares Props an F edge introduces with the files that take them; new checks
   for the files over leaf-fold4's `TailK` and for `_root_` kernel fields; `onep` compares the library theorem with
   scenario A and leaf-fold8's field table; a block ends at the next docstring; binders a consumer quantifies over
   can be listed (`bound`).

**Refresh r3** (unchanged):

1. **Form column and two counts** (the integrator's ruling): 17 published-form rows are LEAF in both counts; 24
   consequences of one theorem are LEAF only in the lenient count. Each names the derivation to compile.
2. **The TYZ premise is four Props in the kernel** (tyz-chain): `TYZThm11Integral` (published form), `TYZLemma29Mod2`,
   the CM leaf and `TYZThm33Pinned` (composites); `TYZLcalOne`, `Lemma321Five`, `Lemma318Literal`, `Thm35First` and
   `SqrtTwoNotInHHprime` are proved or reduced in kernel modules.
3. **leaf-fold5 compiles r2's H list**, except that it keeps av-b1's glue `SimpleImageIsogeny` (the frontier splits it
   into H-73, H-74 again; leaf-fold5 §1.3 gives the variant with T8 kept as a leaf, 69 Props with one glue).
4. **leafq-check** proves `GammaStarGen` and replaces three LEAF? fields by smaller statements (H-86..H-88).

**Refresh r2 and the 17:35 report** (unchanged):


1. **leaf-fold4 compiles the 17:35 frontier.** Scenario A's 69 projected Props are the 17:35 list minus
   `DivisiblePoints` (VERIFIED by chain.py). What was a textual composite of branch results at 17:35 is now one compiled
   theorem.
2. **Fork main carried the 11:21 version of this report** (79 open) until integration w51 merged wip/frontier d8c95123
   at 22:32. The upstream issues had been built from wip/frontier 249195fd, whose rows equal the 17:35 list.
3. **The statement reviews and this report's classes differ on five open rows** (H-3, H-16, H-21, H-25, H-38; §4.7).
4. **Reductions recorded but not folded.** tyz-318 reduces the LEAF T-4 to the GLUE `SqrtTwoNotInHHprime` (TYZ's Step 3)
   and proves T-4 outright when `n` is the only divisor `≡ 5 (mod 8)`; sqrt2-glue works on the rest. shimura-modfn
   splits the CM leaf T-5 but recommends keeping it: at Heegner points where the plane model `(j, j_N)` is singular,
   `j(τ)` and `j(Nτ)` do not determine `g(τ)` (its example `Q = [32,10,1]`, `D = −28`, numerically VERIFIED there).
5. **chain.py repair.** The 17:35 script read ts-kummer at d9c06585, which is not on the fork; r2 reads ts-kummer's final
   1bbe3543, which has the same six theorems. Those edges are off the route since C4'.
6. **av-b1's head 02ae2421 is an unchecked snapshot** from a host shutdown; r2 uses av-b1's files as merged into main.

**From the 17:35 report** (unchanged; for item 1, T3, T6-T9, T11(b), T26, T34, T38 and T41 are now proved or reduced,
and the open textbook rows are those of §4.3 and §4.5):

1. **The brief's "every textbook leaf T1-T32 is proved" is false** (VERIFIED: agent grep of the 150 newest refs, my grep
   of 80 refs for six of the Props). Proved: T2, T14(a′), T14(b′), T15, T16(a), T17, T18, T20, T21, T25, T28, T31 (and
   T36, T37 inside `x1`). Open: T1, T3, T4, T5, T6, T7, T8, T9, T10, T11(a), T11(b), T16(b), T23, T24, T26, T27, T29(a),
   T29(b); of these T1, T10, T16(b), T29 are never used. Since 12:45, T26 follows from T5 (t5-torsion), so T26 is no
   longer on the list.
2. **`GluePieces4.tateRamAtThree` is likely false as stated** (linked-ram finding F1, SPECULATIVE there): it is not
   quantified over `G7Data`, so g0-assemble3's `[L:ℚ] ≤ D` fix does not reach it. If so, g0-assemble3's
   `sixContactMin_of_leaves4` is vacuous. C4 (assemble-port) replaces it by linked-ram's `UnramTate.TateRamAtThreeD`
   (adds `Module.finrank ℚ L ≤ ZInQ.heightD`), which is proved there; route T does not need it either.
3. **Stale status texts.** STATUS.md and README say `HeckeThetaNewform` is "reduced to Atkin–Li"; it is proved
   (atkin-li, now on fork main w45). h-decomposition §2.2 on main marks T14, T28, T36, T37 open (proved) and lists T39
   as a leaf (it follows from T40). g0-assemble3's docstrings call `heckeIrreducible` "truth SPECULATIVE" (settled by
   ts-hecke) and its §6 misses the unused fields `r1rec, r3, r4, r5, r7b, r8, t10`. cm-numeric's report still lists
   `IInH4`, `HprimeNormal`, `GenusFieldLeLni` as leaves (all proved). The reports of ts-kummer and prop-ts-glue still call
   `KummerCompositum` open (kummer-comp's note). assemble-port's LEAF/GLUE labels are not the strict ones (§6.1).
4. **TYZ.** `CMNumeric.tyzZ` and `CMBridge.tyzZ` are two constants with the same body (an integration must keep one; T-6
   is stated at `CMBridge.tyzZ`). T-6, T-7 and the CM leaf are stated through the eta model `X0.phiC`; x0-32's eta
   leaves `EtaModelInvariant`, `EtaModelFricke` are now proved (tyz-cm), but the identification of `X0.phiC` with the
   modular parametrization also rests on x0-32's analytic-model statements, which are not hypotheses of the chain.
5. **Name collisions to resolve when folding**: three structures named `GluePieces5` (cpts-transport, linked-ram,
   assemble-port) and two named `HSyn.GluePieces4` (g0-assemble3, lt-goodred); `WeilPairing.IsogenyQuasiInverse` vs
   `HSyn.G0RevIsog.IsogenyQuasiInverse`; `PropTSGlue.propTSAll_final'` (prop-ts-glue vs ts-sn).
6. **Statement changes proposed here: none.** (Finding 2 is linked-ram's proposal, adopted by assemble-port; gz-decomp's
   `GrossZagierCd` and gz-statements' restricted GZ leaves are on record.)

## 8. Tasks (snapshot 11-16 22:56 PST; heads in `scratch/frontier/refs.txt`)

Finished, with results used in r10: ds965-weak (b893b3da), sgr-direct (56478c75), sgr-fold (b7dfa3da), persists-dvr
(d72c27d6), pi0-fold (2d6070e5), nv-local (c137bf8c), abhyankar (7b72ece3), theta-direct (584bbb24), theta-fold2
(f86320f2), milne-compile (fb502062), gt-sga3 (deba22d7), bfh-leaf (516c2abe), bfh-kronecker (c282ffab), bfh-gamma0
(96a4acb9), t21-proof (f597c34c), ega-limit (6b7310a4), dict-models (ca225d00), coeff-ext (bca51e5c), coeff-fix
(496c1f75), pic-dict (4e95795b), pic-fix (be79cb5b), neron-sh-proof (3842078a), poincare-proof (5795bbc0), period-odd
(6382ef59), cd-optimal (04d7251c), gz-optimal (2631cd0b), gz-moduli (85111fc7), gz-weil (ad22e947), heegner-32
(718d8d4c), gz-conj (2c7ce521), gzopt-dict (92b6cd1e), homfree-noemb (24586d41), etaw32-proof (21a80bfa), hfx-proof
(779d0d7d), hp23-proof (ca83418a), sga3-nbhd (ac9ad381), group-law-dvr (3ab4d8eb), goodmodel-iso (894fb85b),
fold33-copy (5fd456c2), hcm-dict (d1ae76f6), weil-proof (cefb4883), piczero-char0 (2cc19764), fold33-pic (ee94a3e5),
idcomp-lft (87614d93), piclft (6a774a40), phi-ample (7da495fc), gamma0-qexp (8d1223be), phisurj (5507316e), dcy3-fold
(75ae0bdf, as leaf-fold30 merged it) and fork PRs #24 (f85ef980), #25 (7c9177bd), #29 (fefce8ef), #31 (d42bb38f), #34
(4fa17fc5), #35 (37a97052), #36 (47ca4df2), #38 (a9bc2e35); the folds leaf-fold30 (a1dddf46), leaf-fold31 (2880fef1),
leaf-fold32b (6b7a4544), leaf-fold33b (c0f3d085). After main, not used: r16-used (dcf24ac6), isj1-dict (37628525),
x1-igusa (62d9b7c5), weber-field (f2cf835b), aftate-or (7378fd4e), sga1-fix (06be00c5), gaga-chart (5626f0b0),
gr56-prove (90b817cb), gr14-narrow (830ff58d), sga7-cp (0c200c57), composite-out (822da7b5), shimura-split2
(838a7430), holfam (93220b34), pel-hodge (1d9922c7), pb-bypass (c1636db9), pb-fix (e479bc56), pb-fix2 (401a7523),
ht-exists (7088f9ed), r17-bypass (3e6e5017), faltings-cm (ce696e14), height-fix (49e6d97d), javanpeykar-fix
(3d1ce928), aftate-fix2 (c56922c0), charpoly-ell (0d75311f), deg-det (ecf7da39), coeff-field (5bb50efa), nos-proof
(e9828e92), gr-dict (48db1227), h33-dict (d489fc13), gaga-serre (1d7687e7), dict-galois (81d1f67f), coeff-rational
(e85590b8), hodgetate-from-dr (7320b450), derham-print (ccb19bd3), grx6ab-print (b047ce25), elkies-print (168bbb39),
semiab-descend (6a6de248), javanpeykar-rebase (4cb6a008), sga33-shpre (ffd056ea), y3abu-print (579a89bb), y3abu-strict
(e0197d03), tyz-genus (01ad83f2), gz-dict2 (4fd8ddd2), bst-construct (fe8b3066), eichler-bound (09896d1f), r17-print
(785e3f29). Used in r9 and compiled inside C4'''''''''' or applied by scenario F since: leaf-fold20 to leaf-fold29,
leaf-fold-hx, gt-sga7, gt-unip, yu-prune, gt-rayclass, sgr-split, h33-sign, gt-rigidity, rigid-prune, r16-split,
elkies-coord, flt-cqj2, theta-wp8, gz-hl3 (bbb6c764), gz-heegner (58a780e4), jacobi-lambda (b6fc38e9), open-leaf-def,
bg-explicit, st-qbar, faltings5-lower, neron-dvr, r6-nf, h29-split, h29-fix, h29-ne3 and dcy3-used (folded by
dcy3-fold); off the route now: gz-fh (bfh-gamma0's Z10 replaces its Z6). Used in r8 and compiled inside C4''''''''''
since: leaf-fold14 to leaf-fold19, sem-prune, the crowd kit and the gt tasks of r8; read in r8, off the route now:
unipotent-b (24c44f3d), shimura-cft (c1f76fc2). Used in r7, off the route now: igusa-alg (c9360203). Used in r6 and
compiled inside C4'''''''''' or applied by scenario F: leaf-fold11, leaf-fold10, the prune, genus-fold, route-a-fold,
shimura-glue, reduct-glue, dimjac-glue, genus-route, r1univ-rigid, c-to-printed2, t5-glue, x6-glue; off the route now:
theta-split, theta-glue. Used in r5: leaf-fold9, shimura-split, reduct-split, modular-split and tyz-split's statement
review. Used in r4: leaf-fold8, coarse-factor, cloud-w07 (fork PR #11), leaf-fold7, height-glue, qm-glue, leaf-fold6,
av-glue, av-split, height-split, curve-split, hodge-split, qm-split, tyz-split, fork PRs #6-#10; off the route now:
mcr-glue, mcr-quot. Used in r3: leaf-fold5, leafq-check, tyz-chain and the r2 tasks. Read, not folded: leaf-review-a,
leaf-review-b. Cloud claims: claims.tsv (§0).

Running tasks are on the fork's tracker issue #3.

gz-statements (`ZInQKernel/Contrib/GZStatements/Weak.lean`, on main since 11-13) proves that the narrower
`ZInQ.GZStatements.FHNonvanishingCd` and `GrossZagierHeegnerCd` (restricted to `C_d`, `d ≡ 5 mod 8`, `D < −4`) follow
from `FHNonvanishing` and `GrossZagierHeegner` and still give `ZInQ.FrozenTarget`
(`frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`). Scenario F takes that form
since r9, and the library theorem since leaf-fold33 (Z7, Z11, §2.1).

This branch is fork main c0f3d085 plus this refresh.
