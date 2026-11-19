import ZInQKernel.OneProof.H.TailZ97
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing

/-!
# The whole proof in one theorem

`ZInQ.OneProof.frozenTarget` derives the frozen target `ZInQ.FrozenTarget` from every statement that is still open on
the development fork, and from nothing else: the open bundles of the H chain, the manuscript's Theorem 5.3 (the restricted
converse, `ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine`, `diophantine_zq.tex` lines 1005–1011, over the genuine
`Sel_{2^∞}(E_ℓ/ℚ)`), the Cassels–Tate pairing on the curves `E_ℓ` of Theorem 5.3
(`ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves`, the printed input the manuscript cites for its Lemma 5.4 at
`diophantine_zq.tex` L1079–1081; Lemma 5.4 itself is proved from it), the printed leaf BCDT Theorem A
(`ZInQ.Manuscript.PoleS12.BCDTThmA`) and a consequence of Kolyvagin's Theorem 1
(`ZInQ.Manuscript.PoleS12.KolyvaginThm1`, through Shimura's construction and Faltings' isogeny theorem).
Pole completeness PC (`ZInQ.PoleCompleteness`, Theorem 5.2, lines 1001–1004, for the manuscript's pole polynomial) is
proved from these by the manuscript's descent (lines 1019–1121):
`ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing`
(`Contrib/OneProof/CasselsTatePairing.lean`, over `Contrib/OneProof/PoleCompletenessFromRCGenuineFinal.lean`; fork
issue #83), with Lemma 5.4 (`Contrib/OneProof/SelmerCorankFam.lean`, `Contrib/OneProof/Lemma54FromCasselsTate.lean`),
the matrix construction, the local images, the 2-descent, Mordell–Weil for `E_ℓ` and the Kummer identification
`#Sel₂(E_ℓ/ℚ) = #SelM ℓ` proved.
It composes the compiled H chain with the headline
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
(`ZInQKernel/MainGreenTao.lean`: the assembly with route AP, Green–Tao in its dense form and Proposition D proved).

* H: `HDec.HSyn.sixContactMin_of_open18` (`OneProof/H/`) proves `ZInQ.SixContactMin` from the open research leaves
  (`OpenResearchLeaves14`), textbook leaves (`OpenTextbookLeaves10`), added leaves (`OpenAddedLeaves13`) and glue
  (`OpenGlue7`). The modules up to `TailK` are leaf-fold4's chain moved onto the kernel's declarations (op-dedupe,
  op-compact); `TailL`-`TailN` are leaf-fold5's and `TailO` is leaf-fold6's, copied from their olean chains;
  `TailP`-`TailX` are leaf-fold7's (the split tasks av-glue, av-split, curve-split, hodge-split, qm-split, mcr-glue
  folded in; docs/research/leaf-fold7.md); `TailY`-`TailZ4` are leaf-fold8's (height-split, height-glue,
  qm-glue and six cloud-worker Contrib proofs folded in; docs/research/leaf-fold8.md); `TailZ5`-`TailZ9` are leaf-fold9's
  (`r1rec`, `r5` proved from `r1r2`, `r15` from `dsThm966` (modular-split), `r7b`, `r8` from published-form leaves
  (reduct-split), `r5count` from González–Rotger's count on `X₆` (shimura-split), and cloud PR #11's two proofs;
  docs/research/leaf-fold9.md); `TailZ10`-`TailZ15` are leaf-fold10's (dimjac-glue's proof of
  `dimJacobianEqGenus`, `y3Connected` from Deligne's printed theorem (shimura-glue), `r6`, `semistableReductionThm`
  and `semistablePersists` from published-form leaves (reduct-glue); docs/research/leaf-fold10.md); `TailZ16`-`TailZ17`
  are route-a-fold's (r1univ-rigid's Mumford rigidity: the moduli leaves `r1r2`, `shimuraFamily`,
  `gonzalezRotgerCountX6`, `deligneComponentsY3Printed` restated on abelian schemes, as printed, plus the leaf
  `mumfordRigidityCore`; docs/research/route-a-fold.md); `TailZ18`-`TailZ19` are leaf-fold12's (cm24-value's proof of
  `igusaCMValue24`; c-to-printed's `neronLocalizesDVR`, `faltingsLemma5BC`, `semistableNeronBaseChange` from printed
  leaves); `TailZ20`-`TailZ22` are x6-fold's (x6-glue's `r1r2Ab` and `x6ConicModel` from Deligne's, Baba–Granath's,
  González–Rotger's and Elkies' printed theorems, the textbook criterion `GeomConnOfAlgClosure`, T5 and the ray-class
  form of Shimura reciprocity; docs/research/x6-fold.md); `TailZ23` is leaf-fold14's reduct fold (reduct-b's proofs of
  `semistableReductionDVR`, `raynaudSemistable` and of SS1/SS3 from the strictly henselian printed leaves of SGA 7 IX
  4.7 and 3.3 and `StrictHenselizationPair`) and `TailZ24` its t09-pic fold (`t09SymmIsogenyExists` from four printed
  leaves over the Picard functor: representability, `Pic⁰`, `φ_L` an isogeny, Mumford's `ē_n`;
  docs/research/leaf-fold14.md); `TailZ40` is rigid-prune's (TailZ23's conversions use the field
  `mumfordRigidityCore` only as Mumford's GIT Thm 6.14 on QM families, `QMFamilyGroupLaw`, proved from gt-rigidity's
  `MumfordGroupLaw` without Cor. 6.4; docs/research/rigid-prune.md); dcy3-fold removed the added field `deligneComponentsY3PrintedAb`: the chain
  reads it only as `TSHecke.Y3Connected`, now proved by dcy3-used's `DCY3Used.y3Connected_of_leaves` from
  `mumfordGroupLaw` and `shimuraMainThmIDeligneY3AbU` and passed from `sixContactMin_of_open28` down to
  `addedLeaves8_of_open9`; docs/research/dcy3-fold.md); `TailZ41` is leaf-fold30's persists-dvr fold (`sixContactMin_of_open34`; written
  as TailZ40 by leaf-fold30's autofold over rigid-prune's module and moved to TailZ41); pi0-fold removed
  the added fields `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`: they fed only the clause `R1pi0Props` of
  the row `LeafAdopt.R1R2fpRep`, which no consumer reads, so the chain carries the weak row `LeafAdopt.R1R2fpRepW`, whose
  base witness comes from González–Rotger's `GonzalezRotgerX6` (`QMSplit.Moduli.x6Rows_of_leavesW`, TailZ21;
  docs/research/pi0-fold.md).

PC replaces the Route K inputs (lane74, fork issues #77 and #78): the Tian–Yuan–Zhang hypotheses (`h21S`, `h33c`),
Shimura's Theorem 5.4 (`hCM`), Bump–Friedberg–Hoffstein (`hBFH`) and Gross–Zagier (`hGZss`) are no longer hypotheses,
and the files that proved PC for the Route K polynomial from them were removed (they stay reachable at the tag
`route-k-final`). The manuscript proves Theorem 5.2 from its restricted converse Theorem 5.3.

The textbook bundle `OpenTextbookLeaves15` (`TailZ48`) is `OpenTextbookLeaves14` without `homFreeFiniteAlgClosed`: homfree-noemb's
reroute (`Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean`, generated by `scratch/homfree-noemb/gen/gen.py`) copies
the T6 branch with Mumford §19 Thm 3 taken over fields with a ring hom to `ℂ` (`HomFreeC.HomFreeFiniteC`, proved), and
`HDec.HSyn.sixContactMin_of_open41` goes through its `sixContactMin_of_open40_hf` (leaf-fold33).

fold33-copy (sga3-nbhd) removed the research field `sga3_VIB_3_10_Nbhd` by a copy reroute: the research bundle
`OpenResearchLeaves30` (`TailZ49`) is `OpenResearchLeaves29` without it, and `HDec.HSyn.sixContactMin_of_open42` goes
through `sixContactMin_of_open40_hf_ns` (`OneProof/H/NoSGA3Copy.lean`, generated by
`scratch/fold33-copy/gen/gen.py`), a copy of the research chain `OpenResearchLeaves14`-`29` and of every declaration
that takes one of these bundles, without the field and with sga3-nbhd's leaf-free readers. The originals are unchanged.
fold33-copy (goodmodel-iso, fold G) then replaced the research field `mumfordGroupLawConn` and the textbook field
`neronSchemeExtensionExists` by the one printed leaf `neronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over an affine
Dedekind scheme), again by a copy: `OpenResearchLeaves31` and `OpenTextbookLeaves16` (`TailZ50`), and
`HDec.HSyn.sixContactMin_of_open43` goes through `sixContactMin_of_open40_hf_gm` (`OneProof/H/GoodModelIsoCopy.lean`,
the same 65 declarations copied with both folds: `mumfordGroupLaw` narrowed to `MumfordGroupLawDVR`,
`GoodModelIso.mumfordGroupLawDVR_of_dedekind`), with `neronSchemeExtensionExists` supplied by
`GroupLawNeron.neronSchemeExtensionExists_of_dedekind`.

fold33-pic (phisurj) removed the added fields `weilPairingMumford` and `mumfordPhiSurjectiveAC`. The first is proved
(`PhiSurj.weilPairingMumford_of_open`, from L1, L2 and the torsion leaf; autofold, `OpenAddedLeaves21`, `TailZ51`).
The second is not proved but rerouted: its readers only compute `T09Pic.PhiAmpleIsogeny` from it, which is now
`PhiSurj.phiAmpleIsogeny_of_open` (L1, L2, the torsion leaf, a dimension count and the descent half of Mumford §20).
So `OpenAddedLeaves22` (`TailZ52`) is `{picRepresentableAbVar, picZeroAbVar}`, and `HDec.HSyn.sixContactMin_of_open45`
enters the existing chain at the generation `OpenAddedLeaves18` (whose field is `phiAmpleIsogeny`) through
`sixContactMin_of_open37_hf_gm`; no declaration is copied or changed.

fold33-pic (piczero-char0) then replaced the added field `picZeroAbVar` (GLUE, every field), which the proof reads
only in characteristic `0`, by three printed leaves: `OpenAddedLeaves23` (`TailZ53`) is `OpenAddedLeaves22` without it
and with `picLocFinType`, `identityComponentLFT` and `kleimanPicZeroProper`, and `HDec.HSyn.sixContactMin_of_open46`
goes through `sixContactMin_of_open45_pz` (`OneProof/H/PicZeroCharZeroCopy.lean`, generated by
`scratch/fold33-pic/gen/gen.py`), a copy of every declaration that reads the field or takes a bundle carrying it, with
its characteristic-`0` form `PicZeroChar0.PicZeroAbVar0`, proved by `PicZeroChar0.picZeroAbVar0_of_leaves` (Cartier's
theorem, `cartierSmooth_proof`; `Contrib/OneProof/PicZeroAbVarCharZero.lean`), and phisurj's theorems in
characteristic `0` (`Contrib/OneProof/PhiSurjCharZero.lean`). The originals are unchanged.

coeff-field-tc (landed on main by the integrator, regenerated here on TailZ73 with fold-b100's generator, `TailZ74`):
`eigenformCoeffFieldFinite_proof` proves `DSCoeffExt.EigenformCoeffFieldFinite` outright, so `heckePrimeIntegralToRational` and
`gamma1IntegralBasis` leave the research bundle (copy reroute of the live path, originals unchanged).

fold-b105 (fold-chev regenerated, chevalley-free) removed the research field `chevalleyPerfect` (Chevalley over a perfect
field) with no new leaf: the chain read it only through `SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley`,
and `ZInQ.HeightFix.SemiAbelianDescendsPerfect` is proved (`ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`,
`Contrib/OneProof/ChevalleyFree.lean`). `OpenResearchLeaves49` (`TailZ75`) is `OpenResearchLeaves48` without it, and
`HDec.HSyn.sixContactMin_of_open68` enters the coeff-field-tc copy chain at `OpenResearchLeaves36EBCF` through the composite
conversion `openResearchLeaves36EBCF_of_OpenResearchLeaves49` (bypass, generated by `scratch/fold-b105/gen_chev_bypass.py`); no
declaration is copied or changed.

fold-b105 (pb-p1) replaced the research fields `panPrintedP` and `bergerPrintedVT` by `panPrintedF` (Pan,
arXiv:1901.07166v2 Thm 1.0.4) and `bergerSurveyF` (Berger's survey IV.5.1), both over Fontaine's `B_st` as
printed (`Contrib/OneProof/PanBergerFontaine.lean`); `r11r12` follows by `HDec.PkgI4.PanDict.panBerger_of_F`.
`OpenResearchLeaves51` (`TailZ77`) enters the chain at `OpenResearchLeaves36EBCF` through the composite conversion `openResearchLeaves36EBCF_of_OpenResearchLeaves51`
(bypass, generated by `scratch/fold-b105/gen_pbp1_bypass.py`); no declaration is copied or changed.

igusa-drop removed the research field `igusaGL2DSGalSome` (Diamond-Shurman Thm 7.6.3, printed form) with no new
leaf: the chain read it only through `AfTateLam.r16CoreY_of_ds965`, which uses it as `X1PointsConjugate`,
proved from `X0Transitive` (`AfTateLam.r16CoreY_of_ds965_x0`, `Contrib/OneProof/IgusaDrop.lean`).
`OpenResearchLeaves53` (`TailZ79`) is `OpenResearchLeaves52` without it, and `HDec.HSyn.sixContactMin_of_open72` enters the
chain at `OpenResearchLeaves36EBCF` through the composite conversion `openResearchLeaves36EBCF_of_OpenResearchLeaves53` (bypass, generated by
`scratch/igusa-drop/gen_igusa_drop.py`); no declaration is copied or changed.

bost-gr9 (folded by fold-b112) replaced the research field `bostLowerBoundAnSS` (Bost's bound, not cited by the manuscript and
strictly stronger than its citation) by `gaudronRemondSec9LowerAnSS` (Gaudron-Remond, Duke 2014, section 9, `h_F >= -(3/2) dim`, the
manuscript's citation at L894-895, over the printed semistability; `Contrib/OneProof/GaudronRemondSection9.lean`
and `GaudronRemondSection9SS.lean`). `OpenResearchLeaves54` (`TailZ80`) is `OpenResearchLeaves53` with the field replaced, and
`HDec.HSyn.sixContactMin_of_open73` goes through a copy of the 89 declarations of the chain that carry
the field (namespace `HDec.HSyn.GR9`, weaker-leaf bypass, generated by `scratch/fold-b112/gen_gr9_fold.py`); no
existing declaration is changed.

ss-faltings (folded by fold-b115) replaced the research field `sga7_IX_Cor3_3_Def34` (SGA 7 IX Cor. 3.3, not in the
manuscript's bibliography) by `faltingsSemistableHeightBC` (Faltings 1983 §3, p. 354, invariance of the height of a
semiabelian scheme under extension of the base field, read for Néron models: SGA 7 IX Cor. 3.3's content is
named inside this leaf; the manuscript uses it uncited at L596-598); the field of
semistable reduction is proved from Raynaud's criterion over `K(A[15])` (`Contrib/OneProof/SSFaltings.lean`).
`OpenResearchLeaves58` (`TailZ84`) is `OpenResearchLeaves57` with the field replaced, and `HDec.HSyn.sixContactMin_of_open77` goes through
`sixContactMin_of_open76_sf`, a copy of the chain of declarations that carry the field (`OneProof/H/SSFChain.lean`,
generated by `scratch/ss-faltings/gen/gen_chain.py`; bypass); no existing declaration is changed.

d2a6b (folded by fold-b116, chain and bypass regenerated on the post-ss-faltings top) replaced the research field
`sga7_IX_3_5_ForwardGeom_Def34` (SGA 7 IX 3.5, not in the manuscript's bibliography) by `elliotWildInertiaTrivial`
(the manuscript's uncited sentence L817-818); D2 now goes through Raynaud's criterion as cited at L816
(`silverbergZarhinThm35`), and A6 and the kernel field's good reduction (L529-530) through the model of `Y₃` over
ℤ[1/30] (`y3FullThreeRepZ30`; `Contrib/OneProof/A6Z30.lean`, `D2A6Wrap.lean`). `OpenResearchLeaves59` (`TailZ85`) is `OpenResearchLeaves58`
with the field replaced, and `HDec.HSyn.sixContactMin_of_open78` goes through `sixContactMin_of_open73_sf_u`, a copy of the
chain of declarations of `sixContactMin_of_open73_sf` (ss-faltings' chain) that carry the field
(`OneProof/H/D2A6Chain.lean`, generated by `scratch/fold-b116/gen-d2a6b/gen_chain.py`; bypass); no existing
declaration is changed. No SGA 7 statement remains a field.

The joint C8 fold (fold-c8: c8-conrad3, conrad-b3, ht-merge with derham-scholze and ht-abvar, and PR #86) removed the
added fields `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` and the research field `hodgeTateDecompOr`,
and added `conradAppB` (Conrad App. B p. 32 and Prop. B.3, the manuscript's citation at L760-762),
`scholzeH1AbVar` (Scholze 2013 with the Hodge numbers of `H¹`, lem:de-rham-descent) and `t10TateDuality` (Milne):
step C8 now follows the manuscript (`C8Conrad.g12DetPZ_of_inputs`, `Contrib/OneProof/C8*.lean`), Poincaré's
complete reducibility is proved (`ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof`), and
`hodgeTateDecompAbVar` comes from Scholze and Milne (`DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1`).
`OpenResearchLeaves61` and `OpenAddedLeaves28` (`TailZ87`) are the new generations, and `HDec.HSyn.sixContactMin_of_open80` goes through
`sixContactMin_of_open79_hm`, a copy of the chain of declarations that read the Weil-pairing fields of step C8
(`OneProof/H/C8Chain.lean`, generated by `scratch/fold-c8/fold_c8.py`; copy reroute); no existing declaration
is changed.

fold-cm (the CM-branch package, cm-branch, cm-branch2, cox-lattice and cm-fold-rebase; Jack's ruling, verbatim: "Fold now
at +4 (Recommended)") replaced the base of the chain, NoCM (FS5, from González–Rotger's Thm 5.12 on `X₆`, its count and the
`X₆` Kummer fibre), by the manuscript's CM branch (L581-631): the research field `gonzalezRotgerThm512X6RCF` is no longer
read, and the CM-branch inputs `cmFibreSplit` (glue), `fowlerProp27`, `cmjDegree`, `cmPotentialGood` and `cmHeight62`
(leaves pending review) are fields. `OpenResearchLeaves62` (`TailZ88`) is the new generation, and
`HDec.HSyn.sixContactMin_of_open81` goes through the chain of `sixContactMin_of_open80` with the CM inputs threaded and the
CM branch at its base (`Contrib/OneProof/CMBranchUC8.lean`, `OneProof/H/CMTopLive.lean`), the moduli row carried in its
weak form (`R5ptProps` as `True`, `OneProof/H/CMR5*.lean`) and the bundles without the field (`OneProof/H/CMOpen.lean`);
generated by `scratch/fold-cm/gen/`; copy reroute; no existing declaration is changed.
Its second component (y3-x6b, with y3-p1j and y3-x6) replaced the `X₆` witness of the moduli row by the row over
`Y₃` (`Y3X6.R1R2fpY3`, L411-526): the research fields `x6CoarseModuliIdeal` and `elkiesX6StarEveryIdeal` are no longer
read, and `y3ToP1j` (the manuscript's map `Y₃ → P¹_j`, L420-440; leaf pending review) and `heckeSqrtBranchAny` (glue,
formerly derived from Elkies' model of `X₆`; its `Y₃`-only argument is on the spot) are fields. `OpenResearchLeaves63`
(`TailZ89`) is the new generation, and `HDec.HSyn.sixContactMin_of_open82` goes through `OneProof/H/Y3Copy*.lean` and
`OneProof/H/Y3Open.lean` (generated by `scratch/fold-cm/gen/`; copy reroute).

hecke-sqrt proved `heckeSqrtBranchAny` from `y3ToP1j` (`SGRDirect.heckeSqrtBranchAny_proof`; autofold, `TailZ90`,
`OpenResearchLeaves64`, `HDec.HSyn.sixContactMin_of_open83`). nos-narrow removed `neronOggShafarevichSep` with no
replacement: its two live readers (the kernel field, L557-560, and A6, L752-753) read only good reduction ⇒ inertia
fixes prime-to-p torsion, which is proved (`NOSNarrow.nosForward_proof`). `OpenResearchLeaves65` (`TailZ91`) is the new
generation, and `HDec.HSyn.sixContactMin_of_open84` goes through `sixContactMin_of_open83_nos`, the chain of
`sixContactMin_of_open83` with the field omitted (`Contrib/OneProof/NOSNarrowChain.lean`, generated by
`scratch/nos-narrow-fold/gen_chain.py`; readers in `Contrib/OneProof/NOSNarrow.lean` and `NOSNarrowNC.lean`; copy
reroute); no existing declaration is changed.
Fork PR #106 and cm-port2 removed `deRhamVpAbVarDirect` (derived from the added fields `scholzeH1AbVar` and
`t10TateDuality` by `DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne`, the manuscript's
lem:de-rham-descent route) and `cmFibreSplit` (cm-curve-order's proof on the live route,
`HDec.CMBranch.FibreSplit.cmFibreSplit_of_liveInputs_nos`, from six research fields, with nos-narrow's forward
implication in place of the removed NOS field). `OpenResearchLeaves66` (`TailZ92`, autofold) is the new generation and
`HDec.HSyn.sixContactMin_of_open85` the new top.
faltings-dict2 (with faltings-dict and faltings-restate) replaced `faltingsSemistableHeightBC` by Faltings' Lemma 1 as
printed (`faltingsLemma1DVRPrint`, Invent. Math. 73 (1983) p. 350; leaf, rated LEAF): the field is
`ZInQ.FaltingsRestate.faltingsSemistableHeightBC_of_faltingsLemma1Print` from the leaf, `silverbergZarhinThm35` and
`neronSchemeExtensionDedekind`. `OpenResearchLeaves67` (`TailZ93`, autofold) is the new generation and
`HDec.HSyn.sixContactMin_of_open86` the new top.

The hypotheses of `frozenTarget` are therefore exactly the open statements. Discharging one means replacing a field or
hypothesis by its proof; the theorem's statement then loses that hypothesis.
-/

namespace ZInQ.OneProof

/-- **Theorem 1.1, from every statement still open:** the open H bundles, the manuscript's Theorem 5.3 (the restricted
converse, the manuscript's own theorem (not a printed leaf)), the Cassels–Tate pairing on the curves `E_ℓ`, the printed
leaf BCDT Theorem A and a consequence of Kolyvagin's Theorem 1 (through Shimura's construction and Faltings' isogeny theorem). Pole
completeness PC (the manuscript's Theorem 5.2) is proved from the last four, with Lemma 5.4 proved from the pairing
(`ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing`). -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves69) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves) (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open90 r t l)
    (ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTatePairing hRC hCT hB hK)

end ZInQ.OneProof

#print axioms ZInQ.OneProof.frozenTarget
