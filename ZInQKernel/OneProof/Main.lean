import ZInQKernel.OneProof.H.TailZ56
import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.OneProof.TopChain
import ZInQKernel.Contrib.TYZChain.Main
import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.OneProof.TYZLemma29Mod2
import ZInQKernel.Contrib.OneProof.FHNonvanishing
import ZInQKernel.Contrib.OneProof.BFHGamma0
import ZInQKernel.Contrib.OneProof.LegendreThreeSquares
import ZInQKernel.Contrib.OneProof.TYZThm21At31
import ZInQKernel.Contrib.OneProof.JonesPall
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd
import ZInQKernel.Contrib.OneProof.GrossConjugationCd
import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic
import ZInQKernel.Contrib.OneProof.EtaW32Character
import ZInQKernel.Contrib.OneProof.TYZTestVectorExists
import ZInQKernel.Contrib.OneProof.Gamma0QExpansion
import ZInQKernel.Contrib.OneProof.TYZProp23Printed
import ZInQKernel.Contrib.OneProof.ShimuraMainCM

/-!
# The whole proof in one theorem

`ZInQ.OneProof.frozenTarget` derives the frozen target `ZInQ.FrozenTarget` from every statement that is still open on
the development fork, and from nothing else. It composes three compiled chains:

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
* TYZ: `ZInQ.Contrib.TYZChain.tyzThm35ReadingA_of_leaves` proves reading A of Tian–Yuan–Zhang from four leaves; the
  fourth, tyz-35's pinned form of TYZ Theorem 3.3, is derived from TYZ Theorem 3.3 in its printed form
  (`ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33`, `OneProof/TYZSplit.lean`, task tyz-split), and the
  third, Shimura reciprocity for modular functions, from `T5Glue.ShimuraMainCM` alone: every use is at level 32 for
  the coordinates x, y of the eta-quotient model of X0(N), where the eta route with the proved identity
  `ThetaWeierstrass8` replaces the canonical-model hypothesis on X0(N) (`ThetaWP8.tyzThm35ReadingA_noHX`,
  `Contrib/OneProof/ThetaWeierstrass8.lean`, tasks hx-used and theta-wp8).
* GZ and assembly: `ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` proves `ZInQ.FrozenTarget`
  from H, reading A and the two open Gross–Zagier statements, with `HeckeThetaNewform` proved
  (`OneProof/TopChain.lean`) and Hecke's continuation and the functional equation proved
  (`ZInQ.Contrib.heckeContinuation`, `ZInQ.Contrib.functionalEquation5`). Gross–Zagier enters only for the curves
  `C_d` (route A, leaf-fold33): `ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`
  with heegner-32's `grossZagierHeegnerCd_of_printed` (from `T5Glue.ShimuraMainCM`, which hcm-dict's
  `HCMDict.shimuraMainCM_of_printed` derives from Shimura 1971 Thm 5.4 as printed, the binder `hCM`), gz-conj's proved conjugation relation, and
  `GZAlg.grossZagierFormulaCd_of_alg` (gzopt-dict, through period-odd and cd-optimal) from Gross–Zagier over the
  algebraic curve `X₀(N)` (`hGZ`), the `q`-expansion principle for `Γ₀(N)` (proved: gamma0-qexp,
  `Gamma0QExp.gamma0QExpansion_proof`) and the eta-quotient law at level 32 (proved: etaw32-proof,
  `EtaW32Character.etaW32Character_proof`). TYZ's test vector `hfx` is proved (hfx-proof, `HfxProof.tyzTestVectorExists`), and so is TYZ Proposition 2.3
  `hP23` (hp23-proof, `HP23Proof.tyzProp23Printed`).

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

The hypotheses of `frozenTarget` are therefore exactly the open statements. Discharging one means replacing a field or
hypothesis by its proof; the theorem's statement then loses that hypothesis.
-/

namespace ZInQ.Contrib.TYZChain

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus

/-- **Theorem 1.1, from every statement still open.** -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves31) (t : HDec.HSyn.OpenTextbookLeaves17) (l : HDec.HSyn.OpenAddedLeaves25)
    (h11 : TYZThm11Integral)
    (hL29 : H29Split.TYZLemma29PrintedNe3)
    (hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hBFH : ZInQ.BFHPrinted.BFHClauseIIGamma0)
    (hGZ : ZInQ.GZAlg.GrossZagierAlgOptCd) :
    ZInQ.FrozenTarget :=
  ZInQ.GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd
    (HDec.HSyn.sixContactMin_of_open49 r t l)
    (ThetaWP8.tyzThm35ReadingA_noHX h11 (H29Split.tyzLemma29Mod2_of_sixLeaves ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
      ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof ZInQ.Contrib.HfxProof.tyzTestVectorExists hL29 ZInQ.Contrib.T21Proof.tyzThm21At31
      ZInQ.Contrib.HP23Proof.tyzProp23Printed) (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) h33)
    (ZInQ.GZStatements.fhNonvanishingCd_of_fhNonvanishing (ZInQ.BFHPrinted.fhNonvanishing_of_bfhClauseIIGamma0 hBFH))
    (ZInQ.Heegner32.grossZagierHeegnerCd_of_printed (ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM) (ZInQ.GZAlg.grossZagierFormulaCd_of_alg hGZ ZInQ.Contrib.Gamma0QExp.gamma0QExpansion_proof
      ZInQ.Contrib.OneProof.EtaW32Character.etaW32Character_proof)
      ZInQ.GZConj.grossConjugationCd)

end ZInQ.Contrib.TYZChain

#print axioms ZInQ.OneProof.frozenTarget
