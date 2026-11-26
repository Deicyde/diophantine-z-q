import ZInQKernel.Contrib.OneProof.DS965Reroute.PanBerger
import ZInQKernel.OneProof.H.TailZ103

/-! # The live chain without `dsThm965AtPrimes` (part 1 of 5; ds965-reroute, generated)

Generated from `NOSNarrowChain.lean` and the generations `TailZ91`–`TailZ103`: every declaration
that takes a bundle carrying a Diamond–Shurman 9.6.5 field, `R14Det` or `GaloisPiecesC8` is copied
with the suffix `DS` / `_ds`. Below the conversion that reads `modularHTCoeff`, the 9.6.5 field is
replaced by `repExists` (R14 without its determinant, from `modularHTCoeff` and
`dsThm966Printed`); above it, it is deleted. `r14` carries `EigenformRepExists` and
`GaloisPiecesC8DS` has no `r14det` (neither determinant is read on this route). The originals are
unchanged.
-/

set_option linter.style.haveILetI false

-- copied from ZInQKernel/OneProof/H/C8Chain.lean:29 (GaloisPiecesC8), without `r14det`
namespace HDec
namespace G0Galois
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe
noncomputable section
/-- ds965-reroute: `GaloisPiecesC8DS` without its field `r14det` (read by no declaration
on this route). The pieces of the range G8-G12 that are not in the leaf bundles: Burnside (a
textbook leaf;
`G8Matrix` is proved from it, `g8Matrix_of_burnside`), R14's determinant clause (a leaf, R14 as
published), and the named glue `G9Glue`, `G10Glue`, `G12Weight`, `DetTate`, `ResQFiniteIndex`
(`G12Det` is proved from the last two, R14Det and T18, `g12Det_of`). -/
structure GaloisPiecesC8DS : Prop where
  burnside : BurnsideAbsIrred
  deRham : G9Glue
  odd : G10Glue
  weight : G12Weight
  /-- c8-conrad2: the inputs of step C8 by local algebraicity (`C8Conrad.C8Inputs`: Conrad's App.
    B and the
  glue), replacing this generation's Weil-pairing fields (`t09SymmIsogenyExists` /
  `phiAmpleIsogeny`,
  `weilPairingMumford` / `detTate`), which only fed `DetTate` at C8. -/
  c8 : _root_.HDec.G0Galois.C8Conrad.C8Inputs
  finIndex : ResQFiniteIndex
end
end G0Galois
end HDec


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1471
-- (_root_.HDec.HSyn.OpenResearchLeaves2EBU_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
-- op-dedupe
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny
    Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen
    Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale
    Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0
    Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective
    Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap
    Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer
    Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit
    Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap
    Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section
    Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit
    Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent
    Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale
    Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified
    Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified'
    Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen
    Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale
    Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin
    Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo
    Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC (G0FibreSimple.MulIsogeny MulRigidity.CotangentMulN
    MulRigidity.KerUnitOpen MulRigidity.KerUnitOpenOfCotangentSurj MulRigidity.MulEtale
    MulRigidity.MulUnramified MulRigidity.O0 MulRigidity.QuasiFiniteEndSurjective
    MulRigidity.charZero_residueField MulRigidity.cotangentMap MulRigidity.diagonal_isPullback
    MulRigidity.diffKer MulRigidity.formallyUnramified_of_kerUnit
    MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap MulRigidity.isOpenImmersion_of_section
    MulRigidity.isProper_left MulRigidity.kerUnit MulRigidity.kerUnitOpen_of_cotangent
    MulRigidity.kerUnitOpen_of_mulEtale MulRigidity.locallyQuasiFinite_of_formallyUnramified
    MulRigidity.map_origin MulRigidity.mulIsogeny_of_cotangent
    MulRigidity.mulIsogeny_of_kerUnitOpen MulRigidity.mulIsogeny_of_mulEtale
    MulRigidity.mulIsogeny_of_mulUnramified MulRigidity.mulIsogeny_of_mulUnramified'
    MulRigidity.mulUnramified_of_kerUnitOpen MulRigidity.mulUnramified_of_mulEtale
    MulRigidity.ne_of_specializes_of_lqf MulRigidity.origin MulRigidity.quasiFiniteEndSurjective
    MulRigidity.stalkEndo MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib (AbVarBC.G0FibreSimple.MulIsogeny AbVarBC.MulRigidity.CotangentMulN
    AbVarBC.MulRigidity.KerUnitOpen AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj
    AbVarBC.MulRigidity.MulEtale AbVarBC.MulRigidity.MulUnramified AbVarBC.MulRigidity.O0
    AbVarBC.MulRigidity.QuasiFiniteEndSurjective AbVarBC.MulRigidity.charZero_residueField
    AbVarBC.MulRigidity.cotangentMap AbVarBC.MulRigidity.diagonal_isPullback
    AbVarBC.MulRigidity.diffKer AbVarBC.MulRigidity.formallyUnramified_of_kerUnit
    AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap
    AbVarBC.MulRigidity.isOpenImmersion_of_section AbVarBC.MulRigidity.isProper_left
    AbVarBC.MulRigidity.kerUnit AbVarBC.MulRigidity.kerUnitOpen_of_cotangent
    AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale
    AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified AbVarBC.MulRigidity.map_origin
    AbVarBC.MulRigidity.mulIsogeny_of_cotangent AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen
    AbVarBC.MulRigidity.mulIsogeny_of_mulEtale AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified
    AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified'
    AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen AbVarBC.MulRigidity.mulUnramified_of_mulEtale
    AbVarBC.MulRigidity.ne_of_specializes_of_lqf AbVarBC.MulRigidity.origin
    AbVarBC.MulRigidity.quasiFiniteEndSurjective AbVarBC.MulRigidity.stalkEndo
    AbVarBC.MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC.MulRigidity (CotangentMulN KerUnitOpen KerUnitOpenOfCotangentSurj
    MulEtale MulUnramified O0 QuasiFiniteEndSurjective charZero_residueField cotangentMap
    diagonal_isPullback diffKer formallyUnramified_of_kerUnit isIsogenyMor_of_lqf_of_isOpenMap
    isOpenImmersion_of_section isProper_left kerUnit kerUnitOpen_of_cotangent
    kerUnitOpen_of_mulEtale locallyQuasiFinite_of_formallyUnramified map_origin
    mulIsogeny_of_cotangent mulIsogeny_of_kerUnitOpen mulIsogeny_of_mulEtale
    mulIsogeny_of_mulUnramified mulIsogeny_of_mulUnramified' mulUnramified_of_kerUnitOpen
    mulUnramified_of_mulEtale ne_of_specializes_of_lqf origin quasiFiniteEndSurjective stalkEndo
    surjective_of_lqf_self)
open _root_.ZInQ.Contrib.AbVarBC.G0FibreSimple (MulIsogeny) -- op-dedupe
open CategoryTheory AlgebraicGeometry G0Split
/-- **The research-level leaves still open** (leaf-fold2).
  `_root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS` (g0-assemble2: no
`opaque` placeholder) with four fields in their published, corrected or concrete form:
* `r1b`: R1(b) concretely, in family form (fibre-qm-period's `R1bFamily`; was
`GluePieces3.r1bFamily`
  and, before that, the `opaque` `r1an`);
* `r10`: R10 corrected (`PkgI4.DeRhamComparisonHT`, with the multiplicity-0 clause; g9-derham,
  r10-amend);
* `r14`: R14 corrected (`G0Galois.R14Det`, with the determinant clause; was also
  `GluePieces3.r14Det`);
* `r17`: R17 concretely (`LadicCond.CarayolR17'`, Carayol 1986 Thm (A); was
  `GluePieces3.carayolR17` and, before that, the `opaque` `r17`). -/
structure _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS : Prop where
  r1r2 : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c,
    G0Split.FibreQM.R1bFamily (_root_.HDec.HSyn.G0Split.FibreQM.ownY_y3c
        (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
      (_root_.HDec.HSyn.G0Split.FibreQM.ownΦ_y3c (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
      (_root_.HDec.HSyn.G0Split.FibreQM.ownπ_y3c (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
  r1rec : LeafQM.AV.R1rec
  r4 : PkgI1.ThetaModularity
  r5 : True
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  r5count : _root_.GR56.R5fpCountLe
  r6 : _root_.HDec.D2A6.R6U
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 without its determinant (ds965-reroute: the determinant clause of `R14Det` is not read
    on this route). -/
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1522
-- (_root_.HDec.HSyn.researchLeaves3_of_open2_eb_u_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
-- op-dedupe
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny
    Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen
    Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale
    Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0
    Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective
    Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap
    Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer
    Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit
    Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap
    Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section
    Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit
    Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent
    Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale
    Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified
    Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified
    Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified'
    Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen
    Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale
    Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin
    Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo
    Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC (G0FibreSimple.MulIsogeny MulRigidity.CotangentMulN
    MulRigidity.KerUnitOpen MulRigidity.KerUnitOpenOfCotangentSurj MulRigidity.MulEtale
    MulRigidity.MulUnramified MulRigidity.O0 MulRigidity.QuasiFiniteEndSurjective
    MulRigidity.charZero_residueField MulRigidity.cotangentMap MulRigidity.diagonal_isPullback
    MulRigidity.diffKer MulRigidity.formallyUnramified_of_kerUnit
    MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap MulRigidity.isOpenImmersion_of_section
    MulRigidity.isProper_left MulRigidity.kerUnit MulRigidity.kerUnitOpen_of_cotangent
    MulRigidity.kerUnitOpen_of_mulEtale MulRigidity.locallyQuasiFinite_of_formallyUnramified
    MulRigidity.map_origin MulRigidity.mulIsogeny_of_cotangent
    MulRigidity.mulIsogeny_of_kerUnitOpen MulRigidity.mulIsogeny_of_mulEtale
    MulRigidity.mulIsogeny_of_mulUnramified MulRigidity.mulIsogeny_of_mulUnramified'
    MulRigidity.mulUnramified_of_kerUnitOpen MulRigidity.mulUnramified_of_mulEtale
    MulRigidity.ne_of_specializes_of_lqf MulRigidity.origin MulRigidity.quasiFiniteEndSurjective
    MulRigidity.stalkEndo MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib (AbVarBC.G0FibreSimple.MulIsogeny AbVarBC.MulRigidity.CotangentMulN
    AbVarBC.MulRigidity.KerUnitOpen AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj
    AbVarBC.MulRigidity.MulEtale AbVarBC.MulRigidity.MulUnramified AbVarBC.MulRigidity.O0
    AbVarBC.MulRigidity.QuasiFiniteEndSurjective AbVarBC.MulRigidity.charZero_residueField
    AbVarBC.MulRigidity.cotangentMap AbVarBC.MulRigidity.diagonal_isPullback
    AbVarBC.MulRigidity.diffKer AbVarBC.MulRigidity.formallyUnramified_of_kerUnit
    AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap
    AbVarBC.MulRigidity.isOpenImmersion_of_section AbVarBC.MulRigidity.isProper_left
    AbVarBC.MulRigidity.kerUnit AbVarBC.MulRigidity.kerUnitOpen_of_cotangent
    AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale
    AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified AbVarBC.MulRigidity.map_origin
    AbVarBC.MulRigidity.mulIsogeny_of_cotangent AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen
    AbVarBC.MulRigidity.mulIsogeny_of_mulEtale AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified
    AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified'
    AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen AbVarBC.MulRigidity.mulUnramified_of_mulEtale
    AbVarBC.MulRigidity.ne_of_specializes_of_lqf AbVarBC.MulRigidity.origin
    AbVarBC.MulRigidity.quasiFiniteEndSurjective AbVarBC.MulRigidity.stalkEndo
    AbVarBC.MulRigidity.surjective_of_lqf_self)
-- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC.MulRigidity (CotangentMulN KerUnitOpen KerUnitOpenOfCotangentSurj
    MulEtale MulUnramified O0 QuasiFiniteEndSurjective charZero_residueField cotangentMap
    diagonal_isPullback diffKer formallyUnramified_of_kerUnit isIsogenyMor_of_lqf_of_isOpenMap
    isOpenImmersion_of_section isProper_left kerUnit kerUnitOpen_of_cotangent
    kerUnitOpen_of_mulEtale locallyQuasiFinite_of_formallyUnramified map_origin
    mulIsogeny_of_cotangent mulIsogeny_of_kerUnitOpen mulIsogeny_of_mulEtale
    mulIsogeny_of_mulUnramified mulIsogeny_of_mulUnramified' mulUnramified_of_kerUnitOpen
    mulUnramified_of_mulEtale ne_of_specializes_of_lqf origin quasiFiniteEndSurjective stalkEndo
    surjective_of_lqf_self)
open _root_.ZInQ.Contrib.AbVarBC.G0FibreSimple (MulIsogeny) -- op-dedupe
open CategoryTheory AlgebraicGeometry G0Split
theorem _root_.HDec.HSyn.researchLeaves3_of_open2_eb_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS) : _root_.HDec.HSyn.ResearchLeaves3EBU_y3cNOS
    where
  r1r2 := r.r1r2
  r1rec := r.r1rec
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := r.r14
  r15 := r.r15
  r16 := r.r16
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1559
-- (_root_.HDec.HSyn.OpenResearchLeaves5EBU_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
/-- **The research leaves still open** (leaf-fold5): leaf-fold2's
  `_root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS` with nine fields
restated over the kernel's own Props (`ZInQKernel/HDecomp/Objects.lean`; the chain's are copies;
part e40 derives
the chain's from the kernel's): `r3` (LeafPush2), `r6`, `r7a`, `r7b`, `r8` (PkgI2), `r9a`, `r9b`
(PkgI3), `r16` (ModCurves), `r17` (LadicCond). Same
statements. -/
structure _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS : Prop where
  r1r2 : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c,
    G0Split.FibreQM.R1bFamily (_root_.HDec.HSyn.G0Split.FibreQM.ownY_y3c
        (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
      (_root_.HDec.HSyn.G0Split.FibreQM.ownΦ_y3c (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
      (_root_.HDec.HSyn.G0Split.FibreQM.ownπ_y3c (_root_.HDec.LeafAdopt.R1R2fp_of_rep_y3c h))
  r1rec : LeafQM.AV.R1rec
  r4 : PkgI1.ThetaModularity
  r5 : True
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  r5count : _root_.GR56.R5fpCountLe
  r6 : _root_.HDec.D2A6.R6U
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 without its determinant (ds965-reroute: the determinant clause of `R14Det` is not read
    on this route). -/
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : _root_.LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1606
-- (_root_.HDec.HSyn.researchLeaves2_of_open5_eb_u_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
/-- leaf-fold2's research bundle from leaf-fold5's. -/
theorem _root_.HDec.HSyn.researchLeaves2_of_open5_eb_u_y3c_nos_ds (r :
    _root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS) :
    _root_.HDec.HSyn.OpenResearchLeaves2EBU_y3cNOSDS where
  r1r2 := r.r1r2
  r1b := r.r1b
  r1rec := r.r1rec
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r9a := faltingsSemisimple_ofK5 r.r9a
  r9b := faltingsTate_ofK5 r.r9b
  r10 := r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := r.r14
  r15 := r.r15
  r16 := eichlerShimuraJ1_ofK5 r.r16
  r17 := carayolR17_ofK5 r.r17
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1645
-- (_root_.HDec.HSyn.OpenResearchLeaves7EBU_y3c))
noncomputable section
namespace HDec.HSyn
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The research leaves still open** (leaf-fold7): leaf-fold5's
  `_root_.HDec.HSyn.OpenResearchLeaves5EBU_y3cNOSDS` with `r4` replaced by
Igusa's two modularity statements, `r1b` by `ShimuraFamily` (qm-split) and `r14` by
Diamond–Shurman's two theorems
(hodge-split), and `r10` by the Hodge–Tate decomposition and the de Rham property of `H¹_ét`
(hodge-split, with
Tate's two theorems from the added bundle). 29 fields. -/
structure _root_.HDec.HSyn.OpenResearchLeaves7EBU_y3cNOSDS : Prop where
  r1r2 : _root_.HDec.LeafAdopt.R1R2fpRepW_y3c
  /-- qm-split, H-20: Shimura 1967 Main Thm I on one fine witness, for every map `π : Y → P¹`
    (replaces `r1b`). -/
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  /-- qm-split, H-2: Igusa's `ψ₄` is a Siegel modular form of weight 4 (with `igusaChi10`,
    replaces `r4`). -/
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  /-- qm-split, H-2: Igusa's `χ₁₀` is a Siegel modular form of weight 10. -/
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : True
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  r5count : _root_.GR56.R5fpCountLe
  r6 : _root_.HDec.D2A6.R6U
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- hodge-split, H-8: the Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g` (Fontaine
    1982; Tate 1967;
  Faltings 1988; with `deRhamH1AbVarT` and Tate's two theorems, replaces `r10`). -/
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  /-- hodge-split, H-8: `H¹_ét(A_F̄, ℚ_p) = Hom(V_p A, ℚ_p)` is de Rham (Faltings 1989; Tsuji
    1999; Scholze 2013
  Cor. 1.8). -/
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  /-- hodge-split, H-10: Kato's theorem for newforms, transported to any semisimple attached `ρ`
    and dualized
  (replaces `r13`, which is the same for all normalized eigenforms; not a leaf: Kato's `V_f` is
  not definable). -/
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- hodge-split, H-22: Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514 (`k = 1`). -/
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5fin : ZInQ.DefFaltings.StableHeightFinite
end HDec.HSyn
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy3.lean:1750
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `OpenResearchLeaves34EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and
  `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright).
  -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}
    (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place
    lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q ->
    GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with
    arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l
    is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l,
    absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and
    isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de
    Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by
    h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's
    B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4),
    read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:27
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `OpenResearchLeaves33EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and
  `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright).
  -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}
    (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place
    lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q ->
    GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with
    arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l
    is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l,
    absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and
    isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:88
-- (_root_.HDec.HSyn.GR9.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `openResearchLeaves33_of_OpenResearchLeaves34_eb`, copied from `EichlerBoundCopy` with the
  coeff-field-tc edits. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOSDS) (t : OpenTextbookLeaves16) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := _root_.DeRhamPrint.deRhamH1AbVarT_of_leaves n.deRhamVpAbVarPrinted
      n.bdRInvariantsPrinted t.mumfordTorsionAlgClosed
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  y3row := n.y3row
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  repExists := n.repExists
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:129
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `OpenResearchLeaves32EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and
  `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright).
  -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:189
-- (_root_.HDec.HSyn.GR9.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `openResearchLeaves32_of_OpenResearchLeaves33_eb`, copied from `EichlerBoundCopy` with the
  coeff-field-tc edits. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := _root_.CarayolPrinted.carayolR17'_of_printed n.carayolThmA
      (_root_.eigenformCoeffFieldFinite_proof)
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  y3row := n.y3row
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  repExists := n.repExists
  dsThm966Printed := n.dsThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:231
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `OpenResearchLeaves30` with `mumfordGroupLawConn` replaced by `neronSchemeExtensionDedekind`
  (fold33-copy,
goodmodel-iso). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS
    Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke
    stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS
    9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:293
-- (_root_.HDec.HSyn.GR9.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `openResearchLeaves31_of_OpenResearchLeaves32_eb`, copied from `EichlerBoundCopy` with the
  coeff-field-tc edits. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  y3row := n.y3row
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  repExists := n.repExists
  eigenformCoeffFieldFinite := _root_.eigenformCoeffFieldFinite_proof
  dsThm966Printed := n.dsThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:335
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS` without `blr_7_2_1` (leaf-fold33).
  -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` not copied (its readers no longer need
  -- SGA 3 VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS
    Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke
    stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS
    9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:399
-- (_root_.HDec.HSyn.GR9.openResearchLeaves29GM_of_OpenResearchLeaves31_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOSDS` (fold33-copy's copy of
  `OpenResearchLeaves29` with both folds) from
`_root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOSDS`, field by field. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves29GM_of_OpenResearchLeaves31_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  y3row := n.y3row
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  repExists := n.repExists
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:441
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS` without `sga7_IX_3_3_SH`,
  `raynaudSemistableSH`, `mumfordGroupLaw`, `neronBaseChangeStrictHenselization`, `r7a`,
  `dsThm965Weak`, `dsThm966`, with the leaves `sga7_IX_3_3_SHpre`, `raynaudSemistableSHOr`,
  `mumfordGroupLawConn`, `blr_7_2_1`, `neronOggShafarevichSep`, `dsThm965Printed`,
  `eigenformCoeffFieldFinite`, `dsThm966Printed` (leaf-fold32-dict). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` not copied (its readers no longer need
  -- SGA 3 VI_B 3.10)
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I
    Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the
    disjunction of semistability over k(s) (general torus) and on the geometric special fibre.
    With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH.
    -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4
    Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over
    a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso
    proved) and the textbook field neronSchemeExtensionExists (its case D = O_L,
    neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- dict-models, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 7.2 Thm 1 (numbers and
    hypotheses UNVERIFIED): Neron models commute with base change along an extension of DVRs of
    ramification index 1 with separable residue extension (here K'/K separable algebraic, A an
    abelian variety: specializations). The specialization to strictly henselian O1 is the old
    field, with no pinning of O^sh (EGA IV 18.8.8 not needed). Replaces
    neronBaseChangeStrictHenselization. -/
  blr_7_2_1 : _root_.DictModels.NeronBLR72.BLR_7_2_1
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS
    Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke
    stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS
    9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with
    (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that
    is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti
    EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with
    finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue
    p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and
    eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in
    DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:506
-- (_root_.HDec.HSyn.GR9.openResearchLeaves28_of_OpenResearchLeaves29_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOSDS`: `blr_7_2_1` by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves28_of_OpenResearchLeaves29_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  y3row := n.y3row
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  blr_7_2_1 := _root_.NeronSH.neronBaseChangeUnramifiedDVR_proof
  repExists := n.repExists
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:549
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS` without `sga3_VIB_3_10`, with the
  leaves `sga3_VIB_3_10_Nbhd` (leaf-fold32). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:620
-- (_root_.HDec.HSyn.GR9.openResearchLeaves27_of_OpenResearchLeaves28_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS`: `sga7_IX_3_3_SH`,
  `raynaudSemistableSH`, `mumfordGroupLaw`, `neronBaseChangeStrictHenselization`, `r7a`,
  `dsThm965Weak`, `dsThm966` by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves27_of_OpenResearchLeaves28_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := _root_.DSThm966EV.dsThm966_of_printed n.dsThm966Printed
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := _root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind
      n.neronSchemeExtensionDedekind
  y3row := n.y3row
  raynaudSemistableSH := _root_.DictModels.RaynaudOr.raynaudSemistableSH_of_or
      n.raynaudSemistableSHOr _root_.geomConnOfRationalPoint_proof
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization :=
      _root_.DictModels.NeronBLR72.neronBaseChangeStrictHenselization_of_BLR72 n.blr_7_2_1
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  repExists := n.repExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:662
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS` without `semistablePersistsSHcp`
  (persists-dvr). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:734
-- (_root_.HDec.HSyn.GR9.openResearchLeaves26_of_OpenResearchLeaves27_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS`: `sga3_VIB_3_10` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves26_of_OpenResearchLeaves27_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  repExists := n.repExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:776
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS` without `dsThm965`, with the
  leaves `dsThm965Weak` (ds965-weak). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:848
-- (_root_.HDec.HSyn.GR9.openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS`: `semistablePersistsSHcp` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb_sf_u_y3c_nos_ds
    (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
  repExists := n.repExists
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:890
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS` without `babaGranathRationalAb`
  (leaf-fold29). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:961
-- (_root_.HDec.HSyn.GR9.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS`: `dsThm965` by the contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1003
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS` without `elkiesX6StarPrinted`,
  with the leaves `elkiesX6StarFunctionField` (elkies-coord-fold). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1074
-- (_root_.HDec.HSyn.GR9.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS`: `babaGranathRationalAb` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb_sf_u_y3c_nos_ds
    (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOSDS) (t : OpenTextbookLeaves11HF) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  heckeSqrtY3 := n.heckeSqrtY3
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1116
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS` without `r16`, with the leaves
  `r16CoreY` (r16-split). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16;
    R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N):
    [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A =
    [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of
    V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from
    dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4):
    R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which
    has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1)
    comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1187
-- (_root_.HDec.HSyn.GR9.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_sf_u_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS` from
  `_root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS`: `elkiesX6StarPrinted` by the
  contributions. -/
theorem _root_.HDec.HSyn.GR9.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_sf_u_y3c_nos_ds (n
    : _root_.HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOSDS) :
    _root_.HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOSDS where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  repExists := n.repExists
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  y3row := n.y3row
  raynaudSemistableSH := n.raynaudSemistableSH
  faltingsSemistableHeightBC := n.faltingsSemistableHeightBC
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  heckeSqrtY3 := n.heckeSqrtY3
  r6u := n.r6u
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
end HDec.HSyn.GR9
end


-- copied from NOSNarrowChain.lean (there: copied from ZInQKernel/OneProof/H/Y3Copy4.lean:1229
-- (_root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3c))
noncomputable section
namespace HDec.HSyn.GR9
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.all false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
/-- `_root_.HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOSDS` without `rayClassCMAb`,
  `shimuraFamilyAb`, with the leaves `shimuraMainThmIDeligneY3AbU` (leaf-fold22). -/
structure _root_.HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOSDS : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- ds965-reroute: R14 without its determinant, from the live rows `modularHTCoeff` (weight `k ≥
    2`) and `dsThm966Printed` (weight `1`) (`DS965Reroute.eigenformRepExistsG9_of_modularHT`);
    replaces the Diamond–Shurman 9.6.5 field. -/
  repExists : _root_.ZInQ.Contrib.G9.PkgI4.EigenformRepExists
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795),
    replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi
    function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces
    `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each
    connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian
  `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
  `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune
  proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3
  -- VI_B 3.10)
  /-- y3-x6 (carried leaf): the manuscript's map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in
    place of the `X₆` witness. -/
  y3row : _root_.Y3P1j.Y3ToP1j
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I
    Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O`
  and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in
  `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically
  closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with
  `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- ss-faltings: Faltings 1983, invariance of the height of a semistable Néron model under
    finite extension (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`); replaces the SGA 7 IX Cor.
    3.3 fields. -/
  faltingsSemistableHeightBC : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC
  /-- fold34-eichler (eichler-bound): the upper bound `card CM(R) ≤ 2^{b(R)} h(R)`
    (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces
  this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models
    commute with strict henselization), for unramified strictly henselian extensions with
    separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces
    strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞`
    (`HeckeSqrtBranchAny`), in place of Elkies' model. -/
  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction
    semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a
    time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability
    read on the geometric special fibre; reading risk: if the print reads it over k(s), this form
    exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue
    fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward).
    Replaces r6u; StrictHenselizationInside and the K^s axis are proved. -/
  r6u : _root_.HDec.D2A6.R6U
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main
    Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli
    scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x)
    / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at
    Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces
    rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
end HDec.HSyn.GR9
end

