import ZInQKernel.OneProof.Main
import ZInQKernel.Contrib.OneProof.GR14Narrow

/-! gr14-narrow: checks of the manual fold's replacement terms, at the base (43513d87).
(a) TailD L251: `transfer_core r.r19` → `GapGR.transfer_core_fwd r.r19` has the same remaining type.
(b) TailK L308: the replacement `reverseIsogeny` term typechecks in `gluePieces_of_open4`'s context.
(c) TailZ4 L153-L171: `heightRowsNo20_of8` with `R19Fwd` from the forward leaf (the field after the fold). -/

open CategoryTheory AlgebraicGeometry

-- (a)
example (r19 : ZInQ.DefFaltings.R19_GaudronRemond) :
    GapGR.transfer_core_fwd (GapGR.r19Fwd_of_r19 r19) = HDec.HSyn.G0Split.transfer_core r19 := rfl

namespace HDec.HSyn

-- (b) `gluePieces_of_open4` with the `reverseIsogeny` field replaced (TailK L308)
theorem gluePieces_of_open4_gr14 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg) : GluePieces :=
  { gluePieces_of_open4 r t l g hYu with
    reverseIsogeny := GapGR.reverseIsogeny_of_weil mulIsogeny_proved l.isogenyQuasiInverse }

-- (c) `heightRowsNo20_of8` (TailZ4 L153) with `R19Fwd`; `hGR` stands for the field after the fold.
theorem heightRowsNo20_of8_gr14 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8)
    (hGR : GapGR.GaudronRemondThm14Fwd) :
    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.GapGR.R19Fwd ∧
      _root_.ZInQ.DefFaltings.R21_Bost ∧ _root_.ZInQ.LeafPush2.R22_Pazuki ∧
      _root_.ZInQ.DefFaltings.StableHeightFinite :=
  have hN1 := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists
  have gl := _root_.ZInQ.HeightGlue.heightGlue_of_t35
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
  have hMet := _root_.ZInQ.HeightSplit.neronMetrizable_of gl.an3Exists gl.unifDim gl.metrize
  ⟨_root_.ZInQ.HeightSplit.r18_of_leaves r.javanpeykarBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange hMet,
    _root_.GapGR.r19Fwd_of_leaves hGR hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.HeightSplit.r21_of_leaves' r.bostLowerBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange gl.an3Unique,
    _root_.ZInQ.HeightSplit.r22_of_upper r.pazukiCor13Upper hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.HeightSplit.stableHeightFinite_of' hN1 r.semistableReductionThm r.semistableNeronBaseChange
      hMet gl.an3Unique⟩

-- the old row's other components are unchanged
example (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8) :
    (heightRowsNo20_of8_gr14 r t (GapGR.gaudronRemondThm14Fwd_of_field r.gaudronRemondThm14)).2.2 =
      (heightRowsNo20_of8 r t).2.2 := rfl

end HDec.HSyn

#print axioms GapGR.gaudronRemondThm14Fwd_of_field
#print axioms GapGR.isogenyReverseExists_of_milne
#print axioms GapGR.isogenyReverseExists_of_weil
#print axioms GapGR.r19Fwd_of_leaves
#print axioms GapGR.transfer_core_fwd
#print axioms GapGR.gaudronRemondThm14Fwd_of_open
#print axioms GapGR.isogenyReverseExists_of_open
#print axioms HDec.HSyn.gluePieces_of_open4_gr14
#print axioms HDec.HSyn.heightRowsNo20_of8_gr14
