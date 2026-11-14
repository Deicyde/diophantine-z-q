import TailK
open Lean
-- leaf-fold4: the conclusion is the kernel's own `ZInQ.SixContactMin`, and which named constants lie in the
-- dependency closure of `sixContactMin_of_open4`.
/-- The conclusion is the kernel's own `ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`). -/
example : (∀ (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves4)
    (l : HDec.HSyn.OpenAddedLeaves4) (g : HDec.HSyn.OpenGlue4), _root_.ZInQ.SixContactMin) :=
  HDec.HSyn.sixContactMin_of_open4
#print axioms HDec.HSyn.sixContactMin_of_open4
#eval show CoreM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open4
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
  IO.println s!"closure size {visited.size}"
  for n in [`sorryAx,
      `HDec.WeilPairing.DivisiblePoints, `HDec.G0Galois.tatePairingZl_of_leaves, `HDec.G0Galois.detTate_of_leaves,
      `HDec.HSyn.gluePieces_of_open3,
      `HDec.HeckeRestCurve.chartProper, `HDec.HeckeRestCurve.chartQuasiFinite_of_proper,
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_proof,
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof,
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof,
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.piTwistC_of,
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of',
      `HDec.HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of,
      `LeafQM.AV.Pin.autOInnerFinite, `TSkolemKW.leafSkolemNoether,
      `ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness,
      `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega,
      `T5Torsion.TateFree.tateModuleFree_of_torsionStructure,
      `T5Torsion.TateFree.tate_surj_of_torsionStructure,
      `HDec.LGKerWild.exists_localGlue_of_tateModuleFree, `HDec.LTLocal.localGlue_at,
      `HDec.FrobPiecesGood.tateBridge35_of_neron_nmp, `ZInQ.RLeaf.x1RationalCusp_of_x0Transitive] do
    IO.println s!"{n}: {visited.contains n}"
