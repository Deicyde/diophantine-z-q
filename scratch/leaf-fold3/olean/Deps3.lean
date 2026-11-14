import TailI
open Lean
-- leaf-fold3: which of the named constants lie in the dependency closure of `sixContactMin_of_open3`.
#eval show CoreM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open3
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
  for n in [`HDec.LGKerWild.exists_localGlue_of_tateModuleFree, `HDec.LGKerWild.localGlue_of_tateBridge35,
      `HDec.LTLocal.localGlue_at, `HDec.LTLocal.g7Clauses_of_transport,
      `HDec.LTLocal.linkedTateLocalD_of_tateBridge35, `HDec.FrobPiecesGood.tateBridge35_of_neron_nmp,
      `HDec.UnramRootsTask.unramRoots_all, `HDec.KummerComp.kummerMeetGlue, `HDec.PropTSGlue.specNonMeeting,
      `HDec.G0ModField.KernelField.twistDescent, `HDec.ZInQ.HeightBC.hodgeBCInjective,
      `HDec.ZInQ.HeightBC.omegaBaseChange, `HDec.LTGoodRed.goodRedTorsion, `HDec.RvGP2.burnsideAbsIrred,
      `ZInQ.Contrib.Dim.tangentDimAtOrigin, `LeafQM.AV.Pin.smoothStalkDimOne, `sorryAx] do
    IO.println s!"{n}: {visited.contains n}"
