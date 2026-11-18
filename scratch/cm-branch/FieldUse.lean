import ZInQKernel.Contrib.OneProof.CMBranch.Open4
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let some ci := env.find? `HDec.HSyn.sixContactMin_of_open4_cm | throwError "no"
  let cs := (match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default).getUsedConstants
  let interesting := cs.filter fun n =>
    let s := n.toString
    (s.splitOn "r5count").length > 1 || (s.splitOn "cmOptimalEmbedding").length > 1 ||
    (s.splitOn "x6ConicModel").length > 1 || (s.splitOn "FibreComTrivial").length > 1 ||
    (s.splitOn "fibreComTrivial").length > 1 || (s.splitOn "x6KummerFibre").length > 1
  IO.println s!"direct constants: {cs.size}; NoCM-related: {interesting}"
  -- transitive closure restricted to HDec/CMBranch-local defs is expensive; check the old for comparison
  let some ci2 := env.find? `HDec.HSyn.gluePieces_of_open4_hf_pz_eb | throwError "no2"
  let cs2 := (match ci2 with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default).getUsedConstants
  let interesting2 := cs2.filter fun n =>
    let s := n.toString
    (s.splitOn "r5count").length > 1 || (s.splitOn "cmOptimalEmbedding").length > 1 ||
    (s.splitOn "x6ConicModel").length > 1 || (s.splitOn "FibreComTrivial").length > 1 || (s.splitOn "fibreComTrivial").length > 1
  IO.println s!"old gluePieces NoCM-related: {interesting2}"
