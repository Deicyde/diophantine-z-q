import ZInQKernel.OneProof.Main
open Lean in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  for n in [``HDec.HSyn.OpenResearchLeaves79, ``HDec.HSyn.OpenTextbookLeaves18, ``HDec.HSyn.OpenAddedLeaves30] do
    let fs := getStructureFieldsFlattened env n (includeSubobjectFields := false)
    logInfo m!"{n} ({fs.size}): {fs.toList}"
