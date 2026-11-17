import ZInQKernel.OneProof.Main
import Lean
/-! charpoly-hf: every `lean:` target named in blueprint/ (list: scratch/charpoly-hf/bp_names.txt, from
`grep -rh "^lean:" blueprint/`) that exists in the base environment of `ZInQKernel.OneProof.Main` still exists after the
fold (a substitute for `autoform render --require-declarations`, which is not installed on this host). Prints the
missing ones; compare the outputs of the base tree and the folded tree. -/
open Lean
run_cmd do
  let env ← getEnv
  let ls ← IO.FS.lines "scratch/charpoly-hf/bp_names.txt"
  let names := ls.toList.filter (· ≠ "")
  let missing := names.filter (fun s => !env.contains s.toName)
  logInfo s!"{names.length} blueprint targets; {missing.length} not in the environment of Main: {missing}"
