import ZInQKernel.OneProof.Main
/-! yu-prune: for each constant named in `scratch/yu-prune/used-consts-names.txt`, the sorted constants used by its
type and by its value, written to `scratch/yu-prune/used-consts.txt` (run in the base tree and in this tree and diff:
shows that a value-only hash change is a renamed auxiliary `_proof_N`; each `_proof_N` is replaced by its statement's hash). -/
open Lean
run_cmd do
  let env ← getEnv
  let names := (← IO.FS.readFile "scratch/yu-prune/used-consts-names.txt").splitOn "\n" |>.filter (· ≠ "")
  let mut out : Array String := #[]
  for n in names do
    match env.find? n.toName with
    | some ci =>
      -- an auxiliary `_proof_N` constant is recorded by the hash of its statement, not by its name
      let norm (c : Name) : String :=
        if (c.toString.splitOn "._proof_").length > 1 then
          s!"PROOF:{((env.find? c).map (·.type.hash)).getD 0}" else toString c
      let ty := ci.type.getUsedConstants.map norm |>.qsort (· < ·)
      let v := (ci.value? (allowOpaque := true)).map (·.getUsedConstants.map norm |>.qsort (· < ·)) |>.getD #[]
      out := out.push s!"{n}\n  T {ty.toList}\n  V {v.toList}"
    | none => out := out.push s!"{n} MISSING"
  IO.FS.writeFile "scratch/yu-prune/used-consts.txt" ("\n".intercalate out.toList ++ "\n")
