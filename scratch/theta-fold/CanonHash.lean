import ZInQKernel.OneProof.Main
/-! yu-prune: canonical hashes modulo auxiliary-proof names. For each constant named in
`scratch/theta-fold/used-consts-names.txt`, the hash of its type and of its value after every auxiliary
`…._proof_N` constant is replaced (recursively) by a placeholder named after the canonical hash of its statement.
Written to `scratch/theta-fold/canon-hashes.txt`. Run in the base tree and in this tree and compare: equal canonical
hashes mean that the constant changed only by the renaming/sharing of auxiliary proofs. -/
open Lean

partial def canon (env : Environment) (memo : IO.Ref (Std.HashMap Name UInt64)) (e : Expr) : IO Expr := do
  let cs := e.getUsedConstants.filter fun c => (c.toString.splitOn "._proof_").length > 1
  let mut m : Std.HashMap Name Name := {}
  for c in cs do
    let h ← canonProof env memo c
    m := m.insert c (Name.mkSimple s!"PROOF_{h}")
  return e.replace fun
    | .const c ls => (m[c]?).map (fun n => .const n ls)
    | _ => none
where
  canonProof (env : Environment) (memo : IO.Ref (Std.HashMap Name UInt64)) (c : Name) : IO UInt64 := do
    if let some h := (← memo.get)[c]? then return h
    let h ← match env.find? c with
      | some ci => pure (← canon env memo ci.type).hash
      | none => pure 0
    memo.modify (·.insert c h)
    return h

run_cmd do
  let env ← getEnv
  let names := (← IO.FS.readFile "scratch/theta-fold/used-consts-names.txt").splitOn "\n" |>.filter (· ≠ "")
  let memo ← IO.mkRef ({} : Std.HashMap Name UInt64)
  let mut out : Array String := #[]
  for n in names do
    match env.find? n.toName with
    | some ci =>
      let t ← canon env memo ci.type
      let v ← match ci.value? (allowOpaque := true) with
        | some v => pure (← canon env memo v).hash
        | none => pure 0
      out := out.push s!"{n} {t.hash} {v}"
    | none => out := out.push s!"{n} MISSING"
  IO.FS.writeFile "scratch/theta-fold/canon-hashes.txt" ("\n".intercalate out.toList ++ "\n")
