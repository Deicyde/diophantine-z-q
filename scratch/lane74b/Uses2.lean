import ZInQKernel.OneProof.Main

/-! Every reference from a constant defined outside the 79 kept Route K / TYZ / CR3 modules
(`scratch/lane74b/kept-mods.txt`: lane74's 78 H-reach files and `RouteK.Selmer.CharSum`) to a constant defined in one
of them, over the environment of `ZInQKernel.OneProof.Main` (type and value of every constant). -/

open Lean Elab Command

elab "#kept_refs" : command => do
  let env ← getEnv
  let kept ← IO.FS.lines "scratch/lane74b/kept-mods.txt"
  let keptSet : NameHashSet := kept.foldl (fun s m => s.insert m.toName) {}
  -- the modules of the H reach (and Main) that import a kept module, directly or not (scratch/lane74b/sees-kept.txt,
  -- from the import graph); no other module can mention a kept constant
  let sees ← IO.FS.lines "scratch/lane74b/sees-kept.txt"
  let seesSet : NameHashSet := sees.foldl (fun s m => s.insert m.toName) {}
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let mut hits : Std.HashMap (Name × Name) Name := {}
  let mut nconst : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    if !seesSet.contains m then continue
    nconst := nconst + 1
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      if let some mc := modOf c then
        if keptSet.contains mc && !hits.contains (m, c) then hits := hits.insert (m, c) n
  let out := (hits.toArray.map fun ((m, c), n) => s!"{m} : {c} (e.g. in {n})").qsort (· < ·)
  logInfo m!"kernel constants scanned: {nconst}; (module, kept constant) pairs: {out.size}\n{String.intercalate "\n" out.toList}"

#kept_refs
