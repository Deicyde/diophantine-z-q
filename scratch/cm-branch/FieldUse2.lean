import ZInQKernel.Contrib.OneProof.CMBranch.Top
open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let roots := #[`HDec.HSyn.sixContactMin_of_open72_cm, `HDec.HSyn.sixContactMin_of_open72]
  let mut res : Array (Array Name) := #[]
  for root in roots do
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := #[root]
    let mut hits : Array Name := #[]
    while h : stack.size > 0 do
      let n := stack.back
      stack := stack.pop
      if seen.contains n then continue
      seen := seen.insert n
      let s := n.toString
      if (s.splitOn "FS5NoCM").length > 1 || (s.splitOn "FibreComTrivial").length > 1 ||
         (s.splitOn "r5count").length > 1 || (s.splitOn "cmOptimalEmbedding").length > 1 ||
         (s.splitOn "x6ConicModel").length > 1 || (s.splitOn "R5ptProps").length > 1 ||
         (s.splitOn "gonzalezRotger").length > 1 then
        hits := hits.push n
      if (s.startsWith "Mathlib") || (s.startsWith "Lean.") || (s.startsWith "Std.") then continue
      match env.find? n with
      | some ci =>
        let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
        for c in v.getUsedConstants ++ ci.type.getUsedConstants do
          if !seen.contains c then stack := stack.push c
      | none => pure ()
    IO.println s!"{root}: closure {seen.size}, hits {hits.size}"
    res := res.push hits
  let a := res[0]!
  let b := res[1]!
  IO.println s!"only in old (removed by cm-branch): {(b.filter (fun n => !a.contains n)).toList}"
  IO.println s!"only in new: {(a.filter (fun n => !b.contains n)).toList}"
#print axioms HDec.HSyn.sixContactMin_of_open72_cm
