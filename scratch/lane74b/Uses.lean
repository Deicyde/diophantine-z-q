import ZInQKernel.OneProof.Main

/-! Which modules of the kernel does `ZInQ.OneProof.frozenTarget` use (constants in the transitive closure of
its type and value, grouped by defining module)? Prints every `ZInQKernel` module with a used constant whose
name matches the Route K / TYZ / GZ / CR3 patterns, and the count of used kernel modules. -/

open Lean Elab Command

elab "#uses_report" : command => do
  let env ← getEnv
  let root := `ZInQ.OneProof.frozenTarget
  let mut seen : NameHashSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      match ci with
      | .inductInfo ii => cs := cs ++ ii.ctors.toArray
      | .ctorInfo ci' => cs := cs.push ci'.induct
      | _ => pure ()
      for c in cs do
        if !seen.contains c then todo := todo.push c
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for n in seen.toArray do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`ZInQKernel).isPrefixOf m then
        byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let pats := ["RouteK", "TYZ", "GZ", "Hecke", "CR3", "CertifiedRank", "PSide", "GaussFE", "PropN", "Rank"]
  let mut lines : Array String := #[]
  for (m, ns) in byMod.toList do
    let s := m.toString
    if pats.any (fun p => (s.splitOn p).length > 1) then
      let ex := (ns.toList.take 4).map toString
      lines := lines.push s!"{s} {ns.size} {ex}"
  lines := lines.qsort (· < ·)
  logInfo m!"used constants: {seen.size}; kernel modules with used constants: {byMod.size}\nRoute K / TYZ / GZ / CR3-named modules with used constants: {lines.size}\n{String.intercalate "\n" lines.toList}"

#uses_report
