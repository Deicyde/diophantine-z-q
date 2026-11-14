import TailN
open Lean
#eval show MetaM Unit from do
  let env ← getEnv
  for s in [`HDec.HSyn.OpenResearchLeaves2, `HDec.HSyn.OpenTextbookLeaves5, `HDec.HSyn.OpenAddedLeaves5,
      `HDec.HSyn.OpenGlue5] do
    let some info := getStructureInfo? env s | IO.println s!"no {s}"
    for f in info.fieldNames do
      let some pf := env.find? (s ++ f) | continue
      let ty ← Meta.forallTelescope pf.type fun _ b => pure b
      let ty ← Meta.forallTelescope ty fun _ b => pure b
      match ty.getAppFn.constName? with
      | some n =>
        if n.getRoot == `HDec then
          let k := n.replacePrefix `HDec Name.anonymous
          IO.println s!"{f} {n} kernel:{(env.find? k).isSome} {k}"
      | none => pure ()
