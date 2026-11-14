import TailN
open Lean Meta
set_option maxHeartbeats 4000000
#eval show MetaM Unit from do
  let env ← getEnv
  for s in [`HDec.HSyn.OpenResearchLeaves2, `HDec.HSyn.OpenTextbookLeaves5, `HDec.HSyn.OpenAddedLeaves5] do
    let some info := getStructureInfo? env s | IO.println s!"no {s}"
    for f in info.fieldNames do
      let some pf := env.find? (s ++ f) | continue
      let ty ← Meta.forallTelescope pf.type fun _ b => pure b
      match ty.getAppFn.constName? with
      | some n =>
        if n.getRoot == `HDec then
          let k := n.replacePrefix `HDec Name.anonymous
          if let some kc := env.find? k then
            let lv := kc.levelParams.map (fun _ => levelZero)
            let kt := mkConst k lv
            let t0 ← IO.monoMsNow
            let r ← try (withCurrHeartbeats <| isDefEq kt ty) catch e => do IO.println s!"{f}: exception {← e.toMessageData.toString}"; pure false
            let t1 ← IO.monoMsNow
            IO.println s!"{f} {k} defeq:{r} ({t1 - t0} ms) fieldtype:{ty}"
      | none => pure ()
