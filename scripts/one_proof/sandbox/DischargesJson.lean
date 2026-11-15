import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges

/-!
# The discharge check's reporter

The discharge check workflow runs it after the build; never run it on a project machine with a contribution.
`discharge_check.sh` writes `.sandbox/Report.lean`: the imports of `ZInQKernel.OneProof.Main`,
`ZInQKernel.OneProof.Discharges` and the contributed modules, then this file without its `import` lines, and runs
`lake env lean .sandbox/Report.lean`.

`#discharges_json` repeats the matching of `#discharges` (`ZInQKernel/OneProof/Discharges.lean`): for each
candidate theorem, the whole type, then the type with its non-dependent `Prop` hypotheses peeled one by one,
against each open hypothesis, with `isDefEq` under `withReducible`. Each peeled hypothesis is matched against
the open hypotheses the same way, so that a theorem assuming the hypothesis it proves is visible. It prints one
line per theorem that discharges an open hypothesis,

    DISCHARGE-JSON <nonce> {"theorem": ..., "hits": [...], "assumes": [...], "assumes_open": [...],
      "axioms": [...], "sorry": ...}

where `assumes_open` lists the open hypotheses that the peeled hypotheses match,

and a final `DISCHARGE-JSON <nonce> {"summary": {"open_hypotheses": N, "theorems_checked": M,
"discharging": K}}`. The objects are written with `Lean.Json`, so no name can break a line. The nonce is the
environment variable `DISCHARGE_NONCE`, which the workflow sets at run time; without it nothing is printed.
-/

open Lean Elab Command Meta ZInQ.OneProof.Discharges

/-- Print the `#discharges` records as `DISCHARGE-JSON` lines for the discharge check's parser. -/
elab "#discharges_json" : command => do
  let some nonce ← IO.getEnv "DISCHARGE_NONCE" | throwError "DISCHARGE_NONCE is not set"
  if nonce.isEmpty || !nonce.all Char.isAlphanum then
    throwError "DISCHARGE_NONCE must be a non-empty string of ASCII letters and digits"
  let env ← getEnv
  let hyps ← liftTermElabM openHyps
  let cands := candidates env
  let mut found := 0
  for c in cands do
    let some ci := env.find? c | continue
    -- the matching loop of `#discharges`, unchanged
    let res ← liftTermElabM do
      let mut t := ci.type
      let mut assumed : Array Expr := #[]
      let mut hits : Array String := #[]
      repeat
        for h in hyps do
          if t == h.type then hits := hits.push h.label
          else if ← withReducible (isDefEq t h.type) then hits := hits.push h.label
        unless hits.isEmpty do break
        match t with
        | .forallE _ d b _ =>
          if !b.hasLooseBVars && (← isProp d) then
            assumed := assumed.push d
            t := b
          else break
        | _ => break
      let mut assumedOpen : Array String := #[]
      for d in assumed do
        for h in hyps do
          if d == h.type then assumedOpen := assumedOpen.push h.label
          else if ← withReducible (isDefEq d h.type) then assumedOpen := assumedOpen.push h.label
      let assumes ← assumed.mapM fun d => toString <$> ppExpr d
      return (hits, assumes, assumedOpen)
    let (hits, assumes, assumedOpen) := res
    if hits.isEmpty then continue
    found := found + 1
    let axs ← collectAxioms c
    let obj := Json.mkObj [("theorem", toJson (toString c)), ("hits", toJson hits),
      ("assumes", toJson assumes), ("assumes_open", toJson assumedOpen), ("axioms", toJson (axs.map toString)),
      ("sorry", toJson (axs.contains ``sorryAx))]
    IO.println s!"DISCHARGE-JSON {nonce} {obj.compress}"
  let summary := Json.mkObj [("open_hypotheses", toJson hyps.size),
    ("theorems_checked", toJson cands.size), ("discharging", toJson found)]
  IO.println s!"DISCHARGE-JSON {nonce} {(Json.mkObj [("summary", summary)]).compress}"

#discharges_json
