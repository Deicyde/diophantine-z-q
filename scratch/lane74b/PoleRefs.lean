import ZInQKernel
import ZInQKernel.OneProof.Main

/-! lane74b item 2: which constants of the pole modules (`Hypotheses.Pole`, `Hypotheses.PoleManuscript`,
`Syntax.Templates.Core`, `Multiplication.Certificate.{Parity, ConstantsProperties}`, `Assembly.Local.PoleObstruction`,
`Size.Majorants.Templates`) do the constants of `ZInQKernel.OneProof.*` modules mention directly (type or value)? -/

open Lean Elab Command

#print axioms ZInQ.OneProof.frozenTarget

run_cmd do
  let env ← getEnv
  let poleMods : List Name := [`ZInQKernel.Hypotheses.Pole, `ZInQKernel.Hypotheses.PoleManuscript,
    `ZInQKernel.Syntax.Templates.Core, `ZInQKernel.Multiplication.Certificate.Parity,
    `ZInQKernel.Multiplication.Certificate.ConstantsProperties, `ZInQKernel.Assembly.Local.PoleObstruction,
    `ZInQKernel.Size.Majorants.Templates]
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let mut hits : Std.HashMap Name (Nat × Name) := {}
  let mut seenPairs : Std.HashSet (Name × Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    if !(`ZInQKernel.OneProof).isPrefixOf m then continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      if let some mc := modOf c then
        if poleMods.contains mc then
          if !seenPairs.contains (n, c) then
            seenPairs := seenPairs.insert (n, c)
            let (k, ex) := hits.getD c (0, n)
            hits := hits.insert c (k + 1, ex)
  let out := (hits.toArray.map fun (c, (k, ex)) => s!"{c} ({modOf c |>.getD .anonymous}): {k} OneProof constants, e.g. {ex}").qsort (· < ·)
  logInfo m!"pole-module constants mentioned by OneProof constants: {out.size}\n{String.intercalate "\n" out.toList}"
