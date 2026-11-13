import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.GaussFE.Headline
import ZInQKernel.Contrib.PSide.Convergence
import ZInQKernel.Contrib.PSide.Supersingular
import ZInQKernel.Contrib.PSide.BadPrimes
import ZInQKernel.Contrib.PSide.TYZInputsIff

/-! Every declaration under `ZInQ.Contrib` (per sub-namespace), its count, and the union of the
axioms they use; fails if any uses an axiom outside `propext`, `Classical.choice`,
`Quot.sound`. -/

open Lean Meta in
run_meta do
  let env ← getEnv
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut counts : Std.HashMap String Nat := {}
  let mut all : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`ZInQ.Contrib).isPrefixOf n && !n.isInternal then
      match ci with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        all := all.push n
        let key := match n with
          | .str (.str (.str .anonymous "ZInQ") "Contrib") s => s!"ZInQ.Contrib.{s} (top level)"
          | _ => toString ((n.components.take 3).foldl Name.append .anonymous)
        counts := counts.insert key (counts.getD key 0 + 1)
      | _ => pure ()
  let mut used : Array Name := #[]
  for n in all do
    for a in ← collectAxioms n do
      unless std.contains a do throwError "{n} uses the axiom {a}"
      unless used.contains a do used := used.push a
  for (k, c) in counts.toList.toArray.qsort (fun a b => a.1 < b.1) do
    logInfo m!"{k}: {c} declarations"
  logInfo m!"{all.size} declarations under ZInQ.Contrib; axioms used (union): {used}"
