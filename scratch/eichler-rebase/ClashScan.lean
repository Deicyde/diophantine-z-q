import Lean
/-! eichler-rebase step (2), exact form. `AllContribNew.lean` cannot elaborate because main's own Contrib tree
already has clashes (e.g. `PkgI6.TraceContainsRamificationIdx` in both `ZInQKernel.HDecomp.Textbook.Different` and
`ZInQKernel.Contrib.Different.Local`). This scan reads the `.olean` of every module in the joint import closure of
`AllContribNew.lean` (main's 244 top-level Contrib modules + this branch's modules), without building an
environment, and lists every constant name stored by two different modules. A clash that involves one of this branch's
modules is printed `NEWCLASH`; the others (pre-existing on main) `OLDCLASH`. -/
open Lean

def newMods : List Name :=
  [`ZInQKernel.Contrib.OneProof.R5fpCountLe, `ZInQKernel.Contrib.OneProof.GR56Lattice,
   `ZInQKernel.Contrib.OneProof.GRDict, `ZInQKernel.Contrib.OneProof.EichlerBound.Order,
   `ZInQKernel.Contrib.OneProof.EichlerBound.Quadratic, `ZInQKernel.Contrib.OneProof.EichlerBound.Defs,
   `ZInQKernel.Contrib.OneProof.EichlerBound.Embed, `ZInQKernel.Contrib.OneProof.EichlerBound.Unit,
   `ZInQKernel.Contrib.OneProof.EichlerBound.Crit, `ZInQKernel.Contrib.OneProof.EichlerBound.Key,
   `ZInQKernel.Contrib.OneProof.EichlerBound.Key6, `ZInQKernel.Contrib.OneProof.EichlerBound.Inv,
   `ZInQKernel.Contrib.OneProof.EichlerBound.Count, `ZInQKernel.Contrib.OneProof.EichlerBound.Bound]

run_cmd do
  let src ← IO.FS.readFile "scratch/eichler-rebase/AllContribNew.lean"
  let roots := (src.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some ((l.drop 7).trimAscii.toString.toName) else none
  IO.println s!"roots {roots.length}"
  initSearchPath (← findSysroot)
  let mut seen : NameSet := {}
  let mut todo : Array Name := roots.toArray
  let mut owner : Std.HashMap Name Name := {}
  let mut nNew := 0
  let mut nOld := 0
  let mut newConsts := 0
  let mut nmods := 0
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let f ← findOLean m
    let (md, _) ← readModuleData f
    nmods := nmods + 1
    for i in md.imports do todo := todo.push i.module
    let isNew := newMods.contains m
    for c in md.constNames do
      if isNew then newConsts := newConsts + 1
      match owner.get? c with
      | some m' =>
        if isNew || newMods.contains m' then
          IO.println s!"NEWCLASH {c} : {m'} / {m}"; nNew := nNew + 1
        else
          -- realized auxiliary constants (`eq_1`, `eq_def`, `congr_simp`, …) may be stored by several modules
          let aux := c.isInternal || (match c with
            | .str _ s => s.startsWith "eq_" || s == "congr_simp" || s == "eq_def" || s == "eq_unfold" ||
                s == "fun_cases" || s == "induct" || s == "induct_unfolding" || s == "mutual_induct"
            | _ => false)
          if !aux then
            nOld := nOld + 1
            IO.println s!"OLDCLASH {c} : {m'} / {m}"
      | none => owner := owner.insert c m
  IO.println s!"modules read {nmods}; constants {owner.size}; constants of this branch's modules {newConsts}"
  IO.println s!"clashes involving this branch's modules: {nNew}; pre-existing clashes among main's modules: {nOld}"
