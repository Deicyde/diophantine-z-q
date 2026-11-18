import ZInQKernel.Contrib.OneProof.CMBranch.R5Prune
/-! cm-branch2: which conjuncts of the moduli row are READ on the CM-branch route.
For every constant in the transitive closure of the root, walk its value; at every binder (λ, ∀, let) whose type
head is one of the clause defs, record whether the body uses the bound variable (`hasLooseBVar 0`).
"used" outside producers means some proof reads the clause. Output: per clause, the constants that use it. -/
open Lean Meta

partial def scanBinders (clauses : List Name) (e : Expr) : StateM (Std.HashSet Expr × Array (Name × Bool)) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  let rec note (t b : Expr) : StateM (Std.HashSet Expr × Array (Name × Bool)) Unit :=
    match t.getAppFn with
    | .const c _ => if clauses.contains c then modify fun (v, a) => (v, a.push (c, b.hasLooseBVar 0)) else pure ()
    | _ => pure ()
  match e with
  | .lam _ t b _ | .forallE _ t b _ => do scanBinders clauses t; note t b; scanBinders clauses b
  | .letE _ t v b _ => do scanBinders clauses t; scanBinders clauses v; note t b; scanBinders clauses b
  | .app f a => do scanBinders clauses f; scanBinders clauses a
  | .mdata _ b => scanBinders clauses b
  | .proj _ _ b => scanBinders clauses b
  | _ => pure ()

#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open72_cm2_r5
  let clauses : List Name := [`LeafQM.AV.R5ptProps, `LeafQM.AV.R1fpProps, `LeafQM.AV.R1heckeProps,
    `LeafQM.AV.X6Props, `LeafQM.AV.R2X6Props, `HDec.LeafAdopt.R2X6PropsIff, `LeafQM.AV.R2X6PropsIff,
    `LeafQM.AV.R1recProps, `LeafQM.AV.X6Surj, `LeafQM.AV.CMExists, `LeafQM.AV.R2fpProps,
    `HDec.X6Kummer.X6ConicModel, `HDec.X6Kummer.X6ConicModel_r5, `HDec.LeafAdopt.R1R2fpRepW_r5, `LeafQM.AV.R1R2fp_r5, `LeafQM.AV.R5fp]
  let clauses := clauses.filter (fun c => env.contains c)
  IO.println s!"clauses present: {clauses}"
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  let mut uses : Std.HashMap Name (Array Name) := {}
  let mut carried : Std.HashMap Name Nat := {}
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let inZ := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!.toString.startsWith "ZInQKernel")
      | none => false
    if !inZ then continue
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      let ((), (_, res)) := (scanBinders clauses v).run ({}, #[])
      for (c, used) in res do
        if used then uses := uses.insert c ((uses.getD c #[]).push n)
        else carried := carried.insert c (carried.getD c 0 + 1)
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  IO.println s!"closure size {seen.size}"
  for c in clauses do
    let us := (uses.getD c #[]).toList.eraseDups
    IO.println s!"== {c}: used in {us.length} constants, unused binders {carried.getD c 0}"
    IO.println s!"   {us}"
  -- does the closure mention the top field?
  for f in [`HDec.HSyn.OpenResearchLeaves53.gonzalezRotgerThm512X6RCF, `HDec.HSyn.OpenResearchLeaves53.x6CoarseModuliIdeal,
      `HDec.HSyn.OpenResearchLeaves53.elkiesX6StarEveryIdeal] do
    IO.println s!"closure contains {f}: {seen.contains f}"
