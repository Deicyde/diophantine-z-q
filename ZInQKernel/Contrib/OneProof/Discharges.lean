import Lean

/-!
# `#discharges`: which open hypotheses of the single proof a contribution proves

`ZInQ.OneProof.frozenTarget` proves `ZInQ.FrozenTarget` from open hypotheses: the fields of its bundle
arguments (`Prop`-valued structures declared in `ZInQKernel.OneProof` modules) and its other `Prop` arguments.
`docs/one-proof/OPEN.md` lists them.

A contribution is a file `ZInQKernel/Contrib/OneProof/<name>.lean` with a theorem whose type is one of those
hypotheses, or a theorem `L₁ → … → Lₙ → H` that proves the hypothesis `H` from new published-form leaves
`Lᵢ` (each a `def … : Prop` with a docstring giving its source). To check it, put in a scratch file

    import ZInQKernel.Contrib.OneProof.Main
    import ZInQKernel.Contrib.OneProof.Discharges
    import ZInQKernel.Contrib.OneProof.<name>

    #discharges

(the scratch file imports `Main`; the contribution itself must not, since a fold makes `Main` import it) and run
`lake env lean <scratch file>` (after `lake build +ZInQKernel.Contrib.OneProof.Main
+ZInQKernel.Contrib.OneProof.Discharges +ZInQKernel.Contrib.OneProof.<name>`). For every theorem of the current file
and of the modules under `ZInQKernel.Contrib.OneProof`, it reports each open hypothesis the theorem's conclusion
matches, the hypotheses the theorem still assumes, and its axioms. A match needs the conclusion to be the
hypothesis's type up to reducible unfolding; a statement change does not match.
-/

open Lean Elab Command Meta

namespace ZInQ.OneProof.Discharges

/-- An open hypothesis of `frozenTarget`: a bundle field, or a plain `Prop` argument. -/
structure OpenHyp where
  /-- `Bundle.field`, or the argument's name. -/
  label : String
  type : Expr

def isOneProofModule (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => (`ZInQKernel.OneProof).isPrefixOf env.header.modules[idx.toNat]!.module
  | none => false

/-- `Prop`-valued structures declared in OneProof modules: the bundles. -/
def isBundle (env : Environment) (s : Name) : Bool :=
  isStructure env s && isOneProofModule env s &&
    match env.find? s with
    | some (.inductInfo v) => Id.run do
        let mut t := v.type
        while t.isForall do t := t.bindingBody!
        return t == .sort .zero
    | _ => false

/-- The open hypotheses, read off `frozenTarget`'s type. -/
def openHyps (root : Name := `ZInQ.OneProof.frozenTarget) : MetaM (Array OpenHyp) := do
  let env ← getEnv
  let some ci := env.find? root | throwError "{root} is not in the environment; import ZInQKernel.Contrib.OneProof.Main"
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let d ← inferType x
      unless (← isProp d) do continue
      match d.getAppFn with
      | .const s _ =>
        if isBundle env s then
          for f in getStructureFields env s do
            let some pci := env.find? (s ++ f) | continue
            -- the projection's type is `(self : s) → T`; the field type is `T`
            let fty ← forallBoundedTelescope pci.type (some 1) fun ys body => do
              if ys.size == 1 then pure (some body) else pure none
            if let some t := fty then
              unless t.hasLooseBVars || t.hasFVar do
                out := out.push { label := s!"{s.componentsRev.head!}.{f}", type := t }
          continue
      | _ => pure ()
      out := out.push { label := toString (← x.fvarId!.getUserName), type := d }
    return out

/-- The constants to check: theorems of the current file and of `ZInQKernel.Contrib.OneProof.*`. -/
def candidates (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ci matches .thmInfo _ then out := out.push n
  for (n, ci) in env.constants.map₁.toList do
    unless ci matches .thmInfo _ do continue
    if let some idx := env.getModuleIdxFor? n then
      if (`ZInQKernel.Contrib.OneProof).isPrefixOf env.header.modules[idx.toNat]!.module then
        out := out.push n
  return out.qsort (·.toString < ·.toString)

end ZInQ.OneProof.Discharges

open ZInQ.OneProof.Discharges in
/-- Report which open hypotheses of `ZInQ.OneProof.frozenTarget` the theorems of this file and of
`ZInQKernel.Contrib.OneProof.*` prove, with the hypotheses they still assume and their axioms. -/
elab "#discharges" : command => do
  let env ← getEnv
  let hyps ← liftTermElabM openHyps
  let cands := candidates env
  let mut found := 0
  for c in cands do
    let some ci := env.find? c | continue
    -- try the whole type, then peel non-dependent `Prop` hypotheses (the leaves still assumed) one by one
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
      return (hits, assumed)
    let (hits, assumed) := res
    if hits.isEmpty then continue
    found := found + 1
    let axs ← collectAxioms c
    let sorryWarn := if axs.contains ``sorryAx then " (uses sorry: not a proof)" else ""
    logInfo m!"DISCHARGES {hits.toList} by {c}{sorryWarn}\n  still assumes: {assumed.toList}\n  axioms: {axs.toList}"
  logInfo m!"#discharges: {hyps.size} open hypotheses, {cands.size} theorems checked, {found} discharge one"
