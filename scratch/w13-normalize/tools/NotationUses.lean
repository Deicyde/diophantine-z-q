/-
Offline notation-use locator for the W13 source normalization (analysis tool, not production).

For each input Lean file: imports the given *built* modules (never the file's own unbuilt staged
imports), then walks the file's commands with Lean's own command parser.  Only commands that change
parsing are elaborated (`notation`/`infix…`/`macro`/`syntax`/`macro_rules`, `namespace`, `section`,
`end`, `open`, `set_option`, `universe`, `variable`); declarations are only parsed, never elaborated.
Every syntax node whose kind is not known to the imported environment (i.e. a notation declared in
this file) is reported with its byte range, its atoms and the byte ranges of its argument children.
Output: one JSON object per file (stdout of this tool, written to a file).
-/
import Lean
open Lean Elab Command Parser

def elabKinds : List Name := [``Lean.Parser.Command.notation, ``Lean.Parser.Command.mixfix,
  ``Lean.Parser.Command.macro, ``Lean.Parser.Command.syntax, ``Lean.Parser.Command.macro_rules,
  ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
  ``Lean.Parser.Command.open, ``Lean.Parser.Command.set_option, ``Lean.Parser.Command.universe,
  ``Lean.Parser.Command.variable,
  ``Lean.Parser.Command.in]

def rangeJson (stx : Syntax) : Json :=
  match stx.getPos? (canonicalOnly := true), stx.getTailPos? (canonicalOnly := true) with
  | some a, some b => Json.arr #[Json.num a.byteIdx, Json.num b.byteIdx]
  | _, _ => Json.null

partial def collect (env : Environment) (known : Name → Bool) (stx : Syntax) (acc : Array Json) : Array Json :=
  match stx with
  | .node _ k args =>
    let acc := args.foldl (fun acc a => collect env known a acc) acc
    if known k then acc else
      let atoms := args.filterMap fun a => match a with
        | .atom _ v => some (Json.str v)
        | _ => none
      let kids := args.filterMap fun a => match a with
        | .atom _ _ => none
        | a => some (rangeJson a)
      acc.push (Json.mkObj [("kind", Json.str k.toString), ("range", rangeJson stx),
        ("atoms", Json.arr atoms), ("args", Json.arr kids)])
  | _ => acc

partial def loop (inputCtx : InputContext) (known : Name → Bool) (cmdCtx : Command.Context)
    (st : Command.State) (pst : ModuleParserState) (uses : Array Json) (errs : Array Json) :
    IO (Array Json × Array Json) := do
  let scope := st.scopes.head!
  let pmctx : ParserModuleContext :=
    { env := st.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, pst', msgs) := parseCommand inputCtx pmctx pst st.messages
  let st := { st with messages := msgs }
  if isTerminalCommand cmd then
    return (uses, errs)
  -- unwrap `... in` combinators: elaborate only if the whole thing is a scope/notation command
  let k := cmd.getKind
  let perrs := (msgs.toList.filter (·.severity == .error)).length - (st.messages.toList.filter (·.severity == .error)).length
  let errs := if perrs > 0 then errs.push (Json.str s!"parse error near {(cmd.getPos?.getD 0).byteIdx}") else errs
  if k == ``Lean.Parser.Command.open then
    -- elaborate each opened namespace separately, tolerating unknown (unbuilt, staged) ones
    let mut st := st
    let ids := (cmd.getArg 1).getArgs.filter (·.isIdent)
    let isSimple := (cmd.getArg 1).getKind == ``Lean.Parser.Command.openSimple
    let isScoped := (cmd.getArg 1).getKind == ``Lean.Parser.Command.openScoped
    if isSimple || isScoped then
      let ids := ((cmd.getArg 1).getArg (if isScoped then 1 else 0)).getArgs
      for id in ids do
        if id.isIdent then
          let one : Syntax := if isScoped then
              mkNode ``Lean.Parser.Command.open #[mkAtom "open", mkNode ``Lean.Parser.Command.openScoped #[mkAtom "scoped", mkNullNode #[id]]]
            else
              mkNode ``Lean.Parser.Command.open #[mkAtom "open", mkNode ``Lean.Parser.Command.openSimple #[mkNullNode #[id]]]
          let r ← ((elabCommandTopLevel one).run cmdCtx |>.run st).toBaseIO
          match r with
          | .ok ((), st') => st := { st' with messages := {} }
          | .error _ => pure ()
      return ← loop inputCtx known cmdCtx st pst' uses errs
  if elabKinds.contains k && k != ``Lean.Parser.Command.in then
    let isNot := k == ``Lean.Parser.Command.notation || k == ``Lean.Parser.Command.mixfix ||
      k == ``Lean.Parser.Command.macro || k == ``Lean.Parser.Command.syntax
    let uses := if isNot then collect st.env known cmd uses else uses
    let before := (parserExtension.getState st.env).kinds
    let r ← ((elabCommandTopLevel cmd).run cmdCtx |>.run st).toBaseIO
    let uses := match r with
      | .ok ((), st') =>
        if isNot then
          let after := (parserExtension.getState st'.env).kinds
          let newk := after.foldl (fun acc n _ => if before.contains n then acc else acc.push (Json.str n.toString)) #[]
          uses.push (Json.mkObj [("defn", rangeJson cmd), ("kinds", Json.arr newk)])
        else uses
      | .error _ => uses
    match r with
    | .ok ((), st') =>
      let errs := (st'.messages.toList.filter (·.severity == .error)).foldl
        (fun e m => e.push (Json.str s!"{m.pos}: elab error in scope command")) errs
      loop inputCtx known cmdCtx { st' with messages := {} } pst' uses errs
    | .error _ => loop inputCtx known cmdCtx st pst' uses (errs.push (Json.str "exception"))
  else
    let uses := collect st.env known cmd uses
    loop inputCtx known cmdCtx st pst' uses errs

unsafe def main (args : List String) : IO Unit := do
  let modsFile := args[0]!
  let outFile := args[1]!
  let files := args.drop 2
  let mods := (← IO.FS.lines modsFile).filter (· ≠ "") |>.map (·.toName)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024) (loadExts := true)
  let baseKinds := (parserExtension.getState env).kinds
  let builtin ← builtinSyntaxNodeKindSetRef.get
  let known : Name → Bool := fun k => baseKinds.contains k || builtin.contains k || k == nullKind ||
    k == `choice || k == identKind || k == strLitKind || k == numLitKind || k == charLitKind ||
    k == nameLitKind || k == scientificLitKind || k.isAnonymous || (`Lean).isPrefixOf k
  let h ← IO.FS.Handle.mk outFile .write
  for f in files do
    let input ← IO.FS.readFile f
    let inputCtx := mkInputContext input f
    let (_, pst, msgs) ← parseHeader inputCtx
    let st := Command.mkState env msgs {}
    let cmdCtx : Command.Context :=
      { fileName := f, fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none }
    let (uses, errs) ← loop inputCtx known cmdCtx st pst #[] #[]
    h.putStrLn (Json.mkObj [("file", Json.str f), ("uses", Json.arr uses), ("errors", Json.arr errs)]).compress
    h.flush
