# W13 source normalization (Cloud Batch 3 Worker 13)

Date: 2026-11-16. Branch `cloud-b3/w13-normalize`, based on `9558056025e82261994a8cb95a3b39796df13303`
(the source-only recovery commit). Written by Cloud Batch 3 Worker 13 with Metamate/agentcloud assistance;
modifications of the Apache-2.0 vendored files are recorded per file in a "Normalization notice" block
(Apache-2.0 §4(b)); LICENSE, NOTICE, NOTICE.upstream and ATTRIBUTION.upstream.md are unchanged.

## What the normalization does

The recovered port used commands from `ZInQKernel/Contrib/CloudR2NOS/Source/PortUtilExt.lean` (new
elaborators, not accepted for production and therefore not staged) and from the existing upstream
`ZInQKernel/Contrib/CloudW03NeronSurj/PortUtil.lean`. Every such *scope* command is replaced by ordinary
Lean commands with the same effect on Lean's elaboration state:

| port command | effect (from the command's source, read as a specification; never executed) | ordinary Lean emitted |
|---|---|---|
| `r2nos_open_dual "A B~h"` (after `open A B …`) | opens/activates the other half (`A` ↔ `ZInQ.Contrib.CloudW03NeronSurj.FLT.A`) of every namespace Lean's `open` resolved | `open _root_.X …` / `open _root_.X hiding h` for the halves that are not yet open |
| `r2nos_open_scoped_dual "A"` | activates the other half's scoped extensions | `open scoped _root_.X …` |
| `r2nos_namespace_dual` (after `namespace A.B`) | adds the Mathlib-root namespaces `A`, `A.B` of the current port namespace as open declarations, activates them | `open _root_.A _root_.A.B` |
| `r2nos_open_scoped "A"` | activates scoped extensions of `A` and of `FLT.A` | `open scoped _root_.A _root_.…FLT.A` (existing ones) |
| `w03_open "A~h"` | opens `A` and `FLT.A` (unconditionally) | `open _root_.A _root_.…FLT.A` (existing ones, `hiding` where the hidden name exists) |
| `w03_reactivate "N"` | (re)activates scoped extensions of `FLT.N` | `open scoped _root_.…FLT.N` |
| `w03_export "NS" "a b"` | aliases `cur.a ↦ FLT.NS.a` (else `NS.a`, else the private one) | `export _root_.T (a b)` grouped by target namespace |
| `r2nos_alias "a" "t"` | alias `FLT.a ↦ t` | `export …` when the alias lies in the current namespace; dropped when provably redundant (see below) |
| `r2nos_erase_attr "instance"/"simp" "n …"` | erases the attribute from each name that resolves; unknown names are skipped with a warning | `attribute [-instance]` / `attribute [-simp]` listing exactly the names that resolve |
| `#r2nos_type_eq_warn a b` | diagnostic only | removed |
| `import …R2NOS.PortUtilExt` | — | removed (replaced by the existing `CloudW03NeronSurj.PortUtil` import when it was the only one, so `w03_exact_reverting` and `import Lean` stay available) |

The tactic `w03_exact_reverting` (existing upstream, trusted) is kept.

File-local notations (`local notation`, `local infix…`, the two `scoped macro`s, and the unused global
`notation α "^+" M` of `Def_Compat_Mathlib430`) are removed by inlining: Lean's own parser
(`scratch/w13-normalize/tools/NotationUses.lean`, elaborating only parser-changing commands) locates every
use with its exact argument spans; the use is replaced by the right-hand side with the arguments
substituted, parenthesised. A heuristic flags uses where the enclosing declaration may bind an identifier of
the right-hand side (textual inlining is not hygienic); flagged uses are listed as residuals.

## How the translation is computed

`scratch/w13-normalize/tools/translate.py` simulates, for each file in import order, two copies of Lean
4.35's command-level scope state (scopes, open declarations, active scoped namespaces, aliases, erased
attributes) following `Lean/ResolveName.lean`, `Lean/Elab/Open.lean`, `Lean/Elab/BuiltinCommand.lean` and
`Lean/ScopedEnvExtension.lean`: **S** runs the recovered source with the port commands' semantics, **T** runs
the translated file. After every port command the ordinary commands that bring T to S are emitted; after
every other command (`namespace`, `end`, declarations) T is re-synchronised, so a namespace that a port
command opened before it existed is opened (with the same effect) when it comes into existence. Any
difference ordinary Lean cannot express is reported as a residual.

Environment facts: built modules (Mathlib and upstream kernel modules) from their `.olean`s
(`tools/EnvDump.lean`: namespaces registered per module, public constants, protected flags, instances,
simp entries, aliases); staged modules from a static declaration index (`tools/index.py`, Lean 4.35 naming
rules: `_root_`, `private`, `registerNamePrefixes`, structure/inductive auxiliary names).

## Residual risks

* Erase-guard names whose declaring declaration is auto-named (anonymous instances, `@[simps]` lemmas) are
  not in the static index; such a name is kept only if it resolves. A kept name that does not exist in a
  file's import closure is a compile error at that `attribute` line (remove the name: that is exactly the
  port command's behaviour); an omitted name that does exist leaves an instance/simp lemma active.
* The old compile receipts (17:47 bank) were used only as diagnostics to cross-check these decisions, not as
  build or proof evidence.
* Oversized-file splitting and the remaining residuals are listed in `scratch/w13-normalize/REPORT.md`.

## Re-running

```
python3 scratch/w13-normalize/tools/pipeline.py --cone-json <modules.json> --write
python3 scratch/w13-normalize/tools/compile.py --cone-json <modules.json> --jobs 1
```

## Canonical-provider repair (2026-11-16)

The staged copies `CloudB3W13Shared/TateCp/Vendor/AnthropicFLT/Definitions/Def_FLTPrelim_{FreyPackage,GaloisRep,Ramification}.lean`
duplicated main's `CloudB2X0Transitive/Vendor/AnthropicFLT/Definitions/Def_FLTPrelim_*` (token-identical code, same root
declarations) and collided with them when both were imported. Their 42 importing lines in 41 staged files now name main's
providers (each file carries an import notice) and the duplicates were removed from this tree; their recovered bodies stay
in the recovery overlay.

