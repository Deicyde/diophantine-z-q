import ZInQKernel.OneProof.Main
import Lean
/-! theta-fold: are any declarations of the new contributor modules `ZInQKernel.Contrib.OneProof.LinYang*` copies of
declarations elsewhere (same type hash; for definitions also the same value hash)? Also lists same-statement pairs
inside the new modules. Writes scratch/theta-fold/dupscan.txt. -/
open Lean

def isNew (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`ZInQKernel.Contrib.OneProof).isPrefixOf env.header.modules[i.toNat]!.module &&
      (env.header.modules[i.toNat]!.module.toString.splitOn "LinYang").length > 1
  | none => false

run_cmd do
  let env ← getEnv
  let mut byType : Std.HashMap UInt64 (Array Name) := {}
  let mut news : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    if isNew env n then news := news.push (n, ci)
    byType := byType.insert ci.type.hash ((byType.getD ci.type.hash #[]).push n)
  let mut out : Array String := #[]
  for (n, ci) in news do
    let cands := (byType.getD ci.type.hash #[]).filter (· != n)
    for c in cands do
      let some cj := env.find? c | continue
      if cj.type != ci.type then continue
      let same := match ci, cj with
        | .defnInfo a, .defnInfo b => if a.value == b.value then "SAMEVALUE" else "DIFFVALUE"
        | .thmInfo _, .thmInfo _ => "THM"
        | _, _ => "OTHER"
      -- skip trivially shared types (Prop-valued defs with type `Prop`, `ℂ`-valued etc. need value equality)
      if same == "DIFFVALUE" then continue
      let mi := (env.getModuleIdxFor? c).map (fun i => toString env.header.modules[i.toNat]!.module)
      out := out.push s!"{same} {n} ~ {c} ({mi.getD "?"}){if isNew env c then " [new]" else ""}"
  IO.FS.writeFile "scratch/theta-fold/dupscan.txt" ("\n".intercalate (out.qsort (· < ·)).toList ++ "\n")
  logInfo m!"DUPSCAN new={news.size} hits={out.size}"
