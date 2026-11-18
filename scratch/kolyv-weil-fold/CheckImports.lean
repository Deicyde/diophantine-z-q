import ZInQKernel.OneProof.Main

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    IO.println s!"IMPORT {mod}"
