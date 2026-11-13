import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.GaussFE.Headline
import ZInQKernel.Contrib.PSide.Convergence
import ZInQKernel.Contrib.PSide.Supersingular
import ZInQKernel.Contrib.PSide.BadPrimes
import ZInQKernel.Contrib.PSide.TYZInputsIff

/-! Every constant declared in a `ZInQKernel.Contrib.*` module lies under `ZInQ.Contrib`, so the
contributions cannot clash with a baseline name when CI imports every module together. -/

open Lean Meta in
run_meta do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array Name := #[]
  for (c, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[i.toNat]!
      if (`ZInQKernel.Contrib).isPrefixOf m then
        n := n + 1
        unless (`ZInQ.Contrib).isPrefixOf c do bad := bad.push c
  logInfo m!"{n} constants in Contrib modules; outside ZInQ.Contrib: {bad}"
