import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.GaussFE.Headline

/-! Each provider's type is syntactically (`==` on `Expr`) the registered hypothesis constant,
with no extra hypotheses. -/

open Lean Meta in
run_meta do
  for (p, h) in [(``ZInQ.Contrib.heckeContinuation, ``ZInQ.Literature.HeckeContinuation),
      (``ZInQ.Contrib.functionalEquation5, ``ZInQ.Literature.FunctionalEquation5)] do
    let ty := (← getConstInfo p).type
    unless ty == mkConst h do throwError "{p} has type {ty}, not {h}"
    logInfo m!"{p} : {h}  (type is exactly the constant)"

/-- `GaussPointCount` is defined once. -/
example : ZInQ.Contrib.HeckeFE.GaussPointCount := ZInQ.Contrib.GaussFE.gaussPointCount
