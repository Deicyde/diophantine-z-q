import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.JonesPall

/-! jp-compile: `#discharges` for PR #38's `jonesPall_proof`, the rfl type check against `frozenTarget`'s
binder `hJP`, and `#print axioms`. -/

#discharges

-- the theorem's type is the binder's type (definitional, and as an elaboration check)
example : ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16 = ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16 := rfl

-- Syntactic check: the binder named `hJP` of `frozenTarget` has exactly the type of `jonesPall_proof`.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let some ft := env.find? `ZInQ.OneProof.frozenTarget | throwError "no frozenTarget"
  let some jp := env.find? `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof | throwError "no proof"
  forallTelescope ft.type fun xs _ => do
    for x in xs do
      if (← x.fvarId!.getUserName) == `hJP then
        let d ← inferType x
        logInfo m!"binder hJP : {d}; proof type : {jp.type}; syntactically equal: {d == jp.type}; defeq: {← isDefEq d jp.type}"

-- elaboration check: the proof fills the binder
example := @ZInQ.OneProof.frozenTarget
example (r : HDec.HSyn.OpenResearchLeaves26) (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17)
    (g : HDec.HSyn.OpenGlue8) := ZInQ.OneProof.frozenTarget r t l g (hJP := ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof)

#print axioms ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof
#print axioms ZInQ.Contrib.OneProof.JonesPall.jonesPall_representation
