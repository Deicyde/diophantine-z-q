import ZInQKernel.Contrib.MulEtale.Direct.AllBase
import ZInQKernel.Contrib.MulEtale.Expected
import Lean
import Lean.Util.FoldConsts

/-!
# Exact H-101 full-telescope stored-body audit

Separate validation imports use trust level zero. The stored full-telescope
multiplication theorem is checked against the independent literal proposition
VALUE, with an unchanged fresh checking-addition, annotation-sensitive expression
readback, returned-environment check, extra-premise and corrupt-body controls.
Dependency walks inspect types and available opaque values; this is not raw
imported-library or serialized recursor-rule replay. Resource bounds are not
trust settings. No completion is asserted until this command actually succeeds.
-/

set_option autoImplicit false
open Lean

namespace H101DirectFieldRoute.AllBaseAudit

def outerFlags : Expr → List BinderInfo
  | .forallE _ _ body bi => bi :: outerFlags body
  | .mdata _ body => outerFlags body
  | _ => []

run_cmd do
  let env ← (importModules
    #[{ module := `ZInQKernel.Contrib.MulEtale.Direct.AllBase, importAll := true },
      { module := `ZInQKernel.Contrib.MulEtale.Expected, importAll := true }] {}
    (trustLevel := 0) : IO Environment)
  unless env.header.trustLevel.toNat == 0 do
    throwError "Validation import must have trust level zero"
  let name := `H101DirectFieldRoute.multiplication_etale
  let expectedName := `ZInQ.Contrib.MulEtale.Expected.target
  let some (.thmInfo info) := env.find? name |
    throwError "Missing stored full-telescope H-101 theorem"
  let some (.defnInfo expectedInfo) := env.find? expectedName |
    throwError "Missing independent literal expected proposition"
  let some idx := env.getModuleIdxFor? name |
    throwError "Stored theorem has no defining module"
  unless env.header.moduleNames[idx.toNat]? == some `ZInQKernel.Contrib.MulEtale.Direct.AllBase do
    throwError "Wrong theorem module"
  let some expectedIdx := env.getModuleIdxFor? expectedName |
    throwError "Expected proposition has no defining module"
  unless env.header.moduleNames[expectedIdx.toNat]? ==
      some `ZInQKernel.Contrib.MulEtale.Expected do
    throwError "Wrong independent expected module"
  unless info.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
    throwError "Changed universe-zero contract"
  match Kernel.check env {} expectedInfo.value with
  | .ok inferred =>
    match Kernel.isDefEq env {} inferred (mkSort .zero) with
    | .ok true => pure ()
    | _ => throwError "Expected value is not Prop"
  | .error _ => throwError "Expected value is ill-formed"
  unless outerFlags info.type == outerFlags expectedInfo.value do
    throwError "Changed ordered outer binder flags"
  match Kernel.isDefEq env {} info.type expectedInfo.value with
  | .ok true => pure ()
  | _ => throwError "Full actual and expected types differ"
  match Kernel.check env {} info.value with
  | .ok inferred =>
    match Kernel.isDefEq env {} inferred info.type with
    | .ok true => pure ()
    | _ => throwError "Stored body has a different type"
  | .error _ => throwError "Stored body failed kernel checking"
  let fresh := name.str "_freshH101Audit"
  unless (env.find? fresh).isNone do
    throwError "Fresh audit name already exists"
  match env.toKernelEnv.addDeclCore 200000000 20000
    (.thmDecl { info with name := fresh, all := [fresh] }) (cancelTk? := none) with
  | .ok checked =>
    let some (.thmInfo readback) := checked.find? fresh |
      throwError "Missing fresh theorem readback"
    unless Expr.equal readback.type info.type && Expr.equal readback.value info.value &&
        readback.levelParams == info.levelParams && readback.name == fresh &&
        readback.all == [fresh] do
      throwError "Fresh type/body/LP/name/all readback changed"
    let returnedEnv := Environment.ofKernelEnv checked
    match Kernel.check returnedEnv {} readback.value with
    | .ok inferred =>
      match Kernel.isDefEq returnedEnv {} inferred readback.type with
      | .ok true => pure ()
      | _ => throwError "Returned-environment body type changed"
    | .error _ => throwError "Returned body kernel check failed"
  | .error _ => throwError "Fresh unchanged stored-body addition failed"
  let extraFalse := Expr.forallE `extraFalse (mkConst ``False) info.type .default
  match Kernel.check env {} extraFalse with
  | .ok _ => pure ()
  | .error _ => throwError "Extra-premise control itself is ill-formed"
  match Kernel.isDefEq env {} extraFalse expectedInfo.value with
  | .ok false => pure ()
  | _ => throwError "Extra-premise control was not rejected"
  let corruptName := name.str "_corruptH101Audit"
  unless (env.find? corruptName).isNone do
    throwError "Corrupt audit name already exists"
  let corruptValue := mkConst ``True.intro
  match Kernel.check env {} corruptValue with
  | .ok inferred =>
    match Kernel.isDefEq env {} inferred info.type with
    | .ok false => pure ()
    | _ => throwError "Corrupt-body control does not isolate a different type"
  | .error _ => throwError "Corrupt control value itself is ill-formed"
  match env.toKernelEnv.addDeclCore 200000000 20000
    (.thmDecl { info with name := corruptName, all := [corruptName], value := corruptValue })
    (cancelTk? := none) with
  | .error (.declTypeMismatch ..) => pure ()
  | _ => throwError "Corrupt body was not rejected by intended type mismatch"
  for root in [name, expectedName] do
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    while !todo.isEmpty do
      let dependency := todo.back!
      todo := todo.pop
      if seen.contains dependency then continue
      let some ci := env.find? dependency |
        throwError "Missing dependency {dependency}"
      unless !ci.isUnsafe && !ci.isPartial do
        throwError "Unsafe or partial dependency {dependency}"
      seen := seen.insert dependency
      if ci.isAxiom then
        unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "Forbidden axiom {dependency}"
        axioms := axioms.insert dependency
      todo := todo ++ ci.getUsedConstantsAsSet.toList.toArray
    logInfo m!"Safe type/opaque-value closure: {root}; axioms={axioms.toList}"
  logInfo "H-101 full contract, stored body, fresh readback and controls complete; two safe closures"

end H101DirectFieldRoute.AllBaseAudit

#print axioms H101DirectFieldRoute.multiplication_etale
