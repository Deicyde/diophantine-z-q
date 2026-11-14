/-
Resultant integrality tests and exact contract/body checks.
AI-assisted development; no change to the mathematical declarations.
Checking-add resource limits are not trust levels; closure walks are not library replay.
-/

import ZInQKernel.Contrib.ResultantIntegrality.Basic
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases
import ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteExpected
import Lean
import Lean.Util.FoldConsts
set_option autoImplicit false
set_option pp.all true
open Lean
namespace ResultantIntegralitySuiteKernelChecks
def outerBinderFlags : Expr → List BinderInfo
  | .forallE _ _ body bi => bi :: outerBinderFlags body
  | .mdata _ e => outerBinderFlags e
  | _ => []
run_cmd do
  let ordinary ← getEnv
  logInfo m!"Ordinary elaborator header trustLevel={ordinary.header.trustLevel.toNat}; not the validation import"
  let env ← (importModules
    #[{ module := `ZInQKernel.Contrib.ResultantIntegrality.Basic, importAll := true },
      { module := `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases, importAll := true },
      { module := `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteExpected, importAll := true }] {}
    (trustLevel := 0) : IO Environment)
  unless env.header.trustLevel.toNat == 0 do
    throwError "Validation import is not trust level zero"
  logInfo "Validation import trustLevel=0; addDeclCore resource limits: 200000000 heartbeats / 20000 recursion"
  for (name, definingModule) in [
      (`Polynomial.resultant, `Mathlib.RingTheory.Polynomial.Resultant.Basic),
      (`Polynomial.resultant_map_map, `Mathlib.RingTheory.Polynomial.Resultant.Basic),
      (`Polynomial.natDegree_map_of_leadingCoeff_ne_zero, `Mathlib.Algebra.Polynomial.Eval.Degree),
      (`ResultantIntegralityCases.intMap_natDegree, `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityPositiveCases),
      (`ResultantIntegralityCases.intMap_resultant, `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityPositiveCases),
      (`ResultantIntegralityCases.allIntegerResultants_of_intLift, `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralityPositiveCases)] do
    let some _ := env.find? name |
      throwError "Actual original API/genuine-input supplier is absent {name}"
    let some idx := env.getModuleIdxFor? name |
      throwError "Original resultant API/genuine-input supplier has no defining module {name}"
    unless env.header.moduleNames[idx.toNat]? == some definingModule do
      throwError "Original resultant API was replaced: {name}"
  for (name, definingModule, expectedName) in [
      (`PrivateResultantIntegrality.integerPolynomial_of_integral_resultants,
        `ZInQKernel.Contrib.ResultantIntegrality.Basic,
        `ResultantIntegralitySuiteExpected.expectedIntegerReflection),
      (`ResultantIntegralitySuiteCases.genuineIntegerInputs,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedGenuineIntegerInputs),
      (`ResultantIntegralitySuiteCases.positiveOne,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedPositiveOne),
      (`ResultantIntegralitySuiteCases.positiveX,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedPositiveX),
      (`ResultantIntegralitySuiteCases.positiveQuadratic,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedPositiveQuadratic),
      (`ResultantIntegralitySuiteCases.positiveRepeated,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedPositiveRepeated),
      (`ResultantIntegralitySuiteCases.positiveReductionDegree,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedPositiveReductionDegree),
      (`ResultantIntegralitySuiteCases.constantReductionDegree,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedConstantReductionDegree),
      (`ResultantIntegralitySuiteCases.adverseLinear,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedAdverseLinear),
      (`ResultantIntegralitySuiteCases.adverseQuadratic,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedAdverseQuadratic),
      (`ResultantIntegralitySuiteCases.adverseCubic,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedAdverseCubic),
      (`ResultantIntegralitySuiteCases.strictBoundCounterexample,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedStrictBoundCounterexample),
      (`ResultantIntegralitySuiteCases.noMonicityCounterexample,
        `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteCases,
        `ResultantIntegralitySuiteExpected.expectedNoMonicityCounterexample)] do
    let some (.thmInfo info) := env.find? name |
      throwError "Missing actual theorem {name}"
    unless info.name == name do
      throwError "Stored theorem name differs {name}"
    let some candidateIdx := env.getModuleIdxFor? name |
      throwError "Actual theorem has no defining module {name}"
    unless env.header.moduleNames[candidateIdx.toNat]? == some definingModule do
      throwError "Wrong actual defining module {name}"
    let some (.defnInfo expectedInfo) := env.find? expectedName |
      throwError "Missing independent literal specification {expectedName}"
    let some expectedIdx := env.getModuleIdxFor? expectedName |
      throwError "Independent specification has no defining module {expectedName}"
    unless env.header.moduleNames[expectedIdx.toNat]? == some `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteExpected do
      throwError "Wrong independent specification defining module {expectedName}"
    unless info.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
      throwError "Changed concrete Type0 telescope: expected LP[] {name}"
    let expected := expectedInfo.value
    match Kernel.check env {} expected with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "Independent expected value is not Prop {expectedName}"
    | .error _ => throwError "Independent expected value failed kernel check {expectedName}"
    let freshExpected := expectedName.str "_freshLiteralExpectedCheck"
    unless (env.find? freshExpected).isNone do
      throwError "Fresh independent expected name already present {freshExpected}"
    match env.toKernelEnv.addDeclCore 200000000 20000
      (.defnDecl { expectedInfo with name := freshExpected, all := [freshExpected] })
      (cancelTk? := none) with
    | .ok checkedExpected =>
      let some (.defnInfo readbackExpected) := checkedExpected.find? freshExpected |
        throwError "Fresh expected readback is not an actual definition {freshExpected}"
      unless Expr.equal readbackExpected.type expectedInfo.type &&
          Expr.equal readbackExpected.value expectedInfo.value &&
          readbackExpected.levelParams == expectedInfo.levelParams &&
          readbackExpected.levelParams.isEmpty && readbackExpected.name == freshExpected &&
          readbackExpected.all == [freshExpected] &&
          readbackExpected.safety == expectedInfo.safety do
        throwError "Fresh independent expected type/value/LP/name/all/safety changed {expectedName}"
      let freshExpectedEnv := Environment.ofKernelEnv checkedExpected
      match Kernel.check freshExpectedEnv {} readbackExpected.value with
      | .ok sortType =>
        match Kernel.isDefEq freshExpectedEnv {} sortType (mkSort .zero) with
        | .ok true => pure ()
        | _ => throwError "Fresh independent expected value is not Prop {expectedName}"
      | .error _ => throwError "Fresh independent expected value kernel check failed {expectedName}"
    | .error _ => throwError "Fresh independent expected LP[] re-add failed {expectedName}"
    unless outerBinderFlags info.type == outerBinderFlags expected do
      throwError "Changed ordered outer binder flags {name}"
    logInfo m!"Actual complete type: {info.type}; LP={info.levelParams}"
    logInfo m!"Independent literal expected value: {expected}; LP={expectedInfo.levelParams}"
    logInfo m!"Ordered outer binder flags agree; count={(outerBinderFlags info.type).length}"
    match Kernel.isDefEq env {} info.type expected with
    | .ok true => pure ()
    | .ok false => throwError "Complete actual/expected comparison false {name}"
    | .error (.unknownConstant _ unknownName) =>
      throwError "Unknown constant in full type comparison {name}: {unknownName}"
    | .error _ => throwError "Kernel complete type-comparison exception {name}"
    match Kernel.check env {} info.value with
    | .ok inferred =>
      match Kernel.isDefEq env {} inferred info.type with
      | .ok true => pure ()
      | _ => throwError "Actual stored body has different inferred type {name}"
    | .error _ => throwError "Actual stored body rejected {name}"
    let fresh := name.str "_freshStoredBodyCheck"
    unless (env.find? fresh).isNone do
      throwError "Fresh actual-body name is already present {fresh}"
    match env.toKernelEnv.addDeclCore 200000000 20000
      (.thmDecl { info with name := fresh, all := [fresh] }) (cancelTk? := none) with
    | .ok checked =>
      let some (.thmInfo readbackInfo) := checked.find? fresh |
        throwError "Fresh readback is not an actual theorem {fresh}"
      unless Expr.equal readbackInfo.type info.type && Expr.equal readbackInfo.value info.value &&
          readbackInfo.levelParams == info.levelParams && readbackInfo.levelParams.isEmpty &&
          readbackInfo.name == fresh && readbackInfo.all == [fresh] do
        throwError "Fresh stored expression/type/value/LP/name/all changed {name}"
      let freshEnv := Environment.ofKernelEnv checked
      match Kernel.check freshEnv {} readbackInfo.type with
      | .ok sortType =>
        match Kernel.isDefEq freshEnv {} sortType (mkSort .zero) with
        | .ok true => pure ()
        | _ => throwError "Fresh stored type is not Prop {name}"
      | .error _ => throwError "Fresh stored type kernel check failed {name}"
      match Kernel.check freshEnv {} readbackInfo.value with
      | .ok inferred =>
        match Kernel.isDefEq freshEnv {} inferred readbackInfo.type with
        | .ok true => pure ()
        | _ => throwError "Fresh actual returned-environment body/type readback mismatch {name}"
      | .error _ => throwError "Fresh readback body rejected {name}"
    | .error _ => throwError "Fresh actual-body re-add rejected {name}"
    let extraFalse := Expr.forallE `extraFalse (mkConst ``False) info.type .default
    match Kernel.check env {} extraFalse with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "Extra-False control is not Prop {name}"
    | .error _ => throwError "Extra-False control kernel check failed {name}"
    match Kernel.isDefEq env {} extraFalse expected with
    | .ok false => pure ()
    | _ => throwError "Extra-False premise control was not rejected {name}"
    let corruptName := name.str "_corruptedStoredBodyControl"
    unless (env.find? corruptName).isNone do
      throwError "Corrupt control name is already present {corruptName}"
    let corruptValue := mkConst ``True.intro
    match Kernel.check env {} corruptValue with
    | .ok corruptType =>
      match Kernel.isDefEq env {} corruptType info.type with
      | .ok false => pure ()
      | _ => throwError "Corrupt value does not isolate the intended different type {name}"
    | .error _ => throwError "Corrupt control value itself failed kernel check {name}"
    let corrupt := Declaration.thmDecl
      { info with name := corruptName, all := [corruptName], value := corruptValue }
    match env.toKernelEnv.addDeclCore 200000000 20000 corrupt (cancelTk? := none) with
    | .error (.declTypeMismatch ..) => pure ()
    | _ => throwError "Corrupt body was not rejected for intended type-mismatch reason {name}"
    let allowed := [`propext, `Classical.choice, `Quot.sound]
    for root in [name, expectedName] do
      let mut todo := #[root]
      let mut seen : NameSet := {}
      let mut axioms : NameSet := {}
      while !todo.isEmpty do
        let dependency := todo.back!
        todo := todo.pop
        if seen.contains dependency then continue
        let some ci := env.find? dependency |
          throwError "Missing type/opaque-body dependency {dependency}"
        unless !ci.isUnsafe && !ci.isPartial do
          throwError "Unsafe/partial type/opaque-body dependency {dependency}"
        seen := seen.insert dependency
        if ci.isAxiom then
          unless allowed.contains dependency do
            throwError "Forbidden type/opaque-body axiom {dependency}"
          axioms := axioms.insert dependency
        todo := todo ++ ci.getUsedConstantsAsSet.toList.toArray
      logInfo m!"Both-type/opaque-value safe closure: {root}; visited={seen.toList.length}; axioms={axioms.toList}"
    logInfo m!"Actual full-type/body/readback/control checks completed: {name}"
  let some (.defnInfo frozenInfo) := env.find?
    `ResultantIntegralitySuiteExpected.expectedIntegerReflection |
    throwError "Missing independent main expected value for controls"
  let some (.thmInfo mainInfo) := env.find?
    `PrivateResultantIntegrality.integerPolynomial_of_integral_resultants |
    throwError "Missing actual main theorem for wrong-type controls"
  unless outerBinderFlags frozenInfo.value == [.default, .default, .default] do
    throwError "Independent main literal no longer has the three explicit outer binders"
  for controlName in [
      `ResultantIntegralitySuiteExpected.strictDegreeReflection,
      `ResultantIntegralitySuiteExpected.monicityDroppedReflection,
      `ResultantIntegralitySuiteExpected.outputMonicityDroppedReflection,
      `ResultantIntegralitySuiteExpected.monicTestsOnlyReflection] do
    let some (.defnInfo controlInfo) := env.find? controlName |
      throwError "Missing literal adverse-type control {controlName}"
    let some controlIdx := env.getModuleIdxFor? controlName |
      throwError "Literal adverse-type control has no defining module {controlName}"
    unless env.header.moduleNames[controlIdx.toNat]? == some `ZInQKernel.Contrib.ResultantIntegrality.ResultantIntegralitySuiteExpected &&
        controlInfo.levelParams.isEmpty do
      throwError "Literal adverse-type control ownership/LP changed {controlName}"
    match Kernel.check env {} controlInfo.value with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "Adverse-type control is not Prop {controlName}"
    | .error _ => throwError "Adverse-type control kernel check failed {controlName}"
    match Kernel.isDefEq env {} controlInfo.value frozenInfo.value with
    | .ok false => pure ()
    | _ => throwError "Changed contract was not rejected for intended non-defeq reason {controlName}"
    match Kernel.isDefEq env {} mainInfo.type controlInfo.value with
    | .ok false => pure ()
    | _ => throwError "Actual complete main type did not reject wrong literal {controlName}"
    let wrongTypeName := controlName.str "_actualMainBodyWrongTypeControl"
    unless (env.find? wrongTypeName).isNone do
      throwError "Wrong-type control name already present {wrongTypeName}"
    let wrongTypeDecl := Declaration.thmDecl
      { mainInfo with name := wrongTypeName, all := [wrongTypeName], type := controlInfo.value }
    match env.toKernelEnv.addDeclCore 200000000 20000 wrongTypeDecl (cancelTk? := none) with
    | .error (.declTypeMismatch ..) => pure ()
    | _ => throwError "Unchanged actual body/wrong literal did not fail for intended type-mismatch reason {controlName}"
    logInfo m!"Different literal and actual-body wrong-type controls completed: {controlName}; outerFlagCount={(outerBinderFlags controlInfo.value).length}"
  logInfo "Private resultant suite checks completed; imported-library raw replay and proof serialization were not performed"
end ResultantIntegralitySuiteKernelChecks
