import NativeEndTrace
import NativeEndTraceExpectedTypes
import Lean
import Lean.Util.FoldConsts

/-
UNRUN PRIVATE VALIDATION.

The independently written specification is separately compiled and imported as
data alongside the candidate. All comparisons/body checks use the explicitly
recorded trust-zero environment. This checks the bounded rational propositions,
not the stronger integer-polynomial predicate or the whole external library.
-/

open Lean

namespace NativeEndTraceChecks

run_cmd do
  let elaboratorEnv ← getEnv
  logInfo m!"Ordinary elaborator import trustLevel={elaboratorEnv.header.trustLevel.toNat}"
  let env ← (importModules
    #[{ module := `NativeEndTrace, importAll := true },
      { module := `NativeEndTraceExpectedTypes, importAll := true }] {}
    (trustLevel := 0) : IO Environment)
  unless env.header.trustLevel.toNat == 0 do
    throwError "The EndTrace validation import environment is not trust level zero"
  logInfo "Validation import trustLevel=0; addDeclCore limits: 200000000 heartbeats, 20000 recursion"
  for (name, expectedName) in [
      (`AxiomBridge.NativeEndTrace.geometricEnd_natural, ``expectedNaturality),
      (`AxiomBridge.NativeEndTrace.conjugate_homT, ``expectedConjugacy),
      (`AxiomBridge.NativeEndTrace.rationalCharPoly_monic, ``expectedMonic),
      (`AxiomBridge.NativeEndTrace.charpoly_homT_baseChange, ``expectedRationalCharPoly),
      (`AxiomBridge.NativeEndTrace.trace_homT_baseChange, ``expectedRationalTrace),
      (`AxiomBridge.NativeEndTrace.trace_homT_scalar_extension, ``expectedScalarTrace),
      (`AxiomBridge.NativeEndTrace.exists_common_coefficient_trace, ``expectedCommonCoefficient)] do
    let some (.thmInfo info) := env.find? name |
      throwError "Missing actual theorem {name}"
    let some candidateIdx := env.getModuleIdxFor? name |
      throwError "The actual candidate has no defining module {name}"
    unless env.header.moduleNames[candidateIdx.toNat]! == `NativeEndTrace do
      throwError "Wrong actual candidate defining module {name}"
    let some (.defnInfo expectedInfo) := env.find? expectedName |
      throwError "Missing independently written specification {expectedName}"
    let some expectedIdx := env.getModuleIdxFor? expectedName |
      throwError "The specification has no defining module {expectedName}"
    unless env.header.moduleNames[expectedIdx.toNat]! == `NativeEndTraceExpectedTypes do
      throwError "Wrong specification defining module {expectedName}"
    unless info.levelParams.length == expectedInfo.levelParams.length do
      throwError "Changed universe telescope {name}"
    let expected := expectedInfo.value.instantiateLevelParams expectedInfo.levelParams
      (info.levelParams.map Level.param)
    match Kernel.check env {} expected with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "The independent expected expression is not a proposition {expectedName}"
    | .error _ => throwError "The independent expected expression failed its kernel check {expectedName}"
    logInfo m!"Actual complete type: {info.type}; levels={info.levelParams}"
    logInfo m!"Independent expected type: {expected}; levels={expectedInfo.levelParams}"
    match Kernel.isDefEq env {} info.type expected with
    | .ok true => pure ()
    | .ok false => throwError "The complete actual/expected type comparison returned false {name}"
    | .error (.unknownConstant _ unknownName) =>
      throwError "Missing constant in complete type comparison {name}: {unknownName}"
    | .error (.other msg) => throwError "Kernel type-comparison error {name}: {msg}"
    | .error _ => throwError "Kernel type-comparison exception {name}; full expressions are logged"
    match Kernel.check env {} info.value with
    | .ok inferred =>
      match Kernel.isDefEq env {} inferred info.type with
      | .ok true => pure ()
      | _ => throwError "The actual stored proof body has a different inferred type {name}"
    | .error _ => throwError "The actual stored proof body was rejected {name}"
    let fresh := name.str "_freshStoredBodyCheck"
    unless (env.find? fresh).isNone do
      throwError "Fresh body-check name already present {fresh}"
    match env.toKernelEnv.addDeclCore 200000000 20000
      (.thmDecl { info with name := fresh, all := [fresh] }) (cancelTk? := none) with
    | .ok checked =>
      let some stored := checked.find? fresh |
        throwError "Fresh actual-body declaration missing {fresh}"
      unless stored.type == info.type && stored.value? true == some info.value &&
          stored.levelParams == info.levelParams do
        throwError "Fresh actual-body addition changed the stored type/value/universes {name}"
    | .error _ => throwError "Fresh actual-body addition was rejected {name}"
    let extra := Expr.forallE `unprovedInput (mkConst ``False) info.type .default
    match Kernel.isDefEq env {} extra expected with
    | .ok false => pure ()
    | _ => throwError "The extra-premise control was not rejected {name}"
    match Kernel.isDefEq env {} info.type (mkConst `PkgI3.CharPolyIndepOfEll) with
    | .ok false => pure ()
    | _ => throwError "The bounded rational theorem was confused with the whole integer-polynomial predicate {name}"
    let bad := Declaration.thmDecl
      { info with
        name := name.str "_corruptedBody"
        all := [name.str "_corruptedBody"]
        value := mkConst ``True.intro }
    match env.toKernelEnv.addDeclCore 200000000 20000 bad (cancelTk? := none) with
    | .error (.declTypeMismatch ..) => pure ()
    | _ => throwError "The corrupted proof was not rejected for the intended reason {name}"
    let allowed := [`propext, `Classical.choice, `Quot.sound]
    -- Walk each actual candidate AND independent specification's type/value
    -- closure. This is an axiom/safety walk, not kernel replay of every import.
    for root in [name, expectedName] do
      let mut todo := #[root]
      let mut seen : NameSet := {}
      let mut axioms : NameSet := {}
      while !todo.isEmpty do
        let dependency := todo.back!
        todo := todo.pop
        if seen.contains dependency then continue
        let some ci := env.find? dependency |
          throwError "Missing type/body dependency {dependency}"
        unless !ci.isUnsafe && !ci.isPartial do
          throwError "Unsafe/partial type/body dependency {dependency}"
        seen := seen.insert dependency
        if ci.isAxiom then
          unless allowed.contains dependency do
            throwError "Forbidden type/body axiom {dependency}"
          axioms := axioms.insert dependency
        todo := todo ++ ci.getUsedConstantsAsSet.toList.toArray
      logInfo m!"Axiom/safety closure: {root}; visited={seen.toList.length}; axioms={axioms.toList}"
    logInfo m!"Complete expected type, actual body, stored re-add identity and negative controls passed: {name}"
  for (name, definingModule) in [
      (`PkgI3.AbVar.homT, `ZInQKernel.HDecomp.Objects),
      (`geometricTateEquiv, `ComposedPointTateSmoke),
      (`baseChangedHom, `ComposedPointTateSmoke),
      (`AxiomBridge.TateConsumer.tate_free_finite, `TateFreeness),
      (`Stacks.Groupoids.charpoly_tateModuleMap,
        `StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CharPoly)] do
    let some idx := env.getModuleIdxFor? name |
      throwError "Original supplier has no defining module {name}"
    unless env.header.moduleNames[idx.toNat]! == definingModule do
      throwError "Original supplier comes from another module {name}"
  logInfo "All bounded EndTrace comparisons and original supplier-module identities passed"

end NativeEndTraceChecks
