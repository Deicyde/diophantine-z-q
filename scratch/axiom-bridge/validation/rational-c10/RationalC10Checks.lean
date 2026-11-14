import RationalC10Link
import RationalC10ExpectedTypes
import Lean
import Lean.Util.FoldConsts

/-
UNCOMPILED PRIVATE VALIDATION.

Use independently compiled literal expected propositions AND the exact original
three C10-link types with only their named, typed, unused hM binder erased.
Natural-number placeholders below are NOT hM proofs: syntactic equality of two
substitutions proves that no substitution occurs. The erased expression must
then kernel-check as Prop and agree with the separate literal specification.
Numeric addDeclCore values are execution limits, not trust setters.
No complete imported-library replay or serialized-proof read is claimed.
-/

open Lean

namespace RationalC10Checks

def eraseOuterMetadata : Expr → Expr
  | .mdata _ e => eraseOuterMetadata e
  | e => e

def countOuterHM : Expr → Nat
  | .forallE n _ body _ => (if n == `hM then 1 else 0) + countOuterHM body
  | .mdata _ e => countOuterHM e
  | _ => 0

def outerBinderFlags : Expr → List BinderInfo
  | .forallE _ _ body bi => bi :: outerBinderFlags body
  | .mdata _ e => outerBinderFlags e
  | _ => []

/-- Erase exactly the explicit, named hM:original integer predicate. Reject use
of that binder in the remaining type before applying the capture-safe shift. -/
def eraseExactUnusedHM : Expr → Except String Expr
  | .forallE n ty body bi =>
    if n == `hM then
      if eraseOuterMetadata ty != mkConst `PkgI3.CharPolyIndepOfEll ||
          bi != BinderInfo.default then
        .error "The original hM has a changed type or binder flag"
      else
        let without0 := body.instantiate1 (mkNatLit 0)
        let without1 := body.instantiate1 (mkNatLit 1)
        if without0 == without1 then .ok without0
        else .error "The original hM is used in the remaining type"
    else
      match eraseExactUnusedHM body with
      | .ok rest => .ok (.forallE n ty rest bi)
      | .error msg => .error msg
  | .mdata md e =>
    match eraseExactUnusedHM e with
    | .ok rest => .ok (.mdata md rest)
    | .error msg => .error msg
  | _ => .error "The original ordered telescope contains no hM binder"

run_cmd do
  let elaboratorEnv ← getEnv
  logInfo m!"Ordinary elaborator import trustLevel={elaboratorEnv.header.trustLevel.toNat}"
  let env ← (importModules
    #[{ module := `RationalC10Link, importAll := true },
      { module := `RationalC10ExpectedTypes, importAll := true }] {}
    (trustLevel := 0) : IO Environment)
  unless env.header.trustLevel.toNat == 0 do
    throwError "The rational C10 validation import environment is not trust level zero"
  logInfo "Validation import trustLevel=0; addDeclCore limits: 200000000 heartbeats, 20000 recursion"
  for (name, expectedName) in [
      (`AxiomBridge.RationalC10Link.trace_T_of_frobCompare, ``expectedTraceT),
      (`AxiomBridge.RationalC10Link.trace_rL_of_frobCompare, ``expectedTraceRL),
      (`AxiomBridge.RationalC10Link.trace_link_three_five, ``expectedThreeFive),
      (`AxiomBridge.RationalC10Link.c10_of_trace_link, ``expectedC10TraceLink),
      (`AxiomBridge.RationalC10Link.c10_of_squares, ``expectedC10Squares)] do
    let some (.thmInfo info) := env.find? name |
      throwError "Missing actual theorem {name}"
    let some candidateIdx := env.getModuleIdxFor? name |
      throwError "The actual candidate has no defining module {name}"
    unless env.header.moduleNames[candidateIdx.toNat]! == `RationalC10Link do
      throwError "Wrong actual candidate defining module {name}"
    let some (.defnInfo expectedInfo) := env.find? expectedName |
      throwError "Missing independently written specification {expectedName}"
    let some expectedIdx := env.getModuleIdxFor? expectedName |
      throwError "The specification has no defining module {expectedName}"
    unless env.header.moduleNames[expectedIdx.toNat]! == `RationalC10ExpectedTypes do
      throwError "Wrong specification defining module {expectedName}"
    unless info.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
      throwError "Changed original Type0 universe telescope {name}"
    let expected := expectedInfo.value
    match Kernel.check env {} expected with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "The independent expected expression is not a proposition {expectedName}"
    | .error _ => throwError "The independent expected expression failed its kernel check {expectedName}"
    unless outerBinderFlags info.type == outerBinderFlags expected do
      throwError "Changed ordered outer binder flags {name}"
    logInfo m!"Actual complete type: {info.type}; levels={info.levelParams}"
    logInfo m!"Independent expected type: {expected}; levels={expectedInfo.levelParams}"
    logInfo m!"Exact outer binder flags agree; binders={(outerBinderFlags info.type).length}"
    match Kernel.isDefEq env {} info.type expected with
    | .ok true => pure ()
    | .ok false => throwError "The complete actual/expected type comparison returned false {name}"
    | .error (.unknownConstant _ unknownName) =>
      throwError "Missing constant in complete type comparison {name}: {unknownName}"
    | .error _ => throwError "Kernel complete type-comparison exception {name}"
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
    | _ => throwError "The rational consumer was confused with the integer-polynomial predicate {name}"
    let bad := Declaration.thmDecl
      { info with
        name := name.str "_corruptedBody"
        all := [name.str "_corruptedBody"]
        value := mkConst ``True.intro }
    match env.toKernelEnv.addDeclCore 200000000 20000 bad (cancelTk? := none) with
    | .error (.declTypeMismatch ..) => pure ()
    | _ => throwError "The corrupted proof was not rejected for the intended reason {name}"
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
  for (name, expectedName, originalName) in [
      (`AxiomBridge.RationalC10Link.trace_link_three_five, ``expectedThreeFive,
        `GlueC10Link.trace_link_three_five),
      (`AxiomBridge.RationalC10Link.c10_of_trace_link, ``expectedC10TraceLink,
        `GlueC10Link.c10_of_trace_link),
      (`AxiomBridge.RationalC10Link.c10_of_squares, ``expectedC10Squares,
        `GlueC10Link.c10_of_squares)] do
    let some (.thmInfo actual) := env.find? name |
      throwError "Missing candidate in original-type comparison {name}"
    let some (.defnInfo expectedInfo) := env.find? expectedName |
      throwError "Missing literal spec in original-type comparison {expectedName}"
    let some (.thmInfo original) := env.find? originalName |
      throwError "Missing original theorem {originalName}"
    let some originalIdx := env.getModuleIdxFor? originalName |
      throwError "Missing original defining module {originalName}"
    unless env.header.moduleNames[originalIdx.toNat]! == `ZInQKernel.HDecomp.C10.Link do
      throwError "Original theorem was replaced or relocated {originalName}"
    unless original.levelParams.isEmpty && countOuterHM original.type == 1 do
      throwError "Changed original universe or hM binder count {originalName}"
    let .ok erased := eraseExactUnusedHM original.type |
      throwError "Could not erase exactly the unused original hM {originalName}"
    match Kernel.check env {} erased with
    | .ok sortType =>
      match Kernel.isDefEq env {} sortType (mkSort .zero) with
      | .ok true => pure ()
      | _ => throwError "The original hM-erased expression is not Prop {originalName}"
    | .error _ => throwError "The original hM-erased expression failed its kernel check {originalName}"
    unless outerBinderFlags erased == outerBinderFlags actual.type &&
        outerBinderFlags erased == outerBinderFlags expectedInfo.value do
      throwError "Original hM-only removal changed outer binder flags {name}"
    for comparison in [actual.type, expectedInfo.value] do
      match Kernel.isDefEq env {} erased comparison with
      | .ok true => pure ()
      | _ => throwError "The complete original type minus only hM differs {name}"
    match Kernel.isDefEq env {} original.type expectedInfo.value with
    | .ok false => pure ()
    | _ => throwError "Restoring the original hM was not distinguished {name}"
    logInfo m!"Original complete ordered type minus ONLY unused hM matches candidate AND literal spec: {name}"
  for (name, definingModule) in [
      (`PkgI3.AbVar.homT, `ZInQKernel.HDecomp.Objects),
      (`PkgI3.CharPolyIndepOfEll, `ZInQKernel.HDecomp.Objects),
      (`GlueC10Link.FrobCompare, `ZInQKernel.HDecomp.C10.Link),
      (`GlueC10Link.FrobSquares, `ZInQKernel.HDecomp.C10.Link),
      (`GlueC10Link.rL, `ZInQKernel.HDecomp.C10.Link),
      (`GlueC10Link.homComp, `ZInQKernel.HDecomp.C10.Link),
      (`GlueC10Link.trace_eq_two_mul_trace_subRep, `ZInQKernel.HDecomp.C10.Link),
      (`GlueC10.c10, `ZInQKernel.HDecomp.C10.C10),
      (`GlueDescent.MatrixUnits2, `ZInQKernel.HDecomp.Descent.ProjRep),
      (`AxiomBridge.NativeEndTrace.trace_homT_scalar_extension, `NativeEndTrace)] do
    let some idx := env.getModuleIdxFor? name |
      throwError "Original supplier has no defining module {name}"
    unless env.header.moduleNames[idx.toNat]! == definingModule do
      throwError "Original supplier comes from another module {name}"
  logInfo "All rational C10 body/type/both-closure checks and exact original hM-only removals passed"

end RationalC10Checks
