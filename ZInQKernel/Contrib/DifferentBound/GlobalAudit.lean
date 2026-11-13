import ZInQKernel.Contrib.DifferentBound.SerreGlobal
import Lean.Replay

/-!
# Focused exact-type and standard-axiom check for the closed global declaration

The ordinary Lean compilation checks the theorem proof. The command below also
checks the stored declaration's literal type and absence of universe parameters,
not merely a printed or definitionally related conditional statement. Full
candidate dependency replay and independent acceptance remain the integrator's
separate duties.
-/

open NumberField
open ZInQ.Contrib.DifferentBound

run_cmd do
  let info ← Lean.getConstInfo `ZInQ.Contrib.DifferentBound.serreDifferentBound
  unless info.levelParams.isEmpty do
    throwError "The global provider has unexpected universe parameters"
  unless info.type == Lean.mkConst `GlueConductor.SerreDifferentBound do
    throwError "The stored global provider type is not exactly the unchanged baseline proposition"
  let .thmInfo theoremInfo := info |
    throwError "The global provider is not a theorem declaration"
  Lean.logInfo "EXACT STORED TYPE: GlueConductor.SerreDifferentBound; universe parameters: []"
  let env ← Lean.getEnv
  let freshName := `ZInQ.Contrib.DifferentBound._focusedGlobalKernelRecheck
  unless (env.find? freshName).isNone do
    throwError "The fresh kernel-check name is already in use"
  -- Check the actual serialized proof body again under a fresh theorem name,
  -- with the kernel's trust level zero. This does not introduce a proof supplier
  -- or change the environment used to prove the global theorem.
  let declaration := Lean.Declaration.thmDecl
    { theoremInfo with name := freshName, all := [freshName] }
  match env.toKernelEnv.addDeclCore 0 0 declaration (cancelTk? := none) with
  | .ok _ => Lean.logInfo "KERNEL RECHECK: actual global theorem proof body passed at trust level 0"
  | .error _ => throwError "Lean kernel rejected the actual global theorem proof body"

-- This application is checked by the Lean kernel at precisely the baseline's closed type.
example : GlueConductor.SerreDifferentBound := serreDifferentBound

set_option pp.universes true in
#check @serreDifferentBound
#print GlueConductor.SerreDifferentBound
#print axioms serreDifferentBound
#print axioms numberFieldDifferentMultiplicityBound
#print axioms fixedFieldLocalDifferentBound
#print axioms fixedFieldDifferentMultiplicityBound
#print axioms fixedFieldLocal_multiplicity_natCast
#print axioms integersEquiv
#print axioms map_absoluteDifferent_equiv
#print axioms multiplicity_absoluteDifferent_equiv
#print axioms ramificationIdx_integersEquiv
#print axioms Presentation.equiv

-- All p, including the dyadic prime, are instances of the same exact universal theorem.
example (L : Type) [Field L] [NumberField L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(2 : ℤ)})) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat 2 (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound L 2 Nat.prime_two P hP

-- Number fields need not be Galois. No Galois instance occurs in this specialization's type.
example (L : Type) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P.LiesOver (Ideal.span {(p : ℤ)})) :
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L) :=
  serreDifferentBound L p hp P hP
