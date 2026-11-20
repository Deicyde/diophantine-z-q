import ZInQKernel.Contrib.OneProof.RC.KatoP2.EvenBridgeChecked
import ZInQKernel.Contrib.OneProof.RC.KatoP2.FixedComparisonChecked
import ZInQKernel.Contrib.OneProof.RC.KatoP2.FiniteAppE
import Lean.Util.FoldConsts

open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript
open CategoryTheory NumberField IsDedekindDomain SelmerComplex CoefModules
open AppEK1

example (D : IwasawaData KatoLambda2) :
    KatoP2.RetainedK15 D ↔ D.Thm13_4Conclusion 2 := Iff.rfl

example (ℓ : ℕ) {Sig : Finset ℕ}
    (K : KatoZetaInterface (Ecurve ℓ) Sig (2 * CST.newformLevel (Ecurve ℓ)).primeFactors)
    (fam : Even.BinaryFamily (CST.newformLevel (Ecurve ℓ)))
    (μ : ∀ m : FamilyIndex fam, HasRootsOfUnity ℚ (familyPlaces fam) (m : ℕ))
    (nested : ∀ (m m' : FamilyIndex fam), (m : ℕ) ∣ (m' : ℕ) →
      cyclotomicKernel (μ m') ≤ cyclotomicKernel (μ m)) :
    KatoP2.Checked.FixedKatoFiniteComparison ℓ K.es fam μ nested ↔
      AppEK1.FixedKatoFiniteComparison ℓ K fam μ nested := Iff.rfl

open Lean Elab Command in
run_cmd do
  let privateDecls : Array (Name × Name) :=
    #[(`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.casesG),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.g_ne),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.gg),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.sign_surj),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.signB_eq),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.sign_joint_zero),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.sign_sep),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.two_ne_zero_A),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.two_not_mem_signPrime),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.sep_not_mem_signPrime),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.signPrime_height),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.sign_regular),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion,
        `ZInQ.Manuscript.RC.KatoP2.Checked.annihilate_at_sign),
      (`ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Support,
        `ZInQ.Manuscript.RC.KatoP2.Checked.localMap_comp)]
  for (mod, user) in privateDecls do
    let nm := Name.num (`_private ++ mod) 0 ++ user
    elabCommand (← `(command| #print axioms $(mkIdent nm)))

#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.isTorsion_of_kodaiLocal
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.exists_regular_annihilator_of_kodaiLocal
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.kodaiPurity_of_quadratic
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.kodai08_globalTorsion
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.retainedK15_of_kodai08
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.KodaiConstituent.retainedK15
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.appEOutputs_of_katoP2
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.appEOutputs_of_katoP2_fixed
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2_fixed
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2_ecurve
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.evenLowerBound_of_katoP2_ecurve
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.exists_nonzero_image_of_anchored_weightedSum_p2
#print axioms ZInQ.Manuscript.RC.KatoP2.Checked.KatoOddSupportCone.toComparison

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `ZInQKernel.OneProof.Main then
    throwError "Imports the frozen main theorem"
  let blocked : Array Name :=
    #[`ZInQ.Manuscript.RC.PrintsArith.IwasawaData.Thm13_4Conclusion,
      `ZInQ.Manuscript.RC.PrintsArith.KatoZetaLeaf,
      `ZInQ.Manuscript.RC.PrintsArith.KatoZetaInterface,
      `ZInQ.Manuscript.RC.Kato812.KatoZetaInterface812,
      `ZInQ.Manuscript.RC.Even.AppEFromKato,
      `ZInQ.Manuscript.RC.KatoP2.KatoKodai99Thm08Print,
      `ZInQ.Manuscript.RC.KatoP2.Kodai08AwayTwo,
      `ZInQ.Manuscript.RC.KatoP2.KatoSupportComparison,
      `ZInQ.Manuscript.RC.KatoP2.retainedK15_of_kodai08,
      `ZInQ.Manuscript.RC.KatoP2.AppEFromKatoP2,
      `ZInQ.Manuscript.RC.KatoP2.kodai08AwayTwo_of_global]
  let mut todo : Array Name :=
    #[`ZInQ.Manuscript.RC.KatoP2.Checked.KatoKodai99Thm08Print,
      `ZInQ.Manuscript.RC.KatoP2.Checked.AppEFromKatoP2,
      `ZInQ.Manuscript.RC.KatoP2.Checked.KodaiConstituent.retainedK15,
      `ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2,
      `ZInQ.Manuscript.RC.KatoP2.Checked.appEOutputs_of_katoP2_fixed,
      `ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2_fixed,
      `ZInQ.Manuscript.RC.KatoP2.Checked.evenScalar32_of_katoP2_ecurve,
      `ZInQ.Manuscript.RC.KatoP2.Checked.evenLowerBound_of_katoP2_ecurve,
      `ZInQ.Manuscript.RC.KatoP2.finite_e1_p2,
      `ZInQ.Manuscript.RC.KatoP2.Checked.exists_nonzero_image_of_anchored_weightedSum_p2]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let dep := todo.back!
    todo := todo.pop
    if seen.contains dep then continue
    seen := seen.insert dep
    if blocked.contains dep then
      throwError "legacy dyadic dependency: {dep}"
    let some c := env.find? dep | throwError "unknown dependency in closure: {dep}"
    for n in c.getUsedConstantsAsSet do
      if !seen.contains n then todo := todo.push n
  logInfo "No legacy dyadic dependency in the replacement entry points."
