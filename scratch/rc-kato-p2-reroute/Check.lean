import ZInQKernel.Contrib.OneProof.RC.KatoP2.FiniteAppE
import ZInQKernel.Contrib.OneProof.RC.KatoP2.FiniteAnchor
import ZInQKernel.Contrib.OneProof.RC.KatoP2.EvenBridge
import Lean.Util.FoldConsts

open ZInQ.Manuscript.RC.KatoP2

open ZInQ.Manuscript.RC.PrintsArith in
example (D : IwasawaData KatoLambda2) : RetainedK15 D ↔ D.Thm13_4Conclusion 2 := Iff.rfl

#print axioms retained_norm
#print axioms dyadicNorm_of_retained
#print axioms smoother_coprime_of_katoXi
#print axioms new_prime_not_dvd_base
#print axioms norm_above_kodaiBase
#print axioms map_frobUnit
#print axioms weightedEuler
#print axioms kodaiNorm_of_prop812
#print axioms kodaiNorm_prime
#print axioms commutator_fixesAbelian
#print axioms scaleFirst_coord
#print axioms scaleFirst_apply
#print axioms serre_abelian_unipotent
#print axioms serre_abelian_rankOne
#print axioms kodaiUnipotent_of_serre
#print axioms coord_transvection_baseChange
#print axioms kodaiAbsIrred_of_serre
#print axioms retained_norm_to_dyadic
#print axioms kodai07_eq_retained
#print axioms eval_mem_J
#print axioms map_J_le_of_extend
#print axioms kodai08AwayTwo_of_global
#print axioms retainedK15_of_kodai08
#print axioms finiteNorm_of_retained
#print axioms finite_e1_p2
#print axioms RetainedReciprocity.z_ne_zero_of_L_ne_zero
#print axioms anchored_weightedSum_nsmul_ne_zero_p2
#print axioms exists_nonzero_image_of_anchored_weightedSum_p2
#print axioms KodaiConstituent.retainedK15
#print axioms family_smoothers_coprime
#print axioms appEOutputs_of_katoP2
#print axioms evenScalar32_of_katoP2
#print axioms appEOutputs_of_katoP2_fixed
#print axioms evenScalar32_of_katoP2_fixed
#print axioms evenScalar32_of_katoP2_ecurve
#print axioms evenLowerBound_of_katoP2_ecurve

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let blocked : Array Name :=
    #[`ZInQ.Manuscript.RC.PrintsArith.IwasawaData.Thm13_4Conclusion,
      `ZInQ.Manuscript.RC.PrintsArith.KatoZetaLeaf,
      `ZInQ.Manuscript.RC.PrintsArith.KatoZetaInterface,
      `ZInQ.Manuscript.RC.Kato812.KatoZetaInterface812,
      `ZInQ.Manuscript.RC.Even.AppEFromKato]
  let mut todo : Array Name :=
    #[`ZInQ.Manuscript.RC.KatoP2.AppEFromKatoP2,
      `ZInQ.Manuscript.RC.KatoP2.KodaiConstituent.retainedK15,
      `ZInQ.Manuscript.RC.KatoP2.evenScalar32_of_katoP2,
      `ZInQ.Manuscript.RC.KatoP2.appEOutputs_of_katoP2_fixed,
      `ZInQ.Manuscript.RC.KatoP2.evenScalar32_of_katoP2_fixed,
      `ZInQ.Manuscript.RC.KatoP2.evenLowerBound_of_katoP2_ecurve,
      `ZInQ.Manuscript.RC.KatoP2.finite_e1_p2,
      `ZInQ.Manuscript.RC.KatoP2.exists_nonzero_image_of_anchored_weightedSum_p2]
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
