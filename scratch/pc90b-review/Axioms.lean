import ZInQKernel.OneProof.Main
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import ZInQKernel.Hypotheses.PoleManuscript
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_GenusOnePic0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem

open Lean Elab Command

#check @ZInQ.OneProof.frozenTarget
#check ZInQ.Manuscript.PoleS12.kummerSelmerM
#print ZInQ.Manuscript.PoleS12.KummerSelmerM
#print axioms ZInQ.OneProof.frozenTarget
#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
#print axioms ZInQ.Manuscript.PoleS12.kummerSelmerM
#print axioms ZInQ.Manuscript.PoleS12.poleCompleteness_of_restrictedConverseGenuine_final
#print axioms ZInQ.Manuscript.PoleRC.kummerSelmerM_proof

/-- every declaration of the modules the five commits touch: report its axioms if nonstandard -/
elab "#scan_modules" : command => do
  let env ← getEnv
  let mods : List Name := [`ZInQKernel.OneProof.Main, `ZInQKernel.Contrib.OneProof.PoleS12.Leaves,
    `ZInQKernel.Hypotheses.PoleManuscript,
    `ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_GenusOnePic0,
    `ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_dualEndData_dual_mem_and_norm_eq_finrankAlong,
    `ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem]
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  for m in mods do
    let some idx := env.getModuleIdx? m | logInfo m!"module not found {m}"
    let mut n := 0
    let mut bad := 0
    let mut placeHits : Array Name := #[]
    for (c, ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? c == some idx then
        if c.isInternal then continue
        n := n + 1
        if (c.toString.splitOn "placeDivisorSum").length > 1 then placeHits := placeHits.push c
        let ax ← Lean.collectAxioms c
        let nonstd := ax.filter (fun a => !std.contains a)
        if !nonstd.isEmpty then
          bad := bad + 1
          logInfo m!"NONSTANDARD {c}: {nonstd}"
        let _ := ci
    logInfo m!"{m}: {n} declarations scanned, {bad} with nonstandard axioms; names with placeDivisorSum: {placeHits}"

#scan_modules
