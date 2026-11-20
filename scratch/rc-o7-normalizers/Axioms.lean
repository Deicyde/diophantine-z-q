import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Assembly

open Lean Elab Command

/-- Run the ordinary axiom printer on a private constant's internal name. -/
elab "#print_private_axioms " internal:str : command => do
  let name := (internal.getString.splitOn ".").foldl
    (fun name part => match part.toNat? with
      | some n => name.num n
      | none => name.str part) Name.anonymous
  let cmd ← `(#print axioms $(mkCIdent name):ident)
  elabCommand cmd


-- Local
#print axioms ZInQ.Manuscript.RC.O7Normalizers.detectingPrime
#print axioms ZInQ.Manuscript.RC.O7Normalizers.rightConj
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitUnit
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionUnit
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitUnit_chart
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionUnit_chart
#print axioms ZInQ.Manuscript.RC.O7Normalizers.map_rightConj
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitUnit_mem
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionUnit_mem
#print axioms ZInQ.Manuscript.RC.O7Normalizers.split_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.division_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.swap_matrix
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap_cast
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap_trace
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap_det
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap_level
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitSwap_weight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.division_red_neg

-- Transport
#print axioms ZInQ.Manuscript.RC.O7Normalizers.root
#print axioms ZInQ.Manuscript.RC.O7Normalizers.root_injective
#print axioms ZInQ.Manuscript.RC.O7Normalizers.rationalConj_apply
#print axioms ZInQ.Manuscript.RC.O7Normalizers.root_conj
#print axioms ZInQ.Manuscript.RC.O7Normalizers.rationalConj_comp
#print axioms ZInQ.Manuscript.RC.O7Normalizers.atRep_root
#print axioms ZInQ.Manuscript.RC.O7Normalizers.AdelicPoint
#print axioms ZInQ.Manuscript.RC.O7Normalizers.AdelicPoint.eq_of_fields
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointRel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.AdelicOrbits
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointRel_atRep
#print axioms ZInQ.Manuscript.RC.O7Normalizers.PreservesOrder
#print axioms ZInQ.Manuscript.RC.O7Normalizers.preservesOrder_single
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Transport.0.ZInQ.Manuscript.RC.O7Normalizers.inverse_conj_mem"
#print axioms ZInQ.Manuscript.RC.O7Normalizers.PreservesOrder.inv
#print axioms ZInQ.Manuscript.RC.O7Normalizers.PreservesOrder.normalizes
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stepPoint
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stepPoint_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.adelicMove
#print axioms ZInQ.Manuscript.RC.O7Normalizers.adelicClass
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stepPoint_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.ActualPoint
#print axioms ZInQ.Manuscript.RC.O7Normalizers.supportOfPoint
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOfSupport
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOfSupport_root
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOfSupport_generator
#print axioms ZInQ.Manuscript.RC.O7Normalizers.supportOfPoint_inverse
#print axioms ZInQ.Manuscript.RC.O7Normalizers.chosen_pointRel_iff
#print axioms ZInQ.Manuscript.RC.O7Normalizers.toAdelic
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointRel_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOfSupport_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.adelicOrbitsEquiv
#print axioms ZInQ.Manuscript.RC.O7Normalizers.orbitMove
#print axioms ZInQ.Manuscript.RC.O7Normalizers.orbitMove_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.orbitMove_class

-- Norm
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitUnit_valuation
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionUnit_valuation
#print axioms ZInQ.Manuscript.RC.O7Normalizers.discriminant_product
#print axioms ZInQ.Manuscript.RC.O7Normalizers.norm_single

-- Orientation
#print axioms ZInQ.Manuscript.RC.O7Normalizers.generator
#print axioms ZInQ.Manuscript.RC.O7Normalizers.generator_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.label_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitLabel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionLabel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOrientation
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOrientation_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointOrientation_actual
#print axioms ZInQ.Manuscript.RC.O7Normalizers.levelPrime_injective
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitAdele
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionAdele
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitAdele_order
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionAdele_order
#print axioms ZInQ.Manuscript.RC.O7Normalizers.generator_away
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitAdele_chart
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Orientation.0.ZInQ.Manuscript.RC.O7Normalizers.orderChart_cast"
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionOrderChart_compatible
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionAdele_chart
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitLabel_distinct
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionRoot_trace
#print axioms ZInQ.Manuscript.RC.O7Normalizers.divisionLabel_distinct
#print axioms ZInQ.Manuscript.RC.O7Normalizers.residueBit_flip
#print axioms ZInQ.Manuscript.RC.O7Normalizers.split_orientation
#print_private_axioms "_private.ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Orientation.0.ZInQ.Manuscript.RC.O7Normalizers.affine_map"
#print axioms ZInQ.Manuscript.RC.O7Normalizers.division_orientation

-- Weights
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointWeight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.pointWeight_rel
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stepPoint_schwartz
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stepPoint_weight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.splitFactor_on_point
#print axioms ZInQ.Manuscript.RC.O7Normalizers.split_schwartz
#print axioms ZInQ.Manuscript.RC.O7Normalizers.division_schwartz
#print axioms ZInQ.Manuscript.RC.O7Normalizers.division_local_schwartz

-- Assembly
#print axioms ZInQ.Manuscript.RC.O7Normalizers.flip_involutive
#print axioms ZInQ.Manuscript.RC.O7Normalizers.fiberPerm
#print axioms ZInQ.Manuscript.RC.O7Normalizers.fiberPerm_apply
#print axioms ZInQ.Manuscript.RC.O7Normalizers.geometrySigns
#print axioms ZInQ.Manuscript.RC.O7Normalizers.geometrySigns_spec
#print axioms ZInQ.Manuscript.RC.O7Normalizers.cusp_of_multiple
#print axioms ZInQ.Manuscript.RC.O7Normalizers.stageAt
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualStageAt
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualBridge
#print axioms ZInQ.Manuscript.RC.O7Normalizers.levelDivisor
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_disc_neg
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_disc_split
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_disc_detecting
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualOrientationBridge
#print axioms ZInQ.Manuscript.RC.O7Normalizers.supportOrbitWeight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.supportOrbitWeight_mk
#print axioms ZInQ.Manuscript.RC.O7Normalizers.orbitWeight_eq_supportOrbitWeight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualOrbits
#print axioms ZInQ.Manuscript.RC.O7Normalizers.atkinMove
#print axioms ZInQ.Manuscript.RC.O7Normalizers.uniformizerMove
#print axioms ZInQ.Manuscript.RC.O7Normalizers.atkinMove_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.uniformizerMove_class
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualPhase
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualNorm
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actualFactors
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_weight_mk
#print axioms ZInQ.Manuscript.RC.O7Normalizers.level_symbol
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_atkin_weight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.actual_uniformizer_weight
#print axioms ZInQ.Manuscript.RC.O7Normalizers.normalizers
#print axioms ZInQ.Manuscript.RC.O7Normalizers.ofPicardFibers
