import Lean
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.ActualLocal
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.CurveAtPlace
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Evaluation
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.FiniteReduction
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.PointReduction
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Restriction
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Specialize
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Torsion
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.TwistAtPlace
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Valuation

set_option pp.notation false
set_option pp.explicit true

-- Resolve imported private names by their defining module.
open Lean Elab Command in
elab "#check_private" mod:ident name:ident : command => do
  let id := mkIdent (mkPrivateNameCore mod.getId name.getId)
  elabCommand (← `(#check @$id))

-- ActualLocal.lean
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.ActualLocal ZInQ.Manuscript.RC.WitnessSpec.torsionMap_equiv
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.ActualLocal ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.reduced_elliptic
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.ActualLocal ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.two_ne_zero_residue
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localStage
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localStage_red

-- CurveAtPlace.lean
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.CurveAtPlace ZInQ.Manuscript.RC.WitnessSpec.integralEquation_baseChange
#check @ZInQ.Manuscript.RC.WitnessSpec.integralEquation_isIntegral
#check @ZInQ.Manuscript.RC.WitnessSpec.integralEquation
#check @ZInQ.Manuscript.RC.WitnessSpec.integralEquation_elliptic
#check @ZInQ.Manuscript.RC.WitnessSpec.integralEquation_residue
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidueEquiv
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidue_charP
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidue_algebra
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidue_algClosed
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.curveReduction
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.curveReduction_frobenius

-- Evaluation.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.torsionMap
#check @ZInQ.Manuscript.RC.WitnessSpec.torsionMap_bijective
#check @ZInQ.Manuscript.RC.WitnessSpec.frob_sq_on_reduced_torsion
#check @ZInQ.Manuscript.RC.WitnessSpec.stageMap
#check @ZInQ.Manuscript.RC.WitnessSpec.stageMap_apply_division

-- FiniteReduction.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteResidue_charP
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteResidue_algebra
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.residueEmbedding
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteReduction
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteReduction_agrees
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.ringClassReduction
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.ringClassReduction_agrees

-- LocalFrobenius.lean
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.integerFrob
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.integerFrob_at
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.LocalFrobenius ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.integerFrob_compl
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localFrob
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.coe_localFrob
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localResidueEquiv
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localFrob_residue
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localValuationEquiv
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuation_frob_le_one_iff
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuation_frob_residue

-- PointReduction.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.reductionToModel
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.PointReduction ZInQ.Manuscript.RC.WitnessSpec.reductionToModel_some
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.PointReduction ZInQ.Manuscript.RC.WitnessSpec.reductionToModel_pole
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.PointReduction ZInQ.Manuscript.RC.WitnessSpec.fp_frob_apply
#check @ZInQ.Manuscript.RC.WitnessSpec.reductionToModel_frobenius
#check @ZInQ.Manuscript.RC.WitnessSpec.reductionToModel_natural
#check @ZInQ.Manuscript.RC.WitnessSpec.quadraticResiduePoints

-- Restriction.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.rationalPrimeBelow_restrict
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localRingMap_isLocal
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Restriction ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteValuationEquiv
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationRingMap
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationRingMap_isLocal
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.coe_valuationRingMap
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuation_le_one_restrict
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidueMap
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationResidueMap_residue
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.finiteValuationResidueEquiv

-- Specialize.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.witnessReductions
#check @ZInQ.Manuscript.RC.WitnessSpec.witnessReductions_at_witness
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Specialize ZInQ.Manuscript.RC.WitnessSpec.goodAt_disc_unit
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Specialize ZInQ.Manuscript.RC.WitnessSpec.not_dvd_of_legendre_ne_zero
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.mk
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.emb
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.root
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.nonzero
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.square
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.rational
#check @ZInQ.Manuscript.RC.WitnessSpec.ExactWitness.eq_scaled
#check_private ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Specialize ZInQ.Manuscript.RC.WitnessSpec.choose_local_at_witness
#check @ZInQ.Manuscript.RC.WitnessSpec.actualWitness

-- Torsion.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.curveReduction_eq_zero_of_nsmul
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.curveReduction_torsion_bijective

-- TwistAtPlace.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.twistVC_at_place
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.twist_unit_valuation
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.twist_unit_residue
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.twistVC_reduction_equation

-- Valuation.lean
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.restrictHeightOne
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localRing
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localRingIntAlgebra
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localRingLocalization
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.localRingMap
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.coe_localRingMap
#check @ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace.valuationRing
