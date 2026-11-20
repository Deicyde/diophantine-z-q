import ZInQKernel.Contrib.OneProof.RC.KappaRational.FixedScale
import ZInQKernel.Contrib.OneProof.RC.LiftPhase.Actual
import ZInQKernel.Contrib.OneProof.RC.LiftPhase.Local
import ZInQKernel.Contrib.OneProof.RC.LiftPhase.Pool
import ZInQKernel.Contrib.OneProof.RC.PoolCharacter.Extraction
import ZInQKernel.Contrib.OneProof.RC.PoolCharacter.Identification

namespace ZInQ.Manuscript.RC.KappaRational
section
open Filter Topology UpperHalfPlane AlgebraicGeometry CategoryTheory WeierstrassCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ModFnField ZInQ.Manuscript.RC.ParamAtScale
#print axioms coordinate_leading_terms
#print axioms scaledPrimitive_off_lattice_on_tail
#print axioms rational_of_coordinate_expansions
#print axioms rational_of_projective_values_on_tail
#print axioms algebraicParametrizationAtScale_iff
end
end ZInQ.Manuscript.RC.KappaRational
namespace ZInQ.Manuscript.RC.LiftPhase
section
open ThetaClose ThetaJoin ThetaCoeff BlocksPerU WeilIndex
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
#print axioms actualEta_reduce
#print axioms actualLift_order
#print axioms actual_hchar
#print axioms actualOldStageLaw
end
end ZInQ.Manuscript.RC.LiftPhase
namespace ZInQ.Manuscript.RC.LiftPhase
section
open Adelic ThetaJoin LocalWeights
open scoped BigOperators
#print axioms eta_order_of_away
#print axioms prime_dvd_rootModulus
#print axioms residueAlpha_nat
#print axioms etaSource_eq
end
end ZInQ.Manuscript.RC.LiftPhase
namespace ZInQ.Manuscript.RC.LiftPhase
section
open Adelic ThetaJoin BlocksPerU PoolCharacter
open scoped BigOperators
#print axioms residueModuli_dvd
#print axioms poolPhase_eval
#print axioms poolPhase_order
end
end ZInQ.Manuscript.RC.LiftPhase
namespace ZInQ.Manuscript.RC.PoolCharacter
section
open BlocksPerU ThetaCoeff WeilIndex
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators
#print axioms phase_without_extraction
#print axioms oldCharacter_comp_eq_bCharacter_iff_of_extraction
#print axioms embedded_bCharacter_empty
#print axioms phaseCharacter_value
#print axioms oldCharacter_comp_eq_bCharacter_iff
#print axioms oldCharacter_comp_eq_bCharacter_of_phase
end
end ZInQ.Manuscript.RC.PoolCharacter
