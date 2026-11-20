import ZInQKernel.Contrib.OneProof.RC.EisForm.Attachment
import ZInQKernel.Contrib.OneProof.RC.EisForm.Expansion
import ZInQKernel.Contrib.OneProof.RC.EisForm.Lipschitz
import ZInQKernel.Contrib.OneProof.RC.EisForm.Modularity
import ZInQKernel.Contrib.OneProof.RC.EisForm.Occurrence
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Bounds
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Characters
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Fourier
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Lattice
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Mean
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Reduction
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Regroup
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Residues
import ZInQKernel.Contrib.OneProof.RC.TwoFresh.Main
import ZInQKernel.Contrib.OneProof.RC.TwoFresh.Stage

namespace ZInQ.Manuscript.RC.EisForm
section
open AddressGenuine O12 O12EisConst O12Eisenstein PrintsArith TraceLimits Matrix
open Filter Topology UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups
#print axioms pair_goodRec
#print axioms old_goodRec
#print axioms normalizedRep_unramified
#print axioms normalizedRep_goodAttachment
#print axioms baseForm_good_trace
#print axioms continuous_splitTrace
#print axioms repInput_of_split_choice
end
end ZInQ.Manuscript.RC.EisForm
namespace ZInQ.Manuscript.RC.EisForm
section
open O12Eisenstein UpperHalfPlane Function
open scoped Manifold
#print axioms divisorCoeff_eq_sum_divisors
#print axioms norm_divisorCoeff_le
#print axioms hasSum_series
#print axioms series_holo
#print axioms series_periodic
#print axioms series_boundedAtInfty
#print axioms qExpansion_series
end
end ZInQ.Manuscript.RC.EisForm
namespace ZInQ.Manuscript.RC.EisForm
section
open O12Eisenstein UpperHalfPlane Complex
open scoped Real
#print axioms series_eq_lambert
#print axioms primitive_ringHomComp
#print axioms series_eq_lipschitz
end
end ZInQ.Manuscript.RC.EisForm
namespace ZInQ.Manuscript.RC.EisForm
section
open O12 O12EisConst O12Eisenstein UpperHalfPlane TauCeti
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups Manifold ModularForm
#print axioms pairSeries_eq_lipschitz
#print axioms pairSeries_positive
#print axioms pairSeries_holo
#print axioms pairSeries_boundedAtInfty
#print axioms baseForm_of_modularity
end
end ZInQ.Manuscript.RC.EisForm
namespace ZInQ.Manuscript.RC.EisForm
section
open AddressGenuine O12 O12EisConst O12Eisenstein UpperHalfPlane TauCeti PrintsArith
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
#print axioms atLevel_coeff_degree
#print axioms scale_of_labeled_line
#print axioms column_of_labeled_line
#print axioms realizedCoordinate_of_labeled_line
end
end ZInQ.Manuscript.RC.EisForm
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix ModularForm UpperHalfPlane EisensteinSeries
open scoped MatrixGroups
#print axioms summable_gridRows
#print axioms gridSeries_bounded
#print axioms latticeDiff_eq_gridSeries_sub
#print axioms latticeDiff_shift
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane CongruenceSubgroup
open O12Eisenstein O12EisConst EisForm
open scoped MatrixGroups
#print axioms characterWeight_on_row
#print axioms characterWeight_pullback
#print axioms pairWeight_pullback
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix UpperHalfPlane EisensteinSeries O12Eisenstein O12EisConst EisForm
#print axioms ordered_grid_fourier
#print axioms pair_grid_fourier
#print axioms pair_modularity
#print axioms pair_baseForm
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane EisensteinSeries
open Filter Asymptotics
open scoped MatrixGroups Real
#print axioms summable_lattice_diff
#print axioms latticeDiff_add
#print axioms latticeDiff_slash
#print axioms summable_gridRow_inner
#print axioms latticeDiff_eq_rows
#print axioms gridSeries_shift
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix O12Eisenstein O12EisConst EisForm
#print axioms characterWeight_sum_zero
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane CongruenceSubgroup
open O12Eisenstein O12EisConst EisForm
open scoped MatrixGroups ModularForm
#print axioms orderedScale_ne_zero
#print axioms pairScale_ne_zero
#print axioms pair_checks_of_grid_eq
#print axioms missingModularity_of_gridFourier
#print axioms baseForm_of_gridFourier
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix ModularForm UpperHalfPlane EisensteinSeries
#print axioms sum_residue_rows
#print axioms gridCombination_eq_weightedRows
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.EisSlash
section
open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane
open scoped MatrixGroups
#print axioms rowResidue_lift
#print axioms exists_grid_of_residue_eq
#print axioms rowResidue_vecMul
#print axioms gridCombination_eq_rows
#print axioms gridCombination_slash
#print axioms gridCombination_slash_scalar
#print axioms gridCombination_bounded_slash
end
end ZInQ.Manuscript.RC.EisSlash
namespace ZInQ.Manuscript.RC.TwoFresh
section
open AddressGenuine PrintsArith Symbols TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups
open ZInQ.Manuscript.RC.Odd
#print axioms two_hecke_coeff
#print axioms dense_twoFreshTests
#print axioms continuous_twoTraces
#print axioms h2fresh
end
end ZInQ.Manuscript.RC.TwoFresh
namespace ZInQ.Manuscript.RC.TwoFresh
section
open ZInQ.Manuscript.RC.Odd
#print axioms fresh_squarefree_weight
#print axioms ne_unary_of_oddPart
#print axioms fresh_normalizations
end
end ZInQ.Manuscript.RC.TwoFresh
