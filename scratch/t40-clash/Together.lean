-- Task t40-clash: T40 imported together with the Contrib modules the H assembly uses.
-- (There is no ZInQKernel.Contrib.FrobChain module; the frob-chain Contrib modules are
-- FrobPieces/, Chebotarev/ and AbsFrob/, all three imported below.)
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.Mobius.Main
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.AbsFrob.Basic
import ZInQKernel.Contrib.GZTheta.ALFinal
import ZInQKernel.Contrib.RLeaf.T36Torsion
-- the module whose declarations clashed with the Backport/ copy
import ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic

#check @Units.val_mul_zpow_natCast_mul
#check @Units.val_mul_zpow_neg_natCast_succ_mul
#check @TauCeti.mem_range_iff_exists_units_map_eq
#check @Units.eq_of_mul_mul_inv_eq_of_commute
#check @ZInQ.RLeaf.x1RationalCusp_of_x0Transitive
#check @ZInQ.RLeaf.x1ConstantField_of_x0Transitive
