import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Assembly

/-!
# Theorem 5.3, Lane RC32: the consumers of the common-coordinate leaf over the text's objects

The wiring (`RC/Wiring/Leaves.lean`, `rcSteps_of_leaves`) consumes the leaf `common_coordinate`
twice: as the step `RCSteps.common_coordinate` ((4.7), `commonCoordinateTarget_of_L`) and at the
base character in the base-zero lemma (tex 4369–4373: "`ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ Λ^×` by
Lemma `ex:arith-common-coordinate`"). `baseZeroTarget_of_L` is lane RC25's
`BaseZeroAssembly.baseZeroTarget_of_leaves` with `CommonCoordinateInputsL` in place of
`CommonCoordinateInputs`: the base-zero lemma uses the common coordinate only through (4.7), so it
goes through the target (`BaseZeroAssembly.baseZeroInputsCST_of_leaf`), with no intermediate
coefficient model. PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Contrib.CloudB3RC53

/-- **`RCSteps.base_zero` from the leaves, with the common-coordinate leaf over the text's
objects** (tex 4330–4376, 4369–4373): `Prints` (Cai–Shu–Tian Thm 1.1, for the height formula),
`CommonCoordinateInputsL D`, `PrimRegularityInputs D` and the base-zero leaf inputs. PROVED
(lane RC0's `baseZeroTarget_of_inputs` and `baseZeroInputs_of_CST`, lane RC25's
`baseZeroInputsCST_of_leaf`, lane RC16's `heightOneTarget_of_inputs`). -/
theorem baseZeroTarget_of_L {ℓ : ℕ} {D : RCData ℓ} (P : Prints) (hcc : CommonCoordinateInputsL D)
    (hpr : PrimRegularityInputs D) (h : BaseZeroAssembly.BaseZeroLeafInputs D) :
    BaseZeroTarget D :=
  baseZeroTarget_of_inputs P (baseZeroInputs_of_CST (BaseZeroAssembly.baseZeroInputsCST_of_leaf
    (commonCoordinateTarget_of_L hcc)
    (heightOneTarget_of_inputs D hpr (commonCoordinateTarget_of_L hcc)) h))

end ZInQ.Manuscript.RC.Wiring
