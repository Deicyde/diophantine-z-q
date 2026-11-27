import ZInQKernel.OneProof.H.TailZ
import ZInQKernel.Contrib.OneProof.CMjBridgesPeriods

/-! # cmheight62-p1, step 0: every smooth group model of an elliptic curve is metrizable

From T35 (`ZInQ.LeafPush2.UniformizationExists`, proved in the tree as
`HDec.CMBranch.CMjBridges.uniformization_exists`), moved to the model along `theta`
(`ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists`), and
`ZInQ.HeightGlue.metrizationOfUniformization`. No properness. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open NumberField
open ZInQ.DefFaltings

/-- **Step 0.** Every smooth group model `𝒢` of an elliptic curve `E_L` underlies a metrized model
`M` of dimension `1` with `M.model = 𝒢`. -/
theorem exists_metrizedModel {K : Type} [Field K] [NumberField K] {E : PkgI3.AbVar K}
    (hdim : E.dim = 1) {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel E L) : ∃ M : MetrizedModel E L 1, M.model = 𝒢 := by
  have hg : E.dim = ((1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  exact ZInQ.HeightGlue.metrizationOfUniformization K E L 𝒢 1 hg fun τ =>
    ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
      HDec.CMBranch.CMjBridges.uniformization_exists K E L 𝒢 τ 1 hg

end ZInQ.Contrib.CMHeight62
