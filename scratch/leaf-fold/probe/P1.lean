import Mathlib
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.LocalKW.T30
import ZInQKernel.Contrib.KroneckerWeber.Leaves
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense
import ZInQKernel.Contrib.Different.Global
import ZInQKernel.Contrib.T25.NewformOfEigenform
import ZInQKernel.Contrib.T31.Main
import ZInQKernel.HDecomp.Textbook.BrauerNesbitt

set_option profiler true in
example (p : ℕ) [Fact p.Prime] : Module.IsTorsionFree ℚ_[p] ℂ_[p] := inferInstance

set_option synthInstance.maxHeartbeats 20000 in
set_option trace.Meta.synthInstance true in
example (p : ℕ) [Fact p.Prime] : Module.IsTorsionFree ℚ_[p] ℂ_[p] := inferInstance
