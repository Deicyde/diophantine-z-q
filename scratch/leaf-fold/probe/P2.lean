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

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra TauCeti.FinitePadicExtension.ofInstances
  TauCeti.FinitePadicExtension.toModuleFinite TauCeti.FinitePadicExtension.toValuativeExtension

set_option profiler true
set_option profiler.threshold 50

example (p : ℕ) [Fact p.Prime] : Module.IsTorsionFree ℚ_[p] ℂ_[p] := inferInstance
example (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] :
    Algebra.IsAlgebraic ℚ_[p] L := inferInstance
example (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] :
    IsMulTorsionFree (L ≃ₐ[ℚ_[p]] L) := inferInstance
example (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] :
    Normal ℚ_[p] L := inferInstance
example (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [Algebra ℚ_[p] E] :
    Module.Flat ℚ_[p] E := inferInstance
