import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TorsionFreeDualExactness
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.RetainedCupMap
import ZInQKernel.Contrib.RC53Assist.CalibrationShape.CalibrationDischarge
import ZInQKernel.Contrib.RC53Assist.CentralUniversal.GenuineObjects

/-!
# The termwise dual of the fixed retained central comparison

Both the retained finite free terms and the genuine compact Tate/Kummer
cochain terms are torsion-free over the two-adic integers. Scoped dual
exactness therefore applies to the actual constructed comparison.

This produces a quasi-isomorphism between the two exact termwise duals.
To regard the retained dual as a derived Hom representative also requires
the existing cohomological support proof that bounds the retained model.
No unrestricted derived Hom functor or arithmetic self-duality is asserted.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationModel
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Manuscript.RC53Assist.CentralUniversal

section RetainedCentral

variable {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))

/-- All actual retained terms are torsion-free, without imposing any cohomology-rank symmetry. -/
theorem retainedCentralGCx_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((centralRetainedGCx D hfinite).X n) := by
  let : Module.Free ℤ_[2] ((centralRetainedGCx D hfinite).X n) :=
    (centralRetainedGCx_terms D hfinite n).1
  infer_instance

/-- The target is the actual compact central Tate/Kummer complex, whose terms are torsion-free. -/
theorem compactCentralGCx_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((selCx (compactCentralSelData D)).X n) := by
  change Module.IsTorsionFree ℤ_[2] ((compactCentralComplex D).X n)
  rw [compactCentralComplex_eq]
  exact compactKummerTerm_isTorsionFree D.S (centralCurve D) (centralFullTorsion D) n

/-- The relation-indexed form of the already-constructed retained comparison. -/
def retainedCentralComparisonGHom :
    GHom (centralRetainedGCx D hfinite) (selCx (compactCentralSelData D)) :=
  relationHomOfCochainHom (retainedCentralComparison D hfinite)

/-- The forward comparison is exactly the existing retained comparison. -/
theorem retainedCentralComparisonGHom_toCC :
    GHom.toCC (retainedCentralComparisonGHom D hfinite) =
      retainedCentralComparison D hfinite :=
  relationHomOfCochainHom_toCC _

/-- The exact contravariant termwise-dual comparison, with the existing differential signs. -/
def retainedCentralDualComparison (m : ℤ) :
    (dualCx (selCx (compactCentralSelData D)) m).toCC ⟶
      (dualCx (centralRetainedGCx D hfinite) m).toCC :=
  GHom.toCC (dualHom (retainedCentralComparisonGHom D hfinite) m)

/-- Scoped compact-PID dual exactness proves the actual dual comparison is a quasi-isomorphism. -/
theorem retainedCentralDualComparison_quasiIso (m : ℤ) :
    QuasiIso (retainedCentralDualComparison D hfinite m) := by
  have hf : QuasiIso (GHom.toCC (retainedCentralComparisonGHom D hfinite)) := by
    rw [retainedCentralComparisonGHom_toCC]
    exact retainedCentralComparison_quasiIso D hfinite
  exact dualHom_quasiIso_torsionFree (retainedCentralComparisonGHom D hfinite)
    (retainedCentralGCx_torsionFree D hfinite) (compactCentralGCx_torsionFree D) m hf

end RetainedCentral

end ZInQ.Contrib.RC53Assist.IntegralDuality
