import ZInQKernel.Contrib.CloudR2Poincare.L4.KernelGeometry
import ZInQKernel.Contrib.CloudR2Poincare.Skeleton

/-!
# The finite half of the exact Poincaré complement isogeny

The group-law sum below is literally the sum in the lead's fixed statement. Its
scheme-theoretic kernel is proved finite in `KernelGeometry`, rather than assumed.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

/-- The finite half of `ComplementIsogeny`, requiring only the hypotheses actually used. -/
theorem finite_sum_abVar {k : Type} [Field k] (J B Z D : _root_.PkgI3.AbVar k)
    (i : _root_.PkgI3.AbVar.Hom B J) (g : _root_.PkgI3.AbVar.Hom Z J)
    (φ : _root_.PkgI3.AbVar.Hom J D)
    (hgi : IsClosedImmersion g.hom.left) (hg : g.hom ≫ φ.hom = 1)
    (hf : IsFinite (i.hom ≫ φ.hom).left) :
    IsFinite (fst B.X Z.X ≫ i.hom * snd B.X Z.X ≫ g.hom).left := by
  haveI := hgi
  haveI := hf
  exact finite_sum B.X Z.X J.X D.X i.hom g.hom φ.hom hg

end ZInQ.Contrib.CloudR2Poincare.L4
