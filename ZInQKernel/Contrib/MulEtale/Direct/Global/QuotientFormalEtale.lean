/-
Multiplication-etale construction: QuotientFormalEtale.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.FibreStalkNaturality
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified

noncomputable section
open CategoryTheory AlgebraicGeometry
open H101DirectGlobalDetection.CanonicalFibres

namespace H101DirectGlobalDetection.ActualQuotient
universe u

/-- The ACTUAL etale residue-fibre map supplies formal etaleness of the
ACTUAL quotient map induced by f.stalkMap x. -/
theorem quotientMap_formallyEtale_of_etale_fiber
    {X Y B : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ B) (x : X)
    [Etale (fiberHom f g ((f ≫ g) x))] :
    (quotientMap f g x).FormallyEtale := by
  let mf := fiberHom f g ((f ≫ g) x)
  let xf := xFiber f g x
  let eS := sourceQuotientEquiv f g x
  let eT := targetQuotientEquiv f g x
  let E : Arrow.mk (CommRingCat.ofHom (quotientMap f g x)) ≅
      Arrow.mk (mf.stalkMap xf) :=
    Arrow.isoMk eS.toCommRingCatIso eT.toCommRingCatIso (by
      ext a
      exact (quotientMap_fiberStalk_naturality f g x a).symm)
  letI := (quotientMap f g x).toAlgebra
  change Algebra.FormallyEtale (S0 f x ⧸ JS f g x) (T0 x ⧸ JT f g x)
  apply Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
  constructor
  · change (quotientMap f g x).FormallyUnramified
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff E).mpr
      (AlgebraicGeometry.FormallyUnramified.stalkMap mf xf)
  · change (quotientMap f g x).FormallySmooth
    apply (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff E).mpr
    apply (Scheme.Hom.mem_smoothLocus).1
    rw [mf.smoothLocus_eq_top]
    trivial

end H101DirectGlobalDetection.ActualQuotient
