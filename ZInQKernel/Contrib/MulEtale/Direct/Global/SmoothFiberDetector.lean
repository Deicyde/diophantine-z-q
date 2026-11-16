/-
Multiplication-etale construction: SmoothFiberDetector.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.QuotientFormalEtale
import ZInQKernel.Contrib.MulEtale.Direct.Global.QuotientLocalCriterion
import Mathlib.RingTheory.EssentialFiniteness

noncomputable section
open CategoryTheory AlgebraicGeometry
open H101DirectGlobalDetection.CanonicalFibres

namespace H101DirectGlobalDetection
universe u

/-- The actual total-space stalk map is formally etale, derived from the
actual fibre map at the actual fibre point. The base stalk is local, but
the original scheme/base ring is entirely arbitrary. -/
theorem formallyEtale_stalkMap_of_smooth_structural_and_etale_fibers
    {X Y B : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ B)
    [Smooth g] [Smooth (f ≫ g)]
    (Hfib : ∀ s : B, Etale (fiberHom f g s)) (x : X) :
    (f.stalkMap x).hom.FormallyEtale := by
  let p := f ≫ g
  let R := B.presheaf.stalk (p x)
  let A := Y.presheaf.stalk (f x)
  let C := X.presheaf.stalk x
  letI : Algebra R A := (g.stalkMap (f x)).hom.toAlgebra
  letI : Algebra A C := (f.stalkMap x).hom.toAlgebra
  letI : Algebra R C := (p.stalkMap x).hom.toAlgebra
  letI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' (by
    change (p.stalkMap x).hom =
      (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x))
  letI : IsLocalHom (algebraMap R C) :=
    inferInstanceAs (IsLocalHom (p.stalkMap x).hom)
  letI : Algebra.EssFiniteType R A := LocallyOfFiniteType.stalkMap g (f x)
  letI : Algebra.EssFiniteType R C := LocallyOfFiniteType.stalkMap p x
  letI : Algebra.FormallySmooth R A := by
    change (g.stalkMap (f x)).hom.FormallySmooth
    apply (Scheme.Hom.mem_smoothLocus).1
    rw [g.smoothLocus_eq_top]
    trivial
  letI : Algebra.FormallySmooth R C := by
    change (p.stalkMap x).hom.FormallySmooth
    apply (Scheme.Hom.mem_smoothLocus).1
    rw [p.smoothLocus_eq_top]
    trivial
  letI : Etale (fiberHom f g (p x)) := Hfib (p x)
  have Hquot := ActualQuotient.quotientMap_formallyEtale_of_etale_fiber f g x
  have HC : Algebra.FormallyEtale A C :=
    QuotientLocal.formallyEtale_of_quotientMap R A C (by
      change (ActualQuotient.quotientMap f g x).FormallyEtale
      exact Hquot)
  change Algebra.FormallyEtale A C
  exact HC

/-- The smaller genuine all-base scheme detector: smooth source and target
structural morphisms plus actual etale residue fibres imply native Etale f.
The final H101 caller supplies the two structural smoothness proofs from
PkgI2.IsAbelianScheme and Over.w, and Hfib from the actual all-field theorem.
No original target or actual carrier is replaced. -/
theorem etale_of_smooth_structural_and_etale_fibers
    {X Y B : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ B)
    [Smooth g] [Smooth (f ≫ g)]
    (Hfib : ∀ s : B, Etale (fiberHom f g s)) : Etale f := by
  letI : LocallyOfFinitePresentation f :=
    locallyOfFinitePresentation_of_smooth_structural f g
  apply etale_of_formallyEtale_stalkMaps f
  intro x
  exact formallyEtale_stalkMap_of_smooth_structural_and_etale_fibers f g Hfib x

end H101DirectGlobalDetection
