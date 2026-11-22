import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.Rigidity

/-!
# Packaging normalized morphisms of the actual abelian varieties

A normalized scheme morphism to the actual dual (once constructed) is already
a group homomorphism, by the published Jacobian-Challenge pointed-morphism
rigidity theorem. This does not assume a theorem-of-the-square Fact.
Supplier imported unchanged: frenzymath/Jacobian-Challenge
c4254cce15b3e284a0a3ae1d73936f2ee195d272, Apache-2.0; copyright Axel Delaval,
Jie Xu, Shitan Xu. No supplier body is copied here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- A normalized morphism between actual abelian varieties is a homomorphism,
over the original arbitrary field. -/
theorem isMonHom_pointed_abVar_morphism {k : Type u} [Field k]
    {A D : PkgI3.AbVar k} (f : A.X ⟶ D.X) (hf : η[A.X] ≫ f = η[D.X]) :
    IsMonHom f :=
  AlgebraicGeometry.isMonHom_of_isProper_of_geometricallyIntegral f hf

/-- Package that proved homomorphism in the exact Hom carrier of the target. -/
def homOfPointed {k : Type u} [Field k] {A D : PkgI3.AbVar k}
    (f : A.X ⟶ D.X) (hf : η[A.X] ≫ f = η[D.X]) : PkgI3.AbVar.Hom A D := by
  letI : IsMonHom f := isMonHom_pointed_abVar_morphism f hf
  exact PkgI3.AbVar.Hom.mk' f

@[simp]
theorem homOfPointed_hom {k : Type u} [Field k] {A D : PkgI3.AbVar k}
    (f : A.X ⟶ D.X) (hf : η[A.X] ≫ f = η[D.X]) : (homOfPointed f hf).hom = f :=
  rfl

end ZInQ.Contrib.CloudR2Poincare.L2
