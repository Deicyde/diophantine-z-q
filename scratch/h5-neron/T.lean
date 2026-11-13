import ZInQKernel.HDecomp.Faltings.Leaves
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj
variable {S S' : Scheme.{0}} (j : S' ⟶ S) (X Y : Over S) [GrpObj X] [GrpObj Y]
example : (Over.pullback j).LaxBraided := inferInstance
example : IsMonHom (Functor.LaxMonoidal.μ (Over.pullback j) X Y) := inferInstance
example : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).hom := inferInstance
example : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).inv := inferInstance
example : IsMonHom ((Over.pullback j).map (fst X Y)) := inferInstance
