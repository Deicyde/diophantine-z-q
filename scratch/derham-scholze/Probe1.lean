import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
open CategoryTheory AlgebraicGeometry
#check @Scheme.EllAdicCohomology
#check @Equivalence.sheafCongr
#check @Functor.sheafPushforwardContinuous
#check @Abelian.Ext.mapExactFunctor
#check @Over.map
example (X : Scheme.{0}) : Type 1 := X.EllAdicCohomology 5 1
