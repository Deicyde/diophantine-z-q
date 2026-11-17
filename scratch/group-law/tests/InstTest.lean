import ZInQKernel.Contrib.OneProof.GroupLawGlue
import ZInQKernel.Contrib.SpreadOut.Spread
open CategoryTheory AlgebraicGeometry
example {X Y : Scheme.{0}} (f : X ⟶ Y) : (Over.pullback f).Monoidal := inferInstance
example {I : Type} [Category.{0} I] (D : I ⥤ Scheme.{0}) {i j : I} (b : i ⟶ j) : (Over.pullback (D.map b)).Monoidal := inferInstance
