import ZInQKernel.Contrib.OneProof.PicDictionary
open CategoryTheory AlgebraicGeometry MonoidalCategory
example (X : Scheme.{0}) : 𝟙_ X.Modules = Scheme.Modules.unit X := rfl
example {X Y : Scheme.{0}} (f : X ⟶ Y) : (Scheme.Modules.pullbackObjUnitIso f).inv = Functor.LaxMonoidal.ε (Scheme.Modules.pullback f) := by
  sorry
#check @Functor.LaxMonoidal.left_unitality
#check @Functor.LaxMonoidal.μ_natural
#check @Functor.Monoidal.μ_δ
#check @unitors_equal
#check @Scheme.Pic.mulIso
