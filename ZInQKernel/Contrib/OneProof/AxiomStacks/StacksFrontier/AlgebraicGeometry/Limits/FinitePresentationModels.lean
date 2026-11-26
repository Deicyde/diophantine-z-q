module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ZInQKernel.Contrib.OneProof.AxiomStacks.StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import Mathlib.CategoryTheory.Filtered.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace LimitDescent

/-- **Stacks Project, Tag 01ZM part (1)**, at an index type in the universe of the schemes: every
scheme of finite presentation over a cofiltered limit of quasi-compact, quasi-separated schemes
with affine transition morphisms is the base change of one of finite presentation over a stage.

This is the essential-surjectivity half of Tag 0EY1 and is not proved in this library; only its
affine case is, as
`AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation_of_isAffine`.  It is
stated here as a predicate so that the results depending on it carry it as a hypothesis rather
than an open goal.  It is an instance of the statement of Tag 01ZM part (1), so proving that
tag discharges it. -/
def HasFinitePresentationModels : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : J, CompactSpace (D.obj i)] [∀ i : J, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D), IsLimit c → ∀ (X : Over c.pt), FinitePresentation X.hom →
      ∃ (i : J) (Xᵢ : Over (D.obj i)), FinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app i)).obj Xᵢ)

end LimitDescent

end AlgebraicGeometry
