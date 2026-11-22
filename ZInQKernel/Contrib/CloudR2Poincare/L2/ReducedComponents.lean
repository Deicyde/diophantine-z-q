import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Native reduced irreducible components and finite underlying scheme spaces

Radical ideal quotients are reduced on the actual glued affine cover. Together
with the native irreducible-component subscheme this gives an actual integral
closed subscheme for each component, without Cartier or group assumptions.
If all those reductions have dimension zero, their finite union is finite.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Radical quotient subschemes are reduced, using the actual affine cover
Spec(Γ(X,U)/sqrt(I(U))) and native quotient-ring reducedness. -/
theorem isReduced_radical_subscheme {X : Scheme.{u}} (I : X.IdealSheafData) :
    AlgebraicGeometry.IsReduced I.radical.subscheme := by
  letI (U : X.affineOpens) : _root_.IsReduced (Γ(X, U) ⧸ I.radical.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  letI (U : X.affineOpens) :
      AlgebraicGeometry.IsReduced (I.radical.subschemeCover.openCover.X U) := by
    change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.radical.ideal U)))
    infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover I.radical.subscheme
    I.radical.subschemeCover.openCover

/-- The actual reduced induced scheme structure on an irreducible component. -/
def reducedComponent (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : Scheme.{u} :=
  (X.irreducibleComponentIdeal Z hZ).radical.subscheme

/-- Actual closed inclusion of the reduced component into its original scheme. -/
def reducedComponentι (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : reducedComponent X Z hZ ⟶ X :=
  (X.irreducibleComponentIdeal Z hZ).radical.subschemeι

instance reducedComponent_closed (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsClosedImmersion (reducedComponentι X Z hZ) := by
  unfold reducedComponentι
  infer_instance

instance reducedComponent_reduced (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    AlgebraicGeometry.IsReduced (reducedComponent X Z hZ) :=
  isReduced_radical_subscheme _

instance reducedComponent_irreducible (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IrreducibleSpace (reducedComponent X Z hZ) :=
  Subtype.irreducibleSpace hZ.1

instance reducedComponent_integral (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : IsIntegral (reducedComponent X Z hZ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The underlying closed set has not changed under the radical reduction. -/
theorem range_reducedComponentι (X : Scheme.{u}) [IsNoetherian X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    Set.range (reducedComponentι X Z hZ) = Z := by
  change Set.range (X.irreducibleComponentIdeal Z hZ).radical.subschemeι =
    (X.irreducibleComponentIdeal Z hZ).radical.support
  exact Scheme.IdealSheafData.range_subschemeι _

/-- A Noetherian scheme whose reduced irreducible components are zero-dimensional
has a finite underlying topological point space. No component is made a group. -/
theorem finite_scheme_of_reducedComponents_dimZero (X : Scheme.{u}) [IsNoetherian X]
    (hdim : ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      topologicalKrullDim (reducedComponent X Z hZ) ≤ 0) : Finite X := by
  have hfinite (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : Z.Finite := by
    let C := reducedComponent X Z hZ
    letI : IsLocallyNoetherian C :=
      LocallyOfFiniteType.isLocallyNoetherian (reducedComponentι X Z hZ)
    letI : NoetherianSpace C := inferInstanceAs (NoetherianSpace Z)
    letI : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero (hdim Z hZ)
    letI : IsArtinianScheme C := { }
    letI : Finite C := inferInstance
    rw [← range_reducedComponentι X Z hZ]
    exact Set.finite_range _
  have hX : (Set.univ : Set X).Finite := by
    rw [← sUnion_irreducibleComponents]
    exact (finite_irreducibleComponents_of_isNoetherian (X := X)).sUnion hfinite
  exact Set.finite_univ_iff.mp hX

end ZInQ.Contrib.CloudR2Poincare.L2
