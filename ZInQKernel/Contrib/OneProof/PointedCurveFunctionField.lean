import ZInQKernel.Contrib.OneProof.PointedGenusZeroFunctionField
import ZInQKernel.Contrib.OneProof.PointedRationalCurve
import ZInQKernel.Contrib.RC53Assist.S2aNumberField.RegularComparison
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth

/-! The function field of a smooth proper pointed genus-zero curve. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra differentialSheaf
  globalSectionsModule isFunctionField_of_dimension_one functionField_exact_constants)
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs (stalkPlace)
open ZInQ.Contrib.RC53Assist.S2aNumberField (regularDifferentialComparison
  closed_stalk_discreteValuationRing finrank_eq_one_of_retraction)
open ZInQ.Contrib.Dim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

namespace AlgebraicGeometry

variable {k : Type} [Field k] {X : Scheme.{0}}

/-- The cohomological genus of a smooth proper geometrically integral curve
equals the genus of its actual function field. -/
theorem genus_functionField_eq_arithmeticGenus [CharZero k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyIntegral f] :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    letI := functionFieldAlgebra f
    TauCeti.genus k X.functionField = X.arithmeticGenus k := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  have hs : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 f)
  have : GeometricallyIrreducible (X ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIrreducible f)
  have hdim : topologicalKrullDim X = 1 :=
    ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  obtain ⟨c⟩ := regularDifferentialComparison X f hdim
  rw [← TauCeti.finrank_weilDifferentialFiltration_zero
    (isFunctionField_of_dimension_one f hdim) (functionField_exact_constants f),
    ← c.finrank_eq]
  let d := H.zeroLinearEquiv (differentialSheaf f)
  let d' : (differentialSheaf f).H 0 ≃ₗ[k] Γ(differentialSheaf f, ⊤) :=
    { d.toEquiv with
      map_add' := d.map_add
      map_smul' := fun a x => d.map_smul (Scheme.globalSectionsRingHom k (X := X) a) x }
  rw [← d'.finrank_eq]
  exact finrankH_relativeDifferentials_zero_eq_genus (baseField := k) (source := X)

/-- Evaluation at a rational section sends a pulled-back constant to itself. -/
private theorem stalkClosedPointTo_section_constant (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (c : k) :
    Scheme.stalkClosedPointTo s
      (X.presheaf.germ ⊤ (s (IsLocalRing.closedPoint k)) trivial
        (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) = c := by
  have key : ∀ g : Spec (.of k) ⟶ Spec (.of k), g = Spec.map (𝟙 _) →
      ∀ a, Scheme.stalkClosedPointTo g
        ((Spec (.of k)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint k)) trivial a) =
          (Scheme.ΓSpecIso (.of k)).hom a := by
    rintro g rfl a
    exact ConcreteCategory.congr_hom
      (Scheme.germ_stalkClosedPointTo_Spec (𝟙 (CommRingCat.of k))) a
  have hgerm := Scheme.Hom.germ_stalkMap_apply f ⊤ (s (IsLocalRing.closedPoint k)) trivial
    ((Scheme.ΓSpecIso (.of k)).inv c)
  have hcomp := ConcreteCategory.congr_hom (Scheme.stalkClosedPointTo_comp s f)
    ((Spec (.of k)).presheaf.germ ⊤ (f (s (IsLocalRing.closedPoint k))) trivial
      ((Scheme.ΓSpecIso (.of k)).inv c))
  have hid := key (s ≫ f) (hs.trans (Spec.map_id _).symm) ((Scheme.ΓSpecIso (.of k)).inv c)
  change Scheme.stalkClosedPointTo s
    (X.presheaf.germ (f ⁻¹ᵁ ⊤) (s (IsLocalRing.closedPoint k)) trivial
      (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv c))) = c
  rw [← hgerm]
  exact hcomp.symm.trans (hid.trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of k)).inv_hom_id c))

/-- The local ring of a rational point determines a place of degree one. -/
theorem stalkPlace_degree_of_section [IsIntegral X] (f : X ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    [IsDiscreteValuationRing (X.presheaf.stalk (s (IsLocalRing.closedPoint k)))] :
    letI := functionFieldAlgebra f
    (stalkPlace f (s (IsLocalRing.closedPoint k))).degree = 1 := by
  let x := s (IsLocalRing.closedPoint k)
  letI := functionFieldAlgebra f
  letI := ZInQ.Contrib.RC53Assist.AbelianCurve.stalkAlgebra f x
  haveI := ZInQ.Contrib.RC53Assist.AbelianCurve.stalk_functionField_tower f x
  rw [stalkPlace, TauCeti.Place.degree_ofPrime]
  let φ : IsLocalRing.ResidueField (X.presheaf.stalk x) →+* k :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom
  refine finrank_eq_one_of_retraction φ fun c => ?_
  change Scheme.stalkClosedPointTo s
    (X.presheaf.germ ⊤ x trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) = c
  exact stalkClosedPointTo_section_constant f s hs c

/-- A smooth proper integral curve of arithmetic genus zero with a rational
point has a rational function field. -/
theorem exists_ratFunc_equiv_of_arithmeticGenus_zero [CharZero k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (hg : letI : X.Over (Spec (.of k)) := ⟨f⟩; X.arithmeticGenus k = 0) :
    letI := functionFieldAlgebra f
    Nonempty (RatFunc k ≃ₐ[k] X.functionField) := by
  letI := functionFieldAlgebra f
  have hsmooth : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hirr : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_proper_smooth_integral_section f s hs
  have hi : GeometricallyIntegral f :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  have hdim : topologicalKrullDim X = 1 :=
    ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  let x := s (IsLocalRing.closedPoint k)
  have hclosed : IsClosed ({x} : Set X) := isClosed_singleton_of_section f s hs _
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    closed_stalk_discreteValuationRing f hdim hclosed
  have hP : (stalkPlace f x).degree = 1 := stalkPlace_degree_of_section f s hs
  have hgenus : TauCeti.genus k X.functionField = 0 :=
    (genus_functionField_eq_arithmeticGenus f).trans hg
  obtain ⟨e, _, _⟩ := TauCeti.Place.exists_ratFunc_equiv_of_genus_zero
    (isFunctionField_of_dimension_one f hdim) (functionField_exact_constants f)
    hgenus (stalkPlace f x) hP
  exact ⟨e⟩

end AlgebraicGeometry

#print axioms AlgebraicGeometry.genus_functionField_eq_arithmeticGenus
#print axioms AlgebraicGeometry.stalkPlace_degree_of_section
#print axioms AlgebraicGeometry.exists_ratFunc_equiv_of_arithmeticGenus_zero
