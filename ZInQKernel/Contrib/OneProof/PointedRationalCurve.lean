import ZInQKernel.Contrib.CloudW02Connectedness.Basic
import ZInQKernel.Contrib.OneProof.Y3QuotientNormal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.PointedCurve.Basic

/-! A rational point on a proper integral rational curve gives the geometric
irreducibility needed by the pointed-curve interface. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeafQM.AV

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

/-- Global sections of a proper integral scheme over a field with a
rational point coincide with the base field. -/
theorem appTop_bijective_of_proper_integral_section {k : Type} [Field k]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    Function.Bijective f.appTop := by
  let R := Γ(Spec (CommRingCat.of k), ⊤)
  let S := Γ(X, ⊤)
  let _ : Algebra R S := f.appTop.hom.toAlgebra
  have : Algebra.IsIntegral R S := ⟨isIntegral_appTop_of_universallyClosed f⟩
  have hF : IsField R := (MulEquiv.isField_congr
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv).mpr
      (Field.toIsField k)
  have hS := isField_of_isIntegral_of_isField' (S := S) hF
  let _ : Field S := hS.toField
  have hi : Function.Injective s.appTop.hom := s.appTop.hom.injective
  have hcomp : f.appTop ≫ s.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hs]
    simp
  have hleft : Function.LeftInverse s.appTop.hom f.appTop.hom := by
    intro a
    exact congrArg (fun g => g.hom a) hcomp
  exact ⟨hleft.injective, fun b => ⟨s.appTop b, hi (hleft (s.appTop b))⟩⟩

/-- A proper smooth integral curve with a rational point is geometrically
irreducible. -/
theorem geometricallyIrreducible_of_proper_smooth_integral_section {k : Type} [Field k]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyIrreducible f := by
  have hApp := appTop_bijective_of_proper_integral_section f s hs
  have : GeometricallyConnected f := ZariskiConn.ZariskiConnectedness_proof f
    inferInstance inferInstance (ZariskiConn.app_bijective_of_appTop_bijective f hApp)
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{0} => IrreducibleSpace Y) (f := f)]
  intro K _ _
  let fK := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : GeometricallyConnected fK := inferInstanceAs
    (GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  have : ConnectedSpace ↥(Limits.pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := fK)
  exact HDec.TSHecke.irreducibleSpace_of_connected fK inferInstance inferInstance

end AlgebraicGeometry

#print axioms AlgebraicGeometry.geometricallyIrreducible_of_proper_smooth_integral_section
