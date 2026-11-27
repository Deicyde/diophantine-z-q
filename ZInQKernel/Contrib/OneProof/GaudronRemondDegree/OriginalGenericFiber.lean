import ZInQKernel.Contrib.HeightBC.H5GlueOpen
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # The generic fiber of the original model in the residue-field formulation -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped NumberField

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue

universe u

/-- The residue-field point at the generic point of a domain is its fraction-field
point, as a morphism over the actual affine base. -/
theorem exists_genericResidueIso {R F : Type u} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] :
    let S := Spec (CommRingCat.of R)
    let x := genericPoint S
    ∃ t : Spec (S.residueField x) ⟶ Spec (CommRingCat.of F),
      IsIso t ∧ t ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) = S.fromSpecResidueField x := by
  dsimp only
  rw [genericPoint_eq_bot_of_affine]
  let S := Spec (CommRingCat.of R)
  let p : S := (⊥ : PrimeSpectrum R)
  let B := p.asIdeal.ResidueField
  have : IsFractionRing R B := inferInstanceAs (IsFractionRing R (⊥ : Ideal R).ResidueField)
  let a : F ≃ₐ[R] B := IsLocalization.algEquiv (nonZeroDivisors R) F B
  let i := Scheme.Spec.residueFieldIso (CommRingCat.of R) p
  let b := a.toRingEquiv.toCommRingCatIso.hom
  have h : CommRingCat.ofHom (algebraMap R F) ≫ b = CommRingCat.ofHom (algebraMap R B) := by
    ext r
    exact a.commutes r
  refine ⟨Spec.map i.inv ≫ Spec.map b, inferInstance, ?_⟩
  rw [Category.assoc, ← Spec.map_comp, h]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ p

/-- Geometric integrality implies geometric connectedness by applying the same
pullback criterion, without selecting a different fiber. -/
theorem geomConnected_of_geomIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GeometricallyIntegral f) : GeometricallyConnected f := by
  refine ⟨?_⟩
  intro E _ y Z fst snd h
  have : IsIntegral Z := hf.geometrically_isIntegral y fst snd h
  infer_instance

/-- The particular geometric generic-fiber hypothesis of Stacks 37.28.4 on the
original model, in Mathlib's residue-field formulation. -/
theorem originalModel_genericFiber_geometricallyConnected {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K} (N : GroupModel A L) :
    GeometricallyConnected (N.G.hom.fiberToSpecResidueField
      (genericPoint (Spec (CommRingCat.of (𝓞 L))))) := by
  let S := Spec (CommRingCat.of (𝓞 L))
  let x := genericPoint S
  let f := N.G.hom
  let j := jL L
  let q := pullback.snd f j
  obtain ⟨t, _, ht⟩ := exists_genericResidueIso (R := 𝓞 L) (F := L)
  change t ≫ j = S.fromSpecResidueField x at ht
  let a := (A.baseChange L).X.hom
  let v := (Over.forget _).mapIso N.gen
  have hv : v.hom ≫ a = q := Over.w N.gen.hom
  have hqi : GeometricallyIntegral q := by
    rw [← hv]
    have h : (geometrically IsIntegral) (v.hom ≫ a) :=
      (MorphismProperty.cancel_left_of_respectsIso (geometrically IsIntegral) v.hom a).mpr
        ((A.baseChange L).geomInt.geometrically_isIntegral)
    exact ⟨h⟩
  have houter : IsPullback (f.fiberι x) (f.fiberToSpecResidueField x) f (t ≫ j) := by
    rw [ht]
    exact IsPullback.of_hasPullback f (S.fromSpecResidueField x)
  have hleft := IsPullback.of_right' houter (IsPullback.of_hasPullback f j)
  exact geomConnected_of_geomIntegral _ (MorphismProperty.of_isPullback hleft hqi)

#print axioms exists_genericResidueIso
#print axioms originalModel_genericFiber_geometricallyConnected

end ZInQ.Contrib.IsogenyDegree
