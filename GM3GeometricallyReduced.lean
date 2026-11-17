/-
Lane5 producer for C3's exact GeomReducedOverAlgClosed.{u}.
SOURCE ONLY / UNCOMPILED. Truth pre-check: true, EGA IV 4.6.1.

The affine algebra proof is the actual all-field tensor argument in
GM3TensorReduced: Nullstellensatz evaluations and a basis of the test field
kill every coefficient of a nilpotent. This does NOT infer the all-field
Mathlib geometric predicate from the weaker algebraic-closure-only ring
predicate, and introduces no finite-extension/CharZero/smoothness/Noetherian
base restriction. The actual affine pullback/tensor iso and open cover lift
that proof to the precise scheme predicate at arbitrary universe u.
-/
import GM3TensorReduced
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Plan

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace H5OriginalDVR.Lane5.GM3Geometry

/-- Exact affine scheme base change, with the algebra structures derived
from the ACTUAL field-valued morphisms by Spec full faithfulness. -/
theorem reduced_pullback_spec_of_isAlgClosed
    {k L : Type u} [Field k] [IsAlgClosed k] [Field L] (R : CommRingCat.{u})
    (f : Spec R ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced (Spec R)]
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) :
    IsReduced (pullback f g) := by
  obtain ⟨alpha, rfl⟩ := Spec.map_surjective f
  obtain ⟨beta, rfl⟩ := Spec.map_surjective g
  letI : Algebra k R := alpha.hom.toAlgebra
  letI : Algebra k L := beta.hom.toAlgebra
  have hft : RingHom.FiniteType alpha.hom :=
    HasRingHomProperty.Spec_iff.mp (inferInstance : LocallyOfFiniteType (Spec.map alpha))
  letI : Algebra.FiniteType k R := hft
  letI : _root_.IsReduced R := (affine_isReduced_iff R).mp inferInstance
  letI : _root_.IsReduced (R ⊗[k] L) := GM3Algebra.isReduced_tensor_field
  letI : IsReduced (Spec (CommRingCat.of (R ⊗[k] L))) := inferInstance
  change IsReduced (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k R L).hom

/-- Reducedness on EVERY test-field pullback via its actual affine cover. -/
theorem reduced_pullback_of_isAlgClosed
    {k L : Type u} [Field k] [IsAlgClosed k] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X]
    (g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) :
    IsReduced (pullback f g) := by
  let U := X.affineOpenCover
  let V := Scheme.Pullback.openCoverOfLeft U.openCover f g
  letI : ∀ i : V.I₀, IsReduced (V.X i) := fun i => by
    change IsReduced (pullback (U.f i ≫ f) g)
    letI : IsReduced (Spec (U.X i)) := isReduced_of_isOpenImmersion (U.f i)
    exact reduced_pullback_spec_of_isAlgClosed (U.X i) (U.f i ≫ f) g
  exact IsReduced.of_openCover V

/-- EXACT C3 consumer, with no additional supplied property/Factory. -/
theorem geomReducedOverAlgClosed :
    ZInQ.Contrib.CloudR2NOS.Step1.GeomReducedOverAlgClosed.{u} := by
  intro k _ _ X f _ _
  constructor
  intro L instL g Z a b h
  letI : IsReduced (pullback f g) := reduced_pullback_of_isAlgClosed f g
  exact isReduced_of_isOpenImmersion h.isoPullback.hom

end H5OriginalDVR.Lane5.GM3Geometry
