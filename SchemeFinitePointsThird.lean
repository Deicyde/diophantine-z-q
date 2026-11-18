import AffinePointsFirst
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Finitely many rational points on a finite-type scheme over a finite field

A quasi-compact scheme has a finite affine open cover. A rational point
factors through a chart containing its unique source point, and every
chart has only finitely many actual algebra maps into the finite field.
No finiteness of the desired rational-point set is supplied as a premise.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableGeometry.FinitePoints

variable (k : Type) [Field k] [Finite k]

/-- Actual points of an arbitrary affine structure map to the finite field form a finite type. -/
theorem finite_affine_structure_points (R : CommRingCat) (p : Spec R ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] :
    Finite (affinePointDomain k ⟶ Over.mk p) := by
  let f := Spec.preimage p
  let : Algebra k R := f.hom.toAlgebra
  have hp : Spec.map (CommRingCat.ofHom (algebraMap k R)) = p := Spec.map_preimage p
  have hft : (algebraMap k R).FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    change LocallyOfFiniteType (Spec.map (Spec.preimage p))
    rw [Spec.map_preimage]
    infer_instance
  let : Algebra.FiniteType k R := RingHom.finiteType_algebraMap.mp hft
  rw [← hp]
  exact finite_affine_points k R

/-- Actual rational points of the displayed locally finite type, quasi-compact scheme are finite. -/
theorem finite_scheme_points (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [CompactSpace X.left] :
    Finite (affinePointDomain k ⟶ X) := by
  classical
  obtain ⟨V, _, hVfinite, _⟩ := QuasiCompactCover.exists_hom
    (P := @IsOpenImmersion) X.left.affineCover
  let : Finite V.I₀ := hVfinite
  let Y (i : V.I₀) : Over (Spec (CommRingCat.of k)) := Over.mk (V.f i ≫ X.hom)
  have hft (i : V.I₀) : LocallyOfFiniteType (Y i).hom := by
    change LocallyOfFiniteType (V.f i ≫ X.hom)
    let : IsOpenImmersion (V.f i) := V.map_prop i
    infer_instance
  have hfinite (i : V.I₀) : Finite (affinePointDomain k ⟶ Y i) :=
    @finite_affine_structure_points k _ _ (V.X i) (V.f i ≫ X.hom) (hft i)
  let : ∀ i : V.I₀, Finite (affinePointDomain k ⟶ Y i) := hfinite
  let inc (i : V.I₀) : Y i ⟶ X := Over.homMk (V.f i) rfl
  let f : (Σ i : V.I₀, affinePointDomain k ⟶ Y i) → (affinePointDomain k ⟶ X) :=
    fun p ↦ p.2 ≫ inc p.1
  apply Finite.of_surjective f
  intro x
  let z : (affinePointDomain k).left := IsLocalRing.closedPoint k
  let i := V.cover.idx (x.left z)
  have hxrange : Set.range x.left ⊆ Set.range (V.f i) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = z := Subsingleton.elim (α := PrimeSpectrum k) a z
    rw [ha]
    exact V.cover.covers (x.left z)
  let : IsOpenImmersion (V.f i) := V.map_prop i
  let u : (affinePointDomain k).left ⟶ Spec (V.X i) := IsOpenImmersion.lift (V.f i) x.left hxrange
  have hu : u ≫ V.f i = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : affinePointDomain k ⟶ Y i := Over.homMk u (by
    change u ≫ (V.f i ≫ X.hom) = (affinePointDomain k).hom
    rw [← Category.assoc, hu, Over.w x])
  refine ⟨⟨i, y⟩, ?_⟩
  exact Over.OverMorphism.ext hu

end SemistableGeometry.FinitePoints
