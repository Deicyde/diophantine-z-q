import FrobeniusAffineDescentSecond
import SchemeFinitePointsThird

/-!
# Actual geometric scheme points fixed by a Frobenius power

The finite fixed intermediate field is constructed from the given field
Frobenius. An actual fixed Spec-point factors into an affine open chart;
its coordinates descend to that field and give an actual descended point.
A finite affine cover then proves finiteness of the genuine fixed-point
type. Neither that finiteness nor a finite-group bound is assumed.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableGeometry.FrobeniusFixed

variable {k L : Type} [Field k] [Field L] [Algebra k L]

/-- Actual affine geometric points are determined by their actual coordinate algebra maps. -/
theorem coordinates_injective (R : Type) [CommRing R] [Algebra k R] :
    Function.Injective (coordinates (k := k) (L := L) R) := by
  intro x y h
  apply Over.OverMorphism.ext
  have he : Spec.preimage x.left = Spec.preimage y.left := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h
  rw [← Spec.map_preimage x.left, ← Spec.map_preimage y.left, he]

/-- Actual affine points valued in a finite field are finite, also relative to a smaller base field. -/
theorem finite_affine_valued_points (R : Type) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [Finite L] :
    Finite (pointDomain (k := k) (L := L) ⟶ algebraScheme R) := by
  let : Finite (R →ₐ[k] L) := SemistableGeometry.FinitePoints.finite_algHom_of_finiteType k R L
  exact Finite.of_injective _ (coordinates_injective R)

/-- The native affine structure map supplies the algebra structure and finite-type generators. -/
theorem finite_structure_valued_points (R : CommRingCat)
    (p : Spec R ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [Finite L] :
    Finite (pointDomain (k := k) (L := L) ⟶ Over.mk p) := by
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
  exact finite_affine_valued_points R

/-- The actual point type over a finite extension coefficient field is finite. -/
theorem finite_valued_points (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [CompactSpace X.left] [Finite L] :
    Finite (pointDomain (k := k) (L := L) ⟶ X) := by
  classical
  obtain ⟨V, _, hVfinite, _⟩ := QuasiCompactCover.exists_hom
    (P := @IsOpenImmersion) X.left.affineCover
  let : Finite V.I₀ := hVfinite
  let Y (i : V.I₀) : Over (Spec (CommRingCat.of k)) := Over.mk (V.f i ≫ X.hom)
  have hft (i : V.I₀) : LocallyOfFiniteType (Y i).hom := by
    change LocallyOfFiniteType (V.f i ≫ X.hom)
    let : IsOpenImmersion (V.f i) := V.map_prop i
    infer_instance
  let : ∀ i : V.I₀, Finite (pointDomain (k := k) (L := L) ⟶ Y i) := fun i ↦
    @finite_structure_valued_points k L _ _ _ (V.X i) (V.f i ≫ X.hom) (hft i) inferInstance
  let inc (i : V.I₀) : Y i ⟶ X := Over.homMk (V.f i) rfl
  let f : (Σ i : V.I₀, pointDomain (k := k) (L := L) ⟶ Y i) → (pointDomain (k := k) (L := L) ⟶ X) :=
    fun p ↦ p.2 ≫ inc p.1
  apply Finite.of_surjective f
  intro x
  let z : (pointDomain (k := k) (L := L)).left := IsLocalRing.closedPoint L
  let i := V.cover.idx (x.left z)
  have hxrange : Set.range x.left ⊆ Set.range (V.f i) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = z := Subsingleton.elim (α := PrimeSpectrum L) a z
    rw [ha]
    exact V.cover.covers (x.left z)
  let : IsOpenImmersion (V.f i) := V.map_prop i
  let u : (pointDomain (k := k) (L := L)).left ⟶ Spec (V.X i) :=
    IsOpenImmersion.lift (V.f i) x.left hxrange
  have hu : u ≫ V.f i = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : pointDomain (k := k) (L := L) ⟶ Y i := Over.homMk u (by
    change u ≫ (V.f i ≫ X.hom) = (pointDomain (k := k) (L := L)).hom
    rw [← Category.assoc, hu, Over.w x])
  exact ⟨⟨i, y⟩, Over.OverMorphism.ext hu⟩

/-- Every actual scheme point fixed by the field automorphism power descends through an actual affine chart. -/
theorem point_descends (σ : L ≃ₐ[k] L) (r : ℕ)
    (X : Over (Spec (CommRingCat.of k))) [CompactSpace X.left]
    (x : pointDomain (k := k) (L := L) ⟶ X)
    (hx : algebraPointMap (σ ^ r).toAlgHom ≫ x = x) :
    ∃ y : algebraScheme (k := k) (field σ r) ⟶ X,
      algebraPointMap (IsScalarTower.toAlgHom k (field σ r) L) ≫ y = x := by
  classical
  obtain ⟨V, _, _, _⟩ := QuasiCompactCover.exists_hom
    (P := @IsOpenImmersion) X.left.affineCover
  let z : (pointDomain (k := k) (L := L)).left := IsLocalRing.closedPoint L
  let i := V.cover.idx (x.left z)
  have hxrange : Set.range x.left ⊆ Set.range (V.f i) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = z := Subsingleton.elim (α := PrimeSpectrum L) a z
    rw [ha]
    exact V.cover.covers (x.left z)
  let : IsOpenImmersion (V.f i) := V.map_prop i
  let u : (pointDomain (k := k) (L := L)).left ⟶ Spec (V.X i) :=
    IsOpenImmersion.lift (V.f i) x.left hxrange
  have hu : u ≫ V.f i = x.left := IsOpenImmersion.lift_fac _ _ _
  let p := V.f i ≫ X.hom
  let : Algebra k (V.X i) := (Spec.preimage p).hom.toAlgebra
  have hp : Spec.map (CommRingCat.ofHom (algebraMap k (V.X i))) = p := Spec.map_preimage p
  let inc : algebraScheme (k := k) (V.X i) ⟶ X := Over.homMk (V.f i) hp.symm
  let y : pointDomain (k := k) (L := L) ⟶ algebraScheme (V.X i) := Over.homMk u (by
    change u ≫ Spec.map (CommRingCat.ofHom (algebraMap k (V.X i))) =
      (pointDomain (k := k) (L := L)).hom
    rw [hp, ← Category.assoc, hu, Over.w x])
  have hufix : Spec.map (CommRingCat.ofHom ((σ ^ r : L ≃ₐ[k] L) : L →+* L)) ≫ u = u := by
    apply (cancel_mono (V.f i)).mp
    rw [Category.assoc, hu]
    exact congrArg Over.Hom.left hx
  have hyfix : algebraPointMap (σ ^ r).toAlgHom ≫ y = y := Over.OverMorphism.ext hufix
  obtain ⟨d, hd⟩ := affine_point_descends σ r (V.X i) y hyfix
  refine ⟨d ≫ inc, ?_⟩
  rw [← Category.assoc, hd]
  exact Over.OverMorphism.ext hu

/-- The fixed-point type is the literal fixed subset of actual geometric Spec-points. -/
def fixedPoints (σ : L ≃ₐ[k] L) (r : ℕ) (X : Over (Spec (CommRingCat.of k))) :=
  {x : pointDomain (k := k) (L := L) ⟶ X // algebraPointMap (σ ^ r).toAlgHom ≫ x = x}

/-- Finiteness of actual Frobenius-power-fixed geometric points, without a supplied fixed-point bound. -/
theorem finite_fixedPoints (σ : L ≃ₐ[k] L) (q : ℕ) (hq : 2 ≤ q)
    (hσ : ∀ a : L, σ a = a ^ q) (r : ℕ) (hr : 0 < r)
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom] [CompactSpace X.left] :
    Finite (fixedPoints σ r X) := by
  classical
  let : Finite (field σ r) := finite_field σ q hq hσ r hr
  let : Finite (algebraScheme (k := k) (field σ r) ⟶ X) :=
    finite_valued_points (k := k) (L := field σ r) X
  let d : fixedPoints σ r X → (algebraScheme (k := k) (field σ r) ⟶ X) :=
    fun x ↦ Classical.choose (point_descends σ r X x.1 x.2)
  have hd (x : fixedPoints σ r X) :
      algebraPointMap (IsScalarTower.toAlgHom k (field σ r) L) ≫ d x = x.1 :=
    Classical.choose_spec (point_descends σ r X x.1 x.2)
  apply Finite.of_injective d
  intro x y h
  apply Subtype.ext
  rw [← hd x, ← hd y, h]

end SemistableGeometry.FrobeniusFixed
