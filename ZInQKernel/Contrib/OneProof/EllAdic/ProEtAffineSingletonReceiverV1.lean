import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

namespace RC53.EllAdic

universe u

/-- Factor maps use the algebra structure induced by the given map on global sections. -/
abbrev AffineFactorToLimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : Type u) [CommRing B] [Algebra Γ(Y, ⊤) B] : Type u :=
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] B

abbrev affineFactorRingHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {B : Type u} [CommRing B] [Algebra Γ(Y, ⊤) B]
    (i : AffineFactorToLimit f B) : Γ(X, ⊤) ⟶ CommRingCat.of B :=
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let j : Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] B := i
  CommRingCat.ofHom j.toRingHom

private theorem factorTriangle {X Y : Scheme.{u}} (f : X ⟶ Y)
    {B : Type u} [CommRing B] [Algebra Γ(Y, ⊤) B]
    (i : AffineFactorToLimit f B) :
    f.appTop ≫ affineFactorRingHom f i = CommRingCat.ofHom (algebraMap Γ(Y, ⊤) B) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let j : Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] B := i
  apply CommRingCat.hom_ext
  change j.toRingHom.comp (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = algebraMap Γ(Y, ⊤) B
  exact j.comp_algebraMap

private noncomputable abbrev toAffine {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    (k : Γ(X, ⊤) ⟶ R) : Spec R ⟶ X :=
  Spec.map k ≫ X.isoSpec.inv

private theorem toAffine_appTop {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}}
    (k : Γ(X, ⊤) ⟶ R) :
    (toAffine k).appTop ≫ (Scheme.ΓSpecIso R).hom = k := by
  change (Spec.map k ≫ X.isoSpec.inv).appTop ≫ (Scheme.ΓSpecIso R).hom = k
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop, Category.id_comp]

/-- The actual spectra of the algebra maps assemble a singleton cover over
`U` with the specified factorization through each given affine arrow. The
coefficient algebra may in particular be a common tensor refinement. -/
theorem proEt_affineSingleton_of_algebra
    {S : Scheme.{u}} (U : S.ProEt) [IsAffine U.left]
    (V : ℕ → S.ProEt) [∀ n, IsAffine (V n).left] (q : ∀ n, V n ⟶ U)
    (hq : ∀ n, WeaklyEtale (q n).left)
    (B : Type u) [CommRing B] [Algebra Γ(U.left, ⊤) B]
    (i : ∀ n, AffineFactorToLimit (q n).left B)
    (hff : (algebraMap Γ(U.left, ⊤) B).FaithfullyFlat)
    (hweak : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B)))) :
    ∃ (s : Spec (CommRingCat.of B) ⟶ S) (hs : WeaklyEtale s),
      letI : WeaklyEtale s := hs
      let W : S.ProEt := Scheme.ProEt.mk s
      ∃ (p : W ⟶ U) (r : ∀ n, W ⟶ V n),
        (∀ n, r n ≫ q n = p) ∧
        WeaklyEtale p.left ∧ Surjective p.left ∧ (∀ n, WeaklyEtale (r n).left) ∧
        Presieve.singleton p ∈ Scheme.ProEt.precoverage S U ∧
        p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
          CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B) ∧
        (∀ n, (r n).left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
          affineFactorRingHom (q n).left (i n)) := by
  let a : Γ(U.left, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) B)
  let k (n : ℕ) : Γ((V n).left, ⊤) ⟶ CommRingCat.of B := affineFactorRingHom (q n).left (i n)
  let p₀ : Spec (CommRingCat.of B) ⟶ U.left := toAffine a
  let r₀ (n : ℕ) : Spec (CommRingCat.of B) ⟶ (V n).left := toAffine (k n)
  have hfac (n : ℕ) : r₀ n ≫ (q n).left = p₀ := by
    change (Spec.map (k n) ≫ (V n).left.isoSpec.inv) ≫ (q n).left = Spec.map a ≫ U.left.isoSpec.inv
    rw [Category.assoc, ← Scheme.isoSpec_inv_naturality (q n).left, ← Spec.map_comp_assoc]
    exact congrArg (fun b : Γ(U.left, ⊤) ⟶ CommRingCat.of B => Spec.map b ≫ U.left.isoSpec.inv)
      (factorTriangle (q n).left (i n))
  let : WeaklyEtale p₀ :=
    (MorphismProperty.cancel_right_of_respectsIso @WeaklyEtale (Spec.map a) U.left.isoSpec.inv).mpr hweak
  let : Surjective p₀ :=
    (MorphismProperty.cancel_right_of_respectsIso @Surjective (Spec.map a) U.left.isoSpec.inv).mpr
      ((flat_and_surjective_SpecMap_iff a).mpr hff).2
  let : QuasiCompact p₀ := inferInstance
  let hs : WeaklyEtale (p₀ ≫ U.hom) := inferInstance
  let W : S.ProEt := Scheme.ProEt.mk (p₀ ≫ U.hom)
  let p : W ⟶ U := MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤) (X := S)
      (A := W) (B := U) p₀ rfl
  have hover (n : ℕ) : r₀ n ≫ (V n).hom = p₀ ≫ U.hom := by
    have hqover : (q n).left ≫ U.hom = (V n).hom := MorphismProperty.Over.w (q n)
    rw [← hqover, ← Category.assoc, hfac n]
  let r (n : ℕ) : W ⟶ V n := MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤) (X := S)
      (A := W) (B := V n) (r₀ n) (hover n)
  have hcover : Presieve.singleton p ∈ Scheme.ProEt.precoverage S U := by
    rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton]
    change Presieve.singleton p₀ ∈ Scheme.propQCPrecoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) U.left
    exact Scheme.Hom.singleton_mem_propQCPrecoverage
      (P := (@WeaklyEtale : MorphismProperty Scheme.{u})) (f := p₀) (inferInstance : WeaklyEtale p₀)
  refine ⟨p₀ ≫ U.hom, hs, p, r, ?_, ?_, ?_, ?_, hcover, ?_, ?_⟩
  · intro n
    apply MorphismProperty.Over.Hom.ext (P := @WeaklyEtale) (Q := ⊤) (X := S)
    exact hfac n
  · exact (inferInstance : WeaklyEtale p₀)
  · exact (inferInstance : Surjective p₀)
  · intro n
    change WeaklyEtale (r₀ n)
    let : WeaklyEtale (q n).left := hq n
    let : WeaklyEtale (r₀ n ≫ (q n).left) := by
      rw [hfac n]
      exact (inferInstance : WeaklyEtale p₀)
    exact WeaklyEtale.of_comp (r₀ n) (q n).left
  · exact toAffine_appTop a
  · intro n
    exact toAffine_appTop (k n)

end RC53.EllAdic
