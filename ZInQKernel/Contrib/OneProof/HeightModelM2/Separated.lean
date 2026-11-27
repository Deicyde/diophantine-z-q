import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Morphisms out of a flat scheme are determined on the generic fibre

Over a ring `R` with an injective `R → K` (for a domain, its fraction field), let `X` be flat
over `Spec R` and `Y` separated over `Spec R`. Two `Spec R`-morphisms `f g : X → Y` that agree on
the generic fibre `X ×_R K → X` are equal (`ext_of_flat_of_generic`). This is the uniqueness of
extensions over a schematically dense subscheme (EGA I (9.5.6)-type; locator UNVERIFIED): the
equalizer of `f` and `g` is a closed subscheme (`Y` separated), and on an affine chart `Spec A` of
`X` the map `A → A ⊗_R K` is injective (`A` flat over `R`), so the equalizer is everything
(`ext_of_appTop_injective`, from Mathlib's `IsClosedImmersion.isIso_of_injective_of_isAffine`).

Consequence (`isCommMonObj_of_generic`): a group scheme over `Spec R`, flat and separated, whose
generic fibre is commutative, is commutative. The multiplication `μ` and `μ` composed with the
swap agree on the generic fibre (the base change functor is braided), hence everywhere. -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false

namespace ZInQ.HeightModelM2

/-- **Equalizer argument.** On an affine `X`, two morphisms to a separated `Y` that agree after a
map `W → X` injective on global functions are equal. -/
theorem ext_of_appTop_injective {X Y Z W : Scheme} [IsAffine X] (s : Y ⟶ Z) [IsSeparated s]
    {f g : X ⟶ Y} (h : f ≫ s = g ≫ s) (ι₀ : W ⟶ X) (hinj : Function.Injective ι₀.appTop)
    (hι₀ : ι₀ ≫ f = ι₀ ≫ g) : f = g := by
  let d := pullback.lift f g h
  let e : pullback d (pullback.diagonal s) ⟶ X := pullback.fst _ _
  let w : W ⟶ pullback d (pullback.diagonal s) := pullback.lift ι₀ (ι₀ ≫ f) (by
    apply pullback.hom_ext <;> simp [d, hι₀])
  have hw : w ≫ e = ι₀ := pullback.lift_fst _ _ _
  have he : Function.Injective e.appTop := by
    have h0 : ι₀.appTop = e.appTop ≫ w.appTop := by rw [← hw, Scheme.Hom.comp_appTop]
    intro a b hab
    apply hinj
    rw [h0]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]
  haveI := IsClosedImmersion.isIso_of_injective_of_isAffine he
  have h1 : e ≫ f = pullback.snd d (pullback.diagonal s) := by
    have := congrArg (· ≫ pullback.fst s s)
      (pullback.condition (f := d) (g := pullback.diagonal s))
    simpa [d, e] using this
  have h2 : e ≫ g = pullback.snd d (pullback.diagonal s) := by
    have := congrArg (· ≫ pullback.snd s s)
      (pullback.condition (f := d) (g := pullback.diagonal s))
    simpa [d, e] using this
  exact (cancel_epi e).mp (h1.trans h2.symm)

/-- `Spec.map φ` is injective on global functions when `φ` is injective. -/
theorem appTop_Spec_map_injective {R S : CommRingCat} (φ : R ⟶ S) (hφ : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by
  have h := Scheme.ΓSpecIso_inv_naturality φ
  have h' : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [h]; simp
  rw [h']
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1.comp
    (hφ.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)

/-- **Morphisms out of a flat scheme are determined on the generic fibre.** `X` flat over
`Spec R`, `Y` separated over `Spec R`, `R → K` injective: two `Spec R`-morphisms `X → Y` equal on
`X ×_{Spec R} Spec K` are equal. -/
theorem ext_of_flat_of_generic {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (hK : Function.Injective (algebraMap R K)) {X Y : Scheme} (p : X ⟶ Spec (.of R)) [Flat p]
    (q : Y ⟶ Spec (.of R)) [IsSeparated q] {f g : X ⟶ Y} (h : f ≫ q = g ≫ q)
    (hη : pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ f =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ g) : f = g := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  let A : CommRingCat := X.affineOpenCover.X i
  let u : Spec A ⟶ X := X.affineOpenCover.f i
  change u ≫ f = u ≫ g
  let φ : CommRingCat.of R ⟶ A := Spec.preimage (u ≫ p)
  have hφ : Spec.map φ = u ≫ p := Spec.map_preimage _
  have hflat : φ.hom.Flat := by
    have : IsOpenImmersion u := X.affineOpenCover.openCover.map_prop i
    have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra R A := φ.hom.toAlgebra
  haveI : Module.Flat R A := hflat
  let incl : A ⟶ CommRingCat.of (TensorProduct R A K) :=
    CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := K)).toRingHom
  have hinj : Function.Injective incl :=
    Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := A) (B := K) hK
  let jr : CommRingCat.of K ⟶ CommRingCat.of (TensorProduct R A K) :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom
  have hsq : Spec.map incl ≫ u ≫ p =
      Spec.map jr ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := K)
        (algebraMap R A r) =
      Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K) (algebraMap R K r)
    rw [AlgHom.commutes, AlgHom.commutes]
  let m := pullback.lift (Spec.map incl ≫ u) (Spec.map jr) (by simpa using hsq)
  have hm : m ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      Spec.map incl ≫ u := pullback.lift_fst _ _ _
  apply ext_of_appTop_injective q (by simp [h]) (Spec.map incl)
    (appTop_Spec_map_injective incl hinj)
  rw [← Category.assoc, ← Category.assoc, ← hm, Category.assoc, Category.assoc, hη]

/-- Commutativity transfers along an isomorphism of monoid objects. -/
theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {M N : C} [MonObj M] [MonObj N] (e : M ≅ N) [IsMonHom e.hom] [IsCommMonObj N] :
    IsCommMonObj M := by
  constructor
  have hμ : μ[M] = (e.hom ⊗ₘ e.hom) ≫ μ[N] ≫ e.inv := by
    rw [← Category.assoc, ← IsMonHom.mul_hom e.hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hμ, ← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
    ← Category.assoc (β_ N N).hom, IsCommMonObj.mul_comm]

/-- The base change of a morphism, followed by the projection, is the projection followed by the
morphism. -/
theorem pullback_map_left_fst {S T : Scheme} (j : T ⟶ S) {X Y : Over S} (h : X ⟶ Y) :
    ((Over.pullback j).map h).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ h.left := by
  simp

/-- **A flat separated group scheme with commutative generic fibre is commutative**: the
commutator vanishes on the generic fibre, which is schematically dense. -/
theorem isCommMonObj_of_generic {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (hK : Function.Injective (algebraMap R K)) (G : Over (Spec (.of R))) [GrpObj G]
    [Flat G.hom] [IsSeparated G.hom]
    (hc : letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G) :=
      Functor.grpObjObj
      IsCommMonObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G)) :
    IsCommMonObj G := by
  set j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  letI : GrpObj ((Over.pullback j).obj G) := Functor.grpObjObj
  have key : (Over.pullback j).map ((β_ G G).hom ≫ μ) = (Over.pullback j).map μ := by
    rw [← cancel_epi (Functor.LaxMonoidal.μ (Over.pullback j) G G), Functor.map_comp,
      ← Category.assoc, Functor.LaxBraided.braided, Category.assoc]
    exact IsCommMonObj.mul_comm ((Over.pullback j).obj G)
  have hflat : Flat (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  constructor
  apply Over.OverMorphism.ext
  apply ext_of_flat_of_generic hK (G ⊗ G).hom G.hom (by simp [pullback.condition])
  rw [← pullback_map_left_fst, key, pullback_map_left_fst]

end ZInQ.HeightModelM2
