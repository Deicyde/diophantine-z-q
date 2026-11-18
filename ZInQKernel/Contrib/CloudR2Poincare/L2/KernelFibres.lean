import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import ZInQKernel.HDecomp.Objects

/-!
# Finite kernels and fibres: the L2 interface

H-72 round 2, lane L2. These are proved bridges, not an assertion that an ample
polarization has finite kernel. The geometric finiteness input is explicit in
each theorem and must be supplied by an ampleness proof.

The first lemma translates a finite kernel on points into finite fibres on
points. The last lemma is the exact finite-morphism/surjectivity interface for
`PkgI3.AbVar.IsIsogenyMor` and therefore for `PolarizationRetract`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- Each fibre of a group homomorphism with finite kernel is finite. This statement
uses the actual kernel, not a chosen finite quotient or a replacement group. -/
theorem finite_fibre_of_finite_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hker : (f.ker : Set G).Finite) (y : H) :
    {x : G | f x = y}.Finite := by
  classical
  by_cases hne : {x : G | f x = y}.Nonempty
  · obtain ⟨a, ha⟩ := hne
    apply Set.Finite.of_finite_image (f := fun x : G => a⁻¹ * x)
    · refine hker.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      change f (a⁻¹ * x) = 1
      change f x = y at hx
      change f a = y at ha
      simp only [map_mul, map_inv, hx, ha, inv_mul_cancel]
    · intro x hx z hz h
      exact mul_left_cancel h
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

/-- A finite neutral fibre of a group-object homomorphism gives finite fibres on
all `T`-points. In particular this applies to geometric points. -/
theorem finite_point_fibre_of_finite_point_kernel {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {X Y : C} [GrpObj X] [GrpObj Y]
    (f : X ⟶ Y) [IsMonHom f] (T : C)
    (hker : {a : T ⟶ X | a ≫ f = 1}.Finite) (b : T ⟶ Y) :
    {a : T ⟶ X | a ≫ f = b}.Finite := by
  exact finite_fibre_of_finite_kernel (IsMonHom.monoidHom f T) hker b

/-- Properness turns finite scheme-theoretic fibres (at the level of the
underlying topological spaces) into a finite morphism by Zariski's main theorem. -/
theorem isFinite_of_finite_fibres {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    (hf : ∀ y : Y, (f ⁻¹' {y}).Finite) : IsFinite f := by
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f hf
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Over an algebraically closed field, finite fibres on rational points suffice
for a proper morphism between finite-type schemes to be finite. The proof uses
the actual closed points of each fibre and the open quasi-finite locus. -/
theorem isFinite_of_finite_rational_point_fibres {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsProper f.left]
    (hf : ∀ b : 𝟙_ (Over (Spec (.of k))) ⟶ Y,
      {a : 𝟙_ (Over (Spec (.of k))) ⟶ X | a ≫ f = b}.Finite) : IsFinite f.left := by
  classical
  let pt : Spec (.of k) := IsLocalRing.closedPoint k
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hq (x : X.left) (hx : IsClosed ({x} : Set X.left)) : f.left.QuasiFiniteAt x := by
    let a : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp _ _ _)
    let b : 𝟙_ (Over (Spec (.of k))) ⟶ Y := a ≫ f
    let eval : (𝟙_ (Over (Spec (.of k))) ⟶ X) → X.left :=
      fun p => p.left (pt)
    have hclosed : (f.left ⁻¹' {f.left x} ∩ closedPoints X.left).Finite := by
      refine ((hf b).image eval).subset ?_
      intro z hz
      rcases hz with ⟨hzf, hzc⟩
      change f.left z = f.left x at hzf
      change IsClosed ({z} : Set X.left) at hzc
      let az : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
        Over.homMk (pointOfClosedPoint X.hom z hzc) (pointOfClosedPoint_comp _ _ _)
      refine ⟨az, ?_, ?_⟩
      · apply Over.OverMorphism.ext
        apply ext_of_apply_closedPoint_eq Y.hom (Over.w (az ≫ f)) (Over.w b)
        change f.left ((pointOfClosedPoint X.hom z hzc) (pt)) =
          f.left ((pointOfClosedPoint X.hom x hx) (pt))
        rw [pointOfClosedPoint_apply, pointOfClosedPoint_apply]
        exact hzf
      · change (pointOfClosedPoint X.hom z hzc) (pt) = z
        exact pointOfClosedPoint_apply _ _ _ _
    have hy : IsClosed ({f.left x} : Set Y.left) := by
      simpa using f.left.isClosedMap _ hx
    have hF : IsClosed (f.left ⁻¹' {f.left x}) := hy.preimage f.left.continuous
    have hclosed' : IsClosed (f.left ⁻¹' {f.left x} ∩ closedPoints X.left) := by
      rw [← Set.biUnion_of_singleton (f.left ⁻¹' {f.left x} ∩ closedPoints X.left)]
      exact hclosed.isClosed_biUnion fun z hz => hz.2
    have hEq := closure_inter_closedPoints hF
    rw [hclosed'.closure_eq] at hEq
    have hfinite : (f.left ⁻¹' {f.left x}).Finite := hEq ▸ hclosed
    have : Finite (f.left.fiber (f.left x)) :=
      (f.left.fiberHomeo (f.left x)).finite_iff.mpr hfinite
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  have : LocallyQuasiFinite f.left := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine eq_top_iff.mpr fun x _ => ?_
    by_contra hx
    obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints
      (Z := (f.left.quasiFiniteLocus : Set X.left)ᶜ) ⟨x, hx⟩
      f.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
    exact hz (hq z hzclosed)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

/-- On an algebraically closed field, a finite actual point kernel makes a
proper group-scheme homomorphism finite. No kernel scheme or dual is assumed. -/
theorem isFinite_of_finite_rational_point_kernel {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsMonHom f] [IsProper f.left]
    (hker : {a : 𝟙_ (Over (Spec (.of k))) ⟶ X | a ≫ f = 1}.Finite) : IsFinite f.left :=
  isFinite_of_finite_rational_point_fibres f
    (finite_point_fibre_of_finite_point_kernel f _ hker)

/-- The underlying morphism of an actual homomorphism of abelian varieties is
proper; no extra properness or projectivity assumption is required. -/
theorem isProper_abVar_hom {k : Type} [Field k] {A D : PkgI3.AbVar k}
    (f : PkgI3.AbVar.Hom A D) : IsProper f.hom.left := by
  haveI : IsProper (f.hom.left ≫ D.X.hom) := by
    rw [f.hom.w]
    infer_instance
  exact IsProper.of_comp f.hom.left D.X.hom

/-- Exact interface used with the dual constructed by L1: finite fibres on the
actual underlying scheme morphism plus surjectivity imply `IsIsogenyMor`.
This theorem does not assume the desired isogeny as a `Fact`. -/
theorem isIsogenyMor_of_finite_fibres {k : Type} [Field k]
    {B D : PkgI3.AbVar k} (f : PkgI3.AbVar.Hom B D)
    (hf : ∀ y : D.X.left, (f.hom.left ⁻¹' {y}).Finite)
    (hs : Surjective f.hom.left) : PkgI3.AbVar.IsIsogenyMor f.hom := by
  letI : IsProper f.hom.left := isProper_abVar_hom f
  exact ⟨isFinite_of_finite_fibres f.hom.left hf, hs⟩

/-- The same interface in the precise composite spelling of `PolarizationRetract`.
L1 supplies the dual and the homomorphism; L2 supplies finite fibres; the
surjectivity/dimension argument remains explicit. -/
theorem composite_isIsogenyMor_of_finite_fibres {k : Type} [Field k]
    {J B D : PkgI3.AbVar k} (i : PkgI3.AbVar.Hom B J) (φ : PkgI3.AbVar.Hom J D)
    (hf : ∀ y : D.X.left, ((i.hom ≫ φ.hom).left ⁻¹' {y}).Finite)
    (hs : Surjective (i.hom ≫ φ.hom).left) :
    PkgI3.AbVar.IsIsogenyMor (i.hom ≫ φ.hom) := by
  exact isIsogenyMor_of_finite_fibres (PkgI3.AbVar.Hom.mk' (i.hom ≫ φ.hom)) hf hs

end ZInQ.Contrib.CloudR2Poincare.L2
