import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Pure field ranks of the actual native mapping cone

Every map below is the actual HomologicalComplex.homologyMap of the given
chain map or the actual mappingCone.inr. Canonical homology-functor factor
isomorphisms only identify native homology with its homotopy-category
realization; their naturality is used explicitly. No equivalence is selected
from rank data, no rank Fact is supplied, and the cone is never assumed
nonnegative. In particular its degree -1 term is permitted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Actual canonical homology comparison commutes with the actual chain map. -/
theorem cone_homology_comparison_naturality
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D) (n : ℤ)
    (x : (HomotopyCategory.homologyFunctor (ModuleCat.{u} K) (.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj C)) :
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) n).hom.app D
      ((HomotopyCategory.homologyFunctor _ _ n).map
        ((HomotopyCategory.quotient _ _).map Φ) x) =
    HomologicalComplex.homologyMap Φ n
      ((HomotopyCategory.homologyFunctorFactors _ _ n).hom.app C x) := by
  have hn := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) n).hom.naturality Φ
  change (HomotopyCategory.homologyFunctor (ModuleCat.{u} K) (.up ℤ) n).map
      ((HomotopyCategory.quotient _ _).map Φ) ≫
      (HomotopyCategory.homologyFunctorFactors _ _ n).hom.app D =
    (HomotopyCategory.homologyFunctorFactors _ _ n).hom.app C ≫
      HomologicalComplex.homologyMap Φ n at hn
  have hv := congrArg (fun f => f x) hn
  change (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) n).hom.app D
      ((HomotopyCategory.homologyFunctor _ _ n).map
        ((HomotopyCategory.quotient _ _).map Φ) x) =
    HomologicalComplex.homologyMap Φ n
      ((HomotopyCategory.homologyFunctorFactors _ _ n).hom.app C x) at hv
  exact hv

/-- Exactness at the ACTUAL degree-n target homology in the mapping-cone LES. -/
theorem cone_homology_range_eq_ker
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D) (n : ℤ) :
    LinearMap.range (HomologicalComplex.homologyMap Φ n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) n).hom := by
  let F := HomotopyCategory.homologyFunctor (ModuleCat.{u} K) (.up ℤ) n
  let T := CochainComplex.mappingCone.triangleh Φ
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished Φ
  let S := (Pretriangulated.shortComplexOfDistTriangle T hT).map F
  have hS : S.Exact := F.map_distinguished_exact T hT
  let e := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) n
  let ec := (e.app C).toLinearEquiv
  let ed := (e.app D).toLinearEquiv
  let ee := (e.app (CochainComplex.mappingCone Φ)).toLinearEquiv
  let f := (HomologicalComplex.homologyMap Φ n).hom
  let g := (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) n).hom
  have nf (x : S.X₁) : ed (S.f x) = f (ec x) := cone_homology_comparison_naturality C D Φ n x
  have ng (y : S.X₂) : ee (S.g y) = g (ed y) :=
    cone_homology_comparison_naturality D (CochainComplex.mappingCone Φ)
      (CochainComplex.mappingCone.inr Φ) n y
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change g (f x) = 0
    calc
      g (f x) = g (ed (S.f (ec.symm x))) := by rw [nf]; simp
      _ = ee (S.g (S.f (ec.symm x))) := (ng _).symm
      _ = 0 := by rw [S.moduleCat_zero_apply]; exact map_zero ee
  · intro hz
    change g z = 0 at hz
    have hzh : S.g (ed.symm z) = 0 := by
      apply ee.injective
      rw [ng, map_zero ee]
      simpa only [LinearEquiv.apply_symm_apply] using hz
    obtain ⟨xh, hxh⟩ := (S.moduleCat_exact_iff.mp hS) (ed.symm z) hzh
    refine ⟨ec xh, ?_⟩
    change f (ec xh) = z
    rw [← nf, hxh]
    simp

/-- The actual cone inclusion is onto H0 when the ACTUAL H1(Φ) is injective.
This uses exactness at H1(C) and H0(Cone), with no finite/rank hypothesis. -/
theorem cone_hZero_inr_surjective_of_hOne_injective
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D)
    (hOne : Function.Injective (HomologicalComplex.homologyMap Φ 1)) :
    Function.Surjective (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) 0) := by
  let F := HomotopyCategory.homologyFunctor (ModuleCat.{u} K) (.up ℤ) 0
  let T := CochainComplex.mappingCone.triangleh Φ
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished Φ
  let e1 := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) 1
  let ec1 := (e1.app C).toLinearEquiv
  let ed1 := (e1.app D).toLinearEquiv
  have hn (x : (F.shift (1 : ℤ)).obj T.obj₁) :
      ed1 ((F.shift (1 : ℤ)).map T.mor₁ x) = HomologicalComplex.homologyMap Φ 1 (ec1 x) :=
    cone_homology_comparison_naturality C D Φ 1 x
  have hi : Function.Injective ((F.shift (1 : ℤ)).map T.mor₁) := by
    intro a b hab
    apply ec1.injective
    apply hOne
    rw [← hn, ← hn, hab]
  letI : Mono ((F.shift (1 : ℤ)).map T.mor₁) := (ModuleCat.mono_iff_injective _).mpr hi
  have hδ : F.homologySequenceδ T 0 1 rfl = 0 :=
    (F.homologySequence_mono_shift_map_mor₁_iff T hT 0 1 rfl).mp inferInstance
  have hep : Epi ((F.shift (0 : ℤ)).map T.mor₂) :=
    (F.homologySequence_epi_shift_map_mor₂_iff T hT 0 1 rfl).mpr hδ
  have hsurj := (ModuleCat.epi_iff_surjective ((F.shift (0 : ℤ)).map T.mor₂)).mp hep
  let e0 := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} K) (.up ℤ) 0
  let ed0 := (e0.app D).toLinearEquiv
  let ee0 := (e0.app (CochainComplex.mappingCone Φ)).toLinearEquiv
  intro z
  obtain ⟨yh, hyh⟩ := hsurj (ee0.symm z)
  refine ⟨ed0 yh, ?_⟩
  have hn0 := cone_homology_comparison_naturality D (CochainComplex.mappingCone Φ)
    (CochainComplex.mappingCone.inr Φ) 0 yh
  change ee0 (((F.shift (0 : ℤ)).map T.mor₂) yh) =
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) 0 (ed0 yh) at hn0
  rw [← hn0, hyh]
  simp

/-- Finite target H0 and ACTUAL H0(Φ) injection give finite source H0,
without any dimension-one input or selected rank equivalence. -/
theorem finite_hZero_source_of_hZero_injective
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D)
    [Module.Finite K (D.homology 0)]
    (hZero : Function.Injective (HomologicalComplex.homologyMap Φ 0)) :
    Module.Finite K (C.homology 0) :=
  FiniteDimensional.of_injective (HomologicalComplex.homologyMap Φ 0).hom hZero

/-- Finite target H0 and ACTUAL H1(Φ) injection give finite ACTUAL cone H0,
through the genuine cone-inclusion surjection, with no rank hypothesis. -/
theorem finite_hZero_mappingCone_of_hOne_injective
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D)
    [Module.Finite K (D.homology 0)]
    (hOne : Function.Injective (HomologicalComplex.homologyMap Φ 1)) :
    Module.Finite K ((CochainComplex.mappingCone Φ).homology 0) :=
  Module.Finite.of_surjective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) 0).hom
    (cone_hZero_inr_surjective_of_hOne_injective C D Φ hOne)

/-- EXACT §5b ABI: h0(D)=2 and h0(actual Cone Φ)≤1 force h0(C)≥1. -/
theorem one_le_hZero_of_cone_bound
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D)
    [Module.Finite K (C.homology 0)]
    [Module.Finite K (D.homology 0)]
    [Module.Finite K ((CochainComplex.mappingCone Φ).homology 0)]
    (hD : Module.finrank K (D.homology 0) = 2)
    (hCone : Module.finrank K ((CochainComplex.mappingCone Φ).homology 0) ≤ 1) :
    1 ≤ Module.finrank K (C.homology 0) := by
  let f := (HomologicalComplex.homologyMap Φ 0).hom
  let g := (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) 0).hom
  have he : LinearMap.range f = LinearMap.ker g := cone_homology_range_eq_ker C D Φ 0
  have hr : Module.finrank K (LinearMap.range g) + Module.finrank K (LinearMap.ker g) =
      Module.finrank K (D.homology 0) := by
    have h := (LinearMap.ker g).finrank_quotient_add_finrank
    rwa [g.quotKerEquivRange.finrank_eq] at h
  have hf := LinearMap.finrank_range_le f
  have hg : Module.finrank K (LinearMap.range g) ≤
      Module.finrank K ((CochainComplex.mappingCone Φ).homology 0) := Submodule.finrank_le _
  rw [← he] at hr
  omega

/-- Initial-fibre rank one from the ACTUAL H0/H1 injections and h0(C)=1,h0(D)=2.
Only finite H0(D) is supplied: finiteness of H0(C) and H0(Cone) is DERIVED
from the actual injections/surjections, not an extra rank-selected hypothesis. -/
theorem hZero_mappingCone_eq_one
    {K : Type u} [Field K]
    (C D : CochainComplex (ModuleCat.{u} K) ℤ) (Φ : C ⟶ D)
    [Module.Finite K (D.homology 0)]
    (hC : Module.finrank K (C.homology 0) = 1)
    (hD : Module.finrank K (D.homology 0) = 2)
    (hZero : Function.Injective (HomologicalComplex.homologyMap Φ 0))
    (hOne : Function.Injective (HomologicalComplex.homologyMap Φ 1)) :
    Module.finrank K ((CochainComplex.mappingCone Φ).homology 0) = 1 := by
  let f := (HomologicalComplex.homologyMap Φ 0).hom
  let g := (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr Φ) 0).hom
  letI : Module.Finite K (C.homology 0) := finite_hZero_source_of_hZero_injective C D Φ hZero
  have hsurj : Function.Surjective g := cone_hZero_inr_surjective_of_hOne_injective C D Φ hOne
  letI : Module.Finite K ((CochainComplex.mappingCone Φ).homology 0) :=
    finite_hZero_mappingCone_of_hOne_injective C D Φ hOne
  have he : LinearMap.range f = LinearMap.ker g := cone_homology_range_eq_ker C D Φ 0
  have hf : Module.finrank K (LinearMap.range f) = Module.finrank K (C.homology 0) :=
    LinearMap.finrank_range_of_inj hZero
  have hg : Module.finrank K (LinearMap.range g) =
      Module.finrank K ((CochainComplex.mappingCone Φ).homology 0) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact (Submodule.topEquiv : (⊤ : Submodule K ((CochainComplex.mappingCone Φ).homology 0)) ≃ₗ[K]
      (CochainComplex.mappingCone Φ).homology 0).finrank_eq
  have hr : Module.finrank K (LinearMap.range g) + Module.finrank K (LinearMap.ker g) =
      Module.finrank K (D.homology 0) := by
    have h := (LinearMap.ker g).finrank_quotient_add_finrank
    rwa [g.quotKerEquivRange.finrank_eq] at h
  rw [← he, hf, hg, hC, hD] at hr
  omega

end ZInQ.Contrib.CloudR2Poincare.L2
