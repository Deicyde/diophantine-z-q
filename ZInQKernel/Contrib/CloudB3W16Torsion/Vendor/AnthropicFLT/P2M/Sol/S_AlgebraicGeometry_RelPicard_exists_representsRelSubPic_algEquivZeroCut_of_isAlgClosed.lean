/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurve hiding genus

namespace P2mJacAbs

variable (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [IsIntegral C]

section instances

omit [SmoothOfRelativeDimension 1 c] in

theorem geometricallyIntegral : GeometricallyIntegral c :=
  geometricallyIntegral_of_isAlgClosed c

end instances

theorem finset_subset_affineOpen_of_iso {X Y : Scheme.{u}} (Φ : X ≅ Y)
    (h : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    ∀ F : Finset Y, ∃ U : Y.Opens, IsAffineOpen U ∧ ∀ y ∈ F, y ∈ U := by
  classical
  intro F
  obtain ⟨U, hU, hmem⟩ := h (F.image (fun y => Φ.inv y))
  refine ⟨Φ.inv ⁻¹ᵁ U, hU.preimage_of_isIso Φ.inv, fun y hy => ?_⟩
  exact hmem _ (Finset.mem_image_of_mem _ hy)

omit [SmoothOfRelativeDimension 1 c] [IsIntegral C] in

theorem point_ext_of_comp_eq {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (h : s ≫ x.1 = s ≫ y.1) : x = y := by
  apply Subtype.ext
  refine ext_of_apply_closedPoint_eq c x.2 y.2 ?_
  have hs : s (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have := congrArg (fun φ : Spec (CommRingCat.of K) ⟶ C => φ (IsLocalRing.closedPoint K)) h
  simpa [Scheme.Hom.comp_apply, hs] using this

omit [SmoothOfRelativeDimension 1 c] [IsIntegral C] in

theorem sectionFibrePoint_injective {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    Function.Injective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c =>
      (sectionFibrePoint x s).1) := by
  intro x y hxy
  apply point_ext_of_comp_eq k c s
  have := congrArg (· ≫ pullback.fst c s) hxy
  simpa [sectionFibrePoint, pullback.lift_fst] using this

theorem exists_model_self :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L) (Φ : M.C ≅ C),
      Φ.hom ≫ c = M.toBase := by
  haveI := geometricallyIntegral k c
  obtain ⟨L, _, _, M, e, he, -, -, -⟩ :=
    SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed k c k (𝟙 _)
  refine ⟨L, inferInstance, inferInstance, M, e ≪≫ asIso (pullback.fst c (𝟙 _)), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, pullback.condition, Category.comp_id]
  exact he

include c in

private theorem _root_.P2mJacAbs.finset_subset_affineOpen :
    ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  obtain ⟨L, _, _, M, Φ, -⟩ := exists_model_self k c
  exact finset_subset_affineOpen_of_iso Φ M.finset_subset_affineOpen
-- The private affine-open helper is module-local; qualify its use directly.
theorem infinite_points : Infinite (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) := by
  obtain ⟨L, _, _, M, Φ, hΦ⟩ := exists_model_self k c
  haveI : Infinite (Place k L) := CurveModel.infinite_place M
  let ι : Place k L → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c := fun v =>
    ⟨(M.pointEquivPlace.symm v).1 ≫ Φ.hom, by rw [Category.assoc, hΦ]; exact (M.pointEquivPlace.symm v).2⟩
  refine Infinite.of_injective ι fun v w hvw => ?_
  have h1 : (M.pointEquivPlace.symm v).1 = (M.pointEquivPlace.symm w).1 := by
    have := congrArg Subtype.val hvw
    simpa [ι, cancel_mono] using this
  exact M.pointEquivPlace.symm.injective (Subtype.ext h1)

include c in

theorem nonempty_twoAffineOpenCover : Nonempty C.TwoAffineOpenCover := by
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ :=
    AlgebraicCurve.exists_isAffineOpen_sup_eq_top c (_root_.P2mJacAbs.finset_subset_affineOpen k c)
  exact ⟨⟨U, V, hU, hV, hsup, hUV⟩⟩

theorem exists_finiteMapData (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (m₀ : ℕ) :
    ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m := by
  haveI := geometricallyIntegral k c
  obtain ⟨𝒱⟩ := nonempty_twoAffineOpenCover k c
  obtain ⟨𝔉, h, -⟩ :=
    SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover k c ε 𝒱 m₀
  exact ⟨𝔉, h⟩

theorem exists_genus :
    ∃ g : ℕ, ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  haveI := geometricallyIntegral k c
  obtain ⟨𝒱⟩ := nonempty_twoAffineOpenCover k c
  exact SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover k c 𝒱

noncomputable def placeAt {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) : Place K L :=
  M.pointEquivPlace ⟨(sectionFibrePoint x s).1 ≫ e.inv, by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (sectionFibrePoint x s).2⟩

omit [SmoothOfRelativeDimension 1 c] [IsIntegral C] in
theorem placeAt_injective {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase) :
    Function.Injective (placeAt k c s M e he) := by
  intro x y hxy
  have h1 := M.pointEquivPlace.injective hxy
  have h2 : (sectionFibrePoint x s).1 ≫ e.inv = (sectionFibrePoint y s).1 ≫ e.inv := congrArg Subtype.val h1
  rw [cancel_mono] at h2
  exact sectionFibrePoint_injective k c s h2

theorem exists_hasChartSections :
    ∃ (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c),
      HasChartSections c γ := by
  classical
  obtain ⟨g, hg⟩ := exists_genus k c
  haveI := infinite_points k c

  set r : ℕ := 2 * g + 1 with hr
  let pool : Fin (r + 1) ↪ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c :=
    Fin.valEmbedding.trans (Infinite.natEmbedding _)

  let enum : Fin (Fintype.card (Fin (r - g) → Fin (r + 1))) ≃ (Fin (r - g) → Fin (r + 1)) :=
    (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Fin (r - g) → Fin (r + 1)), g, r, by omega,
    fun i j => pool (enum i j), ?_⟩
  intro K _ _ s
  obtain ⟨L, _, _, M, e, he, Kc, g', hRR'⟩ :=
    haveI := geometricallyIntegral k c
    SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed k c K s
  have hgg : g' = g := hg K s L M e he Kc g' hRR'
  subst hgg
  haveI : IsCurveOver K L :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase M.ffEquiv M.ffEquiv_algebraMap
  refine ⟨L, inferInstance, inferInstance, M, e, he, ⟨Kc, hRR'⟩, ?_⟩
  intro D hD hdeg

  let S : Finset (Place K L) := Finset.univ.image (fun a : Fin (r + 1) => placeAt k c s M e he (pool a))
  have hinj : Function.Injective (fun a : Fin (r + 1) => placeAt k c s M e he (pool a)) :=
    (placeAt_injective k c s M e he).comp pool.injective
  have hcard : r + 1 ≤ S.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, le_refl]
  have hS : ∀ v ∈ S, v.deg = 1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v
  obtain ⟨f, -, hfS, hell⟩ :=
    RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card hRR' (by omega) S hS hcard D hdeg
  have hf : ∀ j, ∃ a : Fin (r + 1), placeAt k c s M e he (pool a) = f j := fun j => by
    simpa [S] using hfS j
  choose a ha using hf
  refine ⟨enum.symm a, ?_⟩
  have hγ : ∀ j, pool (enum (enum.symm a) j) = pool (a j) := fun j => by rw [Equiv.apply_symm_apply]
  convert hell using 4 with j
  rw [← ha j, ← hγ j]
  rfl

theorem main (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∃ D : RelativePic0Designation k c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  haveI := geometricallyIntegral k c
  obtain ⟨n, g, r, hgr, γ, hγ⟩ := exists_hasChartSections k c
  exact exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced k c ε
    (exists_finiteMapData k c ε) n g r hgr γ hγ

end P2mJacAbs

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [IsIntegral C]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∃ D : RelativePic0Designation k c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase :=
  P2mJacAbs.main k c ε
