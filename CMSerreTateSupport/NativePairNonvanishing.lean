/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Native tensor-square sections avoiding geometric points

The given square isomorphism and the same nonzero section produce translated
pair sections on the original abelian variety. The zero-ideal product formula,
actual translation and inversion isomorphisms, and density of closed points
show that the full native section family has no common zero.

Compactness extracts a nonempty finite family of actual global sections.
This is a section-generation statement, not a projective-map finiteness or
descent assertion. Original fields, points, modules, powers and universes
are retained throughout.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
import NativeZeroLocusProducts
import NativeTranslationAction
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativePairNonvanishing

/-- Actual square-output plus the SAME nonzero theta yields an actual native
power2 section nonvanishing at each geometric terminal-object point. -/
theorem exists_native_square_section_avoiding_point
    (hSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0)
    (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    ∃ s : Scheme.Modules.unit A.X.left ⟶ Scheme.Modules.tensorPow N 2,
      H5OriginalDVR.Lane2.NativeTranslationAction.point A a ∉ s.zeroLocus.support := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom
  haveI : IsCommMonObj A.X :=
    isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  let D := θ.zeroLocus
  have hD : D ≠ ⊥ := H5OriginalDVR.Lane2.NativeDivisorKernel.zero_divisor_ne_bot_of_section_ne_zero
    N θ hθ D rfl
  have hS : (D.support : Set A.X.left) ≠ Set.univ := by
    intro h
    have ht : D.support = ⊤ := SetLike.coe_injective h
    exact hD (Scheme.IdealSheafData.support_eq_top_iff.mp ht)
  let U : A.X.left.Opens := ⟨(D.support : Set A.X.left)ᶜ, D.support.isClosed.isOpen_compl⟩
  have hU : (U : Set A.X.left).Nonempty := Set.nonempty_compl.mpr hS
  let e1 := H5OriginalDVR.Lane2.NativeTranslationAction.rightTranslationIso A a
  let e2 := H5OriginalDVR.Lane2.NativeTranslationAction.inversionIso A ≪≫ e1
  have hpre (e : A.X.left ≅ A.X.left) : (e.hom ⁻¹ᵁ U : Set A.X.left).Nonempty := by
    obtain ⟨z, hz⟩ := hU
    refine ⟨e.inv z, ?_⟩
    change e.hom (e.inv z) ∈ U
    have he : e.hom (e.inv z) = z := by
      calc
        e.hom (e.inv z) = (e.inv ≫ e.hom) z :=
          (_root_.AlgebraicGeometry.Scheme.Hom.comp_apply e.inv e.hom z).symm
        _ = (𝟙 A.X.left) z :=
          congrArg (fun f : A.X.left ⟶ A.X.left => f z) e.inv_hom_id
        _ = z := rfl
    rw [he]
    exact hz
  let W := (e1.hom ⁻¹ᵁ U) ⊓ (e2.hom ⁻¹ᵁ U)
  have hW : (W : Set A.X.left).Nonempty :=
    nonempty_preirreducible_inter (e1.hom ⁻¹ᵁ U).isOpen (e2.hom ⁻¹ᵁ U).isOpen
      (hpre e1) (hpre e2)
  obtain ⟨z, hzW, hzc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  obtain ⟨⟨x0, hx0⟩, hxz⟩ := (pointEquivClosedPoint A.X.hom).surjective ⟨z, hzc⟩
  let x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X := Over.homMk x0 hx0
  have hxp : H5OriginalDVR.Lane2.NativeTranslationAction.point A x = z :=
    congrArg Subtype.val hxz
  have hxW : H5OriginalDVR.Lane2.NativeTranslationAction.point A x ∈ W := by
    rw [hxp]
    exact hzW
  have ha1 : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x
      (H5OriginalDVR.Lane2.NativeTranslationAction.point A a) ∉ D.support := by
    have h := hxW.1
    change H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A a
      (H5OriginalDVR.Lane2.NativeTranslationAction.point A x) ∉ D.support at h
    rw [H5OriginalDVR.Lane2.NativeTranslationAction.rightTranslation_apply_point] at h ⊢
    simpa only [mul_comm] using h
  have ha2 : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹
      (H5OriginalDVR.Lane2.NativeTranslationAction.point A a) ∉ D.support := by
    have h := hxW.2
    change H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A a
      (ι[A.X].left (H5OriginalDVR.Lane2.NativeTranslationAction.point A x)) ∉ D.support at h
    rw [H5OriginalDVR.Lane2.NativeTranslationAction.inversion_apply_point,
      H5OriginalDVR.Lane2.NativeTranslationAction.rightTranslation_apply_point] at h
    rw [H5OriginalDVR.Lane2.NativeTranslationAction.rightTranslation_apply_point]
    simpa only [mul_comm] using h
  obtain ⟨eSquare⟩ := hSquare A N x x⁻¹
  let s := H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairedSectionFromActualSquare
    A N θ x eSquare
  refine ⟨s, ?_⟩
  dsimp only [s]
  rw [H5OriginalDVR.Lane2.NativeZeroLocusProducts.pairedSection_zeroLocus A N θ D rfl x eSquare,
    Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_comap]
  change ¬ (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x
      (H5OriginalDVR.Lane2.NativeTranslationAction.point A a) ∈ D.support ∨
    H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹
      (H5OriginalDVR.Lane2.NativeTranslationAction.point A a) ∈ D.support)
  exact not_or_intro ha1 ha2

/-- ALL actual global native power2 section maps have no common zero.
The common zero set is closed; a nonempty one would contain a closed point,
and its actual field-valued point is contradicted by the paired section above.
This is still conditional on the genuine earlier I5a proof, NOT finiteness or
an induced projective presentation. -/
theorem native_square_sections_no_common_zero
    (hSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0) :
    (⋂ s : Scheme.Modules.unit A.X.left ⟶ Scheme.Modules.tensorPow N 2,
      (s.zeroLocus.support : Set A.X.left)) = ∅ := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  let S := ⋂ s : Scheme.Modules.unit A.X.left ⟶ Scheme.Modules.tensorPow N 2,
    (s.zeroLocus.support : Set A.X.left)
  have hS : IsClosed S := isClosed_iInter fun s => s.zeroLocus.support.isClosed
  change S = ∅
  by_contra hne
  have hn : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨z, hzS, hzc⟩ := nonempty_inter_closedPoints hn hS.isLocallyClosed
  let a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X :=
    Over.homMk (pointOfClosedPoint A.X.hom z hzc) (pointOfClosedPoint_comp A.X.hom z hzc)
  have ha : H5OriginalDVR.Lane2.NativeTranslationAction.point A a = z :=
    pointOfClosedPoint_apply A.X.hom z hzc (IsLocalRing.closedPoint K)
  obtain ⟨s, hs⟩ := exists_native_square_section_avoiding_point hSquare A N θ hθ a
  apply hs
  rw [ha]
  exact Set.mem_iInter.mp hzS s

/-- Compactness extracts a NONEMPTY finite family of ACTUAL global
native square sections without a common zero. This does not provide a
projective map, its frame/ratio equations, or finiteness/descent. -/
theorem finite_native_square_sections_no_common_zero
    (hSquare : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0) :
    ∃ F : Finset Γ(Scheme.Modules.tensorPow N 2, ⊤), F.Nonempty ∧
      ∀ z : A.X.left, ∃ s ∈ F,
        z ∉ (Scheme.Modules.homOfGlobalSection (Scheme.Modules.tensorPow N 2) s).zeroLocus.support := by
  classical
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  let M := Scheme.Modules.tensorPow N 2
  let I := Scheme.Modules.unit A.X.left ⟶ M
  let U : I → Set A.X.left := fun s => (s.zeroLocus.support : Set A.X.left)ᶜ
  have hzero := native_square_sections_no_common_zero hSquare A N θ hθ
  have hpoint (z : A.X.left) : ∃ s : I, z ∉ s.zeroLocus.support := by
    by_contra hn
    have hzAll : z ∈ ⋂ s : I, (s.zeroLocus.support : Set A.X.left) := by
      apply Set.mem_iInter.mpr
      intro s
      by_contra hs
      exact hn ⟨s, hs⟩
    have hzEmpty : z ∈ (∅ : Set A.X.left) := hzero ▸ hzAll
    exact (Set.notMem_empty z) hzEmpty
  have hcover : (Set.univ : Set A.X.left) ⊆ ⋃ s : I, U s := by
    intro z _
    obtain ⟨s, hs⟩ := hpoint z
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U
    (fun s => s.zeroLocus.support.isClosed.isOpen_compl) hcover
  have hSpoint (z : A.X.left) : ∃ s ∈ S, z ∉ s.zeroLocus.support := by
    obtain ⟨s, hs, hz⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ z))
    exact ⟨s, hs, hz⟩
  let value : I → Γ(M, ⊤) := fun s => s.app ⊤ (1 : Γ(A.X.left, ⊤))
  let F := S.image value
  have hF : F.Nonempty := by
    obtain ⟨s, hs, _⟩ := hSpoint (η[A.X].left (IsLocalRing.closedPoint K))
    exact ⟨value s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  refine ⟨F, hF, ?_⟩
  intro z
  obtain ⟨s, hs, hz⟩ := hSpoint z
  refine ⟨value s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
  have he : Scheme.Modules.homOfGlobalSection M (value s) = s := by
    simpa only [Scheme.Modules.unitHomAddEquiv_symm_apply,
      Scheme.Modules.unitHomAddEquiv_apply, value] using
      (Scheme.Modules.unitHomAddEquiv M).symm_apply_apply s
  rw [he]
  exact hz

end H5OriginalDVR.Lane2.NativePairNonvanishing
