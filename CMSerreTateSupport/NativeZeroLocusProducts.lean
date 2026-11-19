/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Native zero ideals of composed and tensor-product sections

Local coefficients multiply under composition. The resulting equalities
preserve the complete ideal and its multiplicities, not merely its support.
Braiding identifies left and right tensoring without changing the zero ideal;
commutativity of ideal products gives the requested factor order.

For the original group and translated sections, the native tensor-square
formula uses the given square isomorphism and the original point operations.
It does not assert that isomorphism or any global finiteness statement.
-/
import NativeTranslatedPairSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeZeroLocusProducts

/-- Local scalar coefficients multiply under actual composition, so the
zero IDEAL is the product of zero ideals, not just the union of supports. -/
theorem zeroLocus_comp_eq_mul
    {X : Scheme.{u}} {L M N : X.Modules}
    [L.IsInvertible] [M.IsInvertible] [N.IsInvertible]
    (ψ : L ⟶ M) (φ : M ⟶ N) :
    (ψ ≫ φ).zeroLocus = ψ.zeroLocus * φ.zeroLocus := by
  have key (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      (ψ ≫ φ).zeroLocus.ideal V = (ψ.zeroLocus * φ.zeroLocus).ideal V := by
    obtain ⟨U, hxU, _, ⟨eM, hM⟩, eN, hN⟩ :=
      Scheme.Modules.exists_isFreeGenerator₂ M N (x := x) (W := ⊤) trivial
    obtain ⟨V, hxV, hVU, eL, hL⟩ := Scheme.Modules.exists_isFreeGenerator L hxU
    obtain ⟨b, hb⟩ := (hM.map hVU).exists_smul_eq (ψ.app V.1 eL)
    obtain ⟨c, hc⟩ := (hN.map hVU).exists_smul_eq
      (φ.app V.1 (M.presheaf.map (homOfLE hVU).op eM))
    have hcomp : (ψ ≫ φ).app V.1 eL =
        (b * c) • N.presheaf.map (homOfLE hVU).op eN := by
      change φ.app V.1 (ψ.app V.1 eL) = _
      rw [← hb, Scheme.Modules.Hom.app_smul, ← hc, mul_smul]
    refine ⟨V, hxV, ?_⟩
    change (ψ ≫ φ).zeroLocus.ideal V = ψ.zeroLocus.ideal V * φ.zeroLocus.ideal V
    rw [Scheme.Modules.Hom.ideal_zeroLocus (ψ ≫ φ) V hL (hN.map hVU) hcomp,
      Scheme.Modules.Hom.ideal_zeroLocus ψ V hL (hM.map hVU) hb.symm,
      Scheme.Modules.Hom.ideal_zeroLocus φ V (hM.map hVU) (hN.map hVU) hc.symm]
    exact (Ideal.span_singleton_mul_span_singleton b c).symm
  choose V hxV hV using key
  exact Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

/-- Left tensoring with an actual native invertible line preserves the
zero ideal, using the native braiding as an arrow isomorphism. -/
theorem zeroLocus_whiskerLeft
    {X : Scheme.{u}} {M N : X.Modules} [M.IsInvertible] [N.IsInvertible]
    (P : X.Modules) [P.IsInvertible] (φ : M ⟶ N) :
    (P ◁ φ).zeroLocus = φ.zeroLocus := by
  let e : Arrow.mk (P ◁ φ) ≅ Arrow.mk (φ ▷ P) :=
    Arrow.isoMk (β_ P M) (β_ P N) (BraidedCategory.braiding_naturality_right P φ).symm
  exact (Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _ e).trans
    (Scheme.Modules.Hom.zeroLocus_whiskerRight φ P)

/-- Tensor coefficients multiply: the complete native zero ideal of a
tensor morphism is the product of the two native zero ideals. -/
theorem zeroLocus_tensorHom_eq_mul
    {X : Scheme.{u}} {L M N P : X.Modules}
    [L.IsInvertible] [M.IsInvertible] [N.IsInvertible] [P.IsInvertible]
    (φ : L ⟶ M) (ψ : N ⟶ P) :
    (φ ⊗ₘ ψ).zeroLocus = φ.zeroLocus * ψ.zeroLocus := by
  rw [tensorHom_def', zeroLocus_comp_eq_mul,
    Scheme.Modules.Hom.zeroLocus_whiskerRight, zeroLocus_whiskerLeft]
  exact _root_.mul_comm _ _

/-- The ACTUAL theta_x tensor theta_-x section of native N.tensorPow2 has
exactly D.comap(t_x) times D.comap(t_-x) as its zero IDEAL. No basepoint-free
or square producer is assumed complete by this local formula. -/
theorem pairedSection_zeroLocus
    {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N)
    (D : A.X.left.IdealSheafData) (hZero : D = θ.zeroLocus)
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)
    (eSquare :
      (Scheme.Modules.pullback
          (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A (x * x⁻¹))).obj N ⊗ N ≅
        (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).obj N ⊗
          (Scheme.Modules.pullback (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹)).obj N) :
    (H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairedSectionFromActualSquare
        A N θ x eSquare).zeroLocus =
      D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) *
        D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹) := by
  let tx := H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x
  let ty := H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹
  let φ := H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom tx N θ
  let ψ := H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom ty N θ
  let ep := H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairIsoNativePowerTwo A N x eSquare
  let e : Arrow.mk (φ ⊗ₘ ψ) ≅ Arrow.mk
      (H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairedSectionFromActualSquare A N θ x eSquare) :=
    Arrow.isoMk (λ_ (Scheme.Modules.unit A.X.left)) ep (by
      simp [H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairedSectionFromActualSquare,
        φ, ψ, ep, tx, ty])
  rw [← Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _ e, zeroLocus_tensorHom_eq_mul]
  dsimp only [φ, ψ]
  rw [H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom_zeroLocus,
    H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom_zeroLocus, ← hZero]

end H5OriginalDVR.Lane2.NativeZeroLocusProducts
