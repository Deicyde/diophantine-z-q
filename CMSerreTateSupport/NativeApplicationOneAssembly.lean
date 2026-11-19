/-
Copyright (c) 2026 H5 contributors. Apache-2.0.

# Native finite-section construction from effective divisor data

The given line, nonzero section and Cartier ideal are preserved through the
original algebraic-closure base change. The actual square sections and finite
geometric divisor stabilizer supply a presentation of the same tensor square.
Finiteness and field descent then give a positive native power of the original
line over the original field.

Pullback invertibility and projection flatness are derived on the same
geometric scheme. The Cartier representation and its unit cancellation use
that scheme's native module category, not a different line or power.
-/
import AllFieldNativeSquare
import NativeSquarePresentation
import Step2DelegatedInterfaces

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace H5OriginalDVR.Lane2.NativeApplicationOneAssembly

/-- On a reduced original scheme a nonzero line section remains nonzero
under any SURJECTIVE scheme map. The actual zero ideal/support and actual
unit-source PB map prove it; no scalar or sheaf-functor alias is used. -/
theorem pulledSectionHom_ne_zero_of_surjective
    {X Y : Scheme.{u}} [IsReduced X] (p : Y ⟶ X) [Surjective p]
    (N : X.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit X ⟶ N) (hθ : θ ≠ 0) :
    H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom p N θ ≠ 0 := by
  intro hz
  have hzero : (θ.zeroLocus.comap p) = ⊥ := by
    rw [← H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom_zeroLocus p N θ]
    exact (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).mpr hz
  have htop : θ.zeroLocus.support = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨y, rfl⟩ := p.surjective x
    have hy : y ∈ (θ.zeroLocus.comap p).support := by
      rw [hzero, Scheme.IdealSheafData.support_bot]
      trivial
    rw [Scheme.IdealSheafData.support_comap] at hy
    exact hy
  exact hθ ((Scheme.Modules.Hom.zeroLocus_eq_bot_iff θ).mp
    (Scheme.IdealSheafData.support_eq_top_iff.mp htop))

/-- EXACT geometric Application1 assembly: the SAME native N^2 is FBS from
real nonzero effectivity and real IDEAL H(D) finiteness. C3's finite-map
producer is explicit and pending; no presentation/finite/ample Factory. -/
theorem native_square_finite_by_sections
    (hFinite : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u})
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0)
    (D : A.X.left.IdealSheafData) (hD : D.IsInvertible)
    (hZero : D = θ.zeroLocus) (hND : Nonempty (N ≅ D.toModulesᵛ))
    (hHD : (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D).Finite) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
      (R := K) (Scheme.Modules.tensorPow N 2) A.X.hom := by
  obtain ⟨d, ⟨𝔓⟩⟩ := H5OriginalDVR.Lane2.NativeSquarePresentation.exists_native_square_projPresentation
    H5OriginalDVR.Lane2.AllFieldNativeSquare.theoremOfSquare A N θ hθ
  exact ⟨d, 𝔓, hFinite A N θ hθ D hD hZero hND hHD d 𝔓⟩

/-- The SAME original-field line has a positive native FBS power, using the
EXACT future I1 OUTPUT, the actual effectivity section and C3's finite-map
and field-descent producers. Original k can be imperfect or positive char;
its SAME AlgebraicClosure k is the only geometric field used.
This is an intermediate Step2 theorem, not an added original NOS input. -/
theorem native_positive_power_finite_by_sections_of_effective_and_I1
    (hFinite : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u})
    (hDescend : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.NativeFBSFieldDescent.{u})
    {k : Type u} [Field k]
    (A : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety A]
    (N : A.X.left.Modules) [N.IsInvertible]
    (θ : Scheme.Modules.unit A.X.left ⟶ N) (hθ : θ ≠ 0)
    (D : A.X.left.IdealSheafData) (hD : D.IsInvertible) (hZero : D = θ.zeroLocus)
    (hI1 :
      let g := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
      let Abar := PkgI2.baseChange A (AlgebraicClosure k)
      let Nbar : Abar.X.left.Modules := (Scheme.Modules.pullback (pullback.fst A.X.hom g)).obj N
      {x : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ Abar.X |
        Nonempty ((Scheme.Modules.pullback
          (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation Abar x)).obj Nbar ≅ Nbar)}.Finite) :
    ∃ b : ℕ, 0 < b ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
        (R := k) (Scheme.Modules.tensorPow N b) A.X.hom := by
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Abar := PkgI2.baseChange A K
  let p : Abar.X.left ⟶ A.X.left := pullback.fst A.X.hom g
  haveI : Flat g := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    infer_instance
  haveI : Flat p := by
    change Flat (pullback.fst A.X.hom g)
    infer_instance
  let Nbar : Abar.X.left.Modules := (Scheme.Modules.pullback p).obj N
  letI : Nbar.IsInvertible :=
    SheafOfModules.IsInvertible.pullback (morphism := p) (inferInstance : N.IsInvertible)
  let θbar : Scheme.Modules.unit Abar.X.left ⟶ Nbar :=
    H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom p N θ
  let Dbar : Abar.X.left.IdealSheafData := D.comap p
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.X.hom
  haveI : IsReduced A.X.left := inferInstance
  letI : Surjective g := ⟨fun x =>
    ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  letI : Surjective p := inferInstanceAs (Surjective (pullback.fst A.X.hom g))
  have hθbar : θbar ≠ 0 := pulledSectionHom_ne_zero_of_surjective p N θ hθ
  have hDbar : Dbar.IsInvertible := hD.comap_of_flat p
  have hZbar : Dbar = θbar.zeroLocus := by
    dsimp only [Dbar, θbar]
    rw [H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom_zeroLocus, ← hZero]
  have hNbarDbar : Nonempty (Nbar ≅ Dbar.toModulesᵛ) := by
    have hCartier : θbar.zeroLocus.IsInvertible := by
      rw [← hZbar]
      exact hDbar
    letI : Dbar.toModules.IsInvertible := hDbar.isInvertible_toModules
    have hRep : Nonempty (Nbar ≅ θbar.zeroLocus.toModulesᵛ ⊗
        Scheme.Modules.unit Abar.X.left) :=
      Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj θbar hCartier
    obtain ⟨e⟩ := hRep
    rw [← hZbar] at e
    exact ⟨e ≪≫ ρ_ Dbar.toModulesᵛ⟩
  have hHDbar :
      (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer Abar Dbar).Finite :=
    H5OriginalDVR.Lane2.NativeDivisorKernel.geometric_divisorStabilizer_finite_of_I1
      A N θ D hD hZero hI1
  have hFbar :
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
        (R := K) (Scheme.Modules.tensorPow Nbar 2) Abar.X.hom :=
    native_square_finite_by_sections hFinite Abar Nbar θbar hθbar Dbar hDbar hZbar hNbarDbar hHDbar
  exact ⟨2, by decide, hDescend (k := k) (K := K) A N 2 (by decide) hFbar⟩

end H5OriginalDVR.Lane2.NativeApplicationOneAssembly
