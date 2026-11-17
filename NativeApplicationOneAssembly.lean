/-
H5 Step2 / native Application1 and SAME positive-power I2 assembly.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. Native remains HELD.

The two inputs are EXACT named pending C3 producer theorems from frozen
Step2DelegatedInterfaces4d5c8dce: FiniteSquarePresentation and
NativeFBSFieldDescent. They are not Facts or axioms; C6's exact truth/Source
review and their actual proof terms remain required. No original NOS theorem
is claimed proved by a conditional assembly or by an uncompiled native cone.

Lane2's actual all-field square Source a448/cube56c/geof1 is used instead of
an extra square/cube premise. The genuine native theta/N/D and original
right translation are retained. G5 builds the actual projective presentation
from actual native paired sections/frames; C3 proves THAT map finite. Native
left-recursive tensorPow2 is retained through the SAME algebraic closure and
field descent, so the output exponent is literally b=2 over original k.

The new elementary adapter below proves that the ACTUAL unit-source pullback
of theta is nonzero under a SURJECTIVE scheme map from its true zero-IDEAL
support. This does not assume a faithful PB functor, compare ranks or exchange
nonflat homology. Reducedness is required ONLY of the original X and is
proved from original AV geometric integrality in the application.

I0's affine-complement divisor/coset proof and the C5 native algebra/purity
core remain separate; this file does not replace descent M/beta by auxiliary N.
No Stacks imports/bridges/further intake, CharZero/perfectness/dimension cap,
Source/native power or invertibility alias, budget/runtime/root/protected edit.
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
  let p := pullback.fst A.X.hom g
  let Nbar : Abar.X.left.Modules := (Scheme.Modules.pullback p).obj N
  let θbar := H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom p N θ
  let Dbar := D.comap p
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
    letI : Dbar.toModules.IsInvertible := hDbar.isInvertible_toModules
    have hCartier : θbar.zeroLocus.IsInvertible := hZbar ▸ hDbar
    obtain ⟨e⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj θbar hCartier
    have he : Nonempty (Nbar ≅ Dbar.toModulesᵛ ⊗ Scheme.Modules.unit Abar.X.left) := by
      simpa only [← hZbar] using (show Nonempty (_ ≅ _) from ⟨e⟩)
    obtain ⟨e'⟩ := he
    exact ⟨e' ≪≫ ρ_ Dbar.toModulesᵛ⟩
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
