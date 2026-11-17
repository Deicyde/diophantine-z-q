/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section: FBSUnitFinite v2 (C3 interface v2, lead OK 2026-11-17). SOURCE ONLY, UNCOMPILED.
Native HELD. The frozen batch-2 `PresentationBasics.fbsUnitFinite` (AbelianVariety binder) is kept
unchanged as history.

`fbsUnitFinite_of_appTop_bijective`: for ANY group object `Y` over a field with `Y.X.hom` proper and
`Γ(Spec K) → Γ(Y, 𝒪)` bijective, `𝒪_Y` finite-by-sections forces `Y.X.hom` finite. The proof is the
batch-2 proof verbatim with its two uses of `IsAbelianVariety` (properness, and C3's
`appTop_bijective_of_isAbelianVariety`) replaced by these explicit inputs, so C3 instantiates it with
`[Step1.IsProperIntegralGroup Y]` + C3's `appTop_bijective_of_isProperIntegralGroup` (or with the
abelian-variety lemma). No smoothness, no new Fact.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

local notation "FBS'" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- **FBSUnitFinite v2 (general form).** -/
theorem fbsUnitFinite_of_appTop_bijective {K : Type u} [Field K]
    (Y : Grp (Over (Spec (CommRingCat.of K)))) [IsProper Y.X.hom]
    (hΓ : Function.Bijective Y.X.hom.appTop)
    (hFBS : FBS' (𝟙_ Y.X.left.Modules) Y.X.hom) : IsFinite Y.X.hom := by
  obtain ⟨N, 𝔓, hfin⟩ := hFBS
  -- a point of `Y` (the unit section)
  let x : Y.X.left := (η[Y.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X).left.base
    (default : Spec (CommRingCat.of K))
  obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X K N (𝔓.toProj x)
  let Di := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
  -- `σ i ≠ 0`
  have hne := ne_zero_of_frame (𝟙_ Y.X.left.Modules) (𝔓.σ i) (U := 𝔓.toProj ⁻¹ᵁ Di) hi
    (𝔓.frame i _ le_rfl)
  -- `σ i` is a constant, hence a unit of `Γ(Y, ⊤)` (C3 (i): `Γ(Spec K) → Γ(Y)` bijective)
  obtain ⟨c, hc⟩ := hΓ.2
    (show Γ(Y.X.left, ⊤) from 𝔓.σ i)
  have hc0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom c ≠ 0 := by
    intro h0
    apply hne
    have hc' : c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv h0
      simpa using this
    change (show Γ(Y.X.left, ⊤) from 𝔓.σ i) = 0
    rw [← hc, hc', map_zero]
  have hcu : IsUnit c := by
    have hk : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom c) := hc0.isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have hσu : IsUnit (show Γ(Y.X.left, ⊤) from 𝔓.σ i) := by
    rw [← hc]
    exact hcu.map Y.X.hom.appTop.hom
  -- hence `σ i` generates everywhere, so `toProj` lands in the affine chart `D₊(Xᵢ)`
  have hall : ∀ y : Y.X.left, y ∈ 𝔓.toProj ⁻¹ᵁ Di := by
    intro y
    refine (PresChart.mem_preimage_basicOpen_iff 𝔓 i y).2 ⟨⊤, trivial, fun V _ => ?_⟩
    have hu : IsUnit (Y.X.left.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (show Γ(Y.X.left, ⊤) from 𝔓.σ i)) := hσu.map _
    change Function.Bijective fun g : Γ(Y.X.left, V) =>
      g * Y.X.left.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (show Γ(Y.X.left, ⊤) from 𝔓.σ i)
    refine ⟨fun a b hab => hu.mul_right_cancel hab, fun z => ⟨z * ↑hu.unit⁻¹, ?_⟩⟩
    show z * ↑hu.unit⁻¹ * _ = z
    rw [mul_assoc, hu.val_inv_mul, mul_one]
  have htop : 𝔓.toProj ⁻¹ᵁ Di = ⊤ := eq_top_iff.2 fun y _ => hall y
  haveI : IsAffineHom 𝔓.toProj := inferInstance
  have haff : IsAffineOpen (𝔓.toProj ⁻¹ᵁ Di) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.X_mem_one K N i)
      Nat.one_pos).preimage 𝔓.toProj
  rw [htop] at haff
  haveI : IsAffine (⊤ : Y.X.left.Opens).toScheme := haff
  haveI : IsAffine Y.X.left := IsAffine.of_isIso (Y.X.left.topIso.inv)
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩


end ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
