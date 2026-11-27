import Mathlib.RingTheory.Unramified.Basic
import ZInQKernel.Contrib.OneProof.HeightDictionary.Conormal

/-! # `θ` is an isomorphism

The tree's comparison map `θ : 𝔪_ξ/𝔪_ξ² → 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`, `df ↦ 1 ⊗ df`
(`ZInQ.HeightDict.Conormal.theta`) is injective (`Conormal.theta_injective`). It is also
surjective (`theta_surjective`): `θ` is Mathlib's `kerCotangentToTensor` after the identification
`ker(𝒪_{𝒢,ξ} → 𝒪_{S,η}) = 𝔪_ξ`, and the conormal sequence
`I/I² → 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L] → Ω[𝒪_{S,η}/𝓞_L]` is exact
(`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`) with `Ω[𝒪_{S,η}/𝓞_L] = 0`
(`𝒪_{S,η}` is a localization of `𝓞_L`). `thetaEquiv` is the isomorphism. -/
open CategoryTheory AlgebraicGeometry
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM3

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-- `Ω[𝒪_{S,η}/𝓞_L] = 0`: `𝒪_{S,η}` is a localization of `𝓞_L`. -/
theorem subsingleton_kaehler_Reta : Subsingleton Ω[Reta L⁄𝓞 L] := by
  haveI := isLocalization_Reta (L := L)
  haveI := Algebra.FormallyUnramified.of_isLocalization (Rₘ := Reta L)
    (⊥ : Ideal (𝓞 L)).primeCompl
  infer_instance

theorem kerCotangentToTensor_surjective :
    Function.Surjective (kerCotangentToTensor (𝓞 L) 𝒢.genStalk (Reta L)) := by
  have hex := exact_kerCotangentToTensor_mapBaseChange (𝓞 L) 𝒢.genStalk (Reta L)
    (algebraMap_surjective 𝒢)
  haveI := subsingleton_kaehler_Reta (L := L)
  intro y
  exact (hex y).mp (Subsingleton.elim _ _)

theorem mapCotangent_surjective : Function.Surjective (Ideal.mapCotangent
    (IsLocalRing.maximalIdeal 𝒢.genStalk) (RingHom.ker (algebraMap 𝒢.genStalk (Reta L)))
    (AlgHom.id 𝒢.genStalk 𝒢.genStalk) (maximalIdeal_le_ker 𝒢)) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  have hx' : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [← ker_eq_maximalIdeal 𝒢]; exact hx
  exact ⟨(IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent ⟨x, hx'⟩,
    Ideal.mapCotangent_toCotangent _ _ _ _ _⟩

/-- **`θ` is surjective** (the conormal sequence, with `Ω[𝒪_{S,η}/𝓞_L] = 0`). -/
theorem theta_surjective : Function.Surjective (ZInQ.HeightDict.Conormal.theta 𝒢) :=
  (kerCotangentToTensor_surjective 𝒢).comp (mapCotangent_surjective 𝒢)

theorem theta_bijective : Function.Bijective (ZInQ.HeightDict.Conormal.theta 𝒢) :=
  ⟨ZInQ.HeightDict.Conormal.theta_injective 𝒢, theta_surjective 𝒢⟩

/-- **`θ : 𝔪_ξ/𝔪_ξ² ≃ 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`.** -/
noncomputable def thetaEquiv :
    𝒢.cotangent ≃ₗ[𝒢.genStalk] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] :=
  LinearEquiv.ofBijective (ZInQ.HeightDict.Conormal.theta 𝒢) (theta_bijective 𝒢)

end ZInQ.HeightModelM3
