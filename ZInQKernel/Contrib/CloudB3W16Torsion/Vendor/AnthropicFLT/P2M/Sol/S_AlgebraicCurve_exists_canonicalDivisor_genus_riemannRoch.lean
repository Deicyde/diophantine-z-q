/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch

universe u v

open IntermediateField Polynomial

namespace S18RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_and_isSeparable_of_ratFuncAlgHom (t : F)
    (hfd : FiniteDimensional K⟮t⟯ F) (hsep : Algebra.IsSeparable K⟮t⟯ F)
    (φ : RatFunc K →ₐ[K] F) (hφ : φ RatFunc.X = t) :
    letI := φ.toRingHom.toAlgebra
    Module.Finite (RatFunc K) F ∧ Algebra.IsSeparable (RatFunc K) F := by
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let E : IntermediateField K F := φ.fieldRange
  have htE : t ∈ E := ⟨RatFunc.X, hφ⟩
  have hle : K⟮t⟯ ≤ E := adjoin_simple_le_iff.mpr htE
  letI : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower K⟮t⟯ E F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite K⟮t⟯ E F
  haveI : Algebra.IsSeparable E F := Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ E F
  let e : RatFunc K ≃ₐ[K] E := AlgEquiv.ofInjectiveField φ
  have key : ∀ x : E, φ (e.symm x) = (x : F) := fun x => by
    have h2 : ((e (e.symm x) : E) : F) = φ (e.symm x) := AlgEquiv.ofInjective_apply _ _ _
    rw [e.apply_symm_apply] at h2
    exact h2.symm
  have he : (algebraMap (RatFunc K) F).comp (e.symm.toRingEquiv : E ≃+* RatFunc K).toRingHom
      = (RingEquiv.refl F).toRingHom.comp (algebraMap E F) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact key x
  refine ⟨?_, ?_⟩
  · exact Module.Finite.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K) (RingEquiv.refl F) he
  · exact Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K) (RingEquiv.refl F) he

theorem essFiniteType_ratFunc (K : Type*) [Field K] : Algebra.EssFiniteType K (RatFunc K) := by
  haveI : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  exact Algebra.EssFiniteType.comp K K[X] (RatFunc K)

end S18RR

open AlgebraicCurve

theorem solution (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ (Kc : Divisor K F) (g : ℕ), ∀ D : Divisor K F,
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical
  obtain ⟨t, htr, hfd, hsep⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have ht : t ∉ Set.range (algebraMap K F) := by
    rintro ⟨k, rfl⟩
    exact htr (isAlgebraic_algebraMap k)
  obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq (K := K) (F := F) ht
  letI : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq (fun k => (φ.commutes k).symm)
  obtain ⟨hfin, hsepR⟩ := S18RR.finite_and_isSeparable_of_ratFuncAlgHom t hfd hsep φ hφ
  haveI : Module.Finite (RatFunc K) F := hfin
  haveI : Algebra.IsSeparable (RatFunc K) F := hsepR
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  haveI : AlgebraicCurve.IsCurveOver K (RatFunc K) := AlgebraicCurve.instIsCurveOverRatFunc K
  haveI : Algebra.EssFiniteType K (RatFunc K) := S18RR.essFiniteType_ratFunc K
  haveI : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  haveI : ∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
  obtain ⟨ω, hω⟩ := exists_ne (0 : KaehlerDifferential K F)
  exact ⟨AlgebraicCurve.canonicalDivisorOf hω, AlgebraicCurve.genus K F, fun D => hRR hω D⟩
