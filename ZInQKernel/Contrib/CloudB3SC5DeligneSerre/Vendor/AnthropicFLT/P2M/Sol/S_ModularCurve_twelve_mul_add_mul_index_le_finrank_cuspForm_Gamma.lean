/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma (git blob 0038349c35b68797a233250f1f305813695b8b38, sha256 ca4f39e051a71a6e95a43bfd5344525cb73783ef38c1419413c499f14d54f21b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WLight_levelN_structure_package
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups IntermediateField

namespace ModularCurve
export _root_.ModularCurve (LevelN.ring LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin LevelN.twelve_mul_add_mul_index_le_genusFF LevelN.exists_linearMap_regularDifferentials_cuspForm_injective)
namespace GenusBoundAssembly
open _root_.ModularCurve

open AlgebraicCurve ModularCurve.LevelN

section Bridge

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

theorem curve_package {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (_ : ∀ w : Place K F, w.DCoordGenerates),
      Module.Finite K ↥(regularDifferentials K F) ∧
        genusFF K F = Module.finrank K ↥(regularDifferentials K F) := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField htr hfd
  haveI := htfd
  haveI := htsep
  haveI hC1 : IsCurveOver K F := isCurveOver_of_transcendental ht htfd htsep
  haveI hC2 : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional ht htfd
  haveI : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hC3 : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F := ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch K F := by
    unfold FunctionFieldRiemannRoch
    intro _ _ _ ω hω D
    exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed K F
  have hSG : StichtenothGenusExists K F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic K F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hg : genus K F = genusFF K F := genus_eq_genusFF hRR hWDA hC
  obtain ⟨hfin, hdim⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
  exact ⟨hC1, hC2, hC3, hfin, by rw [hdim, hg]⟩

end Bridge

theorem isDomain_ring (N : ℕ) [NeZero N] : IsDomain (ring N) := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  have hdom : ∀ a b : UpperHalfPlane → ℂ, a ∈ ring N → b ∈ ring N → a * b = 0 → a = 0 ∨ b = 0 :=
    h.2.2.2.2.2
  haveI : NoZeroDivisors (ring N) :=
    ⟨fun {a b} hab => by
      have h' := hdom (a : UpperHalfPlane → ℂ) b a.2 b.2 (by
        have := congrArg (Subtype.val) hab
        simpa using this)
      rcases h' with h' | h'
      · left; exact Subtype.ext h'
      · right; exact Subtype.ext h'⟩
  haveI : Nontrivial (ring N) := ⟨⟨0, 1, by
    intro h01
    have := congrArg (fun F : ring N => (F : UpperHalfPlane → ℂ) UpperHalfPlane.I) h01
    simp at this⟩⟩
  exact NoZeroDivisors.to_isDomain _

theorem main (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsDomain (ring N) := isDomain_ring N

  let K := FractionRing (ring N)

  obtain ⟨_, _, _, _, _, htr, hfd, _, _⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin N K

  have hgen := ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF N hN K

  obtain ⟨Φ, hΦ⟩ :=
    ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective N K

  obtain ⟨_, _, _, hfin, hg⟩ := curve_package (K := ℂ) (F := K) htr hfd
  haveI := hfin
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  have hle : Module.finrank ℂ ↥(regularDifferentials ℂ K) ≤
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  calc 12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index
      ≤ 12 * N * genusFF ℂ K +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := hgen
    _ = 12 * N * Module.finrank ℂ ↥(regularDifferentials ℂ K) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by rw [hg]
    _ ≤ 12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
          6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
        gcongr

end ModularCurve.GenusBoundAssembly

theorem solution (N : ℕ) (hN : 2 ≤ N) :
    12 * N + N * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index :=
  ModularCurve.GenusBoundAssembly.main N hN
