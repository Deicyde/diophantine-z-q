/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm (git blob 26d731c3145c68f9cec29d65a01bc9f1779d231c, sha256 6ed7e27d95a2d9bb8b2d9897872ef54960a918d3bed96ee68a9d937be85ae314).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_essFiniteType_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_diffQExp_x1FunctionFieldBar_injective
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_finiteDimensional_Gamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.X1RegDiff
end P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.X1RegDiff

namespace P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm

set_option autoImplicit false

open scoped TensorProduct
open _root_.ModularCurve hiding IsCusp

noncomputable section

namespace X1RegDiff

open ModularForm ModularFormClass Complex
open UpperHalfPlane hiding I




section Children

theorem childA (M : ℕ) [NeZero M] (ι₀ : (AlgebraicClosure ℚ) →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 ⇑f).coeff n ∈ ι₀.range) :
    ∃ ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)],
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) :=
  ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion M ι₀ f hf

theorem childB (M : ℕ) [NeZero M] (ι₀ : (AlgebraicClosure ℚ) →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])
    (hω : coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f)) :
    ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) :=
  ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion M ι₀ f ω hω

theorem childC (M : ℕ) [NeZero M] (ι₀ : (AlgebraicClosure ℚ) →+* ℂ) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])
    (hω : ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) :=
  ModularCurve.exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials M ι₀ ω hω

theorem childE (M : ℕ) [NeZero M] :
    Module.Finite (AlgebraicClosure ℚ) ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) := by
  haveI := ModularCurve.isCurveOver_x1FunctionFieldBar M
  haveI := ModularCurve.essFiniteType_x1FunctionFieldBar M
  haveI := ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar M
  exact (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := (AlgebraicClosure ℚ)) (F := ↥(x1FunctionFieldBar M))).1

theorem childG1 (M : ℕ) [NeZero M] :
    Function.Injective (diffQExp (x1FunctionFieldBar M) : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)] → LaurentSeries (AlgebraicClosure ℚ)) :=
  ModularCurve.diffQExp_x1FunctionFieldBar_injective M

theorem childH (M : ℕ) [NeZero M] : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) :=
  CuspForm.finiteDimensional_Gamma1 M 2

end Children

section Gamma1

variable {M : ℕ} {k : ℤ}

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m * (Function.Periodic.qParam) 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩
  have := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  first | exact this | simpa only [smul_eq_mul] using this | simpa +zetaDelta only [smul_eq_mul] using this

lemma eq_zero_of_forall_qCoeff_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (h : ∀ n, qCoeff f n = 0) : f = 0 := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hs := hasSum_qCoeff f τ
  have hz : (fun m ↦ qCoeff f m * (Function.Periodic.qParam) 1 τ ^ m) = fun _ => 0 := by
    funext m
    rw [h m, zero_mul]
  rw [hz] at hs
  simpa using hs.unique hasSum_zero

lemma eq_of_forall_qCoeff_eq (f g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (h : ∀ n, qCoeff f n = qCoeff g n) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_qCoeff_eq_zero _ fun n => ?_
  simp only [qCoeff, CuspForm.coe_sub]
  rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods f g, map_sub, sub_eq_zero]
  exact h n

end Gamma1

section S2side

variable (M : ℕ)

def qCoeffLin (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma1 M) 2 →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) :
    qCoeffLin M n f = qCoeff f n := rfl

end S2side

section Coeff

variable (M : ℕ) [NeZero M]

def coeffFun (n : ℕ) : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) →ₗ[(AlgebraicClosure ℚ)] (AlgebraicClosure ℚ) where
  toFun ω := (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])).coeff (n : ℤ)
  map_add' ω₁ ω₂ := by
    simp only [Submodule.coe_add, map_add, HahnSeries.coeff_add]
  map_smul' c ω := by
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [← algebraMap_smul (x1FunctionFieldBar M) c (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)]), map_smul]
    change (((algebraMap (AlgebraicClosure ℚ) (x1FunctionFieldBar M) c : x1FunctionFieldBar M) :
        LaurentSeries (AlgebraicClosure ℚ)) * diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])).coeff (n : ℤ) = _
    change (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c * _).coeff _ = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

@[scoped simp] theorem coeffFun_apply (n : ℕ) (ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M))) :
    coeffFun M n ω = (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])).coeff (n : ℤ) := rfl

variable [Algebra (AlgebraicClosure ℚ) ℂ]

def coeffFunC (n : ℕ) : ℂ ⊗[(AlgebraicClosure ℚ)] ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) →ₗ[ℂ] ℂ :=
  (Algebra.TensorProduct.lmul'' (AlgebraicClosure ℚ) (S := ℂ)).toLinearMap ∘ₗ
    (((Algebra.linearMap (AlgebraicClosure ℚ) ℂ).comp (coeffFun M n)).baseChange ℂ)

theorem coeffFunC_tmul (n : ℕ) (c : ℂ) (ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M))) :
    coeffFunC M n (c ⊗ₜ ω) =
      c * algebraMap (AlgebraicClosure ℚ) ℂ ((diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])).coeff (n : ℤ)) := by
  simp [coeffFunC, LinearMap.baseChange_tmul]
  rfl

end Coeff

section Main

variable (M : ℕ) [NeZero M]

theorem main (ι₀ : (AlgebraicClosure ℚ) →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[(AlgebraicClosure ℚ)] ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ∀ ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)),
        coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(e (1 ⊗ₜ ω))) := by
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ι₀.toAlgebra
  haveI := childH M
  haveI := childE M

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast M 2

  have hω : ∀ i : Fin n, ∃ ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)),
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(b i)) := by
    intro i
    have hrange : ∀ m : ℕ, (qExpansion 1 ⇑(b i)).coeff m ∈ ι₀.range := by
      intro m
      obtain ⟨r, hr⟩ := hb i m
      refine ⟨r, ?_⟩
      rw [map_ratCast, hr]
      rfl
    obtain ⟨ω, hωq⟩ := childA M ι₀ (b i) hrange
    exact ⟨⟨ω, childB M ι₀ (b i) ω hωq⟩, hωq⟩
  choose ω hω using hω

  let Ψ : CuspForm (CongruenceSubgroup.Gamma1 M) 2 →ₗ[ℂ] ℂ ⊗[(AlgebraicClosure ℚ)] ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) :=
    b.constr ℂ fun i => (1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω i
  have hΨb : ∀ i, Ψ (b i) = (1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω i := fun i => by
    simp only [Ψ, Module.Basis.constr_basis]

  have hQω : ∀ (i : Fin n) (m : ℕ), coeffFunC M m ((1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω i) = qCoeff (b i) m := by
    intro i m
    rw [coeffFunC_tmul, one_mul]
    have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) (hω i)
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
    exact h
  have hQΨ : ∀ (m : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2), coeffFunC M m (Ψ f) = qCoeff f m := by
    intro m
    have hcomp : (coeffFunC M m).comp Ψ = qCoeffLin M m := by
      refine b.ext fun i => ?_
      rw [LinearMap.comp_apply, hΨb, hQω, qCoeffLin_apply]
    intro f
    simpa using LinearMap.congr_fun hcomp f

  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    refine eq_zero_of_forall_qCoeff_eq_zero f fun m => ?_
    rw [← hQΨ m f, LinearMap.mem_ker.mp hf, map_zero]

  have hsep : ∀ x : ℂ ⊗[(AlgebraicClosure ℚ)] ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)),
      (∀ m : ℕ, coeffFunC M m x = 0) → x = 0 := by
    intro x hx

    let Bq := Module.finBasis (AlgebraicClosure ℚ) ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M))
    let BC := Algebra.TensorProduct.basis ℂ Bq
    have hBC : ∀ i, BC i = (1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] Bq i := fun i => Algebra.TensorProduct.basis_apply Bq i
    obtain ⟨c, rfl⟩ : ∃ c : Fin _ → ℂ, x = ∑ i, c i • BC i := ⟨fun i => BC.repr x i, (BC.sum_repr x).symm⟩

    let g : Fin _ → LaurentSeries ℂ := fun i =>
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (Bq i : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)]))
    have hgps : ∀ i, ∃ p : PowerSeries ℂ, g i = HahnSeries.ofPowerSeries ℤ ℂ p := fun i => by
      obtain ⟨f, hf⟩ := childC M ι₀ (Bq i : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)]) (Bq i).2
      exact ⟨_, hf⟩
    have hLIq : LinearIndependent (AlgebraicClosure ℚ) (fun i => diffQExp (x1FunctionFieldBar M) (Bq i : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])) := by

      let Θq : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)] →ₗ[(AlgebraicClosure ℚ)] LaurentSeries (AlgebraicClosure ℚ) := (diffQExp (x1FunctionFieldBar M)).restrictScalars (AlgebraicClosure ℚ)
      have h1 : LinearIndependent (AlgebraicClosure ℚ) (fun i => ((Bq i : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M))) :
          Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)])) :=
        Bq.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have h2 := h1.map' Θq (LinearMap.ker_eq_bot.mpr (childG1 M))
      exact h2
    have hLI : LinearIndependent ℂ g := by
      have := ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent (AlgebraicClosure ℚ) ℂ _ hLIq
      exact this

    have hsum : ∑ i, c i • g i = 0 := by
      ext m
      rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [HahnSeries.coeff_smul, smul_eq_mul]
      rcases le_or_gt 0 m with hm | hm
      · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
        have h0 := hx m'
        rw [map_sum] at h0
        simp only [map_smul, hBC, coeffFunC_tmul, one_mul, smul_eq_mul] at h0

        convert h0 using 2 with i <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _
      · apply Finset.sum_eq_zero
        intro i _
        obtain ⟨p, hp⟩ := hgps i
        have hr : m ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
          rintro ⟨m'', hm''⟩
          simp only at hm''
          omega
        rw [hp, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range hr, mul_zero]
    have hc : ∀ i, c i = 0 := fun i => Fintype.linearIndependent_iff.mp hLI c hsum i
    simp [hc]
  have hsurj : Function.Surjective Ψ := by
    have hgen : ∀ ω' : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)),
        (1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω' ∈ LinearMap.range Ψ := by
      intro ω'
      obtain ⟨fω, hfω⟩ := childC M ι₀ (ω' : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)]) ω'.2
      refine ⟨fω, ?_⟩
      rw [← sub_eq_zero]
      refine hsep _ fun m => ?_
      rw [map_sub, hQΨ, coeffFunC_tmul, one_mul, sub_eq_zero]
      have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) hfω
      simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
      exact h.symm
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c ω' =>
      have : c ⊗ₜ[(AlgebraicClosure ℚ)] ω' = c • ((1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω') := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (hgen ω')
    | add x y hx hy => exact Submodule.add_mem _ hx hy

  let e₀ : CuspForm (CongruenceSubgroup.Gamma1 M) 2 ≃ₗ[ℂ] ℂ ⊗[(AlgebraicClosure ℚ)] ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)) :=
    LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨e₀.symm, fun ω' => ?_⟩
  obtain ⟨fω, hfω⟩ := childC M ι₀ (ω' : Ω[↥(x1FunctionFieldBar M)⁄(AlgebraicClosure ℚ)]) ω'.2
  have hfeq : e₀.symm ((1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω') = fω := by
    apply eq_of_forall_qCoeff_eq
    intro m
    have he : Ψ (e₀.symm ((1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω')) = (1 : ℂ) ⊗ₜ[(AlgebraicClosure ℚ)] ω' := e₀.apply_symm_apply _
    rw [← hQΨ m, he, coeffFunC_tmul, one_mul]
    have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) hfω
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
    exact h
  rw [hfeq]
  exact hfω

end Main

end X1RegDiff
open scoped _root_.P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.X1RegDiff

end
open scoped _root_.P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.X1RegDiff

open scoped TensorProduct in
theorem solution (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[AlgebraicClosure ℚ]
          ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
              ↥(ModularCurve.x1FunctionFieldBar M)) ≃ₗ[ℂ]
        CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ∀ ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
          ↥(ModularCurve.x1FunctionFieldBar M)),
        ModularCurve.coeffMap ι₀
            (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
              (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(e (1 ⊗ₜ ω))) :=
  X1RegDiff.main M ι₀
