/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup (git blob 7ac314f8c91a423aa150b13f346b28f69ce5dc8f, sha256 c3908d3cc6bd0fdb2919ee4eb050a87d427f8e034733a0a63e96d4c3d93191a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup

set_option autoImplicit false

open NumberField MeasureTheory

noncomputable section

namespace FltWs24
namespace ConstantTermBorel

open AutomorphicForm

theorem unipotentGL2_mul_eq_mul_unipotentGL2 {A : Type*} [CommRing A] (γ : GL (Fin 2) A)
    (hγ : γ ∈ borelSubgroup A) (x y : A)
    (hy : (γ : Matrix (Fin 2) (Fin 2) A) 0 0 * y = x * (γ : Matrix (Fin 2) (Fin 2) A) 1 1) :
    unipotentGL2 x * γ = γ * unipotentGL2 y := by
  apply Units.ext
  have h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hγ
  simp only [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hy, mul_comm, add_comm]

variable (K : Type) [Field K] [NumberField K]



theorem globalPoints_unipotentGL2 (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Units.ext
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_mul_globalPoints (γ : Matrix.GeneralLinearGroup (Fin 2) K) (hγ : γ ∈ borelSubgroup K)
    (x : (AdeleRing (𝓞 K) K)) :
    unipotentGL2 x * globalPoints (𝓞 K) K γ
      = globalPoints (𝓞 K) K γ
        * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K)
            ((((borelDiagFst ⟨γ, hγ⟩)⁻¹ * borelDiagSnd ⟨γ, hγ⟩ : Kˣ) : K)) * x) := by
  refine unipotentGL2_mul_eq_mul_unipotentGL2 (globalPoints (𝓞 K) K γ) (globalPoints_mem_adelicBorel (𝓞 K) K hγ) x _ ?_

  have h00 : ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0
      = algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0) := globalPoints_apply (𝓞 K) K γ 0 0
  have h11 : ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1
      = algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1) := globalPoints_apply (𝓞 K) K γ 1 1
  have hne : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := (borelDiagFst ⟨γ, hγ⟩).ne_zero
  rw [h00, h11, Units.val_mul, Units.val_inv_eq_inv_val, borelDiagFst_apply_val, borelDiagSnd_apply_val]
  change algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)
      * (algebraMap K (AdeleRing (𝓞 K) K) (((γ : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) K) 1 1) * x)
    = x * algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)
  rw [← mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_comm]

end FltWs24.ConstantTermBorel

end

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      φ (AutomorphicForm.globalPoints (𝓞 K) K γ * h) = φ h)
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ AutomorphicForm.borelSubgroup K)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.globalPoints (𝓞 K) K γ * g)
      = AutomorphicForm.constantTerm
          (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by
  set c : Kˣ := (AutomorphicForm.borelDiagFst ⟨γ, hγ⟩)⁻¹ * AutomorphicForm.borelDiagSnd ⟨γ, hγ⟩ with hc

  have hper : ∀ (k : K) (x : AdeleRing (𝓞 K) K),
      φ (AutomorphicForm.unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k + x) * g)
        = φ (AutomorphicForm.unipotentGL2 x * g) := by
    intro k x
    rw [AutomorphicForm.unipotentGL2_add, mul_assoc,
      ← FltWs24.ConstantTermBorel.globalPoints_unipotentGL2 K k,
      hφ _ (AutomorphicForm.unipotentGL2_mem_borelSubgroup k)]

  have hint : (fun x => φ (AutomorphicForm.unipotentGL2 x * (AutomorphicForm.globalPoints (𝓞 K) K γ * g)))
      = fun x => φ (AutomorphicForm.unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) (c : K) * x) * g) := by
    funext x
    rw [← mul_assoc, FltWs24.ConstantTermBorel.unipotentGL2_mul_globalPoints K γ hγ x, mul_assoc,
      hφ γ hγ]
  show ∫ x, φ (AutomorphicForm.unipotentGL2 x * (AutomorphicForm.globalPoints (𝓞 K) K γ * g))
      ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
    = ∫ x, φ (AutomorphicForm.unipotentGL2 x * g)
      ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
  rw [hint]
  exact NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap K
    (f := fun x => φ (AutomorphicForm.unipotentGL2 x * g)) hper (c : K) c.ne_zero
