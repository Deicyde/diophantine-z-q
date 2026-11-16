/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsAdicComplete_of_finite_of_isNoetherianRing
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing

open scoped TensorProduct

namespace SolFinComplete
open AdicCompletion

universe u

theorem isAdicComplete_of_finite_aux {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : M ≃ₗ[R] R ⊗[R] M := (TensorProduct.lid R M).symm
  let e2 : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
     LinearEquiv.rTensor M (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have : (of I M : M → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp only [e1, e2, e3, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      ofTensorProductEquivOfFiniteNoetherian_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul, ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      simpa using this
    rw [h1, one_smul]
  rw [this]; exact e3.bijective.comp (e2.bijective.comp e1.bijective)

theorem isAdicComplete_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr_apply, map_of]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  haveI : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker p) := isAdicComplete_of_finite_aux I _
  exact isAdicComplete_of_linearEquiv I (p.quotKerEquivOfSurjective hp)

end SolFinComplete

theorem solution
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M :=
  SolFinComplete.isAdicComplete_of_finite I M
